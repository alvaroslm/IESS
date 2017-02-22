
//  (C) Alvaro Salmador

#ifdef _MSC_VER
#define _CRT_SECURE_NO_WARNINGS
#endif

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <limits.h>
#include <time.h>
#include <string.h>
#include <math.h>
#include <algorithm>
#include <string>
#include <list>
#include <vector>
#include <map>
#include <set>
#include <deque>
#include <queue>

using namespace std;

#define FOR(__fvar,__fini,__fend) for(__fvar=__fini; __fvar<=__fend; ++__fvar)

//// Global variables

int N=0, Nops=0;
int **Mat; //input data
int **M2; //sum table
int **AplusRSum; //A+ row-wise sum table
int **AminusRSum; //A- row-wise sum table
int *aplus, *aminus; //temporary rows

//// Helper functions

// Print matrix
void mat_print(int **mat) {
	int i,j;
	FOR(i,0,N-1) {
		FOR(j,0,N-1)
			printf("%6d ", mat[i][j]);
		printf("\n");
	}
}

// Allocate memory for matrix
template<typename T> T** mat_alloc(T**, int n) {
	T** mat = new T* [n];
	T* buffer = new T [n*n];
	for(int i=0; i<n; ++i) mat[i] = buffer+i*n;
	return mat;
}

// Free matrix memory
template<typename T> void mat_free(T** mat) {
	delete [] mat[0];
	delete [] mat;
}

///////////////

// Brute force solution O(n^6)
int solve_bf() {
	int w, h, i, j, ii, jj;
	int rsum, max=INT_MIN;
	int maxw=0,maxh=0,maxi=0,maxj=0;
	FOR(w,1,N) FOR(h,1,N) //rect width and height
	{
		FOR(i,0,N-h) //mat row
		{
			FOR(j,0,N-w)  //mat col
			{
				rsum=0;
				FOR(ii,0,h-1) // rect row
					FOR(jj,0,w-1) //rect col
						rsum += Mat[i+ii][j+jj];
				if (rsum>max) {
					max=rsum;
					maxw=w; maxh=h; maxi=i; maxj=j;
				}
			}
		}
	}
	printf("i,j=%d,%d, w,h=%d,%d max=%d\n", maxi, maxj, maxw, maxh, max);
	return max;
}

// Generate sum table ('integral' over the image from 0,0 to i,j) for use by optimized method(s). Each position holds the sum of the rectangle covering 0,0-i,j
void gen_sum(int** __restrict Sum, int** __restrict A, char plusminus=0) {
	int i,j,sum;
	FOR(j,0,N-1) Sum[0][j] = 0; // warning: prevents in-place operation
	FOR(i,0,N-1) //mat row
	{
		sum=0;
		int* lastrow = (i>0) ? Sum[i-1] : Sum[0];
		FOR(j,0,N-1)  //mat col
		{
			if (plusminus==0) sum += A[i][j];	//plusminus is for generating Aplus and Aminus sum matrices (positives or negatives only, repectively)
			else if (plusminus>0) sum += max(A[i][j], 0);
			else sum += min(A[i][j], 0);
			Sum[i][j] = lastrow[j] + sum;
		}
	}
}

// Sum table lookup. Returns sum for i,j-i2,j2 rectangle
inline int sum_table(int i, int j, int i2, int j2, int** S=M2) {
	//TODO : a N+1 matrix with zeros in M2[..][0] and M2[0][..] would be faster than these conditional expressions on the innermost loop
	int ul = (i&&j) ? S[i-1][j-1] : 0;
	int ur = j ? S[i2][j-1] : 0;
	int ll = i ? S[i-1][j2] : 0;
	return S[i2][j2]+ul-ur-ll;
}

// Optimization O(n^4)
int solve_sumtable4() {
	int i, j, i2, j2;
	int max=INT_MIN;
	int maxw=0,maxh=0,maxi=0,maxj=0;
	FOR(i,0,N-1) //mat row
		FOR(j,0,N-1)  //mat col
			FOR(i2,i,N-1)
				FOR(j2,j,N-1) {
					int sum = sum_table(i,j,i2,j2);
					if (sum>max) {
						max=sum;
						maxw=j2-j+1; maxh=i2-i+1; maxi=i; maxj=j;
					}
				}
	printf("\ni,j=%d,%d, w,h=%d,%d max=%d\n", maxi, maxj, maxw, maxh, max);
	return max;
}

// Optimization O(n^3)
int solve_sumtable3() {
	int i, i2, k, sum, sk;
	int max=INT_MIN;
	FOR(i,0,N-1) //rect top row
		FOR(i2,i,N-1) // rect bottom
		{
			sum=0;
			FOR(k,0,N-1) // calculate max sum_table sum possible for this top/bottom row combination 
			{	
				sk = sum_table(i,k,i2,k); // sum for rect col k
				// Kadane's algorithm, we find max consecutive sum of sk
				if (sum>0) sum+=sk; else sum=sk;
				if (sum>max) max=sum;
			}
			if (sum>max) max=sum;
		}
	printf("\nsumtable3: max=%d\n", max);
	return max;
}

// Rectangle rows interval (t0-t1,b0-b1), this is the type of elements we'll have in our priority queue for ESS
struct RectI {
	int t0,t1,b0,b1;
	int prio;
	inline RectI() : t0(0), b0(0), t1(0), b1(0), prio(INT_MIN) {}
	inline RectI(int Tlo, int Thi, int Blo, int Bhi) : t0(Tlo), t1(Thi), b0(Blo), b1(Bhi)  {
		assert(b1>=b0 && t1>=t0); //this can't be
		assert(t0<=t1);
		// constrain the intervals to sensible(valid) values
		if (t0>b0) {
			b0=t0;
			if (b0>b1) b1=b0;
		}
		//assert(t1<=b1);
		if (t1>b1) {  
			t1=b1;
			if (t0>t1) t0=t1;
		}
		prio = upper_bound(); 
	}
	// Upper bound on the sum of any subwindow this RectInterval contains
	inline int upper_bound()  { 
		//Improvement for worst cases An09 section 3.3 (I-ESS)- http://dro.deakin.edu.au/eserv/DU:30044565/venkatesh-efficientalgorithms-2009.pdf
		//int sum = sum_table(t0,l0,b1,r1,AplusSum) + ((t1<=b0 && l1<=r0) ? sum_table(t1,l1,b0,r0,AminusSum) : 0);
		assert(t0<=t1); 
		assert(t0<=b0); 
		assert(t1<=b1); 
		int i,j,k,sum,sk,max;

		FOR(j,0,N-1) 
			aplus[j] = AplusRSum[b1][j] - ((t0>0)?AplusRSum[t0-1][j]:0);
		if (b0>=t1) {
			FOR(j,0,N-1) 
				aminus[j] = AminusRSum[b0][j] - ((t1>0)?AminusRSum[t1-1][j]:0);
		} else {
			FOR(j,0,N-1) 
				aminus[j]=0;
		}
		max=INT_MIN;
		sum=0;
		FOR(k,0,N-1) // calculate max sum with Kadane's algorithm, this will give us the upper bound
		{	
			sk = aplus[k]+aminus[k]; 
			// Kadane's algorithm, we find max consecutive sum of sk
			if (sum>0) sum+=sk; else sum=sk;
			if (sum>max) max=sum;
		}
		Nops += N;
		return max; /**/
		/* //for testing: true max instead of upper bound, this should help ESS always produce the right results if the rest of the code is right
		int i,j,i2,j2,sum=INT_MIN;
		FOR(j,0,N-1)
			FOR(j2,0,N-1)
				FOR(i,t0,t1)
					FOR(i2,b0,b1) {
						if (i>i2 || j>j2)
							continue;
						Nops++;
						if (sum<sum_table(i, j, i2, j2))
							sum = sum_table(i, j, i2, j2);
					}
		return sum;/**/
	}
	inline bool onerows() const { return t0==t1 && b0==b1; } 
	inline bool operator<(const RectI& r) const { return prio<r.prio; }
	void print(char ch=' ') const { printf("(%d:%d, %d:%d)%c", t0, t1, b0, b1, ch); }
	int split(RectI& R1, RectI& R2) const {
		int maxi=-1, type=-1;
		int mid;
		if (onerows()) return -1; //just one rect can't be split
		// Split the largest interval
		if (t1-t0>maxi) { maxi=t1-t0; type=0; }
		if (b1-b0>maxi) { maxi=b1-b0; type=1; }
		assert(type>=0 && type<=1);
		if (type==0) { //T
			mid = (t1+t0)/2;
			R1 = RectI(t0,mid, b0,b1);//, l0,l1, r0,r1);
			R2 = RectI(mid+1,t1, b0,b1);//, l0,l1, r0,r1);
		} else { //B
			mid = (b1+b0)/2;
			R1 = RectI(t0,t1, b0,mid); //, l0,l1, r0,r1);
			R2 = RectI(t0,t1, mid+1,b1); //, l0,l1, r0,r1);
		}
		return type;
	}
};

// Optimization (Improved ESS) 
// Beyond SlidingWindows: Object Localization by Efficient Subwindow Search - http://www.kyb.tuebingen.mpg.de/fileadmin/user_upload/files/publications/lampert-ESS-PAMI_[0].pdf
// Efficient algorithms for subwindow search in object detection and localization - http://dro.deakin.edu.au/eserv/DU:30044565/venkatesh-efficientalgorithms-2009.pdf
int solve_iess() {
	priority_queue<RectI> p;
	RectI R(0, N-1, 0, N-1);//, 0, N-1, 0, N-1);
	RectI R1, R2;
	while (!R.onerows()) {
		// Split R and push r1 and r2
		R.split(R1, R2);
		p.push(R1); 
		p.push(R2);
		// Retrieve top priority rect interval (the one with better ^f upper bound)
		R = p.top();
		p.pop();
		if (p.empty()) { printf("empty!\n"); break; }
	};

	assert(R.t0==R.t1 && R.b0==R.b1);
	printf("\nI-ESS t,b=%d,%d max=%d\n", R.t0, R.b0, R.prio);
	return R.prio;
}


int main()
{
	int i,j;

	// Read size N
	printf("N: ");
	scanf("%d", &N);
	if (N==0) return 0;

	// Generate random matrix
	Mat = mat_alloc(Mat, N);
	//srand(333); //deterministic initialization, for testing
	srand(time(NULL));
	FOR(i,0,N-1)
		FOR(j,0,N-1)
			Mat[i][j] = rand()%2000-1000; // [-1000,1000) so it can be visualized and also integer won't overflow
	
	M2 = mat_alloc(M2, N); //allocate sum table
	gen_sum(M2, Mat); //generate sum table

	// Print the randomly-generated matrix if it's not too big for the screen
	if (N<16) {
		//Display matrix
		mat_print(Mat);
		printf("\n");
		mat_print(M2); //dbg- show sum table
	}

	// Solve the max subwindow search problem with different methods

	//solve_bf(); // O(N^6)

 	if (N<200) solve_sumtable4(); // O(N^4)
	if (N<1000) solve_sumtable3(); // O(N^3)

	///////////////////

	// Calculate A+ and A- row-wise sum matrices
	AplusRSum = mat_alloc(AplusRSum, N);
	AminusRSum = mat_alloc(AminusRSum, N);
	FOR(i,0,N-1) FOR(j,0,N-1) AplusRSum[i][j] = ((i>0)?AplusRSum[i-1][j]:0) + std::max(Mat[i][j], 0);
	FOR(i,0,N-1) FOR(j,0,N-1) AminusRSum[i][j] = ((i>0)?AminusRSum[i-1][j]:0) + std::min(Mat[i][j], 0);
	aplus = new int [N]; //temporary a+, a- sum rows
	aminus = new int [N];

	solve_iess(); //improved ESS

	printf("Nops=%d O(N^%f)\n", Nops, logf((float)Nops)/logf((float)N));

	mat_free(Mat);
	mat_free(M2);
	mat_free(AplusRSum);
	mat_free(AminusRSum);
	delete [] aplus;
	delete [] aminus;

	return 0;
}