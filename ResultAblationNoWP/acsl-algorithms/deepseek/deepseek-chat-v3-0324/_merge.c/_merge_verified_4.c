/*@
  predicate Sorted(int *t, integer lo, integer hi) =
    \forall integer i, j; lo <= i <= j < hi ==> t[i] <= t[j];
*/

/*@
    requires \valid(A + (0..a- 1));
    requires \valid(B + (0..b - 1));
    requires \valid(res + (0..a + b - 1));
    requires \separated(&A[0..(a-1)], &B[0..(b-1)], &res[0..(a+b-1)]);
    requires a > 0;
    requires b > 0;
    requires Sorted(A, 0, a);
    requires Sorted(B, 0, b);
    assigns res[0..a + b - 1];
    ensures e_1: Sorted(res, 0, a + b);
*/
void _merge(int A[], int B[], int res[], int a, int b) {
    int i = 0;
    int j = 0;
    int k = 0;
    // Loop A
    /*@
        loop invariant i_57: 0 <= i <= a;

        loop invariant i_58: 0 <= j <= b;

        loop invariant i_59: k == i + j;

        loop invariant i_60: \forall integer p; 0 <= p < k ==> res[p] <= res[p+1];

        loop invariant i_61: \forall integer p; 0 <= p < i ==> A[p] <= res[k-1];

        loop invariant i_62: \forall integer p; 0 <= p < j ==> B[p] <= res[k-1];

        loop invariant i_63: \forall integer p; 0 <= p < k ==> (p < i + j ==> res[p] <= A[i] || res[p] <= B[j]);


        loop assigns i, j, k;
        loop assigns res[0..a + b - 1];
    */
    while (i < a && j < b) {
        if (A[i] <= B[j]) {
            res[k] = A[i];
            k = k + 1;
            i = i + 1;
        } 
        else {
            res[k] = B[j];
            k = k + 1;
            j = j + 1;
        }
    }
    //@ ghost End_l: ;
    
    // Loop B
    /*@
        loop invariant i_68: 0 <= i <= a;

        loop invariant i_69: k == i + j;

        loop invariant i_70: \forall integer p; 0 <= p < k ==> res[p] <= res[p+1];

        loop invariant i_71: \forall integer p; 0 <= p < i ==> A[p] <= res[k-1];

        loop invariant i_72: \forall integer p; 0 <= p < k ==> (p < i + j ==> res[p] <= A[i]);


        loop assigns res[0..a + b - 1];
        loop assigns i, k;
    */
    while (i < a) {
        res[k] = A[i];
        k = k + 1;
        i = i + 1;
    }

    // Loop C
    /*@
        loop invariant i_64: 0 <= j <= b;

        loop invariant i_65: k == a + j;

        loop invariant i_66: \forall integer p; 0 <= p < k ==> res[p] <= res[p+1];

        loop invariant i_67: \forall integer p; 0 <= p < j ==> B[p] <= res[k-1];


        loop assigns res[0..a + b - 1];
        loop assigns j, k;
    */
    while (j < b) {
        res[k] = B[j];
        k = k + 1;
        j = j + 1;
    }
}