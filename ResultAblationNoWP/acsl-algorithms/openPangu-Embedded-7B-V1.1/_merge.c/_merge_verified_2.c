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
        loop invariant i_18: i + j + k <= a + b;

        loop invariant i_19: 0 <= k <= a + b - 1;

        loop invariant i_20: \exists integer k; 0 <= k < a + b - 1 ==> res[k] == A[i] for some i < a;

        loop invariant i_21: \exists integer k; 0 <= k < a + b - 1 ==> res[k] == B[j] for some j < b;

        loop invariant i_22: \forall integer i, j; 0 <= i < a, 0 <= j < b, 0 <= k < a + b - 1 ==> i + j + k == k\_prev + 1;

        loop invariant i_23: \forall integer k; 0 <= k < a + b - 1 ==> res[k] == \at(res[k], prev);


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
        loop invariant i_29: i + j + k <= a + b;

        loop invariant i_30: 0 <= k <= a + b - 1;


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
        loop invariant i_24: 0 <= i < a, 0 <= j < b, 0 <= k < a + b - 1;

        loop invariant i_25: \exists integer k; 0 <= k < a + b - 1 ==> res[k] == A[i] for some i < a;

        loop invariant i_26: \exists integer k; 0 <= k < a + b - 1 ==> res[k] == B[j] for some j < b;

        loop invariant i_27: \forall integer i, j, k; 0 <= i < a, 0 <= j < b, 0 <= k < a + b - 1 ==> i + j + k == k\_prev + 1;

        loop invariant i_28: \forall integer k; 0 <= k < a + b - 1 ==> res[k] == \at(res[k], prev);


        loop assigns res[0..a + b - 1];
        loop assigns j, k;
    */
    while (j < b) {
        res[k] = B[j];
        k = k + 1;
        j = j + 1;
    }
}