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
        loop invariant i_33: i + j + k <= a + b;

        loop invariant i_34: 0 <= k < a + b;

        loop invariant i_35: 0 <= i < a;

        loop invariant i_36: 0 <= j < b;

        loop invariant i_37: res[0..k-1] contains only A[0..i-1] and B[0..j-1];


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
        loop invariant i_43: 0 <= j < b;

        loop invariant i_44: 0 <= i < a;

        loop invariant i_45: 0 <= k < a + b;

        loop invariant i_46: res[0..k-1] contains only A[0..i-1] and B[0..j-1];


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
        loop invariant i_38: 0 <= j < b;

        loop invariant i_39: 0 <= k < a + b;

        loop invariant i_40: 0 <= i < a;

        loop invariant i_41: res[0..k-1] contains only A[0..i-1] and B[0..j-1];

        loop invariant i_42: i + j + k <= a + b;


        loop assigns res[0..a + b - 1];
        loop assigns j, k;
    */
    while (j < b) {
        res[k] = B[j];
        k = k + 1;
        j = j + 1;
    }
}