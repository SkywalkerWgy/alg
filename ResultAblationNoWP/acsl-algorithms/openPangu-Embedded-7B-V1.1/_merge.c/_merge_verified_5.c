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
        loop invariant i_67: 0 <= i < a;

        loop invariant i_68: 0 <= j < b;

        loop invariant i_69: 0 <= k < a + b;

        loop invariant i_70: res[0..k-1] is sorted;

        loop invariant i_71: i + j + k == a + b;

        loop invariant i_72: \forall integer r; 0 <= r < k ==> res[r] == (r < a ? A[i + r] : B[j + r]);


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
        loop invariant i_78: i + j + k == a + b;

        loop invariant i_79: 0 <= i < a;

        loop invariant i_80: 0 <= j < b;

        loop invariant i_81: 0 <= k < a + b;

        loop invariant i_82: res[0..k-1] is sorted;


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
        loop invariant i_73: i + j + k == a + b;

        loop invariant i_74: 0 <= i < a;

        loop invariant i_75: 0 <= j < b;

        loop invariant i_76: 0 <= k < a + b;

        loop invariant i_77: res[0..k-1] is sorted;


        loop assigns res[0..a + b - 1];
        loop assigns j, k;
    */
    while (j < b) {
        res[k] = B[j];
        k = k + 1;
        j = j + 1;
    }
}