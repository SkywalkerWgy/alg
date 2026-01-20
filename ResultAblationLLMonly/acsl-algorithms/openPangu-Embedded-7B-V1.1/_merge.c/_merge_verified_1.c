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
        loop invariant i_0: i + j + k == a + b;

        loop invariant i_1: 0 <= i < a;

        loop invariant i_2: 0 <= j < b;

        loop invariant i_3: 0 <= k < a + b;

        loop invariant i_4: A[i] <= B[j] ==> res[k] == A[i];

        loop invariant i_5: \forall integer p, q, r; 0 <= p < a, 0 <= q < b, 0 <= r < a + b, p + q + r == a + b - 1 ==> A[p] <= B[q] == res[r] == A[p] || B[q];

        loop invariant i_6: i + k == a;

        loop invariant i_7: j + k == b;


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
        loop invariant i_11: 0 <= i < a, 0 <= j < b, 0 <= k < a + b, A[i] <= B[j] ==> res[k] == A[i];

        loop invariant i_12: 0 <= i < a, 0 <= j < b, 0 <= k < a + b;


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
        loop invariant i_8: 0 <= k < a + b;

        loop invariant i_9: 0 <= i < a + b;

        loop invariant i_10: 0 <= j < b;


        loop assigns res[0..a + b - 1];
        loop assigns j, k;
    */
    while (j < b) {
        res[k] = B[j];
        k = k + 1;
        j = j + 1;
    }
}