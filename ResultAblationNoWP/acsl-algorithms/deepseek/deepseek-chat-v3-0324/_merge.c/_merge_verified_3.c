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
        loop invariant i_37: s for the first loop (Loop A): ``` loop invariant 0 <= i <= a;

        loop invariant i_38: 0 <= i <= a;

        loop invariant i_39: 0 <= j <= b;

        loop invariant i_40: k == i + j;

        loop invariant i_41: Sorted(res, 0, k);

        loop invariant i_42: \forall integer p; 0 <= p < i ==> A[p] <= res[k-1];

        loop invariant i_43: \forall integer q; 0 <= q < j ==> B[q] <= res[k-1];

        loop invariant i_44: \forall integer p; 0 <= p < i ==> res[p + q] == A[p] || \exists integer q; 0 <= q < j && res[p + q] == B[q];

        loop invariant i_45: \forall integer q; 0 <= q < j ==> res[p + q] == B[q] || \exists integer p; 0 <= p < i && res[p + q] == A[p];


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
        loop invariant i_52: 0 <= i <= a;

        loop invariant i_53: k == \at(k, End_l) + (i - \at(i, End_l));

        loop invariant i_54: Sorted(res, 0, k);

        loop invariant i_55: \forall integer p; \at(i, End_l) <= p < i ==> res[\at(k, End_l) + (p - \at(i, End_l))] == A[p];

        loop invariant i_56: \forall integer q; 0 <= q < \at(j, End_l) ==> res[q + \at(i, End_l)] == B[q] || \exists integer p; \at(i, End_l) <= p < i && res[q + p] == A[p];


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
        loop invariant i_46: s for Loop C: ``` loop invariant 0 <= j <= b;

        loop invariant i_47: 0 <= j <= b;

        loop invariant i_48: k == \at(k, End_l) + (j - \at(j, End_l));

        loop invariant i_49: Sorted(res, 0, k);

        loop invariant i_50: \forall integer q; \at(j, End_l) <= q < j ==> res[\at(k, End_l) + (q - \at(j, End_l))] == B[q];

        loop invariant i_51: \forall integer p; 0 <= p < \at(i, End_l) ==> res[p + \at(j, End_l)] == A[p] || \exists integer q; \at(j, End_l) <= q < j && res[p + q] == B[q];


        loop assigns res[0..a + b - 1];
        loop assigns j, k;
    */
    while (j < b) {
        res[k] = B[j];
        k = k + 1;
        j = j + 1;
    }
}