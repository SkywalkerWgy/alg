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
        loop invariant i_73: 0 <= i <= a;

        loop invariant i_74: 0 <= j <= b;

        loop invariant i_75: 0 <= k <= a + b;

        loop invariant i_76: k == i + j;

        loop invariant i_77: Sorted(res, 0, k);

        loop invariant i_78: \forall integer p; 0 <= p < i ==> A[p] <= res[p];

        loop invariant i_79: \forall integer q; 0 <= q < j ==> B[q] <= res[q];

        loop invariant i_80: \forall integer p; 0 <= p < i ==> \exists integer r; 0 <= r < k && A[p] == res[r];

        loop invariant i_81: \forall integer q; 0 <= q < j ==> \exists integer r; 0 <= r < k && B[q] == res[r];


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
        loop invariant i_89: 0 <= i <= a;

        loop invariant i_90: k == \at(k, End_l) + (i - \at(i, End_l));

        loop invariant i_91: \at(j, End_l) == b;

        loop invariant i_92: Sorted(res, 0, k);

        loop invariant i_93: \forall integer p; \at(i, End_l) <= p < i ==> A[p] == res[\at(k, End_l) + (p - \at(i, End_l))];

        loop invariant i_94: \forall integer p; 0 <= p < i ==> \exists integer r; 0 <= r < k && A[p] == res[r];

        loop invariant i_95: \forall integer q; 0 <= q < \at(j, End_l) ==> \exists integer r; 0 <= r < k && B[q] == res[r];


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
        loop invariant i_82: 0 <= j <= b;

        loop invariant i_83: k == \at(k, End_l) + (j - \at(j, End_l));

        loop invariant i_84: \at(i, End_l) == a;

        loop invariant i_85: Sorted(res, 0, k);

        loop invariant i_86: \forall integer q; \at(j, End_l) <= q < j ==> B[q] == res[\at(k, End_l) + (q - \at(j, End_l))];

        loop invariant i_87: \forall integer q; 0 <= q < j ==> \exists integer r; 0 <= r < k && B[q] == res[r];

        loop invariant i_88: \forall integer p; 0 <= p < \at(i, End_l) ==> \exists integer r; 0 <= r < k && A[p] == res[r];


        loop assigns res[0..a + b - 1];
        loop assigns j, k;
    */
    while (j < b) {
        res[k] = B[j];
        k = k + 1;
        j = j + 1;
    }
}