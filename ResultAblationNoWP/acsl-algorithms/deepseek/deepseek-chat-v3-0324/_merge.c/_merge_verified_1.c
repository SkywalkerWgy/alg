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
        loop invariant i_0: 0 <= i <= a;

        loop invariant i_1: 0 <= j <= b;

        loop invariant i_2: k == i + j;

        loop invariant i_3: Sorted(res, 0, k);

        loop invariant i_4: \forall integer p; 0 <= p < i ==> A[p] <= res[p + j];

        loop invariant i_5: \forall integer p; 0 <= p < j ==> B[p] <= res[p + i];


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
        loop invariant i_10: s for Loop B: ``` loop invariant i <= a;

        loop invariant i_11: i <= a;

        loop invariant i_12: k == i + j;

        loop invariant i_13: Sorted(res, 0, k);

        loop invariant i_14: \forall integer p; 0 <= p < j ==> B[p] <= res[i + p];

        loop invariant i_15: \forall integer p; 0 <= p < i ==> A[p] <= res[p + j];

        loop invariant i_16: \forall integer p; 0 <= p < \at(k, End_l) ==> res[p] == \at(res[p], End_l);


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
        loop invariant i_6: j <= b;

        loop invariant i_7: k == (a + j);

        loop invariant i_8: Sorted(res, 0, k);

        loop invariant i_9: \forall integer p; 0 <= p < j ==> B[p] <= res[a + p];


        loop assigns res[0..a + b - 1];
        loop assigns j, k;
    */
    while (j < b) {
        res[k] = B[j];
        k = k + 1;
        j = j + 1;
    }
}