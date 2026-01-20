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
        loop invariant i_0: \valid(A + (0..a - 1));

        loop invariant i_1: \valid(B + (0..b - 1));

        loop invariant i_2: \valid(res + (0..a + b - 1));

        loop invariant i_3: \separated(&A[0..(a-1)], &B[0..(b-1)], &res[0..(a+b-1)]);

        loop invariant i_4: a > 0;

        loop invariant i_5: b > 0;

        loop invariant i_6: Sorted(A, 0, a);

        loop invariant i_7: Sorted(B, 0, b);

        loop invariant i_8: 0 <= i <= a;

        loop invariant i_9: 0 <= j <= b;

        loop invariant i_10: 0 <= k <= a + b;

        loop invariant i_11: k == i + j;

        loop invariant i_12: Sorted(res, 0, k);

        loop invariant i_13: \forall integer p; i <= p < a ==> (k == 0 || res[k-1] <= A[p]);

        loop invariant i_14: \forall integer q; j <= q < b ==> (k == 0 || res[k-1] <= B[q]);


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
        loop invariant i_28: \valid(A + (0..a - 1));

        loop invariant i_29: \valid(B + (0..b - 1));

        loop invariant i_30: \valid(res + (0..a + b - 1));

        loop invariant i_31: \separated(&A[0..(a-1)], &B[0..(b-1)], &res[0..(a+b-1)]);

        loop invariant i_32: a > 0;

        loop invariant i_33: b > 0;

        loop invariant i_34: Sorted(A, 0, a);

        loop invariant i_35: Sorted(B, 0, b);

        loop invariant i_36: 0 <= i <= a;

        loop invariant i_37: 0 <= j <= b;

        loop invariant i_38: 0 <= k <= a + b;

        loop invariant i_39: k == i + j;

        loop invariant i_40: Sorted(res, 0, k);

        loop invariant i_41: \forall integer p; i <= p < a ==> (k == 0 || res[k-1] <= A[p]);

        loop invariant i_42: \forall integer q; j <= q < b ==> (k == 0 || res[k-1] <= B[q]);

        loop invariant i_43: j == \at(j, End_l);

        loop invariant i_44: \forall integer p; 0 <= p < \at(k, End_l) ==> res[p] == \at(res[p], End_l);

        loop invariant i_45: (i < a) ==> j == b;


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
        loop invariant i_15: \valid(A + (0..a - 1));

        loop invariant i_16: \valid(B + (0..b - 1));

        loop invariant i_17: \valid(res + (0..a + b - 1));

        loop invariant i_18: \separated(&A[0..(a-1)], &B[0..(b-1)], &res[0..(a+b-1)]);

        loop invariant i_19: a > 0;

        loop invariant i_20: b > 0;

        loop invariant i_21: Sorted(A, 0, a);

        loop invariant i_22: Sorted(B, 0, b);

        loop invariant i_23: 0 <= j <= b;

        loop invariant i_24: 0 <= k <= a + b;

        loop invariant i_25: k == a + j;

        loop invariant i_26: Sorted(res, 0, k);

        loop invariant i_27: \forall integer q; j <= q < b ==> (k == 0 || res[k-1] <= B[q]);


        loop assigns res[0..a + b - 1];
        loop assigns j, k;
    */
    while (j < b) {
        res[k] = B[j];
        k = k + 1;
        j = j + 1;
    }
}