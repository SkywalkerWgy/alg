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
        loop invariant i_27: 0 <= i <= a;

        loop invariant i_28: 0 <= j <= b;

        loop invariant i_29: 0 <= k <= a + b;

        loop invariant i_30: k == i + j;

        loop invariant i_31: Sorted(res, 0, k);

        loop invariant i_32: i < a ==> (k > 0 ==> res[k-1] <= A[i]);

        loop invariant i_33: j < b ==> (k > 0 ==> res[k-1] <= B[j]);

        loop invariant i_44: i < a ==> (k == 0 || res[k-1] <= A[i]);

        loop invariant i_45: j < b ==> (k == 0 || res[k-1] <= B[j]);


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
        loop invariant i_13: 0 <= i <= a;

        loop invariant i_14: 0 <= j <= b;

        loop invariant i_15: 0 <= k <= a + b;

        loop invariant i_16: k == i + j;

        loop invariant i_17: Sorted(res, 0, k);

        loop invariant i_18: Sorted(A, 0, a);

        loop invariant i_19: Sorted(B, 0, b);

        loop invariant i_20: a > 0;

        loop invariant i_21: b > 0;

        loop invariant i_22: \valid(A + (0..a - 1));

        loop invariant i_23: \valid(B + (0..b - 1));

        loop invariant i_24: \valid(res + (0..a + b - 1));

        loop invariant i_25: \separated(&A[0..(a-1)], &B[0..(b-1)], &res[0..(a+b-1)]);

        loop invariant i_26: i < a ==> (k > 0 && res[k-1] <= A[i]);

        loop invariant i_34: 0 <= i && i <= a;

        loop invariant i_35: i + j == k;

        loop invariant i_36: k > 0;

        loop invariant i_37: Sorted(res, 0, k) || k == 0;

        loop invariant i_38: i < a ==> res[k-1] <= A[i];

        loop invariant i_39: 0 <= j && j <= b;

        loop invariant i_40: i < a ==> (k > 0 ==> res[k-1] <= A[i]);

        loop invariant i_41: j < b ==> (k > 0 ==> res[k-1] <= B[j]);

        loop invariant i_42: 0 <= k && k <= a + b;

        loop invariant i_43: (i < a) ==> ((k > 0) ==> res[k-1] <= A[i]);

        loop invariant i_46: i < a ==> (k == 0 || res[k-1] <= A[i]);

        loop invariant i_47: i < a && k > 0 ==> res[k-1] <= A[i];

        loop invariant i_49: i < a ==> j >= b;


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
        loop invariant i_0: 0 <= j <= b;

        loop invariant i_1: a <= k <= a + b;

        loop invariant i_2: k - a == j;

        loop invariant i_3: Sorted(res, 0, k);

        loop invariant i_4: Sorted(A, 0, a);

        loop invariant i_5: Sorted(B, 0, b);

        loop invariant i_6: a > 0;

        loop invariant i_7: b > 0;

        loop invariant i_8: \valid(A + (0..a - 1));

        loop invariant i_9: \valid(B + (0..b - 1));

        loop invariant i_10: \valid(res + (0..a + b - 1));

        loop invariant i_11: \separated(&A[0..(a-1)], &B[0..(b-1)], &res[0..(a+b-1)]);

        loop invariant i_12: j < b ==> res[k-1] <= B[j];

        loop invariant i_48: j < b ==> (k > 0 ==> res[k-1] <= B[j]);

        loop invariant i_50: 0 <= j;

        loop invariant i_51: j <= b;

        loop invariant i_52: a <= k;

        loop invariant i_53: k <= a + b;

        loop invariant i_54: k == a + j;

        loop invariant i_55: k == 0 || Sorted(res, 0, k);

        loop invariant i_56: 0 <= j && j <= b;

        loop invariant i_57: a <= k && k <= a + b;

        loop invariant i_58: k - j == a;

        loop invariant i_59: Sorted(res, 0, k) && 0 <= k && k <= a + b;

        loop invariant i_60: j < b ==> (k > 0 && res[k-1] <= B[j]);

        loop invariant i_61: \forall integer u; 0 <= u < a ==> A[u] == \at(A[u],End_l);

        loop invariant i_62: \forall integer v; 0 <= v < b ==> B[v] == \at(B[v],End_l);

        loop invariant i_63: 0 <= j && j < b + 1;

        loop invariant i_64: a <= k && k < a + b + 1;

        loop invariant i_65: j == k - a;

        loop invariant i_66: Sorted(res, 0, k) && k >= a;

        loop invariant i_67: j < b ==> (k >= 1 && res[k-1] <= B[j]);


        loop assigns res[0..a + b - 1];
        loop assigns j, k;
    */
    while (j < b) {
        res[k] = B[j];
        k = k + 1;
        j = j + 1;
    }
}