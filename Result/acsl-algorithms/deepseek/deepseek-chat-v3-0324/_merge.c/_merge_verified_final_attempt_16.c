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
        loop invariant i_2: 0 <= k <= a + b;
        loop invariant i_3: k == i + j;
        loop invariant i_5: \forall integer m; 0 <= m < i ==> A[m] <= res[k-1];
        loop invariant i_6: \forall integer m; 0 <= m < j ==> B[m] <= res[k-1];
        loop invariant i_28: (i > 0 && j > 0) ==> (A[i-1] <= B[j] || B[j-1] <= A[i]);
        loop invariant i_41: \forall integer m; 0 <= m < j ==> B[m] <= (i < a ? A[i] : B[j]);
        loop invariant i_42: \forall integer m; 0 <= m < i ==> A[m] <= (j < b ? B[j] : A[i]);
        loop invariant i_52: (j > 0 && i < a) ==> B[j-1] <= A[i];
        loop invariant i_53: \forall integer m; 0 <= m < i ==> A[m] <= (i < a ? A[i] : B[j]);
        loop invariant i_54: \forall integer m; 0 <= m < j ==> B[m] <= (j < b ? B[j] : A[i]);
        loop invariant i_55: (i < a && j < b) ==> (A[i] <= B[j] || B[j] <= A[i]);
        loop invariant i_56: i > 0 ==> A[i-1] <= (i < a ? A[i] : B[j]);
        loop invariant i_57: j > 0 ==> B[j-1] <= (j < b ? B[j] : A[i]);
        loop invariant i_59: i < a ==> \forall integer m; 0 <= m < i ==> A[m] <= A[i];
        loop invariant i_60: j < b ==> \forall integer m; 0 <= m < j ==> B[m] <= B[j];
        loop invariant i_72: i < a ==> (i == 0 || A[i-1] <= A[i]);
        loop invariant i_73: j < b ==> (j == 0 || B[j-1] <= B[j]);
        loop invariant i_88: (i < a && j < b) ==> (A[i] <= B[j]) || (B[j] <= A[i]);
        loop invariant i_89: (i < a) ==> \forall integer m; 0 <= m < i ==> A[m] <= A[i];
        loop invariant i_90: (j < b) ==> \forall integer m; 0 <= m < j ==> B[m] <= B[j];
        loop invariant i_104: \forall integer m; 0 <= m < i ==> (m == 0 || A[m-1] <= A[m]);
        loop invariant i_105: \forall integer m; 0 <= m < i ==> (m == i-1 || A[m] <= A[m+1]);
        loop invariant i_106: \forall integer m; 0 <= m < i-1 ==> A[m] <= A[i-1];
        loop invariant i_107: i <= 1 || A[i-2] <= A[i-1];
        loop invariant i_108: \forall integer m; 0 <= m < j ==> (j < b ==> B[m] <= B[j]);
        loop invariant i_109: j == b || \forall integer m; 0 <= m < j ==> B[m] <= B[j];
        loop invariant i_110: \forall integer m; 0 <= m < j ==> (m < j-1 ==> B[m] <= B[j-1]);
        loop invariant i_116: (i == a || j == b) || (i < a && j < b);
        loop invariant i_118: k == 0 ==> (i == 0 && j == 0);

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
        loop invariant i_8: 0 <= i <= a;
        loop invariant i_9: 0 <= k <= a + b;
        loop invariant i_10: k == \at(k, End_l) + (i - \at(i, End_l));
        loop invariant i_12: \forall integer m; 0 <= m < i ==> A[m] <= res[k-1];
        loop invariant i_13: \forall integer m; \at(i, End_l) <= m < i ==> A[m] == res[\at(k, End_l) + (m - \at(i, End_l))];
        loop invariant i_14: \forall integer m; 0 <= m < \at(j, End_l) ==> B[m] <= res[k-1];
        loop invariant i_15: \forall integer m; 0 <= m < \at(k, End_l) ==> res[m] == \at(res[m], End_l);
        loop invariant i_24: \at(j, End_l) == j;
        loop invariant i_33: \forall integer m; \at(k, End_l) <= m < k ==> res[m] == A[\at(i, End_l) + (m - \at(k, End_l))];
        loop invariant i_47: j == \at(j, End_l);
        loop invariant i_48: \at(k, End_l) <= k;
        loop invariant i_62: \forall integer m; 0 <= m < \at(k, End_l) ==> res[m] <= res[\at(k, End_l)-1];
        loop invariant i_63: \at(k, End_l) <= k <= \at(k, End_l) + (a - \at(i, End_l));
        loop invariant i_70: \at(j, End_l) == b || i == a;
        loop invariant i_76: \forall integer m; \at(i, End_l) <= m <= i ==> A[m] <= A[i] || i == a;
        loop invariant i_77: i == 0 || \forall integer m; \at(i, End_l) <= m < i ==> A[m] <= A[i];
        loop invariant i_78: \forall integer m; \at(k, End_l) <= m < k ==> res[m] <= A[i-1];
        loop invariant i_79: i > \at(i, End_l) ==> A[i-1] <= A[i];
        loop invariant i_83: \at(k, End_l) == 0 || \forall integer m; 0 <= m < \at(k, End_l) ==> res[m] <= res[\at(k, End_l)-1];
        loop invariant i_91: \forall integer m; \at(i, End_l) <= m < i ==> (m < i - 1 ==> A[m] <= A[i-1]);
        loop invariant i_92: \forall integer m; \at(k, End_l) <= m < k ==> res[m] <= res[k-1];
        loop invariant i_93: \forall integer m; 0 <= m < \at(i, End_l) ==> A[m] <= (i < a ? A[i] : B[\at(j, End_l)]);
        loop invariant i_96: \at(i, End_l) < a ==> A[\at(i, End_l)] <= (i < a ? A[i] : B[\at(j, End_l)]);
        loop invariant i_97: \forall integer m; 0 <= m < i ==> A[m] <= (i < a ? A[i] : B[\at(j, End_l)]);
        loop invariant i_103: \at(i, End_l) == a || \at(j, End_l) == b;

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
        loop invariant i_16: 0 <= j <= b;
        loop invariant i_20: \forall integer m; 0 <= m < j ==> B[m] <= res[k-1];
        loop invariant i_22: \forall integer m; 0 <= m < \at(i, End_l) ==> A[m] <= res[k-1];
        loop invariant i_23: \forall integer m; 0 <= m < \at(k, End_l) ==> res[m] == \at(res[m], End_l);
        loop invariant i_39: \at(k, End_l) <= k;
        loop invariant i_49: \at(j, End_l) <= j;
        loop invariant i_64: \at(j, End_l) <= j <= b;
        loop invariant i_66: \forall integer m; \at(j, End_l) <= m < j ==> res[\at(k, End_l) + (m - \at(j, End_l))] == B[m];
        loop invariant i_68: \forall integer m; \at(j, End_l) <= m < j ==> B[m] <= res[k-1];
        loop invariant i_71: \at(j, End_l) < b ==> \at(i, End_l) == a;
        loop invariant i_84: \forall integer m; \at(j, End_l) <= m < j ==> B[m] == res[\at(k, End_l) + (m - \at(j, End_l))] && (m < j - 1 ==> res[\at(k, End_l) + (m - \at(j, End_l))] <= B[j-1]);
        loop invariant i_98: \forall integer m; \at(j, End_l) <= m < j ==> (m < j - 1 ==> B[m] <= B[j-1]);
        loop invariant i_112: \forall integer m; \at(j, End_l) <= m < j ==> (j < b ==> res[\at(k, End_l) + (m - \at(j, End_l))] <= B[j]);
        loop invariant i_115: \forall integer m; \at(k, End_l) <= m < k ==> res[m] <= B[j-1];

        loop assigns res[0..a + b - 1];
        loop assigns j, k;
    */
    while (j < b) {
        res[k] = B[j];
        k = k + 1;
        j = j + 1;
    }
}