/*@
  predicate Sorted(int *t, integer lo, integer hi) =
    \forall integer i, j; lo <= i <= j < hi ==> t[i] <= t[j];
*/

/*@ requires \valid(t+(0..(n - 1)));
    requires n > 0;
    ensures e_1: Sorted(t, 0, n);
    assigns t[0..n-1];
 */
void _insertion_sort(int t[], int n) {
    int i = 1, j = 1;
    int mv;
    
    // Loop A
    /*@
        loop invariant i_0: 1 <= i <= n;
        loop invariant i_1: Sorted(t, 0, i);
        loop invariant i_2: \forall integer k, l; 0 <= k < l < i ==> t[k] <= t[l];
        loop invariant i_3: \forall integer k; i <= k < n ==> t[k] == \at(t[k], Pre);
        loop invariant i_4: \valid(t+(0..n-1));
        loop invariant i_20: \forall integer k; 0 < k < i ==> t[k-1] <= t[k];
        loop invariant i_21: \forall integer k; 0 <= k < i ==> t[k] <= t[i];
        loop invariant i_25: i > 0 ==> t[i-1] <= t[i];
        loop invariant i_27: i <= 1 || \forall integer k; 0 <= k < i ==> t[k] <= t[i];
        loop invariant i_28: i <= 1 || t[i-1] <= t[i];

        loop assigns i, j, mv, t[0..n-1];
     */
    for (i = 1; i < n; i++) {
        mv = t[i];
        // Loop B
        /*@
            loop invariant i_6: 0 <= j <= i;
            loop invariant i_7: (j == i) ==> \forall integer k; 0 < k < i ==> t[k-1] <= t[k];
            loop invariant i_8: (j < i) ==> \forall integer k; 0 < k < j ==> t[k-1] <= t[k];
            loop invariant i_9: (j < i) ==> \forall integer k; j <= k < i ==> t[k] == \at(t[k+1], Pre);
            loop invariant i_10: (j < i) ==> \forall integer k; 0 <= k < j ==> t[k] <= mv;
            loop invariant i_12: Sorted(t, 0, j);
            loop invariant i_13: \forall integer k; 0 <= k < j ==> t[k] <= mv;
            loop invariant i_14: \forall integer k; j <= k < i ==> mv < t[k];
            loop invariant i_16: (j < i) ==> \forall integer k; j < k < i ==> t[k] == \at(t[k+1], Pre);
            loop invariant i_18: \forall integer k; j <= k < i ==> t[k] >= mv;
            loop invariant i_23: (j > 0) ==> (i == j) ==> t[j-1] > mv;
            loop invariant i_26: (j < i) ==> (mv < t[j]);
            loop invariant i_30: (j > 0) ==> (t[j-1] > mv || j == i);
            loop invariant i_31: (j > 0) ==> t[j-1] > mv || j == i;

            loop assigns j, t[0..i];
         */
        for (j = i; j > 0; j--) {
            if (t[j - 1] <= mv) break;
            t[j] = t[j - 1];
        }
        t[j] = mv;
    }
}