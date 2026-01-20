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
        loop invariant i_3: \forall integer k; i <= k < n ==> t[k] == \at(t[k], Pre);
        loop invariant i_4: \valid(t+(0..n-1));

        loop assigns i, j, mv, t[0..n-1];
     */
    for (i = 1; i < n; i++) {
        mv = t[i];
        // Loop B
        /*@
            loop invariant i_6: 0 <= j <= i;
            loop invariant i_8: (j < i) ==> \forall integer k; 0 < k < j ==> t[k-1] <= t[k];
            loop invariant i_14: \forall integer k; j <= k < i ==> mv < t[k];
            loop invariant i_18: \forall integer k; j <= k < i ==> t[k] >= mv;
            loop invariant i_26: (j < i) ==> (mv < t[j]);

            loop assigns j, t[0..i];
         */
        for (j = i; j > 0; j--) {
            if (t[j - 1] <= mv) break;
            t[j] = t[j - 1];
        }
        t[j] = mv;
    }
}