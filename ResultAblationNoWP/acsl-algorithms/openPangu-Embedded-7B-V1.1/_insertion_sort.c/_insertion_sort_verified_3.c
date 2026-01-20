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
        loop invariant i_12: 1 <= i <= n;

        loop invariant i_13: \exists integer k; 0 <= k < i && \at(t[k], End_l) ==> t[k] == t[i];

        loop invariant i_14: \forall integer p; 0 <= p < i ==> t[p] <= t[i];


        loop assigns i, j, mv, t[0..n-1];
     */
    for (i = 1; i < n; i++) {
        mv = t[i];
        // Loop B
        /*@
            loop invariant i_15: 1 <= j <= i;

            loop invariant i_16: 1 <= i <= n;

            loop invariant i_17: \exists integer k; 0 <= k < i && \at(t[k], End_l) ==> t[k] == t[i];

            loop invariant i_18: \forall integer p; 0 <= p < i ==> t[p] <= t[i];


            loop assigns j, t[0..i];
         */
        for (j = i; j > 0; j--) {
            if (t[j - 1] <= mv) break;
            t[j] = t[j - 1];
        }
        t[j] = mv;
    }
}