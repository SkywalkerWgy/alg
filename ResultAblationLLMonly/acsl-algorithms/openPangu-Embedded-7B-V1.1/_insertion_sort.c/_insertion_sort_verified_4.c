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
        loop invariant i_20: 1 <= i <= n && 0 <= j <= i && \forall integer k in [0, i-1]; t[k] <= t[i];

        loop invariant i_21: j >= 0 && j <= i-1 && \forall integer k in [j, i-1]; t[k] <= t[i];

        loop invariant i_22: 0 <= j <= i && \forall integer k in [0, j]; t[k] <= t[j];


        loop assigns i, j, mv, t[0..n-1];
     */
    for (i = 1; i < n; i++) {
        mv = t[i];
        // Loop B
        /*@
            loop invariant i_23: 1 <= j <= i && \forall integer k in [j, i-1]; t[k] <= t[i];

            loop invariant i_24: 0 <= j && j <= i-1;

            loop invariant i_25: \exists integer mv; t[j] == mv && \forall integer k in [0, j-1]; t[k] <= t[j];


            loop assigns j, t[0..i];
         */
        for (j = i; j > 0; j--) {
            if (t[j - 1] <= mv) break;
            t[j] = t[j - 1];
        }
        t[j] = mv;
    }
}