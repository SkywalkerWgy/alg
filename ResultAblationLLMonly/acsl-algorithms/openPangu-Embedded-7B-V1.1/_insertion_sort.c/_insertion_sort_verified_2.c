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
        loop invariant i_7: i >= 1 && j >= i && j <= i+1 && t[i] == mv;

        loop invariant i_9: 1 <= i && i <= n-1 && t[i] == mv;

        loop invariant i_10: 1 <= j && j <= i+1 && t[j] == mv;

        loop invariant i_11: \exists integer k; 1 <= k <= i && t[k] == mv;


        loop assigns i, j, mv, t[0..n-1];
     */
    for (i = 1; i < n; i++) {
        mv = t[i];
        // Loop B
        /*@
            loop invariant i_8: 1 <= i && j >= 1 && j <= i+1 && t[j] == mv;


            loop assigns j, t[0..i];
         */
        for (j = i; j > 0; j--) {
            if (t[j - 1] <= mv) break;
            t[j] = t[j - 1];
        }
        t[j] = mv;
    }
}