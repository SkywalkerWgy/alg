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

        loop invariant i_1: j >= i && j <= i;

        loop invariant i_2: mv == t[i];

        loop invariant i_4: t[j] == mv;


        loop assigns i, j, mv, t[0..n-1];
     */
    for (i = 1; i < n; i++) {
        mv = t[i];
        // Loop B
        /*@
            loop invariant i_6: 1 <= j <= i;

            loop invariant i_7: mv == t[i];

            loop invariant i_9: t[j] == mv;

            loop invariant i_11: 1 <= i <= n;

            loop invariant i_12: j >= i && j <= i;


            loop assigns j, t[0..i];
         */
        for (j = i; j > 0; j--) {
            if (t[j - 1] <= mv) break;
            t[j] = t[j - 1];
        }
        t[j] = mv;
    }
}