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
        loop invariant i_33: 1 <= i <= n;

        loop invariant i_34: 1 <= j <= i;

        loop invariant i_35: \exists integer mv; 0 <= mv < 1 || i >= 2 && j >= 1;


        loop assigns i, j, mv, t[0..n-1];
     */
    for (i = 1; i < n; i++) {
        mv = t[i];
        // Loop B
        /*@
            loop invariant i_36: 1 <= i <= n;

            loop invariant i_37: 1 <= j <= i;

            loop invariant i_38: \exists integer mv; 0 <= mv < 1 || i >= 2 && j >= 1;


            loop assigns j, t[0..i];
         */
        for (j = i; j > 0; j--) {
            if (t[j - 1] <= mv) break;
            t[j] = t[j - 1];
        }
        t[j] = mv;
    }
}