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
        loop invariant i_22: 1 <= i <= n;

        loop invariant i_23: Sorted(t, 0, i);

        loop invariant i_24: \forall integer k; 0 <= k < i ==> t[k] == \at(t[k], Pre);

        loop invariant i_25: \forall integer k, l; 0 <= k < l < i ==> t[k] <= t[l];


        loop assigns i, j, mv, t[0..n-1];
     */
    for (i = 1; i < n; i++) {
        mv = t[i];
        // Loop B
        /*@
            loop invariant i_26: 0 <= j <= i;

            loop invariant i_27: \forall integer k; j <= k <= i ==> t[k] == \at(t[k], Pre);

            loop invariant i_28: \forall integer k; 0 <= k < j ==> t[k] <= mv;

            loop invariant i_29: \forall integer k, l; 0 <= k < l < j ==> t[k] <= t[l];

            loop invariant i_30: \forall integer k, l; j <= k < l <= i ==> t[k] <= t[l];


            loop assigns j, t[0..i];
         */
        for (j = i; j > 0; j--) {
            if (t[j - 1] <= mv) break;
            t[j] = t[j - 1];
        }
        t[j] = mv;
    }
}