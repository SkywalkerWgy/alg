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
        loop invariant i_31: 1 <= i <= n;

        loop invariant i_32: Sorted(t, 0, i);

        loop invariant i_33: \forall integer k; i <= k < n ==> t[k] == \at(t[k], Pre);

        loop invariant i_34: \forall integer k1, k2; 0 <= k1 < i && i <= k2 < n ==> t[k1] <= t[k2];


        loop assigns i, j, mv, t[0..n-1];
     */
    for (i = 1; i < n; i++) {
        mv = t[i];
        // Loop B
        /*@
            loop invariant i_35: 0 <= j <= i;

            loop invariant i_36: j == i || t[j] <= mv;

            loop invariant i_37: \forall integer k; j <= k < i ==> t[k] > mv;

            loop invariant i_38: \forall integer k; 0 <= k < j ==> t[k] == \at(t[k], Pre);

            loop invariant i_39: \forall integer k; j < k <= i ==> t[k] == \at(t[k-1], Pre);

            loop invariant i_40: Sorted(t, 0, j);

            loop invariant i_41: \forall integer k1, k2; 0 <= k1 < j && i <= k2 < n ==> t[k1] <= t[k2];


            loop assigns j, t[0..i];
         */
        for (j = i; j > 0; j--) {
            if (t[j - 1] <= mv) break;
            t[j] = t[j - 1];
        }
        t[j] = mv;
    }
}