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
        loop invariant i_42: 1 <= i <= n;

        loop invariant i_43: Sorted(t, 0, i);

        loop invariant i_44: \forall integer k; i <= k < n ==> t[k] == \at(t[k], Pre);

        loop invariant i_45: \forall integer k, l; 0 <= k < l < i ==> t[k] <= t[l];


        loop assigns i, j, mv, t[0..n-1];
     */
    for (i = 1; i < n; i++) {
        mv = t[i];
        // Loop B
        /*@
            loop invariant i_46: 0 <= j <= i;

            loop invariant i_47: \forall integer k; 0 <= k < j ==> t[k] <= mv;

            loop invariant i_48: \forall integer k; j < k <= i ==> t[k] > mv;

            loop invariant i_49: \forall integer k, l; 0 <= k < l < j ==> t[k] <= t[l];

            loop invariant i_50: \forall integer k, l; j <= k < l <= i ==> t[k] > t[l];

            loop invariant i_51: mv == \at(t[i], Pre);

            loop invariant i_52: \forall integer k; i < k < n ==> t[k] == \at(t[k], Pre);


            loop assigns j, t[0..i];
         */
        for (j = i; j > 0; j--) {
            if (t[j - 1] <= mv) break;
            t[j] = t[j - 1];
        }
        t[j] = mv;
    }
}