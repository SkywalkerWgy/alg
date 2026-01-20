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
        loop invariant i_0: s for Loop A: ``` loop invariant 1 <= i <= n;

        loop invariant i_1: 1 <= i <= n;

        loop invariant i_2: Sorted(t, 0, i);

        loop invariant i_3: \forall integer k; i <= k < n ==> t[k] == \at(t[k], Pre);

        loop invariant i_4: \forall integer k, l; 0 <= k < i <= l < n ==> t[k] <= t[l];


        loop assigns i, j, mv, t[0..n-1];
     */
    for (i = 1; i < n; i++) {
        mv = t[i];
        // Loop B
        /*@
            loop invariant i_5: s for Loop B: ``` loop invariant 0 <= j <= i;

            loop invariant i_6: 0 <= j <= i;

            loop invariant i_7: \forall integer k; j <= k < i ==> t[k] > mv;

            loop invariant i_8: \forall integer k; 0 <= k < j ==> t[k] <= mv;

            loop invariant i_9: Sorted(t, 0, j);

            loop invariant i_10: \forall integer k; j < k <= i ==> t[k] == \at(t[k-1], LoopEntry);


            loop assigns j, t[0..i];
         */
        for (j = i; j > 0; j--) {
            if (t[j - 1] <= mv) break;
            t[j] = t[j - 1];
        }
        t[j] = mv;
    }
}