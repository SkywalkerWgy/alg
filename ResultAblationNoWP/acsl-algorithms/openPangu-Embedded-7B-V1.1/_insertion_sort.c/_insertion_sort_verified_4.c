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
        loop invariant i_19: 1 <= i <= n;

        loop invariant i_20: j >= 1;

        loop invariant i_21: \exists integer k; 0 <= k < i && \max_{p=0}^{i-1} t[p] == t[i];

        loop invariant i_22: t[0] <= t[i] && t[0] <= t[j] && t[j] == \max_{p=0}^{i-1} t[p];

        loop invariant i_23: t[0..i-1] is sorted in non-decreasing order;

        loop invariant i_24: t[i+1..n-1] is sorted in non-decreasing order and all elements are unchanged from the initial state;

        loop invariant i_25: \forall integer p, i; 0 <= p < j && p >= i ==> t[p] == t[i];


        loop assigns i, j, mv, t[0..n-1];
     */
    for (i = 1; i < n; i++) {
        mv = t[i];
        // Loop B
        /*@
            loop invariant i_26: 1 <= i <= n;

            loop invariant i_27: j >= 1;

            loop invariant i_28: \exists integer k; 0 <= k < i && \max_{p=0}^{i-1} t[p] == t[i];

            loop invariant i_29: t[0] <= t[i] && t[0] <= t[j] && t[j] == \max_{p=0}^{i-1} t[p];

            loop invariant i_30: t[0..i-1] is sorted in non-decreasing order;

            loop invariant i_31: t[i+1..n-1] is sorted in non-decreasing order and all elements are unchanged from the initial state;

            loop invariant i_32: \forall integer p, i; 0 <= p < j && p >= i ==> t[p] == t[i];


            loop assigns j, t[0..i];
         */
        for (j = i; j > 0; j--) {
            if (t[j - 1] <= mv) break;
            t[j] = t[j - 1];
        }
        t[j] = mv;
    }
}