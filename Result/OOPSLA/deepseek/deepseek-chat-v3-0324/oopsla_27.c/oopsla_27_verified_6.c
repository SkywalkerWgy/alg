#include <assert.h>

/*
 * "nested2.c" from InvGen benchmark suite
 */

/*@
    requires l > 0;
*/
void oopsla_27(int l, int i, int k, int n) {

    // Loop A
    /*@
        loop invariant i_0: 1 <= k <= n;

        loop invariant i_1: l <= i <= n;

        loop invariant i_2: \forall integer j; 1 <= j < k ==> \forall integer m; l <= m < n;

        loop invariant i_10: l <= i;

        loop invariant i_11: k == 1;

        loop invariant i_13: 0 <= k <= n;

        loop invariant i_14: k >= 1;

        loop invariant i_16: k >= 0;

        loop invariant i_17: l <= n;

        loop invariant i_18: \forall integer j; 1 <= j < k+1 ==> \forall integer m; l <= m < n;

        loop invariant i_22: \forall integer j; 1 <= j < k+1 ==> \forall integer m; l <= m < n ==> m >= l && m < n;


        loop assigns k, i;
    */
    for (k = 1; k < n; k++) {

        // Loop B
        /*@
            loop invariant i_4: l <= i <= n;

            loop invariant i_5: \forall integer j; 1 <= j < k ==> \forall integer m; l <= m < n;

            loop invariant i_15: i == n;

            loop invariant i_19: i == l;

            loop invariant i_20: \forall integer j; 1 <= j < k+1 ==> \forall integer m; l <= m < n;


            loop assigns i;
        */
        for (i = l; i < n; i++) {

        }

        // Loop C
        /*@
            loop invariant i_7: l <= i <= n;

            loop invariant i_8: \forall integer j; 1 <= j < k ==> \forall integer m; l <= m < n;

            loop invariant i_9: 1 <= k <= n;

            loop invariant i_12: \forall integer j; 1 <= j < k+1 ==> \forall integer m; l <= m < n;


            loop assigns k, i;
        */
        for (i = l; i < n; i++) {
            //@ assert  a_1: 1 <= k;
        }
    }
}
