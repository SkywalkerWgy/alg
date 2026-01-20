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
        loop invariant i_0: 1 <= k && k < n;

        loop invariant i_1: l <= i && i < n;

        loop invariant i_2: k <= i;


        loop assigns k, i;
    */
    for (k = 1; k < n; k++) {

        // Loop B
        /*@
            loop invariant i_12: 1 <= k && k < n;

            loop invariant i_13: l <= i && i < n;

            loop invariant i_14: k <= i;

            loop invariant i_15: 1 <= k;

            loop invariant i_16: i >= l;

            loop invariant i_17: k <= n - 1;

            loop invariant i_18: i <= n - 1;


            loop assigns i;
        */
        for (i = l; i < n; i++) {

        }

        // Loop C
        /*@
            loop invariant i_3: 1 <= k && k < n;

            loop invariant i_4: l <= i && i < n;

            loop invariant i_5: k <= i;

            loop invariant i_6: 1 <= k;

            loop invariant i_7: 1 <= i;

            loop invariant i_8: k >= 1;

            loop invariant i_9: i >= l;

            loop invariant i_10: k <= n - 1;

            loop invariant i_11: i <= n - 1;


            loop assigns k, i;
        */
        for (i = l; i < n; i++) {
            //@ assert  a_1: 1 <= k;
        }
    }
}
