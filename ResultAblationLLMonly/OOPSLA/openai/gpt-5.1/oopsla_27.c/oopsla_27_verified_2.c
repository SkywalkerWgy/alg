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
        loop invariant i_0: 1 <= k;

        loop invariant i_7: l > 0;

        loop invariant i_8: 1 <= k <= n;


        loop assigns k, i;
    */
    for (k = 1; k < n; k++) {

        // Loop B
        /*@
            loop invariant i_1: l > 0;

            loop invariant i_2: 1 <= k;

            loop invariant i_3: l <= i <= n;

            loop invariant i_9: 1 <= k && k <= n;

            loop invariant i_10: l <= i && i <= n;


            loop assigns i;
        */
        for (i = l; i < n; i++) {

        }

        // Loop C
        /*@
            loop invariant i_4: l > 0;

            loop invariant i_5: 1 <= k;

            loop invariant i_6: l <= i <= n;

            loop invariant i_11: 1 <= k && k <= n;

            loop invariant i_12: l <= i;


            loop assigns k, i;
        */
        for (i = l; i < n; i++) {
            //@ assert  a_1: 1 <= k;
        }
    }
}
