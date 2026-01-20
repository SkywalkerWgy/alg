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
        loop invariant i_23: 1 <= k && k < n;

        loop invariant i_24: l <= i && i < n;

        loop invariant i_25: 1 <= k;


        loop assigns k, i;
    */
    for (k = 1; k < n; k++) {

        // Loop B
        /*@
            loop invariant i_29: 1 <= k && k < n;

            loop invariant i_30: l <= i && i < n;

            loop invariant i_31: 1 <= k;


            loop assigns i;
        */
        for (i = l; i < n; i++) {

        }

        // Loop C
        /*@
            loop invariant i_26: 1 <= k && k < n;

            loop invariant i_27: l <= i && i < n;

            loop invariant i_28: 1 <= k;


            loop assigns k, i;
        */
        for (i = l; i < n; i++) {
            //@ assert  a_1: 1 <= k;
        }
    }
}
