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
        loop invariant i_26: l > 0 && 1 <= k && 1 <= i && i < n && k < n;


        loop assigns k, i;
    */
    for (k = 1; k < n; k++) {

        // Loop B
        /*@
            loop invariant i_31: 1 <= k && k < n && l > 0;

            loop invariant i_32: 1 <= i && i < n && l <= i;

            loop invariant i_33: k < n && k >= 1;

            loop invariant i_34: i >= l && i < n;

            loop invariant i_35: l > 0 && 1 <= k && 1 <= i && i < n && k < n;


            loop assigns i;
        */
        for (i = l; i < n; i++) {

        }

        // Loop C
        /*@
            loop invariant i_27: 1 <= k && k < n && l > 0;

            loop invariant i_28: 1 <= i && i < n && l <= i;

            loop invariant i_29: k < n && k >= 1;

            loop invariant i_30: i >= l && i < n;


            loop assigns k, i;
        */
        for (i = l; i < n; i++) {
            //@ assert  a_1: 1 <= k;
        }
    }
}
