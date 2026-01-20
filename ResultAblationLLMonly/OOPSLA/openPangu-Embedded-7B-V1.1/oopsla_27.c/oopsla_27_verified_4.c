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
        loop invariant i_32: k < n;

        loop invariant i_33: i >= 0;

        loop invariant i_34: i < n;

        loop invariant i_35: 1 <= k;

        loop invariant i_36: i >= l;


        loop assigns k, i;
    */
    for (k = 1; k < n; k++) {

        // Loop B
        /*@
            loop invariant i_39: i >= 0;

            loop invariant i_40: 1 <= k;

            loop invariant i_41: k <= n - 1;


            loop assigns i;
        */
        for (i = l; i < n; i++) {

        }

        // Loop C
        /*@
            loop invariant i_37: 1 <= k;

            loop invariant i_38: k <= n - 1;


            loop assigns k, i;
        */
        for (i = l; i < n; i++) {
            //@ assert  a_1: 1 <= k;
        }
    }
}
