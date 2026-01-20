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
        loop invariant i_14: 1 <= k && k < n;

        loop invariant i_15: l <= i && i < n;

        loop invariant i_16: 1 <= k && k <= i && i < n;


        loop assigns k, i;
    */
    for (k = 1; k < n; k++) {

        // Loop B
        /*@
            loop invariant i_20: 1 <= k && k < n;

            loop invariant i_21: l <= i && i < n;

            loop invariant i_22: 1 <= k && k <= i && i < n;


            loop assigns i;
        */
        for (i = l; i < n; i++) {

        }

        // Loop C
        /*@
            loop invariant i_17: 1 <= k && k < n;

            loop invariant i_18: l <= i && i < n;

            loop invariant i_19: 1 <= k && k <= i && i < n;


            loop assigns k, i;
        */
        for (i = l; i < n; i++) {
            //@ assert  a_1: 1 <= k;
        }
    }
}
