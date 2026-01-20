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
        loop invariant i_51: 1 <= k;

        loop invariant i_52: 1 <= i;


        loop assigns k, i;
    */
    for (k = 1; k < n; k++) {

        // Loop B
        /*@
            loop invariant i_54: 1 <= k;

            loop invariant i_55: 1 <= i;


            loop assigns i;
        */
        for (i = l; i < n; i++) {

        }

        // Loop C
        /*@
            loop invariant i_53: 1 <= k;


            loop assigns k, i;
        */
        for (i = l; i < n; i++) {
            //@ assert  a_1: 1 <= k;
        }
    }
}
