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
        loop invariant i_42: 1 <= k && k < n;

        loop invariant i_43: 1 <= i && i < n;


        loop assigns k, i;
    */
    for (k = 1; k < n; k++) {

        // Loop B
        /*@
            loop invariant i_46: 1 <= i && i < n;

            loop invariant i_47: 1 <= k && k < n;


            loop assigns i;
        */
        for (i = l; i < n; i++) {

        }

        // Loop C
        /*@
            loop invariant i_44: 1 <= k && k < n;

            loop invariant i_45: 1 <= i && i < n;


            loop assigns k, i;
        */
        for (i = l; i < n; i++) {
            //@ assert  a_1: 1 <= k;
        }
    }
}
