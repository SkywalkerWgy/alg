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
        loop invariant i_41: 1 <= k <= n;

        loop invariant i_42: i == l;


        loop assigns k, i;
    */
    for (k = 1; k < n; k++) {

        // Loop B
        /*@
            loop invariant i_47: l <= i <= n;

            loop invariant i_48: 1 <= k <= n;

            loop invariant i_49: i == l || i > l;


            loop assigns i;
        */
        for (i = l; i < n; i++) {

        }

        // Loop C
        /*@
            loop invariant i_43: s for the third loop (Loop C): ``` loop invariant l <= i <= n;

            loop invariant i_44: l <= i <= n;

            loop invariant i_45: 1 <= k <= n;

            loop invariant i_46: i == l || i > l;


            loop assigns k, i;
        */
        for (i = l; i < n; i++) {
            //@ assert  a_1: 1 <= k;
        }
    }
}
