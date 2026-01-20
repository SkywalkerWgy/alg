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
        loop invariant i_36: k >= 1;

        loop invariant i_37: k < n;

        loop invariant i_38: i >= l;

        loop invariant i_39: i < n;

        loop invariant i_40: 1 <= k ==> n >= 2;


        loop assigns k, i;
    */
    for (k = 1; k < n; k++) {

        // Loop B
        /*@
            loop invariant i_46: k >= 1;

            loop invariant i_47: k < n;

            loop invariant i_48: i >= l;

            loop invariant i_49: i < n;

            loop invariant i_50: 1 <= k ==> n >= 2;


            loop assigns i;
        */
        for (i = l; i < n; i++) {

        }

        // Loop C
        /*@
            loop invariant i_41: k >= 1;

            loop invariant i_42: k < n;

            loop invariant i_43: i >= l;

            loop invariant i_44: i < n;

            loop invariant i_45: 1 <= k ==> n >= 2;


            loop assigns k, i;
        */
        for (i = l; i < n; i++) {
            //@ assert  a_1: 1 <= k;
        }
    }
}
