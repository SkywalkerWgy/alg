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
        loop invariant i_0: k < n;

        loop invariant i_1: i >= 0;

        loop invariant i_2: i < n;

        loop invariant i_3: 1 <= k;


        loop assigns k, i;
    */
    for (k = 1; k < n; k++) {

        // Loop B
        /*@
            loop invariant i_9: k < n;

            loop invariant i_10: i >= 0;

            loop invariant i_11: i < n;

            loop invariant i_12: 1 <= k;

            loop invariant i_13: k >= 1;


            loop assigns i;
        */
        for (i = l; i < n; i++) {

        }

        // Loop C
        /*@
            loop invariant i_4: 1 <= k;

            loop invariant i_5: k < n;

            loop invariant i_6: i >= 0;

            loop invariant i_7: i < n;

            loop invariant i_8: k >= 1;


            loop assigns k, i;
        */
        for (i = l; i < n; i++) {
            //@ assert  a_1: 1 <= k;
        }
    }
}
