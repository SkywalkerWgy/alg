#include <assert.h>
int unknown1();

/*
 * "nest-if8" from InvGen benchmark suite
 */

/*@
    requires m + 1 < n;
*/
void oopsla_31(int i, int j, int k, int n, int m) {
    // Loop A
    /*@
        loop invariant i_30: n + j + k >= i;

        loop invariant i_31: j >= 0;

        loop invariant i_32: k >= 0;

        loop invariant i_33: i + 4 <= j && j >= 0 && j < m;

        loop invariant i_34: k <= j;


        loop assigns n, m, k, j, i;
    */
    for (i = 0; i < n; i += 4) {

        // Loop B
        /*@
            loop invariant i_42: n + j + k >= i;

            loop invariant i_43: j >= 0;

            loop invariant i_44: k >= 0;

            loop invariant i_45: i + 4 <= j && j >= 0 && j < m;

            loop invariant i_46: k <= j;

            loop invariant i_47: j >= i && j < m;

            loop invariant i_48: i >= 0;

            loop invariant i_49: m >= j;


            loop assigns k, j;
        */
        for (j = i; j < m;) {
            if (unknown1()) {
                //@ assert j >= 0;
                j++;
                k = 0;

                // Loop C
                /*@
                    loop invariant i_35: j >= i && j < m;

                    loop invariant i_36: k <= j;

                    loop invariant i_37: i + 4 <= j && j >= 0 && j < m;

                    loop invariant i_38: n + j + k >= i;

                    loop invariant i_39: i >= 0;

                    loop invariant i_40: m >= j;

                    loop invariant i_41: k >= 0;


                    loop assigns k;
                */
                while (k < j) {
                    k++;
                }
            } else {
                //@ assert  a_1: n + j + 5 > i;
                j += 2;
            }
        }
    }
}
