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
        loop invariant i_11: i + j + k <= n;

        loop invariant i_12: k >= 0 && j >= i;

        loop invariant i_13: k <= j;

        loop invariant i_14: j >= 0 && j < m;

        loop invariant i_15: i % 4 == 0;


        loop assigns n, m, k, j, i;
    */
    for (i = 0; i < n; i += 4) {

        // Loop B
        /*@
            loop invariant i_23: k >= 0 && k < j;

            loop invariant i_24: j >= i;

            loop invariant i_25: k <= j;

            loop invariant i_26: i + j + k <= n;

            loop invariant i_27: k <= j && j >= i;

            loop invariant i_28: j >= 0 && j < m;

            loop invariant i_29: i % 4 == 0;


            loop assigns k, j;
        */
        for (j = i; j < m;) {
            if (unknown1()) {
                //@ assert j >= 0;
                j++;
                k = 0;

                // Loop C
                /*@
                    loop invariant i_16: k >= 0 && k < j;

                    loop invariant i_17: j >= i;

                    loop invariant i_18: k <= j;

                    loop invariant i_19: i + j + k <= n;

                    loop invariant i_20: k <= j && j >= i;

                    loop invariant i_21: j >= 0 && j < m;

                    loop invariant i_22: i % 4 == 0;


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
