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
        loop invariant i_50: i, j, k;

        loop invariant i_51: i < n && j >= i;

        loop invariant i_52: j < m;

        loop invariant i_53: k >= 0;


        loop assigns n, m, k, j, i;
    */
    for (i = 0; i < n; i += 4) {

        // Loop B
        /*@
            loop invariant i_58: i, j, k;

            loop invariant i_59: i < n && j >= i;

            loop invariant i_60: j < m;

            loop invariant i_61: k >= 0;

            loop invariant i_62: k == j;

            loop invariant i_63: j >= 0 && k <= j;

            loop invariant i_64: i < n && j >= i && j < m && k >= 0;


            loop assigns k, j;
        */
        for (j = i; j < m;) {
            if (unknown1()) {
                //@ assert j >= 0;
                j++;
                k = 0;

                // Loop C
                /*@
                    loop invariant i_54: i, j, k;

                    loop invariant i_55: j >= 0 && k <= j;

                    loop invariant i_56: i < n && j >= i && j < m && k >= 0;

                    loop invariant i_57: k == j;


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
