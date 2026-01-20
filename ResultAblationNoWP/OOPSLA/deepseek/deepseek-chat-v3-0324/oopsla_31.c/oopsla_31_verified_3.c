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
        loop invariant i_16: i % 4 == 0;

        loop invariant i_17: i >= 0;

        loop invariant i_18: i <= n;

        loop invariant i_19: m + 1 < n;


        loop assigns n, m, k, j, i;
    */
    for (i = 0; i < n; i += 4) {

        // Loop B
        /*@
            loop invariant i_22: i <= j <= m;

            loop invariant i_23: i % 4 == 0;

            loop invariant i_24: i >= 0;

            loop invariant i_25: i <= n;

            loop invariant i_26: m + 1 < n;


            loop assigns k, j;
        */
        for (j = i; j < m;) {
            if (unknown1()) {
                //@ assert j >= 0;
                j++;
                k = 0;

                // Loop C
                /*@
                    loop invariant i_20: 0 <= k <= j;

                    loop invariant i_21: k >= 0;


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
