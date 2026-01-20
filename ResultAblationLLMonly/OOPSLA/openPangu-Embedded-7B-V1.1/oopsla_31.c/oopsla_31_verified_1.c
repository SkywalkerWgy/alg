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
        loop invariant i_0: i + 4 * j < n;

        loop invariant i_1: k >= 0 && k <= j;

        loop invariant i_2: m >= n + 1;


        loop assigns n, m, k, j, i;
    */
    for (i = 0; i < n; i += 4) {

        // Loop B
        /*@
            loop invariant i_7: k >= 0 && k <= j;

            loop invariant i_8: i + 4 * j < n;

            loop invariant i_9: m >= n + 1;

            loop invariant i_10: k == j;

            loop invariant i_11: k < j || k == j;

            loop invariant i_12: j >= 0;


            loop assigns k, j;
        */
        for (j = i; j < m;) {
            if (unknown1()) {
                //@ assert j >= 0;
                j++;
                k = 0;

                // Loop C
                /*@
                    loop invariant i_3: k >= 0 && k <= j;

                    loop invariant i_4: k == j;

                    loop invariant i_5: k < j || k == j;

                    loop invariant i_6: j >= 0;


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
