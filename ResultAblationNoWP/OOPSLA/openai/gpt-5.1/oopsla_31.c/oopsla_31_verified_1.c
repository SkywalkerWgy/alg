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
        loop invariant i_0: n == \at(n, Pre);

        loop invariant i_1: m == \at(m, Pre);

        loop invariant i_2: m + 1 < n;

        loop invariant i_3: 0 <= i;

        loop invariant i_4: i % 4 == 0;


        loop assigns n, m, k, j, i;
    */
    for (i = 0; i < n; i += 4) {

        // Loop B
        /*@
            loop invariant i_8: n == \at(n, Pre);

            loop invariant i_9: m == \at(m, Pre);

            loop invariant i_10: m + 1 < n;

            loop invariant i_11: 0 <= i;

            loop invariant i_12: i % 4 == 0;

            loop invariant i_13: i < n;

            loop invariant i_14: j >= i;

            loop invariant i_15: j >= 0;

            loop invariant i_16: i >= m ==> j == i;

            loop invariant i_17: i < m ==> j <= m + 1;


            loop assigns k, j;
        */
        for (j = i; j < m;) {
            if (unknown1()) {
                //@ assert j >= 0;
                j++;
                k = 0;

                // Loop C
                /*@
                    loop invariant i_5: 0 <= k;

                    loop invariant i_6: k <= j;

                    loop invariant i_7: j >= 0;


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
