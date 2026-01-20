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
        loop invariant i_1: i < n;

        loop invariant i_2: j >= i;

        loop invariant i_3: k <= j;

        loop invariant i_4: n >= i;

        loop invariant i_5: m >= j;

        loop invariant i_20: k >= 0;

        loop invariant i_21: j >= k;

        loop invariant i_22: j < m;

        loop invariant i_23: i <= j;

        loop invariant i_24: n + j + 5 >= i;

        loop invariant i_25: j >= 0;

        loop invariant i_26: m > j;


        loop assigns n, m, k, j, i;
    */
    for (i = 0; i < n; i += 4) {

        // Loop B
        /*@
            loop invariant i_13: k >= 0;

            loop invariant i_14: j >= k;

            loop invariant i_16: i <= j;

            loop invariant i_17: n + j + 5 >= i;

            loop invariant i_18: j >= 0;

            loop invariant i_19: m > j;

            loop invariant i_27: j >= i;


            loop assigns k, j;
        */
        for (j = i; j < m;) {
            if (unknown1()) {
                //@ assert j >= 0;
                j++;
                k = 0;

                // Loop C
                /*@
                    loop invariant i_6: k >= 0;

                    loop invariant i_7: j >= k;

                    loop invariant i_8: j < m;

                    loop invariant i_9: i <= j;

                    loop invariant i_10: n + j + 5 >= i;

                    loop invariant i_11: j >= 0;

                    loop invariant i_12: m > j;


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
