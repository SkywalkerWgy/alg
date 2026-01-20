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
        loop invariant i_1: i % 4 == 0;

        loop invariant i_2: m + 1 < n;

        loop invariant i_15: i >= 0;

        loop invariant i_23: i % 2 == 0;

        loop invariant i_31: m < n;


        loop assigns n, m, k, j, i;
    */
    for (i = 0; i < n; i += 4) {

        // Loop B
        /*@
            loop invariant i_4: j % 2 == i % 2;

            loop invariant i_5: n + j + 5 > i;

            loop invariant i_13: j >= 0;

            loop invariant i_14: j >= i;

            loop invariant i_17: j % 2 == 0;

            loop invariant i_24: j >= 0 && j % 2 == 0;


            loop assigns k, j;
        */
        for (j = i; j < m;) {
            if (unknown1()) {
                //@ assert j >= 0;
                j++;
                k = 0;

                // Loop C
                /*@
                    loop invariant i_6: 0 <= k <= j;

                    loop invariant i_7: k <= j;

                    loop invariant i_8: \forall integer p; 0 <= p < k ==> p < j;

                    loop invariant i_21: k % 2 == 0;

                    loop invariant i_25: k >= 0 && k <= j && k % 2 == 0;

                    loop invariant i_28: \forall integer p; 0 <= p < i ==> p % 2 == 0;


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
