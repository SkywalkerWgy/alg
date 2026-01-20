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
        loop invariant i_27: 0 <= i <= n;

        loop invariant i_28: i % 4 == 0;

        loop invariant i_29: m + 1 < n;


        loop assigns n, m, k, j, i;
    */
    for (i = 0; i < n; i += 4) {

        // Loop B
        /*@
            loop invariant i_32: i <= j <= m;

            loop invariant i_33: \forall integer p; i <= p < j ==> p < m;

            loop invariant i_34: j % 2 == i % 2 || (unknown1() && j % 1 == 0);


            loop assigns k, j;
        */
        for (j = i; j < m;) {
            if (unknown1()) {
                //@ assert j >= 0;
                j++;
                k = 0;

                // Loop C
                /*@
                    loop invariant i_30: 0 <= k <= j;

                    loop invariant i_31: \forall integer p; 0 <= p < k ==> p < j;


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
