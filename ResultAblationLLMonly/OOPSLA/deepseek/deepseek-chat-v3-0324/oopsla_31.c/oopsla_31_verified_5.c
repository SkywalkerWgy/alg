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
        loop invariant i_0: 0 <= i <= n;

        loop invariant i_1: i % 4 == 0;

        loop invariant i_2: \forall integer k; 0 <= k < i ==> k % 4 == 0;

        loop invariant i_8: m + 1 < n;

        loop invariant i_9: \at(m + 1 < n, Pre);


        loop assigns n, m, k, j, i;
    */
    for (i = 0; i < n; i += 4) {

        // Loop B
        /*@
            loop invariant i_3: i <= j <= m;

            loop invariant i_4: \forall integer k; i <= k < j ==> k % 2 == 0;

            loop invariant i_5: j % 2 == 0;


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

                    loop invariant i_7: \forall integer l; 0 <= l < k ==> l < j;


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
