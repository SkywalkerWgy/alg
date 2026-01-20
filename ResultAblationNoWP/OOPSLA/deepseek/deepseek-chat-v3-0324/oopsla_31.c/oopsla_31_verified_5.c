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
        loop invariant i_35: s for Loop A: ``` loop invariant 0 <= i <= n;

        loop invariant i_36: 0 <= i <= n;

        loop invariant i_37: i % 4 == 0;

        loop invariant i_38: m + 1 < n;

        loop invariant i_39: \forall integer x; 0 <= x < i ==> x < m;


        loop assigns n, m, k, j, i;
    */
    for (i = 0; i < n; i += 4) {

        // Loop B
        /*@
            loop invariant i_42: i <= j <= m;

            loop invariant i_43: \forall integer x; i <= x < j ==> x < m;

            loop invariant i_44: j % 2 == 0 || j % 2 == 1;

            loop invariant i_45: n + j + 5 > i;


            loop assigns k, j;
        */
        for (j = i; j < m;) {
            if (unknown1()) {
                //@ assert j >= 0;
                j++;
                k = 0;

                // Loop C
                /*@
                    loop invariant i_40: 0 <= k <= j;

                    loop invariant i_41: \forall integer x; 0 <= x < k ==> x < j;


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
