#include <assert.h>
int unknown1();

/*
 * "nest-if8" from InvGen benchmark suite
 */

/*@
    requires m + 1 < n;
*/
void oopsla_31(int i, int j, int k, int n, int m) {
    /*@
        loop assigns n, m, k, j, i;
    */
    for (i = 0; i < n; i += 4) {

        /*@
            loop assigns k, j;
        */
        for (j = i; j < m;) {
            if (unknown1()) {
                //@ assert j >= 0;
                j++;
                k = 0;

                /*@
                    loop assigns k;
                */
                while (k < j) {
                    k++;
                }
            } else {
                //@ assert n + j + 5 > i;
                j += 2;
            }
        }
    }
}
