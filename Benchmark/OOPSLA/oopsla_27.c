#include <assert.h>

/*
 * "nested2.c" from InvGen benchmark suite
 */

/*@
    requires l > 0;
*/
void oopsla_27(int l, int i, int k, int n) {

    /*@
        loop assigns k, i;
    */
    for (k = 1; k < n; k++) {

        /*@
            loop assigns i;
        */
        for (i = l; i < n; i++) {

        }

        /*@
            loop assigns k, i;
        */
        for (i = l; i < n; i++) {
            //@ assert  a_1: 1 <= k;
        }
    }
}
