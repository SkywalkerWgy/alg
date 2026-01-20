#include <assert.h>

/*
 * "split.c" from InvGen benchmark suite
 */

/*@
    requires k == 100;
    requires i == j;
    ensures  e_1: i == j;
*/
void oopsla_32(int k, int b, int i, int j, int n) {
    /*@
        loop assigns i, j, b;
    */
    for (n = 0; n < 2 * k; n++) {
        if (b) {
            i++;
        } else {
            j++;
        }
        b = !b;
    }
}
