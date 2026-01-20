#include <assert.h>

int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * Based on "Property-Directed Incremental Invariant Generation" by Bradley et al.
 */

/*@
    requires j == 2;
    requires k == 0;
    ensures  e_1: k != 0 ==> j == 2 * k + 2;
*/
void oopsla_13(int flag, int j, int k) {

    /*@
        loop assigns j, k;
    */
    while (unknown1()) { 
        if (flag)
            j = j + 4;
        else {
            j = j + 2;
            k = k + 1;
        }
    }
}
