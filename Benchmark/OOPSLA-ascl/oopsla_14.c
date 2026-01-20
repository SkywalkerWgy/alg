#include <assert.h>

int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * From "The Octagon Abstract Dooopsla_14" HOSC 2006 by Mine.
 */

/*@
    requires m > 0;
    ensures  e_1: a >= -m;
    ensures  e_2: a <= m;
*/
void oopsla_14(int m, int a, int j) {

    /*@
        loop assigns j, a;
    */
    for (j = 1; j <= m; j++) {
        if (unknown1()) {
            a++;
        } else {
            a--; 
        }
    }
}
