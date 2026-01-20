#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*@
    requires x != y;
    ensures  e_1: y >= t;
*/
void oopsla_43(int x, int y, int i, int t) {

    i = 0;
    t = y;

    /*@
        loop assigns y;
    */
    while (unknown1()) {
        if (x > 0)
            y = y + x;
    }
}
