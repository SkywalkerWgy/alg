#include <assert.h>

int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*@
    requires w == 1;
    requires z == 0;
    requires x == 0;
    requires y == 0;
    ensures  e_1: x <= 1;
*/
void oopsla_46(int w, int z, int x, int y) {

    /*@
        loop assigns z, y, x, w;
    */
    while (unknown2()) {
        if (w % 2 == 1) {
            x++;
            w++;
        }
        if (z % 2 == 0) {
            y++;
            z++;
        }
    }
}
