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
    ensures  e_1: x == y;
*/
void oopsla_26(int w, int z, int x, int y) {

    /*@
        loop assigns z, y, x, w;
    */
    while (unknown1()) {

        /*@
            loop assigns y, x;
        */
        while (unknown2()) {
            if (w % 2 == 1)
                x++;
            if (z % 2 == 0)
                y++;
        }

        /*@
            loop assigns z, w;
        */
        while (unknown4()) {
            z = x + y;
            w = z + 1;
        }
    }

}
