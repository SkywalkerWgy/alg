#include <assert.h>

int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*@
    requires x == 0;
    requires y == 0;
    requires j == 0;
    requires i == 0;
    ensures  e_1: x == y;
*/
void oopsla_45(int flag, int x, int y, int j, int i, int w, int z) {

    /*@
        loop assigns y, x, j, i;
    */
    while (unknown1()) {
        x++;
        y++;
        i += x;
        j += y;
        if (flag) {
            j += 1;
        }
    }

    if (j >= i)
        x = y;
    else
        x = y + 1;

    w = 1;
    z = 0;

    /*@
        loop assigns y, x, w, z;
    */
    while (unknown2()) {

        /*@
            loop assigns y, x;
        */
        while (unknown3()) {
            if (w % 2 == 1)
                x++;
            if (z % 2 == 0)
                y++;
        }

        z = x + y;
        w = z + 1;
    }
}
