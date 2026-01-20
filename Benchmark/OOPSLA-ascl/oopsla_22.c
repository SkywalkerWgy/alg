#include <assert.h>

int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*@
    requires x == 0;
    requires y == 0;
    requires z == 0;
    requires k == 0;
    ensures e_1: x == y;
    ensures e_2: y == z;
*/
void oopsla_22(int x, int y, int z, int k) {

    /*@
        loop assigns z, y, x, k;
    */
    while (unknown1()) {
        if (k % 3 == 0) {
            x++;
        }
        y++;
        z++;
        k = x + y + z;
    }
}
