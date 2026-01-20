#include <assert.h>

int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*@
    requires x == 0;
    requires y == 0;
    requires i == 0;
    requires j == 0;
    ensures  e_1: i >= j;
*/
void oopsla_25(int x, int y, int i, int j) {

    /*@
        loop assigns y, x, j, i;
    */
    while (unknown1()) {

        /*@
            loop assigns j, i;
        */
        while (unknown2()) {
            if (x == y) {
                i++;
            } else {
                j++;
            }
        }

        if (i >= j) {
            x++;
            y++;
        } else {
            y++;
        }
    }
}
