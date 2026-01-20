#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*@
    requires n > 0;
    requires x == 0;
    requires y == 0;
    requires i == 0;
    ensures  e_1: i % 2 == 0 ==> x == 2 * y;
*/
void oopsla_38(int n, int x, int y, int i) {

    /*@
        loop assigns y, x, i;
    */
    while (i < n) {
        i++;
        x++;
        if (i % 2 == 0) {
            y++;
        }
    }
}

