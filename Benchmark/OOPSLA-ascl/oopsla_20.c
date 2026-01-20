#include <assert.h>

int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*@
    requires (x + y) == k;
    requires n > 0;
    requires j == 0;
    requires m == 0;
    ensures  e_1: (x + y) == k;
    ensures  e_2: n > 0 ==> 0 <= m < n;
*/
void oopsla_20(int x, int y, int k, int j, int i, int n, int m) {
    /*@
        loop assigns y, x, m, j;
    */
    while (j < n) {
        if (j == i) {
            x++;
            y--;
        } else {
            y++;
            x--;
        }
        if (unknown1()) {
            m = j;
        }
        j++;
    }
}
