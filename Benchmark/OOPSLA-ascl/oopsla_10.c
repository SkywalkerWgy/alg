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
    ensures e_1: x == y;
*/
void oopsla_10(int w, int z, int x, int y) {

    /*@
        loop assigns z, y, x, w;
    */
    while (unknown2()) {
        if (w) {
            x++;
            w = !w;
        }
        
        if (!z) {
            y++; 
            z = !z;
        }
    }
}
