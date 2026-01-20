#include <assert.h>

int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*@
    requires i == 1;
    requires j == 0;
    requires z == i - j;
    requires x == 0;
    requires y == 0;
    requires w == 0;
    ensures e_1: x == y;
*/
void oopsla_02(int i, int j, int z, int x, int y, int w) {

    /*@
        loop assigns z;
        loop assigns y;
        loop assigns x;
        loop assigns w;
    */
    while (unknown2()) 
    {
        z += x + y + w;
        y++;
        if (z % 2 == 1) 
            x++;
        w += 2; 
    }
}
