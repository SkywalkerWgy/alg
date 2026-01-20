#include <assert.h>

int unknown1();
int unknown2();
int unknown3();
int unknown4();

void oopsla_26() {
    int w = 1, z = 0, x = 0, y = 0;
    /*@
        loop assigns z;
        loop assigns y;
        loop assigns x;
        loop assigns w;
    */
    while (unknown1()) {
        /*@
            loop assigns y;
            loop assigns x;
        */
        while (unknown2()) {
            if (w % 2 == 1)
                x++;
            if (z % 2 == 0)
                y++;
        }
        /*@
            loop assigns z;
            loop assigns y;
            loop assigns x;
            loop assigns w;
        */
        while (unknown4()) {
            z = x + y;
            w = z + 1;
        }
    }
    //@ assert  a_1: x == y;
}