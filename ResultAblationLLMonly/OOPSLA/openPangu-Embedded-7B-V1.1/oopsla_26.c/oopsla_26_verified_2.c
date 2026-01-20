#include <assert.h>

int unknown1();
int unknown2();
int unknown3();
int unknown4();

void oopsla_26() {
    int w = 1, z = 0, x = 0, y = 0;
    // Loop A
    /*@
        loop invariant i_10: x == 0 && w == 1 && z == 0 && y == 0;

        loop invariant i_11: x == w && y == z && y == 0 || z % 2 == 1;

        loop invariant i_12: z == x + y && w == z + 1;


        loop assigns z;
        loop assigns y;
        loop assigns x;
        loop assigns w;
    */
    while (unknown1()) {
        // Loop B
        /*@
            loop invariant i_16: x == 0 && w == 1 && z == 0 && y == 0;

            loop invariant i_17: x == w && y == z && y == 0 || z % 2 == 1;

            loop invariant i_18: z == x + y && w == z + 1;


            loop assigns y;
            loop assigns x;
        */
        while (unknown2()) {
            if (w % 2 == 1)
                x++;
            if (z % 2 == 0)
                y++;
        }
        // Loop C
        /*@
            loop invariant i_13: x == 0 && w == 1 && z == 0 && y == 0;

            loop invariant i_14: x == w && y == z && y == 0 || z % 2 == 1;

            loop invariant i_15: z == x + y && w == z + 1;


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