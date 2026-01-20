#include <assert.h>

int unknown1();
int unknown2();
int unknown3();
int unknown4();

void oopsla_26() {
    int w = 1, z = 0, x = 0, y = 0;
    // Loop A
    /*@
        loop invariant i_30: w % 2 == 1;

        loop invariant i_31: z % 2 == 0;

        loop invariant i_32: x == y;


        loop assigns z;
        loop assigns y;
        loop assigns x;
        loop assigns w;
    */
    while (unknown1()) {
        // Loop B
        /*@
            loop invariant i_36: w % 2 == 1;

            loop invariant i_37: z % 2 == 0;

            loop invariant i_38: x == y;


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
            loop invariant i_33: w % 2 == 1;

            loop invariant i_34: z % 2 == 0;

            loop invariant i_35: x == y;


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