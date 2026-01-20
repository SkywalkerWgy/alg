#include <assert.h>

int unknown1();
int unknown2();
int unknown3();
int unknown4();

void oopsla_45(int flag) {
    int x = 0;
    int y = 0;
    int j = 0;
    int i = 0;

    // Loop A
    /*@
        loop invariant i_15: x + y + j >= x * 2;

        loop invariant i_16: i + z == x + y + j + 1;

        loop invariant i_17: w == x + y + z + 1;

        loop invariant i_18: z == x + y;

        loop invariant i_19: w % 2 == 1 || z % 2 == 0;

        loop invariant i_20: x >= 0 && y >= 0 && z >= 0;

        loop invariant i_21: x + y == x;

        loop invariant i_22: i >= x;

        loop invariant i_23: j >= x;


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

    int w = 1;
    int z = 0;
    // Loop B
    /*@
        loop invariant i_25: w == z + x + y + 1;

        loop invariant i_26: x + y + j >= x * 2;

        loop invariant i_27: i + z == x + y + j + 1;

        loop invariant i_28: w == x + y + z + 1;

        loop invariant i_29: z == x + y;

        loop invariant i_30: w % 2 == 1 || z % 2 == 0;

        loop invariant i_31: x >= 0 && y >= 0 && z >= 0;

        loop invariant i_32: x + y == x;

        loop invariant i_33: i >= x;

        loop invariant i_34: j >= x;


        loop assigns y, x, w, z;
    */
    while (unknown2()) {
        // Loop C
        /*@
            loop invariant i_24: z + x + y == z;


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

    //@ assert  a_1: x == y;
}