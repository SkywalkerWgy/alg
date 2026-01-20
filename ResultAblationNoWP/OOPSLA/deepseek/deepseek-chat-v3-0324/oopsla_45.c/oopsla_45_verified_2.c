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
        loop invariant i_10: i == j - (flag ? x : 0);

        loop invariant i_11: x == y;

        loop invariant i_12: x >= 0;

        loop invariant i_13: y >= 0;

        loop invariant i_14: j >= i;


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
        loop invariant i_21: s for Loop B: ``` loop invariant x == y;

        loop invariant i_22: x == y;

        loop invariant i_23: x >= \at(x, Pre);

        loop invariant i_24: y >= \at(y, Pre);

        loop invariant i_25: (w % 2 == 1 && z % 2 == 0) ==> x + y == \at(x + y, Pre) + 1;

        loop invariant i_26: (w % 2 == 1 && z % 2 != 0) ==> x == \at(x, Pre) + 1 && y == \at(y, Pre);

        loop invariant i_27: (w % 2 != 1 && z % 2 == 0) ==> x == \at(x, Pre) && y == \at(y, Pre) + 1;

        loop invariant i_28: (w % 2 != 1 && z % 2 != 0) ==> x == \at(x, Pre) && y == \at(y, Pre);


        loop assigns y, x, w, z;
    */
    while (unknown2()) {
        // Loop C
        /*@
            loop invariant i_15: x >= \at(x, Pre);

            loop invariant i_16: y >= \at(y, Pre);

            loop invariant i_17: (w % 2 == 1 && z % 2 == 0) ==> x + y == \at(x + y, Pre) + 1;

            loop invariant i_18: (w % 2 == 1 && z % 2 != 0) ==> x == \at(x, Pre) + 1 && y == \at(y, Pre);

            loop invariant i_19: (w % 2 != 1 && z % 2 == 0) ==> x == \at(x, Pre) && y == \at(y, Pre) + 1;

            loop invariant i_20: (w % 2 != 1 && z % 2 != 0) ==> x == \at(x, Pre) && y == \at(y, Pre);


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