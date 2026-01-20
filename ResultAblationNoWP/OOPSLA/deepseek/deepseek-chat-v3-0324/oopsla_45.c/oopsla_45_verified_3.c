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
        loop invariant i_29: i == x*(x+1)/2;

        loop invariant i_30: (flag ==> j == y*(y+1)/2 + x) && (!flag ==> j == y*(y+1)/2);

        loop invariant i_31: x == y;


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
        loop invariant i_34: x == y;

        loop invariant i_35: (w % 2 == 1 ==> x == \at(x, Pre) + (w - 1) / 2) && (w % 2 == 0 ==> x == \at(x, Pre) + w / 2);

        loop invariant i_36: (z % 2 == 0 ==> y == \at(y, Pre) + (z + 2) / 2) && (z % 2 == 1 ==> y == \at(y, Pre) + (z + 1) / 2);


        loop assigns y, x, w, z;
    */
    while (unknown2()) {
        // Loop C
        /*@
            loop invariant i_32: (w % 2 == 1 ==> x == \at(x, Pre) + (w - 1) / 2) && (w % 2 == 0 ==> x == \at(x, Pre) + w / 2);

            loop invariant i_33: (z % 2 == 0 ==> y == \at(y, Pre) + (z + 2) / 2) && (z % 2 == 1 ==> y == \at(y, Pre) + (z + 1) / 2);


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