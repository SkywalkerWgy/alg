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
        loop invariant i_45: j == i + (flag ? x : 0);

        loop invariant i_46: y == x;


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
        loop invariant i_51: s for Loop B: ``` loop invariant x == y;

        loop invariant i_52: x == y;

        loop invariant i_53: w == z + 1;

        loop invariant i_54: z == x + y;

        loop invariant i_55: \forall integer tmp; unknown3() ==> (w % 2 == 1 ==> x == \at(x, Pre) + 1) && (z % 2 == 0 ==> y == \at(y, Pre) + 1);

        loop invariant i_56: (w % 2 == 1 && z % 2 == 0) ==> x - \at(x, Pre) == y - \at(y, Pre);


        loop assigns y, x, w, z;
    */
    while (unknown2()) {
        // Loop C
        /*@
            loop invariant i_47: ``` loop invariant w % 2 == 1 ==> x == \at(x, Pre) + (w % 2 == 1 ? 1 : 0);

            loop invariant i_48: w % 2 == 1 ==> x == \at(x, Pre) + (w % 2 == 1 ? 1 : 0);

            loop invariant i_49: z % 2 == 0 ==> y == \at(y, Pre) + (z % 2 == 0 ? 1 : 0);

            loop invariant i_50: (w % 2 == 1 && z % 2 == 0) ==> x - \at(x, Pre) == y - \at(y, Pre);


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