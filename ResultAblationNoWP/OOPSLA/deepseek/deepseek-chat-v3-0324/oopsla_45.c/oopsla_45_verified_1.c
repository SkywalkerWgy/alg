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
        loop invariant i_0: i == j + (flag ? x : 0);

        loop invariant i_1: x == y;

        loop invariant i_2: i >= x;


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
        loop invariant i_7: w == z + 1;

        loop invariant i_8: z <= x + y;

        loop invariant i_9: x - y == \at(x - y, Pre);


        loop assigns y, x, w, z;
    */
    while (unknown2()) {
        // Loop C
        /*@
            loop invariant i_3: x >= \at(x, Pre);

            loop invariant i_4: y >= \at(y, Pre);

            loop invariant i_5: (w % 2 == 1) ==> (x >= \at(x, Pre) + 1);

            loop invariant i_6: (z % 2 == 0) ==> (y >= \at(y, Pre) + 1);


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