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
        loop invariant i_0: j == i + (flag ? x : 0);

        loop invariant i_1: y == x;

        loop invariant i_2: x >= 0;

        loop invariant i_11: x == y || x == y + 1;


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
        loop invariant i_4: w == z + 1;

        loop invariant i_5: z == x + y;

        loop invariant i_6: x == y;

        loop invariant i_12: x >= 0;

        loop invariant i_14: z == 2 * x;

        loop invariant i_15: z == (x == y ? 2*x : 2*y + 1);


        loop assigns y, x, w, z;
    */
    while (unknown2()) {
        // Loop C
        /*@
            loop invariant i_7: x >= 0;

            loop invariant i_8: y >= 0;

            loop invariant i_13: x == y;


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