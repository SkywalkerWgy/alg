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
        loop invariant i_33: i == 0 && j == 0 && x == 0 && y == 0;

        loop invariant i_34: w >= 0 && z >= 0 && (w % 2 == 0 || x == y);


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
        loop invariant i_37: w >= 0 && z >= 0 && (w % 2 == 0 || x == y);

        loop invariant i_38: i == 0 && j == 0 && x == 0 && y == 0;

        loop invariant i_39: w == z + x + y;


        loop assigns y, x, w, z;
    */
    while (unknown2()) {
        // Loop C
        /*@
            loop invariant i_35: w >= 0 && z >= 0 && (w % 2 == 0 || x == y);

            loop invariant i_36: w == z + x + y;


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