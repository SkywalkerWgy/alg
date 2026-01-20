#include <assert.h>

int unknown1();
int unknown2();
int unknown3();
int unknown4();

void oopsla_46() {

    int w = 1;
    int z = 0;
    int x = 0;
    int y = 0;

    // Loop A
    /*@
        loop invariant i_0: (w % 2 == 1 ==> x == 0);

        loop invariant i_1: (w % 2 == 0 ==> x == 1);

        loop invariant i_2: (z % 2 == 0 ==> y == 0);

        loop invariant i_3: (z % 2 == 1 ==> y == 1);

        loop invariant i_4: w % 2 == 1 ==> x == 0;

        loop invariant i_5: w % 2 == 0 ==> x == 1;

        loop invariant i_6: z % 2 == 0 ==> y == 0;

        loop invariant i_7: z % 2 == 1 ==> y == 1;


        loop assigns z, y, x, w;
    */
    while (unknown2()) {
        if (w % 2 == 1) {
            x++;
            w++;
        }
        if (z % 2 == 0) {
            y++;
            z++;
        }
    }

    //@ assert  a_1: x <= 1;
}