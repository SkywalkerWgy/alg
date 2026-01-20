#include <assert.h>

int unknown1();
int unknown2();
int unknown3();
int unknown4();

void oopsla_26() {
    int w = 1, z = 0, x = 0, y = 0;
    // Loop A
    /*@
        loop invariant i_0: w % 2 == 1;

        loop invariant i_1: z % 2 == 0;

        loop invariant i_2: x == y;


        loop assigns z;
        loop assigns y;
        loop assigns x;
        loop assigns w;
    */
    while (unknown1()) {
        // Loop B
        /*@
            loop invariant i_3: x >= y;

            loop invariant i_4: (w % 2 == 1) ==> (x == y);

            loop invariant i_5: (z % 2 == 0) ==> (y >= x);


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
            loop invariant i_6: s for Loop C: ``` loop invariant z == x + y || w == z + 1;

            loop invariant i_7: z == x + y || w == z + 1;

            loop invariant i_8: w % 2 == 1;

            loop invariant i_9: z % 2 == 0;

            loop invariant i_10: x == y;


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