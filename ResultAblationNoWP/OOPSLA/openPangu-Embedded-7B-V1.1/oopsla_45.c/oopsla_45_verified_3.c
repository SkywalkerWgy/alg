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
        loop invariant i_15: x + y + j == x + y + j;

        loop invariant i_16: i <= j;


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
        loop invariant i_22: i <= j;

        loop invariant i_23: x + y + j == x + y + j;

        loop invariant i_24: w >= 1;

        loop invariant i_25: z >= x + y + 1;

        loop invariant i_26: z == x + y + 1;

        loop invariant i_27: \forall integer k; 0 <= k < w && z >= x + y + 1 || k == w - 1;

        loop invariant i_28: \forall integer k; 0 <= k < w ==> z >= x + y + 1;

        loop invariant i_29: \exists integer k; 0 <= k < w && z >= x + y + 1;

        loop invariant i_30: \forall integer p; 0 <= p < i ==> max >= a[p];

        loop invariant i_31: \forall integer p; 0 <= p < i ==> \at(k, End_l) == true;

        loop invariant i_32: \forall integer p; 0 <= p < i ==> res[p] == \at(res[p], End_l);


        loop assigns y, x, w, z;
    */
    while (unknown2()) {
        // Loop C
        /*@
            loop invariant i_17: w >= 1 && x + y <= z;

            loop invariant i_18: z == x + y + 1;

            loop invariant i_19: z >= x + y;

            loop invariant i_20: w >= 1;

            loop invariant i_21: \forall integer k; 0 <= k < w && z >= x + y + 1 || k == w - 1;


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