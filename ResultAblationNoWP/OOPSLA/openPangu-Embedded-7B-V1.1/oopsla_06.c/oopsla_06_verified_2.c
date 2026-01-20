#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

void oopsla_06(){
    int w = 1;
    int z = 0;
    int x = 0;
    int y = 0;

    // Loop A
    /*@
        loop invariant i_8: x >= 0 && y >= 0 && z % 2 == 0;


        loop assigns z;
        loop assigns y;
        loop assigns x;
        loop assigns w;
    */
    while(unknown1()) {
        
        // Loop B
        /*@
            loop invariant i_9: x >= 0 && y >= 0 && z % 2 == 0;

            loop invariant i_10: x == y && w >= 0 && z >= x;

            loop invariant i_11: w % 2 == 1;

            loop invariant i_12: z % 2 == 0;

            loop invariant i_13: x >= 0 && y >= 0;

            loop invariant i_14: z % 2 == 0 && x <= y;

            loop invariant i_15: w % 2 == 1 && x == y;

            loop invariant i_16: x >= 0 && y >= 0 && z % 2 == 0 && w >= 0;

            loop invariant i_17: x == y && z >= x && w % 2 == 1;

            loop invariant i_18: x >= 0 && y >= 0 && z % 2 == 0 && x <= y;

            loop invariant i_19: w % 2 == 1 && x >= 0 && y >= 0 && x <= y;

            loop invariant i_20: x == y;

            loop invariant i_21: z == x + y;

            loop invariant i_22: w == z + 1;

            loop invariant i_23: z % 2 == 0 && x >= 0 && y >= 0 && x <= y;

            loop invariant i_24: z % 2 == 0 && x == y && w >= 0;


            loop assigns y;
            loop assigns x;
        */
        while(unknown2()){
            if(w%2 == 1) x++;
            if(z%2 == 0) y++;
        }
        z = x + y;
        w = z + 1;
    }

    //@ assert a_1: x == y;
}
