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
        loop invariant i_23: w == 1;

        loop invariant i_24: z >= x;

        loop invariant i_25: x + y == z;

        loop invariant i_26: w % 2 == 1;


        loop assigns z;
        loop assigns y;
        loop assigns x;
        loop assigns w;
    */
    while(unknown1()) {
        
        // Loop B
        /*@
            loop invariant i_27: w == 1;

            loop invariant i_28: z >= x;

            loop invariant i_29: x + y == z;

            loop invariant i_30: w % 2 == 1;

            loop invariant i_31: x <= y;

            loop invariant i_32: w % 2 == 1 && x == y;


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
