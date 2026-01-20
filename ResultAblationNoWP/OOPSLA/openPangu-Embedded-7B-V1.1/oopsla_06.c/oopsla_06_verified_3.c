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
        loop invariant i_25: z == 0;

        loop invariant i_26: x == 0;

        loop invariant i_27: y == 0;

        loop invariant i_28: w == 1;

        loop invariant i_29: x == 0 && y == 0;

        loop invariant i_30: w % 2 == 1;

        loop invariant i_31: z % 2 == 0;


        loop assigns z;
        loop assigns y;
        loop assigns x;
        loop assigns w;
    */
    while(unknown1()) {
        
        // Loop B
        /*@
            loop invariant i_32: z == 0;

            loop invariant i_33: x == 0;

            loop invariant i_34: y == 0;

            loop invariant i_35: w == 1;

            loop invariant i_36: x == 0 && y == 0;

            loop invariant i_37: w % 2 == 1;

            loop invariant i_38: z % 2 == 0;


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
