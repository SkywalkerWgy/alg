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
        loop invariant i_31: x == y;

        loop invariant i_32: z == x + y;

        loop invariant i_33: w == z + 1;


        loop assigns z;
        loop assigns y;
        loop assigns x;
        loop assigns w;
    */
    while(unknown1()) {
        
        // Loop B
        /*@
            loop invariant i_34: s for Loop B: ``` loop invariant x == y;

            loop invariant i_35: x == y;

            loop invariant i_36: z == x + y;

            loop invariant i_37: w == z + 1;

            loop invariant i_38: w % 2 == (x + y + 1) % 2;


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
