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
        loop invariant i_3: z == 0;

        loop invariant i_4: x == 0;

        loop invariant i_5: y == 0;

        loop invariant i_6: w == 1;

        loop invariant i_7: w % 2 == 1 || x == y;

        loop invariant i_8: z % 2 == 0;


        loop assigns z;
        loop assigns y;
        loop assigns x;
        loop assigns w;
    */
    while(unknown1()) {
        
        // Loop B
        /*@
            loop invariant i_9: z == 0;

            loop invariant i_10: x == 0;

            loop invariant i_11: y == 0;

            loop invariant i_12: w == 1;

            loop invariant i_13: w % 2 == 1 || x == y;

            loop invariant i_14: z % 2 == 0;

            loop invariant i_15: x == y;

            loop invariant i_16: w % 2 == 1;


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
