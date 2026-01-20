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
        loop invariant i_0: w == z + 1;

        loop invariant i_1: z == x + y;

        loop invariant i_2: x == y;


        loop assigns z;
        loop assigns y;
        loop assigns x;
        loop assigns w;
    */
    while(unknown1()) {
        
        // Loop B
        /*@
            loop invariant i_3: z == x + y - (w % 2 == 1 ? 1 : 0) - (z % 2 == 0 ? 1 : 0);

            loop invariant i_4: x == y || (w % 2 == 1 && z % 2 == 0 && x == y - 1);

            loop invariant i_5: w == z + 1;


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
