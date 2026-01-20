#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

void oopsla_25(){
    int x = 0;
    int y = 0;
    int i = 0;
    int j = 0;

    // Loop A
    /*@
        loop invariant i_19: s for Loop A: ``` loop invariant x >= 0 && y >= 0;

        loop invariant i_20: x >= 0 && y >= 0;

        loop invariant i_21: i >= 0 && j >= 0;

        loop invariant i_22: y >= x;

        loop invariant i_23: (i >= j) ==> (y == x);

        loop invariant i_24: (i < j) ==> (y == x + 1);


        loop assigns y;
        loop assigns x;
        loop assigns j;
        loop assigns i;
    */
    while(unknown1()){

        // Loop B
        /*@
            loop invariant i_25: x >= 0 && y >= 0;

            loop invariant i_26: i >= 0 && j >= 0;

            loop invariant i_27: y >= x;

            loop invariant i_28: (i >= j) ==> (y == x);

            loop invariant i_29: (i < j) ==> (y == x + 1);

            loop invariant i_30: j == \at(j, LoopEntry) + (x != y ? \at(x != y, LoopEntry) : 0);

            loop invariant i_31: i == \at(i, LoopEntry) + (x == y ? \at(x == y, LoopEntry) : 0);


            loop assigns j;
            loop assigns i;
        */
        while(unknown2()){
            if(x == y){
                i++;
            }
            else{
                j++;
            }
        }
        if(i >= j){
            x++;
            y++;
        }
        else{
            y++;
        }
    }

    //@ assert  a_1: i >= j;
}
