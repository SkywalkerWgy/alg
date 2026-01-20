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
        loop invariant i_19: i == j;

        loop invariant i_20: x == y && i == j;

        loop invariant i_21: i >= j;

        loop invariant i_22: i <= j;

        loop invariant i_23: i >= j && x == y;


        loop assigns y;
        loop assigns x;
        loop assigns j;
        loop assigns i;
    */
    while(unknown1()){

        // Loop B
        /*@
            loop invariant i_24: i == j;

            loop invariant i_25: x == y && i == j;

            loop invariant i_26: i >= j;

            loop invariant i_27: i <= j;

            loop invariant i_28: i >= j && x == y;


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
