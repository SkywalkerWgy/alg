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
        loop invariant i_32: x == y || x == y - 1;

        loop invariant i_33: i >= 0;

        loop invariant i_34: j >= 0;

        loop invariant i_35: (i >= j) ==> (x == y);

        loop invariant i_36: (i < j) ==> (x == y - 1);


        loop assigns y;
        loop assigns x;
        loop assigns j;
        loop assigns i;
    */
    while(unknown1()){

        // Loop B
        /*@
            loop invariant i_37: i == \at(i, Pre) + \sum (x == y ? 1 : 0);

            loop invariant i_38: j == \at(j, Pre) + \sum (x != y ? 1 : 0);

            loop invariant i_39: x == y ==> i >= j;

            loop invariant i_40: x == y - 1 ==> i < j;

            loop invariant i_41: i >= 0;

            loop invariant i_42: j >= 0;


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
