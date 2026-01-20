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
        loop invariant i_0: x == y || x == y - 1;

        loop invariant i_1: i >= 0;

        loop invariant i_2: j >= 0;

        loop invariant i_3: (i >= j) ==> (x == y);

        loop invariant i_4: (i < j) ==> (x == y - 1);


        loop assigns y;
        loop assigns x;
        loop assigns j;
        loop assigns i;
    */
    while(unknown1()){

        // Loop B
        /*@
            loop invariant i_5: x == y || x == y - 1;

            loop invariant i_6: i >= 0;

            loop invariant i_7: j >= 0;

            loop invariant i_8: (i >= j) ==> (x == y);

            loop invariant i_9: (i < j) ==> (x == y - 1);


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
