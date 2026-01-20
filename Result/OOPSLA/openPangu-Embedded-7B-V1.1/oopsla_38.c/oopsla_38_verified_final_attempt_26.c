#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
    requires n > 0;
*/
void oopsla_38(int n){
    int x=0;
    int y=0;
    int i=0;
    
    // Loop A
    /*@
        loop invariant i_2: i >= 0;

        loop invariant i_3: x >= 0 && y >= 0;

        loop invariant i_8: i >= 0 && x >= 0 && y >= 0;

        loop invariant i_10: x >= y;

        loop invariant i_13: i >= 0 && y >= 0 && x >= 0;

        loop invariant i_15: x - y >= 0;

        loop invariant i_25: x - y >= 0 && x >= y;

        loop invariant i_34: x - y >= 0 && x >= y && x - y >= 0;

        loop invariant i_37: x >= 0 && y >= 0 && x - y >= 0 && x >= 2 * y;


        loop assigns y;
        loop assigns x;
        loop assigns i;
    */
    while(i<n) {
        i++;
        x++;
        if(i%2 == 0) {
            y++;
        }
    }

    //@ assert  a_1: i % 2 == 0 ==> x == 2 * y;
    
}

