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
        loop invariant i_17: i <= n;

        loop invariant i_18: i >= 0;

        loop invariant i_19: x >= 0;

        loop invariant i_20: y >= 0;

        loop invariant i_21: i % 2 == 0 ==> x == 2 * y;

        loop invariant i_22: i % 2 == 0;

        loop invariant i_23: x == 2 * y;

        loop invariant i_24: i % 2 == 0 || i == n;


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

