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
        loop invariant i_11: i <= n;

        loop invariant i_12: i % 2 == 0 || x % 2 == 0;

        loop invariant i_13: x <= n;

        loop invariant i_14: y < n;

        loop invariant i_15: i == x + y;

        loop invariant i_16: x == 2 * y;


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

