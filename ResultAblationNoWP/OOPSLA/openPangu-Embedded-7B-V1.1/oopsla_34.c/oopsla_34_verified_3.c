#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

void oopsla_34(int n){
    int x=0;
    int y=0;
    int i=0;
    int m=10;
    
    // Loop A
    /*@
        loop invariant i_15: i <= n;

        loop invariant i_16: x <= n;

        loop invariant i_17: i == n - x;

        loop invariant i_18: i % 2 == 0 || x % 2 == 0;

        loop invariant i_19: y == x / 2;


        loop assigns y;
        loop assigns x;
        loop assigns i;
    */
    while(i < n) {
        i++;
        x++;
        if(i%2 == 0){
            y++;
        }
    }
    
    //@ assert  a_1: i == m ==> x == 2 * y;
    
}

