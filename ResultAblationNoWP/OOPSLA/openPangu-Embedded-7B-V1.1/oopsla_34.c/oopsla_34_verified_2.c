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
        loop invariant i_6: i <= n;

        loop invariant i_7: i == m - i;

        loop invariant i_8: x == i;

        loop invariant i_9: y == i - (i % 2);

        loop invariant i_10: i % 2 == 0 ==> y;

        loop invariant i_11: i > 0 && i % 2 == 0 || y == i;

        loop invariant i_12: i >= 0;

        loop invariant i_13: x >= 0;

        loop invariant i_14: y >= 0;


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

