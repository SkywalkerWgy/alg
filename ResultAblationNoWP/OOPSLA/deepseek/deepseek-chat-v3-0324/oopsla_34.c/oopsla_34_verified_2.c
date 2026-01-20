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
        loop invariant i_3: i == x + y;

        loop invariant i_4: x == 2 * y + (i % 2);

        loop invariant i_5: 0 <= i <= n;

        loop invariant i_6: y <= x;

        loop invariant i_7: x <= i;


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

