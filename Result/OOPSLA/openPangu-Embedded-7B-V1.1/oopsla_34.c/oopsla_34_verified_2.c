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
        loop invariant i_0: i <= n;

        loop invariant i_1: x <= n;

        loop invariant i_2: y <= n;

        loop invariant i_3: x <= n + (i % 2 == 0);

        loop invariant i_4: y <= n + (i % 2 == 0);

        loop invariant i_5: i >= 0 && i <= n;

        loop invariant i_6: x >= 0 && x <= n;

        loop invariant i_7: y >= 0 && y <= n;

        loop invariant i_8: x == y;


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

