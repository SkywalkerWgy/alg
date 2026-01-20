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
        loop invariant i_2: i <= n;

        loop invariant i_3: i >= 0;

        loop invariant i_4: x >= 0;

        loop invariant i_5: y >= 0;

        loop invariant i_6: i + x == x + y;

        loop invariant i_7: i % 2 == 0 ==> x == 2 * y;

        loop invariant i_8: i % 2 == 1 ==> x == 2 * y - 1;

        loop invariant i_9: i % 2 == 0 && x == 2 * y && i + x == x + y;

        loop invariant i_10: i % 2 == 1 && x == 2 * y - 1 && i + x == x + y;


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

