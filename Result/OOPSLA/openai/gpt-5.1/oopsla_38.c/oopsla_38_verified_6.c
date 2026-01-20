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
        loop invariant i_0: n > 0;

        loop invariant i_1: 0 <= i <= n;

        loop invariant i_2: x == i;

        loop invariant i_3: y == i / 2;

        loop invariant i_4: \true;

        loop invariant i_5: n >= 0;

        loop invariant i_6: n != 0;


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

