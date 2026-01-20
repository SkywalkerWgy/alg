#include <assert.h>
int unknown1();
int unknown2();
int unknown3();

/*
 *  Based on "Automatically refining abstract interpretations" fig.1
 */

void oopsla_08() {
    int x = 0, y = 0;
    // Loop A
    /*@
        loop invariant i_0: x >= 0;

        loop invariant i_1: (x >= 4 ==> y >= 100 * (x - 4) + 4) && (x < 4 ==> y >= 0);

        loop invariant i_2: y >= 0;

        loop invariant i_3: x >= 4 ==> y >= 100 * (x - 4) + 4;

        loop invariant i_4: x < 4 ==> y >= 0;

        loop invariant i_5: x <= 4 || y >= 100 * (x - 4) + 4;

        loop invariant i_6: x <= y / 25 + 4;


        loop assigns y;
        loop assigns x;
    */
    while(unknown1()) {
        if(unknown2()) { 
            x++; 
            y += 100; 
        }
        else if (unknown3()){ 
            if (x >= 4) { 
                x++; 
                y++; 
            } 
            if (x < 0) {
                y--;
            }
        }
    
    }
    //@ assert a_1: x < 4 || y > 2;
}
