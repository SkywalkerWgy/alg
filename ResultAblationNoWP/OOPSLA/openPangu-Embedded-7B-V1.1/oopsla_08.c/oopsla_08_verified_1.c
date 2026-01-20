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
        loop invariant i_0: x >= 0 && y >= 0 && x <= 4;

        loop invariant i_1: y >= 2 || (x == 0 || x == 1 || x == 2 || x == 3);

        loop invariant i_2: x >= 0 && y >= 0 && x <= 4 && y >= 2 || x == 0 || x == 1 || x == 2 || x == 3;

        loop invariant i_3: x >= 0 && y >= 0 && x <= 4 && (y >= 2 || x == 0 || x == 1 || x == 2 || x == 3);


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
