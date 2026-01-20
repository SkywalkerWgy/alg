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

        loop invariant i_2: y >= 0;

        loop invariant i_3: x >= 4 ==> y >= 100 * (x - 4) + 4;

        loop invariant i_4: x < 4 ==> y >= 0;

        loop invariant i_5: x <= 4 || y >= 100 * (x - 4) + 4;

        loop invariant i_6: x <= y / 25 + 4;

        loop invariant i_9: y >= 100 * (x - 4) + 4 || x < 4;

        loop invariant i_10: x <= y / 100 + 4;

        loop invariant i_11: x >= 4 ==> y >= 100*(x-4);

        loop invariant i_12: y >= 100*(x-4);

        loop invariant i_13: (x < 4 && y >= 0) || (x >= 4 && y >= 100*(x-4));

        loop invariant i_14: x >= 0 && y >= 0;

        loop invariant i_15: (x <= 4 && y >= 0) || (x > 4 && y >= 100*(x-4) + 4);

        loop invariant i_16: (x < 4 ==> y >= 0) && (x >= 4 ==> y >= 100*(x-4));

        loop invariant i_17: (x <= 4 && y >= 0) || (x > 4 && y >= 100*(x-4));

        loop invariant i_18: x == 0 ==> y == 0;

        loop invariant i_19: x <= y;

        loop invariant i_20: x >= 5 ==> y >= 100*(x-4) + 4;

        loop invariant i_21: x < 4 || y >= 100*(x-4) + 4;

        loop invariant i_22: x <= 4 || y >= 100*(x-5) + 104;


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
