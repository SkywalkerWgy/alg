#include <assert.h>
int unknown1();
int unknown2();
int unknown3();

/*
 *  Based on "Automatically refining abstract interpretations" fig.1
 */

/*@
    requires x == 0;
    requires y == 0;
    ensures e_1: x < 4 || y > 2;
*/
void oopsla_08(int x, int y) {
    /*@
        loop assigns x, y;
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
}
