#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * From "A Practical and Complete Approach to Predicate Refinement" by McMillan TACAS'06
 */

/*@
    requires x == i;
    requires y == j;
    ensures  e_1: i == j ==> y == 0;
*/
void oopsla_16(int i, int j, int x, int y) {

    /*@
        loop assigns y, x;
    */
    while (x != 0) {
        x--;
        y--;
    }
}
