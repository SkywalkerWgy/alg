#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * From "Simplifying Loop Invariant Generation using Splitter Predicates", Sharma et al. CAV'11
 */

/*@
    requires n >= 0;
    requires m >= 0;
    requires m < n;
*/
void oopsla_19(int n, int m){
    int x = 0; 
    int y = m;
    // Loop A
    /*@
        loop invariant i_14: x <= n;

        loop invariant i_15: x >= 0;

        loop invariant i_16: y <= m;

        loop invariant i_17: x == x;


        loop assigns y;
        loop assigns x;
    */
    while(x < n) {
        x++;
        if(x > m) y++;
    }

    //@ assert  a_1: y == n;
}
