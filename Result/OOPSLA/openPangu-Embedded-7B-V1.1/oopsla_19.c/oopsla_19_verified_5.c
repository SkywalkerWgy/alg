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
        loop invariant i_0: x <= n;

        loop invariant i_1: x >= 0;

        loop invariant i_2: x <= m;

        loop invariant i_3: y >= 0;

        loop invariant i_4: y <= n;

        loop invariant i_5: x == y || x > m;

        loop invariant i_6: x == y || x <= m;

        loop invariant i_7: x <= m || y == 0;

        loop invariant i_8: x <= m || x == y;


        loop assigns y;
        loop assigns x;
    */
    while(x < n) {
        x++;
        if(x > m) y++;
    }

    //@ assert  a_1: y == n;
}
