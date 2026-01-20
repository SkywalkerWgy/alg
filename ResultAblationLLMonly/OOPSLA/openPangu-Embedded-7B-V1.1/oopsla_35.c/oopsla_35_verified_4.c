#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * InvGen, CAV'09 paper, fig 2
 */

/*@
requires n > 0;
*/
void oopsla_35(int n) {
    int x= 0;
    // Loop A
    /*@
        loop invariant i_3: x < n;


        loop assigns x;
    */
    while(x<n) {
        x++;
    } 

    //@ assert  a_1: n > 0 ==> x == n;
    
}
