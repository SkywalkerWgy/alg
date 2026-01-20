#include<assert.h>

int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*@
    requires (x + y) == k;
    requires n > 0;
*/
void oopsla_20(int x, int y, int k, int j, int i, int n) {
    int m = 0;
    j = 0;

    // Loop A
    /*@
        loop invariant i_0: x + y == k;

        loop invariant i_1: 0 <= m;

        loop invariant i_2: m <= j;

        loop invariant i_3: 0 <= j;

        loop invariant i_4: j <= n;


        loop assigns y;
        loop assigns x;
        loop assigns m;
        loop assigns j;
    */
    while (j < n) {
        if (j == i) {
            x++;
            y--;
        } 
        else {
            y++;
            x--;
        }
        if (unknown1()){
            m = j;
        }
        j++;
    }

    //@ assert  a_1: (x + y) == k;
    //@ assert  a_2: n > 0 ==> 0 <= m;
    //@ assert  a_3: n > 0 ==> m < n;
}