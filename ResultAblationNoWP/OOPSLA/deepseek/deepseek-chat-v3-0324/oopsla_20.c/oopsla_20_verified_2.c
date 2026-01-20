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
        loop invariant i_5: (x + y) == k;

        loop invariant i_6: 0 <= j <= n;

        loop invariant i_7: (j <= i ==> m == 0) || (j > i ==> 0 <= m < j);

        loop invariant i_8: \forall integer t; 0 <= t < j && t != i ==> (x + y) == k;


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