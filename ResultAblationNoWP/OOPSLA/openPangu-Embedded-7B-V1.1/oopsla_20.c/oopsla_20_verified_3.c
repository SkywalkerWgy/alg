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
        loop invariant i_6: m >= 0;

        loop invariant i_7: j <= n;

        loop invariant i_8: (x + y) == k && n > 0 && m < n;

        loop invariant i_9: m == j || (j == i && x >= 0) || (j < i && y <= 0);

        loop invariant i_10: (x + y) == k;

        loop invariant i_11: n > 0 || j == n;

        loop invariant i_12: j < n && (j == i || y > 0);


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