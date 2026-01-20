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
        loop invariant i_0: m == 0;

        loop invariant i_3: j >= 0 && j < n;

        loop invariant i_4: m == 0 && j == 0;

        loop invariant i_5: i == 0 && m == 0;

        loop invariant i_6: i == j;

        loop invariant i_7: i >= 0 && i < n && j >= 0 && j < n;

        loop invariant i_8: m == j;

        loop invariant i_9: m >= 0 && m < n;

        loop invariant i_10: m == 0 && m < n;

        loop invariant i_11: i >= 0 && i < n;

        loop invariant i_12: m >= 0;

        loop invariant i_13: m < n;

        loop invariant i_14: j >= 0;


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