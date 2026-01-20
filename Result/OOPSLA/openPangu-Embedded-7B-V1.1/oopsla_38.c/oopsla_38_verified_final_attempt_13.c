#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
    requires n > 0;
*/
void oopsla_38(int n){
    int x=0;
    int y=0;
    int i=0;
    
    // Loop A
    /*@
        loop invariant i_1: i % 2 == 0 ==> x == 2 * y;

        loop invariant i_2: i >= 0;

        loop invariant i_3: x >= 0 && y >= 0;

        loop invariant i_6: i % 2 == 0 ==> x == y;

        loop invariant i_8: i >= 0 && x >= 0 && y >= 0;

        loop invariant i_10: x >= y;

        loop invariant i_12: x == 2 * y;

        loop invariant i_13: i >= 0 && y >= 0 && x >= 0;

        loop invariant i_14: x >= 2 * y;

        loop invariant i_15: x - y >= 0;

        loop invariant i_16: y - x >= 0 && (i % 2 == 1 || y >= x);

        loop invariant i_18: x - y <= n - i;

        loop invariant i_20: x >= y && (i % 2 == 0 || y >= x);

        loop invariant i_21: x - y >= 0 && i % 2 == 0;

        loop invariant i_22: x - y >= 0 && y - x <= n - i;

        loop invariant i_23: x >= 2 * y && i >= 0 && x >= 0 && y >= 0 && i < n;

        loop invariant i_24: x - y >= 0 && x >= y && i % 2 == 0;

        loop invariant i_25: x - y >= 0 && x >= y;

        loop invariant i_26: x >= 0 && y >= 0 && x - y <= n - i;

        loop invariant i_27: x >= 0 && y >= 0 && x - y >= 0 && i < n;

        loop invariant i_28: x - y >= 0 && (i % 2 == 0 || y >= x);

        loop invariant i_29: x >= y && x - y <= n - i;

        loop invariant i_31: i >= 0 && i < n;

        loop invariant i_32: x >= y && i % 2 == 0 || y >= x;

        loop invariant i_33: x - y >= 0 && x >= y && x - y <= n - i;

        loop invariant i_34: x - y >= 0 && x >= y && x - y >= 0;

        loop invariant i_35: x >= 2 * y && x - y >= 0 && i >= 0 && x >= y && y >= 0 && i < n;

        loop invariant i_36: x - y >= 0 && (i % 2 == 0 || y >= x) && x >= 2 * y;

        loop invariant i_37: x >= 0 && y >= 0 && x - y >= 0 && x >= 2 * y;

        loop invariant i_38: x >= 2 * y && x - y >= 0 && i >= 0 && i < n && x >= y && y >= 0;

        loop invariant i_39: x >= 2 * y && x - y >= 0 && i % 2 == 0;

        loop invariant i_40: x >= 2 * y && x - y >= 0 && i % 2 == 0 && y >= x;

        loop invariant i_41: x >= 2 * y && x - y >= 0 && i % 2 == 0 && y >= x && y >= 0 && x >= 0 && i < n;

        loop invariant i_42: x >= 2 * y && x - y >= 0 && i % 2 == 0 && y >= x && x >= 0 && y >= 0 && i < n;

        loop invariant i_43: x >= 2 * y && x - y >= 0 && i % 2 == 0 && y >= x && i >= 0 && i < n;

        loop invariant i_44: x >= 2 * y && x - y >= 0 && i % 2 == 0 && y >= x && y >= 0 && x >= 0;


        loop assigns y;
        loop assigns x;
        loop assigns i;
    */
    while(i<n) {
        i++;
        x++;
        if(i%2 == 0) {
            y++;
        }
    }

    //@ assert  a_1: i % 2 == 0 ==> x == 2 * y;
    
}

