#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

void oopsla_34(int n){
    int x=0;
    int y=0;
    int i=0;
    int m=10;
    
    // Loop A
    /*@
        loop invariant i_0: i == 0 && x == 0 && y == 0;

        loop invariant i_1: i <= n && x <= y && (y == 0 || i >= 1);

        loop invariant i_2: i % 2 == 0 || y == 0;

        loop invariant i_3: i < n && x < n - (i % 2 == 0 ? 1 : 0);

        loop invariant i_4: i == n || (x == n - (y > 0 ? 1 : 0) && y == n/2 && (n % 2 == 0 || x == n/2));

        loop invariant i_5: i == m || (x == 2 * y && i == m && y <= n);


        loop assigns y;
        loop assigns x;
        loop assigns i;
    */
    while(i < n) {
        i++;
        x++;
        if(i%2 == 0){
            y++;
        }
    }
    
    //@ assert  a_1: i == m ==> x == 2 * y;
    
}

