#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

void oopsla_22(){
    int x = 0;
    int y = 0;
    int z = 0;
    int k = 0;

    // Loop A
    /*@
        loop invariant i_0: x == y;

        loop invariant i_1: y == z;

        loop invariant i_2: k == x + y + z;

        loop invariant i_3: k % 3 == 0;


        loop assigns z;
        loop assigns y;
        loop assigns x;
        loop assigns k;
    */
    while(unknown1())
    {
        if(k%3 == 0){
            x++;
        }
        y++;
        z++;
        k = x+y+z;
    }

    //@ assert a_1: x==y;
    //@ assert a_2: y==z;
 
}