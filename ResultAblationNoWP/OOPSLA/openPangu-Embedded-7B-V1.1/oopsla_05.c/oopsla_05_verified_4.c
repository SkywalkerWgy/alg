#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

void oopsla_05(int flag){
	int x = 0;
	int y = 0;
	int j = 0;
	int i = 0;

    // Loop A
    /*@
        loop invariant i_18: j >= i;

        loop invariant i_19: x >= 0;

        loop invariant i_20: y >= 0;

        loop invariant i_21: i <= j;

        loop invariant i_22: j >= x;

        loop invariant i_23: flag == 0 || j >= i + 1;

        loop invariant i_24: for the following loop. loop assigns y;


        loop assigns y;
        loop assigns x;
        loop assigns j;
        loop assigns i;
	*/
	while(unknown1()) {
        x++;
        y++;
        i += x;
        j += y;
        if (flag){
            j += 1;
        }
	} 

	//@ assert a_1: (j>=i);
}
