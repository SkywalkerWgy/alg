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
        loop invariant i_25: i <= j;

        loop invariant i_26: j <= y;

        loop invariant i_27: x <= y;

        loop invariant i_28: for the following loop. loop assigns y;


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
