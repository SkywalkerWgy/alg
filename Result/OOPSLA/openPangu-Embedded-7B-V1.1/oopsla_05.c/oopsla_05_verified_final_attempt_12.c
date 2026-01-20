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
        loop invariant i_1: x == y || i == 0;

        loop invariant i_3: x == y || i == 0 || j == 0;

        loop invariant i_5: x == y || i == 0 || j == 0 || flag == 1;

        loop invariant i_6: x == y || i == 0 || j == 0 || flag == 0;

        loop invariant i_8: x == y;

        loop invariant i_9: i == 0 && j == 0 || flag == 1;

        loop invariant i_10: i == 0 && j == 0 || flag == 0;


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
