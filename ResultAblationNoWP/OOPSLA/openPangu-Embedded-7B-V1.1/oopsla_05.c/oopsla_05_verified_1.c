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
        loop invariant i_0: j >= i;

        loop invariant i_1: x <= y;

        loop invariant i_2: i <= j;

        loop invariant i_3: j <= i + 1;

        loop invariant i_4: 0 <= x && 0 <= y && 0 <= i && 0 <= j && 0 <= i + 1;

        loop invariant i_5: 0 <= i && 0 <= j && 0 <= x && 0 <= y && 0 <= i + 1;

        loop invariant i_6: x <= y && i <= j && j <= i + 1 && 0 <= x && 0 <= y;

        loop invariant i_7: 0 <= x && 0 <= y && i <= j && j <= i + 1;

        loop invariant i_8: 0 <= x && 0 <= y && i <= j && j <= i + 1 && x <= y;

        loop invariant i_9: 0 <= x && 0 <=;


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
