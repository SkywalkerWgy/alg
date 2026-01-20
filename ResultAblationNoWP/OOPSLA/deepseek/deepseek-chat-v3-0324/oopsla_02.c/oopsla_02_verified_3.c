#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

void oopsla_02(){
	int i = 1;
	int j = 0;
	int z = i - j;
	int x = 0;
	int y = 0;
	int w = 0;

    // Loop A
	/*@
        loop invariant i_6: z == (i - j) + x * (2 * y - x) + y * (y + 1);

        loop invariant i_7: w == 2 * y;

        loop invariant i_8: x <= y;

        loop invariant i_9: x == (z % 2 == 1 ? y : y - 1);


        loop assigns x, y, z, w;
	*/
	while(unknown2()) 
	{
		z += x + y + w;
		y++;
		if (z % 2 == 1) 
		  x++;
		w += 2; 
	}

	//@ assert a_1: x==y;
}
