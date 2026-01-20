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
        loop invariant i_0: z % 2 == 1 || x == y;

        loop invariant i_1: y >= x;

        loop invariant i_2: w == 0 || z % 2 == 1;

        loop invariant i_3: x == y == 0 && z % 2 == 1 || x + y == 1;

        loop invariant i_5: z % 2 == 1;

        loop invariant i_6: (x + y + w) % 3 == 0;


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
