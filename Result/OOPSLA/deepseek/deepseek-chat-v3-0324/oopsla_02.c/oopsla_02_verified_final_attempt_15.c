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
        loop invariant i_0: y >= 0;

        loop invariant i_1: z == x + y*(y+1) + 2*(y*(y-1)/2) + i - j;

        loop invariant i_2: x <= y;

        loop invariant i_3: z % 2 == 1 ==> x == y;

        loop invariant i_4: z % 2 == 0 ==> x <= y;

        loop invariant i_5: w == 2*y;

        loop invariant i_6: z == x + y*(y+1) + w*(y-1)/2 + i - j;

        loop invariant i_8: w >= 0;

        loop invariant i_9: (x == y) <==> (z % 2 == 1);

        loop invariant i_11: x == y ==> z % 2 == 1;

        loop invariant i_12: x <= y + 1;

        loop invariant i_16: z % 2 == 0 ==> 2*y + x + w == 2*(i - j) + 2;

        loop invariant i_17: (z % 2 == 1 && (i - j + 1) % 2 == 1) || (z % 2 == 0 && (i - j + 1) % 2 == 0);

        loop invariant i_18: (i - j) % 2 == 0 ==> z % 2 == 1;

        loop invariant i_19: (i - j) % 2 == 1 ==> z % 2 == 0;


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
