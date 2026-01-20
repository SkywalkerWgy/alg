/*@
    requires i >= 0 && j >= 0;
*/
int svcomp_12(int i, int j) {
    int x = i;
    int y = j;
    
    // Loop A
    /*@
        loop invariant i_0: i >= 0;

        loop invariant i_1: j >= 0;

        loop invariant i_2: x >= 0;

        loop invariant i_3: y - x == j - i;


        loop assigns x, y;
    */
    while (x != 0) {
    	x--;
    	y--;
    }

    if (i == j) {
    	//@ assert(y == 0);
    }
    
    return 0;
}
