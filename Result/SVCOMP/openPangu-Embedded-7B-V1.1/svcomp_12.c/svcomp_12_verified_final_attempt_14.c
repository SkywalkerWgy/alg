/*@
    requires i >= 0 && j >= 0;
*/
int svcomp_12(int i, int j) {
    int x = i;
    int y = j;
    
    // Loop A
    /*@
        loop invariant i_3: i >= 0 && j >= 0;

        loop invariant i_7: x <= i && y <= j;


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
