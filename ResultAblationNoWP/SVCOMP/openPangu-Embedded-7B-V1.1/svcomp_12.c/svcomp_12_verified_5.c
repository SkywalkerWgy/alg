/*@
    requires i >= 0 && j >= 0;
*/
int svcomp_12(int i, int j) {
    int x = i;
    int y = j;
    
    // Loop A
    /*@
        loop invariant i_10: i >= 0 && j >= 0 && x == i - x;

        loop invariant i_11: y == j - x;


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
