/*@
    requires i >= 0 && j >= 0;
*/
int svcomp_12(int i, int j) {
    int x = i;
    int y = j;
    
    // Loop A
    /*@
        loop invariant i_7: 0 <= x && x == y;

        loop invariant i_8: 0 <= x;

        loop invariant i_9: 0 <= y;


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
