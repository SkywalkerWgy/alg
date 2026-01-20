// count_up_down_true-unreach-call_true-termination.c

/*@
    requires n > 0;
*/
int svcomp_6(int n, int x, int y) {
	x = n;
	y = 0;
	
    // Loop A
	/*@
        loop invariant i_0: n == x;

        loop invariant i_2: x > 0;

        loop invariant i_3: y == n - 1;

        loop invariant i_4: y == n;


        loop assigns x, y;
    */
	while (x > 0) {
		x++;
		y--;
	}

	//@ assert y == n;
	return 0;
}
