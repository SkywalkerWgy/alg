// count_up_down_true-unreach-call_true-termination.c

/*@
    requires n > 0;
*/
int svcomp_6(int n, int x, int y) {
	x = n;
	y = 0;
	
    // Loop A
	/*@
        loop invariant i_2: x > 0;

        loop invariant i_5: x >= 0;

        loop invariant i_6: y <= n;

        loop invariant i_7: y <= n - 1;

        loop invariant i_8: y >= 0;

        loop invariant i_9: x <= n;

        loop invariant i_10: y < n;


        loop assigns x, y;
    */
	while (x > 0) {
		x++;
		y--;
	}

	//@ assert y == n;
	return 0;
}
