//terminator_03_true-unreach-call_true-termination.c

/*@
    requires y <= 1000000;
*/
int svcomp_20(int x, int y) {

	if (y > 0) {
        // Loop A
		/*@
            loop invariant i_2: x + y * k <= 100;

            loop invariant i_3: x < 100;

            loop invariant i_4: y >= 0;

            loop invariant i_5: k >= 0 && k <= 100;


            loop assigns y;
            loop assigns x;
		*/
		while (x < 100) {
			x = x + y;
		}
	}
	
	//@ assert y <= 0 || (y > 0 && x >= 100);

	return 0;
}
