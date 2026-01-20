/*@
    requires 0 < n;
*/
int svcomp_9(int n) {
	int k = 0;
	int i = 0;

    // Loop A
	/*@
        loop invariant i_0: i <= n && k < n;

        loop invariant i_1: k < n;


        loop assigns i, k;
    */
	while (i < n) {
		i++;
		k++;
	}
	int j = n;
	
    // Loop B
    /*@
        loop invariant i_2: i <= n && k < n;

        loop invariant i_3: k < n;

        loop invariant i_4: k > 0;


        loop assigns j, k;
    */
	while (j > 0) {
		//@ assert k > 0;
		j--;
		k--;
	}

	return 0;
}