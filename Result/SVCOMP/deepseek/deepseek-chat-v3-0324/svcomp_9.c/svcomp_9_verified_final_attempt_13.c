/*@
    requires 0 < n;
*/
int svcomp_9(int n) {
	int k = 0;
	int i = 0;

    // Loop A
	/*@
        loop invariant i_0: k == i;

        loop invariant i_1: 0 <= i <= n;

        loop invariant i_7: i <= n;

        loop invariant i_8: k <= n;


        loop assigns i, k;
    */
	while (i < n) {
		i++;
		k++;
	}
	int j = n;
	
    // Loop B
    /*@
        loop invariant i_2: k == i + (n - j);

        loop invariant i_3: 0 <= j <= n;

        loop invariant i_4: i == n;

        loop invariant i_5: k >= 0;


        loop assigns j, k;
    */
	while (j > 0) {
		//@ assert k > 0;
		j--;
		k--;
	}

	return 0;
}