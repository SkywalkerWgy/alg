/*@
    requires 0 < n;
*/
int svcomp_9(int n) {
	int k = 0;
	int i = 0;

    // Loop A
	/*@
        loop invariant i_4: 0 <= i <= n;

        loop invariant i_5: k == i;


        loop assigns i, k;
    */
	while (i < n) {
		i++;
		k++;
	}
	int j = n;
	
    // Loop B
    /*@
        loop invariant i_6: s for Loop B: ``` loop invariant 0 <= j <= n;

        loop invariant i_7: 0 <= j <= n;

        loop invariant i_8: k == j + (i - j);

        loop invariant i_9: k >= 0;


        loop assigns j, k;
    */
	while (j > 0) {
		//@ assert k > 0;
		j--;
		k--;
	}

	return 0;
}