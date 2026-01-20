/*@
    requires 0 < n;
*/
int svcomp_9(int n) {
	int k = 0;
	int i = 0;

    // Loop A
	/*@
        loop invariant i_21: i < n && k == i;

        loop invariant i_22: j == n - i && k == j;

        loop invariant i_23: k >= 0;

        loop invariant i_24: \forall integer m; 0 <= m < i ==> m <= k;

        loop invariant i_25: \forall integer m; 0 <= m < j ==> m <= k;


        loop assigns i, k;
    */
	while (i < n) {
		i++;
		k++;
	}
	int j = n;
	
    // Loop B
    /*@
        loop invariant i_26: i < n && k == i && k >= 0;

        loop invariant i_27: j > 0 && k == j && k >= 0;


        loop assigns j, k;
    */
	while (j > 0) {
		//@ assert k > 0;
		j--;
		k--;
	}

	return 0;
}