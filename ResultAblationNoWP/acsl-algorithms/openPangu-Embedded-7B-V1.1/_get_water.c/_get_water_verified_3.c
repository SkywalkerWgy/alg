/*@
  predicate Sorted(int *t, integer lo, integer hi) =
    \forall integer i, j; lo <= i <= j < hi ==> t[i] <= t[j];
*/

/*@
    requires \valid(d + (0..n - 1));
    requires \valid(f + (0..n - 1));
    requires \separated(&d[0..(n - 1)], &f[0..(n - 1)]);
    requires \forall integer k; 0 < k < n ==> f[k] == 0;
    requires d[0] == 0;
    requires f[0] == 1;
    requires n > 0;
    requires m > 0;
    requires Sorted(d, 0, n);
    assigns f[0..n - 1];
    ensures e_1: \exists integer k; 0 <= k < n && f[k] == 1 && \result <= d[k] + m;
*/
int _get_water(int d[], int f[], int n, int m) { 
	int maxDistance = m; 
    // Loop A
    /*@
        loop invariant i_7: maxDistance >= m;

        loop invariant i_8: \forall integer i, 0 <= i < n; if i > 0, then d[i - 1] <= maxDistance;

        loop invariant i_9: \exists integer k, 0 <= k < n; f[k] == 1 implies d[k] <= maxDistance;

        loop invariant i_10: \forall integer i, 0 <= i < n; f[i] == 1 implies d[i - 1] <= maxDistance;

        loop invariant i_11: \exists integer k, 0 <= k < n && f[k] == 1 && d[k] <= maxDistance; ```;


        loop assigns i;
        loop assigns maxDistance;
        loop assigns f[0..n - 1];
    */
	for (int i = 1; i < n; i++) { 
		if (d[i] > maxDistance) { 
			f[i - 1] = 1;         
			maxDistance = m + d[i - 1];
		}
	}
    return maxDistance;
}
