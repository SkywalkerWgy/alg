/*@
    predicate sorted(int *t, integer lo, integer hi) =
        \forall integer i, j; lo <= i <= j < hi ==> t[i] <= t[j];
*/

/*@ 
    requires \valid(s + (0..(n - 1)));
    requires \valid(f + (0..(n - 1)));
    requires \valid(selected + (0..(n - 1)));
    requires n > 0;
    requires sorted(f, 0, n);
    requires \separated(&s[0..(n - 1)], &f[0..(n - 1)], &selected[0..(n - 1)]);
    requires \forall integer k; 0 <= k < n ==> s[k] < f[k];
    requires \forall integer k; 0 <= k < n ==> selected[k] == 0;
    assigns selected[0..(n - 1)];
    ensures e_1: \forall integer p, q; (0 <= p < q < n && selected[p] == 1 && selected[q] == 1) ==> s[q] >= f[p];
*/
void _greedy_selector(int n, int* s, int* f, int* selected)
{
	int j = 0;
    selected[0] = 1;
    // Loop A
    /*@
        loop invariant i_4: selected[0] == 1;

        loop invariant i_5: j >= 0;

        loop invariant i_6: \forall integer i; 0 <= i < j < n ==> selected[i] == 0;


        loop assigns i, j, selected[0..(n - 1)];
    */
	for (int i = 1; i < n; i++){
		if (s[i] >= f[j]) { 
			selected[i] = 1;
			j = i;
		}
    }
}