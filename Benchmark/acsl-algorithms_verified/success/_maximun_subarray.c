/*@
  logic integer subarray_sum(int* a, integer i, integer j, integer n) =
    (i >= 0 && j >= 0 && n > 0 && i < j && i < n && j <= n) ? subarray_sum(a, i, j - 1, n) + a[j - 1] : 0;
*/

/*@
  requires \valid_read(a+(0..n-1));
  requires n > 0;
  assigns \nothing;
  ensures \forall integer i, j; 0 <= i < j <= n ==> subarray_sum(a, i, j, n) <= \result;
  ensures \exists integer i, j; 0 <= i < j <= n && \result == subarray_sum(a, i, j, n);
*/
int _maximun_subarray(int a[], int n) {
    int current_sum = a[0];
    int max_sum = a[0];
    int i;
    /*@ ghost int curr_p = 0; */
    /*@ ghost int max_p = 0, max_q = 1;*/
    /*@
      loop invariant idx_bound: 1 <= i <= n;
      loop invariant curr_p_bound: 0 <= curr_p < i;
      loop invariant max_pq_bound: 0 <= max_p < max_q <= i;
      loop invariant max_is_geq: current_sum <= max_sum;
      loop invariant max_is_sum: max_sum == subarray_sum(a,max_p,max_q,n);
      loop invariant max_is_max: \forall integer p, q; 0 <= p < q <= i ==> subarray_sum(a, p, q, n) <= max_sum;
      loop invariant curr_is_local_max: \forall integer p; 0 <= p < i ==> subarray_sum(a, p, i, n) <= current_sum;
      loop invariant curr_is_sum: current_sum == subarray_sum(a, curr_p, i, n);
      loop assigns current_sum, max_sum, i, curr_p, max_p, max_q;
    */
    for (i = 1; i < n; i++) {
        if (a[i] < current_sum + a[i]) {
            current_sum = current_sum + a[i];
        }
        else {
            current_sum = a[i];
            //@ ghost curr_p = i;
        }

        if (current_sum > max_sum) {
            max_sum = current_sum;
            //@ ghost max_p = curr_p;
            //@ ghost max_q = i+1;
        }
    }
    return max_sum;
}