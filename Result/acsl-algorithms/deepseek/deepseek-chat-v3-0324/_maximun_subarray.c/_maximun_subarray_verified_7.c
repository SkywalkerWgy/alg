/*@
  logic integer subarray_sum(int* a, integer i, integer j, integer n) =
    (i >= 0 && j >= 0 && n > 0 && i < j && i < n && j <= n) ? subarray_sum(a, i, j - 1, n) + a[j - 1] : 0;
*/

/*@
  requires \valid_read(a+(0..n-1));
  requires n > 0;
  assigns \nothing;
  ensures e_1: \forall integer i, j; 0 <= i < j <= n ==> subarray_sum(a, i, j, n) <= \result;
  ensures e_2: \exists integer i, j; 0 <= i < j <= n && \result == subarray_sum(a, i, j, n);
*/
int _maximun_subarray(int a[], int n) {
    int current_sum = a[0];
    int max_sum = a[0];
    int i;
    //@ ghost int curr_p = 0;
    //@ ghost int max_p = 0, max_q = 1;
  // Loop A
    /*@
      loop invariant i_0: 0 <= i <= n;
      loop invariant i_1: current_sum == subarray_sum(a, curr_p, i, n);
      loop invariant i_3: max_sum == subarray_sum(a, max_p, max_q, n);
      loop invariant i_4: \forall integer p, q; 0 <= p < q <= i ==> subarray_sum(a, p, q, n) <= max_sum;
      loop invariant i_5: \exists integer p, q; 0 <= p < q <= i && max_sum == subarray_sum(a, p, q, n);
      loop invariant i_7: max_sum >= current_sum;
      loop invariant i_11: \forall integer p, q; 0 <= p < q <= i && q > curr_p ==> subarray_sum(a, p, q, n) <= max_sum;
      loop invariant i_12: \forall integer p; 0 <= p <= curr_p ==> subarray_sum(a, p, i, n) <= current_sum;
      loop invariant i_13: current_sum <= max_sum;
      loop invariant i_14: curr_p <= i;
      loop invariant i_15: \forall integer p; curr_p <= p < i ==> subarray_sum(a, p, i, n) <= current_sum;
      loop invariant i_16: max_p <= max_q < i+1;

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