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
      loop invariant i_8: 1 < n;

      loop invariant i_9: 0 <= i < n;

      loop invariant i_10: current_sum == a[0] + \sum_{k=1}^i a[k] \, (a[k] < current_sum);

      loop invariant i_11: max_sum == \max(\max_sum, \max(\sum_{k=0}^j a[k]));

      loop invariant i_12: \forall integer j; j < i ==> \forall integer k, 0 <= k < j; \sum_{k=0}^k a[k] <= current_sum;

      loop invariant i_13: \exists integer j; j >= i && \sum_{k=0}^j a[k] == max_sum;

      loop invariant i_14: \exists integer j; j == i && current_sum == a[i];


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