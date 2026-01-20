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
      loop invariant i_0: i >= 1;

      loop invariant i_1: current_sum == a[0] + \sum_{k=1}^i [a[k] < current_sum] (or current_sum == a[0] + \sum_{k=1}^i a[k]);

      loop invariant i_2: max_sum == a[0] + \max_{1 <= k <= i} (a[k] + \sum_{l=1}^k [a[l] < current_sum]) (or max_sum >= a[0] + \sum_{k=1}^i a[k]);

      loop invariant i_3: \exists integer p; 0 <= p < i && curr_p == p;

      loop invariant i_4: \forall integer k; 0 <= k < i ==> max_p >= curr_p;

      loop invariant i_5: \forall integer k; 0 <= k < i ==> max_q == i+1;


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