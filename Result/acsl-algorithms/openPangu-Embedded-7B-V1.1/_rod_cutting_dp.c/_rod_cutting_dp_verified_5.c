/*@
    predicate is_max(integer a, integer b, integer result) =
        result >= a && 
        result >= b && 
        (result == a || result == b);
*/

/*@
    assigns \nothing;
    ensures is_max(a, b, \result);
*/
int max(int a, int b) {
  int max_val = a >= b ? a : b;
  return max_val;
}

/*@
  requires n > 1;
  requires \valid(price + (0..n));
  requires \valid(r + (0..n));
  requires \forall integer k; 0 <= k <= n ==> r[k] == 0;
  requires \forall integer k; 0 <= k <= n ==> price[k] > 0;
  ensures e_1: \forall integer p; 1 <= p <= n ==> (\forall integer q; 1 <= q < p + 1 ==> r[p] >= price[q] + r[p - q]);
  assigns r[0..n];
*/
int _rod_cutting_dp(int price[], int r[], int n) {
  // Loop A
    /*@
      loop invariant i_0: 1 <= j <= n;

      loop invariant i_2: \forall integer k; 0 <= k <= j ==> r[k] == -2147483648;

      loop invariant i_17: r[j] == -2147483648 || r[j] >= price[i] + r[j - i];


      loop assigns r[0..n];
      loop assigns j;
    */
    for (int j = 1; j <= n; j++) {
        r[j] = -2147483648;
        // Loop B
        /*@
            loop invariant i_5: 1 <= j <= n;

            loop invariant i_6: r[j] == -2147483648 || r[j] >= price[i] + r[j - i];

            loop invariant i_7: \forall integer k; 0 <= k <= j ==> r[k] == -2147483648;

            loop invariant i_8: 1 <= i <= j;

            loop invariant i_9: r[j] == price[i] + r[j - i];


            loop assigns r[j];
            loop assigns i;
        */
        for (int i = 1; i <= j; i++) {
            if (r[j] <= price[i] + r[j - i]){
                r[j] = price[i] + r[j - i];
            }
        }
    }
    return r[n];
}