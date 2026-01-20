
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
    predicate is_min(integer a, integer b, integer result) =
        result <= a && 
        result <= b && 
        (result == a || result == b);
*/

/*@
    assigns \nothing;
    ensures is_min(a, b, \result);
*/
int min(int a, int b) {
  int min_val = a >= b ? b : a;
  return min_val;
}

/*@
    requires n > 0;
    requires \valid(prices + (0..(n-1)));
    assigns \nothing;
    ensures e_1: \forall integer p, q; 0 < p < q < n ==> \result >= prices[q] - prices[p];
*/
int _max_profit(int* prices, int n) {
    int minprice = 2147483647, maxprofit = 0;

    // Loop A
    /*@
        loop invariant i_0: 0 <= i < n;

        loop invariant i_11: 0 <= i < n && 0 <= i_0 < n;


        loop assigns i, maxprofit, minprice;
    */
    for (int i = 0; i < n ; i++) {
        int price = prices[i];
        maxprofit = max(maxprofit, price - minprice);
        minprice = min(price, minprice);
    }
    return maxprofit;
}