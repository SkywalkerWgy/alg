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
  logic integer trap_rain(int* leftMax, int* rightMax, int* height, integer i, integer j, integer n) =
    (i >= 0 && j >= 0 && n > 0 && i < j && i < n && j <= n) ? trap_rain(leftMax, rightMax, height, i, j - 1, n) + (leftMax[j - 1] >= rightMax[j - 1] ? rightMax[j - 1] : leftMax[j - 1]) - height[j - 1] : 0;
*/

/*@
    requires n > 0;
    requires \valid(height + (0..(n - 1)));
    requires \valid(leftMax + (0..(n - 1)));
    requires \valid(rightMax + (0..(n - 1)));
    requires \separated(&height[0..(n - 1)], &leftMax[0..(n - 1)], &rightMax[0..(n - 1)]);
    requires \forall integer i; 0 <= i < n ==> height[i] >= 0;
    requires \forall integer i; 0 <= i < n ==> leftMax[i] == 0;
    requires \forall integer i; 0 <= i < n ==> rightMax[i] == 0;
    assigns leftMax[0..(n - 1)];
    assigns rightMax[0..(n - 1)];
    ensures e_1: \forall integer p, q; 0 <= p <= q < n ==> height[p] <= leftMax[q];
    ensures e_2: \forall integer p, q; 0 <= p <= q < n ==> height[q] <= rightMax[p];
    ensures e_3: \result == trap_rain(leftMax, rightMax, height, 0, n, n);
*/
int _trap_rain(int* height, int* leftMax, int* rightMax, int n) {
    leftMax[0] = height[0];
    // Loop A
    /*@
        loop invariant i_1: \forall integer p, q; 0 <= p <= q < i ==> height[p] <= leftMax[q];

        loop invariant i_2: 1 <= i <= n;

        loop invariant i_16: \forall integer p; 0 <= p < i ==> height[p] <= leftMax[p];

        loop invariant i_20: \forall integer p; 0 <= p < i ==> leftMax[p] >= height[p];

        loop invariant i_27: \forall integer p; 0 <= p < i ==> leftMax[p] == \max(height[0..p]);

        loop invariant i_28: \forall integer p; 0 <= p < n ==> rightMax[p] == 0;


        loop assigns leftMax[1..(n - 1)];
        loop assigns i;
    */
    for (int i = 1; i < n; ++i) {
        leftMax[i] = max(leftMax[i - 1], height[i]);
    }

    rightMax[n - 1] = height[n - 1];
    // Loop B
    /*@
        loop invariant i_5: -1 <= i <= n - 2;

        loop invariant i_13: \forall integer p; 0 <= p < n ==> height[p] <= rightMax[p];

        loop invariant i_17: \forall integer p; i < p < n ==> height[p] <= rightMax[p];

        loop invariant i_18: \forall integer p, q; 0 <= p <= q < n ==> height[q] <= rightMax[p];

        loop invariant i_21: \forall integer p; i < p < n ==> rightMax[p] >= height[p];

        loop invariant i_22: \forall integer p; p == n-1 ==> rightMax[p] >= height[p];

        loop invariant i_25: \forall integer p, q; i < p <= q < n ==> height[q] <= rightMax[p];

        loop invariant i_29: \forall integer p; 0 <= p < n ==> rightMax[p] == \max(height[p..n-1]);


        loop assigns rightMax[0..(n - 2)];
        loop assigns i;
    */
    for (int i = n - 2; i >= 0; --i) {
        rightMax[i] = max(rightMax[i + 1], height[i]);
    }

    int ans = 0;

    // Loop C
    /*@
        loop invariant i_6: \forall integer k; 0 <= k < i ==> ans == trap_rain(leftMax, rightMax, height, 0, k, n);

        loop invariant i_7: 0 <= i <= n;

        loop invariant i_9: ans == (i == 0 ? 0 : trap_rain(leftMax, rightMax, height, 0, i, n));

        loop invariant i_10: ans == trap_rain(leftMax, rightMax, height, 0, i, n);

        loop invariant i_11: \forall integer p; 0 <= p < n ==> (i <= p ==> height[p] <= rightMax[p]);

        loop invariant i_14: \forall integer p, q; 0 <= p <= q < n ==> height[q] <= rightMax[p];

        loop invariant i_19: \forall integer k; 0 <= k < i ==> trap_rain(leftMax, rightMax, height, 0, k, n) == trap_rain(leftMax, rightMax, height, 0, k, n);

        loop invariant i_26: \forall integer k; 0 <= k < i ==> ans >= trap_rain(leftMax, rightMax, height, 0, k, n);

        loop invariant i_30: \forall integer k; 0 <= k < i ==> ans == trap_rain(leftMax, rightMax, height, 0, k + 1, n);


        loop assigns ans;
        loop assigns i;
    */
    for (int i = 0; i < n; ++i) {
        ans += min(leftMax[i], rightMax[i]) - height[i];
    }
    return ans;
}