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
    ensures \forall integer p, q; 0 <= p <= q < n ==> height[p] <= leftMax[q];
    ensures \forall integer p, q; 0 <= p <= q < n ==> height[q] <= rightMax[p];
    ensures \result == trap_rain(leftMax, rightMax, height, 0, n, n);
*/
int _trap_rain(int* height, int* leftMax, int* rightMax, int n) {
    leftMax[0] = height[0];
    /*@
        loop invariant 1 <= i <= n;
        loop invariant \forall integer p, q; 0 <= p <= q < i ==> height[p] <= leftMax[q];
        loop assigns leftMax[1..(n - 1)];
        loop assigns i;
    */
    for (int i = 1; i < n; ++i) {
        leftMax[i] = max(leftMax[i - 1], height[i]);
    }

    rightMax[n - 1] = height[n - 1];
    /*@
        loop invariant -1 <= i <= n - 2;
        loop invariant \forall integer p, q; i < p <= q <= n - 1 ==> height[q] <= rightMax[p];
        loop assigns rightMax[0..(n - 2)];
        loop assigns i;
    */
    for (int i = n - 2; i >= 0; --i) {
        rightMax[i] = max(rightMax[i + 1], height[i]);
    }

    int ans = 0;

    /*@
        loop invariant 0 <= i <= n;
        loop invariant ans == trap_rain(leftMax, rightMax, height, 0, i, n);
        loop assigns ans;
        loop assigns i;
    */
    for (int i = 0; i < n; ++i) {
        ans += min(leftMax[i], rightMax[i]) - height[i];
    }
    return ans;
}