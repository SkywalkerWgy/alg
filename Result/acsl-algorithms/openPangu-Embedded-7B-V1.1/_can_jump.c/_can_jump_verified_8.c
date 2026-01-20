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
    requires n > 0;
    requires \valid(nums + (0..(n - 1)));
    requires \forall integer i; 0 <= i < n ==> nums[i] >= 0;
    assigns \nothing;
    ensures e_1: ((\forall integer j; 0 <= j < n ==> \result >= j + nums[j]) && (\result >= n - 1)) || (\result == -1);
*/
int _can_jump(int* nums, int n) 
{
    int k = 0;
    // Loop A
    /*@
        loop invariant i_0: \forall integer k; 0 <= k < n ==> k >= 0 && k <= n - 1;

        loop invariant i_1: \forall integer i; 0 <= i < n ==> nums[i] >= 0;

        loop invariant i_3: \forall integer k; 0 <= k < n ==> k >= i;

        loop invariant i_7: \forall integer k; 0 <= k < n ==> k >= i && k >= 0 && k <= n - 1 && nums[k] >= 0 && k >= i;

        loop invariant i_8: \forall integer i; 0 <= i < n ==> i >= k && i >= 0 && i <= n - 1 && nums[i] >= 0;

        loop invariant i_9: \forall integer i; 0 <= i < n ==> i >= 0 && i <= n - 1 && nums[i] >= 0;

        loop invariant i_10: \forall integer k; 0 <= k < n ==> k >= i && k >= 0 && k <= n - 1 && nums[k] >= 0;


        loop assigns i;
        loop assigns k;
    */
    for(int i = 0; i < n; i++)
    {
        if(i > k)
        {
            return -1;
        }
        k = max(k, i + nums[i]);
    }
    return k;
}