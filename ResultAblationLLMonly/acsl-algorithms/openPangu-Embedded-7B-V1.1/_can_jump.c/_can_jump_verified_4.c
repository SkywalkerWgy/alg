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
        loop invariant i_10: 0 <= k;

        loop invariant i_11: i < n && k >= i;


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