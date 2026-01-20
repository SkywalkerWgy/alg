function SeqSum(s: seq<int>): int
{
    if s == [] then 0 else s[0] + SeqSum(s[1..])
}

function max(a: int, b: int): int
{
   if a >= b then a else b
}

method MaxSubarray(a: array<int>) returns (ret: int)
    requires a.Length > 1
    ensures forall i, j :: 0 <= i < j <= a.Length ==> SeqSum(a[i..j]) <= ret
    ensures exists i, j :: 0 <= i < j <= a.Length && ret == SeqSum(a[i..j])
{
    var current_sum := a[0];
    var max_sum := a[0];
    for i := 1 to a.Length 
        invariant 1 <= i <= a.Length 
        invariant a.Length > 1
        invariant current_sum <= max_sum
        invariant max_sum == max(current_sum, max_sum)
        invariant exists p, q:: 0 <= p < q <= i && current_sum == SeqSum(a[p..q])
        invariant exists p, q:: 0 <= p < q <= i && max_sum == SeqSum(a[p..q])
        invariant forall p, q:: 0 <= p < q <= i ==> SeqSum(a[p..q]) <= max_sum
        invariant forall p:: 0 <= p < i ==> SeqSum(a[p..i]) <= current_sum
    {

        if a[i] < current_sum + a[i]
        {
            current_sum := current_sum + a[i];
        }
        else
        {
            current_sum := a[i];
        }

        if current_sum > max_sum
        {
            max_sum := current_sum;
        }
    }
    return max_sum;
}