predicate IsPermutation<T(==)>(input: array<T>, output: array<T>)
    reads input
    reads output
{
    multiset(input[..]) == multiset(output[..])
}

predicate Sorted(a: seq<int>)
{
    forall j, k :: 0 <= j <= k < |a| ==> a[j] <= a[k]
}

method BubbleSort(arr: array<int>) returns (out: array<int>)
    modifies arr
    ensures IsPermutation(arr, out)  
    ensures Sorted(out[..])              
{
    out := arr;  
    if arr.Length <= 1 {
        return;    
    }
    ghost var initialSeq := arr[..];
    
    var i := 1;
    while (i < arr.Length)
        invariant 0 < i <= arr.Length
        invariant Sorted(arr[0..i])
    {
        var j := i;
        while (j > 0 && arr[j-1] > arr[j])
            invariant 0 <= j <= i < arr.Length
            invariant i == j ==> Sorted(arr[0..i])
            invariant j < i ==> (Sorted(arr[j..i + 1]) && Sorted(arr[0..j]))
            invariant j < i && j > 0 ==> arr[j - 1] <= arr[j + 1]
        {
            arr[j], arr[j - 1] := arr[j - 1], arr[j];
            j := j - 1;
        }
        i := i + 1;
    }
    return arr;
}