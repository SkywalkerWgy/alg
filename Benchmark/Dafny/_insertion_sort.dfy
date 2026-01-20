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

method InsertionSort(arr: array<int>) returns (out: array<int>)
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
    var j := 1;
    while i < arr.Length
        invariant 1 <= i <= arr.Length
        invariant Sorted(arr[0..i])
    {
        var key := arr[i];
        j := i;
        while j > 0 && arr[j - 1] > key
            invariant 0 <= j <= i
            invariant j == i ==> Sorted(arr[0..i])
            invariant j < i ==> Sorted(arr[0..i + 1])
            invariant forall k :: j <= k < i ==> arr[k] > key
        {
            arr[j] := arr[j - 1];
            j := j - 1;
        }
        arr[j] := key;
        i := i + 1;
    }
    return arr;
}