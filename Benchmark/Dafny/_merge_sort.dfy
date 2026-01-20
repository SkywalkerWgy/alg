predicate IsPermutation<T(==)>(input: seq<T>, output: seq<T>)
{
    multiset(input) == multiset(output)
}

predicate Sorted(a: seq<int>)
{
    forall j, k :: 0 <= j <= k < |a| ==> a[j] <= a[k]
}

predicate merged(a1: seq<int>, a2: seq<int>, b: seq<int>)
{
  multiset(a1) + multiset(a2) == multiset(b)
}

method merge(a1: seq<int>, a2: seq<int>, start: int, end: int, b: array<int>)
    modifies b
    requires Sorted(a1)
    requires Sorted(a2)
    requires end - start == |a1| + |a2|
    requires 0 <= start <= end <= b.Length
    ensures Sorted(b[start..end])
    ensures merged(a1, a2, b[start..end])
    ensures forall p:: 0 <= p < start ==> old(b[p]) == b[p]
    ensures forall p:: end <= p < b.Length ==> old(b[p]) == b[p]
{
  assert forall xs : seq<int> :: xs[0..|xs|] == xs;
  assert forall xs : seq<int>, a,b : int :: 0 <= a < b < |xs| ==> xs[a..b+1] == xs[a..b] + [xs[b]];
  var a1Pos := 0;
  var a2Pos := 0;
  var k := start;
  while k < end
    invariant (start <= k && k <= end)
    invariant Sorted(b[start..k])
    invariant (|a1| - a1Pos) + (|a2| - a2Pos) == end - k
    invariant 0 <= a1Pos <= |a1|
    invariant 0 <= a2Pos <= |a2|
    invariant forall i :: start <= i < k && a1Pos < |a1| ==> b[i] <= a1[a1Pos]
    invariant forall i :: start <= i < k && a2Pos < |a2| ==> b[i] <= a2[a2Pos]
    invariant merged(a1[0..a1Pos], a2[0..a2Pos], b[start..k])
    invariant forall p:: 0 <= p < start ==> old(b[p]) == b[p]
    invariant forall p:: end <= p < b.Length ==> old(b[p]) == b[p]
  {
    if a1Pos < |a1| && a2Pos < |a2| && a1[a1Pos] <= a2[a2Pos] {
      b[k] := a1[a1Pos];
      a1Pos := a1Pos + 1;
    } else if a1Pos < |a1| && a2Pos < |a2| && a1[a1Pos] > a2[a2Pos] {
      b[k] := a2[a2Pos];
      a2Pos := a2Pos + 1;
    } else if a1Pos < |a1| {
      assert(a2Pos >= |a2|);
      b[k] := a1[a1Pos];
      a1Pos := a1Pos + 1;
    } else {
      assert(a1Pos >= |a1|);
      b[k] := a2[a2Pos];
      a2Pos := a2Pos + 1;
    }
    k := k + 1;
  }
}

// method MergeSort(arr: array<int>, left: int, right: int)
//     modifies arr
//     decreases *
//     requires 0 <= left <= right <= arr.Length
//     ensures IsPermutation(old(arr[left..right]), arr[left..right])  
//     ensures Sorted(arr[left..right]) 
//     ensures forall p:: 0 <= p < left ==> old(arr[p]) == arr[p]
//     ensures forall p:: right <= p < arr.Length ==> old(arr[p]) == arr[p]
// {
//     assert forall xs : seq<int> :: xs[0..|xs|] == xs;
//     assert forall xs : seq<int>, a,b : int :: 0 <= a < b < |xs| ==> xs[a..b+1] == xs[a..b] + [xs[b]];
//     if left == right {
//         return;
//     }

//     var mid := (left + right) / 2;

//     MergeSort(arr, mid, right);
//     MergeSort(arr, left, mid);
//     merge(arr[left..mid], arr[mid..right], left, right, arr);
// }