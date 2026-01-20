method LinearSearch(a: array<int>, key: int) returns (ret: int) 
  requires a.Length > 0
  ensures ret >= 0 ==> 0 <= ret < a.Length && a[ret] == key
  ensures ret < 0 ==> forall j :: 0 <= j < a.Length ==> a[j] != key
{
  ret := -1;
  var i := 0;
  while (ret == -1 && i < a.Length) 
    invariant ret >= 0 ==> 0 <= ret < a.Length && a[ret] == key
    invariant ret < 0 ==> 0 <= i <= a.Length && forall j ::  0 <= j < i ==> a[j] != key
  {
    if (a[i] == key) { ret := i; }
    else { i := i + 1; }
  } 
  return ret;
}