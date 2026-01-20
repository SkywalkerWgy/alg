/*@
  predicate sorted{Here}(int* a, integer start_index, integer end_index) =
    \forall integer k1, k2;
    start_index <= k1 <= k2 <= end_index ==> a[k1] <= a[k2];
*/

/*@
  requires \valid(x) && \valid(y);
  assigns *x, *y;
  ensures *x == \old(*y) && *y == \old(*x);
*/
void swap(int *x, int *y) {
  int tmp = *x;
  *x = *y;
  *y = tmp;
}

/*@
requires lo <= hi;
requires \valid(a + (lo .. hi));
assigns a[lo..hi];
ensures lo <= \result <= hi;
ensures \forall integer i; lo <= i <= \result ==> a[i] <= a[\result];
ensures \forall integer i; \result <= i <= hi ==> a[i] >= a[\result];
ensures lo <= \result <= hi;
*/
int partition(int* a, int lo, int hi) {
  int pivot = a[hi];
  int i = lo - 1;
  int j;

  /*@
    loop invariant lo <= j <= hi;
    loop invariant lo - 1 <= i < j;
    loop invariant \forall integer k; lo <= k <= i ==> a[k] <= pivot;
    loop invariant \forall integer k; i < k < j ==> a[k] > pivot;
    loop invariant a[hi] == pivot;
    loop assigns a[lo..hi], i, j;
    loop variant hi - j;
  */
  for (j = lo; j < hi; j++) {
      if (a[j] <= pivot) {
          i++;
          swap(&a[i], &a[j]);
      }
  }
  swap(&a[i + 1], &a[hi]);
  return i + 1;
}

/*@ 
    requires \valid(t + (l..r));
    decreases r - l;
    assigns t[l..r];
 */
void quick_rec(int* t, int l, int r) {
    if (l >= r) return;
    int pivot = partition(t, l, r);
    quick_rec(t, l, pivot - 1);
    quick_rec(t, pivot + 1, r);
    
}

/*@ requires n > 0;
    requires \valid(t + (0..n-1));
    assigns t[0..n-1];
*/
void _quick_sort(int* t, int n) {
    quick_rec(t, 0, n - 1);
}