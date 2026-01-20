/*@ requires n >= 0;
    requires \valid(a + (0..n-1));

    assigns \nothing;

    behavior empty:
      assumes n == 0;
      ensures \result == 0;
    behavior not_empty:
      assumes 0 < n;
      ensures 0 <= \result < n;
      ensures \forall integer i; 0 <= i < n ==> a[i] >= a[\result];
    complete behaviors;
    disjoint behaviors;
*/
int _min_seq(int *a, int n) {
    if (n == 0) {
        return 0;
    }
    int min = 0;

    /*@
        loop invariant 0 <= i <= n;
        loop invariant 0 <= min < n;
        loop invariant \forall integer k; 0 <= k < i ==> a[k] >= a[min];
        loop assigns min, i;
        loop variant n - i;
    */
    for (int i = 1; i < n; i++) {
        if (a[min] > a[i]) {
            min = i;
        }
    }
    return min;
}