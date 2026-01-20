/*@ requires n >= 0;
    requires \valid(a + (0..n-1));

    assigns \nothing;

    behavior empty:
      assumes n == 0;
      ensures e_1: \result == 0;
    behavior not_empty:
      assumes 0 < n;
      ensures e_2: 0 <= \result < n;
      ensures e_3: \forall integer i; 0 <= i < n ==> a[i] <= a[\result];
    complete behaviors;
    disjoint behaviors;
*/
int _max_seq(int *a, int n) {
    if (n == 0) {
        return 0;
    }
    int max = 0;

    // Loop A
    /*@
        loop invariant i_0: 0 <= max < n;

        loop invariant i_1: \forall integer k; 0 <= k < i ==> a[k] <= a[max];

        loop invariant i_2: \exists integer max; 0 <= max < n;

        loop invariant i_3: \forall integer p; 0 <= p < n ==> a[p] <= a[max];

        loop invariant i_4: \forall integer k; 0 <= k < max ==> a[k] <= a[max];


        loop assigns max, i;
    */
    for (int i = 1; i < n; i++) {
        if (a[max] < a[i]) {
            max = i;
        }
    }
    return max;
}