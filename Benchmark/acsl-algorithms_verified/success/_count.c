/*@
  logic integer sum(int* array, integer begin, integer end) =
    begin >= end ? 0 : array[end - 1] + sum(array, begin, end - 1);
*/

/*@
    logic integer countnumber(int* array, integer begin, integer end, integer number) =
        begin >= end ? 0 : ((array[end - 1] == number ? 1 : 0) + countnumber(array, begin, end - 1, number));
*/

/*@ lemma unchanged{L1,L2}: \forall int* array; \forall integer begin, end, number;
    (\forall integer i; begin <= i < end ==> \at(array[i], L1) == \at(array[i], L2)) ==>
    countnumber{L1}(array, begin, end, number) == countnumber{L2}(array, begin, end, number);
*/

/*@
    predicate sorted{L}(int* a, integer lo, integer hi) =
        \forall integer i, j; lo <= i < j < hi ==> a[i] <= a[j];
*/

/*@
    requires n > 0;
    requires k > 0;
    requires \valid(a + (0..(n - 1)));
    requires \valid(b + (0..(n - 1)));
    requires \valid(count + (0..k));
    requires \separated(&a[0..(n - 1)], &b[0..(n - 1)], &count[0..(k)]);
    requires \forall integer i; 0 <= i < n ==> 0 <= a[i] <= k;
    requires \forall integer i; 0 <= i <= k ==> count[i] == 0;
    assigns count[0..k];
    ensures \forall integer x; 0 <= x <= k ==> count[x] == countnumber(a, 0, n, x);
    ensures \forall integer x; 0 <= x <= k ==> count[x] >= 0;
*/
void _count(int* a, int* b, int n, int* count, int k) {
    /*@
        loop invariant 0 <= number <= k + 1;
        loop invariant k > 0;
        loop invariant n > 0;
        loop invariant \forall integer x; 0 <= x <= k ==> count[x] >= 0;
        loop invariant \forall integer i; 0 <= i < n ==> 0 <= a[i] <= k;
        loop invariant \forall integer x; 0 <= x < number ==> count[x] == countnumber(a, 0, n, x);
        loop invariant \forall integer x; number <= x <= k ==> count[x] == 0;
        loop assigns count[0..k]; loop assigns number;
        loop variant k - number;
    */
    for (int number = 0; number <= k; number++){
        count[number] = 0;
        /*@
            loop invariant 0 <= i <= n;
            loop invariant 0 <= number <= k;
            loop invariant \forall integer x; 0 <= x <= k ==> count[x] >= 0;
            loop invariant \forall integer i; 0 <= i < n ==> 0 <= a[i] <= k;
            loop invariant count[number] == countnumber(a, 0, i, number);
            loop assigns count[number];
            loop assigns i;
            loop variant n - i;
        */
        for (int i = 0; i < n; i++) {
            count[number] += (a[i] == number ? 1 : 0);
        }
    }
}