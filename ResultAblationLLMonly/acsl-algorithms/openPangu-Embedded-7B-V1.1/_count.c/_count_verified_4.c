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
    ensures e_1: \forall integer x; 0 <= x <= k ==> count[x] == countnumber(a, 0, n, x);
    ensures e_2: \forall integer x; 0 <= x <= k ==> count[x] >= 0;
*/
void _count(int* a, int* b, int n, int* count, int k) {
    // Loop A
    /*@
        loop invariant i_11: 0 <= number <= k;

        loop invariant i_12: \forall integer i; 0 <= i < n ==> 0 <= count[number] <= k;

        loop invariant i_13: \forall integer i; 0 <= count[number] < n;

        loop invariant i_14: \forall integer i; count[number] \forall int x; (x == number ? 1 : 0) + countnumber(array, 0, i, x) == count[number];

        loop invariant i_15: \forall integer i; 0 <= count[number] && 0 <= array[i] && array[i] <= k;


        loop assigns count[0..k]; 
        loop assigns number;
    */
    for (int number = 0; number <= k; number++){
        count[number] = 0;
        // Loop B
        /*@
            loop invariant i_16: for the following loop. [Loop <LOOP A>] loop invariant 0 <= number <= k;

            loop invariant i_17: 0 <= number <= k;

            loop invariant i_18: \forall integer i; 0 <= count[number] <= k;

            loop invariant i_19: \forall integer i; 0 <= count[number] < n;

            loop invariant i_20: \forall integer i; count[number] \forall int x; (x == number ? 1 : 0) + countnumber(array, 0, i, x) == count[number];

            loop invariant i_21: \forall integer i; 0 <= count[number] && 0 <= array[i] && array[i] <= k;


            loop assigns count[number];
            loop assigns i;
        */
        for (int i = 0; i < n; i++) {
            count[number] += (a[i] == number ? 1 : 0);
        }
    }
}