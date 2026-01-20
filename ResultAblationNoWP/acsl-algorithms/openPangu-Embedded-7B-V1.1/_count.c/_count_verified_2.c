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
        loop invariant i_4: \forall integer number; 0 <= number <= k ==> count[number] == 0;

        loop invariant i_5: \forall integer i; 0 <= i < n ==> count[number] >= 0;

        loop invariant i_6: \forall integer i; 0 <= i < n ==> count[number] \forall \exists integer x in a..x; x == number; loop invariant \forall integer number; 0 <= number <= k ==> \exists integer i; 0 <= i < n && a[i] == number;

        loop invariant i_7: \forall integer number; 0 <= number <= k ==> \exists integer i; 0 <= i < n && a[i] == number;

        loop invariant i_8: \forall integer number; 0 <= number <= k ==> \forall integer i; 0 <= i < n && (a[i] == number || \exists j >= i; a[j] == number); loop invariant \forall integer number; 0 <= number <= k ==> \forall integer i; 0 <= i < n && (a[i] == number || \exists j; i <= j < n && a[j] == number); loop invariant \forall integer number; 0 <= number <= k ==> \forall integer i; i < n ==> \exists integer j; i <= j < n && a[j] == number;

        loop invariant i_9: \forall integer number; 0 <= number <= k ==> \forall integer i; 0 <= i < n && (a[i] == number || \exists j; i <= j < n && a[j] == number); loop invariant \forall integer number; 0 <= number <= k ==> \forall integer i; i < n ==> \exists integer j; i <= j < n && a[j] == number;

        loop invariant i_10: \forall integer number; 0 <= number <= k ==> \forall integer i; i < n ==> \exists integer j; i <= j < n && a[j] == number;

        loop invariant i_11: \forall integer i; 0 <= i < n ==> \exists integer number; 0 <= number <= k && count[number] > 0 && a[i] == number;


        loop assigns count[0..k]; 
        loop assigns number;
    */
    for (int number = 0; number <= k; number++){
        count[number] = 0;
        // Loop B
        /*@
            loop invariant i_12: \forall integer number; 0 <= number <= k ==> count[number] == 0;

            loop invariant i_13: \forall integer i; 0 <= i < n ==> count[number] >= 0;

            loop invariant i_14: \forall integer i; 0 <= i < n ==> count[number] \forall \exists integer x in a[0..i]; x == number; loop invariant \forall integer number; 0 <= number <= k ==> \exists integer i; 0 <= i < n && a[i] == number;

            loop invariant i_15: \forall integer number; 0 <= number <= k ==> \exists integer i; 0 <= i < n && a[i] == number;

            loop invariant i_16: \forall integer number; 0 <= number <= k ==> \forall integer i; 0 <= i < n && (a[i] == number || \exists j >= i; a[j] == number); loop invariant \forall integer number; 0 <= number <= k ==> \forall integer i; 0 <= i < n && (a[i] == number || \exists j; i <= j < n && a[j] == number); loop invariant \forall integer number; 0 <= number <= k ==> \forall integer i; i < n ==> \exists integer j; i <= j < n && a[j] == number;

            loop invariant i_17: \forall integer number; 0 <= number <= k ==> \forall integer i; 0 <= i < n && (a[i] == number || \exists j; i <= j < n && a[j] == number); loop invariant \forall integer number; 0 <= number <= k ==> \forall integer i; i < n ==> \exists integer j; i <= j < n && a[j] == number;

            loop invariant i_18: \forall integer number; 0 <= number <= k ==> \forall integer i; i < n ==> \exists integer j; i <= j < n && a[j] == number;

            loop invariant i_19: \forall integer i; 0 <= i < n ==> \exists integer number; 0 <= number <= k && count[number] > 0 && a[i] == number;


            loop assigns count[number];
            loop assigns i;
        */
        for (int i = 0; i < n; i++) {
            count[number] += (a[i] == number ? 1 : 0);
        }
    }
}