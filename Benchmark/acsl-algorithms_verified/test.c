/*@
  logic integer sum(int* array, integer begin, integer end) =
    begin >= end ? 0 : array[end-1] + sum(array, begin, end-1);
*/

/*@ 
    requires n >= 0 && \valid(t + (0..(n - 1))) ;
    ensures \result == sum(t, 0, n);
*/
int array_sum(int t[], int n) {
    int i;
    int s = 0;
    /*@ 
        loop invariant 0 <= i <= n;
        loop invariant s == sum(t, 0, i);
        loop assigns s, i;
        loop variant n - i;
    */
    for(i = 0; i < n; i++) {
        s += t[i]; 
    }
    return s;
}