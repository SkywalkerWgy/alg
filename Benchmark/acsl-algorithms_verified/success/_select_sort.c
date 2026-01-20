/*@
  predicate sorted(int *t, integer lo, integer hi) =
    \forall integer i, j; lo <= i <= j < hi ==> t[i] <= t[j];
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

/*@ requires \valid(arr+(0..(n - 1)));
    requires n > 0;
    ensures sorted(arr, 0, n);
    assigns arr[0..(n - 1)];
*/
void _select_sort(int* arr, int n)
{
    /*@
        loop invariant i1: 0 <= i <= n - 1;
        loop invariant i2: sorted(arr, 0, i);
        loop invariant i3: \forall integer p, q; 0 <= p < i && i <= q < n ==> arr[p] <= arr[q];
        loop assigns i, arr[0..(n - 1)];
    */
    for (int i = 0; i < n - 1; i++)
    {
        int min = i;
        /*@
            loop invariant i4: sorted(arr, 0, i);
            loop invariant i5: 0 <= i < n;
            loop invariant i6: i <= j <= n;
            loop invariant i7: i <= min < n;
            loop invariant i8: \forall integer k; i <= k < j ==> arr[k] >= arr[min];
            loop invariant i9: \forall integer p, q; 0 <= p < i && i <= q < n ==> arr[p] <= arr[q];
            loop assigns j, min;
        */
        for (int j = i; j < n; j++){  
            if (arr[j] < arr[min]){
                min = j;    
            }
        } 
        swap(&arr[min], &arr[i]);   
    }
}