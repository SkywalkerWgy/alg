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
    ensures e_1: sorted(arr, 0, n);
    assigns arr[0..(n - 1)];
*/
void _select_sort(int* arr, int n)
{
    // Loop A
    /*@
        loop invariant i_22: i < n && i < n - 1;

        loop invariant i_23: \forall integer k in [i+1, n - 1]; \exists integer m in [0, i] such that arr[m] <= arr[k] && \forall integer l in [m+1, k]; m < k; loop invariant \forall integer k in [0, i - 1]; arr[k] <= arr[i];

        loop invariant i_24: \forall integer k in [0, i - 1]; arr[k] <= arr[i];

        loop invariant i_25: \forall integer k in [min, i - 1]; arr[k] <= arr[i];

        loop invariant i_26: arr[0..(n - 1)] is valid;

        loop invariant i_27: \forall integer j in [i, n - 1]; \exists integer m in [0, i] such that arr[m] <= arr[j] && \forall integer k in [m + 1, j]; arr[k] >= arr[m]; loop invariant \forall integer j in [i, min]; arr[j] >= arr[i];

        loop invariant i_28: \forall integer j in [i, min]; arr[j] >= arr[i];

        loop invariant i_29: \forall integer j in [0, min - 1]; arr[j] <= arr[min];

        loop invariant i_30: \forall integer j in [min, n - 1]; arr[j] >= arr[i];


        loop assigns i, arr[0..(n - 1)];
    */
    for (int i = 0; i < n - 1; i++)
    {
        int min = i;
        // Loop B
        /*@
            loop invariant i_31: i < n && i < n - 1;

            loop invariant i_32: \forall integer k in [i+1, n - 1]; \exists integer m in [0, i] such that arr[m] <= arr[k] && \forall integer l in [m+1, k]; arr[l] >= arr[m]; loop invariant i_24: \forall integer k in [0, i - 1]; arr[k] <= arr[i];

            loop invariant i_33: \forall integer k in [0, i - 1]; arr[k] <= arr[i];

            loop invariant i_34: \forall integer k in [min, i - 1]; arr[k] >= arr[i];

            loop invariant i_35: arr[0..(n - 1)] is valid;

            loop invariant i_36: \forall integer j in [i, n - 1]; \exists integer m in [0, i] such that arr[m] <= arr[j] && \forall integer k in [m+1, j]; arr[k] >= arr[m]; loop invariant i_28: \forall integer j in [0, min - 1]; arr[j] <= arr[min];

            loop invariant i_37: \forall integer j in [0, min - 1]; arr[j] <= arr[min];

            loop invariant i_38: \forall integer j in [min, n - 1]; arr[j] >= arr[i];


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