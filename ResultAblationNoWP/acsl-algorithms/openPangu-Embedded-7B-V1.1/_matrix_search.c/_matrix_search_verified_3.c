

/*@ 
    requires n == 10;

    requires \valid(matrix + (0..(n)));
    requires \valid(matrix[0..(n)] + (0..(n)));

    requires \forall integer row, k1, k2; 0 <= row < n && 0 <= k1 < k2 < n ==> matrix[row][k1] <= matrix[row][k2];
    requires \forall integer col, k1, k2; 0 <= col < n && 0 <= k1 < k2 < n ==> matrix[k1][col] <= matrix[k2][col];

    assigns \nothing;

    ensures e_1: \result == 0 ==> \forall integer i, j; 0 <= i < n && 0 <= j < n ==> matrix[i][j] != target;
    ensures e_2: \result == 1 ==> \exists integer i, j; 0 <= i < n && 0 <= j < n && matrix[i][j] == target;
*/
int _matrix_search(int** matrix, int n, int target){
    int i = 0, j = n - 1;
    // Loop A
    /*@
        loop invariant i_2: i >= 0 && i < n && j >= 0 && j < n;

        loop invariant i_3: \forall integer k; 0 <= k < i ==> matrix[i][k] >= target || k == j-1 && matrix[i][j-1] >= target;

        loop invariant i_4: \exists integer k; 0 <= k < i && (j - k == n - 1 || k == j-1 && matrix[i][j-1] >= target);

        loop invariant i_5: \forall integer col; 0 <= col < n && matrix[k][col] <= matrix[i][k] for some k <= i, j-1;

        loop invariant i_6: \forall integer row; 0 <= row < n && for some row, \at(matrix[row], End_r) ==> row >= i && row < j;

        loop invariant i_7: \forall integer row, k; 0 <= row < n && 0 <= k < j && k >= i && k < j ==> matrix[row][k] <= matrix[row][j];


        loop assigns i, j;
    */
    while(i < n && j >= 0) {
        if(matrix[i][j] == target) 
            return 1;
        else if(matrix[i][j] > target) 
            j--;
        else 
            i++;
    }
    return 0;
}