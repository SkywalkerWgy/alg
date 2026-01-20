

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
        loop invariant i_0: 0 <= i <= n;
        loop invariant i_1: -1 <= j < n;
        loop invariant i_2: \forall integer k, l; 0 <= k < i && 0 <= l < n ==> matrix[k][l] < target;
        loop invariant i_3: \forall integer k, l; i <= k < n && j < l < n ==> matrix[k][l] > target;
        loop invariant i_4: \forall integer k, l; 0 <= k < i && 0 <= l <= j ==> matrix[k][l] < target;
        loop invariant i_6: \forall integer k; 0 <= k < i ==> matrix[k][j] < target;
        loop invariant i_7: \forall integer k, l; 0 <= k < i && j < l < n ==> matrix[k][l] < target;
        loop invariant i_8: \forall integer k, l; i <= k < n && 0 <= l <= j ==> matrix[k][l] > target;
        loop invariant i_9: \forall integer k, l; i <= k < n && 0 <= l <= j && k == i && l == j ==> matrix[k][l] > target;
        loop invariant i_10: \forall integer k, l; i <= k < n && 0 <= l <= j && k == i ==> matrix[k][l] >= (k == i && l == j ? matrix[i][j] : 0);
        loop invariant i_11: \forall integer k, l; i <= k < n && 0 <= l <= j && k == i && l == j ==> matrix[k][l] == matrix[i][j];
        loop invariant i_12: \forall integer k, l; i <= k < n && 0 <= l <= j && k == i ==> matrix[k][l] > target;

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