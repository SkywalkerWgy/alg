

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
        loop invariant i_0: i >= 0 && i < n && j >= 0 && j < n;

        loop invariant i_1: i < n || j < 0;

        loop invariant i_2: i < n && j >= 0 && i <= j;

        loop invariant i_4: i >= 0 && j < n;


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