/*@
    requires n > 1;
    requires \valid(arr + (0..(n - 1)));
    requires \valid(dp + (0..(n - 1)));
    requires \separated(&arr[0..(n - 1)], &dp[0..(n - 1)]);
    requires \forall integer k; 0 <= k < n ==> dp[k] == 1;
    ensures e_1: \forall integer p, q; (0 <= q < p < n && arr[q] < arr[p]) ==> dp[p] >= dp[q] + 1;
    ensures e_2: \forall integer q; (0 <= q < n) ==> \result >= dp[q];
    ensures e_3: \exists integer q; (0 <= q < n) && \result == dp[q];
    assigns dp[0..(n - 1)];
*/
int _lis(int arr[], int n, int dp[]) {
    // Loop A
    /*@
        loop invariant i_45: \forall i; 0 <= i < n ==> dp[i] >= 0;

        loop invariant i_46: \forall j; 0 <= j < i ==> dp[i] >= dp[j] + 1;

        loop invariant i_47: \forall i; 0 <= i < n ==> dp[i] <= dp[0];


        loop assigns dp[0..(n - 1)];
        loop assigns i;
    */
    for (int i = 0; i < n; i++) {
        //@ ghost int cur = -1; 
        // Loop B
        /*@
            loop invariant i_51: \forall i; 0 <= i < n ==> dp[i] >= 0;

            loop invariant i_52: \forall j; 0 <= j < i ==> dp[i] >= dp[j] + 1;

            loop invariant i_53: \forall i; 0 <= i < n ==> dp[i] <= dp[0];

            loop invariant i_54: ans >= 0;

            loop invariant i_55: dp[i] >= 0 && dp[i] <= dp[0] for all 0 <= i < n;

            loop invariant i_56: ans >= 0 && ans <= dp[0];


            loop assigns dp[i];
            loop assigns j;
            loop assigns cur;
        */
        for (int j = 0; j < i; j++) {
            if (arr[j] < arr[i]){
                if (dp[i] < dp[j] + 1){
                    dp[i] = dp[j] + 1;
                    //@ ghost cur = j;
                }
            }
        }
    }

    //@ ghost int res = 0;
    int ans = dp[0];

    // Loop C
    /*@
        loop invariant i_48: ans >= 0;

        loop invariant i_49: dp[i] >= 0 && dp[i] <= dp[0] for all 0 <= i < n;

        loop invariant i_50: ans >= 0 && ans <= dp[0];


        loop assigns i;
        loop assigns res;
        loop assigns ans;
    */
    for (int i = 0; i < n; i++) {
        if (dp[i] > ans) {
            ans = dp[i];
            //@ ghost res = i;
        }
    }

    return ans;
}