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
        loop invariant i_57: 0 <= i < n;

        loop invariant i_58: dp[0..i] == 1;

        loop invariant i_59: \forall integer j in 0..i; dp[j] >= 1;

        loop invariant i_60: \forall integer j, k in 0..i; arr[j] < arr[k] ==> dp[j] <= dp[k];

        loop invariant i_61: \exists integer j in 0..i such that dp[j] == dp[k] && arr[j] < arr[k]; [Loop <Loop B>] loop invariant 0 <= j < i;

        loop invariant i_62: 0 <= j < i;

        loop invariant i_63: dp[i] >= dp[j] + 1;

        loop invariant i_64: \forall integer j in 0..i; if (arr[j] < arr[i]) then dp[i] >= dp[j] + 1;

        loop invariant i_65: \exists integer j in 0..i such that dp[j] == dp[i] && arr[j] < arr[i]; [Loop <Loop C>] loop invariant 0 <= i < n;

        loop invariant i_66: ans >= dp[i];

        loop invariant i_67: \exists integer i in 0..n such that dp[i] == dp[0] && arr[i] == arr[0]; loop invariant \forall integer i in 0..n; dp[i] >= 1;

        loop invariant i_68: \forall integer i in 0..n; dp[i] >= 1;


        loop assigns dp[0..(n - 1)];
        loop assigns i;
    */
    for (int i = 0; i < n; i++) {
        //@ ghost int cur = -1; 
        // Loop B
        /*@
            loop invariant i_81: 0 <= i < n;

            loop invariant i_82: dp[0..i] == 1;

            loop invariant i_83: \forall integer j in 0..i; dp[j] >= 1;

            loop invariant i_84: \forall integer j, k in 0..i; arr[j] < arr[k] ==> dp[j] <= dp[k];

            loop invariant i_85: \exists integer j in 0..i such that dp[j] == dp[k] && arr[j] < arr[k]; loop invariant i_62: 0 <= j < i;

            loop invariant i_86: 0 <= j < i;

            loop invariant i_87: dp[i] >= dp[j] + 1;

            loop invariant i_88: \forall integer j in 0..i; if (arr[j] < arr[i]) then dp[i] >= dp[j] + 1;

            loop invariant i_89: \exists integer j in 0..i such that dp[j] == dp[i] && arr[j] < arr[i]; [Loop <Loop B>] loop invariant 0 <= j < i;

            loop invariant i_90: ans >= dp[i];

            loop invariant i_91: \exists integer i in 0..n such that dp[i] == dp[0] && arr[i] == arr[0]; loop invariant i_68: \forall integer i in 0..n; dp[i] >= 1;

            loop invariant i_92: \forall integer i in 0..n; dp[i] >= 1;


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
        loop invariant i_69: 0 <= i < n;

        loop invariant i_70: dp[0..i] == 1;

        loop invariant i_71: \forall integer j in 0..i; dp[j] >= 1;

        loop invariant i_72: \forall integer j, k in 0..i; arr[j] < arr[k] ==> dp[j] <= dp[k];

        loop invariant i_73: \exists integer j in 0..i such that dp[j] == dp[k] && arr[j] < arr[k]; loop invariant i_61: 0 <= j < i;

        loop invariant i_74: 0 <= j < i;

        loop invariant i_75: dp[i] >= dp[j] + 1;

        loop invariant i_76: \forall integer j in 0..i; if (arr[j] < arr[i]) then dp[i] >= dp[j] + 1;

        loop invariant i_77: \exists integer j in 0..i such that dp[j] == dp[i] && arr[j] < arr[i]; [Loop <Loop C>] loop invariant 0 <= i < n;

        loop invariant i_78: ans >= dp[i];

        loop invariant i_79: \exists integer i in 0..n such that dp[i] == dp[0] && arr[i] == arr[0]; loop invariant i_68: \forall integer i in 0..n; dp[i] >= 1;

        loop invariant i_80: \forall integer i in 0..n; dp[i] >= 1;


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