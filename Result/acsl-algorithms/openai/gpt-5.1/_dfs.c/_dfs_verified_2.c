/*@
    predicate connect(int** graph, integer i, integer j, integer n) =
        0 <= i < n && 0 <= j < n && ((i == j) || (graph[i][j] == 1) || (graph[j][i] == 1) || (\exists integer k; 0 <= k < n && connect(graph, i, k, n) && connect(graph, k, j, n)));
*/

/*@
    requires 0 <= start < n;
    requires \valid(graph + (0..(n)));
    requires \valid(graph[0..(n)] + (0..(n)));
    requires \valid(dist + (0..(n)));
    requires \valid(visited + (0..(n)));
    requires \valid(stack + (0..(n)));
    requires \forall integer i, j; 0 <= i <= n && 0 <= j <= n && i != j ==> \separated(&graph[i] + (0..(n)), &graph[j] + (0..(n)), &dist[0..(n)], &visited[0..(n)], &stack[0..(n)]);
    requires \separated(&dist[0..(n)], &visited[0..(n)], &stack[0..(n)]);
    requires \forall integer j; 0 <= j <= n && j != start ==> visited[j] == 0 && dist[j] == -1;
    requires visited[start] == 1 && dist[start] == 0;
    requires stack[0] == start;
    requires \forall integer i, j; 0 <= i <= n ==> graph[i][i] == 1;
    requires \forall integer i, j; 0 <= i <= n && 0 <= j <= n ==> graph[i][j] == graph[j][i];
    requires \forall integer i, j; 0 <= i <= n && 0 <= j <= n ==> (graph[i][j] == 0 || graph[i][j] == 1);
    ensures e_1: \forall integer i; (0 <= i < n && visited[i] == 1) ==> connect(graph, i, start, n);
    assigns dist[0..(n)], visited[0..(n)], stack[0..(n)];
*/
void _dfs(int** graph, int* dist, int* visited, int* stack, int start, int n) {
    int top = 0;
    int node = start;
    // Loop A
    /*@
        loop invariant i_0: 0 <= start < n;

        loop invariant i_1: 0 <= top < n;

        loop invariant i_2: 0 <= node < n;

        loop invariant i_3: visited[start] == 1;

        loop invariant i_4: dist[start] == 0;

        loop invariant i_5: stack[0] == start;

        loop invariant i_6: visited[node] == 1;

        loop invariant i_7: \forall integer i; 0 <= i < n ==> (visited[i] == 0 || visited[i] == 1);

        loop invariant i_8: \forall integer i; 0 <= i < n && visited[i] == 0 ==> dist[i] == -1;

        loop invariant i_9: \forall integer i; 0 <= i < n && visited[i] == 1 ==> 0 <= dist[i];

        loop invariant i_10: \forall integer k; 0 <= k <= top ==> 0 <= stack[k] < n;

        loop invariant i_11: \forall integer k; 0 <= k <= top ==> visited[stack[k]] == 1;

        loop invariant i_12: \forall integer i; 0 <= i < n && visited[i] == 1 ==> connect(graph, i, start, n);

        loop invariant i_13: \forall integer i; 0 <= i < n ==> graph[i][i] == 1;

        loop invariant i_14: \forall integer i, j; 0 <= i < n && 0 <= j < n ==> graph[i][j] == graph[j][i];

        loop invariant i_15: \forall integer i, j; 0 <= i < n && 0 <= j < n ==> (graph[i][j] == 0 || graph[i][j] == 1);

        loop invariant i_16: \forall integer i, j; 0 <= i < n && 0 <= j < n && i != j ==> \separated(&graph[i] + (0..(n)), &graph[j] + (0..(n)), &dist[0..(n)], &visited[0..(n)], &stack[0..(n)]);

        loop invariant i_17: \separated(&dist[0..(n)], &visited[0..(n)], &stack[0..(n)]);

        loop invariant i_48: 0 <= top && top < n;

        loop invariant i_49: 0 <= node && node < n;

        loop invariant i_50: visited[start] == 1 && dist[start] == 0 && stack[0] == start;

        loop invariant i_51: \forall integer v; (0 <= v && v < n && visited[v] == 0) ==> dist[v] == -1;

        loop invariant i_52: \forall integer v; (0 <= v && v < n && visited[v] == 1) ==> dist[v] >= 0;

        loop invariant i_53: \forall integer k; (0 <= k && k <= top) ==> (0 <= stack[k] && stack[k] < n && visited[stack[k]] == 1);

        loop invariant i_54: \forall integer v; (0 <= v && v < n && visited[v] == 1) ==> connect(graph, v, start, n);

        loop invariant i_55: \forall integer a; (0 <= a && a < n) ==> graph[a][a] == 1;

        loop invariant i_56: \forall integer a, b; (0 <= a && a < n && 0 <= b && b < n) ==> graph[a][b] == graph[b][a];

        loop invariant i_57: \forall integer a, b; (0 <= a && a < n && 0 <= b && b < n) ==> (graph[a][b] == 0 || graph[a][b] == 1);


        loop assigns top;
        loop assigns node;
        loop assigns stack[0..(n)];
        loop assigns dist[0..(n)];
        loop assigns visited[0..(n)];
    */
    while (0 <= top && top < n) {
        // Loop B
        /*@
            loop invariant i_18: 0 <= start < n;

            loop invariant i_19: 0 <= top <= n;

            loop invariant i_20: 0 <= node < n;

            loop invariant i_21: visited[start] == 1;

            loop invariant i_22: dist[start] == 0;

            loop invariant i_23: stack[0] == start;

            loop invariant i_24: visited[node] == 1;

            loop invariant i_25: \forall integer v; 0 <= v < n ==> (visited[v] == 0 || visited[v] == 1);

            loop invariant i_26: \forall integer v; 0 <= v < n && visited[v] == 0 ==> dist[v] == -1;

            loop invariant i_27: \forall integer v; 0 <= v < n && visited[v] == 1 ==> 0 <= dist[v];

            loop invariant i_28: \forall integer k; 0 <= k <= top ==> 0 <= stack[k] < n;

            loop invariant i_29: \forall integer k; 0 <= k <= top ==> visited[stack[k]] == 1;

            loop invariant i_30: \forall integer v; 0 <= v < n && visited[v] == 1 ==> connect(graph, v, start, n);

            loop invariant i_31: \forall integer a; 0 <= a < n ==> graph[a][a] == 1;

            loop invariant i_32: \forall integer a, b; 0 <= a < n && 0 <= b < n ==> graph[a][b] == graph[b][a];

            loop invariant i_33: \forall integer a, b; 0 <= a < n && 0 <= b < n ==> (graph[a][b] == 0 || graph[a][b] == 1);

            loop invariant i_34: \forall integer a, b; 0 <= a < n && 0 <= b < n && a != b ==> \separated(&graph[a] + (0..(n)), &graph[b] + (0..(n)), &dist[0..(n)], &visited[0..(n)], &stack[0..(n)]);

            loop invariant i_35: \separated(&dist[0..(n)], &visited[0..(n)], &stack[0..(n)]);

            loop invariant i_36: 0 <= i <= n;

            loop invariant i_37: 0 <= i && i <= n;

            loop invariant i_38: 0 <= top && top <= n;

            loop invariant i_39: 0 <= node && node < n;

            loop invariant i_40: visited[start] == 1 && dist[start] == 0 && stack[0] == start;

            loop invariant i_41: \forall integer v; (0 <= v && v < n && visited[v] == 0) ==> dist[v] == -1;

            loop invariant i_42: \forall integer v; (0 <= v && v < n && visited[v] == 1) ==> dist[v] >= 0;

            loop invariant i_43: \forall integer k; (0 <= k && k <= top) ==> (0 <= stack[k] && stack[k] < n && visited[stack[k]] == 1);

            loop invariant i_44: \forall integer v; (0 <= v && v < n && visited[v] == 1) ==> connect(graph, v, start, n);

            loop invariant i_45: \forall integer a; (0 <= a && a < n) ==> graph[a][a] == 1;

            loop invariant i_46: \forall integer a, b; (0 <= a && a < n && 0 <= b && b < n) ==> graph[a][b] == graph[b][a];

            loop invariant i_47: \forall integer a, b; (0 <= a && a < n && 0 <= b && b < n) ==> (graph[a][b] == 0 || graph[a][b] == 1);


            loop assigns top;
            loop assigns stack[0..(n)];
            loop assigns dist[0..(n)];
            loop assigns visited[0..(n)];
            loop assigns i;
        */
        for (int i = 0; i < n; i++) {
            if (graph[node][i] == 1 && visited[i] == 0 && top < n) { 
                top++;
                stack[top] = i;
                visited[i] = 1;
                dist[i] = dist[node] + 1;
            }
        }
        top -= 1;
        if(0 <= top){
            node = stack[top];
        }
        else{
            break;
        }
    }
}