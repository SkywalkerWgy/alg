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
        loop invariant i_19: 0 <= top < n;

        loop invariant i_20: 0 <= node < n;

        loop invariant i_21: visited[start] == 1 && dist[start] == 0;

        loop invariant i_22: \forall integer i; 0 <= i < n && visited[i] == 1 ==> connect(graph, i, start, n);

        loop invariant i_23: \forall integer i; 0 <= i < top ==> \valid(stack + (0..i));

        loop invariant i_24: stack[top] == node;

        loop invariant i_25: \forall integer i; 0 <= i < n && visited[i] == 1 ==> dist[i] != -1;

        loop invariant i_26: \forall integer i; 0 <= i < n && visited[i] == 0 ==> dist[i] == -1;

        loop invariant i_27: \forall integer i; 0 <= i < n ==> (visited[i] == 0 || visited[i] == 1);


        loop assigns top;
        loop assigns node;
        loop assigns stack[0..(n)];
        loop assigns dist[0..(n)];
        loop assigns visited[0..(n)];
    */
    while (0 <= top && top < n) {
        // Loop B
        /*@
            loop invariant i_28: 0 <= i <= n;

            loop invariant i_29: \forall integer j; 0 <= j < i && graph[node][j] == 1 && visited[j] == 0 && top < n ==> visited[j] == 1 && dist[j] == dist[node] + 1 && stack[top] == j;

            loop invariant i_30: \forall integer j; 0 <= j < i && (graph[node][j] == 0 || visited[j] == 1 || top >= n) ==> visited[j] == \at(visited[j], Pre) && dist[j] == \at(dist[j], Pre);

            loop invariant i_31: \forall integer k; 0 <= k < n && visited[k] == 1 ==> connect(graph, k, start, n);

            loop invariant i_32: \forall integer k; 0 <= k < n && visited[k] == 1 ==> dist[k] != -1;

            loop invariant i_33: \forall integer k; 0 <= k < n && visited[k] == 0 ==> dist[k] == -1;

            loop invariant i_34: \forall integer k; 0 <= k < n ==> (visited[k] == 0 || visited[k] == 1);

            loop invariant i_35: 0 <= top < n;

            loop invariant i_36: stack[top] == node;


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