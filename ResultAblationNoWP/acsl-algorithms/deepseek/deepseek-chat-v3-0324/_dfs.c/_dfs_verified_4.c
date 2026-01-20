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
        loop invariant i_56: 0 <= top <= n;

        loop invariant i_57: \forall integer i; 0 <= i <= top ==> visited[stack[i]] == 1;

        loop invariant i_58: \forall integer i; 0 <= i <= top ==> dist[stack[i]] == dist[start] + \sum(0 <= k < i; 1);

        loop invariant i_59: \forall integer i; 0 <= i <= top ==> connect(graph, stack[i], start, n);

        loop invariant i_60: \forall integer i; 0 <= i < n && visited[i] == 1 ==> connect(graph, i, start, n);

        loop invariant i_61: \forall integer i; 0 <= i < n && visited[i] == 1 ==> dist[i] != -1;

        loop invariant i_62: \forall integer i; 0 <= i < n && visited[i] == 0 ==> dist[i] == -1;

        loop invariant i_63: stack[0] == start;

        loop invariant i_64: visited[start] == 1;

        loop invariant i_65: dist[start] == 0;


        loop assigns top;
        loop assigns node;
        loop assigns stack[0..(n)];
        loop assigns dist[0..(n)];
        loop assigns visited[0..(n)];
    */
    while (0 <= top && top < n) {
        // Loop B
        /*@
            loop invariant i_66: 0 <= i <= n;

            loop invariant i_67: \forall integer j; 0 <= j < i && graph[node][j] == 1 && visited[j] == 0 && top < n ==> visited[j] == 1 && dist[j] == dist[node] + 1 && stack[top] == j;

            loop invariant i_68: \forall integer j; 0 <= j < i && (graph[node][j] == 0 || visited[j] == 1 || top >= n) ==> visited[j] == \at(visited[j], Pre);

            loop invariant i_69: \forall integer j; 0 <= j < n && visited[j] == 1 ==> connect(graph, j, start, n);

            loop invariant i_70: \forall integer j; 0 <= j < n && visited[j] == 1 ==> dist[j] != -1;

            loop invariant i_71: \forall integer j; 0 <= j < n && visited[j] == 0 ==> dist[j] == -1;

            loop invariant i_72: stack[0] == start;

            loop invariant i_73: visited[start] == 1;

            loop invariant i_74: dist[start] == 0;


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