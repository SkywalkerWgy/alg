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
    requires \valid(queue + (0..(n)));
    requires \forall integer i, j; 0 <= i <= n && 0 <= j <= n && i != j ==> \separated(&graph[i] + (0..(n)), &graph[j] + (0..(n)), &dist[0..(n)], &visited[0..(n)], &queue[0..(n)]);
    requires \separated(&dist[0..(n)], &visited[0..(n)], &queue[0..(n)]);
    requires \forall integer j; 0 <= j <= n && j != start ==> visited[j] == 0 && dist[j] == -1;
    requires visited[start] == 1 && dist[start] == 0;
    requires queue[0] == start;
    requires \forall integer i, j; 0 <= i <= n ==> graph[i][i] == 1;
    requires \forall integer i, j; 0 <= i <= n && 0 <= j <= n ==> graph[i][j] == graph[j][i];
    requires \forall integer i, j; 0 <= i <= n && 0 <= j <= n ==> (graph[i][j] == 0 || graph[i][j] == 1);
    ensures e_1: \forall integer i; (0 <= i < n && visited[i] == 1) ==> connect(graph, i, start, n);
    assigns dist[0..(n)], visited[0..(n)], queue[0..(n)];
*/
void _bfs(int** graph, int* dist, int* visited, int* queue, int start, int n) {
    int rear = 0;
    int front = 0;
    int node = start;
    // Loop A
    /*@
        loop invariant i_73: 0 <= front <= rear < n;

        loop invariant i_74: \forall integer i; 0 <= i < front ==> visited[queue[i]] == 1;

        loop invariant i_75: \forall integer i; front <= i <= rear ==> visited[queue[i]] == 1;

        loop invariant i_76: \forall integer i; 0 <= i < n && visited[i] == 1 ==> connect(graph, i, start, n);

        loop invariant i_77: \forall integer i; 0 <= i < n && visited[i] == 1 ==> dist[i] == \min(\numof int j; 0 <= j < n && connect(graph, i, j, n) && visited[j] == 1, dist[j] + 1);

        loop invariant i_78: \forall integer i; 0 <= i < n && visited[i] == 1 ==> dist[i] >= 0;

        loop invariant i_79: \forall integer i; 0 <= i < n && visited[i] == 0 ==> dist[i] == -1;

        loop invariant i_80: queue[0] == start;

        loop invariant i_81: \forall integer i; 0 <= i < n ==> graph[i][i] == 1;

        loop invariant i_82: \forall integer i, j; 0 <= i < n && 0 <= j < n ==> graph[i][j] == graph[j][i];

        loop invariant i_83: \forall integer i, j; 0 <= i < n && 0 <= j < n ==> (graph[i][j] == 0 || graph[i][j] == 1);


        loop assigns front;
        loop assigns rear;
        loop assigns node;
        loop assigns queue[0..(n)];
        loop assigns dist[0..(n)];
        loop assigns visited[0..(n)];
    */
    while (front <= rear && front < n && rear < n) {
        // Loop B
        /*@
            loop invariant i_84: 0 <= i <= n;

            loop invariant i_85: \forall integer j; 0 <= j < i ==> (graph[node][j] == 0 || visited[j] == 1);

            loop invariant i_86: \forall integer j; 0 <= j < i && graph[node][j] == 1 ==> visited[j] == 1;

            loop invariant i_87: \forall integer j; 0 <= j < n && visited[j] == 1 ==> connect(graph, j, start, n);

            loop invariant i_88: \forall integer j; 0 <= j < n && visited[j] == 1 ==> dist[j] >= 0;

            loop invariant i_89: \forall integer j; 0 <= j < n && visited[j] == 0 ==> dist[j] == -1;

            loop invariant i_90: \forall integer j; 0 <= j < i && graph[node][j] == 1 && visited[j] == 0 ==> rear < n && queue[rear] == j && visited[j] == 1 && dist[j] == dist[node] + 1;


            loop assigns rear;
            loop assigns queue[0..(n)];
            loop assigns dist[0..(n)];
            loop assigns visited[0..(n)];
            loop assigns i;
        */
        for (int i = 0; i < n; i++) {
            if (graph[node][i] == 1 && visited[i] == 0 && rear < n) { 
                rear++;
                queue[rear] = i;
                visited[i] = 1;
                dist[i] = dist[node] + 1;
            }
        }
        front += 1;
        if(front <= rear){
            node = queue[front];
        }
        else{
            break;
        }
    }
}