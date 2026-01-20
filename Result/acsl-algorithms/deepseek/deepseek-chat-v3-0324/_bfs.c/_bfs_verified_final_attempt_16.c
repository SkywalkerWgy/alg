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
        loop invariant i_1: \forall integer k; 0 <= k <= rear ==> connect(graph, queue[k], start, n);

        loop invariant i_2: \forall integer k; 0 <= k < front ==> visited[queue[k]] == 1;

        loop invariant i_3: \forall integer k; front <= k <= rear ==> visited[queue[k]] == 1;

        loop invariant i_4: \forall integer k; 0 <= k <= rear ==> dist[queue[k]] != -1;

        loop invariant i_5: \forall integer k; 0 <= k < n && visited[k] == 1 ==> \exists integer m; 0 <= m <= rear && k == queue[m];

        loop invariant i_6: \forall integer k; 0 <= k < n && dist[k] != -1 ==> visited[k] == 1;

        loop invariant i_7: \forall integer k, l; 0 <= k < front && 0 <= l < n && graph[queue[k]][l] == 1 ==> visited[l] == 1;

        loop invariant i_8: \forall integer i; 0 <= i < n && visited[i] == 1 ==> dist[i] != -1;

        loop invariant i_9: \forall integer i; 0 <= i < n && visited[i] == 1 ==> connect(graph, i, start, n);

        loop invariant i_10: node == queue[front];

        loop invariant i_94: 0 <= front <= rear <= n;


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
            loop invariant i_12: 0 <= i <= n;

            loop invariant i_16: \forall integer k; 0 <= k < n && dist[k] != -1 ==> visited[k] == 1;

            loop invariant i_18: \forall integer k; 0 <= k <= rear ==> visited[queue[k]] == 1;

            loop invariant i_19: \forall integer k; 0 <= k <= rear ==> dist[queue[k]] != -1;

            loop invariant i_21: rear <= n;

            loop invariant i_22: front <= rear;

            loop invariant i_23: \forall integer k; 0 <= k < n && dist[k] != -1 && k != i ==> visited[k] == 1;

            loop invariant i_24: \forall integer k; 0 <= k < n && (dist[k] != -1 || (graph[node][i] == 1 && k == i && visited[i] == 1)) ==> visited[k] == 1;

            loop invariant i_25: \forall integer k; front <= k <= rear ==> dist[queue[k]] != -1;

            loop invariant i_26: \forall integer k; 0 <= k < n && visited[k] == 1 && k != i && dist[k] == -1 ==> \exists integer m; front <= m <= rear && queue[m] == k;

            loop invariant i_28: \forall integer k; 0 <= k <= rear ==> visited[queue[k]] == 1 && dist[queue[k]] != -1;

            loop invariant i_31: \forall integer k; 0 <= k < n && visited[k] == 1 && dist[k] == -1 ==> \exists integer m; front <= m <= rear && k == queue[m];

            loop invariant i_32: \forall integer k; 0 <= k < n && visited[k] == 1 && k != i ==> \exists integer m; 0 <= m <= rear && k == queue[m];

            loop invariant i_33: \forall integer k; 0 <= k < i && visited[k] == 1 ==> \exists integer m; 0 <= m <= rear && k == queue[m];

            loop invariant i_35: \forall integer k; 0 <= k < n && graph[node][k] == 1 && visited[k] == 1 ==> \exists integer m; 0 <= m <= rear && k == queue[m];

            loop invariant i_36: \forall integer k; 0 <= k < n && visited[k] == 1 && (k != i || (graph[node][i] == 1 && visited[i] == 1)) ==> \exists integer m; 0 <= m <= rear && k == queue[m];

            loop invariant i_42: \forall integer k; 0 <= k < i && visited[k] == 1 ==> dist[k] != -1;

            loop invariant i_43: \forall integer k; 0 <= k < n && visited[k] == 1 && k != i ==> dist[k] != -1;

            loop invariant i_49: \forall integer k; 0 <= k < i && graph[node][k] == 1 && visited[k] == 0 ==> (k != i ==> visited[k] == 1 && dist[k] == dist[node] + 1 && \exists integer m; front <= m <= rear && queue[m] == k); loop invariant i_27b: \forall integer k; 0 <= k < n && visited[k] == 1 ==> (k == i || \exists integer m; 0 <= m <= rear && k == queue[m]); loop invariant i_27c: \forall integer k; 0 <= k < n && dist[k] != -1 ==> (k == i || \exists integer m; 0 <= m <= rear && k == queue[m]); loop invariant i_27d: \forall integer k; 0 <= k < i && graph[node][k] == 1 ==> visited[k] == 1;

            loop invariant i_50: \forall integer k; 0 <= k < n && visited[k] == 1 ==> (k == i || \exists integer m; 0 <= m <= rear && k == queue[m]); loop invariant i_27c: \forall integer k; 0 <= k < n && dist[k] != -1 ==> (k == i || \exists integer m; 0 <= m <= rear && k == queue[m]); loop invariant i_27d: \forall integer k; 0 <= k < i && graph[node][k] == 1 ==> visited[k] == 1;

            loop invariant i_51: \forall integer k; 0 <= k < n && dist[k] != -1 ==> (k == i || \exists integer m; 0 <= m <= rear && k == queue[m]); loop invariant i_27d: \forall integer k; 0 <= k < i && graph[node][k] == 1 ==> visited[k] == 1;

            loop invariant i_52: \forall integer k; 0 <= k < i && visited[k] == 1 && dist[k] != -1 ==> \exists integer m; 0 <= m <= rear && k == queue[m];

            loop invariant i_53: \forall integer k; 0 <= k < n && visited[k] == 1 && dist[k] != -1 && (k >= i || graph[node][k] != 1) ==> \exists integer m; 0 <= m <= rear && k == queue[m];

            loop invariant i_54: \forall integer k; 0 <= k < n && dist[k] != -1 && (k != i || visited[i] == 1) ==> \exists integer m; 0 <= m <= rear && k == queue[m];

            loop invariant i_55: \forall integer k; 0 <= k < n && visited[k] == 1 && (k != i || graph[node][i] == 1) ==> \exists integer m; 0 <= m <= rear && k == queue[m];

            loop invariant i_56: \forall integer k; 0 <= k < i && graph[node][k] == 1 && visited[k] == 1 ==> \exists integer m; 0 <= m <= rear && k == queue[m];

            loop invariant i_59: \forall integer k; i <= k < n && visited[k] == 1 ==> dist[k] != -1;

            loop invariant i_63: \forall integer k; 0 <= k < i && graph[node][k] == 1 ==> connect(graph, k, node, n);

            loop invariant i_67: \forall integer k; 0 <= k < i && graph[node][k] == 1 && visited[k] == 0 ==> rear < n;

            loop invariant i_68: \forall integer k; 0 <= k < i && graph[node][k] == 1 && visited[k] == 0 ==> visited[k] == 1 && dist[k] == dist[node] + 1 && queue[rear] == k;

            loop invariant i_70: \forall integer k; 0 <= k < n && visited[k] == 1 && k >= i ==> \exists integer m; 0 <= m <= rear && k == queue[m];

            loop invariant i_72: \forall integer k; 0 <= k < i && graph[node][k] == 1 ==> (visited[k] == 1 || k == i);

            loop invariant i_78: \forall integer k; 0 <= k < i && graph[node][k] == 1 && visited[k] == 1 && k != node ==> dist[k] == dist[node] + 1;

            loop invariant i_80: \forall integer k; 0 <= k < i && graph[node][k] == 1 ==> (visited[k] == 1 || (k == i && graph[node][i] == 1 && visited[i] == 0));

            loop invariant i_81: \forall integer k; 0 <= k < i && graph[node][k] == 1 && k != node ==> visited[k] == 1;

            loop invariant i_85: \forall integer k; 0 <= k < n && visited[k] == 1 && graph[node][k] == 1 ==> \exists integer m; 0 <= m <= rear && k == queue[m];

            loop invariant i_86: \forall integer k; 0 <= k < i && visited[k] == 1 && k != node ==> \exists integer m; 0 <= m <= rear && k == queue[m];

            loop invariant i_91: 0 <= front <= rear <= n;

            loop invariant i_92: \forall integer k; front <= k <= rear ==> visited[queue[k]] == 1;

            loop invariant i_93: rear < n ==> \forall integer k; 0 <= k < i && graph[node][k] == 1 ==> visited[k] == 1;

            loop invariant i_96: \forall integer k; i <= k < n && visited[k] == 1 && k != node ==> \exists integer m; 0 <= m <= rear && k == queue[m];

            loop invariant i_97: \forall integer k; 0 <= k < n && graph[node][k] == 1 && visited[k] == 1 && k < i ==> \exists integer m; 0 <= m <= rear && k == queue[m];

            loop invariant i_98: \forall integer k; 0 <= k < i && graph[node][k] == 1 && visited[k] == 0 ==> rear < n && visited[k] == 1 && dist[k] == dist[node] + 1 && queue[rear] == k;

            loop invariant i_99: \forall integer k; 0 <= k < i && graph[node][k] == 1 && visited[k] == 1 && k != node ==> \exists integer m; front <= m <= rear && queue[m] == k;

            loop invariant i_100: \forall integer k; 0 <= k < i && graph[node][k] == 1 && visited[k] == 1 && k == node ==> front == 0 && queue[0] == node;

            loop invariant i_101: \forall integer k; 0 <= k < i && graph[node][k] == 1 && visited[k] == 1 ==> (k == node || \exists integer m; front <= m <= rear && queue[m] == k); loop invariant i_93: \forall integer k; 0 <= k < i && graph[node][k] == 1 && visited[k] == 1 && k != node ==> queue[front] == node;

            loop invariant i_102: \forall integer k; 0 <= k < i && graph[node][k] == 1 && visited[k] == 1 && k != node ==> queue[front] == node;

            loop invariant i_105: \forall integer k; 0 <= k < n && visited[k] == 1 && k < i ==> \exists integer m; 0 <= m <= rear && k == queue[m];

            loop invariant i_106: \forall integer k; 0 <= k < n && visited[k] == 1 && k >= i && graph[node][k] == 0 ==> \exists integer m; 0 <= m <= rear && k == queue[m];

            loop invariant i_107: \forall integer k; 0 <= k < i && visited[k] == 1 && (k != node || front == 0) ==> \exists integer m; 0 <= m <= rear && k == queue[m];

            loop invariant i_112: \forall integer k; 0 <= k < i && visited[k] == 1 && graph[node][k] == 1 ==> dist[k] == dist[node] + 1;

            loop invariant i_115: \forall integer k; 0 <= k < front && k != node && graph[queue[k]][i] == 1 ==> visited[i] == 1;

            loop invariant i_116: \forall integer k; 0 <= k < n && visited[k] == 1 && (k < i || (graph[node][k] == 1 && visited[k] == 1)) ==> \exists integer m; 0 <= m <= rear && k == queue[m];

            loop invariant i_117: \forall integer k; 0 <= k < front && graph[queue[k]][i] == 1 && i != node ==> visited[i] == 1;

            loop invariant i_118: \forall integer k; 0 <= k < i && graph[node][k] == 1 ==> \exists integer m; front <= m <= rear && queue[m] == k;

            loop invariant i_122: \forall integer k; 0 <= k < n && visited[k] == 1 && (k < i || graph[node][k] == 0) ==> \exists integer m; 0 <= m <= rear && k == queue[m];


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