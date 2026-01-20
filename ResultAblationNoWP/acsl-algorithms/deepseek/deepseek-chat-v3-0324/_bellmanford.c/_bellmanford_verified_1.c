#include <limits.h>
#define MAX_VERTICES 100
#define INF INT_MAX
struct Edge {
    int u, v, weight;
};

/*@
    requires e > 0;
    requires n > 0;
    requires \valid(edges+(0..(e - 1)));
    requires \valid(dist+(0..(n - 1)));
    requires \valid(parent+(0..(n - 1)));
    requires 0 <= start < n;
    requires \forall integer k; 0 <= k < e ==> 0 <= edges[k].u < n && 0 <= edges[k].v < n;
    requires \forall integer k; 0 <= k < n ==> parent[k] == -1;
    requires \forall integer k; 0 <= k < n ==> dist[k] == INF;
    assigns dist[0..(n-1)], parent[0..(n-1)];
*/
int _bellmanford(int n, int e, struct Edge edges[], int start, int dist[], int parent[]) {
    dist[start] = 0;

    // Loop A
    /*@
        loop invariant i_0: 1 <= i <= n;

        loop invariant i_1: \forall integer k; 0 <= k < n ==> (dist[k] == INF || (dist[k] == \min(\sum_{l=0}^{i-1} edges[l].weight, INF)));

        loop invariant i_2: \forall integer k; 0 <= k < n ==> (parent[k] == -1 || (parent[k] >= 0 && parent[k] < n && dist[parent[k]] + edges[j].weight == dist[k]));

        loop invariant i_3: \forall integer k; 0 <= k < n ==> (dist[k] != INF ==> \exists integer p; 0 <= p < i && edges[p].v == k && dist[edges[p].u] + edges[p].weight == dist[k]); ```;


        loop assigns dist[0..(n-1)], parent[0..(n-1)], i;
    */
    for (int i = 1; i < n; i++) {
        // Loop B
        /*@
            loop invariant i_4: 0 <= j <= e;

            loop invariant i_5: \forall integer k; 0 <= k < j ==> (dist[edges[k].v] <= dist[edges[k].u] + edges[k].weight || dist[edges[k].u] == INF);

            loop invariant i_6: \forall integer k; 0 <= k < n ==> (dist[k] == INF || (dist[k] == \min(\sum_{l=0}^{i-1} edges[l].weight, INF)));

            loop invariant i_7: \forall integer k; 0 <= k < n ==> (parent[k] == -1 || (parent[k] >= 0 && parent[k] < n && dist[parent[k]] + edges[j-1].weight == dist[k]));

            loop invariant i_8: \forall integer k; 0 <= k < n ==> (dist[k] != INF ==> \exists integer p; 0 <= p < i && edges[p].v == k && dist[edges[p].u] + edges[p].weight == dist[k]); ```;


            loop assigns dist[0..(n-1)];
            loop assigns parent[0..(n-1)];
            loop assigns j;
        */
        for (int j = 0; j < e; j++) {
            int u = edges[j].u;
            int v = edges[j].v;
            int weight = edges[j].weight;
            if (dist[u] != INF && dist[u] + weight < dist[v]) {
                dist[v] = dist[u] + weight;
                parent[v] = u;
            }
        }
    }

    return 0;
}