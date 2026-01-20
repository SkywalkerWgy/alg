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
        loop invariant i_26: 1 <= i <= n;

        loop invariant i_27: \forall integer k; 0 <= k < n ==> (dist[k] == INF || (\exists integer p; 0 <= p < e && edges[p].v == k && dist[edges[p].u] != INF && dist[k] >= dist[edges[p].u] + edges[p].weight)); loop invariant \forall integer k; 0 <= k < n ==> (parent[k] == -1 || (0 <= parent[k] < n && dist[k] == dist[parent[k]] + (\sum integer p; 0 <= p < e && edges[p].u == parent[k] && edges[p].v == k; edges[p].weight)));

        loop invariant i_28: \forall integer k; 0 <= k < n ==> (parent[k] == -1 || (0 <= parent[k] < n && dist[k] == dist[parent[k]] + (\sum integer p; 0 <= p < e && edges[p].u == parent[k] && edges[p].v == k; edges[p].weight)));


        loop assigns dist[0..(n-1)], parent[0..(n-1)], i;
    */
    for (int i = 1; i < n; i++) {
        // Loop B
        /*@
            loop invariant i_29: 0 <= j <= e;

            loop invariant i_30: \forall integer k; 0 <= k < n ==> (dist[k] == INF || (\exists integer p; 0 <= p < j && edges[p].v == k && dist[edges[p].u] != INF && dist[k] >= dist[edges[p].u] + edges[p].weight)); loop invariant \forall integer k; 0 <= k < n ==> (parent[k] == -1 || (0 <= parent[k] < n && dist[k] == dist[parent[k]] + (\sum integer p; 0 <= p < e && edges[p].u == parent[k] && edges[p].v == k; edges[p].weight)));

            loop invariant i_31: \forall integer k; 0 <= k < n ==> (parent[k] == -1 || (0 <= parent[k] < n && dist[k] == dist[parent[k]] + (\sum integer p; 0 <= p < e && edges[p].u == parent[k] && edges[p].v == k; edges[p].weight)));


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