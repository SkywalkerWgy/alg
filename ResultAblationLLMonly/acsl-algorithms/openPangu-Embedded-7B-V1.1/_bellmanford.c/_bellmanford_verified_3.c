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
        loop invariant i_20: 1 <= i <= n;

        loop invariant i_21: 0 <= j < e;

        loop invariant i_22: \forall integer k; 0 <= edges[k].u < n && 0 <= edges[k].v < n;

        loop invariant i_23: \forall integer k; 0 <= parent[k] <= n - 1;

        loop invariant i_24: \forall integer k; 0 <= dist[k] <= INF;

        loop invariant i_25: \forall integer k; 0 <= dist[k] < dist[parent[k]] + 1 for all j such that edges[j].u == k;


        loop assigns dist[0..(n-1)], parent[0..(n-1)], i;
    */
    for (int i = 1; i < n; i++) {
        // Loop B
        /*@
            loop invariant i_26: 1 <= i <= n;

            loop invariant i_27: 0 <= j < e;

            loop invariant i_28: \forall integer k; 0 <= k < e ==> 0 <= edges[k].u < n && 0 <= edges[k].v < n;

            loop invariant i_29: \forall integer k; 0 <= parent[k] <= n - 1;

            loop invariant i_30: \forall integer k; 0 <= dist[k] <= INF;

            loop invariant i_31: \forall integer k; 0 <= dist[k] < dist[parent[k]] + 1 for all j such that edges[j].u == k;


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