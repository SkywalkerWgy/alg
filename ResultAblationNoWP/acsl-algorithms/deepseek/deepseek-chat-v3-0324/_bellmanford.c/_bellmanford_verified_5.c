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
        loop invariant i_32: 1 <= i <= n;

        loop invariant i_33: \forall integer k; 0 <= k < n ==> (dist[k] == INF || (dist[k] != INF && dist[k] == \at(dist[k], Pre)));

        loop invariant i_34: \forall integer k; 0 <= k < n ==> (parent[k] == -1 || (parent[k] != -1 && parent[k] == \at(parent[k], Pre)));

        loop invariant i_35: \forall integer k; 0 <= k < e ==> (dist[edges[k].u] != INF && dist[edges[k].u] + edges[k].weight < dist[edges[k].v] ==> dist[edges[k].v] == dist[edges[k].u] + edges[k].weight && parent[edges[k].v] == edges[k].u);


        loop assigns dist[0..(n-1)], parent[0..(n-1)], i;
    */
    for (int i = 1; i < n; i++) {
        // Loop B
        /*@
            loop invariant i_36: 0 <= j <= e;

            loop invariant i_37: \forall integer k; 0 <= k < j ==> (dist[edges[k].u] != INF && dist[edges[k].u] + edges[k].weight < dist[edges[k].v] ==> dist[edges[k].v] == dist[edges[k].u] + edges[k].weight && parent[edges[k].v] == edges[k].u);

            loop invariant i_38: \forall integer k; 0 <= k < n ==> (dist[k] == INF || (dist[k] != INF && (dist[k] == \at(dist[k], Pre) || (\exists integer l; 0 <= l < j && edges[l].v == k && dist[edges[l].u] != INF && dist[edges[l].u] + edges[l].weight == dist[k])))); loop invariant \forall integer k; 0 <= k < n ==> (parent[k] == -1 || (parent[k] != -1 && (parent[k] == \at(parent[k], Pre) || (\exists integer l; 0 <= l < j && edges[l].v == k && parent[k] == edges[l].u)))); ```;

            loop invariant i_39: \forall integer k; 0 <= k < n ==> (parent[k] == -1 || (parent[k] != -1 && (parent[k] == \at(parent[k], Pre) || (\exists integer l; 0 <= l < j && edges[l].v == k && parent[k] == edges[l].u)))); ```;


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