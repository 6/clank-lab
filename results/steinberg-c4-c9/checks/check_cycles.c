/* Independent cycle-length check (C).
 *
 * For every edge (u,v) with u < v, counts the simple u-v paths of length
 * L-1 that avoid the edge itself and use only vertices larger than u; each
 * simple cycle of length L whose smallest vertex is u is then found exactly
 * twice (once per edge of the cycle at u), so counts are halved.
 *
 * Usage: check_cycles graph.txt LMAX FORBIDDEN...   (e.g. 10 4 9)
 * Prints the counts for lengths 3..LMAX; exit 0 iff none is forbidden.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 4096
static int n, m, deg[MAXN], *adj[MAXN];
static int onpath[MAXN];
static long long cnt[64];
static int lmax, root, target;

static void dfs(int v, int len) {
    /* len = number of edges used so far on the path root..v */
    for (int i = 0; i < deg[v]; i++) {
        int w = adj[v][i];
        if (w == target && len + 1 >= 2) {
            /* path root..v..target has len+1 edges; with edge target-root
               this closes a cycle of length len+2 */
            if (v != root && len + 2 <= lmax) cnt[len + 2]++;
            continue;
        }
        if (w <= root || onpath[w] || len + 2 >= lmax) continue;
        onpath[w] = 1;
        dfs(w, len + 1);
        onpath[w] = 0;
    }
}

int main(int argc, char **argv) {
    if (argc < 3) return 2;
    FILE *f = fopen(argv[1], "r");
    if (!f) return 2;
    lmax = atoi(argv[2]);
    if (lmax < 3 || lmax > 60) return 2;
    char line[256];
    int got = 0, ne = 0;
    static int eu[MAXN * 8], ev[MAXN * 8];
    while (fgets(line, sizeof line, f)) {
        if (line[0] == '#' || line[0] == '\n') continue;
        int a, b;
        if (sscanf(line, "%d %d", &a, &b) != 2) return 2;
        if (!got) { n = a; m = b; got = 1; continue; }
        if (a < 0 || b < 0 || a >= n || b >= n || a == b || ne >= MAXN * 8) return 2;
        eu[ne] = a; ev[ne] = b; ne++;
    }
    if (!got || ne != m || n > MAXN) return 2;
    for (int i = 0; i < m; i++) { deg[eu[i]]++; deg[ev[i]]++; }
    for (int v = 0; v < n; v++) { adj[v] = malloc(sizeof(int) * (deg[v] + 1)); deg[v] = 0; }
    for (int i = 0; i < m; i++) { adj[eu[i]][deg[eu[i]]++] = ev[i]; adj[ev[i]][deg[ev[i]]++] = eu[i]; }
    for (int v = 0; v < n; v++)
        for (int i = 0; i < deg[v]; i++)
            for (int j = i + 1; j < deg[v]; j++)
                if (adj[v][i] == adj[v][j]) { fprintf(stderr, "repeated edge\n"); return 2; }
    /* cycles through the edge (root, target) with root the smallest vertex */
    for (root = 0; root < n; root++) {
        for (int i = 0; i < deg[root]; i++) {
            target = adj[root][i];
            if (target <= root) continue;
            onpath[root] = 1;
            /* walk from root along edges other than root-target */
            for (int j = 0; j < deg[root]; j++) {
                int w = adj[root][j];
                if (w == target || w <= root) continue;
                onpath[w] = 1;
                dfs(w, 1);
                onpath[w] = 0;
            }
            onpath[root] = 0;
        }
    }
    int bad = 0;
    printf("%s: cycle counts by length (<= %d):", argv[1], lmax);
    for (int l = 3; l <= lmax; l++) {
        long long c = cnt[l] / 2;
        if (cnt[l] % 2) { fprintf(stderr, "internal parity error at %d\n", l); return 3; }
        if (c) printf(" %d:%lld", l, c);
        for (int k = 3; k < argc; k++)
            if (atoi(argv[k]) == l && c) bad = 1;
    }
    printf("\n");
    if (bad) { printf("REJECT: forbidden cycle length present\n"); return 1; }
    printf("OK: no forbidden cycle length\n");
    return 0;
}
