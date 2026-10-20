/* Independent planarity certificate check (C).
 *
 * Reads graph.txt ("n m" then edges) and rotation.txt (lines "v: w1 w2 ...").
 * Verifies each rotation is a permutation of the vertex's neighbours, the
 * graph is connected, and the face permutation of the rotation system has
 * F faces with V - E + F = 2 (a spherical embedding).
 * Exit 0 iff all hold.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 4096
#define MAXD 64
static int n, m, deg[MAXN], nb[MAXN][MAXD];
static int rdeg[MAXN], rot[MAXN][MAXD];

static int has(int v, int w) {
    for (int i = 0; i < deg[v]; i++) if (nb[v][i] == w) return 1;
    return 0;
}

static int rpos(int v, int w) {
    for (int i = 0; i < rdeg[v]; i++) if (rot[v][i] == w) return i;
    return -1;
}

int main(int argc, char **argv) {
    if (argc < 3) return 2;
    FILE *f = fopen(argv[1], "r");
    if (!f) return 2;
    char line[4096];
    int got = 0, ne = 0;
    while (fgets(line, sizeof line, f)) {
        if (line[0] == '#' || line[0] == '\n') continue;
        int a, b;
        if (sscanf(line, "%d %d", &a, &b) != 2) return 2;
        if (!got) { n = a; m = b; got = 1; if (n > MAXN) return 2; continue; }
        if (a < 0 || b < 0 || a >= n || b >= n || a == b || has(a, b)) return 2;
        if (deg[a] >= MAXD || deg[b] >= MAXD) return 2;
        nb[a][deg[a]++] = b; nb[b][deg[b]++] = a; ne++;
    }
    fclose(f);
    if (!got || ne != m) return 2;
    f = fopen(argv[2], "r");
    if (!f) return 2;
    static int seenv[MAXN];
    while (fgets(line, sizeof line, f)) {
        if (line[0] == '#' || line[0] == '\n') continue;
        char *p = line;
        int v = (int)strtol(p, &p, 10);
        if (*p != ':' || v < 0 || v >= n || seenv[v]) { printf("REJECT: bad rotation line\n"); return 1; }
        seenv[v] = 1; p++;
        while (1) {
            char *q;
            long w = strtol(p, &q, 10);
            if (q == p) break;
            p = q;
            if (rdeg[v] >= MAXD) return 2;
            rot[v][rdeg[v]++] = (int)w;
        }
    }
    fclose(f);
    for (int v = 0; v < n; v++) {
        if (!seenv[v] || rdeg[v] != deg[v]) { printf("REJECT: rotation size at %d\n", v); return 1; }
        for (int i = 0; i < rdeg[v]; i++) {
            if (!has(v, rot[v][i])) { printf("REJECT: non-neighbour in rotation at %d\n", v); return 1; }
            for (int j = i + 1; j < rdeg[v]; j++)
                if (rot[v][i] == rot[v][j]) { printf("REJECT: repeat in rotation at %d\n", v); return 1; }
        }
    }
    /* connectivity */
    static int vis[MAXN], st[MAXN];
    int sp = 0, nv = 1;
    vis[0] = 1; st[sp++] = 0;
    while (sp) {
        int v = st[--sp];
        for (int i = 0; i < deg[v]; i++) {
            int w = nb[v][i];
            if (!vis[w]) { vis[w] = 1; nv++; st[sp++] = w; }
        }
    }
    if (nv != n) { printf("REJECT: not connected\n"); return 1; }
    /* darts indexed by (v, position in rot[v]) */
    static unsigned char used[MAXN][MAXD];
    int faces = 0;
    for (int v = 0; v < n; v++)
        for (int i = 0; i < rdeg[v]; i++) {
            if (used[v][i]) continue;
            faces++;
            int u = v, k = i;
            while (!used[u][k]) {
                used[u][k] = 1;
                int w = rot[u][k];            /* dart u -> w */
                int pu = rpos(w, u);          /* u's position at w */
                int nk = (pu + 1) % rdeg[w];  /* next dart w -> rot[w][nk] */
                u = w; k = nk;
            }
        }
    int chi = n - m + faces;
    printf("%s: V=%d E=%d F=%d, V-E+F=%d\n", argv[2], n, m, faces, chi);
    if (chi != 2) { printf("REJECT: not a spherical embedding\n"); return 1; }
    printf("OK: planar (spherical rotation system)\n");
    return 0;
}
