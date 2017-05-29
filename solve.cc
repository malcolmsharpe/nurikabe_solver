#include <algorithm>
#include <cassert>
#include <complex>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <map>
#include <queue>
#include <set>
#include <sstream>
#include <vector>
using namespace std;

#define FR(i,a,b) for(int i=(a);i<(b);++i)
#define FOR(i,n) FR(i,0,n)
#define CLR(x,a) memset(x,a,sizeof(x))
#define setmin(a,b) a = min(a,b)
#define PB push_back
#define FORALL(i,v) for(typeof((v).end())i=(v).begin();i!=(v).end();++i)
#define MP make_pair
#define A first
#define B second
#define RF(i,a,b) for(int i=(a)-1;i>=(b);--i)
#define BEND(v) (v).begin(),(v).end()
#define SZ(v) int((v).size())
#define FORI(i,v) FOR(i,SZ(v))
typedef long double ld;
typedef long long ll;

const int MAXDIM = 16;
const int MAXISLE = MAXDIM*MAXDIM;

const int UNK = -1;
const int LAND = 0;
const int SEA = 1;

struct island
{
    int r;
    int c;
    int s;
};
int I;
island isles[MAXISLE];

int R,C;
int gridval[MAXDIM][MAXDIM];
int gridgen[MAXDIM][MAXDIM];
vector<bool> validgen;
int currentgen;

int stat_nbranches;

int getgrid(int r, int c)
{
    if (!validgen[gridgen[r][c]]) return UNK;
    return gridval[r][c];
}

void setgrid_direct(int r, int c, int val)
{
    gridval[r][c] = val;
    gridgen[r][c] = currentgen;
}

string pretty[MAXDIM];
void print_grid()
{
    FOR(r,R) {
        pretty[r].clear();
        FOR(c,C) {
            pretty[r].push_back(' ');
        }
    }

    FOR(r,R) {
        FOR(c,C) {
            int val = getgrid(r, c);

            char ch = '?';
            if (val == LAND) ch = '.';
            if (val == SEA) ch = '#';
            pretty[r][c] = ch;
        }
    }

    FOR(i,I) {
        char ch = 'I';
        if (isles[i].s < 10) ch = isles[i].s + '0';
        pretty[isles[i].r][isles[i].c] = ch;
    }

    FOR(r,R) {
        printf("%s\n", pretty[r].c_str());
    }
}

bool in_bounds(int r, int c)
{
    return 0 <= r && r < R && 0 <= c && c < C;
}

bool contradiction;
bool dirty;
int steps;

void setgrid(int r, int c, int val)
{
    if (val == UNK) return;
    if (getgrid(r, c) == val) return;
    if (getgrid(r, c) != UNK && getgrid(r, c) != val) {
        printf("    Contradiction: (%d,%d) is already %d, can't set to %d\n", r, c, getgrid(r, c), val);
        contradiction = true;
        return;
    }
    setgrid_direct(r, c, val);
    printf("    Set (%d,%d) to %d\n", r, c, val);
    dirty = true;
}

int color[MAXDIM][MAXDIM];
int island_cursize[MAXISLE];

const int NDIR = 4;
const int DR[] = { 1, 0, -1, 0 };
const int DC[] = { 0, 1, 0, -1 };

int queue_r[MAXDIM*MAXDIM], queue_c[MAXDIM*MAXDIM];
int queue_front, queue_back;
bool mark[MAXDIM][MAXDIM];

bool enqueue(int r, int c)
{
    if (mark[r][c]) return false;
    mark[r][c] = true;
    queue_r[queue_back] = r;
    queue_c[queue_back] = c;
    ++queue_back;
    return true;
}

void flood_island(int i)
{
    // If this island merged with another island: contradiction.
    if (color[isles[i].r][isles[i].c] != -1) {
        printf("    Contradiction: island %d (%d, %d, %d) has merged with another island\n", i, isles[i].r, isles[i].c, isles[i].s);
        contradiction = true;
    }

    queue_front = queue_back = 0;

    enqueue(isles[i].r, isles[i].c);

    island_cursize[i] = 0;
    while (queue_front < queue_back) {
        int r = queue_r[queue_front];
        int c = queue_c[queue_front];
        ++queue_front;

        color[r][c] = i;
        ++island_cursize[i];

        FOR(dir,NDIR) {
            int dr = DR[dir];
            int dc = DC[dir];

            int r2 = r+dr;
            int c2 = c+dc;

            if (in_bounds(r2, c2) && getgrid(r2, c2) == LAND) {
                enqueue(r2, c2);
            }
        }
    }

    // If this island is too large: contradiction.
    if (island_cursize[i] > isles[i].s) {
        printf("    Contradiction: island %d (%d, %d, %d) has become too large\n", i, isles[i].r, isles[i].c, isles[i].s);
        contradiction = true;
    }
}

void flood_islands()
{
    FOR(r,R) FOR(c,C) mark[r][c] = false;
    FOR(r,R) FOR(c,C) color[r][c] = -1;

    FOR(i,I) flood_island(i);
}

int nbr_color_n[MAXDIM][MAXDIM]; // 0 = no color neighbors; 1 = one color neighbor; 2 = more than one color neighbor
int nbr_color[MAXDIM][MAXDIM];

void compute_nbr_color()
{
    FOR(r,R) FOR(c,C) {
        nbr_color_n[r][c] = 0;
        nbr_color[r][c] = -1;

        FOR(dir,NDIR) {
            int dr = DR[dir];
            int dc = DC[dir];

            int r2 = r+dr;
            int c2 = c+dc;

            if (in_bounds(r2, c2) && color[r2][c2] != -1 && nbr_color_n[r][c] < 2 && color[r2][c2] != nbr_color[r][c]) {
                ++nbr_color_n[r][c];
                nbr_color[r][c] = color[r2][c2];
            }
        }
    }
}

int n_flooded_unk = 0;
int flooded_unk_r[MAXDIM*MAXDIM];
int flooded_unk_c[MAXDIM*MAXDIM];

void flood_unk(int i)
{
    queue_front = queue_back = 0;

    enqueue(isles[i].r, isles[i].c);

    n_flooded_unk = 0;
    while (queue_front < queue_back) {
        int r = queue_r[queue_front];
        int c = queue_c[queue_front];
        ++queue_front;

        if (getgrid(r, c) == UNK) {
            flooded_unk_r[n_flooded_unk] = r;
            flooded_unk_c[n_flooded_unk] = c;
            ++n_flooded_unk;
        }

        // If we already found enough space, might as well stop.
        if (island_cursize[i] + n_flooded_unk > isles[i].s) break;

        FOR(dir,NDIR) {
            int dr = DR[dir];
            int dc = DC[dir];

            int r2 = r+dr;
            int c2 = c+dc;

            if (in_bounds(r2, c2)) {
                int val = getgrid(r2, c2);
                if (
                        // Can spread to our own land
                        (val == LAND && color[r2][c2] == i) ||

                        (val == UNK &&
                            // Can spread to land not adjacent to anyone
                            (nbr_color_n[r2][c2] == 0 ||
                            // Can spread to land adjacent to only us (and no one else)
                                (nbr_color_n[r2][c2] == 1 && nbr_color[r2][c2] == i)))) {
                    enqueue(r2, c2);
                }
            }
        }
    }

    // Check whether this island can only fit by occupying ALL the cells we explored.
    if (island_cursize[i] + n_flooded_unk == isles[i].s) {
        FOR(i, n_flooded_unk) {
            setgrid(flooded_unk_r[i], flooded_unk_c[i], LAND);
        }
    }
}

void flood_unks()
{
    flood_islands();
    compute_nbr_color();
    FOR(i,I) {
        FOR(r,R) FOR(c,C) mark[r][c] = false;
        flood_unk(i);
    }
}

int ncomp;
int comp_nbr_n[MAXDIM*MAXDIM];
int comp_nbr_r[MAXDIM*MAXDIM];
int comp_nbr_c[MAXDIM*MAXDIM];

void flood_comp_of_type(int r, int c, int p, int t)
{
    queue_front = queue_back = 0;

    enqueue(r, c);

    while (queue_front < queue_back) {
        int r = queue_r[queue_front];
        int c = queue_c[queue_front];
        ++queue_front;

        FOR(dir,NDIR) {
            int dr = DR[dir];
            int dc = DC[dir];

            int r2 = r+dr;
            int c2 = c+dc;

            if (in_bounds(r2, c2)) {
                int val = getgrid(r2, c2);

                if (val == t) {
                    enqueue(r2, c2);
                } else if (val == UNK) {
                    ++comp_nbr_n[p];
                    comp_nbr_r[p] = r2;
                    comp_nbr_c[p] = c2;
                }
            }
        }
    }
}

void sea_escape()
{
    FOR(r,R) FOR(c,C) mark[r][c] = false;

    ncomp = 0;
    FOR(r,R) FOR(c,C) if (getgrid(r,c) == SEA && !mark[r][c]) {
        comp_nbr_n[ncomp] = 0;
        comp_nbr_r[ncomp] = -1;
        comp_nbr_c[ncomp] = -1;
        flood_comp_of_type(r, c, ncomp, SEA);
        ++ncomp;
    }

    if (ncomp >= 2) {
        FOR(p,ncomp) {
            if (comp_nbr_n[p] == 1) {
                int r = comp_nbr_r[p];
                int c = comp_nbr_c[p];

                setgrid(r, c, SEA);
            } else if (comp_nbr_n[p] == 0) {
                printf("    Contradiction: sea is divided but a component is trapped\n");
                contradiction = true;
            }
        }
    }
}

void land_escape()
{
    flood_islands();

    FOR(r,R) FOR(c,C) mark[r][c] = false;

    ncomp = 0;
    FOR(r,R) FOR(c,C) if (getgrid(r,c) == LAND && !mark[r][c]) {
        comp_nbr_n[ncomp] = 0;
        comp_nbr_r[ncomp] = -1;
        comp_nbr_c[ncomp] = -1;
        flood_comp_of_type(r, c, ncomp, LAND);

        if (color[r][c] == -1 && comp_nbr_n[ncomp] == 0) {
            printf("    Contradiction: orphaned land (%d, %d) is trapped\n", r, c);
            contradiction = true;
        }

        ++ncomp;
    }

    FOR(p,ncomp) if (comp_nbr_n[p] == 1) {
        int r = comp_nbr_r[p];
        int c = comp_nbr_c[p];

        setgrid(r, c, LAND);
    }
}

void color_reachables(int i)
{
    int remaining = isles[i].s - island_cursize[i];

    FOR(r,R) FOR(c,C) mark[r][c] = false;
    queue_front = queue_back = 0;

    FOR(r,R) FOR(c,C) if (color[r][c] == i) {
        FOR(dir,NDIR) {
            int dr = DR[dir];
            int dc = DC[dir];

            int r2 = r+dr;
            int c2 = c+dc;

            if (in_bounds(r2, c2) && getgrid(r2, c2) == UNK) {
                enqueue(r2, c2);
            }
        }
    }

    int dist = 0;
    int queue_inc = 0;
    while (queue_front < queue_back) {
        if (queue_inc == queue_front) {
            ++dist;
            queue_inc = queue_back;
            if (dist > remaining) break;
        }

        int r = queue_r[queue_front];
        int c = queue_c[queue_front];
        ++queue_front;

        color[r][c] = i;

        FOR(dir,NDIR) {
            int dr = DR[dir];
            int dc = DC[dir];

            int r2 = r+dr;
            int c2 = c+dc;

            if (in_bounds(r2, c2) && getgrid(r2, c2) == UNK) {
                enqueue(r2, c2);
            }
        }
    }
}

void unreachables()
{
    flood_islands();

    FOR(i,I) color_reachables(i);

    FOR(r,R) FOR(c,C) if (color[r][c] == -1 && getgrid(r,c) == UNK) setgrid(r,c,SEA);
}

void solve_step()
{
    printf("Solve step %d\n", steps);
    ++steps;
    dirty = false;
    contradiction = false;

    // Disconnected islands
    printf("  Disconnected islands\n");
    flood_islands();
    FOR(r,R) FOR(c,C) {
        int nbr = -1;
        bool must_sea = false;

        FOR(dir,NDIR) {
            int dr = DR[dir];
            int dc = DC[dir];

            int r2 = r+dr;
            int c2 = c+dc;

            if (in_bounds(r2, c2) && color[r2][c2] != -1 && color[r2][c2] != nbr) {
                if (nbr != -1) must_sea = true;
                nbr = color[r2][c2];
            }
        }

        if (must_sea) setgrid(r, c, SEA);
    }

    // Complete islands
    printf("  Complete islands\n");
    flood_islands();
    FOR(r,R) FOR(c,C) if (getgrid(r,c) == UNK) {
        bool must_sea = false;
        FOR(dir,NDIR) {
            int dr = DR[dir];
            int dc = DC[dir];

            int r2 = r+dr;
            int c2 = c+dc;

            if (in_bounds(r2, c2) && color[r2][c2] != -1) {
                int i = color[r2][c2];
                if (island_cursize[i] == isles[i].s) must_sea = true;
            }
        }

        if (must_sea) setgrid(r, c, SEA);
    }

    // Orphan escape
    // NOTE: This MUST be run immediately after "complete islands",
    // to ensure that we only escape incomplete islands!
    printf("  Land escape\n");
    land_escape();

    // No pools
    printf("  No pools\n");
    FOR(r,R-1) FOR(c,C-1) {
        int nsea = 0;
        FOR(dr,2) FOR(dc,2) {
            if (getgrid(r+dr, c+dc) == SEA) ++nsea;
        }

        if (nsea == 3) FOR(dr,2) FOR(dc,2) {
            if (getgrid(r+dr, c+dc) == UNK) setgrid(r+dr, c+dc, LAND);
        }

        // If there is a pool: contradiction.
        if (nsea == 4) {
            printf("Contradiction: there is a pool\n");
            contradiction = true;
        }
    }

    // Squeeze islands
    printf("  Squeeze islands\n");
    flood_unks();

    // Sea escape
    printf("  Sea escape\n");
    sea_escape();

    // Unreachables
    printf("  Unreachables\n");
    unreachables();

    printf("  dirty = %d\n", int(dirty));
}

bool solve()
{
    assert(validgen[currentgen]);

    steps = 0;
    do {
        solve_step();
        print_grid();

        if (contradiction) {
            // An ancestor call made an invalid guess. Parent invalidates our generation.
            printf("Encountered contradiction\n");
            return false;
        }
    } while (dirty);

    bool complete = true;
    FOR(r,R) FOR(c,C) if (getgrid(r, c) == UNK) complete = false;
    if (complete) {
        printf("Completed solve!\n");
        return true;
    }

    // Try branching from any cell with minimum unknown neighbors.
    int best_unk = 4;
    int best_r = -1;
    int best_c = -1;

    FOR(r,R) FOR(c,C) if (getgrid(r, c) == UNK) {
        int n_unk = 0;

        FOR(dir,NDIR) {
            int dr = DR[dir];
            int dc = DC[dir];

            int r2 = r+dr;
            int c2 = c+dc;

            if (in_bounds(r2, c2) && getgrid(r2, c2) == UNK) {
                ++n_unk;
            }
        }

        if (n_unk < best_unk) {
            best_unk = n_unk;
            best_r = r;
            best_c = c;
        }
    }

    printf("Branching from cell (%d, %d) with %d unknown neighbors...\n", best_r, best_c, best_unk);
    ++stat_nbranches;
    FOR(val, 2) {
        validgen.push_back(true);
        ++currentgen;
        int trialgen = currentgen;
        setgrid(best_r, best_c, val);

        if (solve()) {
            return true;
        } else {
            // Clear the trial set and the non-recursive solve steps from the call.
            validgen[trialgen] = false;
        }
    }

    return false;
}

void run()
{
    stat_nbranches = 0;

    scanf(" %d %d", &C, &R);
    scanf(" %d", &I);

    FOR(i,I) {
        scanf(" %d %d %d", &isles[i].r, &isles[i].c, &isles[i].s);
    }

    validgen.clear();

    // All cells are initially invalid (i.e. unknown).
    validgen.push_back(false);
    currentgen = 0;

    FOR(r,R) {
        FOR(c,C) {
            setgrid_direct(r, c, 0);
        }
    }

    // Numbered cells are certainly land.
    validgen.push_back(true);
    ++currentgen;

    FOR(i,I) {
        setgrid_direct(isles[i].r, isles[i].c, LAND);
    }

    // Now solve recursively.
    validgen.push_back(true);
    ++currentgen;
    bool success = solve();
    printf("Solve result :  %s\n", success ? "Success!" : "Failure");
    printf("    # branches = %d\n", stat_nbranches);

    print_grid();
}

int main()
{
    run();
    return 0;
}
