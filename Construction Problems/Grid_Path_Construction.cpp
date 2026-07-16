/**
 *    author:  "Het Pethani"
 *    created: 16.07.2026 11:22:33
**/
#pragma GCC optimize("O3")
#include <iostream>
#include <iomanip>
#include <vector>
#include <array>
#include <deque>
#include <list>
#include <forward_list>
#include <queue>
#include <stack>
#include <set>
#include <map>
#include <unordered_set>
#include <unordered_map>
#include <string>
#include <cstring>
#include <algorithm>
#include <numeric>
#include <functional>
#include <utility>
#include <tuple>
#include <bitset>
#include <cmath>
#include <complex>
#include <random>
#include <chrono>
#include <limits>
#include <climits>
#include <cfloat>
#include <cassert>
#include <fstream>
#include <sstream>
#include <iterator>
#include <exception>
#include <stdexcept>
#include <type_traits>
#include <memory>
#include <optional>
#include <variant>
#include <any>
#include <filesystem>
using namespace std;

// ==================== MACROS ====================
#define Code_ ios_base::sync_with_stdio(false);
#define By_ cin.tie(NULL);
#define HP cout.tie(NULL);

#define int long long
#define ll long long
#define lld long double
#define vll vector<ll>
#define vvll vector<vll>
#define vvvll vector<vvll>
#define vvvvll vector<vvvll>
#define vpll vector<pair<ll, ll>>
#define pll pair<ll, ll>
#define pb push_back
#define ff first
#define ss second
#define all(v) v.begin(), v.end()
#define rall(v) v.rbegin(), v.rend()
#define sz(v) (int)v.size()
#define frf(i, a, b) for (auto i = a; i < b; i++)
#define frfg(i, a, b, g) for (auto i = a; i < b; i += g)
#define rfrf(i, a, b) for (auto i = a; i >= b; i--)
#define rfrfg(i, a, b, g) for (auto i = a; i >= b; i -= g)

const lld pi = 3.141592653589793238;
// const int INF = 4e18;
// const int NEG = -4e18;
const int MOD = 1e9 + 7;
const int MOD2 = 998244353;

// ==================== MATH FUNCTIONS ====================
ll gcd(ll a, ll b) { return b == 0 ? a : gcd(b, a % b); }
ll lcm(ll a, ll b) { return (a / gcd(a, b)) * b; }
ll extgcd(ll a, ll b, ll &x, ll &y) {
    if (b == 0) {
        x = 1;
        y = 0;
        return a;
    }
    ll x1, y1;
    ll g = extgcd(b, a % b, x1, y1);
    x = y1;
    y = x1 - (a / b) * y1;
    return g;
}

ll mod_add(ll a, ll b, ll m = MOD) { return (a + b) % m; }
ll mod_sub(ll a, ll b, ll m = MOD) { return (a - b + m) % m; }
ll mod_mul(ll a, ll b, ll m = MOD) { return (a * b) % m; }
ll mod_pow(ll a, ll b, ll m = MOD) {
    ll res = 1;
    while (b) {
        if (b & 1)
            res = mod_mul(res, a, m);
        a = mod_mul(a, a, m);
        b >>= 1;
    }
    return res;
}
ll mod_inv(ll a, ll m = MOD) { return mod_pow(a, m - 2, m); }
ll mod_div(ll a, ll b, ll m = MOD) { return mod_mul(a, mod_inv(b, m), m); }

bool isPrime(ll n) {
    if (n <= 1) return false;
    if (n <= 3) return true;
    if (n % 2 == 0 || n % 3 == 0) return false;
    for (ll i = 5; i * i <= n; i += 6)
        if (n % i == 0 || n % (i + 2) == 0) return false;
    return true;
}
bool isPowerOfTwo(ll n) { return n && !(n & (n - 1)); }
bool isPerfectSquare(ll x) {
    ll s = sqrt(x);
    return s * s == x;
}
ll fact(ll n) {
    ll res = 1;
    frf(i, 2, n + 1) res = mod_mul(res, i);
    return res;
}
ll nCr(ll n, ll r) {
    if (r > n) return 0;
    if (r == 0 || r == n) return 1;
    ll res = 1;
    r = min(r, n - r);
    frf(i, 0, r) {
        res = mod_mul(res, n - i);
        res = mod_div(res, i + 1);
    }
    return res;
}

// ----- DIVISORS & FACTORIZATION -----
vll getDivisors(ll n) {
    vll divs;
    for (ll i = 1; i * i <= n; i++) {
        if (n % i == 0) {
            divs.pb(i);
            if (i * i != n) divs.pb(n / i);
        }
    }
    sort(all(divs));
    return divs;
}
vll getPrimeDivisors(ll n) {
    vll factors;
    for (ll i = 2; i * i <= n; i++) {
        while (n % i == 0) {
            factors.pb(i);
            n /= i;
        }
    }
    if (n > 1) factors.pb(n);
    return factors;
}

vector<int> divisorCount(int MAX) {
    vector<int> divs(MAX + 1, 0);
    for (int i = 1; i <= MAX; i++) {
        for (int j = i; j <= MAX; j += i) {
            divs[j]++;
        }
    }
    return divs;
}

// ==================== SIEVE ====================
const int MAXN = 10000005;
vector<bool> sievePrime(MAXN, true);
vector<int> primes;

void sieve() {
    sievePrime[0] = sievePrime[1] = false;
    for (int i = 2; i < MAXN; i++) {
        if (sievePrime[i]) {
            primes.push_back(i);
            for (int j = i * 2; j < MAXN; j += i) {
                sievePrime[j] = false;
            }
        }
    }
}

const int MAXA = 500000;
int spf[MAXA + 1];
void build_spf() {
    for (int i = 2; i <= MAXA; i++) {
        if (!spf[i]) {
            for (int j = i; j <= MAXA; j += i) {
                if (!spf[j]) spf[j] = i;
            }
        }
    }
}

#define SET_BIT(n, k)     ((n) | (1LL << (k)))
#define CLEAR_BIT(n, k)   ((n) & ~(1LL << (k)))
#define TOGGLE_BIT(n, k)  ((n) ^ (1LL << (k)))
#define CHECK_BIT(n, k)   (((n) >> (k)) & 1)
#define LSB(n)            ((n) & -(n))
#define IS_POWER_OF_2(n)  ((n) > 0 && ((n) & ((n) - 1)) == 0)
#define CLEAR_LSB(n)      ((n) & ((n) - 1))
#define COUNT_SET_BITS(n) (__builtin_popcountll(n))
#define COUNT_LEAD_ZEROS(n) (__builtin_clzll(n))
#define COUNT_TRAIL_ZEROS(n) (__builtin_ctzll(n))

int ask(int l, int r) {
    cout << '?' << " " << l << " " << r << endl;
    ll n;
    cin >> n;
    return n;
}
int DigitSum(ll n) {
    int s = 0;
    while (n) {
        s += n % 10;
        n /= 10;
    }
    return s;
}

class Disjointset {
    vector<int> parent, rank, size;
public:
    Disjointset(int n) {
        parent.resize(n + 1);
        rank.resize(n + 1, 0);
        size.resize(n + 1, 1);
        for (int i = 0; i <= n; i++)
            parent[i] = i;
    }
    int findUPar(int node) {
        if (node == parent[node]) return node;
        return parent[node] = findUPar(parent[node]);
    }
    void unionByRank(int u, int v) {
        int pu = findUPar(u);
        int pv = findUPar(v);
        if (pu == pv) return;
        if (rank[pu] < rank[pv]) {
            parent[pu] = pv;
        } else if (rank[pv] < rank[pu]) {
            parent[pv] = pu;
        } else {
            parent[pv] = pu;
            rank[pu]++;
        }
    }
    void unionBySize(int u, int v) {
        int pu = findUPar(u);
        int pv = findUPar(v);
        if (pu == pv) return;
        if (size[pu] < size[pv]) {
            parent[pu] = pv;
            size[pv] += size[pu];
        } else {
            parent[pv] = pu;
            size[pu] += size[pv];
        }
    }
    int getSize(int node) {
        return size[findUPar(node)];
    }
};

class SegmentTree {
private:
    struct Node {
        ll sum;
        ll mn;
        ll mx;
        ll gcd;
    };
    vector<Node> tree;
    vector<ll> arr;
    int n;
    Node merge(Node a, Node b) {
        return {
            a.sum + b.sum,
            min(a.mn, b.mn),
            max(a.mx, b.mx),
            gcd(a.gcd, b.gcd)
        };
    }
    void build(int idx, int l, int r) {
        if (l == r) {
            tree[idx] = {arr[l], arr[l], arr[l], arr[l]};
            return;
        }
        int mid = (l + r) / 2;
        build(2 * idx + 1, l, mid);
        build(2 * idx + 2, mid + 1, r);
        tree[idx] = merge(tree[2 * idx + 1], tree[2 * idx + 2]);
    }
    Node query(int idx, int l, int r, int ql, int qr) {
        if (qr < l || ql > r) return {0, LLONG_MAX, LLONG_MIN, 0};
        if (ql <= l && r <= qr) return tree[idx];
        int mid = (l + r) / 2;
        Node left = query(2 * idx + 1, l, mid, ql, qr);
        Node right = query(2 * idx + 2, mid + 1, r, ql, qr);
        return merge(left, right);
    }
    void update(int idx, int l, int r, int pos, ll val) {
        if (l == r) {
            arr[l] = val;
            tree[idx] = {val, val, val, val};
            return;
        }
        int mid = (l + r) / 2;
        if (pos <= mid) update(2 * idx + 1, l, mid, pos, val);
        else update(2 * idx + 2, mid + 1, r, pos, val);
        tree[idx] = merge(tree[2 * idx + 1], tree[2 * idx + 2]);
    }
public:
    SegmentTree(const vector<ll> &input) {
        arr = input;
        n = arr.size();
        tree.resize(4 * n);
        build(0, 0, n - 1);
    }
    ll getSum(int l, int r) { return query(0, 0, n - 1, l, r).sum; }
    ll getMin(int l, int r) { return query(0, 0, n - 1, l, r).mn; }
    ll getMax(int l, int r) { return query(0, 0, n - 1, l, r).mx; }
    ll getGCD(int l, int r) { return query(0, 0, n - 1, l, r).gcd; }
    void setValue(int pos, ll val) { update(0, 0, n - 1, pos, val); }
};

struct Fenwick {
    int n;
    vector<long long> bit;
    Fenwick(int sz) {
        n = sz;
        bit.assign(n + 1, 0);
    }
    void update(int idx, long long val) {
        while (idx <= n) {
            bit[idx] += val;
            idx += idx & -idx;
        }
    }
    long long query(int idx) {
        long long sum = 0;
        while (idx > 0) {
            sum += bit[idx];
            idx -= idx & -idx;
        }
        return sum;
    }
    int kth(int k) {
        int idx = 0;
        int mask = 1;
        while (mask < n) mask <<= 1;
        while (mask) {
            int next = idx + mask;
            if (next <= n && bit[next] < k) {
                idx = next;
                k -= bit[next];
            }
            mask >>= 1;
        }
        return idx + 1;
    }
    long long query(int l, int r) {
        return query(r) - query(l - 1);
    }
};

// ==================== OUTPUT MACROS ====================
#define PY cout << "YES\n"
#define py cout << "Yes\n"
#define PN cout << "NO\n"
#define pn cout << "No\n"
#define pm cout << "-1\n"
#define sp(x) cout << fixed << setprecision(x)
#define oe(x) cout << x << "\n"
#define oe2(x, y) cout << x << " " << y << "\n"
#define oe3(x, y, z) cout << x << " " << y << " " << z << "\n"
#define oe4(a, b, c, d) cout << a << " " << b << " " << c << " " << d << "\n"
#define o(x) cout << x << " "
#define o2(x, y) cout << x << " " << y << " "
#define o3(x, y, z) cout << x << " " << y << " " << z << " "
#define o4(a, b, c, d) cout << a << " " << b << " " << c << " " << d << " "
#define nl cout << "\n"
const int dx4[] = {-1, 1, 0, 0};
const int dy4[] = {0, 0, -1, 1};
const char dc[] = {'U', 'D', 'L', 'R'};
const int dx8[] = {-1, -1, -1, 0, 0, 1, 1, 1};
const int dy8[] = {-1, 0, 1, -1, 1, -1, 0, 1};

// ==================== INPUT MACROS ====================
#define i1(a) \
    ll a;     \
    cin >> a
#define i2(a, b) \
    ll a, b;     \
    cin >> a >> b
#define i3(a, b, c) \
    ll a, b, c;     \
    cin >> a >> b >> c
#define i4(a, b, c, d) \
    ll a, b, c, d;     \
    cin >> a >> b >> c >> d
#define i5(a, b, c, d, e) \
    ll a, b, c, d, e;     \
    cin >> a >> b >> c >> d >> e

#define s1(a) \
    string a; \
    cin >> a

#define v1(v, n)      \
    vll v(n);         \
    frf(i, 0, n) cin >> v[i]
#define v2(v, n, m)              \
    vvll v(n, vll(m));           \
    frf(i, 0, n)                 \
        frf(j, 0, m) cin >> v[i][j]

// ====================================================================
//  Beginning of the original Hamiltonian‑path solution
// ====================================================================

const int N = 2e5 + 10;
const ll LINF = 1e18;
const int INF = 1e9;
const int dy[4] = {1, 0, -1, 0}, dx[4] = {0, 1, 0, -1};
char F[4] = {'D', 'R', 'U', 'L'};
int P[256];

string pr[6][6][6][6][6][6];

bool is_solvable(int n, int m, int sy, int sx, int ty, int tx) {
    if (n == 1 && m == 1) return true;
    if (sy == ty && sx == tx) return false;

    if (n > m) {
        swap(n, m);
        swap(sy, sx);
        swap(ty, tx);
    }
    if (sx > tx) {
        swap(sx, tx);
        swap(sy, ty);
    }
    if (n == 1) {
        if (sx == 0 && tx == m - 1) return true;
        else return false;
    } else if (n == 2) {
        if (sx == tx && (sx == 0 || sx == m - 1)) return true;
        else if (sx == tx) return false;

        if ((sx + sy) % 2 == (tx + ty) % 2) return false;
        else return true;
    } else if ((n * m) % 2 == 1) {
        if ((sx + sy) % 2 == 0 && (tx + ty) % 2 == 0) return true;
        else return false;
    } else if (n == 3) {
        if ((sx + sy) % 2 == (tx + ty) % 2) return false;
        if ((sx + sy) % 2 == 1 && (sx < tx - 1 || (sy == 1 && sx < tx))) return false;
        if ((tx + ty) % 2 == 1 && (tx < sx - 1 || (ty == 1 && tx < sx))) return false;
        return true;
    } else {
        if ((sx + sy) % 2 == (tx + ty) % 2) return false;
        else return true;
    }
}

string solve(int n, int m, int sy, int sx, int ty, int tx) {
    if (n > m) {
        int tmpy, tmpx;

        tmpx = sy;
        tmpy = m - sx - 1;
        sx = tmpx;
        sy = tmpy;

        tmpx = ty;
        tmpy = m - tx - 1;
        tx = tmpx;
        ty = tmpy;

        swap(n, m);
        auto res = solve(n, m, sy, sx, ty, tx);

        for (int i = 0; i < sz(res); ++i) {
            res[i] = F[((int)(P[res[i]])+3) % 4];
        }
        return res;
    }
    if (sx > tx) {
        sx = m - sx - 1;
        tx = m - tx - 1;
        auto res = solve(n, m, sy, sx, ty, tx);
        for (int i = 0; i < sz(res); ++i) {
            if (res[i] == 'L')
                res[i] = 'R';
            else if (res[i] == 'R')
                res[i] = 'L';
        }
        return res;
    }
    if (sy > ty) {
        sy = n - sy - 1;
        ty = n - ty - 1;
        auto res = solve(n, m, sy, sx, ty, tx);
        for (int i = 0; i < res.size(); ++i) {
            if (res[i] == 'U')
                res[i] = 'D';
            else if (res[i] == 'D')
                res[i] = 'U';
        }
        return res;
    }

    if (n == 1) {
        string res;
        for (int i = 0; i < m - 1; ++i)
            res += 'R';
        return res;
    }
    if (n == 2 && sy == ty && sx + 1 == tx) {
        string res;
        if (sy == 0) {
            for (int i = 0; i < sx; ++i)
                res += 'L';
            res += 'D';
            for (int i = 0; i < m - 1; ++i)
                res += 'R';
            res += 'U';
            for (int i = m - 1; i > tx; --i)
                res += 'L';
        } else {
            for (int i = 0; i < sx; ++i)
                res += 'L';
            res += 'U';
            for (int i = 0; i < m - 1; ++i)
                res += 'R';
            res += 'D';
            for (int i = m - 1; i > tx; --i)
                res += 'L';
        }
        return res;
    }
    if (n <= 4 && m <= 5) {
        return pr[n][m][sy][sx][ty][tx];
    }
    if (sx >= 2 && is_solvable(n, m - 2, sy, sx - 2, ty, tx - 2)) {
        auto res = solve(n, m - 2, sy, sx - 2, ty, tx - 2);
        pll cur = {sy, sx - 2};
        for (int i = 0; i < res.size(); ++i) {
            pll next = {cur.ff + dy[P[res[i]]], cur.ss + dx[P[res[i]]]};
            if (cur.ss == 0 && next.ss == 0) {
                return res.substr(0, i) + "L" + solve(n, 2, cur.ff, 1, next.ff, 1) + "R" + res.substr(i + 1, res.size());
            }
            cur = next;
        }
    }
    if (tx <= m - 3 && is_solvable(n, m - 2, sy, sx, ty, tx)) {
        auto res = solve(n, m - 2, sy, sx, ty, tx);
        pll cur = {sy, sx};
        for (int i = 0; i < res.size(); ++i) {
            pll next = {cur.ff + dy[P[res[i]]], cur.ss + dx[P[res[i]]]};
            if (cur.ss == m - 3 && next.ss == m - 3) {
                return res.substr(0, i) + "R" + solve(n, 2, cur.ff, 0, next.ff, 0) + "L" + res.substr(i + 1, res.size());
            }
            cur = next;
        }
    }

    for (int i = sy; i < ty; ++i)
        for (int j = 0; j < m; ++j)
            if (is_solvable(i + 1, m, sy, sx, i, j) && is_solvable(n - i - 1, m, 0, j, ty - (i + 1), tx)) {
                auto res1 = solve(i + 1, m, sy, sx, i, j);
                auto res2 = solve(n - i - 1, m, 0, j, ty - (i + 1), tx);
                return res1 + "D" + res2;
            }

    for (int j = sx; j < tx; ++j)
        for (int i = 0; i < n; ++i)
            if (is_solvable(n, j + 1, sy, sx, i, j) && is_solvable(n, m - j - 1, i, 0, ty, tx - (j + 1))) {
                auto res1 = solve(n, j + 1, sy, sx, i, j);
                auto res2 = solve(n, m - j - 1, i, 0, ty, tx - (j + 1));
                return res1 + "R" + res2;
            }
}

bool checker(int n, int m, int sy, int sx, int ty, int tx, string res) {
    if (res.size() != n * m - 1) return false;
    vector<vector<int>> used(n, vector<int>(m));
    int y = sy, x = sx;
    for (int i = 0; i < n * m - 1; ++i) {
        if (y < 0 || y >= n || x < 0 || x >= m || used[y][x]) return false;
        used[y][x] = 1;
        int f = P[res[i]];
        y += dy[f];
        x += dx[f];
    }
    if (y != ty || x != tx) return false;
    return true;
}

signed main() {
    Code_ By_ HP;          
    P['D'] = 0;
    P['R'] = 1;
    P['U'] = 2;
    P['L'] = 3;
    pr[2][2][0][0][0][1] = "DRU";
    pr[2][2][0][0][1][0] = "RDL";
    pr[2][2][0][1][1][1] = "LDR";
    pr[2][2][1][0][1][1] = "URD";
    pr[2][3][0][0][0][1] = "DRRUL";
    pr[2][3][0][0][1][0] = "RRDLL";
    pr[2][3][0][0][1][2] = "DRURD";
    pr[2][3][0][1][0][2] = "LDRRU";
    pr[2][3][0][2][1][2] = "LLDRR";
    pr[2][3][1][0][1][1] = "URRDL";
    pr[2][3][1][1][1][2] = "LURRD";
    pr[2][4][0][0][0][1] = "DRRRULL";
    pr[2][4][0][0][0][3] = "DRURDRU";
    pr[2][4][0][0][1][0] = "RRRDLLL";
    pr[2][4][0][0][1][2] = "DRURRDL";
    pr[2][4][0][1][0][2] = "LDRRRUL";
    pr[2][4][0][1][1][3] = "LDRRURD";
    pr[2][4][0][2][0][3] = "LLDRRRU";
    pr[2][4][0][3][1][3] = "LLLDRRR";
    pr[2][4][1][0][1][1] = "URRRDLL";
    pr[2][4][1][0][1][3] = "URDRURD";
    pr[2][4][1][1][1][2] = "LURRRDL";
    pr[2][4][1][2][1][3] = "LLURRRD";
    pr[2][5][0][0][0][1] = "DRRRRULLL";
    pr[2][5][0][0][0][3] = "DRURDRRUL";
    pr[2][5][0][0][1][0] = "RRRRDLLLL";
    pr[2][5][0][0][1][2] = "DRURRRDLL";
    pr[2][5][0][0][1][4] = "DRURDRURD";
    pr[2][5][0][1][0][2] = "LDRRRRULL";
    pr[2][5][0][1][0][4] = "LDRRURDRU";
    pr[2][5][0][1][1][3] = "LDRRURRDL";
    pr[2][5][0][2][0][3] = "LLDRRRRUL";
    pr[2][5][0][2][1][4] = "LLDRRRURD";
    pr[2][5][0][3][0][4] = "LLLDRRRRU";
    pr[2][5][0][4][1][4] = "LLLLDRRRR";
    pr[2][5][1][0][1][1] = "URRRRDLLL";
    pr[2][5][1][0][1][3] = "URDRURRDL";
    pr[2][5][1][1][1][2] = "LURRRRDLL";
    pr[2][5][1][1][1][4] = "LURRDRURD";
    pr[2][5][1][2][1][3] = "LLURRRRDL";
    pr[2][5][1][3][1][4] = "LLLURRRRD";
    pr[3][3][0][0][0][2] = "RDLDRRUU";
    pr[3][3][0][0][1][1] = "RRDDLLUR";
    pr[3][3][0][0][2][0] = "RRDDLULD";
    pr[3][3][0][0][2][2] = "RRDLLDRR";
    pr[3][3][0][2][2][2] = "LLDDRURD";
    pr[3][3][1][1][2][2] = "RULLDDRR";
    pr[3][3][2][0][2][2] = "UURRDLDR";
    pr[3][4][0][0][0][1] = "DDRURDRUULL";
    pr[3][4][0][0][0][3] = "RRDLLDRRRUU";
    pr[3][4][0][0][1][0] = "RRRDDLULDLU";
    pr[3][4][0][0][1][2] = "RRRDDLLLURR";
    pr[3][4][0][0][2][1] = "RRRDDLULLDR";
    pr[3][4][0][0][2][3] = "RRRDLLLDRRR";
    pr[3][4][0][1][0][2] = "LDDRURDRUUL";
    pr[3][4][0][1][1][1] = "LDDRRRUULDL";
    pr[3][4][0][1][2][2] = "LDDRURURDDL";
    pr[3][4][0][2][0][3] = "LLDDRURDRUU";
    pr[3][4][0][2][1][2] = "RDDLLLUURDR";
    pr[3][4][0][2][2][3] = "RDLLULDDRRR";
    pr[3][4][0][3][1][3] = "LLLDDRURDRU";
    pr[3][4][1][0][2][0] = "URRRDDLULDL";
    pr[3][4][1][1][1][2] = "ULDDRRRUULD";
    pr[3][4][1][1][2][1] = "RDRUULLLDDR";
    pr[3][4][1][1][2][3] = "ULDDRRUURDD";
    pr[3][4][1][2][2][2] = "LDLUURRRDDL";
    pr[3][4][1][3][2][3] = "ULLLDDRURDR";
    pr[3][4][2][0][2][1] = "UURRRDDLULD";
    pr[3][4][2][0][2][3] = "UURRRDLLDRR";
    pr[3][4][2][1][2][2] = "LUURDRURDDL";
    pr[3][4][2][2][2][3] = "ULDLUURRRDD";
    pr[3][5][0][0][0][2] = "RDLDRRURDRUULL";
    pr[3][5][0][0][0][4] = "RRRDLLLDRRRRUU";
    pr[3][5][0][0][1][1] = "RRRRDDLULDLLUR";
    pr[3][5][0][0][1][3] = "RRRRDDLLLLURRR";
    pr[3][5][0][0][2][0] = "RRRRDDLULDLULD";
    pr[3][5][0][0][2][2] = "RRRRDDLULLLDRR";
    pr[3][5][0][0][2][4] = "RRRRDLLLLDRRRR";
    pr[3][5][0][2][0][4] = "LLDDRURDRRULUR";
    pr[3][5][0][2][1][3] = "LLDDRURDRRUULD";
    pr[3][5][0][2][2][2] = "LLDDRURRURDDLL";
    pr[3][5][0][2][2][4] = "LLDDRURDRUURDD";
    pr[3][5][0][4][2][4] = "LLLLDDRURDRURD";
    pr[3][5][1][1][1][3] = "ULDDRRUURRDDLU";
    pr[3][5][1][1][2][2] = "RRDRUULLLLDDRR";
    pr[3][5][1][1][2][4] = "ULDDRRUURRDLDR";
    pr[3][5][1][3][2][4] = "RULLLLDDRURDRR";
    pr[3][5][2][0][2][2] = "UURRRRDDLULLDR";
    pr[3][5][2][0][2][4] = "UURRRRDLLLDRRR";
    pr[3][5][2][2][2][4] = "ULDLUURRRRDLDR";
    pr[4][4][0][0][0][1] = "DRRDLLDRRRUUULL";
    pr[4][4][0][0][0][3] = "RRDLLDDRURDRUUU";
    pr[4][4][0][0][1][0] = "RRRDLLDRRDLLLUU";
    pr[4][4][0][0][1][2] = "RRRDDDLULDLUURR";
    pr[4][4][0][0][2][1] = "RRRDLLLDDRRRULL";
    pr[4][4][0][0][2][3] = "RRRDLLLDDRURDRU";
    pr[4][4][0][0][3][0] = "RRRDLLLDRRRDLLL";
    pr[4][4][0][0][3][2] = "RRRDLLLDDRURRDL";
    pr[4][4][0][1][0][2] = "LDRRDLLDRRRUUUL";
    pr[4][4][0][1][1][1] = "LDDDRURDRUUULDL";
    pr[4][4][0][1][1][3] = "LDRDLDRRRULUURD";
    pr[4][4][0][1][2][2] = "LDRRURDDDLLLURR";
    pr[4][4][0][1][3][1] = "LDRRURDDDLULLDR";
    pr[4][4][0][1][3][3] = "LDRRURDDLLLDRRR";
    pr[4][4][0][2][0][3] = "LLDRRDLLDRRRUUU";
    pr[4][4][0][2][1][2] = "RDDDLULDLUUURDR";
    pr[4][4][0][2][2][3] = "RDLLULDDDRURDRU";
    pr[4][4][0][2][3][2] = "RDLLULDDDRURRDL";
    pr[4][4][0][3][1][3] = "LLLDRRDLLDRRRUU";
    pr[4][4][0][3][3][3] = "LLLDRRRDLLLDRRR";
    pr[4][4][1][0][1][1] = "URRRDLDRDLLLURU";
    pr[4][4][1][0][1][3] = "URDDLDRRRULUURD";
    pr[4][4][1][0][2][0] = "URRRDLLDRRDLLLU";
    pr[4][4][1][0][2][2] = "URRRDLLDLDRRRUL";
    pr[4][4][1][0][3][1] = "URRRDDDLUULDLDR";
    pr[4][4][1][0][3][3] = "URRRDLLDLDRRURD";
    pr[4][4][1][1][1][2] = "ULDDDRURDRUUULD";
    pr[4][4][1][1][2][1] = "ULDDDRRRUUULDDL";
    pr[4][4][1][1][2][3] = "LURRRDLDLLDRRRU";
    pr[4][4][1][1][3][2] = "ULDDDRURUURDDDL";
    pr[4][4][1][2][1][3] = "LDRRDLLLUUURRRD";
    pr[4][4][1][2][2][2] = "URDDDLLLUUURDDR";
    pr[4][4][1][2][3][3] = "URDDLLUULDDDRRR";
    pr[4][4][1][3][2][3] = "ULLLDRRDLLDRRRU";
    pr[4][4][2][0][2][1] = "DRRRUUULLLDRRDL";
    pr[4][4][2][0][2][3] = "DRUULURRRDLDDRU";
    pr[4][4][2][0][3][0] = "UURRRDLLDRRDLLL";
    pr[4][4][2][0][3][2] = "DRUULURRRDLDRDL";
    pr[4][4][2][1][2][2] = "UULDDDRRRUUULDD";
    pr[4][4][2][1][3][1] = "URDDRUUULLLDDDR";
    pr[4][4][2][1][3][3] = "UULDDDRRUUURDDD";
    pr[4][4][2][2][2][3] = "URULLLDRDLDRRRU";
    pr[4][4][2][2][3][2] = "ULDDLUUURRRDDDL";
    pr[4][4][2][3][3][3] = "UULLLDRRDLLDRRR";
    pr[4][4][3][0][3][1] = "UUURRRDLLDRRDLL";
    pr[4][4][3][0][3][3] = "UUURRRDLLDDRURD";
    pr[4][4][3][1][3][2] = "LUUURRRDLLDRRDL";
    pr[4][4][3][2][3][3] = "UULDDLUUURRRDDD";
    pr[4][5][0][0][0][1] = "DRRRDLLLDRRRRUUULLL";
    pr[4][5][0][0][0][3] = "RRDLLDDRURDRRULURUL";
    pr[4][5][0][0][1][0] = "RRRRDLLLDRRRDLLLLUU";
    pr[4][5][0][0][1][2] = "RRRRDLDRDLLULDLUURR";
    pr[4][5][0][0][1][4] = "RRDLLDDRURDRRULUURD";
    pr[4][5][0][0][2][1] = "RRRRDLLLLDDRRRRULLL";
    pr[4][5][0][0][2][3] = "RRRRDLLLLDDRURDRRUL";
    pr[4][5][0][0][3][0] = "RRRRDLLLLDRRRRDLLLL";
    pr[4][5][0][0][3][2] = "RRRRDLLLLDDRURRRDLL";
    pr[4][5][0][0][3][4] = "RRRRDLLLLDDRURDRURD";
    pr[4][5][0][1][0][2] = "LDRRRDLLLDRRRRUUULL";
    pr[4][5][0][1][0][4] = "LDRRURDDLLLDRRRRUUU";
    pr[4][5][0][1][1][1] = "LDDDRURDRRULURULLDL";
    pr[4][5][0][1][1][3] = "LDRRURRDDDLLLLURRRU";
    pr[4][5][0][1][2][2] = "LDRRURRDLDRDLLLLURR";
    pr[4][5][0][1][2][4] = "LDRRURRDLDLLLDRRRRU";
    pr[4][5][0][1][3][1] = "LDRRURRDLDRDLLULLDR";
    pr[4][5][0][1][3][3] = "LDRDLDRRUUURRDLDRDL";
    pr[4][5][0][2][0][3] = "LLDRRRDLLLDRRRRUUUL";
    pr[4][5][0][2][1][2] = "LLDRDLDRRURDRUUULDL";
    pr[4][5][0][2][1][4] = "LLDRRDLLDRRRRULUURD";
    pr[4][5][0][2][2][3] = "LLDRRRURDDDLLLLURRR";
    pr[4][5][0][2][3][2] = "LLDRRRURDDDLULLLDRR";
    pr[4][5][0][2][3][4] = "LLDRRRURDDLLLLDRRRR";
    pr[4][5][0][3][0][4] = "LLLDRRRDLLLDRRRRUUU";
    pr[4][5][0][3][1][3] = "RDDDLULDLLURULURRDR";
    pr[4][5][0][3][2][4] = "RDLLULLDRDLDRRURDRU";
    pr[4][5][0][3][3][3] = "RDLLULLDRDLDRRURRDL";
    pr[4][5][0][4][1][4] = "LLLLDRRRDLLLDRRRRUU";
    pr[4][5][0][4][3][4] = "LLLLDRRRRDLLLLDRRRR";
    pr[4][5][1][0][1][1] = "URRRRDLLDRRDLLLLURU";
    pr[4][5][1][0][1][3] = "URRRRDDDLULDLLURURR";
    pr[4][5][1][0][2][0] = "URRRRDLLLDRRRDLLLLU";
    pr[4][5][1][0][2][2] = "URRRRDLLLDLDRRRRULL";
    pr[4][5][1][0][2][4] = "URRRRDLLLDLDRRURDRU";
    pr[4][5][1][0][3][1] = "URRRRDLDRDLLUULDLDR";
    pr[4][5][1][0][3][3] = "URRRRDLLLDLDRRURRDL";
    pr[4][5][1][1][1][2] = "ULDDDRURDRRULURULLD";
    pr[4][5][1][1][1][4] = "ULDDDRURDRRULULURRD";
    pr[4][5][1][1][2][1] = "ULDDDRRRRUUULLDRDLL";
    pr[4][5][1][1][2][3] = "ULDDDRURDRRUUULLDRD";
    pr[4][5][1][1][3][2] = "ULDDDRURUURRDLDRDLL";
    pr[4][5][1][1][3][4] = "ULDDDRURDRUULURRDDD";
    pr[4][5][1][2][1][3] = "ULLDRDLDRRURDRUUULD";
    pr[4][5][1][2][2][2] = "ULLDRDLDRRRRUUULDDL";
    pr[4][5][1][2][2][4] = "URRDLDLLUULDDDRRRRU";
    pr[4][5][1][2][3][3] = "ULLDRDLDRRURUURDDDL";
    pr[4][5][1][3][1][4] = "LLDRRRDLLLLUUURRRRD";
    pr[4][5][1][3][2][3] = "URDDDLLLLUUURRDLDRR";
    pr[4][5][1][3][3][4] = "URDDLLUULLDRDLDRRRR";
    pr[4][5][1][4][2][4] = "ULLLLDRRRDLLLDRRRRU";
    pr[4][5][2][0][2][1] = "DRRUURDDRUUULLLLDRD";
    pr[4][5][2][0][2][3] = "DRUULURRRRDLLDDRRUL";
    pr[4][5][2][0][3][0] = "UURRRRDLLLDRRRDLLLL";
    pr[4][5][2][0][3][2] = "DRUULURRRRDLLDRRDLL";
    pr[4][5][2][0][3][4] = "DRUULURRRRDLLDDRURD";
    pr[4][5][2][1][2][2] = "UULDDDRRRRUUULLDRDL";
    pr[4][5][2][1][2][4] = "UULDDDRRUUURRDLDDRU";
    pr[4][5][2][1][3][1] = "URRDLDRRUUULLLLDDDR";
    pr[4][5][2][1][3][3] = "UULDDDRRUUURRDLDRDL";
    pr[4][5][2][2][2][3] = "UULLDRDLDRRRRUUULDD";
    pr[4][5][2][2][3][2] = "ULDDLUUURRRRDLDRDLL";
    pr[4][5][2][2][3][4] = "UULLDRDLDRRRUUURDDD";
    pr[4][5][2][3][2][4] = "URULLLLDRRDLLDRRRRU";
    pr[4][5][2][3][3][3] = "ULLDRDLLUUURRRRDDDL";
    pr[4][5][2][4][3][4] = "UULLLLDRRRDLLLDRRRR";
    pr[4][5][3][0][3][1] = "UUURRRRDLLLDRRRDLLL";
    pr[4][5][3][0][3][3] = "UUURRRRDLLLDDRURRDL";
    pr[4][5][3][1][3][2] = "LUUURRRRDLLLDRRRDLL";
    pr[4][5][3][1][3][4] = "LUUURRRRDLLLDRDRURD";
    pr[4][5][3][2][3][3] = "UULDDLUUURRRRDLDRDL";
    pr[4][5][3][3][3][4] = "UULLDRDLLUUURRRRDDD";

    i1(t);
    while (t--) {
        int n, m, sy, sx, ty, tx;
        cin >> n >> m >> sy >> sx >> ty >> tx;
        --sy, --sx, --ty, --tx;
        if (is_solvable(n, m, sy, sx, ty, tx)) {
            PY;
            auto res = solve(n, m, sy, sx, ty, tx);
            oe(res);
        } else {
            PN;
        }
    }
}