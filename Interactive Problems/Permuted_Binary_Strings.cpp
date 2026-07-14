/**
 *    author:  "Het Pethani"
 *    created: 14.07.2026 10:57:49
**/
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

// using i64  = int64_t;
// using i128 = __int128;

// #include <ext/pb_ds/assoc_container.hpp>
// #include <ext/pb_ds/tree_policy.hpp>

// using namespace __gnu_pbds;

// template<class T>
// using ordered_set = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update>;
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
#define frfg(i, a, b, g) for (auto i = a; i < b; i+=g)
#define rfrf(i, a, b) for (auto i = a; i >= b; i--)
#define rfrfg(i, a, b, g) for (auto i = a; i >= b; i-=g)
 
const lld pi = 3.141592653589793238;
const ll INF = 4e18;
const ll NEG = -4e18;
const ll MOD = 1e9 + 7;
const ll MOD2 = 998244353;
 
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
ll mod_pow(ll a, ll b, ll m = MOD){
    ll res = 1;
    while (b){
        if (b & 1)
            res = mod_mul(res, a, m);
        a = mod_mul(a, a, m);
        b >>= 1;
    }
    return res;
}
ll mod_inv(ll a, ll m = MOD) { return mod_pow(a, m - 2, m); }
ll mod_div(ll a, ll b, ll m = MOD){return mod_mul(a, mod_inv(b, m), m); }
 
bool isPrime(ll n){
    if (n <= 1)return false;
    if (n <= 3)return true;
    if (n % 2 == 0 || n % 3 == 0)return false;
    for (ll i = 5; i * i <= n; i += 6)
        if (n % i == 0 || n % (i + 2) == 0)return false;
    return true;
}
bool isPowerOfTwo(ll n) { return n && !(n & (n - 1)); }
bool isPerfectSquare(ll x){
    ll s = sqrt(x);
    return s * s == x;
}
ll fact(ll n){
    ll res = 1;
    frf(i, 2, n + 1) res = mod_mul(res, i);
    return res;
}
ll nCr(ll n, ll r){
    if (r > n)return 0;
    if (r == 0 || r == n)return 1;
    ll res = 1;
    r = min(r, n - r);
    frf(i, 0, r){
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
//call fun...
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
void build_spf(){
    for(int i=2;i<=MAXA;i++){
        if(!spf[i]){
            for(int j=i;j<=MAXA;j+=i){
                if(!spf[j])spf[j]=i;
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


int ask(int l,int r)
{
    cout<<'?'<<" "<<l<<" "<<r<<endl;
    ll n;cin>>n;
    return n;
}
int DigitSum(ll n){
    int s=0;
    while(n){
        s+=n%10;
        n/=10;
    }return s;
}
class Disjointset {
    vector<int> parent, rank, size;
public:
    Disjointset(int n) {
        parent.resize(n+1);
        rank.resize(n+1, 0);
        size.resize(n+1, 1);
        for(int i = 0; i <= n; i++)
            parent[i] = i;
    }
 
    int findUPar(int node) {
        if(node == parent[node]) return node;
        return parent[node] = findUPar(parent[node]);
    }
 
    void unionByRank(int u, int v) {
        int pu = findUPar(u);
        int pv = findUPar(v);
        if(pu == pv) return;
        if(rank[pu] < rank[pv]) {
            parent[pu] = pv;
        } 
        else if(rank[pv] < rank[pu]) {
            parent[pv] = pu;
        } 
        else {
            parent[pv] = pu;
            rank[pu]++;
        }
    }
 
    void unionBySize(int u, int v) {
        int pu = findUPar(u);
        int pv = findUPar(v);
        if(pu == pv) return;
        if(size[pu] < size[pv]) {
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
    vector<ll> tree;
    vector<ll> arr;
    int n;
 
    void build(int idx, int l, int r) {
        if (l == r) {
            tree[idx] = arr[l];
            return;
        }
 
        int mid = (l + r) / 2;
        build(2 * idx + 1, l, mid);
        build(2 * idx + 2, mid + 1, r);
 
        tree[idx] = tree[2 * idx + 1] + tree[2 * idx + 2];
    }
 
    ll query(int idx, int l, int r, int ql, int qr) {
        if (ql > r || qr < l)
            return 0;
 
        if (ql <= l && r <= qr)
            return tree[idx];
 
        int mid = (l + r) / 2;
 
        ll leftRes = query(2 * idx + 1, l, mid, ql, qr);
        ll rightRes = query(2 * idx + 2, mid + 1, r, ql, qr);
 
        return leftRes + rightRes;
    }
 
    void update(int idx, int l, int r, int pos, ll val) {
        if (l == r) {
            arr[l] = val;
            tree[idx] = val;
            return;
        }
 
        int mid = (l + r) / 2;
 
        if (pos <= mid)
            update(2 * idx + 1, l, mid, pos, val);
        else
            update(2 * idx + 2, mid + 1, r, pos, val);
 
        tree[idx] = tree[2 * idx + 1] + tree[2 * idx + 2];
    }
 
public:
    SegmentTree(const vector<ll>& input) {
        arr = input;
        n = arr.size();
 
        tree.resize(4 * n);
        build(0, 0, n - 1);
    }
 
    ll getSum(int l, int r) {
        return query(0, 0, n - 1, l, r);
    }
 
    void setValue(int pos, ll val) {
        update(0, 0, n - 1, pos, val);
    }
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
        while(mask < n) mask <<= 1;
 
        while(mask){
            int next = idx + mask;
            if(next <= n && bit[next] < k){
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
#define sp(x) cout<<fixed<<setprecision(x)
#define oe(x) cout << x << "\n"
#define oe2(x, y) cout << x << " " << y << "\n"
#define oe3(x, y, z) cout << x << " " << y << " " << z << "\n"
#define oe4(a, b, c, d) cout << a << " " << b << " " << c <<" "<<d<<"\n"
#define o(x) cout << x << " "
#define o2(x, y) cout << x << " " << y << " "
#define o3(x, y, z) cout << x << " " << y << " " << z << " "
#define o4(a, b, c, d) cout << a << " " << b << " " << c << " " <<d <<" "
#define nl cout << "\n"
const int dx4[] = {-1, 1, 0, 0};
const int dy4[] = {0, 0, -1, 1};
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
 
#define v1(v,n) \
    vll v(n); \
    frf(i, 0, n) cin >> v[i]
#define v2(v,n, m)         \
    vvll v(n, vll(m));   \
    frf(i, 0, n)         \
        frf(j, 0, m)     \
            cin >> v[i][j]


void solve(){
    i1(n);
    vll ans(n,0);
    frf(k,0,10){
        string q="";
        frf(i,1,n+1){
            if((i>>k)&1)q+='1';
            else q+='0';
        }
        cout<<"? "<<q<<endl;
        string qa;
        cin>>qa;
        frf(i,0,n){
            if(qa[i]=='1'){
                ans[i]|=(1<<k);
            }
        }
    }
    cout<<"! ";
    for(auto it:ans)o(it);
    cout<<endl;
}
 
signed main(){
    Code_ By_ HP;
    // int t;cin>>t;
    int t=1;
    while(t--){
        solve();
    }
}
