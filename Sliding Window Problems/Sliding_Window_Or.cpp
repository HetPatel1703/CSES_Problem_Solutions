/**
 *    author:  "Het Pethani"
 *    created: 12.07.2026 10:24:07
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
#define PARITY(n)         (__builtin_parityll(n)) 

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
 
bool checkBipartite(int src , vvll &adj , vector<int> &color){
    queue<int> q;
    q.push(src);
    color[src] = 0;
 
    while(!q.empty()){
        int node = q.front();
        q.pop();
        for(auto it : adj[node]){
            if(color[it] == -1){
                color[it] = 1 - color[node];
                q.push(it);
            }
            else if(color[it] == color[node]){
                return false;
            }
        }
    }
    return true;
}
pair<vll,vll> getBipartiteSets(int n , vvll &adj){
    vector<int> color(n+1 , -1);
    vll leftPart , rightPart;
 
    for(int i=1;i<=n;i++){
        if(color[i] != -1) continue;
        queue<int> q;
        q.push(i);
        color[i] = 0;
        while(!q.empty()){
            int node = q.front();
            q.pop();
            if(color[node] == 0)
                leftPart.pb(node);
            else
                rightPart.pb(node);
 
            for(auto it : adj[node]){
                if(color[it] == -1){
                    color[it] = 1 - color[node];
                    q.push(it);
                }
            }
        }
    }
    return {leftPart , rightPart};
}
 
vll LPS(string s){
    int n=sz(s);
    vll kmp(n,0);
    int l=0;
    int i=1;
    while(i<n){
        if(s[i]==s[l]){
            l++;
            kmp[i]=l;
            i++;
        }else if(l)l=kmp[l-1];
        else {
            kmp[i]=0;
            i++;
        }
    }
    return kmp;
}
struct SparseTable {
    vector<vector<int>> st;
    
    SparseTable(vector<int>& arr) {
        int k = log2(arr.size()) + 1;
        st.assign(arr.size(), vector<int>(k));
        
        for(int i = 0; i < arr.size(); i++) st[i][0] = arr[i];
        
        for(int j = 1; j < k; j++) {
            for(int i = 0; i + (1 << j) <= arr.size(); i++) {
                st[i][j] = st[i][j-1] | st[i + (1 << (j-1))][j-1];
            }
        }
    }
    
    int query(int l, int r) {
        int j = log2(r - l + 1);
        return st[l][j] | st[r - (1 << j) + 1][j];
    }
    int querymin(int l, int r) {
        int j = log2(r - l + 1);
        return min(st[l][j] , st[r - (1 << j) + 1][j]);
    }
    int querymax(int l, int r) {
        int j = log2(r - l + 1);
        return max(st[l][j] , st[r - (1 << j) + 1][j]);
    }
    int querygcd(int l, int r) {
        int j = log2(r - l + 1);
        return gcd(st[l][j] , st[r - (1 << j) + 1][j]);
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



struct Stack {
    stack<pair<int,int>>st;

    bool empty() {
        return st.empty();
    }

    void push(int x) {
        if (st.empty())
            st.push({x, x});
        else
            st.push({x,st.top().ss|x});
    }

    void pop() {
        st.pop();
    }

    int topValue() {
        return st.top().ff;
    }

    int get() {
        return st.top().ss;
    }
};

struct Queue {
    Stack s1, s2;

    void move() {
        while (!s1.empty()) {
            int x = s1.topValue();
            s1.pop();
            s2.push(x);
        }
    }

    void push(int x) {
        s1.push(x);
    }

    void pop() {
        if (s2.empty())
            move();
        s2.pop();
    }

    int query() {
        if (s1.empty()) return s2.get();
        if (s2.empty()) return s1.get();
        return s1.get()|s2.get();
    }
};

void solve() {
    i2(n, k);
    i4(x, a, b, c);

    Queue q;

    auto nxt = [&](int v) {
        return (1LL * v * a + b) % c;
    };

    int l = x, r = x;

    q.push(r);

    for (int i = 1; i < k; i++) {
        r = nxt(r);
        q.push(r);
    }

    int ans = q.query();

    for (int i = k; i < n; i++) {
        q.pop();
        l = nxt(l);
        r = nxt(r);
        q.push(r);
        ans ^= q.query();
    }
    oe(ans);
}
 
signed main(){
    Code_ By_ HP;
    // int t;cin>>t;
    int t=1;
    while(t--){
        solve();
    }
}
