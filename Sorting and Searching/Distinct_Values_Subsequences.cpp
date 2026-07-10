/*
author: ""THE_BLACK_ALGO""
*/

#include <bits/stdc++.h>
using namespace std;
 
// ==================== MACROS ====================
#define Code_ ios_base::sync_with_stdio(false);
#define By_ cin.tie(NULL);
#define HP cout.tie(NULL);

// using i64  = int64_t;
// using i128 = __int128;
#define int long long
#define ll long long
#define lld long double
#define vll vector<ll>
#define vvll vector<vll>
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
const ll INF = LONG_LONG_MAX;
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

pll CRT(int r1,int m1,int r2,int m2){
    long long x,y;
    long long g = extgcd(m1,m2,x,y);

    if((r2-r1)%g!=0){
        return {-1,-1};
    }
    long long l = (m1/g)*m2;
    int k=(r2-r1)/g * x;
    k %= (m2/g);
    long long ans =(m1*k+r1)%l;
    ans = (ans + l)%l;
    return {ans,l};
}

bool find_any_solution(ll a,ll b,ll c,ll &x,ll &y,ll &g){
    g = extgcd(abs(a),abs(b),x,y);
    if(c % g != 0){
        return false;
    }
    x *= c/g;
    y *= c/g;
    if(a < 0) x = -x;
    if(b < 0) y = -y;
    return true;
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
 
ll fn(ll n){
    if(n % 4 == 0) return n;
    if(n % 4 == 1) return 1;
    if(n % 4 == 2) return n + 1;
    return 0;   
}
ll findXOR(ll l, ll r) { return fn(l - 1) ^ fn(r); }

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
    v1(a,n);
    int ans=0;
    int p=1;
    map<int,int>mp;
    frf(i,0,n){
        int seqs=(p*mod_inv(mp[a[i]]+1))%MOD;
        ans=mod_add(ans,seqs);
        mp[a[i]]++;
        p=mod_mul(p,mp[a[i]]+1);
        p=mod_mul(p,mod_inv(mp[a[i]]));
    }oe(ans%MOD);

    // vll dp(n+1);
    // dp[0]=1;
    // map<int,int>mp;
    // frf(i,1,n+1){
    //     int v=a[i-1];
    //     dp[i]=(2LL*dp[i-1])%MOD;
    //     if(mp.count(v)){
    //         int p=mp[v];
    //         dp[i]=(dp[i]-dp[p]+MOD)%MOD;
    //     }
    //     mp[v]=i;
    // }oe((dp[n]-1+MOD)%MOD);
}
 
signed main(){
    Code_ By_ HP;
    // int t;cin>>t;
    int t=1;
    while(t--){
        solve();
    }
}
