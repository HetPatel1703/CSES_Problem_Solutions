#include <bits/stdc++.h>
using namespace std;
 
// ==================== MACROS ====================
#define Code_ ios_base::sync_with_stdio(false);
#define By_ cin.tie(NULL);
#define HP cout.tie(NULL);
 
#define ll long long
#define lld long double
#define ull unsigned long long
#define vi vector<int>
#define vll vector<ll>
#define vvi vector<vi>
#define vvll vector<vll>
#define vpi vector<pair<int, int>>
#define vpll vector<pair<ll, ll>>
#define vs vector<string>
#define vvs vector<vs>
#define pii pair<int, int>
#define pll pair<ll, ll>
#define pb push_back
#define mp make_pair
#define ff first
#define ss second
#define all(v) v.begin(), v.end()
#define allr(v) v.rbegin(), v.rend()
#define sz(v) (int)v.size()
#define mem(n, i) memset(n, i, sizeof n)
#define rep(i, a, b) for (int i = a; i < b; i++)
#define rev(i, a, b) for (int i = a; i >= b; i--)
 
const lld pi = 3.141592653589793238;
const ll INF = LONG_LONG_MAX;
const ll MOD = 1e9 + 7;
const ll MOD2 = 998244353;
 
// ==================== MATH FUNCTIONS ====================
ll gcd(ll a, ll b) { return b == 0 ? a : gcd(b, a % b); }
ll lcm(ll a, ll b) { return (a / gcd(a, b)) * b; }
ll mod_add(ll a, ll b, ll m = MOD) { return (a + b) % m; }
ll mod_sub(ll a, ll b, ll m = MOD) { return (a - b + m) % m; }
ll mod_mul(ll a, ll b, ll m = MOD) { return (a * b) % m; }
ll mod_pow(ll a, ll b, ll m = MOD)
{
    ll res = 1;
    while (b)
    {
        if (b & 1)
            res = mod_mul(res, a, m);
        a = mod_mul(a, a, m);
        b >>= 1;
    }
    return res;
}
ll mod_inv(ll a, ll m = MOD) { return mod_pow(a, m - 2, m); }
ll mod_div(ll a, ll b, ll m = MOD) { return mod_mul(a, mod_inv(b, m), m); }
 
bool isPrime(ll n)
{
    if (n <= 1)
        return false;
    if (n <= 3)
        return true;
    if (n % 2 == 0 || n % 3 == 0)
        return false;
    for (ll i = 5; i * i <= n; i += 6)
        if (n % i == 0 || n % (i + 2) == 0)
            return false;
    return true;
}
bool isPowerOfTwo(ll n) { return n && !(n & (n - 1)); }
bool isPerfectSquare(ll x)
{
    ll s = sqrt(x);
    return s * s == x;
}
ll fact(ll n)
{
    ll res = 1;
    rep(i, 2, n + 1) res = mod_mul(res, i);
    return res;
}
ll nCr(ll n, ll r)
{
    if (r > n)
        return 0;
    if (r == 0 || r == n)
        return 1;
    ll res = 1;
    r = min(r, n - r);
    rep(i, 0, r)
    {
        res = mod_mul(res, n - i);
        res = mod_div(res, i + 1);
    }
    return res;
}
 
// ==================== OUTPUT MACROS ====================
#define py cout << "YES\n"
#define pn cout << "NO\n"
#define pm cout << "-1\n"
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
#define s2(a, b) \
    string a, b; \
    cin >> a >> b
 
#define v1(n) \
    vi v(n);  \
    rep(i, 0, n) cin >> v[i]
#define v2(n) \
    vll v(n); \
    rep(i, 0, n) cin >> v[i]
#define v3(n, m)         \
    vvll v(n, vll(m));   \
    rep(i, 0, n)         \
        rep(j, 0, m)     \
            cin >> v[i][j]
            
            
void solve(){
    i1(n);
    v2(n);
    long long ans=0;
    rep(i,1,n)if(v[i]<v[i-1])ans+=(v[i-1]-v[i]),v[i]+=v[i-1]-v[i];
    o(ans);
    return;
}
 
signed main(){
    Code_ By_ HP;
    // int t;
    // cin>>t;
    // while(t--){
    //     solve();
    // }
    solve();
}