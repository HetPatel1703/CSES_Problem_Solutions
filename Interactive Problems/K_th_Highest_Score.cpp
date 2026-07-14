/**
 *    author:  "Het Pethani"
 *    created: 13.07.2026 11:18:38
**/
#include <iostream>
#include <vector>
#include <map>
#include <algorithm>

using namespace std;

const long long INF = 2e18; 

int n, k;
map<int, long long> cache_F;
map<int, long long> cache_S;

long long queryF(int i) {
    if (i == 0) return INF;
    if (i == n + 1) return -INF;
    if (cache_F.count(i)) return cache_F[i];
    
    cout << "F " << i << endl;
    long long res;
    cin >> res;
    return cache_F[i] = res;
}

long long queryS(int i) {
    if (i == 0) return INF;
    if (i == n + 1) return -INF;
    if (cache_S.count(i)) return cache_S[i];
    
    cout << "S " << i << endl;
    long long res;
    cin >> res;
    return cache_S[i] = res;
}

int main() {
    ios_base::sync_with_stdio(false);
    cin.tie(NULL);

    if (!(cin >> n >> k)) return 0;

    int low = max(0, k - n);
    int high = min(n, k);

    while (low <= high) {
        int i = low + (high - low) / 2;
        int j = k - i; 

        long long val_Ai = queryF(i);
        long long val_Bj_plus_1 = queryS(j + 1);
        
        if (val_Ai < val_Bj_plus_1) {
            high = i - 1;
            continue;
        }

        long long val_Bj = queryS(j);
        long long val_Ai_plus_1 = queryF(i + 1);

        if (val_Bj < val_Ai_plus_1) {
            low = i + 1;
            continue;
        }

        long long ans = min(val_Ai, val_Bj);
        cout << "! " << ans << endl;
        break;
    }

    return 0;
}