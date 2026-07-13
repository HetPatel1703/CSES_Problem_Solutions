/**
 *    author:  "Het Pethani"
 *    created: 13.07.2026 10:17:13
**/
#include <iostream>
#include <vector>
#include <algorithm>

using namespace std;

// Minimal Line structure
struct Line {
    long long m = 0, c = 0;
    long long eval(long long x) const { return m * x + c; }
};

const int MAXM = 200005;
Line tree[4 * MAXM]; // Global zero-initialization acts as our 0-area baseline

// 1. Pure Li Chao Tree descent
void add_line(int node, int l, int r, Line line) {
    int mid = l + (r - l) / 2;
    bool left_better = line.eval(l) > tree[node].eval(l);
    bool mid_better = line.eval(mid) > tree[node].eval(mid);
    
    if (mid_better) swap(tree[node], line);
    if (l == r) return;
    
    if (left_better != mid_better) add_line(2 * node, l, mid, line);
    else add_line(2 * node + 1, mid + 1, r, line);
}

// 2. Segment Tree range routing
void add_seg(int node, int l, int r, int ql, int qr, Line line) {
    if (ql <= l && r <= qr) { 
        add_line(node, l, r, line); 
        return; 
    }
    int mid = l + (r - l) / 2;
    if (ql <= mid) add_seg(2 * node, l, mid, ql, qr, line);
    if (qr > mid) add_seg(2 * node + 1, mid + 1, r, ql, qr, line);
}

// 3. Point Query for the max area
long long query(int node, int l, int r, int x) {
    long long res = tree[node].eval(x);
    if (l == r) return res;
    int mid = l + (r - l) / 2;
    if (x <= mid) return max(res, query(2 * node, l, mid, x));
    return max(res, query(2 * node + 1, mid + 1, r, x));
}

int main() {
    // Fast I/O
    ios_base::sync_with_stdio(false);
    cin.tie(NULL);

    int n, k;
    if (!(cin >> n >> k)) return 0;

    vector<long long> x(n + 1);
    for (int i = 1; i <= n; i++) cin >> x[i];

    // Monotonic stacks for global bounds (Left and Right limits)
    vector<int> L(n + 1, 1), R(n + 1, n);
    vector<int> st;
    for (int i = 1; i <= n; i++) {
        while (!st.empty() && x[st.back()] >= x[i]) st.pop_back();
        if (!st.empty()) L[i] = st.back() + 1;
        st.push_back(i);
    }
    st.clear();
    for (int i = n; i >= 1; i--) {
        while (!st.empty() && x[st.back()] >= x[i]) st.pop_back();
        if (!st.empty()) R[i] = st.back() - 1;
        st.push_back(i);
    }

    int M = n - k + 1;
    
    // Helper to clamp boundaries safely
    auto add = [&](long long ql, long long qr, long long m, long long c) {
        ql = max(1LL, ql); 
        qr = min((long long)M, qr);
        if (ql <= qr) add_seg(1, 1, M, ql, qr, {m, c});
    };

    // Calculate segments directly
    for (int i = 1; i <= n; i++) {
        long long l = L[i], r = R[i], X = x[i];
        long long j1 = min(l, r - k + 1);
        long long j2 = max(l, r - k + 1);

        // Rising slope, Flat peak, Falling slope
        add(l - k + 1, j1, X, X * (k - l));
        add(j1, j2, 0, X * min(r - l + 1, (long long)k));
        add(j2, r, -X, X * (r + 1));
    }

    // Output all queries
    for (int j = 1; j <= M; j++) {
        cout << query(1, 1, M, j) << (j == M ? "" : " ");
    }
    cout << "\n";

    return 0;
}