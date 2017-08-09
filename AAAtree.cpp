#include <cstdio>
#include <cstring>
#include <algorithm>
#include <iostream>

using namespace std;

const int N = 200005;
const int inf = ~0U>>1;

// node information
int fa[N], c[N][4], val[N];
bool rev[N], in[N];
// current information
int tot, ROOT;
int n, m;
int edge[N][2];

// rubbish collection
int R[N], rcnt;
// tools stack
int stack[N], scnt;
// tag
struct tag {
    int a, b; // ax + b
    tag() : a(1), b(0) {}
    tag(int _a, int _b) : a(_a), b(_b) {}
    inline bool exist() {
        return (a != 1) || (b != 0);
    }
    inline tag operator+(const tag & oth) {
        return tag(a * oth.a, b * oth.a + oth.b);
    }
    void clear() {
        a = 1;
        b = 0;
    }
};
tag ctag[N], ttag[N];

inline int calctag(int x, tag y) {
    return y.a * x + y.b;
}

// data
struct data {
    int sum, minv, maxv, size;
    data() : sum(0), minv(inf), maxv(-inf), size(0) {}
    data(int value) : sum(value), minv(value), maxv(value), size(1) {}
    data(int _sum, int _minv, int _maxv, int _size) :
        sum(_sum), minv(_minv), maxv(_maxv), size(_size) {}
    inline data operator+(const data & oth) {
        return data(sum + oth.sum, min(minv, oth.minv), max(maxv, oth.maxv), size + oth.size);
    }
    void clear() {
        sum = 0;
        minv = inf;
        maxv = -inf;
        size = 0;
    }
};
data csum[N], tsum[N], asum[N];

inline data operator+(const data & a, const tag & b) {
    if (a.size == 0) return a;
    return data(a.sum * b.a + a.size * b.b, calctag(a.minv, b), calctag(a.maxv, b), a.size);
}

inline bool isroot(int x, int type) {
    if (type) {
        return !fa[x] || !in[fa[x]] || !in[x];
    } else {
        return !fa[x] || (c[fa[x]][0] != x && c[fa[x]][1] != x) || in[fa[x]] || in[x];
    }
}

inline void Rev(int x) {
    if (!x) return;
    swap(c[x][0], c[x][1]);
    rev[x] ^= 1;
}

inline void tagchain(int x, tag t) {
    if (!x) return;
    csum[x] = csum[x] + t;
    asum[x] = csum[x] + tsum[x];
    val[x] = calctag(val[x], t);
    ctag[x] = ctag[x] + t;
}

inline void tagtree(int x, tag t, bool type) {
    if (!x) return;
    tsum[x] = tsum[x] + t;
    ttag[x] = ttag[x] + t;
    if (!in[x] && type) {
        tagchain(x, t);
    } else {
        asum[x] = csum[x] + tsum[x];
    }
}

inline void pushdown(int x) {
    if (!x) return;
    if (rev[x]) {
        Rev(c[x][0]); Rev(c[x][1]); rev[x] = 0;
    }
    if (!in[x] && ctag[x].exist()) {
        tagchain(c[x][0], ctag[x]);
        tagchain(c[x][1], ctag[x]);
        ctag[x].clear();
    }
    if (ttag[x].exist()) {
        tagtree(c[x][0], ttag[x], 0); tagtree(c[x][1], ttag[x], 0);
        tagtree(c[x][2], ttag[x], 1); tagtree(c[x][3], ttag[x], 1);
        ttag[x].clear();
    }
}

inline void update(int x) {
    tsum[x].clear();
    for (int i = 0; i < 2; i++)
        if (c[x][i]) {
            tsum[x] = tsum[x] + tsum[c[x][i]];
        }
    for (int i = 2; i < 4; i++)
        if (c[x][i]) {
            tsum[x] = tsum[x] + asum[c[x][i]];
        }
    if (in[x]) {
        csum[x].clear();
        asum[x] = tsum[x];
    } else {
        csum[x] = data(val[x]);
        for (int i = 0; i < 2; i++)
            if (c[x][i]) {
                csum[x] = csum[x] + csum[c[x][i]];
            }
        asum[x] = csum[x] + tsum[x];
    }
}

inline int getson(int x, int t) {
    pushdown(c[x][t]);
    return c[x][t];
}

inline void rotate(int x, int t) {
    int y = fa[x];
    int w = (c[y][t + 1] == x) + t;
    c[y][w] = c[x][w ^ 1];
    if (c[x][w ^ 1]) fa[c[x][w ^ 1]] = y;
    if (fa[y]) {
        int z = fa[y];
        for (int i = 0; i < 4; i++)
            if (c[z][i] == y) {
                c[z][i] = x;
            }
    }
    fa[x] = fa[y]; fa[y] = x;
    c[x][w ^ 1] = y;
    update(y);
}

inline void splay(int x, int type = 0) {
    scnt = 1; stack[1] = x;
    int tmp = x;
    while (!isroot(tmp, type)) {
        stack[++ scnt] = fa[tmp];
        tmp = fa[tmp];
    }
    while (scnt > 0) {
        pushdown(stack[scnt]);
        scnt --;
    }
    while (!isroot(x, type)) {
        int y = fa[x];
        if (!isroot(y, type)) {
            if ((c[fa[y]][type] == y) ^ (c[y][type] == x)) {
                rotate(x, type);
            } else {
                rotate(y, type);
            }
        }
        rotate(x, type);
    }
    update(x);
}

inline int getnewnode() {
    int ret;
    if (rcnt > 0) {
        ret = R[rcnt];
        rcnt --;
    } else {
        ret = ++ tot;
    }
    c[ret][2] = c[ret][3] = 0;
    in[ret] = 1;
    return ret;
}

inline void setson(int x, int t, int y) {
    c[x][t] = y;
    fa[y] = x;
}

inline int getid(int x) {
    for (int i = 0; i < 4; i++)
        if (c[fa[x]][i] == x) {
            return i;
        }
    return -1;
}

inline void add(int x, int y) {
    if (!y) return;
    pushdown(x);
    for (int i = 2; i < 4; i++) {
        if (!c[x][i]) {
            setson(x, i, y);
            return;
        }
    }
    while (c[x][2] && in[c[x][2]]) {
        x = getson(x, 2);
    }
    int z = getnewnode();
    setson(z, 2, c[x][2]);
    setson(z, 3, y);
    setson(x, 2, z);
    splay(z, 2);
}

inline void del(int x) {
    if (!x) return;
    splay(x, 0);
    if (!fa[x]) return;
    int y = fa[x];
    if (in[y]) {
        scnt = 1; stack[1] = y;
        int tmp = y;
        int z = fa[y];
        while (!isroot(tmp, 2)) {
            stack[++ scnt] = fa[tmp];
            tmp = fa[tmp];
        }
        while (scnt > 0) {
            pushdown(stack[scnt]);
            scnt --;
        }
        if (z) {
            setson(z, getid(y), getson(y, getid(x) ^ 1));
            splay(z, 2);
        }
        R[++ rcnt] = y;
    } else {
        c[y][getid(x)] = 0;
        splay(y, 0);
    }
    fa[x] = 0;
}

inline int getfa(int x) {
    splay(x, 0);
    if (!fa[x]) return 0;
    if (!in[fa[x]]) return fa[x];
    int t = fa[x];
    splay(t, 2);
    return fa[t];
}

inline int access(int x) {
    int y = 0;
    for (; x; y = x, x = getfa(x)) {
        //printf("%d %d\n", x, y);
        splay(x, 0);
        del(y);
        add(x, c[x][1]);
        setson(x, 1, y);
        update(x);
    }
    //puts("OUT");
    return y;
}

inline int lca(int x, int y) {
    access(x);
    return access(y);
}

inline int root(int x) {
    access(x);
    splay(x, 0);
    while (c[x][0]) x = c[x][0];
    return x;
}

inline void makeroot(int x) {
    access(x);
    splay(x, 0);
    Rev(x);
}

inline void link(int x, int y) {
    makeroot(x);
    add(y, x);
    access(x);
}

inline void cut(int x) {
    access(x);
    splay(x, 0);
    fa[c[x][0]] = 0;
    c[x][0] = 0;
    update(x);
}

inline void modifychain(int x, int y, tag p) {
    makeroot(x);
    access(y);
    splay(y, 0);
    tagchain(y, p);
}

inline data querychain(int x, int y) {
    makeroot(x);
    access(y);
    splay(y, 0);
    return csum[y];
}

inline void modifytree(int x, tag p) {
    access(x);
    splay(x, 0);
    val[x] = calctag(val[x], p);
    for (int i = 2; i < 4; i++)
        if (c[x][i]) {
            tagtree(c[x][i], p, 1);
        }
    update(x);
    splay(x, 0);
}

inline data querytree(int x) {
    access(x);
    splay(x, 0);
    data ret = data(val[x]);
    for (int i = 2; i < 4; i++)
        if (c[x][i]) ret = ret + asum[c[x][i]];
    return ret;
}

namespace Reader {
	const int L = (1 << 20) + 5;
	char buffer[L], *S, *T;
	__inline bool getchar(char &ch) {
		if (S == T) {
			T = (S = buffer) + fread(buffer, 1, L, stdin);
			if (S == T) {
				ch = EOF;
				return false;
			}
		}
		ch = *S ++;
		return true;
	}
	__inline bool getint(int &x) {
		char ch;
		for (; getchar(ch) && (ch < '0' || ch > '9'); );
		if (ch == EOF) return false;
		x = ch - '0';
		for (; getchar(ch), ch >= '0' && ch <= '9'; )
			x = x * 10 + ch - '0';
		return true;
	}
}

int main() {
    scanf("%d%d", &n, &m);
    tot = n;
    for (int i = 1; i < n; i++) {
        Reader::getint(edge[i][0]);
        Reader::getint(edge[i][1]);
    }
    for (int i = 1; i <= n; i++) {
        Reader::getint(val[i]);
        update(i);
    }
    for (int i = 1; i < n; i++) {
        link(edge[i][0], edge[i][1]);
    }
    Reader::getint(ROOT);
    makeroot(ROOT);
    for (int ii = 1; ii <= m; ii++) {
        int k, x, y, z;
        Reader::getint(k);
        if (k == 1) {
            Reader::getint(ROOT);
            makeroot(ROOT);
        }
        if (k == 9) {
            Reader::getint(x);
            Reader::getint(y);
            if (lca(x, y) == x) continue;
            cut(x);
            link(y, x);
            makeroot(ROOT);
        }
        if (k == 0) {
            Reader::getint(x);
            Reader::getint(y);
            modifytree(x, tag(0, y));
        }
        if (k == 5) {
            Reader::getint(x);
            Reader::getint(y);
            modifytree(x, tag(1, y));
        }
        if (k == 3) {
            Reader::getint(x);
            printf("%d\n", querytree(x).minv);
        }
        if (k == 4) {
            Reader::getint(x);
            printf("%d\n", querytree(x).maxv);
        }
        if (k == 11) {
            Reader::getint(x);
            printf("%d\n", querytree(x).sum);
        }
        if (k == 2) {
            Reader::getint(x);
            Reader::getint(y);
            Reader::getint(z);
            modifychain(x, y, tag(0, z));
            makeroot(ROOT);
        }
        if (k == 6) {
            Reader::getint(x);
            Reader::getint(y);
            Reader::getint(z);
            modifychain(x, y, tag(1, z));
            makeroot(ROOT);
        }
        if (k == 7) {
            Reader::getint(x);
            Reader::getint(y);
            printf("%d\n", querychain(x, y).minv);
            makeroot(ROOT);
        }
        if (k == 8) {
            Reader::getint(x);
            Reader::getint(y);
            printf("%d\n", querychain(x, y).maxv);
            makeroot(ROOT);
        }
        if (k == 10) {
            Reader::getint(x);
            Reader::getint(y);
            printf("%d\n", querychain(x, y).sum);
            makeroot(ROOT);
        }
    }
    return 0;
}
