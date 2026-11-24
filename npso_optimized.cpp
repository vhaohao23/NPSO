// ============================================================================
//  NPSO : Network Particle Swarm Optimization for Community Detection
//  Objective : Modularity Q  (undirected, unweighted graph)
//
//  Pipeline (theo tài liệu):
//     Particles initialization (LAR)
//     repeat Tmax times:
//         Particles evolutionary  (discrete PSO, Jaccard "minus")
//         Mutation
//         Local search (with isolated-vertex strategy)
//         Calculate fitness, pbest, gbest
//     Merge community  (post-processing on Xp, Pbp, Pg)
//
//  Input format (1-indexed):
//     {number_of_node} {number_of_edges}
//     {u v} per line  (edge list)
//
//  Compile:  g++ -O3 -march=native -funroll-loops -o npso npso.cpp
//  Run:      ./npso < graph.txt   [seed]  [pop] [Tmax]
// ============================================================================
#include <bits/stdc++.h>
using namespace std;

// --------------------------------------------------------------------------
// Fast RNG (xoshiro256**) -- much faster than std::mt19937 in hot loops.
// --------------------------------------------------------------------------
struct Rng {
    uint64_t s[4];
    explicit Rng(uint64_t seed = 0x9E3779B97F4A7C15ULL) {
        // splitmix64 to seed
        for (int i = 0; i < 4; ++i) {
            seed += 0x9E3779B97F4A7C15ULL;
            uint64_t z = seed;
            z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
            z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
            s[i] = z ^ (z >> 31);
        }
    }
    static inline uint64_t rotl(uint64_t x, int k) { return (x << k) | (x >> (64 - k)); }
    inline uint64_t next() {
        const uint64_t r = rotl(s[1] * 5, 7) * 9;
        const uint64_t t = s[1] << 17;
        s[2] ^= s[0]; s[3] ^= s[1]; s[1] ^= s[2]; s[0] ^= s[3];
        s[2] ^= t;    s[3] = rotl(s[3], 45);
        return r;
    }
    inline double dbl() { return (next() >> 11) * (1.0 / 9007199254740992.0); } // [0,1)
    inline int range(int n) { return (int)(((__uint128_t)next() * (uint64_t)n) >> 64); } // [0,n)
};

// --------------------------------------------------------------------------
// Graph in CSR format (Compressed Sparse Row).
// --------------------------------------------------------------------------
struct Graph {
    int n = 0;
    long long m = 0;                 // number of undirected edges
    vector<int> deg;                 // degree of each vertex
    vector<long long> off;           // CSR offsets  (size n+1)
    vector<int> adj;                 // CSR neighbors (size 2m)
    double inv2m = 0.0;              // 1 / (2m)

    inline const int* nbeg(int v) const { return &adj[off[v]]; }
    inline const int* nend(int v) const { return &adj[off[v + 1]]; }
};

static Graph readGraph(istream& in) {
    Graph g;
    long long mDeclared;
    if (!(in >> g.n >> mDeclared)) { cerr << "bad header\n"; exit(1); }

    // Read edges first (we store into temporary, then build CSR).
    vector<int> eu, ev;
    eu.reserve(mDeclared); ev.reserve(mDeclared);
    g.deg.assign(g.n, 0);

    int a, b;
    // Use a set of undirected edges to drop duplicates / self loops cheaply
    // via hashing only when needed; for speed we keep raw but skip self loops.
    while (in >> a >> b) {
        --a; --b;                              // to 0-indexed
        if (a < 0 || b < 0 || a >= g.n || b >= g.n) continue;
        if (a == b) continue;                  // skip self-loop
        eu.push_back(a); ev.push_back(b);
        g.deg[a]++; g.deg[b]++;
    }
    g.m = (long long)eu.size();

    // Build CSR offsets.
    g.off.assign(g.n + 1, 0);
    for (int v = 0; v < g.n; ++v) g.off[v + 1] = g.off[v] + g.deg[v];
    g.adj.assign(2 * g.m, 0);
    vector<long long> cur(g.off.begin(), g.off.end());
    for (long long i = 0; i < g.m; ++i) {
        int u = eu[i], w = ev[i];
        g.adj[cur[u]++] = w;
        g.adj[cur[w]++] = u;
    }
    g.inv2m = (g.m > 0) ? 1.0 / (2.0 * (double)g.m) : 0.0;
    return g;
}

// --------------------------------------------------------------------------
// Modularity helpers.
//   Q = sum_c [ e_in_c/(2m)  -  (tot_c/(2m))^2 ]
//   where e_in_c = 2 * (#edges inside c)  counted as endpoint-degree-inside,
//   tot_c = sum of degrees in c.
// We keep label arrays; compute Q from scratch in O(n + m) when needed.
// --------------------------------------------------------------------------
static double modularity(const Graph& g, const vector<int>& comm,
                         vector<double>& tot_buf, vector<double>& ein_buf) {
    const int n = g.n;
    // tot[c], ein[c] sized n (labels are in [0,n))
    fill(tot_buf.begin(), tot_buf.end(), 0.0);
    fill(ein_buf.begin(), ein_buf.end(), 0.0);
    for (int v = 0; v < n; ++v) tot_buf[comm[v]] += g.deg[v];
    for (int v = 0; v < n; ++v) {
        int cv = comm[v];
        const int* e = g.nbeg(v); const int* en = g.nend(v);
        for (; e != en; ++e) if (comm[*e] == cv) ein_buf[cv] += 1.0; // counts each internal edge twice (both endpoints)
    }
    double q = 0.0;
    const double inv2m = g.inv2m;
    for (int c = 0; c < n; ++c) {
        if (tot_buf[c] == 0.0 && ein_buf[c] == 0.0) continue;
        double tc = tot_buf[c] * inv2m;
        q += ein_buf[c] * inv2m - tc * tc;
    }
    return q;
}

// Normalize labels to 0..k-1 (dense). Returns number of communities.
static int normalizeLabels(vector<int>& lab) {
    static thread_local vector<int> remap;
    int n = (int)lab.size();
    // labels may be up to 2n-1 (temp labels n+i used in evolve)
    int maxLab = 0;
    for (int x : lab) if (x > maxLab) maxLab = x;
    if ((int)remap.size() < maxLab + 1) remap.assign(maxLab + 1, -1);
    else fill(remap.begin(), remap.begin() + (maxLab + 1), -1);
    int k = 0;
    for (int i = 0; i < n; ++i) {
        int c = lab[i];
        if (remap[c] == -1) remap[c] = k++;
        lab[i] = remap[c];
    }
    return k;
}

// --------------------------------------------------------------------------
// Decode a "locus-based" genotype (gi = neighbor index it points to) into
// community labels via connected components on the chosen-edge graph.
// Iterative union-find for O(n a(n)).
// --------------------------------------------------------------------------
struct DSU {
    vector<int> p, r;
    void init(int n) { p.resize(n); r.assign(n, 0); for (int i=0;i<n;++i) p[i]=i; }
    int find(int x){ while(p[x]!=x){ p[x]=p[p[x]]; x=p[x]; } return x; }
    void uni(int a,int b){ a=find(a); b=find(b); if(a==b) return; if(r[a]<r[b]) swap(a,b); p[b]=a; if(r[a]==r[b]) r[a]++; }
};

static void decodeLAR(const vector<int>& gene, DSU& dsu, vector<int>& comm) {
    int n = (int)gene.size();
    dsu.init(n);
    for (int i = 0; i < n; ++i) dsu.uni(i, gene[i]);
    for (int i = 0; i < n; ++i) comm[i] = dsu.find(i);
    normalizeLabels(comm);
}

// --------------------------------------------------------------------------
// Particle representation.
//   x : community label per vertex (the position / solution)
//   v : real velocity per vertex (init -1)
// --------------------------------------------------------------------------
struct Particle {
    vector<int>    x;       // position (labels), size n
    vector<double> v;       // velocity, size n
    vector<int>    pbx;     // personal best position
    double         fit = -1e18;
    double         pbfit = -1e18;
};

// --------------------------------------------------------------------------
// Jaccard-based "minus":  x_a - x_b = 1 - calSame(a,b)
// calSame uses the *community membership sets* of the two vertices.
// Interpretation: for vertex i, set A = vertices sharing i's community in
// solution a, set B = vertices sharing i's community in solution b.
// J(A,B) = |A ∩ B| / |A ∪ B|.
// We compute this per-vertex on demand using a stamp array. O(|A|+|B|).
// --------------------------------------------------------------------------
struct CommunityIndex {
    // Flat CSR layout: members of community c are
    //   flat[ start[c] .. start[c+1] )
    // Avoids allocating k separate vectors on every rebuild.
    vector<int> start;   // size k+1
    vector<int> flat;    // size n
    int k = 0;

    struct Span { const int* b; const int* e;
                  bool empty() const { return b == e; }
                  const int* begin() const { return b; }
                  const int* end()   const { return e; } };

    inline Span members(int c) const {
        return Span{ &flat[start[c]], &flat[start[c + 1]] };
    }

    void build(const vector<int>& lab, int k_) {
        k = k_;
        int n = (int)lab.size();
        start.assign(k + 1, 0);
        for (int v = 0; v < n; ++v) start[lab[v] + 1]++;
        for (int c = 0; c < k; ++c) start[c + 1] += start[c];
        flat.resize(n);
        // temp cursor reuses start copy
        static thread_local vector<int> cur;
        cur.assign(start.begin(), start.end());
        for (int v = 0; v < n; ++v) flat[cur[lab[v]]++] = v;
    }
};

// --------------------------------------------------------------------------
// NPSO main solver.
// --------------------------------------------------------------------------
struct NPSO {
    const Graph& g;
    Rng rng;
    int    pop;
    int    Tmax;
    double c1 = 1.0, c2 = 1.0;
    double muProb = 0.10;

    // scratch buffers (reused, avoid reallocation)
    vector<double> tot_buf, ein_buf;
    DSU dsu;
    vector<int> stamp;       // generic stamp buffer
    vector<int> ev_nx;       // reusable working copy for evolve
    int stampVal = 0;

    NPSO(const Graph& g_, uint64_t seed, int pop_, int Tmax_)
        : g(g_), rng(seed), pop(pop_), Tmax(Tmax_) {
        tot_buf.assign(g.n, 0.0);
        ein_buf.assign(g.n, 0.0);
        stamp.assign(g.n, 0);
        dsu.init(g.n);
    }

    inline double fitness(const vector<int>& comm) {
        return modularity(g, comm, tot_buf, ein_buf);
    }

    // ---- LAR initialization for one particle ----
    void initParticle(Particle& p) {
        int n = g.n;
        vector<int> gene(n);
        for (int i = 0; i < n; ++i) {
            int d = g.deg[i];
            if (d == 0) { gene[i] = i; continue; }       // isolated vertex -> own community
            const int* e = g.nbeg(i);
            gene[i] = e[rng.range(d)];                    // random neighbor
        }
        p.x.assign(n, 0);
        decodeLAR(gene, dsu, p.x);
        p.v.assign(n, -1.0);                              // velocity init -1
        p.fit = fitness(p.x);
        p.pbx = p.x;
        p.pbfit = p.fit;
    }

    // ---- Jaccard similarity of membership sets of vertex i in two solutions
    //      a and b, given precomputed community member lists. ----
    // calSame for vertex i:
    //   A = members of community a[i] in solution a
    //   B = members of community b[i] in solution b
    //   J = |A∩B| / |A∪B|
    inline double calSame(int i,
                          const vector<int>& a, const CommunityIndex& ia,
                          const vector<int>& b, const CommunityIndex& ib) {
        auto A = ia.members(a[i]);
        auto B = ib.members(b[i]);
        if (A.empty() || B.empty()) return 0.0;
        // stamp A, count intersection by scanning B
        ++stampVal;
        for (int x : A) stamp[x] = stampVal;
        int inter = 0;
        for (int x : B) if (stamp[x] == stampVal) ++inter;
        int uni = (int)(A.e - A.b) + (int)(B.e - B.b) - inter;
        return uni ? (double)inter / (double)uni : 0.0;
    }

    // Flat stamp-indexed memo for calSame within a single evolve() call.
    // calSame depends only on the pair (community in a, community in b).
    // We index by  key = a[i]*(kb+1) + b[i]  into a flat array, validated by a
    // per-evolve stamp so we never have to clear the whole array.
    vector<double> memoValPb, memoValGb;
    vector<int>    memoStampPb, memoStampGb;
    int            memoStamp = 0;

    inline double calSameMemo(int i, const vector<int>& a, const CommunityIndex& ia,
                              const vector<int>& b, const CommunityIndex& ib,
                              vector<double>& memoVal, vector<int>& memoStampArr) {
        long long key = (long long)a[i] * (long long)(ib.k + 1) + b[i];
        if (key < (long long)memoStampArr.size() && memoStampArr[key] == memoStamp)
            return memoVal[key];
        double val = calSame(i, a, ia, b, ib);
        if (key < (long long)memoStampArr.size()) {
            memoStampArr[key] = memoStamp;
            memoVal[key] = val;
        }
        return val;
    }

    // ---- Particle evolutionary step ----
    // For each vertex i compute velocity then probabilistically rewrite x_i's
    // community toward pbest or gbest.
    int evolve(Particle& p, const vector<int>& gbest,
                const CommunityIndex& idxX, const CommunityIndex& idxPb,
                const CommunityIndex& idxGb) {
        int n = g.n;
        // size flat memo arrays to the key space (kx*(kguide+1)); capped so a
        // pathological all-singleton solution doesn't blow memory (fallback:
        // keys beyond capacity simply aren't cached -> still correct).
        long long needPb = (long long)idxX.k * (long long)(idxPb.k + 1);
        long long needGb = (long long)idxX.k * (long long)(idxGb.k + 1);
        long long capKeys = (long long)4 * n * n > 4000000 ? 4000000 : (long long)4 * n * n;
        if (needPb > capKeys) needPb = capKeys;
        if (needGb > capKeys) needGb = capKeys;
        if ((long long)memoStampPb.size() < needPb) { memoStampPb.assign(needPb, -1); memoValPb.assign(needPb, 0.0); }
        if ((long long)memoStampGb.size() < needGb) { memoStampGb.assign(needGb, -1); memoValGb.assign(needGb, 0.0); }
        ++memoStamp;
        // ---- Phase 1: update velocity per vertex (reads only OLD x via idxX) ----
        for (int i = 0; i < n; ++i) {
            double w = (p.v[i] <= 0.0) ? 1.1 : 0.9;
            double r1 = rng.dbl(), r2 = rng.dbl();
            double sub_pb = 1.0 - calSameMemo(i, p.x, idxX, p.pbx, idxPb, memoValPb, memoStampPb);
            double sub_gb = 1.0 - calSameMemo(i, p.x, idxX, gbest, idxGb, memoValGb, memoStampGb);
            p.v[i] = w * p.v[i] + c1 * r1 * sub_pb + c2 * r2 * sub_gb;
        }
        // ---- Phase 2: decide which vertices trigger, BEFORE mutating x ----
        ev_nx.assign(p.x.begin(), p.x.end());   // reusable working copy
        vector<int>& nx = ev_nx;
        for (int i = 0; i < n; ++i) {
            double prob = 1.0 / (1.0 + exp(-p.v[i]));
            if (rng.dbl() <= prob) {
                bool useGb = (rng.dbl() < 0.5);
                const CommunityIndex& gi = useGb ? idxGb : idxPb;
                const vector<int>& guide = useGb ? gbest : p.pbx;
                int cu = guide[i];            // guide labels are stable
                auto S = gi.members(cu);
                int newLabel = n + i;         // guaranteed-unique temp label (>= n)
                for (int s : S) nx[s] = newLabel;
            }
        }
        p.x.swap(nx);
        return normalizeLabels(p.x);   // return community count
    }

    // ---- Mutation ----
    // Returns true if it modified p.x (caller then needs to normalize before LS).
    bool mutate(Particle& p, CommunityIndex& idxX) {
        if (rng.dbl() >= muProb) return false;
        int n = g.n;
        int u = rng.range(n);
        int oldC = p.x[u];
        int newLabel = u;          // u starts a new community
        // gather old-community members BEFORE modifying
        auto sameC = idxX.members(oldC);
        p.x[u] = newLabel;
        if (rng.dbl() < 0.5) {
            // Strategy 1: each old-community member -> new community w.p. 0.5
            for (int s : sameC) if (s != u && rng.dbl() < 0.5) p.x[s] = newLabel;
        } else {
            // Strategy 2: all neighbors of u joined into u's new community
            const int* e = g.nbeg(u); const int* en = g.nend(u);
            for (; e != en; ++e) p.x[*e] = newLabel;
        }
        return true;   // labels are NOT dense now; caller normalizes
    }

    // ---- Local search with isolated-vertex strategy ----
    // Greedy: for each vertex, move it to the neighboring community giving the
    // largest positive ΔQ; also consider becoming its own singleton community.
    // ΔQ for moving v out of A into B (undirected, unweighted):
    //   ΔQ = [ (ki_in_B - ki_in_A) / m ] - [ k_v*(tot_B - tot_A + k_v) / (2 m^2) ]
    // We maintain tot[c] (sum of degrees) and recompute internal edges to
    // neighbor communities on the fly.
    // localSearch reusable buffers (member-level, sized lazily)
    vector<double> ls_tot, ls_kiTo, ls_ein;
    vector<int>    ls_touched;
    vector<int>    ls_touchStamp;   // stamp-based "isTouched"
    int            ls_stamp = 0;
    // queue-based active set
    vector<int>    ls_queue;        // ring/linear queue of active vertices
    vector<char>   ls_inQueue;      // membership flag (avoid duplicates)

    // If kHint >= 0, comm is assumed already dense with kHint communities
    // (skips the O(n) normalize). Otherwise we normalize internally.
    // Returns the final modularity Q of comm (computed incrementally, so the
    // caller does NOT need a separate O(n+m) fitness() pass).
    double localSearch(vector<int>& comm, int kHint = -1) {
        int n = g.n;
        int k = (kHint >= 0) ? kHint : normalizeLabels(comm);

        // ensure capacity (labels can grow up to n via singletons)
        if ((int)ls_tot.size() < n) {
            ls_tot.assign(n, 0.0);
            ls_kiTo.assign(n, 0.0);
            ls_ein.assign(n, 0.0);
            ls_touchStamp.assign(n, 0);
        }
        if ((int)ls_inQueue.size() < n) ls_inQueue.assign(n, 0);
        // reset tot/ein for active communities, then accumulate.
        for (int c = 0; c < k; ++c) { ls_tot[c] = 0.0; ls_ein[c] = 0.0; }
        for (int v = 0; v < n; ++v) ls_tot[comm[v]] += g.deg[v];
        // internal edge endpoints per community (each internal edge counted twice)
        for (int v = 0; v < n; ++v) {
            int cv = comm[v];
            const int* e = g.nbeg(v); const int* en = g.nend(v);
            for (; e != en; ++e) if (comm[*e] == cv) ls_ein[cv] += 1.0;
        }

        const double m = (double)g.m;
        const double inv_m   = (m > 0) ? 1.0 / m : 0.0;
        const double inv_2m2 = (m > 0) ? 1.0 / (2.0 * m * m) : 0.0;

        ls_queue.clear();
        ls_queue.reserve(n);
        for (int v = 0; v < n; ++v) { ls_queue.push_back(v); ls_inQueue[v] = 1; }

        size_t head = 0;
        long long processed = 0;
        const long long cap = (long long)n * 4 + 16;

        while (head < ls_queue.size() && processed < cap) {
            int v = ls_queue[head++];
            ls_inQueue[v] = 0;
            ++processed;

            int cv = comm[v];
            double kv = g.deg[v];

            ls_touched.clear();
            ++ls_stamp;
            const int* e = g.nbeg(v); const int* en = g.nend(v);
            for (; e != en; ++e) {
                int c = comm[*e];
                if (ls_touchStamp[c] != ls_stamp) {
                    ls_touchStamp[c] = ls_stamp; ls_touched.push_back(c); ls_kiTo[c] = 0.0;
                }
                ls_kiTo[c] += 1.0;
            }
            double ki_in_cur = (ls_touchStamp[cv] == ls_stamp) ? ls_kiTo[cv] : 0.0;

            double tot_cv_wo = ls_tot[cv] - kv;
            double dQ_remove = -ki_in_cur * inv_m + kv * tot_cv_wo * inv_2m2;

            int bestC = cv;
            double bestGain = 0.0;
            double bestKiIn = 0.0;   // ki_in to the chosen target (for ein update)

            for (int c : ls_touched) {
                if (c == cv) continue;
                double dQ_insert = ls_kiTo[c] * inv_m - kv * ls_tot[c] * inv_2m2;
                double gain = dQ_remove + dQ_insert;
                if (gain > bestGain + 1e-12) { bestGain = gain; bestC = c; bestKiIn = ls_kiTo[c]; }
            }
            // isolated-vertex strategy: singleton (ki_in=0)
            if (dQ_remove > bestGain + 1e-12) { bestGain = dQ_remove; bestC = -1; bestKiIn = 0.0; }

            if (bestC != cv) {
                // update ein: remove v from cv, add v to target
                ls_ein[cv] -= 2.0 * ki_in_cur;
                ls_tot[cv] -= kv;
                if (bestC == -1) {
                    int newc = k++;
                    if (newc >= (int)ls_tot.size()) {
                        ls_tot.push_back(0.0); ls_kiTo.push_back(0.0);
                        ls_ein.push_back(0.0); ls_touchStamp.push_back(0);
                    }
                    ls_tot[newc] = 0.0; ls_ein[newc] = 0.0;
                    comm[v] = newc; ls_tot[newc] += kv;   // ein stays 0 (singleton)
                } else {
                    comm[v] = bestC;
                    ls_tot[bestC] += kv;
                    ls_ein[bestC] += 2.0 * bestKiIn;
                }
                const int* e2 = g.nbeg(v); const int* en2 = g.nend(v);
                for (; e2 != en2; ++e2) {
                    int u = *e2;
                    if (!ls_inQueue[u]) { ls_inQueue[u] = 1; ls_queue.push_back(u); }
                }
            }
        }
        for (size_t i = head; i < ls_queue.size(); ++i) ls_inQueue[ls_queue[i]] = 0;

        // Q is invariant under relabeling, so compute it NOW from the
        // incrementally-maintained ls_tot[]/ls_ein[] (indexed by current labels),
        // BEFORE normalize renames them. This avoids any O(n+m) rescan.
        // Active label ids are < k (k may have grown via singletons).
        double q = 0.0;
        for (int c = 0; c < k; ++c) {
            if (ls_tot[c] == 0.0 && ls_ein[c] == 0.0) continue;
            double tc = ls_tot[c] * g.inv2m;
            q += ls_ein[c] * g.inv2m - tc * tc;
        }
        normalizeLabels(comm);   // dense labels for output / next-iter indexing
        return q;
    }

    // ---- Merge community (post-processing) ----
    // Iterate target communities Ca from largest to smallest; for each, try
    // merging trial communities Cb from smallest to largest. Accept if ΔQ>0.
    // ΔQ of merging Cb into Ca:
    //   ΔQ = 2*e(Ca,Cb)/(2m) - 2*tot[Ca]*tot[Cb]/(2m)^2
    //      = e(Ca,Cb)/m - tot[Ca]*tot[Cb]/(2 m^2)
    // where e(Ca,Cb) = number of edges between Ca and Cb.
    void mergeCommunities(vector<int>& comm) {
        int n = g.n;
        int k = normalizeLabels(comm);
        if (k <= 1) return;

        const double m = (double)g.m;
        const double inv_m = (m > 0) ? 1.0 / m : 0.0;
        const double inv_2m2 = (m > 0) ? 1.0 / (2.0 * m * m) : 0.0;

        vector<double> tot(k, 0.0);
        vector<int> size(k, 0);
        for (int v = 0; v < n; ++v) { tot[comm[v]] += g.deg[v]; size[comm[v]]++; }

        // community adjacency: edges between communities, via hash maps.
        // For each community, map<neighborComm, edgeCount>.
        vector<unordered_map<int,double>> cadj(k);
        for (int v = 0; v < n; ++v) {
            int cv = comm[v];
            const int* e = g.nbeg(v); const int* en = g.nend(v);
            for (; e != en; ++e) {
                int cu = comm[*e];
                if (cu != cv) cadj[cv][cu] += 1.0;  // counted both directions over all v
            }
        }
        // Note: cadj[a][b] currently counts each inter-edge once per endpoint
        // scan; since we scan every vertex, edge (x in a, y in b) contributes
        // +1 to cadj[a][b] (from x) and +1 to cadj[b][a] (from y). So
        // cadj[a][b] == cadj[b][a] == true #edges between a,b. Good.

        // DSU over communities to track merges.
        vector<int> parent(k);
        for (int i = 0; i < k; ++i) parent[i] = i;
        function<int(int)> find = [&](int x){ while(parent[x]!=x){ parent[x]=parent[parent[x]]; x=parent[x]; } return x; };

        // order Ca by size descending
        vector<int> order(k);
        iota(order.begin(), order.end(), 0);
        sort(order.begin(), order.end(), [&](int a,int b){ return size[a] > size[b]; });

        vector<char> alive(k, 1);

        for (int ca : order) {
            ca = find(ca);
            if (!alive[ca]) continue;
            bool changed = true;
            while (changed) {
                changed = false;
                // collect current neighbor communities of ca, sorted by size asc
                vector<pair<int,int>> nbrs; // (size, comm)
                for (auto& kv : cadj[ca]) {
                    int cb = find(kv.first);
                    if (cb == ca || !alive[cb]) continue;
                    nbrs.push_back({size[cb], cb});
                }
                sort(nbrs.begin(), nbrs.end());
                for (auto& pr : nbrs) {
                    int cb = find(pr.second);
                    if (cb == ca || !alive[cb]) continue;
                    auto it = cadj[ca].find(cb);
                    double eab = (it != cadj[ca].end()) ? it->second : 0.0;
                    // recompute eab robustly from both maps (after merges)
                    double dQ = eab * inv_m - tot[ca] * tot[cb] * inv_2m2;
                    if (dQ > 1e-12) {
                        // merge cb into ca
                        parent[cb] = ca;
                        alive[cb] = 0;
                        tot[ca] += tot[cb];
                        size[ca] += size[cb];
                        // merge adjacency: fold cb's neighbors into ca
                        for (auto& kv2 : cadj[cb]) {
                            int t = find(kv2.first);
                            if (t == ca) continue;
                            cadj[ca][t] += kv2.second;
                            cadj[t][ca] += kv2.second;  // keep symmetric-ish
                        }
                        cadj[ca].erase(cb);
                        changed = true;
                        break; // restart scan for ca with updated neighbors
                    }
                }
            }
        }
        // relabel by representative
        for (int v = 0; v < n; ++v) comm[v] = find(comm[v]);
        normalizeLabels(comm);
    }

    // ---- Full run ----
    vector<int> run() {
        int n = g.n;
        if (g.m == 0) { vector<int> c(n); iota(c.begin(), c.end(), 0); return c; }

        // initialize population
        vector<Particle> swarm(pop);
        for (auto& p : swarm) initParticle(p);

        vector<int> gbest = swarm[0].pbx;
        double gbfit = swarm[0].pbfit;
        for (auto& p : swarm) if (p.pbfit > gbfit) { gbfit = p.pbfit; gbest = p.pbx; }

        CommunityIndex idxX, idxPb, idxGb;

        for (int t = 0; t < Tmax; ++t) {
            // Freeze gbest for this whole iteration; build its index once.
            int kg = normalizeLabels(gbest);
            idxGb.build(gbest, kg);

            // Track the best discovered THIS iteration; apply after the sweep.
            double iterBestFit = gbfit;
            const vector<int>* iterBestPtr = nullptr;

            for (auto& p : swarm) {
                int kx  = normalizeLabels(p.x);   idxX.build(p.x, kx);
                int kpb = normalizeLabels(p.pbx); idxPb.build(p.pbx, kpb);

                int kx2 = evolve(p, gbest, idxX, idxPb, idxGb);
                // evolve already normalized p.x and returned its k.
                idxX.build(p.x, kx2);
                bool changed = mutate(p, idxX);
                // localSearch returns Q directly (incremental) -> no fitness() pass.
                p.fit = changed ? localSearch(p.x, -1) : localSearch(p.x, kx2);

                if (p.fit > p.pbfit) { p.pbfit = p.fit; p.pbx = p.x; }
                if (p.fit > iterBestFit) { iterBestFit = p.fit; iterBestPtr = &p.x; }
            }
            // Commit the iteration's best into gbest (stable for next round).
            if (iterBestPtr) { gbest = *iterBestPtr; gbfit = iterBestFit; }
        }

        // ---- Merge community on Pg, all Pbp, all Xp ; keep the best ----
        auto tryMerge = [&](vector<int> cand) {
            mergeCommunities(cand);
            double f = fitness(cand);
            if (f > gbfit) { gbfit = f; gbest = cand; }
        };
        tryMerge(gbest);
        for (auto& p : swarm) { tryMerge(p.pbx); tryMerge(p.x); }

        normalizeLabels(gbest);
        return gbest;
    }
};

// --------------------------------------------------------------------------
int main(int argc, char** argv) {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    uint64_t seed = (argc > 1) ? strtoull(argv[1], nullptr, 10) : 12345ULL;
    int pop  = (argc > 2) ? atoi(argv[2]) : 30;
    int Tmax = (argc > 3) ? atoi(argv[3]) : 50;
    int restarts = (argc > 4) ? atoi(argv[4]) : 1;   // independent runs; best kept

    Graph g = readGraph(cin);

    auto t0 = chrono::high_resolution_clock::now();

    vector<int> bestComm;
    double bestQ = -1e18;

#ifdef _OPENMP
    // Independent restarts run in parallel; each has its own NPSO (own buffers).
    #pragma omp parallel
    {
        vector<int> localComm; double localQ = -1e18;
        #pragma omp for schedule(dynamic) nowait
        for (int r = 0; r < restarts; ++r) {
            NPSO solver(g, seed + 0x9E3779B97F4A7C15ULL * (uint64_t)(r + 1), pop, Tmax);
            vector<int> c = solver.run();
            vector<double> tb(g.n, 0.0), eb(g.n, 0.0);
            double q = modularity(g, c, tb, eb);
            if (q > localQ) { localQ = q; localComm = std::move(c); }
        }
        #pragma omp critical
        { if (localQ > bestQ) { bestQ = localQ; bestComm = localComm; } }
    }
#else
    for (int r = 0; r < restarts; ++r) {
        NPSO solver(g, seed + 0x9E3779B97F4A7C15ULL * (uint64_t)(r + 1), pop, Tmax);
        vector<int> c = solver.run();
        vector<double> tb(g.n, 0.0), eb(g.n, 0.0);
        double q = modularity(g, c, tb, eb);
        if (q > bestQ) { bestQ = q; bestComm = std::move(c); }
    }
#endif

    vector<int> comm = std::move(bestComm);
    auto t1 = chrono::high_resolution_clock::now();

    double Q = bestQ;
    int k = normalizeLabels(comm);

    double ms = chrono::duration<double, milli>(t1 - t0).count();

    cerr << "n=" << g.n << " m=" << g.m
         << "  communities=" << k
         << "  Q=" << fixed << setprecision(6) << Q
         << "  restarts=" << restarts
         << "  time=" << setprecision(2) << ms << "ms\n";

    // Output: community label (0-indexed communities) per vertex, 1-indexed vertex.
    cout << Q << "\n";
    // for (int v = 0; v < g.n; ++v) cout << (v + 1) << " " << comm[v] << "\n";
    return 0;
}