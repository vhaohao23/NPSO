#include<bits/stdc++.h>
using namespace std;

#define rep(i,a,b,x)  for(long long i=a;i<=b;i+=x)
#define fastIO ios_base::sync_with_stdio(false);cout.tie(NULL);cin.tie(NULL);

random_device rd;   
mt19937 gen;

int N=10;
const double c1=1,c2=1;
double w=1.01;

int T=10;
const double para_disw=1.0/400.0;
long long n,m;
vector<vector<int>> E;
vector<vector<int>> P;     
vector<vector<int>> Pb;
vector<int> Pg;
vector<double> Q;
vector<double> Qb;
double Qg=0;

vector<vector<double>> V;
vector<long long> k;

vector<vector<long long>> dk;
vector<vector<long long>> lk;

// Seed control for reproducibility
void setSeed(unsigned int seed){
    gen.seed(seed);
}

double modularity(vector<long long>& dk, vector<long long>& lk){
    double Q = 0.0;
    double m_double = static_cast<double>(m);
    double two_m = 2.0 * m_double;
    
    for (long long i = 1; i <= n; i++){
        double term1 = static_cast<double>(lk[i]) / m_double;
        double dk_norm = static_cast<double>(dk[i]) / two_m;
        Q += term1 - dk_norm * dk_norm;
    }
    
    return Q;
}

void LAR_rand(vector<vector<int>> &a){
    rep(u,1,n,1){
        if (!E[u].size()) continue;
        uniform_int_distribution<int> disv(0,E[u].size()-1);
        int v=E[u][disv(gen)];
        a[u].push_back(v);
        a[v].push_back(u);
    }
}

vector<int> decoding(vector<vector<int>>& a){
    bool dd[n+1]={};
    static vector<int> q; 
    
    vector<int> l(n+1);
    int cnt=0;

    rep(i,1,n,1)
        if (!dd[i]){
            ++cnt;
            q.clear();
            q.reserve(n); 
            
            int head = 0;
            q.push_back(i);
            dd[i] = true;
            
            while (head < q.size()){
                int u = q[head++];
                l[u] = cnt;
                
                const auto& neighbors = a[u];
                for (int v : neighbors)
                    if (!dd[v]){
                        dd[v] = true;
                        q.push_back(v);
                    }
            }
        }
    return l;
}

void caldklk(vector<int> &p,vector<long long> &dk,vector<long long> &lk){
    dk.assign(n+1,0); 
    lk.assign(n+1,0);

    for (long long u=1;u<=n;u++){
        dk[p[u]] += k[u];
         
        for (int v:E[u])
            if (p[u]==p[v] && u<v){
                ++lk[p[u]];
            }
    }
}

void initialization(){
    rep(i,1,N,1){
        vector<vector<int>> a(n+1);
        LAR_rand(a);
        P[i]=decoding(a);
        dk[i].resize(n+1,0);
        lk[i].resize(n+1,0);
        caldklk(P[i],dk[i],lk[i]);

        Q[i]=modularity(dk[i],lk[i]);

        Pb[i]=P[i];
        Qb[i]=Q[i];
        if (Qb[i]>Qg){
            Qg=Qb[i];
            Pg=Pb[i];
        }
    } 
}

map<pair<int,int>, int> cntIntersection;

vector<double> calSame(const vector<int>& p1, const vector<int>& p2){
    static vector<int> cnt1, cnt2;
    
    cnt1.assign(n+1, 0);
    cnt2.assign(n+1, 0);
    cntIntersection.clear();

    rep(i,1,n,1){
        cnt1[p1[i]]++; 
        cnt2[p2[i]]++;
        cntIntersection[{p1[i], p2[i]}]++;
    }

    static vector<double> res;
    res.assign(n+1, 0);
    
    rep(i,1,n,1){
        int intersection = cntIntersection[{p1[i], p2[i]}];
        res[i] = double(intersection) / 
                 double(cnt1[p1[i]] + cnt2[p2[i]] - intersection);
    }

    return res;
}

void standardization(vector<int> &p){
    unordered_map<int,int> mp;
    int cnt=0;
    rep(i,1,n,1)
        if (!mp[p[i]])
            mp[p[i]]=++cnt;
    rep(i,1,n,1)
        p[i]=mp[p[i]];
}

vector<unordered_map<int, vector<int>>> cachedCommPb;
unordered_map<int, vector<int>> cachedCommPg_global;

void rebuildCommunityMap(const vector<int>& partition, unordered_map<int, vector<int>>& res){
    res.clear();
    rep(i,1,n,1){
        res[partition[i]].push_back(i);
    }
}

void localSearch(vector<int>& p, vector<long long>& dk, vector<long long>& lk){
    static vector<int> commEdgeCount(n+1, 0);
    static vector<int> validComms;
    validComms.reserve(n/2);
    
    double inv_4m2 = 1.0 / (4.0 * double(m) * double(m));
    double inv_m = 1.0 / double(m);

    rep(u,1,n,1){
        if (E[u].empty()) continue;
        
        validComms.clear();
        int oldComm = p[u];
        
        for (int v : E[u]){
            int vComm = p[v];
            if (commEdgeCount[vComm] == 0 && vComm != oldComm) 
                validComms.push_back(vComm);
            commEdgeCount[vComm]++;
        }

        int bestComm = oldComm;
        double bestDeltaQ = 0.0;
        vector<double> bestDeltas(4, 0.0);
        
        int oldCommEdges = commEdgeCount[oldComm];
        double ku = double(k[u]);
        double dk_old = double(dk[oldComm]);
        
        for (int comm : validComms){
            int newCommEdges = commEdgeCount[comm];
            double deltal1 = -oldCommEdges;
            double deltal2 = newCommEdges;
            
            double dk_old_new = dk_old - ku;
            double dk_new_old = double(dk[comm]);
            double dk_new_new = dk_new_old + ku;
            
            double deltaQ = (deltal1 + deltal2) * inv_m
                - (dk_old_new * dk_old_new - dk_old * dk_old) * inv_4m2
                - (dk_new_new * dk_new_new - dk_new_old * dk_new_old) * inv_4m2;

            if (deltaQ > bestDeltaQ){
                bestDeltaQ = deltaQ;
                bestDeltas = {deltal1, deltal2, -ku, ku};
                bestComm = comm;
            }
        }

        validComms.push_back(oldComm);
        for (int comm : validComms){
            commEdgeCount[comm] = 0;
        }

        if (bestComm != oldComm){
            lk[oldComm] += (long long)bestDeltas[0];
            lk[bestComm] += (long long)bestDeltas[1];
            dk[oldComm] += (long long)bestDeltas[2];
            dk[bestComm] += (long long)bestDeltas[3];
            p[u] = bestComm;
        }
    }
}

void caculateIter(){
    if (n+m<=1000) {T=100,N=100;return;}
    else if (n+m>=1000000) {T=10,N=10;return;}
    
    double log_ratio = (double(log10(n+m)) - 3.0) / 3.0;
    T = (int)(100 - 90 * log_ratio);
    N = (int)(100 - 90 * log_ratio);
}

void mutation(vector<int>& p, vector<long long>& dk, vector<long long>& lk){
    uniform_int_distribution<int> disn(1,n);
    int u=disn(gen);
    
    uniform_real_distribution<double> disType(0.0,1.0);
    double type=disType(gen);

    int S= *max_element(p.begin()+1,p.end());
    ++S;

    if (type<0.5){
        double nodeMuProb=0.5;
        uniform_real_distribution<double> disProb(0.0,1.0);
        for (long long i=1;i<=n;i++)
            if (p[i]==p[u]){
                double randProb=disProb(gen);
                if (randProb<nodeMuProb){
                    p[i]=S;
                }
            }
    }
    else {
        p[u]=S;
        for (int v:E[u]){
            if (p[v]==p[u]){
                p[v]=S;
            }
        }
    }
}

// ============ NEW: REFINEMENT PHASE ============
void refinement(vector<int>& p, vector<long long>& dk, vector<long long>& lk){
    vector<int> new_p = p;
    int max_label = *max_element(p.begin()+1, p.end());
    
    rep(comm, 1, max_label, 1){
        vector<int> nodes_in_comm;
        rep(i, 1, n, 1){
            if (p[i] == comm){
                nodes_in_comm.push_back(i);
            }
        }
        
        if (nodes_in_comm.empty()) continue;
        
        unordered_set<int> visited;
        int subcomm_label = comm;
        
        for (int start : nodes_in_comm){
            if (visited.count(start)) continue;
            
            queue<int> q;
            q.push(start);
            visited.insert(start);
            
            vector<int> component;
            component.push_back(start);
            
            while (!q.empty()){
                int u = q.front();
                q.pop();
                
                for (int v : E[u]){
                    if (p[v] == comm && !visited.count(v)){
                        visited.insert(v);
                        q.push(v);
                        component.push_back(v);
                    }
                }
            }
            
            if (subcomm_label != comm){
                for (int node : component){
                    new_p[node] = subcomm_label;
                }
            }
            
            subcomm_label = ++max_label;
        }
    }
    
    p = new_p;
    standardization(p);
    caldklk(p, dk, lk);
}

// ============ NEW: SINGLETON OPTIMIZATION ============
void singletonOptimization(vector<int>& p, vector<long long>& dk, vector<long long>& lk){
    unordered_map<int, int> comm_size;
    rep(i, 1, n, 1){
        comm_size[p[i]]++;
    }
    
    vector<int> singletons;
    rep(i, 1, n, 1){
        if (comm_size[p[i]] == 1){
            singletons.push_back(i);
        }
    }
    
    double inv_4m2 = 1.0 / (4.0 * double(m) * double(m));
    double inv_m = 1.0 / double(m);
    
    for (int u : singletons){
        if (E[u].empty()) continue;
        
        int oldComm = p[u];
        int bestComm = oldComm;
        double bestDeltaQ = 0.0;
        
        unordered_map<int, int> neighbor_comms;
        for (int v : E[u]){
            if (p[v] != oldComm){
                neighbor_comms[p[v]]++;
            }
        }
        
        double ku = double(k[u]);
        double dk_old = double(dk[oldComm]);
        
        for (auto& [comm, edges] : neighbor_comms){
            double deltal1 = 0;
            double deltal2 = edges;
            
            double dk_old_new = dk_old - ku;
            double dk_new_old = double(dk[comm]);
            double dk_new_new = dk_new_old + ku;
            
            double deltaQ = (deltal1 + deltal2) * inv_m
                - (dk_old_new * dk_old_new - dk_old * dk_old) * inv_4m2
                - (dk_new_new * dk_new_new - dk_new_old * dk_new_old) * inv_4m2;
            
            if (deltaQ > bestDeltaQ){
                bestDeltaQ = deltaQ;
                bestComm = comm;
            }
        }
        
        if (bestComm != oldComm && bestDeltaQ > 0){
            dk[oldComm] -= ku;
            lk[oldComm] = 0;
            dk[bestComm] += ku;
            
            int edges_to_new = neighbor_comms[bestComm];
            lk[bestComm] += edges_to_new;
            
            p[u] = bestComm;
        }
    }
    
    standardization(p);
    caldklk(p, dk, lk);
}

void mergeCommunities(vector<int>& p, vector<long long>& dk, vector<long long>& lk){
    double inv_2m = 1.0 / (2.0 * double(m));
    double inv_4m2 = 1.0 / (4.0 * double(m) * double(m));
    
    map<pair<int,int>, long long> e_ij;
    set<int> activeCommunities;
    
    for (long long u = 1; u <= n; u++) {
        activeCommunities.insert(p[u]);
        for (int v : E[u]) {
            if (u < v && p[u] != p[v]) {
                int ci = p[u], cj = p[v];
                if (ci > cj) swap(ci, cj);
                e_ij[{ci, cj}]++;
            }
        }
    }
    
    priority_queue<tuple<double, int, int>> pq;
    
    for (auto& [pair_comm, eij] : e_ij) {
        int ci = pair_comm.first;
        int cj = pair_comm.second;
        
        double eij_norm = double(eij) * inv_2m;
        double ai = double(dk[ci]) * inv_2m;
        double aj = double(dk[cj]) * inv_2m;
        
        double deltaQ = 2.0 * (eij_norm - ai * aj);
        
        if (deltaQ > 0) {
            pq.push({deltaQ, ci, cj});
        }
    }
    
    while (!pq.empty()) {
        auto [deltaQ, ci, cj] = pq.top();
        pq.pop();
        
        if (activeCommunities.find(ci) == activeCommunities.end() || 
            activeCommunities.find(cj) == activeCommunities.end()) {
            continue;
        }
        
        auto it = e_ij.find({min(ci,cj), max(ci,cj)});
        if (it == e_ij.end()) continue;
        
        long long eij = it->second;
        double eij_norm = double(eij) * inv_2m;
        double ai = double(dk[ci]) * inv_2m;
        double aj = double(dk[cj]) * inv_2m;
        double current_deltaQ = 2.0 * (eij_norm - ai * aj);
        
        if (abs(current_deltaQ - deltaQ) > 1e-9 || current_deltaQ <= 0) {
            continue;
        }
        
        for (long long u = 1; u <= n; u++) {
            if (p[u] == cj) {
                p[u] = ci;
            }
        }
        
        dk[ci] += dk[cj];
        lk[ci] += lk[cj] + eij;
        dk[cj] = 0;
        lk[cj] = 0;
        
        activeCommunities.erase(cj);
        
        vector<tuple<int,long long,int>> toAdd;
        
        for (auto it = e_ij.begin(); it != e_ij.end(); ) {
            auto [pair_comm, eij_val] = *it;
            int c1 = pair_comm.first;
            int c2 = pair_comm.second;
            
            if (c1 == cj || c2 == cj) {
                int other = (c1 == cj) ? c2 : c1;
                if (other != ci) {
                    int new_c1 = min(ci, other);
                    int new_c2 = max(ci, other);
                    
                    auto it2 = e_ij.find({new_c1, new_c2});
                    if (it2 != e_ij.end()) {
                        it2->second += eij_val;
                        toAdd.push_back({other, it2->second, 1});
                    } else {
                        toAdd.push_back({other, eij_val, 0});
                    }
                }
                it = e_ij.erase(it);
            } else {
                ++it;
            }
        }
        
        for (auto [other, new_eij, flag] : toAdd) {
            if (flag == 0) {
                int new_c1 = min(ci, other);
                int new_c2 = max(ci, other);
                e_ij[{new_c1, new_c2}] = new_eij;
            }
            
            double eij_new = double(new_eij) * inv_2m;
            double ai_new = double(dk[ci]) * inv_2m;
            double ao = double(dk[other]) * inv_2m;
            
            double new_deltaQ = 2.0 * (eij_new - ai_new * ao);
            
            if (new_deltaQ > 0) {
                pq.push({new_deltaQ, min(ci, other), max(ci, other)});
            }
        }
    }
    
    standardization(p);
}

void NPSO(){
    initialization();
    cout<<"Initial Qg: "<<Qg<<"\n";
    
    rep(p,1,N,1){
        rebuildCommunityMap(Pb[p], cachedCommPb[p]);
    }
    rebuildCommunityMap(Pg, cachedCommPg_global);
    
    cout<<"Iterations: "<<T<<"\n";
    cout<<"Population: "<<N<<"\n\n";
    
    double muProb=0.15;
    double disw=para_disw*double(T);
    
    // ============ NEW: EARLY STOPPING ============
    double prev_Qg = -1.0;
    int no_improve_count = 0;
    const int MAX_NO_IMPROVE = 5;
    const double MIN_IMPROVEMENT = 1e-6;

    rep(t,1,T,1){
        rep(p,1,N,1){
            uniform_real_distribution<double> dis(0.0,1.0);
            vector<double> r1(n+1), r2(n+1);
            vector<double> diffPb=calSame(P[p],Pb[p]);
            vector<double> diffPg=calSame(P[p],Pg);
            rep(i,1,n,1){
                r1[i]=dis(gen);
                r2[i]=dis(gen);
                if (V[p][i]>0) w=1-disw;
                else w=1+disw;
                V[p][i]=w*V[p][i]+c1*r1[i]*diffPb[i]+c2*r2[i]*diffPg[i];
            }
            vector<bool> dd(n+1,0);

            int s = *max_element(P[p].begin() + 1, P[p].end());
            rep(i,1,n,1)
                if (!dd[i]){
                    double prob=1.0/(1.0+exp(-V[p][i]));
                    double randProb=dis(gen);
                    if (randProb<prob){
                        double sumr1r2=r1[i]+r2[i];
                        uniform_real_distribution<double> disp(0.0,sumr1r2);
                        double randp=disp(gen);

                        vector<int>* community;
                        if (randp<r1[i]){
                            community = &cachedCommPb[p][Pb[p][i]];
                        }else{
                            community = &cachedCommPg_global[Pg[i]];
                        }
                        ++s;
                        for (int j : *community){
                            if (!dd[j]){
                                P[p][j]=s;
                                dd[j] = true;
                            }
                        }
                    }
                }

            standardization(P[p]);
            caldklk(P[p],dk[p],lk[p]);
            Q[p]=modularity(dk[p],lk[p]);

            if (dis(gen)<muProb)
                mutation(P[p],dk[p],lk[p]);
            standardization(P[p]);
            caldklk(P[p],dk[p],lk[p]);
            
            localSearch(P[p],dk[p],lk[p]);
            Q[p]=modularity(dk[p],lk[p]);
        }

        rep(p,1,N,1){
            if (Q[p]>Qb[p]){
                Pb[p]=P[p];
                Qb[p]=Q[p];
                rebuildCommunityMap(Pb[p], cachedCommPb[p]); 
                
                if (Qb[p]>Qg){
                    Qg=Qb[p];
                    Pg=Pb[p];
                    rebuildCommunityMap(Pg, cachedCommPg_global);
                }
            }
        }

        // ============ NEW: EARLY STOPPING CHECK ============
        if (abs(Qg - prev_Qg) < MIN_IMPROVEMENT){
            no_improve_count++;
            if (no_improve_count >= MAX_NO_IMPROVE){
                cout << "Early stopping at iteration " << t << " (no improvement)\n\n";
                break;
            }
        } else {
            no_improve_count = 0;
        }
        prev_Qg = Qg;

        cout<<"Iteration "<<t<<": Q="<<Qg<<"\n";
    }

    cout<<"\n=== FINAL OPTIMIZATION PHASE ===\n";
    
    vector<vector<long long>> dkPb(N+1, vector<long long>(n+1, 0));
    vector<vector<long long>> lkPb(N+1, vector<long long>(n+1, 0));
    for (int i = 1; i <= N; ++i) {
        caldklk(Pb[i], dkPb[i], lkPb[i]);
        Qb[i] = modularity(dkPb[i], lkPb[i]);
    }

    vector<long long> dkPg(n+1, 0), lkPg(n+1, 0);
    caldklk(Pg, dkPg, lkPg);
    Qg = modularity(dkPg, lkPg);
    
    rep(i,1,N,1){
        // Full optimization pipeline
        mergeCommunities(P[i], dk[i], lk[i]);
        refinement(P[i], dk[i], lk[i]);  // NEW
        singletonOptimization(P[i], dk[i], lk[i]);  // NEW
        localSearch(P[i], dk[i], lk[i]);
        caldklk(P[i], dk[i], lk[i]);
        Q[i] = modularity(dk[i], lk[i]);
        cout<<"Individual "<<i<<": "<<Q[i]<<"\n";

        mergeCommunities(Pb[i], dkPb[i], lkPb[i]);
        refinement(Pb[i], dkPb[i], lkPb[i]);  // NEW
        singletonOptimization(Pb[i], dkPb[i], lkPb[i]);  // NEW
        localSearch(Pb[i], dkPb[i], lkPb[i]);
        caldklk(Pb[i], dkPb[i], lkPb[i]);
        Qb[i] = modularity(dkPb[i], lkPb[i]);
        cout<<"Pbest "<<i<<": "<<Qb[i]<<"\n";
    }

    mergeCommunities(Pg, dkPg, lkPg);
    refinement(Pg, dkPg, lkPg);  // NEW
    singletonOptimization(Pg, dkPg, lkPg);  // NEW
    localSearch(Pg, dkPg, lkPg);
    caldklk(Pg, dkPg, lkPg);
    Qg = modularity(dkPg, lkPg);
    cout<<"Gbest: "<<Qg<<"\n\n";

    double ans=0;
    rep(i,1,N,1){
        ans=max(ans,Q[i]);
        ans=max(ans,Qb[i]);
    }
    ans=max(ans,Qg);

    cout<<"=== FINAL RESULT ===\n";
    cout<<"Best modularity: "<<ans<<"\n";
    
    // Find which partition achieved best result
    if (ans == Qg) cout<<"Achieved by: Global best (Pg)\n";
    else {
        rep(i,1,N,1){
            if (ans == Qb[i]) {
                cout<<"Achieved by: Pbest["<<i<<"]\n";
                break;
            }
            if (ans == Q[i]) {
                cout<<"Achieved by: Individual["<<i<<"]\n";
                break;
            }
        }
    }
}

int main(){
    clock_t tStart = clock();
    
    freopen("input.txt","r",stdin);
    // freopen("output.txt","w",stdout);

    cin>>n>>m;

    caculateIter();

    E.resize(n+1);
    k.resize(n+1,0);  
    V.resize(N+1,vector<double>(n+1,-1));
    P.resize(N+1);
    Pb.resize(N+1);
    Q.resize(N+1,0);
    Qb.resize(N+1,0);
    dk.resize(N+1);
    lk.resize(N+1);
    cachedCommPb.resize(N+1);

    // ============ NEW: SEED CONTROL ============
    // Uncomment next line for reproducible results
    // setSeed(42);
    setSeed(rd());  // Random seed

    int u,v;
    rep(i,1,m,1){
        cin>>u>>v;
        E[u].push_back(v);
        E[v].push_back(u);
        k[u]++,k[v]++;
    }

    cout<<"=== NPSO COMMUNITY DETECTION ===\n";
    cout<<"Graph: n="<<n<<", m="<<m<<"\n\n";

    NPSO();
        
    printf("\nTime taken: %.2fs\n", (double)(clock() - tStart)/CLOCKS_PER_SEC);
    return 0;
}