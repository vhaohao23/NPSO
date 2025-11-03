#include<bits/stdc++.h>
using namespace std;

#define rep(i,a,b,x)  for(int i=a;i<=b;i+=x)
#define fastIO ios_base::sync_with_stdio(false);cout.tie(NULL);cin.tie(NULL);

random_device rd;   
mt19937 gen(rd());

int N=10;
const double c1=1,c2=1;
double w=1.01;

int T=10;
const double para_disw=1.0/400.0;
int n,m;
vector<vector<int>> E;
vector<vector<int>> P;     
vector<vector<int>> Pb;
vector<int> Pg;
vector<double> Q;
vector<double> Qb;
double Qg=0;

vector<vector<double>> V;
vector<double> k;

vector<vector<long long>> dk;
vector<vector<long long>> lk;



double modularity(vector<long long>& dk, vector<long long>& lk){
    double Q = 0.0;
    double m_double = static_cast<double>(m);  // m cũng nên là long long
    double two_m = 2.0 * m_double;
    
    for (int i = 1; i <= n; i++){
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
    dk.assign(n+1,0); lk.assign(n+1,0);

    for (int u=1;u<=n;u++){
        dk[p[u]]+=k[u];
         
        for (int v:E[u])
            if (p[u]==p[v]&&u<v){
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


unordered_map<long long, int> cntIntersection;

vector<double> calSame(const vector<int>& p1, const vector<int>& p2){
    static vector<int> cnt1, cnt2;
    static vector<long long> keys;
    
    cnt1.assign(n+1, 0);
    cnt2.assign(n+1, 0);
    keys.resize(n+1);
    
    cntIntersection.clear();

    rep(i,1,n,1){
        cnt1[p1[i]]++; 
        cnt2[p2[i]]++;
        keys[i] = ((long long)p1[i] << 32) | (unsigned long long)p2[i];// hash pair of label
        cntIntersection[keys[i]]++;
    }

    static vector<double> res;
    res.assign(n+1, 0);
    
    rep(i,1,n,1){
        int intersection = cntIntersection[keys[i]]; 
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
bool needRebuildPg = true;

void rebuildCommunityMap(const vector<int>& partition, unordered_map<int, vector<int>>& res){
    res.clear();
    rep(i,1,n,1){
        res[partition[i]].push_back(i);
    }
}

void localSearch(vector<int>& p, vector<long long>& dk, vector<long long>& lk){
    static vector<int> commEdgeCount(2*n+1, 0);
    static vector<int> validComms;
    validComms.reserve(n/2); // Reserve reasonable size
    
    double inv_4m2 = 1.0 / (4.0 * double(m) * double(m));
    double inv_m = 1.0 / double(m);
    int S= *max_element(p.begin()+1,p.end())+1;
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
        double ku = k[u];
        double dk_old = dk[oldComm];//sum egree of u's old community before moving 
        
        for (int comm : validComms){
            int newCommEdges = commEdgeCount[comm];
            double deltal1 = -oldCommEdges;
            double deltal2 = newCommEdges;
            
            double dk_old_new = dk_old - ku;//sum degree of u's old community after moving
            double dk_new_old = dk[comm];//sum degree of u's new community before moving
            double dk_new_new = dk_new_old + ku;//sum degree of u's new community after moving
            
            double deltaQ = (deltal1 + deltal2) * inv_m
                - (dk_old_new * dk_old_new - dk_old * dk_old) * inv_4m2
                - (dk_new_new * dk_new_new - dk_new_old * dk_new_old) * inv_4m2;

            if (deltaQ > bestDeltaQ){
                bestDeltaQ = deltaQ;
                bestDeltas = {deltal1, deltal2, -ku, ku};
                bestComm = comm;
            }
        }

        int singleComm=S+1;
        double dk_new=dk_old - ku;
        double deltal1=-oldCommEdges;
        double deltal2=0;
        double deltaQ = (deltal1 + deltal2) * inv_m
            - (dk_new * dk_new - dk_old * dk_old) * inv_4m2
            - (ku * ku) * inv_4m2;
        if (deltaQ > bestDeltaQ){
            bestDeltaQ = deltaQ;
            bestDeltas = {deltal1, deltal2, -ku, ku};
            bestComm = singleComm;
            ++S;
        }



        // Clear
        validComms.push_back(oldComm);
        for (int comm : validComms){
            commEdgeCount[comm] = 0;
        }

        if (bestComm != oldComm){
            lk[oldComm] += bestDeltas[0];
            lk[bestComm] += bestDeltas[1];
            dk[oldComm] += bestDeltas[2];
            dk[bestComm] += bestDeltas[3];
            p[u] = bestComm;
        }
    }
}

void caculateIter(){
    if (n+m<=1000) {T=100,N=100;return;}
    else if (n+m>=1000000) {T=10,N=10;return;}
    
    double log_ratio = (double(log10(n+m)) - 3.0) / 3.0;  // 3.0 = log10(1000), 3.0 = log10(1e6) - log10(1000)
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
        double nodeMuProb=0.5; // probability of mutating each node in the same community
        uniform_real_distribution<double> disProb(0.0,1.0);
        for (int i=1;i<=n;i++)
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


void mergeCommunities(vector<int>& p, vector<long long>& dk, vector<long long>& lk){
    double inv_2m = 1.0 / (2.0 * double(m));
    double inv_4m2 = 1.0 / (4.0 * double(m) * double(m));
    
    // Build adjacency between communities
    map<pair<int,int>, int> e_ij; // edges between different communities
    set<int> activeCommunities;
    
    for (int u = 1; u <= n; u++) {
        activeCommunities.insert(p[u]);
        for (int v : E[u]) {
            if (u < v && p[u] != p[v]) {
                int ci = p[u], cj = p[v];
                if (ci > cj) swap(ci, cj);
                e_ij[{ci, cj}]++;
            }
        }
    }
    
    // Priority queue for best merges
    priority_queue<tuple<double, int, int>> pq; // (deltaQ, c1, c2)
    
    // Calculate initial deltaQ for all community pairs
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
    
    // Greedy merging
    while (!pq.empty()) {
        auto [deltaQ, ci, cj] = pq.top();
        pq.pop();
        
        // Check if communities still exist
        if (activeCommunities.find(ci) == activeCommunities.end() || 
            activeCommunities.find(cj) == activeCommunities.end()) {
            continue;
        }
        
        // Check if this merge is still valid (deltaQ might be outdated)
        auto it = e_ij.find({min(ci,cj), max(ci,cj)});
        if (it == e_ij.end()) continue;
        
        int eij = it->second;
        double eij_norm = double(eij) * inv_2m;
        double ai = double(dk[ci]) * inv_2m;
        double aj = double(dk[cj]) * inv_2m;
        double current_deltaQ = 2.0 * (eij_norm - ai * aj);
        
        // If deltaQ changed significantly, skip (outdated)
        if (abs(current_deltaQ - deltaQ) > 1e-9 || current_deltaQ <= 0) {
            continue;
        }
        
        // Perform merge: merge cj into ci
        for (int u = 1; u <= n; u++) {
            if (p[u] == cj) {
                p[u] = ci;
            }
        }
        
        // Update dk and lk
        dk[ci] += dk[cj];
        lk[ci] += lk[cj] + eij;
        dk[cj] = 0;
        lk[cj] = 0;
        
        activeCommunities.erase(cj);
        
        // Update e_ij: merge all edges from cj to ci
        vector<pair<int,int>> toRemove;
        vector<tuple<int,int,int>> toAdd; // (other_comm, ci, new_eij)
        
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
                        toAdd.push_back({other, it2->second, 1}); // flag=1: update
                    } else {
                        toAdd.push_back({other, eij_val, 0}); // flag=0: new
                    }
                }
                it = e_ij.erase(it);
            } else {
                ++it;
            }
        }
        
        // Add new pairs and recalculate deltaQ
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
    
    // Standardize community labels
    standardization(p);
}

void NPSO(){
    initialization();
    cout<<Qg<<"\n";
    // Initial cache
    rep(p,1,N,1){
        rebuildCommunityMap(Pb[p], cachedCommPb[p]);
    }
    rebuildCommunityMap(Pg, cachedCommPg_global);
    
    // rep(i,1,n,1)
    //     cout<<Pg[i]<<" ";
    cout<<"\n";
    cout<<T<<"\n";
    double muProb=0.15; // mutation probability

    double disw=para_disw*double(T);

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

            // make the change decision
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
                            community = &cachedCommPb[p][Pb[p][i]];// go to Pbest
                        }else{
                            community = &cachedCommPg_global[Pg[i]]; // go to Gbest
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

        // update personal best and global best
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


        cout<<"Iteration "<<t<<": "<<Qg<<" "<<N<<" "<<V[1][1]<<" "<<V[1][10]<<" "<<V[3][1]<<" "<<V[3][10]<<"\n";
    }

    // build dk, lk for Pb and Pg before final merging 
    vector<vector<long long>> dkPb(N+1, vector<long long>(n+1, 0));
    vector<vector<long long>> lkPb(N+1, vector<long long>(n+1, 0));
    for (int i = 1; i <= N; ++i) {
        caldklk(Pb[i], dkPb[i], lkPb[i]);
        Qb[i] = modularity(dkPb[i], lkPb[i]);
    }

    // global best dk/lk
    vector<long long> dkPg(n+1, 0), lkPg(n+1, 0);
    caldklk(Pg, dkPg, lkPg);
    Qg = modularity(dkPg, lkPg);
    
    rep(i,1,N,1){
        mergeCommunities(P[i], dk[i], lk[i]);
        caldklk(P[i], dk[i], lk[i]);
        Q[i] = modularity(dk[i], lk[i]);
        cout<<"Final merge individual "<<i<<": "<<Q[i]<<"\n";

        mergeCommunities(Pb[i], dkPb[i], lkPb[i]);
        caldklk(Pb[i], dkPb[i], lkPb[i]);
        Qb[i] = modularity(dkPb[i], lkPb[i]);
        cout<<"Final merge individual "<<i<<": "<<Qb[i]<<"\n";
    }

    mergeCommunities(Pg, dkPg, lkPg);
    caldklk(Pg, dkPg, lkPg);
    Qg = modularity(dkPg, lkPg);
    cout<<"Final merge global best: "<<Qg<<"\n";

    double ans=0;
    rep(i,1,N,1){
        ans=max(ans,Q[i]);
        ans=max(ans,Qb[i]);
    }
    ans=max(ans,Qg);

    cout<<"modularity best:"<<ans<<"\n";
}

int main(){
    // fastIO
    clock_t tStart = clock();
    
    freopen("/home/vhaohao/hao/nckh/dataset-community/amazon.txt","r",stdin);
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


    int u,v;
    rep(i,1,m,1){
        cin>>u>>v;
        E[u].push_back(v);
        E[v].push_back(u);
        k[u]++,k[v]++;
    }

    NPSO();
        
    printf("\nTime taken: %.2fs\n", (double)(clock() - tStart)/CLOCKS_PER_SEC);
}