#include<bits/stdc++.h>
#include <omp.h>

using namespace std;

#define rep(i,a,b,x)  for(int i=a;i<=b;i+=x)
#define fastIO ios_base::sync_with_stdio(false);cout.tie(NULL);cin.tie(NULL);

random_device rd;   
mt19937 gen(rd());

int N=1;
const double c1=1,c2=1;
double w=1.01;

int T=1;
const double para_disw=1.0/400.0;
int n,m;
vector<vector<int>> E;
vector<vector<int>> P;     
vector<vector<int>> Pb;
vector<int> Pg;
vector<double> Q;
vector<double> Qb;
double Qg=0;

vector<int> trueLabel;

vector<vector<double>> V;
vector<double> k;

vector<vector<long long>> dk;
vector<vector<long long>> lk;

double calI(vector<int> l1,vector<int> l2){
    int s1 = *max_element(l1.begin(), l1.end());
    int s2 = *max_element(l2.begin(), l2.end());
    vector<vector<int>> c1 (s1+1);
    vector<vector<int>> c2(s2+1);

    for (int i=1;i<=n;i++)
        c1[l1[i]].push_back(i),c2[l2[i]].push_back(i);

    double I=0;
    for (int i=1;i<=s1;i++){
        if (c1[i].empty()) continue;
        for (int j=1;j<=s2;j++){
            if (c2[j].empty()) continue;
            
            double Cij=0;
            for (int v:c1[i]) if (l2[v]==j) Cij++;
            if (Cij>0&& c1[i].size() && c2[j].size())
                I+=Cij*log( Cij*double(n)/double(c1[i].size()*c2[j].size()) );
        }
    }

    return I;
}
double calH(vector<int> l){
    int s=*max_element(l.begin(), l.end());
    vector<vector<int>> c(s+1);
    for (int i=1;i<=n;i++)
        c[l[i]].push_back(i);
    double H=0;
    for (int i=1;i<=s;i++){
        if (c[i].size())
            H+=double(c[i].size()*log(double(c[i].size())/double(n)));
    }
    return H;
}
double NMI(vector<int> l1,vector<int> l2){
    return -2.0*calI(l1,l2)/(calH(l1)+calH(l2));
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
        dk[i].resize(n+5,0);
        lk[i].resize(n+5,0);
        caldklk(P[i],dk[i],lk[i]);

        Q[i]=NMI(P[i], trueLabel);

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
    validComms.reserve(n/2);
    
    int S = *max_element(p.begin()+1, p.end()) + 1;
    double currentNMI = NMI(p, trueLabel);
    bool improved = false;
    
    rep(u,1,n,1){
        if (E[u].empty()) continue;
        
        validComms.clear();
        int oldComm = p[u];
        
        // Count edges to each neighboring community
        for (int v : E[u]){
            int vComm = p[v];
            if (commEdgeCount[vComm] == 0 && vComm != oldComm) 
                validComms.push_back(vComm);
            commEdgeCount[vComm]++;
        }

        int bestComm = oldComm;
        double bestNMI = currentNMI;
        
        int oldCommEdges = commEdgeCount[oldComm];
        double ku = k[u];
        
        // Test moving node u to each neighboring community
        for (int comm : validComms){
            p[u] = comm;
            double testNMI = NMI(p, trueLabel);
            
            if (testNMI > bestNMI){
                bestNMI = testNMI;
                bestComm = comm;
            }
            
            p[u] = oldComm; // Restore
        }

        // Test moving node u to a singleton community
        int singleComm = S + 1;
        p[u] = singleComm;
        double testNMI = NMI(p, trueLabel);
        
        if (testNMI > bestNMI){
            bestNMI = testNMI;
            bestComm = singleComm;
            ++S;
        }
        
        p[u] = oldComm; // Restore

        // Clear edge counts
        validComms.push_back(oldComm);
        for (int comm : validComms){
            commEdgeCount[comm] = 0;
        }

        // Apply best move if improvement found
        if (bestComm != oldComm){
            // Update internal edge counts
            int newCommEdges = 0;
            for (int v : E[u]){
                if (p[v] == oldComm && v != u) oldCommEdges--;
                if (p[v] == bestComm) newCommEdges++;
            }
            
            lk[oldComm] -= oldCommEdges;
            lk[bestComm] += newCommEdges;
            dk[oldComm] -= ku;
            dk[bestComm] += ku;
            p[u] = bestComm;
            
            currentNMI = bestNMI;
            improved = true;
        }
    }
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
    // 1. Build adjacency between communities
    // e_ij stores edges between community u and community v
    map<pair<int,int>, int> e_ij; 
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
    
    // 2. Greedy Merging Loop based on NMI
    while (true) {
        double currentNMI = NMI(p, trueLabel);
        double maxNMI = currentNMI;
        int bestCi = -1, bestCj = -1;

        // Iterate through all connected community pairs to find the best merge
        for (auto& [pair_comm, val] : e_ij) {
            int ci = pair_comm.first;
            int cj = pair_comm.second;

            // --- SIMULATE MERGE ---
            // Create a temporary partition to test the NMI
            vector<int> p_test = p;
            for (int u = 1; u <= n; u++) {
                if (p_test[u] == cj) {
                    p_test[u] = ci;
                }
            }

            // Calculate NMI for this potential merge
            double testNMI = NMI(p_test, trueLabel);

            // Check if this merge improves NMI
            if (testNMI > maxNMI + 1e-9) { // Use epsilon for float comparison
                maxNMI = testNMI;
                bestCi = ci;
                bestCj = cj;
            }
        }

        // 3. If no merge improves NMI, break the loop
        if (bestCi == -1) {
            break;
        }

        // 4. COMMIT THE BEST MERGE
        int ci = bestCi;
        int cj = bestCj;

        // Update partition vector p
        for (int u = 1; u <= n; u++) {
            if (p[u] == cj) {
                p[u] = ci;
            }
        }

        // Update dk and lk (Maintained for consistency, though NMI doesn't use them directly)
        int edges_between = e_ij[{min(ci,cj), max(ci,cj)}];
        dk[ci] += dk[cj];
        lk[ci] += lk[cj] + edges_between;
        dk[cj] = 0;
        lk[cj] = 0;
        
        activeCommunities.erase(cj);
        
        // Update e_ij: Move all edges connected to cj over to ci
        vector<tuple<int,int,int>> toAdd; // (other_comm, eij_val, flag)
        
        for (auto it = e_ij.begin(); it != e_ij.end(); ) {
            auto [pair_comm, eij_val] = *it;
            int c1 = pair_comm.first;
            int c2 = pair_comm.second;
            
            if (c1 == cj || c2 == cj) {
                int other = (c1 == cj) ? c2 : c1;
                // If the other community is not the one we merged into (ci)
                if (other != ci) {
                    int new_c1 = min(ci, other);
                    int new_c2 = max(ci, other);
                    
                    // Check if edge already exists between ci and other
                    auto it2 = e_ij.find({new_c1, new_c2});
                    if (it2 != e_ij.end()) {
                        // Mark to update existing edge
                        it2->second += eij_val;
                        // We don't need to add to toAdd list because we updated in place, 
                        // but strictly speaking, we just need to ensure the map is consistent.
                        // The original logic separated this to avoid iterator invalidation issues.
                    } else {
                        // Mark to create new edge
                        toAdd.push_back({other, eij_val, 0}); 
                    }
                }
                // Remove the old edge connected to cj
                it = e_ij.erase(it);
            } else {
                ++it;
            }
        }
        
        // Add the new edges to the map
        for (auto [other, val, flag] : toAdd) {
             int new_c1 = min(ci, other);
             int new_c2 = max(ci, other);
             e_ij[{new_c1, new_c2}] = val;
        }
    }
    
    // Standardize community labels
    standardization(p);
}

void consolidation(vector<int> &l,int l1,int l2){
    for (int i=1;i<=n;i++)
        if (l[i]==l1)
            l[i]=l2;
}

void SecondaryCommunityConsolidation(vector<int> &l){
    map<int,bool> mp;
    map<int,int> cntNode;
    int numC=0;
    for (int i=1;i<=n;i++){
        if (mp.find(l[i])==mp.end()){
            ++numC;
            mp[l[i]]=1;
        }
        cntNode[l[i]]++;
    }

    
    vector<pair<int,int>> decComminities;
    for (auto [x,_]:mp)
        decComminities.push_back({x,cntNode[x]});
    
        sort(decComminities.begin(),decComminities.end(),[](pair<int,int> a,pair<int,int> b){
        return a.second>b.second;
    });

    int i=numC-1;
    vector<int> xtmp;
    while (i>0){
        int j=0;
        bool check=0;
        while (i>j){
            xtmp=l;
            consolidation(l,decComminities[i].first,decComminities[j].first);

            if (NMI(l,trueLabel)>NMI(xtmp,trueLabel)){
                --i;
                check=1;
                break;
            }
            else l=xtmp;
            ++j;
        }

        if (!check) --i;
    }
    
}

void NPSO(){
    initialization();
    // cout<<Qg<<"\n";
    // Initial cache
    rep(p,1,N,1){
        rebuildCommunityMap(Pb[p], cachedCommPb[p]);
    }
    rebuildCommunityMap(Pg, cachedCommPg_global);
    
    // rep(i,1,n,1)
    //     cout<<Pg[i]<<" ";
    // cout<<"\n";
    // cout<<T<<"\n";
    double muProb=0.15; // mutation probability

    double disw=para_disw*double(T);
    int cntStable=0;
    rep(t,1,T,1){
        rep(p,1,N,1){
            uniform_real_distribution<double> dis(0.0,1.0);
            vector<double> r1(n+1), r2(n+1);
            vector<double> diffPb=calSame(P[p],Pb[p]);
            vector<double> diffPg=calSame(P[p],Pg);
            rep(i,1,n,1){
                r1[i]=dis(gen);
                r2[i]=dis(gen);
                // if (V[p][i]>0) w=1-disw;
                // else w=1+disw;
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
            Q[p]=NMI(P[p], trueLabel);

            if (dis(gen)<muProb)
                mutation(P[p],dk[p],lk[p]);
            standardization(P[p]);
            caldklk(P[p],dk[p],lk[p]);
            
            localSearch(P[p],dk[p],lk[p]);
            Q[p]=NMI(P[p], trueLabel);
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
                    cntStable = 0; // reset stable counter on improvement
                }
            }
        }

        ++cntStable;
        if (cntStable>5){
            rep(i,1,N,1){
                SecondaryCommunityConsolidation(P[i]);
                Q[i] = NMI(P[i], trueLabel);

                SecondaryCommunityConsolidation(Pb[i]);
                Qb[i] = NMI(Pb[i], trueLabel);
            }
            SecondaryCommunityConsolidation(Pg);
            Qg = NMI(Pg, trueLabel);
            
            rep(p,1,N,1){
                if (Q[p]>Qb[p]){
                    Pb[p]=P[p];
                    Qb[p]=Q[p];
                    rebuildCommunityMap(Pb[p], cachedCommPb[p]); 
                    
                    if (Qb[p]>Qg){
                        Qg=Qb[p];
                        Pg=Pb[p];
                        rebuildCommunityMap(Pg, cachedCommPg_global);
                        cntStable = 0; // reset stable counter on improvement
                    }
                }
            }
            break;
        }
        // cout<<"Iteration "<<t<<": "<<Qg<<" "<<N<<" "<<V[1][1]<<" "<<V[1][10]<<" "<<V[3][1]<<" "<<V[3][10]<<"\n";
    }

    // build dk, lk for Pb and Pg before final merging 
    vector<vector<long long>> dkPb(N+1, vector<long long>(n+1, 0));
    vector<vector<long long>> lkPb(N+1, vector<long long>(n+1, 0));
    for (int i = 1; i <= N; ++i) {
        // caldklk(Pb[i], dkPb[i], lkPb[i]);
        Qb[i] = NMI(Pb[i], trueLabel);
    }

    // global best dk/lk
    vector<long long> dkPg(n+1, 0), lkPg(n+1, 0);
    // caldklk(Pg, dkPg, lkPg);
    Qg = NMI(Pg, trueLabel);
    int s;
    rep(i,1,N,1){
        SecondaryCommunityConsolidation(P[i]);
        // caldklk(P[i], dk[i], lk[i]);
        Q[i] = NMI(P[i], trueLabel);
        s=*max_element(P[i].begin()+1,P[i].end());
        // cout<<"Final merge individual "<<i<<": "<<Q[i]<<" "<<s<<"\n";

        SecondaryCommunityConsolidation(Pb[i]);
        // caldklk(Pb[i], dkPb[i], lkPb[i]);
        Qb[i] = NMI(Pb[i], trueLabel);
        s=*max_element(Pb[i].begin()+1,Pb[i].end());
        // cout<<"Final merge individual "<<i<<": "<<Qb[i]<<" "<<s<<"\n";
    }

    SecondaryCommunityConsolidation(Pg);
    // caldklk(Pg, dkPg, lkPg);
    Qg = NMI(Pg, trueLabel);
    s=*max_element(Pg.begin()+1,Pg.end());
    // cout<<"Final merge global best: "<<Qg<<" "<<s<<"\n";

    double ans=Qg;
    rep(i,1,N,1){
        ans=max(ans,Q[i]);
        ans=max(ans,Qb[i]);
    }
    cout<<"Final NMI: "<<ans<<"\n";
}

int main(){
    // fastIO
    clock_t tStart = clock();
    
    freopen("c:\\Users\\HP\\Downloads\\synthetic networks-20251125T004928Z-1-001\\synthetic networks\\GN\\GN-0.85\\network.dat","r",stdin);
    // freopen("output.txt","w",stdout);

    cin>>n>>m;


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
        u++; v++;
        E[u].push_back(v);
        E[v].push_back(u);
        k[u]++,k[v]++;
    }

    {
    std::string path = "c:\\Users\\HP\\Downloads\\synthetic networks-20251125T004928Z-1-001\\synthetic networks\\GN\\GN-0.85\\community.dat";
    std::ifstream fin(path);
    if (!fin.is_open()){
        perror(path.c_str());
        exit(1);
    }

    // ensure size and direct indexing
    trueLabel.assign(n+1, 0);

    // Two common formats:
    // 1) lines: "<node> <label>"
    for (int i = 0; i < n; ++i) {
        int node, label;
        if (!(fin >> node >> label)) {
            std::cerr << "Read error or EOF at line " << i+1 << "\n";
            break;
        }

        trueLabel[node+1] = label+1; // keep your +1 if desired
        // cout<<node+1<<":"<<trueLabel[node+1]<<"\n";
    }
    fin.close();
    }


    // cout << "True labels: ";
    // for (int i = 1; i <= n; i++) {
    //     cout << i<<":"<<trueLabel[i] << " \n";
    // }
    // cout << "\n";


    NPSO();
        
    // printf("\nTime taken: %.2fs\n", (double)(clock() - tStart)/CLOCKS_PER_SEC);
}