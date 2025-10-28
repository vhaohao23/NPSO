#include<bits/stdc++.h>
using namespace std;

#define rep(i,a,b,x)  for(int i=a;i<=b;i+=x)
#define fastIO ios_base::sync_with_stdio(false);cout.tie(NULL);cin.tie(NULL);

random_device rd;   
mt19937 gen(rd());

int N;
const double c1=1,c2=1;
const double w=1.01;

int T;

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

vector<vector<int>> dk;
vector<vector<int>> lk;



double modularity(vector<int> dk,vector<int> lk){
    double Q=0;

    for (int i=1;i<=n;i++){
        Q+=double(lk[i])/double(m)-pow(double(dk[i])/double(2*m),2.0);
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

void caldklk(vector<int> &p,vector<int> &dk,vector<int> &lk){
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

vector<double> calDiff(const vector<int>& p1, const vector<int>& p2){
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

void localSearch(vector<int>& p, vector<int>& dk, vector<int>& lk){
    static vector<int> commEdgeCount(n+1, 0);
    static vector<int> validComms;
    validComms.reserve(n/2); // Reserve reasonable size
    
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

void mutation(vector<int>& p, vector<int>& dk, vector<int>& lk){
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

// void EPD(){
//     if (P.size()<5) return;

//     vector<pair<double, int>> modularityValues;
//     for (int i = 1; i <= N; i++) {
//         double modValue = modularity(dk[i],lk[i]);  
//         modularityValues.push_back({modValue, i});
//     }

//     sort(modularityValues.begin(), modularityValues.end());

//     vector<vector<int>> sortedP(N + 1);
//     vector<double> sortedQ(N + 1);
//     vector<vector<double>> sortedV(N + 1);
//     vector<vector<int>> sortedPb(N + 1);
//     vector<double> sortedQb(N + 1);
//     vector<vector<int>> sorteddk(N + 1);
//     vector<vector<int>> sortedlk(N + 1); 
//     for (int i = 0; i < N; i++) {
//         sortedP[i + 1] = P[modularityValues[i].second];
//         sortedQ[i + 1] = Q[modularityValues[i].second];
//         sortedV[i + 1] = V[modularityValues[i].second];
//         sortedPb[i + 1] = Pb[modularityValues[i].second];
//         sortedQb[i + 1] = Qb[modularityValues[i].second];
//         sorteddk[i + 1] = dk[modularityValues[i].second];
//         sortedlk[i + 1] = lk[modularityValues[i].second];
//     }

//     P=sortedP;
//     Q=sortedQ;
//     V=sortedV;
//     Pb=sortedPb;
//     Qb=sortedQb;
//     dk=sorteddk;
//     lk=sortedlk;

//     double N_nor=N-(N/2+1)+1;
//     uniform_real_distribution<double> dis(0,1);
//     for (int i=N/2+1;i<=N;i++){
//         double C=1.0-exp(-double(i)/N_nor);
//         double rand=dis(gen);
//         if (rand<=C){
//             P.erase(P.begin() + i);
//             Q.erase(Q.begin() + i);
//             V.erase(V.begin() + i);
//             Pb.erase(Pb.begin() + i);
//             Qb.erase(Qb.begin() + i);
//             dk.erase(dk.begin() + i);
//             lk.erase(lk.begin() + i);
//             --N;
//         }
//     }
    
// }


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
    rep(t,1,T,1){
        rep(p,1,N,1){
            uniform_real_distribution<double> dis(0.0,1.0);
            vector<double> r1(n+1), r2(n+1);
            vector<double> diffPb=calDiff(P[p],Pb[p]);
            vector<double> diffPg=calDiff(P[p],Pg);
            rep(i,1,n,1){
                r1[i]=dis(gen);
                r2[i]=dis(gen);
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


        cout<<"Iteration "<<t<<": "<<Qg<<" "<<N<<"\n";
    }

    cout<<Qg<<"\n";
    standardization(Pg);
    // rep(i,1,n,1)
    //     cout<<Pg[i]<<" ";
    cout<<V[1][1]<<"\n";

}

int main(){
    // fastIO
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