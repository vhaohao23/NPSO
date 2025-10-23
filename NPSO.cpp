#include<bits/stdc++.h>
using namespace std;

#define rep(i,a,b,x)  for(int i=a;i<=b;i+=x)

random_device rd;   
mt19937 gen(rd());

const int N=100;
const double c1=2,c2=2;
const double w=0.7298;

int T=100;

int n,m;
vector<vector<int>> E;
vector<vector<int>> P(N+1);     
vector<vector<int>> Pb(N+1);
vector<int> Pg;
vector<double> Q(N+1,0);
vector<double> Qb(N+1,0);
double Qg=0;

vector<vector<double>> V;
vector<double> k;

vector<vector<int>> dk(N+1);
vector<vector<int>> lk(N+1);



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

vector<int> decoding(vector<vector<int>> a){
    bool dd[n+1]={};
    vector<int> l(n+1);
    int cnt=0;

    rep(i,1,n,1)
        if (!dd[i]){
            ++cnt;
            queue<int> q;
            q.push(i);
            while (!q.empty()){
                int u=q.front();
                q.pop();
                l[u]=cnt;
                for (int v:a[u])
                    if (!dd[v]){
                        dd[v]=true;
                        q.push(v);
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
    map<int,int> mp;
    int cnt=0;
    rep(i,1,n,1)
        if (!mp[p[i]])
            mp[p[i]]=++cnt;
    rep(i,1,n,1)
        p[i]=mp[p[i]];
}

vector<unordered_map<int, vector<int>>> cachedCommPb(N+1);
unordered_map<int, vector<int>> cachedCommPg_global;
bool needRebuildPg = true;

void rebuildCommunityMap(const vector<int>& partition, unordered_map<int, vector<int>>& res){
    res.clear();
    rep(i,1,n,1){
        res[partition[i]].push_back(i);
    }
}

void NPSO(){
    initialization();   
    
    // Initial cache
    rep(p,1,N,1){
        rebuildCommunityMap(Pb[p], cachedCommPb[p]);
    }
    rebuildCommunityMap(Pg, cachedCommPg_global);
    
    cout<<Qg<<"\n";    
    rep(i,1,n,1)
        cout<<Pg[i]<<" ";
    cout<<"\n";

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

            vector<vector<int>> a(n+1);
            vector<bool> dd(n+1,0);

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

                        int lastNode = -1;
                        for (int j : *community){
                            if (!dd[j]){
                                if (lastNode != -1){
                                    a[lastNode].push_back(j);
                                    a[j].push_back(lastNode);
                                }
                                lastNode = j;
                                dd[j] = true;
                            }
                        }
                    }
                }

            P[p]=decoding(a);
            caldklk(P[p],dk[p],lk[p]);
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
    }

    cout<<Qg<<"\n";
    standardization(Pg);
    rep(i,1,n,1)
        cout<<Pg[i]<<" ";
}

int main(){
    clock_t tStart = clock();
    
    freopen("input.txt","r",stdin);

    cin>>n>>m;

    E.resize(n+1);
    k.resize(n+1,0);  
    V.resize(N+1,vector<double>(n+1,-1));

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