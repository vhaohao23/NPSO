#include<bits/stdc++.h>
using namespace std;

#define rep(i,a,b,x) for(int i=a;i<=b;i+=x)
#define fastIO ios_base::sync_with_stdio(false);cout.tie(NULL);cin.tie(NULL);

class LouvainAlgorithm {
private:
    int n, m;
    vector<vector<int>> adj;
    vector<int> degree;
    vector<int> community;
    double total_edges;
    
    // Cache
    unordered_map<int, long long> comm_total_degree;
    unordered_map<int, long long> comm_internal_edges;
    
    int total_moves;
    
public:
    LouvainAlgorithm() : total_moves(0) {}
    
    void readInput() {
        freopen("input.txt", "r", stdin);
        
        cin >> n >> m;
        total_edges = m;
        
        adj.resize(n + 1);
        degree.resize(n + 1, 0);
        community.resize(n + 1);
        
        for (int i = 1; i <= n; i++) {
            community[i] = i;
        }
        
        for (int i = 0; i < m; i++) {
            int u, v;
            cin >> u >> v;
            adj[u].push_back(v);
            adj[v].push_back(u);
            degree[u]++;
            degree[v]++;
        }
    }
    
    void buildCache() {
        comm_total_degree.clear();
        comm_internal_edges.clear();
        
        // Total degree per community
        for (int i = 1; i <= n; i++) {
            comm_total_degree[community[i]] += degree[i];
        }
        
        // Internal edges per community (count each edge ONCE)
        for (int u = 1; u <= n; u++) {
            for (int v : adj[u]) {
                if (u < v && community[u] == community[v]) {
                    comm_internal_edges[community[u]]++;
                }
            }
        }
    }
    
    // FIXED: Correct modularity formula
    double computeModularity() {
        double Q = 0.0;
        double m_double = (double)total_edges;
        double two_m = 2.0 * m_double;
        
        set<int> unique_comms;
        for (int i = 1; i <= n; i++) {
            unique_comms.insert(community[i]);
        }
        
        for (int c : unique_comms) {
            // L_c = number of edges inside community c
            double L_c = (double)comm_internal_edges[c];
            
            // K_c = sum of degrees in community c
            double K_c = (double)comm_total_degree[c];
            
            // Q = sum_c [ L_c/m - (K_c/2m)^2 ]
            Q += (L_c / m_double) - (K_c / two_m) * (K_c / two_m);
        }
        
        return Q;
    }
    
    // FIXED: Correct modularity gain calculation
    double modularityGain(int node, int from_comm, int to_comm) {
        if (from_comm == to_comm) return 0.0;
        
        double m_double = (double)total_edges;
        double two_m = 2.0 * m_double;
        
        int k_i = degree[node];
        
        // Count edges from node to each community
        int k_i_in_from = 0;  // edges to nodes in from_comm
        int k_i_in_to = 0;    // edges to nodes in to_comm
        
        for (int neighbor : adj[node]) {
            if (community[neighbor] == from_comm) k_i_in_from++;
            if (community[neighbor] == to_comm) k_i_in_to++;
        }
        
        // Sigma_tot = sum of degrees in community
        long long sigma_from = comm_total_degree[from_comm];
        long long sigma_to = comm_total_degree[to_comm];
        
        // Delta Q formula (correct version)
        // Remove from old community: -[ k_i_in / m - k_i * sigma_from / (2m^2) ]
        // Add to new community: +[ k_i_in / m - k_i * sigma_to / (2m^2) ]
        
        double delta_remove = (double)k_i_in_from / m_double 
                            - (double)k_i * (double)(sigma_from - k_i) / (two_m * m_double);
        
        double delta_add = (double)k_i_in_to / m_double 
                         - (double)k_i * (double)(sigma_to + k_i) / (two_m * m_double);
        
        return delta_add - delta_remove;
    }
    
    bool localMovePhase() {
        vector<int> nodes;
        for (int i = 1; i <= n; i++) {
            nodes.push_back(i);
        }
        
        random_shuffle(nodes.begin(), nodes.end());
        
        bool improved = false;
        int moves = 0;
        
        for (int u : nodes) {
            if (adj[u].empty()) continue;
            
            // Find neighboring communities
            unordered_map<int, int> neighbor_comms;
            for (int v : adj[u]) {
                neighbor_comms[community[v]]++;
            }
            
            int current_comm = community[u];
            int best_comm = current_comm;
            double best_gain = 0.0;
            
            // Try all neighboring communities
            for (auto& [comm, count] : neighbor_comms) {
                if (comm == current_comm) continue;
                
                double gain = modularityGain(u, current_comm, comm);
                
                if (gain > best_gain + 1e-10) {
                    best_gain = gain;
                    best_comm = comm;
                }
            }
            
            // Move if improvement
            if (best_comm != current_comm && best_gain > 1e-10) {
                // Update cache
                int k_i_in_old = 0;
                int k_i_in_new = 0;
                
                for (int v : adj[u]) {
                    if (community[v] == current_comm) k_i_in_old++;
                    if (community[v] == best_comm) k_i_in_new++;
                }
                
                comm_total_degree[current_comm] -= degree[u];
                comm_total_degree[best_comm] += degree[u];
                
                comm_internal_edges[current_comm] -= k_i_in_old;
                comm_internal_edges[best_comm] += k_i_in_new;
                
                community[u] = best_comm;
                improved = true;
                moves++;
            }
        }
        
        total_moves += moves;
        return improved;
    }
    
    void aggregateGraph() {
        // Renumber communities consecutively
        unordered_map<int, int> new_id;
        int id_counter = 1;
        
        for (int i = 1; i <= n; i++) {
            if (new_id.find(community[i]) == new_id.end()) {
                new_id[community[i]] = id_counter++;
            }
            community[i] = new_id[community[i]];
        }
        
        // Build super-graph
        map<pair<int, int>, int> super_edges;
        
        for (int u = 1; u <= n; u++) {
            for (int v : adj[u]) {
                int cu = community[u];
                int cv = community[v];
                
                if (cu < cv) {
                    super_edges[{cu, cv}]++;
                } else if (cu > cv) {
                    super_edges[{cv, cu}]++;
                }
            }
        }
        
        // Rebuild graph at community level
        int num_super_nodes = id_counter - 1;
        
        vector<vector<int>> new_adj(num_super_nodes + 1);
        vector<int> new_degree(num_super_nodes + 1, 0);
        
        for (auto& [edge, weight] : super_edges) {
            int u = edge.first;
            int v = edge.second;
            
            for (int i = 0; i < weight; i++) {
                new_adj[u].push_back(v);
                new_adj[v].push_back(u);
                new_degree[u]++;
                new_degree[v]++;
            }
        }
        
        // Update
        n = num_super_nodes;
        adj = new_adj;
        degree = new_degree;
        
        for (int i = 1; i <= n; i++) {
            community[i] = i;
        }
    }
    
    void run(int max_levels = 100) {
        cout << "========================================" << endl;
        cout << "Louvain Algorithm (FIXED)" << endl;
        cout << "========================================" << endl;
        cout << "Nodes: " << n << ", Edges: " << m << endl;
        cout << endl;
        
        auto start_time = chrono::high_resolution_clock::now();
        
        buildCache();
        double prev_modularity = computeModularity();
        
        cout << "Initial modularity: " << fixed << setprecision(8) 
             << prev_modularity << endl;
        
        if (prev_modularity < 0) {
            cout << "WARNING: Negative modularity detected!" << endl;
            cout << "This usually means there's a bug in the implementation." << endl;
        }
        
        cout << "Initial communities: " << comm_total_degree.size() << endl;
        cout << endl;
        
        int level = 0;
        
        while (level < max_levels) {
            level++;
            
            cout << "=== Level " << level << " ===" << endl;
            auto level_start = chrono::high_resolution_clock::now();
            
            // Phase 1: Local moving
            int pass = 0;
            bool improved = true;
            
            while (improved && pass < 10) {
                pass++;
                int moves_before = total_moves;
                
                improved = localMovePhase();
                
                buildCache();
                double current_Q = computeModularity();
                
                int moves_this_pass = total_moves - moves_before;
                
                cout << "  Pass " << pass << ": Q=" << fixed << setprecision(8) 
                     << current_Q << ", Communities=" << comm_total_degree.size()
                     << ", Moves=" << moves_this_pass << endl;
                
                if (current_Q - prev_modularity < 1e-8) {
                    cout << "  Converged (improvement < 1e-8)" << endl;
                    break;
                }
                
                prev_modularity = current_Q;
            }
            
            buildCache();
            double level_Q = computeModularity();
            
            auto level_end = chrono::high_resolution_clock::now();
            auto level_duration = chrono::duration_cast<chrono::milliseconds>(level_end - level_start);
            
            cout << "Level " << level << " completed in " 
                 << level_duration.count() / 1000.0 << "s" << endl;
            cout << "Modularity: " << fixed << setprecision(8) << level_Q 
                 << ", Communities: " << comm_total_degree.size() << endl;
            cout << endl;
            
            // Phase 2: Aggregation
            int old_n = n;
            aggregateGraph();
            
            if (n == old_n || n == 1) {
                cout << "Converged: no more aggregation" << endl;
                break;
            }
            
            buildCache();
        }
        
        auto end_time = chrono::high_resolution_clock::now();
        auto total_duration = chrono::duration_cast<chrono::milliseconds>(end_time - start_time);
        
        double final_modularity = computeModularity();
        
        cout << "========================================" << endl;
        cout << "FINAL RESULTS" << endl;
        cout << "========================================" << endl;
        cout << "Final Modularity: " << fixed << setprecision(8) << final_modularity << endl;
        cout << "Levels: " << level << endl;
        cout << "Total Moves: " << total_moves << endl;
        cout << "Communities: " << comm_total_degree.size() << endl;
        cout << "Time: " << fixed << setprecision(2) 
             << total_duration.count() / 1000.0 << " seconds" << endl;
        cout << "========================================" << endl;
    }
    
    void writeOutput() {
        freopen("output_louvain.txt", "w", stdout);
        
        map<int, vector<int>> comm_nodes;
        for (int i = 1; i <= n; i++) {
            comm_nodes[community[i]].push_back(i);
        }
        
        cout << "Louvain Results" << endl;
        cout << "Communities: " << comm_nodes.size() << endl;
        cout << "Modularity: " << fixed << setprecision(8) << computeModularity() << endl;
        cout << endl;
        
        cout << "Node -> Community" << endl;
        for (int i = 1; i <= min(1000, n); i++) {
            cout << i << " " << community[i] << endl;
        }
    }
};

int main() {
    clock_t tStart = clock();
    srand(time(NULL));
    
    LouvainAlgorithm louvain;
    louvain.readInput();
    louvain.run(100);
    louvain.writeOutput();
    
    fclose(stdout);
    freopen("/dev/tty", "w", stdout);
    
    printf("\nTime: %.2fs\n", (double)(clock() - tStart)/CLOCKS_PER_SEC);
    printf("Results saved to output_louvain.txt\n");
    
    return 0;
}