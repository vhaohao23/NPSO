#include <iostream>
#include <cstdlib>

int main() {
    freopen("output.txt", "w", stdout);
    system("g++ -O3 -fopenmp -march=native npso_optimized.cpp -o npso_optimized");
    for(int i = 1; i <= 30; i++) {
        system("./npso_optimized");
    }
    
    return 0;
}