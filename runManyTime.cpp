#include <iostream>
#include <cstdlib>

int main() {
    freopen("output.txt", "w", stdout);
    system("g++ -O3 -fopenmp -march=native NPSO_NMI.cpp -o NPSO_NMI");
    for(int i = 1; i <= 30; i++) {
        system("./NPSO_NMI");
    }
    
    return 0;
}