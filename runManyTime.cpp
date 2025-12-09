#include <iostream>
#include <cstdlib>

int main() {
    freopen("output.txt", "w", stdout);
    system("g++ -O3 -fopenmp -march=native NPSO.cpp -o NPSO");
    for(int i = 1; i <= 30; i++) {
        system("./NPSO");
    }
    
    return 0;
}