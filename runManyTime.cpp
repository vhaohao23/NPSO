#include <iostream>
#include <cstdlib>

int main() {
    freopen("output.txt", "w", stdout);
    system("g++ -O3 -march=native NPSO_NMI.cpp -o NPSO_NMI.exe");
    for(int i = 1; i <= 20; i++) {
        system("NPSO_NMI.exe");
    }
    
    return 0;
}