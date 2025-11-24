#include <iostream>
#include <cstdlib>

int main() {
    freopen("output.txt", "w", stdout);
    for(int i = 1; i <= 10; i++) {
        system("g++ -O3 -march=native NPSO_NMI.cpp -o NPSO_NMI.exe");
        system("./NPSO_NMI.exe");
    }
    
    return 0;
}