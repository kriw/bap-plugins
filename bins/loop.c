#include <stdio.h>
int add(int a, int b) { return a + b; }
int main(int argc) {
    int sum = 0;
    for (int i = 0; i < argc; i++) {
        sum = add(sum, i);
    }
    if (sum > 0x50) {
        printf("Big: %d\n", sum);
    } else {
        printf("Small: %d\n", sum);
    }
    return 0;
}
