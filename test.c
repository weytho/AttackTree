//  cc -fPIC -shared -o my_func.so my_func.c
#include <stdio.h>
#include <string.h>

int main(int argc, char *argv[]) {
   
    printf("MAIN argc : %d \n", argc);
    printf("MAIN argv : %s \n", argv[1]);
    char * input = argv[1];
    int count = 0;
    while(*input !='\0')
    {
        printf("%c\n", input[0]);
        count++;
        input++;
    }
    printf("%d\n", count);
    input = argv[1];
    char *add = "bbbbb";
    printf("%s\n", input);
    strncat(input,add,6);
    printf("%s\n", input);
    return count;
}