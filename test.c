//  cc -fPIC -shared -o my_func.so my_func.c
int main(int argc, char *argv[]) {
   
    printf("MAIN argc : %d \n", argc);
    printf("MAIN argv : %s \n", argv);
    char * input = argv;
    int count = 0;
    while(*input !='\0')
    {
        printf("%c\n", input[0]);
        count++;
        input++;
    }
    printf("%d\n", count);
    return count;
}