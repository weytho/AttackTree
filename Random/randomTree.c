#include<stdio.h>
#include<string.h>
#include<time.h>
#include<stdlib.h>
#include<math.h>


void main(int argc, char *argv[]) {

    if(argc < 3){
        printf("./randomTree [filename] [maxdepth]\n");
        return;
    }

    srand(time(NULL));
   
    char *name = argv[1];
    printf("Name of file is : %s \n", name);
    FILE * file = fopen(name,"a");
    if(file == NULL){
        printf("Cannot open file %s\n",argv[1]);
        return;
    }
   
    int maxdepth = atoi(argv[2]);
    printf("Max Depth %d\n",maxdepth);

    char root[] = "Node";
    int depth = 0;
    int branching_factor = 3;
    //strncat(root, "bbb",4);
    
    nodeGenerator(file,root,depth,maxdepth);

    for (int i=0; i<20;i++){
        int r = rand() % 10;
        fprintf(file, "%d\n",r);
        printf("%d\n", r);
    }

    fclose(file);
}