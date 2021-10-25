//  cc -fPIC -shared -o my_func.so my_func.c
#include <stdio.h>
#include <string.h>

typedef struct Logic_Node Logic_Node;
struct Logic_Node {
    char name[20];
    int type; // 0 AND 1 OR 2 LEAF
    struct Logic_Node *next;
};

int main(int argc, char *argv[]) {
   

    
}

Logic_Node* createNode(char *name, int type){
    Logic_Node * n = malloc(sizeof(Logic_Node));
    memcpy(n->name, name, sizeof(char)*20);
    n->type = 0;
    n->next = NULL;
    return n;
}

void free_node(Logic_Node * n){
    free(n);
}