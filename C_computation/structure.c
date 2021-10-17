struct Node {
   char  title[50];
   int   root;
   int   leaf;
   int   type;
} Node;  

struct Edge {
   struct Node  parent;
   struct Node  child;
   int   weight;
   int   type;
} Edge; 

int main(int argc, char *argv[]) {
   printf("Path too file is : %s", argv[1]);
   return 0;
}