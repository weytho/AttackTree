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