typedef struct s_Node Node;
struct s_Node {
   char  title[50];
   char  type[10];
   int   root;
   int   leaf;
};

typedef struct s_Edge Edge;
struct Edge {
   char  parent[50];
   char  child[50];
   int   weight;
   int   type;
};  

typedef struct s_List List;
struct s_List {
   List *next;
   Node *data;
};

List* list_create(Node* data)
{
   List *list = malloc(sizeof(List));
   if(list){
      list->data = data;
      list->next = NULL;
   }
   return list;
}

List* list_add (List *list, Node* data)
{
   List **plist = &list;
   while (*plist){
      plist = &(*plist)->next;
   }
   *plist = list_create(data);
   if (*plist)
      return list;
   else 
      return NULL;
}