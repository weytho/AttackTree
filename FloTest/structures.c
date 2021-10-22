
// -------- NODES

typedef struct s_Node Node;
struct s_Node {
   char  title[50];
   char  type[5];
   int   root;
   int   leaf;
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

void list_free (List *list)
{
   List *runner = list;
   while(runner != NULL)
   {
      runner = runner->next;
      free(list->data);
      free(list);
      list = runner;
   }
}


// -------- EDGES

typedef struct s_Edge Edge;
struct s_Edge {
   char  parent[50];
   char  child[50];
}; 


typedef struct e_List EList;
struct e_List {
   EList *next;
   Edge *data;
};

EList* elist_create(Edge* data)
{
   printf("elist_create \n");
   EList *list = malloc(sizeof(EList));
   if(list){
      list->data = data;
      list->next = NULL;
   }
   return list;
}

EList* elist_add (EList *list, Edge* data)
{
   printf("elist_add \n");
   EList **plist = &list;
   while (*plist){
      plist = &(*plist)->next;
   }
   *plist = elist_create(data);
   if (*plist)
      return list;
   else 
      return NULL;
}

void elist_free (EList *list)
{
   EList *runner = list;
   while(runner != NULL)
   {
      runner = runner->next;
      free(list->data);
      free(list);
      list = runner;
   }
}