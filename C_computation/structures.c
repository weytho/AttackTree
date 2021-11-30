
// -------- NODES

typedef struct s_Node Node;
struct s_Node {
   char  title[50];
   char  type[5];
   int   root;
   int   leaf;
   int   cost;
   double   prob;
   int     CM;
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
   int   CM;
}; 


typedef struct e_List EList;
struct e_List {
   EList *next;
   Edge *data;
};

EList* elist_create(Edge* data)
{
   EList *list = malloc(sizeof(EList));
   if(list){
      list->data = data;
      list->next = NULL;
   }
   return list;
}

EList* elist_add (EList *list, Edge* data)
{
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


// -------- Formula

typedef struct b_Form Formula;
struct b_Form {
   char *data;
   Formula *next;
};

void form_free(Formula *form){
   Formula *runner = form;
   while (runner != NULL)
   {
      runner = runner->next;
      free(form);
      form = runner;
   }
}

Formula * Parenthesis(char* type){
   Formula* new = malloc(sizeof(Formula));
   new->next = NULL;
   if(!strncmp("LEFT",type,5)){
      new->data = "( ";
   }
   else if(!strncmp("RIGHT",type,6)){
      new->data = " )";
   }
   else if(!strncmp("AND",type,4)){
      new->data = " AND ";
   }
   else if(!strncmp("OR",type,3)){
      new->data = " OR ";
   }
   else{
      new->data = " SAND ";
   }
   return new;
}

Formula * formula(char* type){
   Formula* new = malloc(sizeof(Formula));
   new->next = NULL;
   if(!strncmp("LEFT",type,5)){
      new->data = "( ";
   }
   else if(!strncmp("RIGHT",type,6)){
      new->data = " )";
   }
   else if(!strncmp("AND",type,4)){
      new->data = " & ";
   }
   else if(!strncmp("OR",type,3)){
      new->data = " | ";
   }
   else{
      new->data = " & ";
   }
   return new;
}

// -------- Return

typedef struct CostProbability CostProb;
struct CostProbability {
   int    cost;
   double prob;
   double esp;
};

// -------- Esperance (empirical)

double esp(int cost, double prob)
{
   double esp = cost;
   double last = cost;
   for (int i = 0; i < 10; i++)
   {
      last = last * (1-prob);
      esp = esp + last; 
   }
   printf("[ESP] Cost : %d | Prob : %f | Esp : %f \n", cost, prob, esp);
   return esp;
}
