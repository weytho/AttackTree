
typedef struct t_Node TNode;
struct t_Node {
   char*  variable;
   char*  truth;
   TNode* next;
};

typedef struct s_List List;
struct s_List {
   List *next;
   TNode *data;
};

List* list_create(TNode* data)
{
   List *list = malloc(sizeof(List));
   if(list){
      list->data = data;
      list->next = NULL;
   }
   return list;
}

List* list_add (List *list, TNode* data)
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