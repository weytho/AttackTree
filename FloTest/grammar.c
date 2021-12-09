#include<stdio.h>
#include<string.h>
#include<json-c/json.h>
#include"structures.c"
#include "HashTable.c"


typedef struct custom_List DLL_List;
struct custom_List {
      Node* n;
      DLL_List *next;
      DLL_List* parents;
      DLL_List* children;
};

Node * copy_node(Node *old){
   Node * new_Node = malloc(sizeof(Node));
   memcpy(new_Node->title, old->title, sizeof(new_Node->title));
   memcpy(new_Node->type, old->type, sizeof(new_Node->type));
   return new_Node;
}

void printDLL_List(DLL_List * list){
   DLL_List * current = list;

      printf("title : %s ", current->n->title);
      printf(" -- > ");
      DLL_List * new_current = current->parents;

      while (new_current != NULL) {
         printf("par : %s ", new_current->n->title);
         new_current = new_current->next;
      }
      printf(" ||| ");

      DLL_List * new_current2 = current->children;
      while (new_current2 != NULL) { 
         printf("child: %s ", new_current2->n->title);
         new_current2 = new_current2->next;
      }
      printf("\n");
}

void printDLL_total(DLL_List * list){
   printf("Print\n");
   DLL_List * current = list;
   if(current != NULL){
      printDLL_List(current);
      current = current->children;
      while (current != NULL) {
         printDLL_total(current);
         current = current->next;
      }
   }
}

DLL_List * addToEndList(DLL_List *head_list, DLL_List *node){
   if( head_list == NULL ){
      head_list = node;
   } else {
      DLL_List * current = head_list;
      while (current->next != NULL) {
         current = current->next;
      }
      current->next = node;
   }
   return head_list;
}

DLL_List * extractFromList(DLL_List **head_list, char *name){
   DLL_List * current = *head_list;
   DLL_List * last = NULL;
   DLL_List * tmp = NULL;

   while (current != NULL && current->n != NULL) {
      if (strcmp(current->n->title, name) == 0){
         if (last == NULL){
            *head_list = current->next;
            return current;
         }
         last->next = current->next;
         return current;
      }
      tmp = extractFromList(&(current->children), name);
      if (tmp != NULL){
         return tmp;
      }
      last = current;
      current = current->next;
   }
   return NULL;
}

int isInList(DLL_List *head_list, char * name){
   if( head_list == NULL ){
      return 0;
   }

   DLL_List * current = head_list;
   while (current != NULL) {
      if (strcmp(current->n->title, name) == 0){
         printf("GOOD !\n");
         return 1;
      }
      if (isInList(current->children, name) == 1){
         return 1;
      }
      current = current->next;
   }
   return 0;
}

DLL_List * getFromList(DLL_List *head_list, char * name){
   DLL_List * current = head_list;
   DLL_List * tmp = NULL;
   while (current != NULL) {
      if (strcmp(current->n->title, name) == 0){
         return current;
      }
      tmp = getFromList(current->children, name);
      if (tmp != NULL){
         return tmp;
      }
      current = current->next;
   }
   return NULL;
}

void addParents(DLL_List *node, DLL_List *parent){

   // TODO pas utile comme ça ?
   DLL_List * new_parent = malloc(sizeof(DLL_List));
   new_parent->n = parent->n; //copy_node(parent->n); // = parent->n;
   new_parent->children = parent->children;
   new_parent->parents = parent->parents;
   new_parent->next = NULL;

   if(node->parents == NULL){
      node->parents = new_parent;
   } else {
      DLL_List * current = node->parents;
      while (current->next != NULL) {
         current = current->next;
      }
      current->next = new_parent;
      //parent->next = NULL;
   }
}

void addChildrentoAllInstances(DLL_List * whole, DLL_List *child, DLL_List *node){
   DLL_List * current = whole;
   while (current != NULL) {
      if (strcmp(current->n->title, node->n->title) == 0){
         current->children = child;
         child->next = NULL;
      }
      addChildrentoAllInstances(current->children, child, node);
      current = current->next;
   }
}

void addChildren(DLL_List * node, DLL_List *child, DLL_List * whole){

   if(node->children == NULL){
      // Pobleme modif all nodes les mêmes
      // TODO fix double pointers
      addChildrentoAllInstances(whole, child, node);
   } else {
      DLL_List * current = node->children;
      while (current->next != NULL) {
         current = current->next;
      }
      current->next = child;
      child->next = NULL;
   }
}


DLL_List * createDLLNode(char * title, char * type){

   DLL_List * new_DLL = malloc(sizeof(DLL_List));
   Node * new_Node = malloc(sizeof(Node));

   //memcpy(new_Node->title, title, sizeof(new_Node->title));
   //memcpy(new_Node->type, type, sizeof(new_Node->type));
   snprintf(new_Node->title, sizeof(new_Node->title), "%s", title);
   snprintf(new_Node->type, sizeof(new_Node->type), "%s", type);

   new_DLL->n = new_Node;
   new_DLL->children = NULL;
   new_DLL->parents = NULL;
   new_DLL->next = NULL;

   return new_DLL;
}

typedef struct basic_List BasicList;
struct basic_List {
      DLL_List *data;
      BasicList *next;
};

int is_in_flatList(BasicList *list, char* name){
   BasicList * runner = list;
   while (runner != NULL) {
      if (strcmp(runner->data->n->title, name) == 0){
         return 1;
      }
      runner = runner->next;
   }
   return 0;
}

DLL_List * get_from_flatList(BasicList *list, char* name){
   BasicList * runner = list;
   while (runner != NULL) {
      if (strcmp(runner->data->n->title, name) == 0){
         return runner->data;
      }
      runner = runner->next;
   }
   return NULL;
}

void printFlatList(BasicList *list){
   BasicList * runner = list;
   while (runner != NULL) {
      printf(" %s \n",runner->data->n->title);
      runner = runner->next;
   }
}

BasicList *createNode_flatList(DLL_List *list){
    BasicList *newNode = malloc(sizeof(BasicList));
    newNode->data = list;
    newNode->next = NULL;
    return newNode;
}

BasicList * push_flatlist(BasicList *list, BasicList* topush){
   topush->next = list;
   return topush;
}

BasicList * flatten_tree_uniq(DLL_List *list, BasicList *baseList){
   if( list == NULL ){
      return baseList;
   }
   DLL_List * current = list;
   DLL_List * children = NULL;
   DLL_List * next = NULL;
   while (current != NULL) {
      printFlatList(baseList);
      printf("CUT\n");
      if (is_in_flatList(baseList, current->n->title) == 0){
         BasicList * tmp = createNode_flatList(current);
         baseList = push_flatlist(baseList, tmp);
         children = current->children;
         next = current->next;
      } else {
         children = current->children;
         next = current->next;
         if( current != get_from_flatList(baseList, current->n->title) ) {
            free(current);
         }
      }
      baseList = flatten_tree_uniq(children, baseList);
      current = next;
   }
   return baseList;
}

void free_flat_list(BasicList *list)
{
   if (list == NULL){
      return;
   }
   BasicList * runner = list;
   BasicList * current = NULL;
   DLL_List * parent = NULL;
   DLL_List * child = NULL;
   DLL_List * tmp = NULL;
   while (runner != NULL) {
      current = runner;
      runner = current->next;

      free(current->data->n);
      current->data->n = NULL;

      parent = current->data->parents;
      while (parent != NULL){
         tmp = parent->next;
         free(parent);
         parent = tmp;
      }
      current->data->parents = NULL;

      free(current->data);
      current->data = NULL;
      free(current);
      current = NULL;
   }
}

BasicList * init_flatten(DLL_List *list){
   BasicList * flatList = createNode_flatList(list);
   BasicList * complete = flatten_tree_uniq(list->children, flatList);
   printFlatList(complete);
   free_flat_list(complete);
   return complete;
}

void DLL_free_from_top(DLL_List *list){

   if (list == NULL){
      return;
   }

   printf("YE PRINTING NOW !\n");
   init_flatten(list);
}

int cycle_check(DLL_List *parent, char * child_name){

   DLL_List * current = parent;
   if (strcmp(current->n->title, child_name) == 0){
      return 1;
   }
   current = current->parents;
   while (current != NULL) {
      if (cycle_check(current, child_name) == 1){
         return 1;
      }
      current = current->next;
   }
   return 0;

}


void set_properties(DLL_List * list, HashTable * h){
   DLL_List * current = list;
   DLL_List * new_current2 = current->children;

   if (new_current2 == NULL) {
      // check for properties
      printf("NICE1111 !%s! \n", current->n->title);
      int i = NameIndex(h, current->n->title);//current->n->title);
      printf("%d\n", i);
      displayH(h);
      NodeP * Nn = getH(h, i);
      if(Nn != NULL){
         printf("NICE !! %d, %f\n", Nn->cost, Nn->prob);
         current->n->cost = Nn->cost;
         current->n->prob = Nn->prob;
         deleteH(h, Nn);
         displayH(h);
      }

   }
}

void set_properties_total(DLL_List * list, HashTable * h){
   DLL_List * current = list;
   if(current != NULL){
      printf("NICE000 !! \n");
      set_properties(current, h);
      current = current->children;
      while (current != NULL) {
         set_properties_total(current, h);
         current = current->next;
      }
   }
}