/**
*  @file
*/

#include<stdio.h>
#include<string.h>
#include<json-c/json.h>
#include"structures.c"
#include "HashTable.c"
#include <ctype.h>


typedef struct custom_List Tree_LL;
struct custom_List {
      Node* n;
      Tree_LL *next;
      Tree_LL* parents;
      Tree_LL* children;
};

Node * copy_node(Node *old){
   Node * new_Node = malloc(sizeof(Node));
   memcpy(new_Node->title, old->title, sizeof(new_Node->title));
   memcpy(new_Node->type, old->type, sizeof(new_Node->type));
   new_Node->cost = 0;
   new_Node->prob = 1.0;
   return new_Node;
}

void replace_spaces(char *str){
   if (str != NULL) {
      while (*str){
         if(isspace((unsigned char)*str)){
            *str = '_';
         }
         str++;
      }
   }
}

char *trimwhitespace(char *str){
   if(str == NULL){
      return NULL;
   }
   char *end;
   // Trim leading space
   while(isspace((unsigned char)*str)) str++;
   if(*str == 0)  // All spaces?
      return str;
   // Trim trailing space
   end = str + strlen(str) - 1;
   while(end > str && isspace((unsigned char)*end)) end--;
   // Write new null terminator character
   end[1] = '\0';
   return str;
}

int is_empty(char *s) {
  while (*s != '\0') {
    if (!isspace((unsigned char)*s))
      return 0;
    s++;
  }
  return 1;
}

void printTree_LL(Tree_LL * list){
   Tree_LL * current = list;

      printf("title : %s ", current->n->title);
      printf(" -- > ");
      Tree_LL * new_current = current->parents;

      while (new_current != NULL) {
         printf("par : %s ", new_current->n->title);
         new_current = new_current->next;
      }
      printf(" ||| ");

      Tree_LL * new_current2 = current->children;
      while (new_current2 != NULL) { 
         printf("child: %s ", new_current2->n->title);
         new_current2 = new_current2->next;
      }
      printf("\n");
}

void printTree_total(Tree_LL * list){
   printf("Print\n");
   Tree_LL * current = list;
   if(current != NULL){
      printTree_LL(current);
      current = current->children;
      while (current != NULL) {
         printTree_total(current);
         current = current->next;
      }
   }
}

Tree_LL * addToEndList(Tree_LL *head_list, Tree_LL *node){
   if( head_list == NULL ){
      head_list = node;
   } else {
      Tree_LL * current = head_list;
      while (current->next != NULL) {
         current = current->next;
      }
      current->next = node;
   }
   return head_list;
}

Tree_LL * extractFromList(Tree_LL **head_list, char *name){
   Tree_LL * current = *head_list;
   Tree_LL * last = NULL;
   Tree_LL * tmp = NULL;

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

int isInList(Tree_LL *head_list, char * name){
   if( head_list == NULL ){
      return 0;
   }

   Tree_LL * current = head_list;
   while (current != NULL) {
      if (strcmp(current->n->title, name) == 0){
         return 1;
      }
      if (isInList(current->children, name) == 1){
         return 1;
      }
      current = current->next;
   }
   return 0;
}

Tree_LL * getFromList(Tree_LL *head_list, char * name){
   Tree_LL * current = head_list;
   Tree_LL * tmp = NULL;
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

void addParents(Tree_LL *node, Tree_LL *parent){

   Tree_LL * new_parent = malloc(sizeof(Tree_LL));
   new_parent->n = parent->n;
   new_parent->children = parent->children;
   new_parent->parents = parent->parents;
   new_parent->next = NULL;

   if(node->parents == NULL){
      node->parents = new_parent;
   } else {
      Tree_LL * current = node->parents;
      while (current->next != NULL) {
         current = current->next;
      }
      current->next = new_parent;
   }
}

void addChildrentoAllInstances(Tree_LL * whole, Tree_LL *child, Tree_LL *node){
   Tree_LL * current = whole;
   while (current != NULL) {
      if (strcmp(current->n->title, node->n->title) == 0){
         current->children = child;
         child->next = NULL;
      }
      addChildrentoAllInstances(current->children, child, node);
      current = current->next;
   }
}

void addChildren(Tree_LL * node, Tree_LL *child, Tree_LL * whole){

   if(node->children == NULL){
      // Pobleme modif all nodes les mêmes
      addChildrentoAllInstances(whole, child, node);
   } else {
      Tree_LL * current = node->children;
      while (current->next != NULL) {
         current = current->next;
      }
      current->next = child;
      child->next = NULL;
   }
}


Tree_LL * createTreeNode(char * title, char * type){

   Tree_LL * new_TLL = malloc(sizeof(Tree_LL));
   Node * new_Node = malloc(sizeof(Node));

   snprintf(new_Node->title, sizeof(new_Node->title), "%s", title);
   snprintf(new_Node->type, sizeof(new_Node->type), "%s", type);
   new_Node->cost = 0;
   new_Node->prob = 1.0;

   new_TLL->n = new_Node;
   new_TLL->children = NULL;
   new_TLL->parents = NULL;
   new_TLL->next = NULL;

   return new_TLL;
}

typedef struct basic_List BasicList;
struct basic_List {
      Tree_LL *data;
      BasicList *next;
};

typedef struct double_basic_List DoubleBList;
struct double_basic_List {
      BasicList *good;
      BasicList *bad;
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

int is_in_pointer_list(BasicList *list, Tree_LL *current){
   BasicList * runner = list;

   while (runner != NULL) {
      if (runner->data == current){
         return 1;
      }
      runner = runner->next;
   }
   return 0;
}

Tree_LL * get_from_flatList(BasicList *list, char* name){
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

BasicList *createNode_flatList(Tree_LL *list){
    BasicList *newNode = malloc(sizeof(BasicList));
    newNode->data = list;
    newNode->next = NULL;
    return newNode;
}

BasicList * push_flatlist(BasicList *list, BasicList* topush){
   topush->next = list;
   return topush;
}

DoubleBList * flatten_tree_uniq(Tree_LL *list, DoubleBList* results){
   if( list == NULL ){
      return results;
   }
   Tree_LL * current = list;
   Tree_LL * children = NULL;
   Tree_LL * next = NULL;
   while (current != NULL) {

      if (is_in_flatList(results->good, current->n->title) == 0){
         BasicList * tmp = createNode_flatList(current);
         results->good = push_flatlist(results->good, tmp);
         children = current->children;
         next = current->next;
      } else {
         children = current->children;
         next = current->next;

         if(results->bad == NULL){
            results->bad = createNode_flatList(current);
         } else {
            if(get_from_flatList(results->good, current->n->title) != current && !is_in_pointer_list(results->bad, current)) {
               BasicList * tmp = createNode_flatList(current);
               results->bad = push_flatlist(results->bad, tmp);
            }
         }

      }
      results = flatten_tree_uniq(children, results);
      current = next;
   }

   return results;
}

void free_flat_list(BasicList *list)
{
   if (list == NULL){
      return;
   }
   BasicList * runner = list;
   BasicList * current = NULL;
   Tree_LL * parent = NULL;
   Tree_LL * tmp = NULL;
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

BasicList * init_flatten(Tree_LL *list){
   BasicList * flatList = createNode_flatList(list);
   BasicList * final;

   DoubleBList *res = malloc(sizeof(DoubleBList));
   res->good = flatList;
   res->bad = NULL;
   
   res = flatten_tree_uniq(list->children, res);
   printFlatList(res->good);
   free_flat_list(res->good);

   if (res->bad == NULL){
      final = res->good;
      free(res);
      return final;
   }
   BasicList * runner = res->bad;
   BasicList * current = NULL;
   while (runner != NULL) {
      current = runner;
      runner = current->next;

      free(current->data);
      current->data = NULL;
      free(current);
      current = NULL;
   
   }

   final = res->good;
   free(res);
   return final;
}

void Tree_free_from_top(Tree_LL *list){

   if (list == NULL){
      return;
   }

   init_flatten(list);
}

int cycle_check(Tree_LL *parent, char * child_name){

   Tree_LL * current = parent;

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


void set_properties(Tree_LL * list, HashTable * h){
   Tree_LL * current = list;
   Tree_LL * new_current2 = current->children;

   if (new_current2 == NULL) {
      // check for properties
      int i = NameIndex(h, current->n->title);

      NodeP * Nn = getH(h, i);
      if(Nn != NULL){
         current->n->cost = Nn->cost;
         current->n->prob = Nn->prob;
         deleteH(h, Nn);
      }

   }
}

void set_properties_total(Tree_LL * list, HashTable * h){
   Tree_LL * current = list;
   if(current != NULL){
      set_properties(current, h);
      current = current->children;
      while (current != NULL) {
         set_properties_total(current, h);
         current = current->next;
      }
   }
}


HashTable * parse_properties(char * prop_text){

   struct HashTable *ht_properties;

   char *saveptr3;
   char *saveptr4;
   char *saveptr5;

   char delim5[] = ";";
   char delim6[] = ":";
   char delim7[] = "=";
   char delim8[] = "=,";

   size_t size_prop = strlen(prop_text) + 1;
   char *length_ptr = malloc(size_prop * sizeof(char));
   memcpy(length_ptr, prop_text, size_prop);

   printf("@@@@@@@@@@@@@ NODES @@@@@@@@@@@@@\n");

   int count = 0;
   char *length_runner = strtok_r(length_ptr, delim6, &saveptr5);

   while(length_runner != NULL){
      count = count + 1;
      length_runner = strtok_r(NULL, delim6, &saveptr5);
   }
   if( count > 0 ){
      count = count - 1;
   }

   free(length_ptr);

   ht_properties = newHastable(count * 2);

   char *ptr_prop = strtok_r(prop_text, delim5, &saveptr3);
   char * prop_name;
   char * prop_value;

   while(ptr_prop != NULL){

      if(!is_empty(ptr_prop)){

         size_t size2 = strlen(ptr_prop) + 1;
         char *ptr_prop_copy = malloc(size2 * sizeof(char));
         memcpy(ptr_prop_copy, ptr_prop, size2);

         ptr_prop = trimwhitespace(strtok_r(ptr_prop_copy, delim6, &saveptr4));
         replace_spaces(ptr_prop);

         NodeP *n_prop = malloc(sizeof(NodeP));
         n_prop->cost = 0;
         n_prop->prob = 1.0;

         memcpy(n_prop->Name, ptr_prop, sizeof(n_prop->Name));

         prop_name = trimwhitespace(strtok_r(NULL, delim7, &saveptr4));

         while(prop_name != NULL){

            if(!is_empty(prop_name)){
               prop_value = trimwhitespace(strtok_r(NULL, delim8, &saveptr4));
               
               if(strcmp(prop_name, "cost") == 0){
                  n_prop->cost = strtol(prop_value, NULL, 10);
               } else if (strcmp(prop_name, "prob") == 0){
                  n_prop->prob = strtod(prop_value, NULL);
               }
            }
            prop_name = trimwhitespace(strtok_r(NULL, delim7, &saveptr4));
            
         }

         insertH(ht_properties, n_prop);
         free(ptr_prop_copy);
      }

      ptr_prop = strtok_r(NULL, delim5, &saveptr3); 
   }

   return ht_properties;
}

HashTable * parse_countermeasures(char * counter_text, HashTable *ht_properties){

   struct HashTable *ht_CM;

   char *saveptr6;
   char *saveptr7;

   char delim9[] = ")";
   char delim10[] = "(,";

   size_t counter_size = strlen(counter_text) + 1;
   char * new_counter_text = malloc(counter_size * sizeof(char));
   memcpy(new_counter_text, counter_text, counter_size);

   int count = 0;
   char *length_runner = strtok_r(new_counter_text, delim9, &saveptr6);

   while(length_runner != NULL){
      count = count + 1;
      length_runner = strtok_r(NULL, delim9, &saveptr6);
   }
   if( count > 0 ){
      count = count - 1;
   }

   free(new_counter_text);

   ht_CM = newHastable(count * 2);

   char *new_ptr = strtok_r(counter_text, delim9, &saveptr6);
   char * ptr_cm;

   while(new_ptr != NULL){

      if(!is_empty(new_ptr)){

         size_t size2 = strlen(new_ptr) + 1;
         char *n_ptr_copy = malloc(size2 * sizeof(char));
         memcpy(n_ptr_copy, new_ptr, size2);

         ptr_cm = trimwhitespace(strtok_r(n_ptr_copy, delim10, &saveptr7));
         replace_spaces(ptr_cm);

         new_ptr = trimwhitespace(strtok_r(NULL, delim10, &saveptr7));
         replace_spaces(new_ptr);
         int i = -1;

         while(new_ptr != NULL){

            i = NameIndex(ht_CM, new_ptr);

            NodeP * Nn = getH(ht_CM, i);

            if(Nn != NULL){
               NodeCM * node = malloc(sizeof(NodeCM));

               if (ht_properties != NULL){
                  int k = NameIndex(ht_properties, ptr_cm);

                  NodeP * prop_Nn = getH(ht_properties, k);
                  if(prop_Nn != NULL){
                     node->cost = prop_Nn->cost;
                     node->prob = prop_Nn->prob;
                  } else {
                     node->cost = 0;
                     node->prob = 1.0;
                  }
               }

               if(Nn->CMlist != NULL){
                  NodeCM * tmp = Nn->CMlist;
                  memcpy(node->CMtitle, ptr_cm, sizeof(node->CMtitle));
                  node->next = NULL;
                  while(tmp->next != NULL){
                     tmp = tmp->next;
                  }
                  tmp->next = node;
               } else {
                  memcpy(node->CMtitle, ptr_cm, sizeof(node->CMtitle));
                  node->next = NULL;
                  Nn->CMlist = node;
               }
            } else {

               Nn = malloc(sizeof(NodeP));
               memcpy(Nn->Name, new_ptr, sizeof(Nn->Name));
               NodeCM * node = malloc(sizeof(NodeCM));
               memcpy(node->CMtitle, ptr_cm, sizeof(node->CMtitle));
               node->next = NULL;
               Nn->CMlist = node;

               if (ht_properties != NULL){
                  int j = NameIndex(ht_properties, ptr_cm);

                  NodeP * prop_Nn = getH(ht_properties, j);
                  if(prop_Nn != NULL){
                     Nn->cost = prop_Nn->cost;
                     Nn->prob = prop_Nn->prob;
                     node->cost = prop_Nn->cost;
                     node->prob = prop_Nn->prob;
                  } else {
                     Nn->cost = 0;
                     Nn->prob = 1.0;
                     node->cost = 0;
                     node->prob = 1.0;
                  }
               }

               insertH(ht_CM, Nn);
            }

            new_ptr = trimwhitespace(strtok_r(NULL, delim10, &saveptr7));
            replace_spaces(new_ptr);

         }

      }

      new_ptr = strtok_r(NULL, delim9, &saveptr6);
      
   }

   printf("END OF PARSER CM ! \n");
   //displayH(ht_CM);
   return ht_CM;

}