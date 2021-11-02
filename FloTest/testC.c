#include<stdio.h>
#include<json-c/json.h>
#include <string.h>
#include <stdlib.h>
#include "structures.c"
#include <ctype.h>
// sudo apt install libjson-c-dev
// gcc -shared -Wl,-soname,testlib -o testlib.so -fPIC testC.c -ljson-c
// /bin/python3 /home/flo/Desktop/Github/AttackTree/testThread.py
// https://stackoverflow.com/questions/38661635/ctypes-struct-returned-from-library

typedef struct full_List FList;
struct full_List {
   List *nl;
   EList *el;
   Formula *fo;
};

int JsonReader(struct json_object *parsed_json, List **list, EList **edges, Formula **form, Node *parent, int root){

   // READ THE JSON //
   struct json_object *action;
   struct json_object *type;
   struct json_object *costleaf;
   json_object_object_get_ex(parsed_json, "Action", &action);
   json_object_object_get_ex(parsed_json, "Type", &type);

   // CREATE + FILL THE NODE
   Node *node = malloc(sizeof(Node));
   if (node == NULL){
      printf("[Node] Malloc error\n");
   }
   strcpy(node->title, json_object_get_string(action));
   strcpy(node->type, json_object_get_string(type));
   node->root = root;
   if (strcmp(json_object_get_string(type), "LEAF" ))
      node->leaf = 0;
   else {
      node->leaf = 1;
      json_object_object_get_ex(parsed_json, "Cost", &costleaf);
      node->cost = json_object_get_int(costleaf);
   }

   // ADD IT TO THE LIST
   if (node->root == 1)
      *list = list_create(node);
   else 
      *list = list_add(*list, node);

   // ADD THE EDGE
   if (node->root == 1){}
   else{
      Edge *ed = malloc(sizeof(Edge));
      memcpy(ed->parent, parent->title, sizeof(char)*50);
      memcpy(ed->child, node->title,sizeof(char)*50);
      if (*edges == NULL)
      {
         *edges = elist_create(ed);
      }
      else{
         *edges = elist_add(*edges, ed);
      }
   }

   // ADD to formula
   if (node->leaf == 1){
      Formula *newVar = malloc(sizeof(Formula));
      newVar->data = json_object_get_string(action);
      newVar->next = NULL;
      if((*form) == NULL){
         (*form) = newVar;
      }
      else{
         Formula *runner = *(form);
         while(runner->next != NULL){
            runner = runner->next;
         }
         runner->next = newVar;
      }
   }

   // LOOK FOR ITS CHILDRENS
   if (node->leaf == 0) {
      struct json_object *children;
      size_t n_children;
      json_object_object_get_ex(parsed_json, "Child", &children);
      n_children = json_object_array_length(children);
      Formula *left = Parenthesis("LEFT");
      if((*form) == NULL){
         (*form) = left;
      }
      else{
         Formula *runner = *(form);
         while(runner->next != NULL){
            runner = runner->next;
         }
         runner->next = left;
      }

      int and_cost = 0;
      int or_cost = 999999;
      
      for(int i=0; i<n_children; i++){
         int cost = JsonReader(json_object_array_get_idx(children, i), list, edges, form, node, 0);
         and_cost = and_cost + cost;
         if(cost < or_cost){
            or_cost = cost;
         }
         if(i<n_children-1){
            Formula *t = Parenthesis(json_object_get_string(type));
            Formula *runner = *(form);
            while(runner->next != NULL){
               runner = runner->next;
            }
            runner->next = t; 
         }
      }

      Formula *right = Parenthesis("RIGHT");
      Formula *runner = *(form);
      while(runner->next != NULL){
         runner = runner->next;
      }
      runner->next = right;   

      if(!strcmp(json_object_get_string(type), "OR" )) {
         node->cost = or_cost;
      }
      else{
         node->cost = and_cost;
      }
   }
   return node->cost;
}


FList * mainfct(char * path) {
	//path = "/home/flo/Desktop/Github/AttackTree/FloTest/StructureGraph.json";
	printf("Path to file is : %s \n", path);
   printf("FLO\n");
	FILE *fp; 
   printf("FLO\n");
	char buffer[1024*2];
   printf("FLO\n");
	struct json_object *parsed_json;
   printf("FLO00000000000000000\n");
	fp = fopen(path,"r");
   printf("FLO00000\n");
	fread(buffer, 1024*2, 1, fp);
	fclose(fp);
   printf("FLO2\n");
	parsed_json = json_tokener_parse(buffer);
	EList *edges = NULL;
	List *list = NULL;
   Formula *form = NULL;
   printf("FLO233333\n");
	int cost = JsonReader(parsed_json, &list, &edges, &form, NULL, 1);
   printf("FLO22222\n");
	if(edges == NULL)
	{
		printf("Ceci est un crash \n");
		return 0;
	}

	List* runner = list;
	int count = 0;
	while(runner != NULL){
		count ++;
		printf("count : %d \n", count);
		printf("Node title : %s \n", runner->data->title);
		printf("Node type  : %s \n", runner->data->type);
		printf("Node root  : %d \n", runner->data->root);
		printf("Node leaf  : %d \n", runner->data->leaf);
		runner = runner->next;
	}

   EList* runner2 = edges;
   count = 0;
   while(runner2 != NULL){
      count ++;
      printf("count : %d \n", count);
      printf("Edges parent : %s \n", runner2->data->parent);
      printf("Edges child  : %s \n", runner2->data->child);
      runner2 = runner2->next;
   }

   //list_free(list);
   //elist_free(edges);

   Formula* runner3 = form;
   while(runner3 != NULL){
      printf("%s",runner3->data);
      runner3 = runner3->next;
   }
   printf("\n");

   FList *fl;
   FList init;

   init.el = edges;
   init.nl = list;
   init.fo = form;

   fl = malloc(sizeof(FList));
   if (fl == NULL){
      printf("[Node] Malloc  fl error\n");
   }
   *fl = init;

   return fl;
}

void freeList(List *l) {
	list_free(l);
}

void freeEList(EList *l) {
	elist_free(l);
}

void freeForm(Formula *l) {
	form_free(l);
}

int main (int argc, char * argv[]) { 
	printf("STARTING \n");

	char *path = "/home/flo/Desktop/Github/AttackTree/Structure/StructureGraph.json";
	mainfct(path);

	//CustomList * l = getList();
	//CustomNode * n = getNode();
	printf("START");
	//printf("l pointer : %p", (void *) l);
	//printf("HHHHHHHHHHHHHH %s, ",l->data->name);
	//freeNode(n);
	//freeList(l);
	return 0;
}

int is_empty(char *s) {
  while (*s != '\0') {
    if (!isspace((unsigned char)*s))
      return 0;
    s++;
  }
  return 1;
}

typedef struct custom_List DLL_List;
struct custom_List {
      Node* n;
      DLL_List *next;
      DLL_List* parents;
      DLL_List* children;
};

void printDLL_List(DLL_List * list){
   printf("Print\n");
   DLL_List * current = list;
   while (current != NULL) {
      printf("title : %s ", current->n->title);
      printf("\n");
      DLL_List * new_current = current->parents;
      while (new_current != NULL) { 
         printf("title par : %s ", new_current->n->title);
         new_current = new_current->next;
      }
      printf("\n");
      DLL_List * new_current2 = current->children;
      while (new_current2 != NULL) { 
         printf("title child: %s ", new_current2->n->title);
         new_current2 = new_current2->next;
      }
      printf("\n");
      //printDLL_List(current->parents);
      //printDLL_List(current->children);
      current = current->next;
   }
   
   printf("\n");

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
   //printf("####state###\n");
   //printDLL_List(head_list);

   return head_list;
}

DLL_List * extractFromList(DLL_List *head_list, char *name){
   DLL_List * current = head_list;
   DLL_List * last = NULL;
   DLL_List * new_current;
   while (current != NULL) {
      if (strcmp(current->n->title, name) == 0){
         if (last == NULL){
            head_list = current->next;
            return current;
         }
         last->next = current->next;
         return current;
      }
      last = current;
      current = current->next;
   }

   current = head_list->parents;
   while (current != NULL) {
      new_current = current;
      while (new_current != NULL) {
         if (strcmp(new_current->n->title, name) == 0){
            if (last == NULL){
               head_list = new_current->next;
               return new_current;
            }
            last->next = new_current->next;
            return new_current;
         }
         last = new_current;
         new_current = new_current->next;
      }
      current = current->parents;
   }

   current = head_list->children;
   while (current != NULL) {
      new_current = current;
      while (new_current != NULL) {
         if (strcmp(new_current->n->title, name) == 0){
            if (last == NULL){
               head_list = new_current->next;
               return new_current;
            }
            last->next = new_current->next;
            return new_current;
         }
         last = new_current;
         new_current = new_current->next;
      }
      current = current->children;
   }
   return NULL;
}

int isInList(DLL_List *head_list, char * name){
   printf("Name is %s, \n", name);
   if( head_list == NULL ){
      return 0;
   }

   DLL_List * current = head_list;

   while (current != NULL) {
      printf("Name found %s, \n", current->n->title);
      if (strcmp(current->n->title, name) == 0){
         return 1;
      }
      current = current->next;
   }
   printf("YOYO\n");
   DLL_List * curr2 = head_list->parents;
   while (curr2 != NULL) {
      DLL_List * curr21 = curr2;
      while (curr21 != NULL) {
         printf("Name found 2 %s, \n", curr21->n->title);
         if (strcmp(curr21->n->title, name) == 0){
            return 1;
         }
         curr21 = curr21->next;
      }
      curr2 = curr2->parents;
   }

   printf("YOYO\n");
   DLL_List * curr3 = head_list->children;
   while (curr3 != NULL) {
      DLL_List * curr31 = curr3;
      while (curr31 != NULL) {
         printf("Name found 3 %s, \n", curr31->n->title);
         if (strcmp(curr31->n->title, name) == 0){
            return 1;
         }
         curr31 = curr31->next;
      }
      curr3 = curr3->children;
   }

   return 0;
}

DLL_List * getFromList(DLL_List *head_list, char * name){
   DLL_List * current = head_list;
   while (current != NULL) {
      if (strcmp(current->n->title, name) == 0){
         return current;
      }
      current = current->next;
   }
   DLL_List * new_current;
   current = head_list->parents;
   while (current != NULL) {
      new_current = current;
      while (new_current != NULL) {
         if (strcmp(new_current->n->title, name) == 0){
            return new_current;
         }
         new_current = new_current->next;
      }
      current = current->parents;
   }
   current = head_list->children;
   while (current != NULL) {
      new_current = current;
      while (new_current != NULL) {
         if (strcmp(new_current->n->title, name) == 0){
            return new_current;
         }
         new_current = new_current->next;
      }
      current = current->children;
   }
   return NULL;
}

void addParents(DLL_List *node, DLL_List *parent){

   if(node->parents == NULL){
      node->parents = parent;
   } else {
      DLL_List * current = node->parents;
      while (current->next != NULL) {
         current = current->next;
      }
      current->next = parent;
      parent->next = NULL;
   }
}

void addChildren(DLL_List *node, DLL_List *child){

   if(node->children == NULL){
      node->children = child;
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
   DLL_List * new_parents = malloc(sizeof(DLL_List));
   DLL_List * new_children = malloc(sizeof(DLL_List));
   Node * new_Node = malloc(sizeof(Node));

   memcpy(new_Node->title, title, sizeof(new_Node->title));
   memcpy(new_Node->type, type, sizeof(new_Node->type));

   new_DLL->n = new_Node;
   new_DLL->children = NULL;
   new_DLL->parents = NULL;
   new_DLL->next = NULL;
   //printDLL_List(new_DLL);
   return new_DLL;
}

json_object * build_json(json_object * parent , DLL_List * tree){

   json_object_object_add(parent, "Action", json_object_new_string(tree->n->title));
   json_object_object_add(parent, "Type", json_object_new_string(tree->n->type));


   DLL_List * new_tree = tree->children;
   if( new_tree != NULL ){
      json_object *children = json_object_new_array();
      json_object_object_add(parent, "Child", children);
      while (new_tree != NULL) {
         json_object *tmp_root = json_object_new_object();
         json_object_array_add(children, build_json(tmp_root, new_tree));
         new_tree = new_tree->next;
      }
   }

   return parent;
}

void create_Json_file(DLL_List * wholeTree){

   printf(" NAME FINAL IS %s\n", wholeTree->n->title);
   const char *filename = "StructureTestingParser.json";
   json_object *root = json_object_new_object();

   // FULL RECURSIF PLEASE
   DLL_List * new_tree = wholeTree;
   json_object * new_root = build_json(root, new_tree);

   if (json_object_to_file_ext(filename, new_root, JSON_C_TO_STRING_PRETTY))
      printf("Error: failed to save %s!!\n", filename);
   else
      printf("%s saved.\n", filename);

   // cleanup and exit
   json_object_put(root);
}

///////////////////////
int parser(char * toParse) {
   size_t size = strlen(toParse) + 1;
   char * RawText = malloc(size * sizeof(char));
   memcpy(RawText, toParse, size);
   printf("###\n");
   printf("TEXT IS HERE '%s'\n", RawText);
   char delim[] = "\n\v";
   char delim2[] = " \t";
   char delim3[] = " \t-";
   char delim4[] = " \t->{},";
   char delim5[] = " \t,} ";

   char *saveptr;
   char *saveptr2;

	char *ptr = strtok_r(RawText, delim, &saveptr);

   DLL_List * whole_list = NULL;
   printf("!!!!!!!\n");

	while (ptr != NULL && !is_empty(ptr))	{
      
      size_t size2 = strlen(ptr) + 1;
      char *ptr_copy = malloc(size2 * sizeof(char));
      memcpy(ptr_copy, ptr, size2);
      char *ptr2 = strtok_r(ptr_copy, delim2, &saveptr2);

      if(ptr2 != NULL) {

         char *ptr3 = strtok_r(NULL, delim3, &saveptr2);         

         DLL_List * dll_node;
         if( isInList(whole_list, ptr2) == 0){
            //printf("TEP \n");
            dll_node = createDLLNode(ptr2, ptr3);
            whole_list = addToEndList(whole_list, dll_node);
            //printDLL_List(whole_list);
         } else {
            printf("TEP2 \n");
            dll_node = getFromList(whole_list, ptr2);
         }

         ptr2 = strtok_r(NULL, delim4, &saveptr2);

         while (ptr2 != NULL && !is_empty(ptr2))   {
            
            printf("INTEP 3\n");
            DLL_List * tmp_dll;
            if( isInList(whole_list, ptr2) == 0 ){
               tmp_dll = createDLLNode(ptr2, "");
               //whole_list = addToEndList(whole_list, tmp_dll);
            } else {
               printf("TEP 4\n");
               tmp_dll = extractFromList(whole_list, ptr2);
            }

            printf("DLLL 3\n");
            //printDLL_List(dll_node);
            printf("we have : %s with : %s\n", dll_node->n->title, tmp_dll->n->title);
            addChildren(dll_node, tmp_dll);
            addParents(tmp_dll, dll_node);

            ptr2 = strtok_r(NULL, delim5, &saveptr2);

            //printf("BBBBBBBBBBBb\n");
         }

      }
      ptr = strtok_r(NULL, delim, &saveptr);
      printf("OOOOOOOOOOOOOO\n");
	}


   /*###########*/
   printf("ENNNNNNNND\n");
   printDLL_List(whole_list);

   create_Json_file(whole_list);

   /*###########*/

   printf("###############\n");
	return 0;
}
