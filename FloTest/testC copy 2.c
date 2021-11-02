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

/*typedef struct treeParser TParser;
struct treeParser {
   Node *n;
   Children *n;
   int c;
};*/

typedef struct childrenLL ChildLL;
struct childrenLL {
      char name[50];
      ChildLL* next;
};

typedef struct treeLL TreeLL;
struct treeLL {
      Node* n;
      TreeLL* next;
      ChildLL* children;
};

int parser(char * toParse) {
   size_t size = strlen(toParse) + 1;
   char * RawText = malloc(size * sizeof(char));
   memcpy(RawText, toParse, size);
   printf("TEXT WAS '%s'\n", toParse);
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

   TreeLL * initTree = malloc(sizeof(TreeLL));
   TreeLL * headTree = initTree;

	while (ptr != NULL && !is_empty(ptr))
	{
      
      size_t size2 = strlen(ptr) + 1;

      char *ptr_copy = malloc(size2 * sizeof(char));
      memcpy(ptr_copy, ptr, size2);
      char *ptr2 = strtok_r(ptr_copy, delim2, &saveptr2);
      //printf("# %s\n", ptr2);
      if(ptr2 != NULL){
         Node * tmp = malloc(sizeof(Node));

         memcpy(tmp->title, ptr2, sizeof(tmp->title));

         ptr2 = strtok_r(NULL, delim3, &saveptr2);
         //printf("#2 %s\n", ptr2);
         memcpy(tmp->type, ptr2, sizeof(tmp->type));

         ptr2 = strtok_r(NULL, delim4, &saveptr2);
         //printf("#3 %s\n", ptr2);
         ChildLL * init_child = malloc(sizeof(ChildLL));
         ChildLL * headChild = init_child;
   
         while (ptr2 != NULL)
         {
            memcpy(init_child->name, ptr2, sizeof(init_child->name));
            ChildLL * tmp_child = malloc(sizeof(ChildLL));
            ptr2 = strtok_r(NULL, delim5, &saveptr2);
            if (ptr2 != NULL){
               init_child->next = tmp_child;
               init_child = tmp_child;
            }
         }

         TreeLL * tmp_tree = malloc(sizeof(TreeLL));
         initTree->n = tmp;
         initTree->children = headChild;
         initTree->next = tmp_tree;
         initTree = tmp_tree;

      }
      ptr = strtok_r(NULL, delim, &saveptr);
      
	}

   while(headTree->next != NULL){
      printf("#+++++++++++++ %s\n", headTree->n->title);
      printf("#+++ %s\n", headTree->n->type);
      printf("#++++++++ %s\n", headTree->children->name);
      while(headTree->children->next != NULL){
         printf("#++++++++ %s\n", headTree->children->next->name);
         headTree->children = headTree->children->next;
      }
      headTree = headTree->next;
   }


   printf("###############\n");
	return 0;
}
