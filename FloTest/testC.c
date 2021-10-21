#include<stdio.h>
#include<json-c/json.h>
#include <string.h>
#include <stdlib.h>
#include "structures.c"
// sudo apt install libjson-c-dev
// gcc -shared -Wl,-soname,testlib -o testlib.so -fPIC testC.c -ljson-c
// /bin/python3 /home/flo/Desktop/Github/AttackTree/testThread.py
// https://stackoverflow.com/questions/38661635/ctypes-struct-returned-from-library

typedef struct full_List FList;
struct full_List {
   List *nl;
   EList *el;
};

void JsonReader(struct json_object *parsed_json, List **list, EList **edges, Node *parent, int root){

   // READ THE JSON //
   struct json_object *action;
   struct json_object *type;
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
   else 
      node->leaf = 1;

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

   // LOOK FOR ITS CHILDRENS
   if (node->leaf == 0) {
      struct json_object *children;
      size_t n_children;
      json_object_object_get_ex(parsed_json, "Child", &children);
      n_children = json_object_array_length(children);
      for(int i=0; i<n_children; i++){
         JsonReader(json_object_array_get_idx(children, i), list, edges, node, 0);
      }
   }
}


FList * mainfct(char * path) {
	//path = "/home/flo/Desktop/Github/AttackTree/FloTest/test.json";
	printf("Path to file is : %s \n", path);

	FILE *fp; 
	char buffer[1024*2];

	struct json_object *parsed_json;

	fp = fopen(path,"r");
	fread(buffer, 1024*2, 1, fp);
	fclose(fp);

	parsed_json = json_tokener_parse(buffer);
	EList *edges = NULL;
	List *list = NULL;
	JsonReader(parsed_json, &list, &edges, NULL, 1);
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

   	FList *fl;
	FList init;
   
   	init.el = edges;
   	init.nl = list;

   	fl = malloc(sizeof(FList));
	*fl = init;

   	return fl;
}

void freeList(List *l) {
	list_free(l);
}

void freeEList(EList *l) {
	elist_free(l);
}

int main (int argc, char * argv[]) { 
	printf("STARTING \n");

	char *path = "/home/flo/Desktop/Github/AttackTree/FloTest/test.json";
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
