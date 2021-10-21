#include<stdio.h>
#include<json-c/json.h>
#include <string.h>
#include <stdlib.h>
#include "structures.c"
// sudo apt install libjson-c-dev
// gcc -shared -Wl,-soname,testlib -o testlib.so -fPIC testC.c -ljson-c
// /bin/python3 /home/flo/Desktop/Github/AttackTree/testThread.py
// https://stackoverflow.com/questions/38661635/ctypes-struct-returned-from-library

List* JsonReader(struct json_object *parsed_json, List *list, int root){

   // READ THE JSON //
   struct json_object *action;
   struct json_object *type;
   json_object_object_get_ex(parsed_json, "Action", &action);
   json_object_object_get_ex(parsed_json, "Type", &type);

   // CREATE + FILL THE NODE
   Node *node = malloc(sizeof(Node));
   if (node == NULL){
      printf("[Node] Malloc error\n");
      return NULL;
   }
   strcpy(node->title, json_object_get_string(action));
   strcpy(node->type, json_object_get_string(type));
   node->root = root;
   if (strcmp(json_object_get_string(type), "LEAF" ))
      node->leaf = 0;
   else 
      node->leaf = 1;

   // ADD IT TO THE LIST
   if (node->root)
      list = list_create(node);
   else 
      list = list_add(list, node);

   // LOOK FOR ITS CHILDRENS
   if (node->leaf == 0) {
      struct json_object *children;
      size_t n_children;
      json_object_object_get_ex(parsed_json, "Child", &children);
      n_children = json_object_array_length(children);
      for(int i=0; i<n_children; i++){
         list = JsonReader(json_object_array_get_idx(children, i), list, 0);
      }
   }
   return list;
}


List * mainfct(char * path) {
	//path = "/home/flo/Desktop/Github/AttackTree/FloTest/test.json";
	printf("Path to file is : %s \n", path);

	FILE *fp; 
	char buffer[1024*2];

	struct json_object *parsed_json;

	fp = fopen(path,"r");
	fread(buffer, 1024*2, 1, fp);
	fclose(fp);

	parsed_json = json_tokener_parse(buffer);
	List *list = JsonReader(parsed_json, list, 1);

	printf("Node : %s \n", list->data->title);

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
	return list;
}

void freeList(List *l) {
	list_free(l);
}


/*
CustomNode *getNode() {
	CustomNode *n;
	// Mutable structure needed
	CustomNode init;
	strncpy(init.name,"testnode", 10);
	init.value = 13;
	init.c = 10;
	n = malloc(sizeof(CustomNode));
	*n = init;
  	return n;
}

CustomList *getList() {
	//printf("heheheh");
	CustomList *l;
	CustomList init;
	//printf("pointer is %p\n", (void *) getNode());
	init.value = 666;
	init.data = getNode();
	init.next = NULL;
	//printf("pointer is %p\n", (void *) init.next);
	l = malloc(sizeof(CustomList));
	*l = init;
  	return l;
}

void freeNode(CustomNode *n) {
	free(n);
}

void freeList(CustomList *l) {
	CustomList* tmp;
   	while (l != NULL)
    {
       tmp = l;
	   free(tmp->data);
       l = l->next;
       free(tmp);
    }
}
*/

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
