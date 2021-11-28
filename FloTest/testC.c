#include<stdio.h>
#include<json-c/json.h>
#include <string.h>
#include <stdlib.h>
//#include "structures.c"
#include "grammar.c"
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

CostProb * JsonReader(struct json_object *parsed_json, List **list, EList **edges, Formula **form, Node *parent, int root){
   printf("AAAAAAAAAAAAAAAAAAAAAAAAAAAA\n");
   // READ THE JSON //
   struct json_object *action;
   struct json_object *type;
   struct json_object *costleaf;
   struct json_object *probleaf;
   struct json_object *CM;
   json_object_object_get_ex(parsed_json, "Action", &action);
   json_object_object_get_ex(parsed_json, "Type", &type);
   json_object_object_get_ex(parsed_json, "CM", &CM);
   
   // Compute CM 

   int totCMcost = 0;
   int cnt = 0;
   if(CM != NULL){
      int CMlength = json_object_array_length(CM);
      while (cnt < CMlength){
         struct json_object *CMchild;
         struct json_object *CMtitle;
         struct json_object *CMcost;
         CMchild = json_object_array_get_idx(CM, cnt);
         json_object_object_get_ex(CMchild, "CMtitle", &CMtitle);
         json_object_object_get_ex(CMchild, "CMcost", &CMcost);
         totCMcost += json_object_get_int(CMcost);

         // ADD CM to nodes
         Node *CMnode = malloc(sizeof(Node));
         if (CMnode == NULL){
            printf("[Node] Malloc error\n");
         }
         strcpy(CMnode->title, json_object_get_string(CMtitle));
         strcpy(CMnode->type, "CntMs");
         CMnode->cost = json_object_get_int(CMcost);
         CMnode->leaf = 1;
         CMnode->root = 0;
         CMnode->CM = 1;
         CMnode->prob = 1;
         if (*list == NULL)
            *list = list_create(CMnode);
         else 
            *list = list_add(*list, CMnode);
         // Edge
         Edge *CMed = malloc(sizeof(Edge));
         memcpy(CMed->parent, json_object_get_string(action), sizeof(char)*50);
         memcpy(CMed->child, CMnode->title, sizeof(char)*50);
         CMed->CM = 1;
         if (*edges == NULL)
            *edges = elist_create(CMed);
         else
            *edges = elist_add(*edges, CMed);
         cnt++;
      }
   }
   
   // CREATE + FILL THE NODE
   Node *node = malloc(sizeof(Node));
   if (node == NULL){
      printf("[Node] Malloc error\n");
   }
   strcpy(node->title, json_object_get_string(action));
   strcpy(node->type, json_object_get_string(type));
   node->root = root;
   node->CM = 0;
   if (strcmp(json_object_get_string(type), "LEAF" )){
      node->leaf = 0;
      node->prob = 1;
   }
   else {
      node->leaf = 1;
      json_object_object_get_ex(parsed_json, "Cost", &costleaf);
      node->cost = json_object_get_int(costleaf) + totCMcost;
      json_object_object_get_ex(parsed_json, "Prob", &probleaf);
      node->prob = json_object_get_double(probleaf);
   }

   // ADD IT TO THE LIST
   if (*list == NULL)
      *list = list_create(node);
   else 
      *list = list_add(*list, node);

   // ADD THE EDGE
   if (node->root != 1){
      Edge *ed = malloc(sizeof(Edge));
      memcpy(ed->parent, parent->title, sizeof(char)*50);
      memcpy(ed->child, node->title,sizeof(char)*50);
      ed->CM = 0;
      if (*edges == NULL)
         *edges = elist_create(ed);
      else
         *edges = elist_add(*edges, ed);
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
      int or_cost = 0;
      double and_prob = 1;
      double or_prob  = 0;
      double esp = 999999.9;
      
      for(int i=0; i<n_children; i++){
         CostProb *ret = JsonReader(json_object_array_get_idx(children, i), list, edges, form, node, 0);
         int cost = ret->cost;
         double prob =ret->prob;
         and_cost = and_cost + cost;
         and_prob = and_prob * prob;
         if(ret->esp < esp){
            or_cost = cost;
            or_prob = prob;
            esp = ret->esp;
         }
         if(i<n_children-1){
            Formula *t = Parenthesis(json_object_get_string(type));
            Formula *runner = *(form);
            while(runner->next != NULL){
               runner = runner->next;
            }
            runner->next = t; 
         }
         free(ret);
      }

      Formula *right = Parenthesis("RIGHT");
      Formula *runner = *(form);
      while(runner->next != NULL){
         runner = runner->next;
      }
      runner->next = right;   

      if(!strcmp(json_object_get_string(type), "OR" )) {
         node->cost = or_cost + totCMcost;
         node->prob = or_prob;
      }
      else{
         node->cost = and_cost + totCMcost;
         node->prob = and_prob;
      }
   }
   printf("[Node] Title : %s\n",node->title);
   CostProb *retval = malloc(sizeof(CostProb));
   retval->cost = node->cost;
   retval->prob = node->prob;
   retval->esp = esp(node->cost, node->prob);

   return retval;
}


FList * mainfct(char * path) {
	//path = "/home/flo/Desktop/Github/AttackTree/FloTest/StructureGraph.json";
	printf("Path to file is : %s \n", path);

	FILE *fp; 
	struct json_object *parsed_json;
	fp = fopen(path,"r");  

   printf("Path to file is : %s \n", path);
   fseek(fp, 0, SEEK_END);
   long size = ftell(fp);
   fseek(fp, 0, SEEK_SET);
   char buffer[size];
	fread(buffer, size, 1, fp);
	fclose(fp);
	parsed_json = json_tokener_parse(buffer);
   printf("Path to file is : %s \n", path);
	EList *edges = NULL;
	List *list = NULL;
   Formula *form = NULL;

   CostProb *ret = JsonReader(parsed_json, &list, &edges, &form, NULL, 1);

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

   printf("Total cost is %d\n",ret->cost);
   printf("Proba  is %f\n",ret->prob);
   printf("Esp  is %f\n",ret->esp);

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
	//char *path = "/home/flo/Desktop/Github/AttackTree/Structure/StructureGraph.json";
	//mainfct(path);
	//CustomList * l = getList();
	//CustomNode * n = getNode();
	//printf("START");
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

json_object * build_json(json_object * parent , DLL_List * tree){

   printDLL_total(tree);

   json_object_object_add(parent, "Action", json_object_new_string(tree->n->title));
   json_object_object_add(parent, "Type", json_object_new_string(tree->n->type));
   //json_object_object_add(parent, "CM", json_object_new_array());

   /*DLL_List * CM_list = tree->n->CM;
   if( CM_list != NULL ){
      json_object *counter = json_object_new_array();
      json_object_object_add(parent, "CM", counter);
      while (CM_list != NULL) {
         json_object *tmp_root = json_object_new_object();
         json_object_array_add(counter, build_json(tmp_root, CM_list));
         CM_list = CM_list->next;
      }
   }*/

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

   // Clean file
   fclose(fopen(filename, "w"));

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
   char delim2[] = " \t-";
   char delim3[] = " \t->";
   char delim4[] = " \t->{},";
   char delim5[] = " \t,}";

   char *saveptr;
   char *saveptr2;

	char *ptr = strtok_r(RawText, delim, &saveptr);

   DLL_List * whole_list = NULL;

	while (ptr != NULL && !is_empty(ptr))	{
      
      size_t size2 = strlen(ptr) + 1;
      char *ptr_copy = malloc(size2 * sizeof(char));
      memcpy(ptr_copy, ptr, size2);
      char *ptr2 = strtok_r(ptr_copy, delim2, &saveptr2);

      if(ptr2 != NULL) {

         char *ptr3 = strtok_r(NULL, delim3, &saveptr2);         

         DLL_List * dll_node;
         if( isInList(whole_list, ptr2) == 0){
            printf("TEP \n");
            dll_node = createDLLNode(ptr2, ptr3);
            whole_list = addToEndList(whole_list, dll_node);
            //printDLL_List(whole_list);
         } else {
            printf("TEP2 \n");
            dll_node = getFromList(whole_list, ptr2);
            memcpy(dll_node->n->type, ptr3, sizeof(dll_node->n->type));
         }

         ptr2 = strtok_r(NULL, delim4, &saveptr2);

         while (ptr2 != NULL && !is_empty(ptr2))   {
            
            //printf("INTEP 3\n");
            DLL_List * tmp_dll;
            if( isInList(whole_list, ptr2) == 0 ){
               tmp_dll = createDLLNode(ptr2, "LEAF");
            } else {
               printf("TEP 4\n");
               
               tmp_dll = getFromList(whole_list, ptr2);

               if(tmp_dll->parents == NULL){
                  tmp_dll = extractFromList(&whole_list, ptr2);
                  // Pas suffisant
                  tmp_dll->next = NULL;
               } else {
                  printf("TEP 8\n");
                  DLL_List * new_tmp_dll = malloc(sizeof(DLL_List));
                  new_tmp_dll->n = tmp_dll->n; //copy_node(tmp_dll->n); //tmp_dll->n;
                  new_tmp_dll->children = tmp_dll->children;
                  new_tmp_dll->parents = tmp_dll->parents;
                  new_tmp_dll->next = NULL;
                  tmp_dll = new_tmp_dll;

               }
            }

            //printf("DLLL 3\n");
            printf("we have : %s with : %s\n", dll_node->n->title, tmp_dll->n->title);
            
            // TODO REFAIRE PLUS PROPREMENT
            //printf("ADD CHILDREN\n");

            addChildren(dll_node, tmp_dll, whole_list);

            //printDLL_total(whole_list);

            //printf("ADD PARENTS\n");
            
            addParents(tmp_dll, dll_node);

            //printDLL_total(whole_list);

            ptr2 = strtok_r(NULL, delim5, &saveptr2);
         }

      }
      ptr = strtok_r(NULL, delim, &saveptr);
      free(ptr_copy);
	}

   free(RawText);


   /*###########*/
   printf("ENNNNNNNND\n");
   printDLL_total(whole_list);
   create_Json_file(whole_list);

   DLL_free_from_top(whole_list);
   /*###########*/
   printf("###############\n");
	return 0;
}