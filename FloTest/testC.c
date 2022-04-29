/**
*  @file
*/
#include<stdio.h>
#include<json-c/json.h>
#include <string.h>
#include <stdlib.h>
//#include "structures.c"
#include "grammar.c"
#include <ctype.h>
#include <locale.h>
// sudo apt install libjson-c-dev
// gcc -shared -Wl,-soname,testlib -o testlib.so -fPIC testC.c -ljson-c
// /bin/python3 /home/flo/Desktop/Github/AttackTree/testThread.py
// https://stackoverflow.com/questions/38661635/ctypes-struct-returned-from-library

typedef struct full_List FList;
struct full_List {
   List *nl;
   EList *el;
   Formula *fo;
   Formula *fo_cm;
};


void freeList(List *l) {
	list_free(l);
}

void freeEList(EList *l) {
	elist_free(l);
}

void freeForm(Formula *l) {
	form_free(l);
}

/**
*  This function is in charge of reading the tree from a Json format as described in the documentation. 
*  It goes through the Json file recursively to read the nodes and iterate on their childrens. 
*  arguments-----
*  parsed_json : the json parsed 
*  list : The list of nodes
*  edges : The list of edges
*  form : The list representng the formula of the leaves
*  parent : The parent of the actual node (to create the edges)
*  root : 1 if the node is the root of the tree, should be always set to 1
*  CMfomrula : 1 to add the CM leaf to the boolean formula
*/


CostProb * JsonReader(struct json_object *parsed_json, List **list, EList **edges, Formula **form, Node *parent, int root, int CMformula){

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
         struct json_object *CMprob;
         CMchild = json_object_array_get_idx(CM, cnt);
         json_object_object_get_ex(CMchild, "CMtitle", &CMtitle);
         bool hasCost = json_object_object_get_ex(CMchild, "CMcost", &CMcost);
         bool hasProb = json_object_object_get_ex(CMchild, "CMprob", &CMprob);
         //totCMcost += json_object_get_int(CMcost);

         // ADD CM to nodes
         Node *CMnode = malloc(sizeof(Node));
         if (CMnode == NULL){
            printf("[Node] Malloc error\n");
         }
         char buf[101];
         snprintf(buf, sizeof(buf), "%s_%s", json_object_get_string(CMtitle), json_object_get_string(action));
         strcpy(CMnode->title, buf);
         strcpy(CMnode->variable, json_object_get_string(CMtitle));
         strcpy(CMnode->type, "CntMs");
         if (hasCost){
            CMnode->cost = json_object_get_int(CMcost);
         } else {
            CMnode->cost = 0;
         }
         CMnode->leaf = 1;
         CMnode->root = 0;
         CMnode->CM = 0;
         if (hasProb){
            CMnode->prob = json_object_get_double(CMprob);
         } else {
            CMnode->prob = 1.0;
         }
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

         if(CMformula == 1){
            // ADD CM to formula
            if (cnt == 0){
               Formula *left = formula("LEFT");
               Formula *not = formula("NOT");
               Formula *left2 = formula("LEFT");
               left->next = not;
               not->next = left2;
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
            }
            Formula *newVar = malloc(sizeof(Formula));
            newVar->data = json_object_get_string(CMtitle);
            newVar->next = NULL;
            Formula *runner = *(form);
            while(runner->next != NULL){
               runner = runner->next;
            }
            runner->next = newVar;

            Formula *next = NULL;
            if (cnt < CMlength - 1){
               next = formula("OR");         
            }
            else{
               next = formula("RIGHT");
               next->next = formula("AND");
            }

            runner = *(form);
            while(runner->next != NULL){
               runner = runner->next;
            }
            runner->next = next;
         }

         cnt++;
      }
   }

   // CREATE + FILL THE NODE
   Node *node = malloc(sizeof(Node));
   if (node == NULL){
      printf("[Node] Malloc error\n");
   }
   char * type_string = json_object_get_string(type);
   strcpy(node->title, json_object_get_string(action));
   strcpy(node->variable, json_object_get_string(action));
   strcpy(node->type, type_string);
   node->root = root;
   
   node->CM = 0;
   if(CM != NULL){
      int CMlength = json_object_array_length(CM);
      if(CMlength >0){
         node->CM = 1;
      }
   }

   if (strcmp(type_string, "LEAF" )){
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
      Formula *left = formula("LEFT");
      if (strcmp(type_string, "NOT") == 0) {
         Formula *left2 = formula("LEFTNOT");
         left->next = left2;
      }

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
         CostProb *ret = JsonReader(json_object_array_get_idx(children, i), list, edges, form, node, 0, CMformula);
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
            Formula *t = formula(type_string);
            Formula *runner = *(form);
            while(runner->next != NULL){
               runner = runner->next;
            }
            runner->next = t; 
         }
         free(ret);
      }

      Formula *right = formula("RIGHT");
      Formula *runner = *(form);
      while(runner->next != NULL){
         runner = runner->next;
      }
      runner->next = right;   

      if(!strcmp(type_string, "OR" )) {
         node->cost = or_cost + totCMcost;
         node->prob = or_prob;
      }
      else{
         node->cost = and_cost + totCMcost;
         node->prob = and_prob;
      }
   }

   if(CMformula == 1){
      if(CM != NULL){
      Formula *right = formula("RIGHT");
      Formula *runner = *(form);
      while(runner->next != NULL){
         runner = runner->next;
      }
      runner->next = right;  
      }
   }

   //printf("[Node] Title : %s\n",node->title);
   CostProb *retval = malloc(sizeof(CostProb));
   retval->cost = node->cost;
   retval->prob = node->prob;
   retval->esp = esp(node->cost, node->prob);

   return retval;
}


FList * mainfct(char * path, int with_cm) {
	//path = "/home/flo/Desktop/Github/AttackTree/FloTest/StructureGraph.json";
	printf("Path to file is : %s \n", path);

	FILE *fp; 
	struct json_object *parsed_json;
	fp = fopen(path,"r");  

   fseek(fp, 0, SEEK_END);
   long size = ftell(fp);
   fseek(fp, 0, SEEK_SET);
   char buffer[size];
	fread(buffer, size, 1, fp);
	fclose(fp);
	parsed_json = json_tokener_parse(buffer);

	EList *edges = NULL;
	List *list = NULL;
   Formula *form = NULL;

   CostProb *ret = JsonReader(parsed_json, &list, &edges, &form, NULL, 1, 0);

   freeList(list);
   freeEList(edges);

   edges = NULL;
	list = NULL;
   Formula *form_with_cm = NULL;

   ret = JsonReader(parsed_json, &list, &edges, &form_with_cm, NULL, 1, 1);

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
   init.fo_cm = form_with_cm;

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

json_object * build_json(json_object * parent , DLL_List * tree, int boolean_mode, HashTable *ht_CM){

   //printDLL_total(tree);

   json_object_object_add(parent, "Action", json_object_new_string(tree->n->title));
   json_object_object_add(parent, "Type", json_object_new_string(tree->n->type));

   // TODO vérifier autrement
   if(boolean_mode == 0){
      json_object_object_add(parent, "Cost", json_object_new_int(tree->n->cost));
      json_object_object_add(parent, "Prob", json_object_new_double(tree->n->prob));
   }

   //json_object_object_add(parent, "CM", json_object_new_array());

   if(ht_CM != NULL){
      int i = NameIndex(ht_CM, tree->n->title);//current->n->title);
      printf("NAME IS  :: = ((%s)) \n", tree->n->title);
      NodeP * Nn = getH(ht_CM, i);
      printf("NAME NODE P IS  :: = ((%s)) \n", Nn->Name);
      if(Nn != NULL){

         NodeCM * CM_list = Nn->CMlist;
         if( CM_list != NULL ){
            json_object *counter = json_object_new_array();
            json_object_object_add(parent, "CM", counter);
            while (CM_list != NULL) {
               json_object *tmp_root_cm = json_object_new_object();
               //char buf[101];
               //snprintf(buf, sizeof(buf), "%s_%s", CM_list->CMtitle, Nn->Name);
               json_object_object_add(tmp_root_cm, "CMtitle", json_object_new_string(CM_list->CMtitle));
               printf("NAME :: = (%s) \n", CM_list->CMtitle);
               if(boolean_mode == 0){
                  printf("COST = %d \n", CM_list->cost);
                  printf("PROB = %f \n", CM_list->prob);
                  json_object_object_add(tmp_root_cm, "CMcost", json_object_new_int(CM_list->cost));
                  json_object_object_add(tmp_root_cm, "CMprob", json_object_new_double(CM_list->prob));
               }
               json_object_array_add(counter, tmp_root_cm);
               CM_list = CM_list->next;
            }
         }
         //deleteH(ht_CM, Nn);
         //displayH(ht_CM);
      }
   }

   DLL_List * new_tree = tree->children;
   if( new_tree != NULL ){
      json_object *children = json_object_new_array();
      json_object_object_add(parent, "Child", children);
      while (new_tree != NULL) {
         json_object *tmp_root = json_object_new_object();
         json_object_array_add(children, build_json(tmp_root, new_tree, boolean_mode, ht_CM));
         new_tree = new_tree->next;
      }
   }

   return parent;
}

void create_Json_file(DLL_List * wholeTree, int boolean_mode, HashTable *ht_CM, char *filename){

   printf(" NAME FINAL IS %s\n", wholeTree->n->title);
   //const char *filename = "res/StructureTestingParser.json";
   json_object *root = json_object_new_object();

   // Clean file
   fclose(fopen(filename, "w"));

   // FULL RECURSIF PLEASE
   DLL_List * new_tree = wholeTree;
   json_object * new_root = build_json(root, new_tree, boolean_mode, ht_CM);

   if (json_object_to_file_ext(filename, new_root, JSON_C_TO_STRING_PRETTY))
      printf("Error: failed to save %s!!\n", filename);
   else
      printf("%s saved.\n", filename);

   // cleanup and exit
   json_object_put(root);
}

///////////////////////
int parser(char * toParse, char * prop_text, char * counter_text, char * filename) {
   if(toParse == NULL || is_empty(toParse)){
      return 1;
   }
   int boolean_mode = 0;

   if(is_empty(prop_text)){
      printf("BOOLEAN MODE \n");
      boolean_mode = 1;
   }
   setlocale(LC_NUMERIC, "C");

   struct HashTable *ht_properties = NULL;
   struct HashTable *ht_CM = NULL;

   if(boolean_mode == 0){
      printf("BOOLEAN MODE 000\n");
      ht_properties = parse_properties(prop_text);

   }


   if(!is_empty(counter_text)){

      ht_CM = parse_countermeasures(counter_text, ht_properties);

   }


   size_t size = strlen(toParse) + 1;
   char * RawText = malloc(size * sizeof(char));
   memcpy(RawText, toParse, size);

   printf("TEXT IS HERE '%s'\n", RawText);

   char delim2[] = "}";
   char delim3[] = "->";
   char delim4[] = "->{,";

   char *saveptr;
   char *saveptr2;

	char *ptr = strtok_r(RawText, delim2, &saveptr);

   DLL_List * whole_list = NULL;
   int parent_is_in = 0;

	while (ptr != NULL) {

      if(!is_empty(ptr)){
         
         size_t size2 = strlen(ptr) + 1;
         char *ptr_copy = malloc(size2 * sizeof(char));
         memcpy(ptr_copy, ptr, size2);
         char *ptr2 = trimwhitespace(strtok_r(ptr_copy, delim3, &saveptr2));
         replace_spaces(ptr2);
         bool is_NOT = false;
         int cnt = 0;

         if(ptr2 != NULL) {

            char *ptr3 = trimwhitespace(strtok_r(NULL, delim3, &saveptr2));   
            replace_spaces(ptr3);      
            //printf("HELLO : %s : %s\n", ptr2, ptr3);
            DLL_List * dll_node;
            if( isInList(whole_list, ptr2) == 0){
               printf("TEP \n");
               dll_node = createDLLNode(ptr2, ptr3);
               whole_list = addToEndList(whole_list, dll_node);
               //printDLL_List(whole_list);
            } else {
               printf("TEP2 \n");
               parent_is_in = 1;
               dll_node = getFromList(whole_list, ptr2);
               // TODO CHECK FOR REWRITE
               if(dll_node->children != NULL){
                  free(RawText);
                  free(ptr_copy);
                  // FREE PARENTS ?
                  DLL_free_from_top(whole_list);
                  printf("2\n");
                  return 2;
               }
               //memcpy(dll_node->n->type, ptr3, sizeof(dll_node->n->type));
               snprintf(dll_node->n->type, sizeof(dll_node->n->type), "%s", ptr3);
               if(strcmp(ptr3, "NOT") == 0){
                  is_NOT = true;
               }
            }

            ptr2 = trimwhitespace(strtok_r(NULL, delim4, &saveptr2));
            replace_spaces(ptr2);

            while (ptr2 != NULL)   {
               if (!is_empty(ptr2)) {
                  //printf("INTEP 3\n");
                  cnt = cnt + 1;
                  if( is_NOT && cnt > 1){
                     free(RawText);
                     free(ptr_copy);
                     DLL_free_from_top(whole_list);
                     printf("5\n");
                     return 5;
                  }
                  DLL_List * tmp_dll;
                  if( isInList(whole_list, ptr2) == 0 ){
                     tmp_dll = createDLLNode(ptr2, "LEAF");
                  } else {
                     printf("TEP 4\n");
                     
                     tmp_dll = getFromList(whole_list, ptr2);

                     if(strcmp(tmp_dll->n->title, dll_node->n->title) == 0){
                        free(RawText);
                        free(ptr_copy);
                        DLL_free_from_top(whole_list);
                        printf("3\n");
                        return 3;
                     }

                     if(parent_is_in == 1 && tmp_dll->children != NULL){
                        int r = cycle_check(dll_node, tmp_dll->n->title);
                        if(r != 0){
                           free(RawText);
                           free(ptr_copy);
                           DLL_free_from_top(whole_list);
                           printf("3\n");
                           return 3;
                        }
                     }

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
               }
               
               ptr2 = trimwhitespace(strtok_r(NULL, delim4, &saveptr2));
               replace_spaces(ptr2);

            }

            parent_is_in = 0;

         }
         free(ptr_copy);
      }
      ptr = strtok_r(NULL, delim2, &saveptr);
	}

   free(RawText);

   printf("ENNNNNNNND\n");
   printDLL_total(whole_list);

   if(whole_list->next != NULL){
      DLL_free_from_top(whole_list);
      printf("4\n");
      return 4;
   }

   // ADD properties

   if( boolean_mode == 0 ){
      printf("BOOLEAN MODE\n");
      displayH(ht_properties);
      set_properties_total(whole_list, ht_properties);
      //freeH(ht_properties);
   }

   // ADD countermeasures

   create_Json_file(whole_list, boolean_mode, ht_CM, filename);
   if( ht_CM != NULL ){
      freeH(ht_CM);
   }
   if (ht_properties != NULL) {
      freeH(ht_properties);
   }

   DLL_free_from_top(whole_list);

   printf("ENNNNNNNND222222222222\n");

	return 0;
}


int main (int argc, char * argv[]) { 
	printf("STARTING TEST \n");
	//char *path = "/home/flo/Desktop/Github/AttackTree/Structure/StructureGraph.json";
	//mainfct(path);
	//CustomList * l = getList();
	//CustomNode * n = getNode();
	//printf("START");
	//printf("l pointer : %p", (void *) l);
	//printf("HHHHHHHHHHHHHH %s, ",l->data->name);
	//freeNode(n);
	//freeList(l);

   char a[]= " node -AND-> {node0,node1,node2} \
node0 -OR-> {node00,node01,node02} \
node00 -AND-> {node000,node001,node002} \
node000 -SAND-> {node0000,node0001} \
node001 -OR-> {node0010,node0011,node0012,node000} \
node0011 -OR-> {node00110,node00111,node00112,node000} \
node01 -SAND-> {node010,node011,node012} \
node1 -AND-> {node10,node11} \
node10 -SAND-> {node100,node101,node102,node000} \
node102 -AND-> {node1020,node1021} \
node1021 -AND-> {node10210,node10211,node10212,node02} \
node11 -OR-> {node110,node111,node100} \
node2 -SAND-> {node20,node21,node22,node0010} \
node20 -AND-> {node200,node201,node202,node00110} \
node201 -OR-> {node2010,node2011,node200} \
node21 -OR-> {node210,node211,node212,node111} \
node22 -SAND-> {node220,node221} \
node221 -OR-> {node2210,node2211,node2212,node00}";
   char b[]= " CM1 (node20,node2) \
CM2 (node,node2) \
CM3 (node120,node20) \
CM4 (node21,node01) \
CM5 (node20,node10) ";
   char c[]= " node00:{cost = 4,prob = 1.0} \
node01:{cost = 2,prob = 1.0} \
node10:{cost = 1,prob = 1.0} \
node11:{cost = 6,prob = 1.0} \
node1200:{cost = 8,prob = 1.0} \
node1201:{cost = 8,prob = 1.0} \
node121:{cost = 7,prob = 1.0} \
node122:{cost = 9,prob = 1.0} \
node20:{cost = 1,prob = 1.0}  \
node21:{cost = 4,prob = 1.0} ";

   int r = parser(a, " ", " ", "test");
	return 0;
}