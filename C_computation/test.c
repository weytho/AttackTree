#include<stdio.h>
#include<string.h>
#include<json-c/json.h>
#include"structures.c"

void JsonReader(struct json_object *parsed_json, List **list, EList **edges, Formula **form, Node *parent, int root){

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
      
      for(int i=0; i<n_children; i++){
         JsonReader(json_object_array_get_idx(children, i), list, edges, form, node, 0);
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
   }
}

int main(int argc, char *argv[]) {
   
   char *path = argv[1];
   //path = "/home/flo/Desktop/Github/AttackTree/Structure/StructureGraph.json";
   printf("Path to file is : %s \n", path);
   
   //FILE *fp; 
   char buffer[1024*2];

   struct json_object *parsed_json;

   FILE *fp = fopen(path,"r");
   fread(buffer, 1024*2, 1, fp);
   fclose(fp);

   parsed_json = json_tokener_parse(buffer);
   EList *edges = NULL;
   List *list = NULL;
   Formula *form = NULL;

   JsonReader(parsed_json, &list, &edges, &form, NULL, 1);

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


   Formula* runner3 = form;
   while(runner3 != NULL){
      printf("%s",runner3->data);
      runner3 = runner3->next;
   }
   printf("\n");
   

   list_free(list);
   elist_free(edges);
   form_free(form);

   return 0;
}