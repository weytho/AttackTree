#include<stdio.h>
#include<string.h>
#include<json-c/json.h>
#include<math.h>
#include"structures.c"

CostProb * JsonReader(struct json_object *parsed_json, List **list, EList **edges, Formula **form, Node *parent, int root){

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
   int CMlength = json_object_array_length(CM);
   int totCMcost = 0;
   int cnt = 0;
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

int main(int argc, char *argv[]) {
   
   char *path = argv[1];
   printf("Path to file is : %s \n", path);
   
   FILE *fp; 
   char buffer[1024*4];

   struct json_object *parsed_json;

   fp = fopen(path,"r");
   fread(buffer, 1024*4, 1, fp);
   fclose(fp);

   parsed_json = json_tokener_parse(buffer);
   EList *edges = NULL;
   List *list = NULL;
   Formula *form = NULL;
   CostProb *ret = JsonReader(parsed_json, &list, &edges, &form, NULL, 1);

   List* runner = list;
   int count = 0;
   while(runner != NULL){
      count ++;
      printf("count : %d \n", count);
      printf("Node title : %s \n", runner->data->title);
      printf("Node type  : %s \n", runner->data->type);
      printf("Node root  : %d \n", runner->data->root);
      printf("Node leaf  : %d \n", runner->data->leaf);
      printf("Node cost  : %d \n", runner->data->cost);
      printf("Node prob  : %f \n", runner->data->prob);
      printf("Node CM    : %d \n", runner->data->CM);
      runner = runner->next;
   }

   EList* runner2 = edges;
   count = 0;
   while(runner2 != NULL){
      count ++;
      printf("count : %d \n", count);
      printf("Edges parent : %s \n", runner2->data->parent);
      printf("Edges child  : %s \n", runner2->data->child);
      printf("Edges CM     : %d \n", runner2->data->CM);
      runner2 = runner2->next;
   }


   Formula* runner3 = form;
   while(runner3 != NULL){
      printf("%s",runner3->data);
      runner3 = runner3->next;
   }
   printf("\n");

   printf("Total cost is %d\n",ret->cost);
   printf("Proba  is %f\n",ret->prob);
   printf("Esp  is %f\n",ret->esp);
   

   list_free(list);
   elist_free(edges);
   form_free(form);

   return 0;
}