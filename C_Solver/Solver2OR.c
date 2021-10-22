#include<stdio.h>
#include<json-c/json.h>
#include<string.h>
#include"truthStructure.c"

List* Solver(struct json_object *parsed_json, List *list, int truth, int departOR, int lenOR){
   // READ THE JSON //
   struct json_object *action;
   struct json_object *type;
   json_object_object_get_ex(parsed_json, "Action", &action);
   json_object_object_get_ex(parsed_json, "Type", &type);

   // CHECK TYPE OF NODE 
   // printf("[SOLVER] CHECK TYPE OF NODE : %s\n", json_object_get_string(type));

   // LEAF NODE : CREATION OF TNODE TO WRITE ON THE TRACE
   if (!strcmp(json_object_get_string(type), "LEAF" )){

      TNode *var = malloc(sizeof(TNode));
      var->variable = json_object_get_string(action);
      if(truth == 1){
         var->truth = "true";
      }
      else{
         var->truth = "false";
      }
      // ADD IT TO THE RIGHT PLACES
      if(list == NULL){
         list = list_create(var);
      }
      else if(departOR<0){
         List * runner1 = list;
         while(runner1 != NULL){
            TNode *cp = malloc(sizeof(TNode));
            memcpy(cp,var,sizeof(TNode));
            if(runner1->data == NULL)
            {
               runner1->data = cp;
               runner1 = runner1->next;
            }
            else {
               TNode *runner2 = runner1->data;
               while(runner2->next != NULL){
                  runner2 = runner2->next;
               }
               runner2->next = cp;
               runner1 = runner1->next;
            }
         }
         free(var);
      }
      else{
         List * runner1 = list;
        for(int i=0; i<departOR;i++){
            runner1=runner1->next;
        }

        int cnt = 0;
        while(runner1 != NULL && cnt <lenOR){
            TNode *cp = malloc(sizeof(TNode));
            memcpy(cp,var,sizeof(TNode));
            if(runner1->data == NULL)
            {
               runner1->data = cp;
               runner1 = runner1->next;
            }
            else {
                TNode *runner2 = runner1->data;
                while(runner2->next != NULL){
                  runner2 = runner2->next;
                }
                runner2->next = cp;
                runner1 = runner1->next;
            }
            cnt++;
        }
        free(var);
      }
      return list;
   }
   else if (!strcmp(json_object_get_string(type), "SAND")){
      struct json_object *children;
      size_t n_children;
      json_object_object_get_ex(parsed_json, "Child", &children);
      n_children = json_object_array_length(children);
      for(int i=0; i<n_children; i++){
         list = Solver(json_object_array_get_idx(children, i), list, truth, departOR, lenOR);
      }
      return list;
   }
   else if (!strcmp(json_object_get_string(type), "AND" )){
      struct json_object *children;
      size_t n_children;
      json_object_object_get_ex(parsed_json, "Child", &children);
      n_children = json_object_array_length(children);
      for(int i=0; i<n_children; i++){
         list = Solver(json_object_array_get_idx(children, i), list, truth, departOR, lenOR);
      }
      return list;
   }
   else if (!strcmp(json_object_get_string(type), "OR" )){
      // BRANCHING DUE TO OR STATEMENT
      int number_of_attacks = 0; // ATTENTION SI 0 ! TODO
      List *counter = list;
      while(counter != NULL){
         number_of_attacks++;
         counter = counter->next;
      }
      List *tail = list;
      List *runner = list;
      while (tail->next != NULL)
      {
         tail = tail->next;
      }

      // COPIE DES ATTAQUES
      for(int i=0; i<number_of_attacks;i++) // TODO QUID SI OR AVEC PLUS QUE 2 ? -> REMETTRE LES 3 en 2
      {
         TNode *head_node = malloc(sizeof(TNode));
         memcpy(head_node, runner->data, sizeof(TNode));

         list = list_add(list, head_node);
         tail = tail->next;
                           
         TNode *runner2 = runner->data->next;
         TNode *runner3 = tail->data;
         while (runner2 != NULL)
         {
            TNode *new_node = malloc(sizeof(TNode));
            memcpy(new_node, runner2, sizeof(TNode));
            runner3->next = new_node;
            runner2 = runner2->next;
            runner3 = runner3->next;            
         }
         runner = runner->next;
      }

      struct json_object *children;
      size_t n_children;
      json_object_object_get_ex(parsed_json, "Child", &children);
      n_children = json_object_array_length(children);
      for(int i=0; i<n_children; i++){
        list = Solver(json_object_array_get_idx(children, i), list, 1,i*number_of_attacks, number_of_attacks); // HERE TO DO REGARDING (departOR, lenOR)
        list = Solver(json_object_array_get_idx(children, i), list, 0,(1-i)*number_of_attacks, number_of_attacks);
      }
      return list;
   }
   else{
      // PROBLEME
      return list;
   }
}

int main(int argc, char *argv[]) {
   
   char *path = argv[1];
   printf("Path to file is : %s \n", path);
   
   FILE *fp; 
   char buffer[1024*2];

   struct json_object *parsed_json;

   fp = fopen(path,"r");
   fread(buffer, 1024*2, 1, fp);
   fclose(fp);
   List *list = NULL;
   List *ret = NULL;
   parsed_json = json_tokener_parse(buffer);
   ret = Solver(parsed_json, list, 1,-1, 0);

   List* runner = ret;
   int count = 0;
   while(runner != NULL){
      count ++;
      printf("Attaque numéro : %d \n", count);
      TNode *runner2 = runner->data;
      while (runner2 != NULL)
      {
         printf("Variable : %s | truth : %s\n", runner2->variable,runner2->truth);
         runner2 = runner2->next;
      }
      runner = runner->next;
   }
   list_free(list);
   list_free(ret);

   return 0;
}