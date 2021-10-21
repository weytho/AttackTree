#include<stdio.h>
#include<json-c/json.h>
#include"structures.c"

List* JsonReader(struct json_object *parsed_json, List *list, int root){

   // READ THE JSON //
   struct json_object *action;
   struct json_object *type;
   json_object_object_get_ex(parsed_json, "Action", &action);
   json_object_object_get_ex(parsed_json, "Type", &type);

    // CHECK TYPE OF NODE 

    // CHECK TRUTH NECESSITY

    // ASK THE FOLLOWING NODES TO RESPECT THAT TRUTH (if not leaf)

    // RETURN A LIST OF THE POSSIBILITIES 

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

int main(int argc, char *argv[]) {
   
   char *path = argv[1];
   printf("Path to file is : %s \n", path);
   
   FILE *fp; 
   char buffer[1024];

   struct json_object *parsed_json;

   fp = fopen(path,"r");
   fread(buffer, 1024, 1, fp);
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

   return 0;
}