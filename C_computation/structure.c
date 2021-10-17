#include<stdio.h>
#include<json-c/json.h>

void JsonReader(struct json_object *parsed_json){
   struct json_object *action;
   struct json_object *type;

   json_object_object_get_ex(parsed_json, "Node action", &action);
   json_object_object_get_ex(parsed_json, "Type", &type);
   printf("-----------\n");
   printf("Action : %s\n", json_object_get_string(action));
   printf("Type   : %s\n", json_object_get_string(type));
   if (strcmp(json_object_get_string(type), "LEAF" )){
      struct json_object *children;
      size_t n_children;
      json_object_object_get_ex(parsed_json, "Child", &children);
      n_children = json_object_array_length(children);
      printf("Nbr children : %lu\n", n_children);
      for(int i=0; i<n_children; i++){
         JsonReader(json_object_array_get_idx(children, i));
      }
   }
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
   JsonReader(parsed_json);

   return 0;
}