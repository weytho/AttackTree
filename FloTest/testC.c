#include<stdio.h>
#include<json-c/json.h>
// sudo apt install libjson-c-dev
// gcc -shared -Wl,-soname,testlib -o testlib.so -fPIC testC.c -ljson-c
// /bin/python3 /home/flo/Desktop/Github/AttackTree/testThread.py

int main(char * path) {
   printf("path in C %s\n", path);
   FILE *fp;
	char buffer[1024];
	struct json_object *parsed_json;
	struct json_object *n_action;
	struct json_object *type;
	struct json_object *child;

   fp = fopen(path,"r");
	fread(buffer, 1024, 1, fp);
	fclose(fp);

   parsed_json = json_tokener_parse(buffer);

	json_object_object_get_ex(parsed_json, "Node action", &n_action);
	json_object_object_get_ex(parsed_json, "Type", &type);
	json_object_object_get_ex(parsed_json, "Child", &child);

   printf("Node action: %s\n", json_object_get_string(n_action));
   printf("Type: %s\n", json_object_get_string(type));
   printf("Child: %s\n", json_object_get_string(child));
   return 0;
}
