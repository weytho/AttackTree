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

// https://stackoverflow.com/questions/122616/how-do-i-trim-leading-trailing-whitespace-in-a-standard-way
// Note: This function returns a pointer to a substring of the original string.
// If the given string was allocated dynamically, the caller must not overwrite
// that pointer with the returned value, since the original pointer must be
// deallocated using the same allocator with which it was allocated.  The return
// value must NOT be deallocated using free() etc.
char *trimwhitespace(char *str)
{
   if(str == NULL){
      return NULL;
   }
   char *end;
   // Trim leading space
   while(isspace((unsigned char)*str)) str++;
   if(*str == 0)  // All spaces?
      return str;
   // Trim trailing space
   end = str + strlen(str) - 1;
   while(end > str && isspace((unsigned char)*end)) end--;
   // Write new null terminator character
   end[1] = '\0';
   return str;
}

///////////////////////
int parser(char * toParse, char * prop_text, char * counter_text, char * filename) {

   setlocale(LC_NUMERIC, "C");

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
   printf("ptr =%s\n", ptr);

	while (ptr != NULL) {

      if(!is_empty(ptr)){
         
         size_t size2 = strlen(ptr) + 1;
         char *ptr_copy = malloc(size2 * sizeof(char));
         memcpy(ptr_copy, ptr, size2);
         char *ptr2 = trimwhitespace(strtok_r(ptr_copy, delim3, &saveptr2));
         printf("ptr2 =%s\n", ptr2);

         if(ptr2 != NULL) {

            char *ptr3 = trimwhitespace(strtok_r(NULL, delim3, &saveptr2));
            printf("ptr3 =%s\n", ptr3);      

            ptr2 = trimwhitespace(strtok_r(NULL, delim4, &saveptr2));

            // TRIMMMMMMMMMM TODO !!!!

            while (ptr2 != NULL )   {
               if (!is_empty(ptr2)) {
                  printf("newptr2 =%s\n", ptr2);
               }
               ptr2 = trimwhitespace(strtok_r(NULL, delim4, &saveptr2));
               
            }
         }
      }
      printf("end = %s\n", ptr);
      ptr = strtok_r(NULL, delim2, &saveptr);
	}
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

   char a[]= " node is good   k - AND -> { node0 ,node1, node2 le bo } \
node0 -OR-> {node00,node01,node02} \
node00 -AND-> {node000,node001,node002} \
node000 -SAND-> {node0000,node0001} \
node001 -OR-> {node0010,node0011,node0012,node000} \
node0011 -OR-> {node00110,node00111,node00112,node000} \
node01 -SAND-> {node010,node011,node012}";
   char b[]= " CM1 (node20,node2) \
CM2 (node,node2) \
CM3 (node120,node20)";
   char c[]= " node00:{cost = 4,prob = 1.0} \
node01:{cost = 2,prob = 1.0} \
node10:{cost = 1,prob = 1.0} \
node11:{cost = 6,prob = 1.0}";

   int r = parser(a, " ", " ", "test");
	return 0;
}