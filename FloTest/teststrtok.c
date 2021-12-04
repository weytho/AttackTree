#include<stdio.h>
#include<json-c/json.h>
#include <string.h>
#include <stdlib.h>
//#include "structures.c"
#include "grammar.c"
#include <ctype.h>

int parser(char * toParse, char * prop_text, char * counter_text) {
   if(toParse == NULL){
      return 1;
   }
   size_t size = strlen(toParse) + 1;
   char * RawText = malloc(size * sizeof(char));
   memcpy(RawText, toParse, size);
   printf("TEXT IS HERE '%s'\n", RawText);
   char delim2[] = "}\t\r\n\v\f";
   char delim3[] = "-> \t\r\n\v\f";
   char delim4[] = "->{, \t\r\n\v\f";

   char *saveptr;
   char *saveptr2;

	char *ptr = strtok_r(RawText, delim2, &saveptr);

   while(ptr != NULL){
      printf("here delim11 : %s\n", ptr);
      size_t size2 = strlen(ptr) + 1;
      char *ptr_copy = malloc(size2 * sizeof(char));
      memcpy(ptr_copy, ptr, size2);

      char *ptr2 = strtok_r(ptr_copy, delim3, &saveptr2);
      printf("here delim22 : %s\n", ptr2);

      char *ptr3 = strtok_r(NULL, delim3, &saveptr2);
      printf("here delim33 : %s\n", ptr3);

      char *ptr4 = strtok_r(NULL, delim4, &saveptr2);
      while(ptr4 != NULL){
         printf("here delim44 : %s\n", ptr4);
         ptr4 = strtok_r(NULL, delim4, &saveptr2);
      }
      //printf("here pnt : %s\n", saveptr);
      ptr = strtok_r(NULL, delim2, &saveptr);
      
   }

   free(RawText);

	return 0;
}


int main (int argc, char * argv[]) { 
	printf("STARTING TEST \n");

   char a[]= " \
   D3 -OR-> {F3, R, S} \
   F3 -AND-> {F12} \
   R -AND-> {F12} \
   S -OR-> {F12} \
   R -OR-> {F13}\
   ";
   char b[]= "blahblahblah";
   char c[]= "blahblahblah";

   int r = parser(a, b, c);
	return 0;
}