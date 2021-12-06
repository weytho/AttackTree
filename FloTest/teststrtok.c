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
      //printf("here delim11 : %s\n", ptr);
      size_t size2 = strlen(ptr) + 1;
      char *ptr_copy = malloc(size2 * sizeof(char));
      memcpy(ptr_copy, ptr, size2);

      char *ptr2 = strtok_r(ptr_copy, delim3, &saveptr2);
      //printf("here delim22 : %s\n", ptr2);

      char *ptr3 = strtok_r(NULL, delim3, &saveptr2);
      //printf("here delim33 : %s\n", ptr3);

      char *ptr4 = strtok_r(NULL, delim4, &saveptr2);
      while(ptr4 != NULL){
         //printf("here delim44 : %s\n", ptr4);
         ptr4 = strtok_r(NULL, delim4, &saveptr2);
      }
      //printf("here pnt : %s\n", saveptr);
      ptr = strtok_r(NULL, delim2, &saveptr);
      
   }

   free(RawText);

   char *saveptr3;
   char *saveptr4;

   char delim5[] = "\t\r\n\v\f";
   char delim6[] = ": \t\r\n\v\f";
   char delim7[] = ":= \t\r\n\v\f";
   char delim8[] = ":=, \t\r\n\v\f";

   printf("TEXT IS HERE '%s'\n", prop_text);
   size_t prop_size = strlen(prop_text) + 1;
   char * new_prop_text = malloc(prop_size * sizeof(char));
   memcpy(new_prop_text, prop_text, prop_size);

   char *new_ptr = strtok_r(prop_text, delim5, &saveptr3);

   while(new_ptr != NULL){

      size_t size2 = strlen(new_ptr) + 1;
      char *n_ptr_copy = malloc(size2 * sizeof(char));
      memcpy(n_ptr_copy, new_ptr, size2);

      printf("here we have : %s\n", new_ptr);
      new_ptr = strtok_r(n_ptr_copy, delim6, &saveptr4);

         ////
      printf("here we have : %s\n", new_ptr);
      new_ptr = strtok_r(NULL, delim7, &saveptr4);
         ////

      while(new_ptr != NULL){

         printf("here2 we have : %s\n", new_ptr);

         new_ptr = strtok_r(NULL, delim8, &saveptr4);
         printf("here2 we have : %s\n", new_ptr);
         
         new_ptr = strtok_r(NULL, delim7, &saveptr4);

      }

      //printf("here2 we have : %s\n", new_ptr);
      new_ptr = strtok_r(NULL, delim5, &saveptr3);
      
   }

   char *saveptr5;
   char delim_lines[] = ":";

   printf("TEXT IS HERE '%s'\n", new_prop_text);
   int count = 0;
   char *length_runner = strtok_r(new_prop_text, delim_lines, &saveptr5);

   while(length_runner != NULL){
      count = count + 1;
      printf("YOOOOOO we have : %s\n", length_runner);
      length_runner = strtok_r(NULL, delim_lines, &saveptr5);
   }

   printf(" COUNT : %d\n", count);
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
   char b[]= " \
   F13 : cost = 10, proba = 1.0 \n \
   F12 : cost = 10, proba = 1.0 \
   ";
   char c[]= "blahblahblah";

   int r = parser(a, b, c);
	return 0;
}