#include<stdio.h>
#include<json-c/json.h>
#include <string.h>
#include <stdlib.h>
//#include "structures.c"
#include "grammar.c"
#include <ctype.h>

int main (int argc, char * argv[]) { 
	printf("STARTING TEST \n");

   char a[]= " \
   D3 -OR-> {F3, R, S} \n \
   F3 -AND-> {F12} \n \
   R -AND-> {F12} \n \
   S -OR-> {F12} \n \
   R -OR-> {F13}\
   ";
   char b[]= " \
   F13 : {cost = 10, proba = 1.0 }\n \
   F12 : {cost = 10, proba = 1.0} \
   ";
   char c[]= "blahblahblah";

   Node * new_Node = malloc(sizeof(Node));

   char * test;
   test = "0.5";
   char *end2;

   new_Node->prob = strtod(test, &end2);

   //memcpy(new_Node->prob, ptr_prop, sizeof(n_prop->Name));

   printf("VALLLLLLLL !%lf! \n", new_Node->prob);

   double number;
   char myNumber[10] = "3113.14";
   number = strtod(myNumber,NULL);
   printf("%lf\n", number);


	return 0;
}