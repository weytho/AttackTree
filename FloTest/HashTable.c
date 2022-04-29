/**
*  @file
*  C HashTable with functions 
*/
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>

typedef struct NodeCountermeasure NodeCM;
struct NodeCountermeasure {
   char CMtitle [50];
   int cost;
   double prob;
   NodeCM * next;
};

typedef struct NodeProperty NodeP;
struct NodeProperty {
   char Name [50];
   int cost;
   double prob;
   NodeCM * CMlist;
};

/**
*  Main hastable structure 
*/
typedef struct HashTable HashTable;
struct HashTable {
   int size;
   int numberElem;
   int * hashArray;
   NodeP * NodeArray;
};

// function prototype
static void insertH(HashTable *h, NodeP *n);

/**
*  hastable constructor
*  argument----
*  The size of the initial HashTable 
*  The system can resize by growing the size but try tom aim at the good size directly.
*/
HashTable * newHastable(int size) {
   if (size <=0){
      return NULL;
   }
   HashTable * h = malloc(sizeof(struct HashTable));
   if(h){
      h->size = size;
      h->numberElem = 0;
      h->hashArray = malloc(sizeof(int)*size);
      for(int i = 0; i<h->size; i++) {
         h->hashArray[i] = -1;
      }
      h->NodeArray = malloc(sizeof(NodeP)*size);
      return h;
   }
   else {
      return NULL;
   }
}

/**
*  Hash the key wih the size of the table 
*/
int hashCodeH(HashTable *h, int key) {
   return key % h->size;
}

/**
*  Returns an integer value of the name of the NodeP 
*/
int NodePKey(NodeP *n) {
   if (n->Name == NULL){
      printf("No name initialized for NodeP\n");
      return -1;
   }
   int cnt = 0;
   int sum = 0;
   while(n->Name[cnt] != '\0'){
      sum = sum + (int) n->Name[cnt];
      cnt++;
   }
   return sum;
}

/**
*  Returns the index of the NodeP in the HashTable
*/
int NodeIndex(HashTable *h, NodeP *n) {
   //get the hash 
   int key = NodePKey(n);
   if(key<0){
      printf("Negative key for NodeP\n");
      return -1;
   }
   int hashIndex = hashCodeH(h,key);  
   
   //move in array until an empty 
   while(h->hashArray[hashIndex] != -1) {
      if(h->hashArray[hashIndex] >= 0){
         int cmp = strcmp(n->Name,h->NodeArray[hashIndex].Name);
         if(cmp == 0){
            return hashIndex;
         }
      }
      //go to next cell
      ++hashIndex;
      
      //wrap around the table
      hashIndex %= h->size;
   }        
   return -1;        
}

/**
*  Returns an integer value of the Name 
*/
int NamePKey(char * Name) {
   int cnt = 0;
   int sum = 0;
   while(Name[cnt] != '\0'){
      sum = sum + (int) Name[cnt];
      cnt++;
   }
   return sum;
}

/**
*  Returns the index of the Name in the HashTable
*/
int NameIndex(HashTable *h, char * Name) {
   //get the hash 
   int key = NamePKey(Name);
   if(key<0){
      printf("Negative key for NodeP\n");
      return -1;
   }
   int hashIndex = hashCodeH(h,key);  
   
   //move in array until an empty 
   while(h->hashArray[hashIndex] != -1) {
      if(h->hashArray[hashIndex] >= 0){
         int cmp = strcmp(Name,h->NodeArray[hashIndex].Name);
         if(cmp == 0){
            return hashIndex;
         }
      }
      //go to next cell
      ++hashIndex;
      
      //wrap around the table
      hashIndex %= h->size;
   }        
   return -1;        
}

/**
*  Returns the NodeP at the index in the HashTable
*/
NodeP * getH(HashTable *h, int index){
   if (index < 0 || index > h->size-1){
      return NULL;
   }
   return &(h->NodeArray[index]);
}

/**
*  Returns a new HashTable with double the size of the previous one
*  This function is used by the insertH function when an item is added to an halffull HashTable
*/
HashTable * resize(HashTable *h){
   HashTable * newH = newHastable(h->size*2);
   for(int i=0; i<h->size; i++){
      if(h->hashArray[i] >= 0){
         insertH(newH, &(h->NodeArray[i]));
      }
   }
   //free(h);
   return newH;
}

/**
*  Inserts a new NodeP n to the HashTable 
*  If the Hash=table  is halffull, the size is doubled
*/
void insertH(HashTable *h, NodeP *n) {
   if(h->numberElem+1 > h->size/2){
      *h = *resize(h);
   }
   //get the hash 
   int key = NodePKey(n);
   if(key<0){
      printf("Negative key for NodeP\n");
      return;
   }
   int hashIndex = hashCodeH(h,key);  
   //move in array until an empty or deleted cell
   while(h->hashArray[hashIndex] >= 0) {
      //go to next cell
      ++hashIndex;
      
      //wrap around the table
      hashIndex %= h->size;
   }
   h->hashArray[hashIndex] = key;
   h->NodeArray[hashIndex] = *n;
   h->numberElem +=1;
}

/**
*  Finds and deletes a NodeP in the Hashtable if it exists
*/
int deleteH(HashTable *h, NodeP *n) {

   //get the hash 
   int key = NodePKey(n);
   if(key<0){
      printf("Negative key for NodeP\n");
      return -1;
   }
   int hashIndex = hashCodeH(h,key);  
   //printf("[deleteH] hashIndex : %d\n",hashIndex);

   //move in array until an empty
   while(h->hashArray[hashIndex] !=-1) {
   
      if(h->hashArray[hashIndex] == key) {
         int key = h->hashArray[hashIndex];
         h->hashArray[hashIndex] = -2;
         h->numberElem -=1;
         return key;
      }
      
      //go to next cell
      ++hashIndex;
      
      //wrap around the table
      hashIndex %= h->size;
   }      
   return -1;        
}

/**
*  Simple HashTable displayer
*/
void displayH(HashTable *h) {
   printf("Nbr elements : %d\n",h->numberElem);
   for(int i = 0; i<h->size; i++) {
      printf(" %d",h->hashArray[i]);
   }
   printf("\n");
}

/**
*  Simple HashTable displayer
*/
void displayN(HashTable *h) {
   for(int i = 0; i<h->size; i++) {
      printf(" %s\n",h->NodeArray[i].Name);
   }
}

/**
*  free method for HashTable
*/
void freeH(HashTable *h){
   free(h->NodeArray);
   free(h->hashArray);
   free(h);
}

/*int main() {
   printf("Main\n");
   struct HashTable *h = newHastable(2);
   displayH(h);
   NodeP *n = malloc(sizeof(NodeP));
   n->Name = "Flocon";
   NodeP *n2 = malloc(sizeof(NodeP));
   n2->Name = "Thoma";
   NodeP *n3 = malloc(sizeof(NodeP));
   n3->Name = "Maxence";
   NodeP *n4 = malloc(sizeof(NodeP));
   n4->Name = "Alex";
   NodeP *n5 = malloc(sizeof(NodeP));
   n5->Name = "Remiche";
   insertH(h,n);
   displayH(h);
   //displayN(h);
   insertH(h,n2);
   displayH(h);
   deleteH(h,n);
   displayH(h);
   deleteH(h,n2);
   displayH(h);
   insertH(h,n2);
   displayH(h);
   insertH(h,n);
   displayH(h);
   insertH(h,n3);
   displayH(h);
   insertH(h,n4);
   displayH(h);
   insertH(h,n5);
   displayH(h);
   insertH(h,n5);
   displayH(h);

   int index = NodeIndex(h,n);

   printf("Index : %d\n",NodeIndex(h,n));
   printf("Index : %d\n",NodeIndex(h,n2));
   printf("Index : %d\n",NodeIndex(h,n3));
   printf("Index : %d\n",NodeIndex(h,n4));
   printf("Index : %d\n",NodeIndex(h,n5));
   printf("Index : %d\n",NameIndex(h,"Flocon"));
   printf("Index : %d\n",NameIndex(h,"Thoma"));
   printf("Index : %d\n",NameIndex(h,"Maxence"));
   printf("Index : %d\n",NameIndex(h,"Alex"));
   printf("Index : %d\n",NameIndex(h,"Remiche"));

   NodeP * Nn = getH(h,index);
   printf("Got node : %s\n",Nn->Name);

   deleteH(h,n);
   deleteH(h,n5);
   deleteH(h,n2);
   deleteH(h,n3);
   deleteH(h,n4);
   displayH(h);

   printf("Index : %d\n",NodeIndex(h,n5));


   freeH(h);
   free(n);
   free(n2);
   free(n3);
   free(n4);
   free(n5);
   printf("Done\n");

}*/