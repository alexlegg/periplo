#include <iostream>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

using namespace std;
#include <assert.h>
#include "SplayTree.h"

class cmp_int {
  public:
    bool operator() (int x, int y) const { return x < y; }
};

void check(bool contained[], int ints[], SplayTree<int,cmp_int>& tree, int size) {
//    printf("Before check\n");
//    tree.printTree();
    for (int i = 0; i < size; i++) {
        if (contained[i] == true) {
            int tree_el = tree.find(ints[i]);
            if (tree_el != ints[i]) {
                printf("Expected %d, got %d\n", ints[i], tree_el);
                assert(false);
            }
        }
        else if (contained[i] == false) {
            assert(tree.find(ints[i]) == -1); // I wonder ...
        }
    }
//    tree.printTree();
//    printf("After check\n");
}

int main(int argc, char** argv) {
    if (argc < 3 || strcmp(argv[1], "--help") == 0) {
        printf("Usage: %s <seed> <rounds>\n", argv[0]);
        return 1;
    }
    srandom(atoi(argv[1]));
    int max_rounds = atoi(argv[2]);

    int size = 1000;
    for (int round = 0; round < max_rounds; round++) {

        printf("Round %d/%d\n", round+1, max_rounds);

        SplayTree<int,cmp_int> tree;
        int nil = -1;
        tree.setNil(nil);

//        int array[3] = {0, 1, 2};
//        tree.debug(array, 3);
//        tree.printTree();
//
//        int in = 2;
//        int out = tree.find(in);
//        tree.printTree();
//        assert(out == in);
//        return 1;

        int*  ints = (int*) malloc(sizeof(int)*size);
        bool* contained = (bool*)malloc(sizeof(int)*size);

        // Get integers from 0 to size-1
        for (int i = 0; i < size; i++) {
            ints[i] = i;
            contained[i] = false;
        }

        // Shuffle the list
        for (int i = 0; i < size; i++) {
            int change = i + (int)((float)random()/RAND_MAX)-i;
            int tmp = ints[i];
            ints[i] = ints[change];
            ints[change] = tmp;
        }

        // Fill the tree
        for (int i = 0; i < size; i++) {
            tree.insert(ints[i]);
            contained[i] = true;
        }
        tree.perf(cout);

        for (int i = 0; i < 100; i++) {
            int action = random() % 3;
            if (action == 0) {
                // Insert an element
                int el = (float)random()/RAND_MAX*size;
                printf("Insert: %d (%s)\n", ints[el], contained[el] == true ? "contained" : "new");
                tree.insert(ints[el]);
                contained[el] = true;
            }
            else if (action == 1) {
                // Remove an existing element
                while ( !tree.isEmpty() ) {
                    int el = (float)random()/RAND_MAX*size;
                    if (contained[el] == true) {
                        printf("Remove: %d (%s)\n", ints[el], contained[el] == true ? "contained" : "not contained");
                        tree.remove(ints[el]);
                        contained[el] = false;
                        break;
                    }
                }
            }
            else if (action == 2) {
                continue ;
                // Remove a nonexisting element
                printf("Remove: %d (not contained)\n", size);
                tree.remove(size);
            }
            tree.perf(cout);
        }
        // This check effectively turns the tree to a linked list as a
        // side effect.
        check(contained, ints, tree, size);
        tree.perf(cout);
        tree.printTree();
        free(ints);
        free(contained);
    }
}
