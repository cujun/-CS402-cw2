#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <algorithm>
#include <vector>

#include "FormulaTree.h"

using namespace std;

int main(int argc, char* argv[])
{
    /* Enter Input in prefix form*/
    if (argc <= 1) {
        printf("Usage: ./cnf \"[arguments for literals and operators]\"\n");
        return 0;
    }
    vector<char*> args;
    char* argv_cpy = argv[1];
    int idx_pos = 0, len = strlen(argv[1]);
    while (idx_pos < strlen(argv[1])) {
        char* new_args = (char*)malloc(sizeof(char) * 22);
        sscanf(argv_cpy + idx_pos, "%s", new_args);
        args.push_back(new_args);
        idx_pos += strlen(new_args)+1;
    }

    /* Make FormulaTree */
    FormulaTree my_formula;    
    my_formula.MakeTree(args.size(), args, 0);

    /* Reconstruct FormulaTree to have CNF form */
    my_formula.ConvertToCNF();

    /* Print FormulaTree */
    my_formula.PrintPrefix();
    my_formula.PrintInfix();

    /* Check Validity */
    if (my_formula.IsValid())
        printf("Valid\n");
    else
        printf("Not Valid\n");

    return 0;
}
