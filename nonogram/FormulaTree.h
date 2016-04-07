#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <algorithm>
#include <vector>
#include <string>
#include <map>

#define NONE -1
#define AND 0
#define OR 1
#define NOT 2
#define IMPLI 3
#define RIMPLI 4
#define EQUIV 5
#define MAX_STRLEN 111

using namespace std;

map<string, bool> g_literal_map;
const char g_str_oper[] = {"&|-><="};
int token_checker(const char* token)
{
    if (strlen(token) == 1) {
        for (int i = 0; i < 6; ++i)
            if (g_str_oper[i] == token[0])
                return i;
        return NONE;
    }
    else
        return NONE;
}

struct Node {
    Node* left_child;
    Node* right_child;
    int oper;
    char literal_name[MAX_STRLEN];
    bool negative;

    bool is_literal() const { return (this->oper == NONE); }
    bool is_negative() const { return (this->negative); }
    void Init()
    {
        this->left_child = NULL; this->right_child = NULL;
        oper = NONE;
        negative = false;
    }
};

struct FormulaTree {
    Node* root = NULL;
    int clauses_cnt;

    void clause_counting(Node* curr)
    {
        if (!curr) return;
        if (curr->oper == AND) {
            this->clauses_cnt++;
            clause_counting(curr->left_child);
            clause_counting(curr->right_child);
        }
        return;
    }

    void PrintPrefix() const
    {
        PrintPrefixRec(this->root);
        puts("");
        return;
    }
    void PrintPrefixRec(Node* curr) const
    {
        if (!curr)  return;

        if (curr->is_literal()) {
            if (curr->is_negative())
                printf("- ");
            printf("%s ", curr->literal_name);
        }
        else {
            printf("%c ", g_str_oper[curr->oper]);
            PrintPrefixRec(curr->left_child);
            PrintPrefixRec(curr->right_child);
        }
        return;
    }

    void PrintInfix() const
    {
        PrintInfixRec(this->root);
        puts("");
        return;
    }
    void PrintInfixRec(Node* curr) const
    {
        if (!curr)  return;

        if (curr->is_literal()) {
            if (curr->is_negative())
                printf("- ");
            printf("%s ", curr->literal_name);
        }
        else if (curr->oper == OR) {
            PrintInfixRec(curr->left_child);
            printf("| ");
            PrintInfixRec(curr->right_child);
        }
        else if (curr->oper == AND) {
            if ( !(curr->left_child->is_literal()) &&
                    curr->left_child->oper != AND ) printf("( ");
            PrintInfixRec(curr->left_child);
            if ( !(curr->left_child->is_literal()) &&
                    curr->left_child->oper != AND ) printf(") ");
            printf("& ");
            if ( !(curr->right_child->is_literal()) &&
                    curr->right_child->oper != AND ) printf("( ");
            PrintInfixRec(curr->right_child);
            if ( !(curr->right_child->is_literal()) &&
                    curr->right_child->oper != AND ) printf(") ");
        }
        else {
            /* for debug */
            printf("At PrintInfixRec, unexpected error occured!\n");
            exit(-1);
            /* --------- */
        }
        return;
    }

    void MakeTree(int n, vector<char*> input, int start_idx)
    {
        int idx = start_idx;
        this->root = (Node*)malloc(sizeof(Node) * 1);
        this->root->Init();
        int token_res = token_checker(input[idx++]);
        if (token_res == NONE) {
            strcpy(root->literal_name, input[idx-1]);
        }
        else if (token_res == NOT) {
            int next_res = token_checker(input[idx]);
            if (next_res == NONE) {
                strcpy(root->literal_name, input[idx++]);
                root->negative = true;
            }
            else if (next_res == NOT) {
                free(this->root);
                MakeTree(n, input, start_idx+2);
            }
            else {
                root->oper = token_res;
                MakeTreeRec(root, 0, idx, n, input);
            }
        }
        else {
            root->oper = token_res;
            MakeTreeRec(root, 0, idx, n, input);
            MakeTreeRec(root, 1, idx, n, input);
        }
        return;
    }
    void MakeTreeRec(Node* parent, bool type, int& curr_idx, int n, vector<char*> input)
    {
        if (curr_idx >= n)  return;

        Node* new_node = (Node*)malloc(sizeof(Node) * 1);
        new_node->Init();
        if (!type)    // left child of parent.
            parent->left_child = new_node;
        else          // right child of parent.
            parent->right_child = new_node;
        int token_res = token_checker(input[curr_idx++]);
        if (token_res == NONE) {
            strcpy(new_node->literal_name, input[curr_idx-1]);
        }
        else if (token_res == NOT) {
            int next_res = token_checker(input[curr_idx]);
            if (next_res == NONE) {
                strcpy(new_node->literal_name, input[curr_idx++]);
                new_node->negative = true;
            }
            else if (next_res == NOT) {
                curr_idx++;
                free(new_node);
                MakeTreeRec(parent, type, curr_idx, n, input);
            }
            else {
                new_node->oper = token_res;
                MakeTreeRec(new_node, 0, curr_idx, n, input);
            }
        }
        else {
            new_node->oper = token_res;
            MakeTreeRec(new_node, 0, curr_idx, n, input);
            MakeTreeRec(new_node, 1, curr_idx, n, input);
        }
        return;
    }

    Node* CopyTree(Node* curr)
    {
        if (!curr) return NULL;
        Node* new_node = (Node*)malloc(sizeof(Node) * 1);
        (*new_node) = (*curr);
        new_node->left_child = CopyTree(curr->left_child);
        new_node->right_child = CopyTree(curr->right_child);
        return new_node;
    }

    void ConvertToCNF()
    {
        // step 0: eliminate all equivalences.
        // EquivFree(this->root);
        // step 1: eliminate all implications.(After converting RIMPLI to IMPLI)
        // ImpliFree(this->root);
        // step 2: eliminate all non-literal negations.
        // ConvertToNNF(this->root, this->root, 0);
        // step 3: distribute all ORs.
        ConvertToCNFSub(this->root, this->root, 0);

        return;
    }
    void EquivFree(Node* curr)
    {
        if (!curr) return;

        // p = q <-> (~p | q) & (p | ~q)
        EquivFree(curr->left_child);
        EquivFree(curr->right_child);
        if (curr->oper == EQUIV) {
            curr->oper = AND;
            Node* left_copy = CopyTree(curr->left_child);
            Node* right_copy = CopyTree(curr->right_child);
            if (left_copy->oper == NOT)
                left_copy = left_copy->left_child;
            else if (left_copy->is_literal())
                left_copy->negative = !(left_copy->negative);
            else {
                Node* not_left = (Node*)malloc(sizeof(Node) * 1);
                not_left->Init();
                not_left->oper = NOT;
                not_left->left_child = left_copy;
                left_copy = not_left;
            }
            if (right_copy->oper == NOT)
                right_copy = left_copy->left_child;
            else if (right_copy->is_literal())
                right_copy->negative = !(right_copy->negative);
            else {
                Node* not_right = (Node*)malloc(sizeof(Node) * 1);
                not_right->Init();
                not_right->oper = NOT;
                not_right->left_child = right_copy;
                right_copy = not_right;
            }

            Node* new_left = (Node*)malloc(sizeof(Node) * 1);
            new_left->Init(); new_left->oper = OR;
            new_left->left_child = left_copy;
            new_left->right_child = curr->right_child;
            Node* new_right = (Node*)malloc(sizeof(Node) * 1);
            new_right->Init(); new_right->oper = OR;
            new_right->left_child = curr->left_child;
            new_right->right_child = right_copy;
            curr->left_child = new_left;
            curr->right_child = new_right;
        }
        return;
    }
    void ImpliFree(Node* curr)
    {
        if (!curr) return;
        if (curr->oper == RIMPLI) {
            curr->oper = IMPLI;
            Node* swp = curr->left_child;
            curr->left_child = curr->right_child;
            curr->right_child = swp;
            ImpliFree(curr);
            return;
        }

        if (curr->oper == IMPLI) {
            curr->oper = OR;
            if (curr->left_child->is_literal()) {
                curr->left_child->negative = !(curr->left_child->negative);
            }
            else if (curr->left_child->oper == NOT) {
                curr->left_child = curr->left_child->left_child;
            }
            else {
                Node* new_node = (Node*)malloc(sizeof(Node) * 1);
                new_node->Init();
                new_node->oper = NOT;
                new_node->left_child = curr->left_child;
                curr->left_child = new_node;
            }
        }
        ImpliFree(curr->left_child);
        ImpliFree(curr->right_child);
        return;
    }
    void ConvertToNNF(Node* curr, Node* parent, bool type)
    {
        if (!curr) return;

        if (curr->oper == NOT) {
            Node* be_freed = curr;
            if (curr == this->root)
                this->root = curr->left_child;
            else if (!type)
                parent->left_child = curr->left_child;
            else
                parent->right_child = curr->left_child;
            curr = curr->left_child;
            free(be_freed);
            /* for debug */
            if (curr->oper != OR && curr->oper != AND) {
                printf("At ConvertToNNF, unexpected error is occured.\n");
                exit(-1);
            }
            /*----------*/
            curr->oper = (curr->oper==OR)?AND:OR;
            if (curr->left_child->is_literal()) {
                curr->left_child->negative = !(curr->left_child->negative);
            }
            else if (curr->left_child->oper == NOT) {
                be_freed = curr->left_child;
                curr->left_child = curr->left_child->left_child;
                free(be_freed);
            }
            else {
                Node* new_node = (Node*)malloc(sizeof(Node) * 1);
                new_node->Init();
                new_node->oper = NOT;
                new_node->left_child = curr->left_child;
                curr->left_child = new_node;
            }
            if (curr->right_child->is_literal()) {
                curr->right_child->negative = !(curr->right_child->negative);
            }
            else if (curr->right_child->oper == NOT) {
                be_freed = curr->right_child;
                curr->right_child = curr->right_child->left_child;
                free(be_freed);
            }
            else {
                Node* new_node = (Node*)malloc(sizeof(Node) * 1);
                new_node->Init();
                new_node->oper = NOT;
                new_node->left_child = curr->right_child;
                curr->right_child = new_node;
            }
        }
        ConvertToNNF(curr->left_child, curr, 0);
        ConvertToNNF(curr->right_child, curr, 1);
        return;
    }
    void ConvertToCNFSub(Node* curr, Node* parent, bool type)
    {
        if (!curr) return;

        ConvertToCNFSub(curr->left_child, curr, 0);
        ConvertToCNFSub(curr->right_child, curr, 1);
        if (curr->oper == OR) {
            Node* distr_node = Distr(curr->left_child, curr->right_child);
            free(curr);
            if (curr == parent)
                this->root = distr_node;
            else if (!type)
                parent->left_child = distr_node;
            else
                parent->right_child = distr_node;
        }
        return;
    }
    Node* Distr(Node* le, Node* ri)
    {
        Node* new_node = (Node*)malloc(sizeof(Node) * 1);
        new_node->Init();
        if (le->oper == AND) {
            new_node->oper = AND;
            new_node->left_child = Distr(le->left_child, ri);
            new_node->right_child = Distr(le->right_child, ri);
        }
        else if (ri->oper == AND) {
            new_node->oper = AND;
            new_node->left_child = Distr(le, ri->left_child);
            new_node->right_child = Distr(le, ri->right_child);
        }
        else {
            new_node->oper = OR;
            new_node->left_child = le;
            new_node->right_child = ri;
        }
        return new_node;
    }

    bool IsValid() const { return IsValidSub(this->root); }
    bool IsValidSub(Node* curr) const
    {
        if (!curr) return true;

        bool res = true;
        if (curr->oper == AND)
            res &= IsValidSub(curr->left_child) & IsValidSub(curr->right_child);
        else if (curr->oper == OR) {
            g_literal_map.clear();
            res = CheckTerm(curr);
        }
        else
            return false;
        return res;
    }
    bool CheckTerm(Node* curr) const
    {
        if (!curr) return true;
        
        if (curr->is_literal()) {
            if (g_literal_map.find(curr->literal_name) == g_literal_map.end())
                g_literal_map[curr->literal_name] = (curr->is_negative()) ? 1 : 0;
            else if (g_literal_map[curr->literal_name] != curr->negative)
                return true;
            return false;
        }
        else if (curr->oper == OR)
            return CheckTerm(curr->left_child) | CheckTerm(curr->right_child);
        else {
            /*-for debug-*/
            printf("At CheckTerm, unexpected error occured!\n");
            exit(-1);
            /*-----------*/
        }
    }
};
