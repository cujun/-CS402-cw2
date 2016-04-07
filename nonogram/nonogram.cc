#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <algorithm>
#include <vector>
#include <string>

#include "FormulaTree.h"

#define MAX_ROW 11111

using namespace std;

int g_row, g_col;
vector<int> g_clues[MAX_ROW * 2 + 1];
int g_literal_name[MAX_ROW][MAX_ROW];
string g_input_str = "";
bool g_literal_state[MAX_ROW], g_encoding_flag;
FILE* g_fp_input;

void Encoding(int out_idx, int in_idx, int clue_out_idx, int clue_in_idx, bool type)
{
    int n = (!type) ? g_col : g_row;

    // exit condition.
    if (in_idx >= n) return;
    if (in_idx + g_clues[clue_out_idx][clue_in_idx] > n) return;

    for (int i = in_idx; i < in_idx + g_clues[clue_out_idx][clue_in_idx]; ++i)
        g_literal_state[i] = true;
    // check if term satisfies all restrictions.
    if (clue_in_idx+1 == g_clues[clue_out_idx].size()) {
        g_input_str += "| ";
        for (int i = 0; i < n; ++i) {
            if (i != n-1)               g_input_str += "& ";
            if (!g_literal_state[i])    g_input_str += "- ";
            g_input_str += (!type) ? to_string(g_literal_name[out_idx][i]) : to_string(g_literal_name[i][out_idx]);
            g_input_str += " ";
        }
        for (int i = in_idx; i < in_idx + g_clues[clue_out_idx][clue_in_idx]; ++i)
            g_literal_state[i] = false;
        g_encoding_flag = true;
        return;
    }
    for (int i = in_idx + g_clues[clue_out_idx][clue_in_idx] + 1; i <= n+1; ++i)
        Encoding(out_idx, i, clue_out_idx, clue_in_idx+1, type);
    for (int i = in_idx; i < in_idx + g_clues[clue_out_idx][clue_in_idx]; ++i)
        g_literal_state[i] = false;
    return;
}

void PrintMinisatInputSub(Node* curr)
{
    if (!curr) return;

    if (curr->oper == OR) {
        PrintMinisatInputSub(curr->left_child);
        PrintMinisatInputSub(curr->right_child);
    }
    else if (curr->oper == AND) {
        printf("At PrintMinisatInputSub, unexpected error occured!\n");
        exit(-1);
    }
    else {
        if (curr->is_negative()) fprintf(g_fp_input, "-");
        fprintf(g_fp_input, "%s ", curr->literal_name);
    }
    return;
}
void PrintMinisatInput(Node* curr)
{
    if (!curr) return;

    if (curr->oper == AND) {
        PrintMinisatInput(curr->left_child);
        PrintMinisatInput(curr->right_child);
    }
    else if (curr->oper == OR) {
        PrintMinisatInputSub(curr);
        fprintf(g_fp_input, "0\n");
    }
    else {
        if (curr->is_negative()) fprintf(g_fp_input, "-");
        fprintf(g_fp_input, "%s ", curr->literal_name);
        fprintf(g_fp_input, "0\n");
    }
    return;
}

int main(int argc, char* argv[])
{
    if (argc < 2) {
        printf("Usage: ./nonogram [input file name]\n");
        exit(0);
    }

    // Enter input from file.
    FILE* fp_in = fopen(argv[1], "r");
    fscanf(fp_in, "%d", &g_row);
    fscanf(fp_in, "%d\n", &g_col);
    if (g_row < 1 || g_col < 1) {
        printf("Inappropriate Input\n");
        fclose(fp_in);
        return 0;
    }
    int literal_name_cnt = 1;
    for (int i = 0; i < g_row; ++i)
        for (int j = 0; j < g_col; ++j)
            g_literal_name[i][j] = literal_name_cnt++;
    for (int i = 0; i < g_row+g_col; ++i) {
        char input[111];
        fgets(input, sizeof(input), fp_in); input[strlen(input)-1] = 0;
        char* input_pos = input;
        for (int j = 0; ; ++j) {
            char temp[111];
            int num;
            if (sscanf(input_pos, "%s", temp) < 1) break;
            sscanf(input_pos, "%d", &num);
            g_clues[i].push_back(num);
            input_pos += strlen(temp)+1;
        }
    }
    fclose(fp_in);

    // SAT Encoding.
    for (int i = 0; i < g_row; ++i) {
        g_input_str += "& ";
        memset(g_literal_state, false, sizeof(g_literal_state));
        g_encoding_flag = false;
        for (int j = 0; j < g_col; ++j)
            Encoding(i, j, i, 0, 0);
        int len = g_input_str.length();
        for (int j = len-1; j >= 0; --j) {
            if (g_input_str[j] == '|') {
                g_input_str.erase(j, 2);
                break;
            }
        }
        if (g_encoding_flag == false) {
            printf("No Solution\n");
            return 0;
        }
    }
    for (int i = 0; i < g_col; ++i) {
        if (i != g_col-1) g_input_str += "& ";
        memset(g_literal_state, false, sizeof(g_literal_state));
        g_encoding_flag = false;
        for (int j = 0; j < g_row; ++j)
            Encoding(i, j, g_row+i, 0, 1);
        int len = g_input_str.length();
        for (int j = len-1; j >= 0; --j) {
            if (g_input_str[j] == '|') {
                g_input_str.erase(j, 2);
                break;
            }
        }
        if (g_encoding_flag == false) {
            printf("No Solution\n");
            return 0;
        }
    }
    g_input_str.erase(g_input_str.length()-1, 1);

    // Make FormulaTree using encoded string.
    // And convert to CNF.
    char* input_str = (char*)malloc(sizeof(char) * (g_input_str.length()+1));
    strcpy(input_str, g_input_str.c_str());
    vector<char*> args;
    char* input_cpy = input_str;
    while (true) {
        char* new_args = (char*)malloc(sizeof(char) * 22);
        if (sscanf(input_cpy, "%s", new_args) < 1) break;
        args.push_back(new_args);
        input_cpy += strlen(new_args)+1;
    }
    FormulaTree my_formula;
    my_formula.MakeTree(args.size(), args, 0);
    my_formula.ConvertToCNF();

    // Extract data of FormulaTree
    // And execute minisat using that data according to the minisat input format.
    const string in = "minisat.in";
    const string out = "minisat.out";
    g_fp_input = fopen(in.c_str(), "w");
    my_formula.clauses_cnt = 1;
    my_formula.clause_counting(my_formula.root);
    fprintf(g_fp_input, "p cnf %d %d\n", g_row*g_col, my_formula.clauses_cnt);
    PrintMinisatInput(my_formula.root);
    fclose(g_fp_input);

    system("minisat minisat.in minisat.out > /dev/null");

    FILE* fp_output = fopen(out.c_str(), "r");
    char result[22]; fscanf(fp_output, "%s", result);
    for (int i = 0; i < g_row; ++i) {
        for (int j = 0; j < g_col; ++j) {
            int a; fscanf(fp_output, "%d", &a);
            if (a == 0) break;
            if (a < 0) printf(".");
            else printf("#");
        }
        puts("");
    }
    fclose(fp_output);

    system("rm minisat.in minisat.out");
    return 0;
}
