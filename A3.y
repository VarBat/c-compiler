%token INTEGER_LITERAL FLOAT_LITERAL IDENTIFIER SC PRINTF FORMAT_SPECIFIER FORMAT SCANF
%token INT VOID FLOAT WHILE IF ELSE BREAK CONTINUE RETURN
%token COMMA PAREN_OPEN PAREN_CLOSE SQ_OPEN SQ_CLOSE CURLY_OPEN CURLY_CLOSE
%token OR EE NE LE LT GE GT AND PLUS MINUS INTO BY MOD NOT ASSGN UNAND
%{
	#define YYSTYPE struct node*
    #include <stdio.h>
    #include <string.h>
    #include <stdlib.h>
    #include <iostream>
    #include <bits/stdc++.h>
    using namespace std;
    #include "y.tab.h"
    #define max(a,b) (a>b)?a:b
    void yyerror(string);
    int yylex(void);
    extern char* yytext;
    extern int lineno;
    typedef struct node{
        bool asmd = false;
        string type;
        struct node* children[10];
        int noc;
        int lno;
        int cf;
        int attr;
    }node;
    node* root;
    void getasm(node* root);
    node* mk0(string t);
    node* mk1(string t, node* one);
    node* mk2(string t, node* one, node* two);
    node* mk3(string t, node* one, node* two, node* three);
    node* mk4(string t, node* one, node* two, node* three, node* four);
    node* mk5(string t, node* one, node* two, node* three, node* four, node* five);
    node* mk6(string t, node* one, node* two, node* three, node* four, node* five, node* six);
    node* mk7(string t, node* one, node* two, node* three, node* four, node* five, node* six, node* seven);
    void freenodes(node* root);
    void printtree(node* root);
    string getlabel();
    unordered_map<string,unordered_map <string,int>> loc;
    unordered_map<string,int> temp;
    unordered_map<string,string> funlabel;
    string currfun;
    int nn = 0, variables=0;
    int top = 4;
    int ctr = 0;
    int ifexpr(node* root);
    void ifblock(node* root);
    void const_fold(node* root);
    map<string,int> stab;
    map<string,int> avail;
    void const_prop(node* root);
    int ifflag=0,cprop=1,cfold=1;
    vector<string> uvar;
    map<string,int> umap;
    void unusedvar(node* root);
    int if_sim=0,if_sim1=0;
    int maxx=INT_MIN;
    vector<pair<int,int> > cfvec;
    void fold_sum(node* root);
    void fold_sum1(node* root);
    map<string,int> varlno;
    map<int,vector<pair<string,int> > > cpmap;
    bool compare(const pair<string,int> &a, const pair<string,int> &b);
    map<string,int> csemap;
    map<int,int> sredmap;
    void sred_sum(node* root);
    vector<node*> csevec;
    int cse_equal(node* root1,node* root2);
    void cse_vecform(node* root);
    void cse_ssa(node* root);
    bool compare1(const vector<int> &a,const vector<int> &b);
    int ifline=0;
    ofstream out("summary.txt");
    int ffold=0,fprop=0;
    map<int,vector<node*> > fsum;
    void fold_s(node* root);
%}

%%

program:        decl_list 
                {
                    root = mk1("program", $1);
                };

decl_list:      decl_list decl        
                {
                    $$ = mk2("decl_list", $1, $2);
                }
                | decl                  
                {
                    $$ = mk1("decl_list", $1);
                }
                ;

decl:           var_decl                
                {
                    variables++;
                    loc["global"][$1->children[0]->children[0]->type] = top;
                    top += 4;
                    $$ = mk1("decl", $1);
                }
                | func_decl             
                {
                    currfun = $1->children[1]->children[0]->type;
                    loc[currfun] = temp;
                    temp.clear();
                    $$ = mk1("decl", $1);
                }
                ;

var_decl:       type_spec identifier SC 
                {
                    $3 = mk0(";");
                    $$ = mk3("var_decl", $1, $2, $3);
                }                                                    
                | type_spec identifier COMMA var_decl
                {
                    $3 = mk0(",");
                    $$ = mk4("var_decl", $1, $2, $3, $4);
                }
                | type_spec identifier SQ_OPEN integerLit SQ_CLOSE SC
                {
                    $3 = mk0("[");
                    $5 = mk0("]");
                    $6 = mk0(";");
                    $$ = mk6("var_decl", $1, $2, $3, $4, $5, $6);
                }
                | type_spec identifier SQ_OPEN integerLit SQ_CLOSE COMMA var_decl
                {
                    $3 = mk0("[");
                    $5 = mk0("]");
                    $6 = mk0(",");
                    $$ = mk7("var_decl", $1, $2, $3, $4, $5, $6,$7);
                }
                ;

type_spec:      VOID 
                {
                    $1 = mk0("void");
                    $$ = mk1("type_spec", $1);
                }
                | INT 
                {
                    $1 = mk0("int");
                    $$ = mk1("type_spec", $1);
                }
                | FLOAT 
                {
                    $1 = mk0("float");
                    $$ = mk1("type_spec", $1);
                }
                ;

func_decl:      type_spec identifier PAREN_OPEN params PAREN_CLOSE compound_stmt
                {
                    $3 = mk0("(");
                    $5 = mk0(")");
                    $$ = mk6("func_decl", $1, $2, $3, $4, $5, $6);
                }
                ;

params:         param_list 
                {
                    $$ = mk1("params", $1);
                }
                | 
                {
                    $$ = mk1("params", mk0("epsilon"));
                }
                ;

param_list:     param_list COMMA param 
                {
                    $2 = mk0(",");
                    $$ = mk3("param_list", $1, $2, $3);
                }
                | param
                {
                    $$ = mk1("param_list", $1);
                }
                ;

param:          type_spec identifier 
                {
                    variables++;
                    temp[$2->children[0]->type] = top;
                    top+=4;
                    $$ = mk2("param", $1, $2);
                }
                | type_spec identifier SQ_OPEN SQ_CLOSE
                {
                    $3 = mk0("[");
                    $4 = mk0("]");
                    $$ = mk4("param", $1, $2, $3 , $4);
                }
                | type_spec SQ_OPEN SQ_CLOSE identifier
                {
                    $2 = mk0("[");
                    $3 = mk0("]");
                    $$ = mk4("param", $1, $2, $3 , $4);
                }
                ;

stmt_list:      stmt_list stmt 
                {
                    $$ = mk2("stmt_list", $1, $2);
                }
                | stmt
                {
                    $$ = mk1("stmt_list", $1);
                }
                ;

stmt:           assign_stmt 
                {
                    $$ = mk1("stmt", $1);
                }
                | compound_stmt 
                {
                    $$ = mk1("stmt", $1);
                }
                | if_stmt 
                {
                    $$ = mk1("stmt", $1);
                }
                | while_stmt
                {
                    $$ = mk1("stmt", $1);
                }
                | return_stmt 
                {
                    $$ = mk1("stmt", $1);
                }
                | break_stmt 
                {
                    $$ = mk1("stmt", $1);
                }
                | continue_stmt
                {
                    $$ = mk1("stmt", $1);
                }
                | print_stmt
                {
                    $$ = mk1("stmt", $1);
                }
                | scan_stmt
                {
                	$$ = mk1("stmt",$1);
                }
                ;

while_stmt:     WHILE PAREN_OPEN expr PAREN_CLOSE stmt
                {
                    $1 = mk0("while");
                    $2 = mk0("(");
                    $4 = mk0(")");
                    $$ = mk5("while_stmt", $1, $2, $3, $4, $5);
                }
                ;

print_stmt:     PRINTF PAREN_OPEN FORMAT_SPECIFIER COMMA identifier PAREN_CLOSE SC
                {
                    $$ = mk1("print_stmt",$5);
                }
                ;
                
scan_stmt:		SCANF PAREN_OPEN FORMAT COMMA UNAND identifier PAREN_CLOSE SC
				{
					$$ = mk1("scan_stmt",$6);	
				}
				; 

compound_stmt:  CURLY_OPEN local_decls stmt_list CURLY_CLOSE
                {
                    $1 = mk0("{");
                    $4 = mk0("}");
                    $$ = mk4("compound_stmt", $1, $2, $3, $4);
                }
                ;

local_decls:    local_decls local_decl 
                {
                    $$ = mk2("local_decls", $1, $2);
                }
                |
                {
                    $$ = mk1("local_decls", mk0("epsilon"));
                }
                ;

local_decl:     type_spec identifier SC 
                {
                    variables++;
                    temp[$2->children[0]->type] = top;
                    top+=4;
                    $3 = mk0(";");
                    $$ = mk3("local_decl", $1, $2, $3);
                }
                | type_spec identifier SQ_OPEN expr SQ_CLOSE SC
                {
                    $3 = mk0("[");
                    $5 = mk0("]");
                    $6 = mk0(";");
                    $$ = mk6("local_decl", $1, $2, $3, $4, $5, $6);
                }
                ;

if_stmt:        IF PAREN_OPEN expr PAREN_CLOSE stmt
                {
                    $1 = mk0("if");
                    $2 = mk0("(");
                    $4 = mk0(")");
                    $$ = mk5("if_stmt", $1, $2, $3, $4, $5);
                }
                | IF PAREN_OPEN expr PAREN_CLOSE stmt ELSE stmt
                {
                    $1 = mk0("if");
                    $2 = mk0("(");
                    $4 = mk0(")");
                    $6 = mk0("else");
                    $$ = mk7("if_stmt", $1, $2, $3, $4, $5, $6, $7);
                }
                ;

return_stmt:    RETURN SC 
                {
                    $1 = mk0("return");
                    $2 = mk0(";");
                    $$ = mk2("return_stmt", $1, $2);
                }
                | RETURN expr SC
                {
                    $1 = mk0("return");
                    $3 = mk0(";");
                    $$ = mk3("return_stmt", $1, $2, $3);
                }
                ;

break_stmt:     BREAK SC
                {
                    $1 = mk0("break");
                    $2 = mk0(";");
                    $$ = mk2("break_stmt", $1, $2);
                }
                ;

continue_stmt:  CONTINUE SC
                {
                    $1 = mk0("continue");
                    $2 = mk0(";");
                    $$ = mk2("continue_stmt", $1, $2);
                }
                ;

assign_stmt:    identifier ASSGN expr SC 
                {
                    $4 = mk0(";");
                    $$ = mk2("assign_stmt", mk2("=", $1, $3), $4);
                }
                | identifier SQ_OPEN expr SQ_CLOSE ASSGN expr SC
                {
                    $5 = mk5("=", $1, mk0("["), $3, mk0("]"), $6);
                    $$ = mk1("assign_stmt", $5);
                }
                ;

expr:           Pexpr OR Pexpr 
                {
                    $2 = mk2("||", $1, $3);
                    $$ = mk1("expr", $2);
                }
                | Pexpr EE Pexpr
                {
                   $2 = mk2("==", $1, $3);
                    $$ = mk1("expr", $2);
                } 
                | Pexpr NE Pexpr
                {
                    $2 = mk2("!=", $1, $3);
                    $$ = mk1("expr", $2);
                }
                | Pexpr LE Pexpr 
                {
                    $2 = mk2("<=", $1, $3);
                    $$ = mk1("expr", $2);
                }
                | Pexpr LT Pexpr 
                {
                    $2 = mk2("<", $1, $3);
                    $$ = mk1("expr", $2);
                }
                | Pexpr GE Pexpr 
                {
                    $2 = mk2(">=", $1, $3);
                    $$ = mk1("expr", $2);
                }
                | Pexpr GT Pexpr
                {
                    $2 = mk2(">", $1, $3);
                    $$ = mk1("expr", $2);
                }
                | Pexpr AND Pexpr
                {
                    $2 = mk2("&&", $1, $3);
                    $$ = mk1("expr", $2);
                }
                | Pexpr PLUS Pexpr 
                {
                    $2 = mk2("+", $1, $3);
                    $$ = mk1("expr", $2);
                }
                | Pexpr MINUS Pexpr
                {
                    $2 = mk2("-", $1, $3);
                    $$ = mk1("expr", $2);
                }
                | Pexpr INTO Pexpr 
                {
                    $2 = mk2("*", $1, $3);
                    $$ = mk1("expr", $2);
                }
                | Pexpr BY Pexpr 
                {
                   $2 = mk2("/", $1, $3);
                    $$ = mk1("expr", $2);
                }
                | Pexpr MOD Pexpr
                {
                    $2 = mk2("%%", $1, $3);
                    $$ = mk1("expr", $2);
                }
                | NOT Pexpr 
                {
                    $1 = mk0("!");
                    $$ = mk2("expr", $1, $2);
                }
                | MINUS Pexpr
                {
                    $1 = mk0("-");
                    $$ = mk2("expr", $1, $2);
                } 
                | PLUS Pexpr 
                {
                    $1 = mk0("+");
                    $$ = mk2("expr", $1, $2);
                }
                | INTO Pexpr 
                {
                    $1 = mk0("*");
                    $$ = mk2("expr", $1, $2);
                }
                | UNAND Pexpr
                {
                    $1 = mk0("&");
                    $$ = mk2("expr", $1, $2);
                }
                | Pexpr
                {
                    $$ = mk1("expr", $1);
                }
                | identifier PAREN_OPEN args PAREN_CLOSE
                {
                    if(loc.find($1->children[0]->type)==loc.end())
                        yyerror("");
                    $2 = mk0("(");
                    $4 = mk0(")");
                    $$ = mk4("expr", $1, $2, $3, $4);
                }
                | identifier SQ_OPEN expr SQ_CLOSE
                {
                    $2 = mk0("[");
                    $4 = mk0("]");
                    $$ = mk4("expr", $1, $2, $3, $4);
                }
                ;

Pexpr:          integerLit
                {
                    $$ = mk1("Pexpr", $1);
                }
                | floatLit 
                {
                    $$ = mk1("Pexpr", $1);
                }
                | identifier 
                {
                    if(temp.find($1->children[0]->type)==temp.end() && loc["global"].find($1->children[0]->type)==loc["global"].end())
                        yyerror("");
                    $$ = mk1("Pexpr", $1);
                }
                | PAREN_OPEN expr PAREN_CLOSE 
                {
                    $1 = mk0("(");
                    $3 = mk0(")");
                    $$ = mk3("Pexpr", $1, $2, $3);
                }
                ;

integerLit:     INTEGER_LITERAL 
                {
                    $1 = mk0(string(yytext));
                    $$ = mk1("integerLit", $1);
                }
                ;

floatLit:       FLOAT_LITERAL 
                {
                    $1 = mk0(string(yytext));
                    $$ = mk1("floatLit", $1);
                }
                ;

identifier:     IDENTIFIER 
                {
                    $1 = mk0(string(yytext));
                    $$ = mk1("IDENTIFIER", $1);
                }
                ;

args:           args_list 
                {
                    $$ = mk1("args", $1);
                }
                | 
                {
                    $$ = mk1("args", mk0("epsilon"));
                }
                ;

args_list:      args_list COMMA expr 
                {
                    $2 = mk0(",");
                    $$ = mk3("args_list", $1, $2, $3);
                }
                | expr
                {
                    $$ = mk1("args_list", $1);
                }
                ;
%%

void yyerror(string s) {
    printf("Invalid\n");
    exit(0);
}

int main(void) {
	freopen("assembly.s","w",stdout);
    loc["global"];
    yyparse();
    while(cprop || cfold){
    	cprop = 0;
    	cfold = 0;
    	const_fold(root);
    	const_prop(root);
    	fprop=0;
    	ffold=0;
    	//cout<<"1 "<<cprop<<" "<<cfold<<endl;
    }
    ifblock(root);
    cprop=1;
    while(cprop || cfold){
    	cprop = 0;
    	cfold = 0;
    	const_fold(root);
    	const_prop(root);
    	fprop=0;
    	ffold=0;
    	//cout<<"2 "<<cprop<<" "<<cfold<<endl;
    }
    out<<"unused-vars"<<endl;
    unusedvar(root);
    for(int i=0;i<uvar.size();i++){
    	if(umap[uvar[i]]==1){
    		out<<uvar[i]<<endl;
    	}
    }
    out<<endl;
    out<<"if-simpl"<<endl;
    if(if_sim){
		out<<if_sim1<<endl;    
    }
    out<<endl;
    out<<"strength-reduction"<<endl;
    sred_sum(root);
    //cout<<sredmap.size()<<endl;
    for(auto i=sredmap.begin();i!=sredmap.end();i++){
    	out<<i->first<<" "<<i->second<<endl;
    }
    out<<endl;
    out<<"constant-folding"<<endl;
    /*fold_sum(root);
    for(int i=0;i<cfvec.size();i++){
    	if(if_sim && cfvec[i].first!=ifline){
    		out<<cfvec[i].first<<" "<<cfvec[i].second<<endl;
    	}
    	else if(!if_sim){
    		out<<cfvec[i].first<<" "<<cfvec[i].second<<endl;
    	}
    }*/
    fold_s(root);
    //out<<fsum.size()<<endl;
    for(auto i =fsum.begin();i!=fsum.end();i++){
    	int flag = 0;
    	int fmax=INT_MIN;
    	vector<node*> temp;
    	temp = i->second;
    	for(int j=0;j<temp.size();j++){
    		if(temp[j]->cf==1){
    			flag=1;
    		}
    		if(stoi(temp[j]->type)>fmax){
    			fmax=stoi(temp[j]->type);
    		}
    	}
    	if(flag){
    		out<<i->first<<" "<<fmax<<endl;
    	}
    }
    out<<endl;
    out<<"constant-propagation"<<endl;
    for(auto i =cpmap.begin();i!=cpmap.end();i++){
    	if(if_sim && i->first==ifline){
    		continue;
    	}
    	out<<i->first<<" ";
    	vector<pair<string,int> > temp = i->second;
    	sort(temp.begin(),temp.end(),compare);
    	for(int j=0;j<temp.size();j++){
    		out<<temp[j].first<<" "<<temp[j].second<<" ";
    	}
    	out<<endl;
    }
    out<<endl;
    out<<"cse"<<endl;
    cse_vecform(root);
    cse_ssa(root);
    vector<vector<int> > v;
    for(int i=0;i<csevec.size();i++){
    	vector<int> temp;
    	temp.push_back(csevec[i]->lno);
    	for(int j=i+1;j<csevec.size();j++){
    		if(cse_equal(csevec[i],csevec[j])){
    		//cout<<csevec[i]->lno<<" "<<csevec[j]->lno<<endl;
    			temp.push_back(csevec[j]->lno);
    			csevec.erase(csevec.begin()+j);
    			j--;
    		}
    	}
    	csevec.erase(csevec.begin()+i);
    	i--;
    	sort(temp.begin(),temp.end());
    	if(temp.size()>1){
    		v.push_back(temp);
    	}
    }
    sort(v.begin(),v.end(),compare1);
    for(int i=0;i<v.size();i++){
    	vector<int> temp = v[i];
    	for(int j=0;j<temp.size();j++){
    		out<<temp[j]<<" ";
    	}
    	out<<endl;
    }
    out<<endl;
    top = (int)(16 * (ceil(variables/4.0)));
    // cout << top << endl;
    // for(auto &it:loc) {
    //     cout << it.first << endl;
    //     for(auto &j:it.second)
    //     {
    //         cout <<"\t"<< j.first <<"->" << j.second << endl;
    //     }
    //     cout <<"===" << endl;
    // }
    printf(".LC0:\n\t.string \"%%d\"\n");
    printf(".LC1:\n\t.string \"%%d\\n\"\n\t.text\n\t.globl main\n\t.type main, @function\n");
    printf("main:\n.LFB0:\n\t.cfi_startproc\n\tpushq %%rbp\n\t.cfi_def_cfa_offset 16\n\t.cfi_offset 6, -16\n\tmovq %%rsp, %%rbp\n\t.cfi_def_cfa_register 6\n\t");
    printf("subq $%d,%%rsp\n", top);
    getasm(root);
    printf("\tmovl $0, %%eax\n\tleave\n\t.cfi_def_cfa 7, 8\n\tret\n\t.cfi_endproc\n");
    //printtree(root);
    freenodes(root);
    return 0;
}

void getexp(node* root) {
    if(root == NULL)
        return;

    for(int i=0;i<root->noc;i++)
        getexp(root->children[i]);

    if(root->type == "IDENTIFIER" && !root->asmd) {
        printf("\tmovl -%d(%%rbp),%%ecx\n\tpushq %%rcx\n",loc[currfun][root->children[0]->type]);
        root->asmd = true;
    }
    //add for function call
    else if(root->type == "integerLit") {
        printf("\tmovl $%d,%%ecx\n\tpushq %%rcx\n",stoi(root->children[0]->type));
    }
    else if(root->type == "floatLit") {
        printf("\tmovl $%d,%%ecx\n\tpushq %%rcx\n",stoi(root->children[0]->type));
    }
    else if(root->type == "+" && root->noc == 2) {
        printf("\tpopq %%rbx\n\tpopq %%rcx\n\taddl %%ebx, %%ecx\n\tpushq %%rcx\n");
    }
    else if(root->type == "-" && root->noc == 2) {
        printf("\tpopq %%rbx\n\tpopq %%rcx\n\tsubl %%ebx, %%ecx\n\tpushq %%rcx\n");
    }
    else if(root->type == "*" && root->noc == 2) {
        printf("\tpopq %%rbx\n\tpopq %%rcx\n\timull %%ebx, %%ecx\n\tpushq %%rcx\n");
    }
    else if(root->type == "/") {
        printf("\tpopq %%rcx\n\tpopq %%rax\n\tcltd\n\tidivl %%ecx\n\tpushq %%rax\n");
    }
    else if(root->type == "%%") {
        printf("\tpopq %%rcx\n\tpopq %%rax\n\tcltd\n\tidivl %%ecx\n\tpushq %%rdx\n");
    }
    else if(root->type == "||") {
        string l1 = getlabel();
        string l2 = getlabel();
        string l3 = getlabel();
        cout <<"\tpopq %rax\n\tpopq %rbx\n\tcmpl $0,%eax\n\tjne "<<l1<<"\n\tcmpl $0,%ebx\n\tje "<<l2<<"\n"<<l1<<":\n\tmovl $1,%eax\n\tjmp "<<l3<<"\n"<<l2<<":\n\tmovl $0,%eax\n"<<l3<<":\n\tpushq %rax\n";
    }
    else if(root->type == "&&") {
        string l1 = getlabel();
        string l2 = getlabel();
        cout <<"\tpopq %rax\n\tpopq %rbx\n\tcmpl $0,%ebx\n\tje "<<l1<<"\n\tcmpl $0,%eax\n\tje "<<l1<<"\n\tmovl $1,%eax\n\tjmp "<<l2<<"\n"<<l1<<":\n\tmovl $0,%eax\n"<<l2<<":\n\tpushq %rax\n";
    }
    else if(root->type == "==") {
        cout <<"\tpopq %rax\n\tpopq %rbx\n\tcmpl %eax,%ebx\n\tsete %al\n\tmovzbl %al,%eax\n\tpushq %rax\n";
    }
    else if(root->type == "!=") {
        cout <<"\tpopq %rax\n\tpopq %rbx\n\tcmpl %eax,%ebx\n\tsetne %al\n\tmovzbl %al,%eax\n\tpushq %rax\n";
    }
    else if(root->type == "<=") {
        cout <<"\tpopq %rax\n\tpopq %rbx\n\tcmpl %eax,%ebx\n\tsetle %al\n\tmovzbl %al,%eax\n\tpushq %rax\n";
    }
    else if(root->type == "<") {
        cout <<"\tpopq %rax\n\tpopq %rbx\n\tcmpl %eax,%ebx\n\tsetl %al\n\tmovzbl %al,%eax\n\tpushq %rax\n";
    }
    else if(root->type == ">=") {
        cout <<"\tpopq %rax\n\tpopq %rbx\n\tcmpl %eax,%ebx\n\tsetge %al\n\tmovzbl %al,%eax\n\tpushq %rax\n";
    }
    else if(root->type == ">") {
        cout <<"\tpopq %rax\n\tpopq %rbx\n\tcmpl %eax,%ebx\n\tsetg %al\n\tmovzbl %al,%eax\n\tpushq %rax\n";
    }
    else if(root->type == "expr" && root->children[0]->type == "!") {
        getasm(root->children[1]);
        cout <<"\tpopq %rbx\n\tcmpl $0,%ebx\n\tsete %al\n\tmovzbl %al,%eax\n\tpushq %rax\n";
    }
    else if(root->type == "expr" && root->children[0]->type == "-" && root->children[0]->noc == 0) {
        getasm(root->children[1]);
        cout <<"\tpopq %rax\n\tnegl %eax\n\tpushq %rax\n";
    }
}

void getasm(node* root) {
    if(root == NULL)
        return;

    if(root->type == "if_stmt" && !root->asmd) {
        root->asmd = true;
        if(root->noc == 5) {
            getexp(root->children[2]);
            string l1 = getlabel();
            cout << "\tpopq %rax\n\tcmpl $0, %eax\n\tje " << l1 << "\n";
            getasm(root->children[4]);
            cout << l1 << ":\n";
        }
        else if(root->noc == 7) {
            getexp(root->children[2]);
            string l1 = getlabel();
            string l2 = getlabel();
            cout << "\tpopq %rax\n\tcmpl $0, %eax\n\tje " << l1 << "\n";
            getasm(root->children[4]);
            cout << "\tjmp " << l2 << "\n";
            cout << l1 << ":\n";
            getasm(root->children[6]);
            cout << l2 << ":\n";
        }
    }
    else if(root->type == "while_stmt" && !root->asmd) {
        root->asmd = true;
        string l1 = getlabel();
        string l2 = getlabel();
        cout << l1 << ":\n"; 
        getexp(root->children[2]);
        cout << "\tpopq %rax\n\tcmpl $0, %eax\n\tje " << l2 << "\n";
        getasm(root->children[4]);
        cout << "jmp " << l1 <<"\n";
        cout << l2 <<":\n";
    }
    // else if(root->type == "func_decl" && !root->asmd) {
    //     root->asmd = true;
    //     currfun = root->children[1]->children[0]->type;

    //     cout << currfun << ":\n";
    //     printf("\t.cfi_startproc\n\tpushq %%rbp\n\t.cfi_def_cfa_offset 16\n\t.cfi_offset 6, -16\n\tmovq %%rsp, %%rbp\n\t.cfi_def_cfa_register 6\n\t");
    //     getasm(root->children[3]);
    //     getasm(root->children[5]);
    //     printf("\t.cfi_def_cfa 7, 8\n\tret\n\t.cfi_endproc\n");
    // }

    for(int i=0;i<root->noc;i++)
        getasm(root->children[i]);

    if(root->type == "print_stmt" && !root->asmd) {
        root->asmd = true;
        int addr = loc[currfun][root->children[0]->children[0]->type];
        printf("\tmovl -%d(%%rbp), %%eax\n\tmovl %%eax, %%esi\n\tleaq    .LC1(%%rip), %%rdi\n\tmovl $0, %%eax\n\tcall printf@PLT\n",addr);      
    }
    else if(root->type=="scan_stmt" && !root->asmd){
    	root->asmd = true;
        int addr = loc[currfun][root->children[0]->children[0]->type];
        printf("\tleaq -%d(%%rbp), %%rax\n\tmovq %%rax, %%rsi\n\tleaq    .LC0(%%rip), %%rdi\n\tmovl $0, %%eax\n\tcall\tscanf@PLT\n",addr);      
    }
    else if(root->type == "=" && !root->asmd) {
        root->asmd = true;
        getexp(root->children[1]);
        //cout << exp;
        printf("\tpopq %%rbx\n\tmovl %%ebx, -%d(%%rbp)\n",loc[currfun][root->children[0]->children[0]->type]);
    }
    // else if(root->type == "return_stmt" && !root->asmd) {
    //     root->asmd = true;
    //     if(root->noc != 2) {
    //         getexp(root->children[1]);
    //     }
    // }
    // else if(root->type == "param" && !root->asmd) {
    //     root->asmd = true;
    //     printf("\tpopq %%rax\n\tmovl %%eax,-%d(rbp)\n",loc[currfun][root->children[1]->children[0]->type]);
    // }

}

node* mk0(string t) {
    node* newnode = new node;
    
    newnode->type = t;
    
    newnode->noc = 0;
    newnode->lno=lineno;
    newnode->cf=0;
    return newnode;
}

node* mk1(string t, node* one) {
    node* newnode = new node;
    
    newnode->type = t;
    
    newnode->children[0] = one;
    newnode->noc = 1;
    newnode->lno=lineno;
    newnode->cf=0;
    return newnode;
}

node* mk2(string t, node* one, node* two) {
    node* newnode = new node;
    
    newnode->type = t;
    
    newnode->children[0] = one;
    newnode->children[1] = two;
    newnode->noc = 2;
    newnode->lno=lineno;
    newnode->cf=0;
    return newnode;
}

node* mk3(string t, node* one, node* two, node* three) {
    node* newnode = new node;
    
    newnode->type = t;
    
    newnode->children[0] = one;
    newnode->children[1] = two;
    newnode->children[2] = three;
    newnode->noc = 3;
    newnode->lno=lineno;
    newnode->cf=0;
    return newnode;
}

node* mk4(string t, node* one, node* two, node* three, node* four) {
    node* newnode = new node;
    
    newnode->type = t;
    
    newnode->children[0] = one;
    newnode->children[1] = two;
    newnode->children[2] = three;
    newnode->children[3] = four;
    newnode->noc = 4;
    newnode->lno=lineno;
    newnode->cf=0;
    return newnode;
}

node* mk5(string t, node* one, node* two, node* three, node* four, node* five) {
    node* newnode = new node;
    
    newnode->type = t;
    
    newnode->children[0] = one;
    newnode->children[1] = two;
    newnode->children[2] = three;
    newnode->children[3] = four;
    newnode->children[4] = five;
    newnode->noc = 5;
    newnode->lno=lineno;
    newnode->cf=0;
    return newnode;
}

node* mk6(string t, node* one, node* two, node* three, node* four, node* five, node* six) {
    node* newnode = new node;
    
    newnode->type = t;
    
    newnode->children[0] = one;
    newnode->children[1] = two;
    newnode->children[2] = three;
    newnode->children[3] = four;
    newnode->children[4] = five;
    newnode->children[5] = six;
    newnode->noc = 6;
    newnode->lno=lineno;
    newnode->cf=0;
    return newnode;
}

node* mk7(string t, node* one, node* two, node* three, node* four, node* five, node* six, node* seven) {
    node* newnode = new node;
    
    newnode->type = t;
    
    newnode->children[0] = one;
    newnode->children[1] = two;
    newnode->children[2] = three;
    newnode->children[3] = four;
    newnode->children[4] = five;
    newnode->children[5] = six;
    newnode->children[6] = seven;
    newnode->noc = 7;
    newnode->lno=lineno;
    newnode->cf=0;
    return newnode;
}


void freenodes(node* root) {
    if(root->noc == 0) {
        free(root); 
        return;
    }
    int i;
    for(int i = 0; i < root->noc; i++)
        free(root->children[i]);
    free(root);
}

string getlabel() {
    return (".L" + to_string(ctr++)); 
}

void ifblock(node* root){
	if(root==NULL){
		return;
	}
	if(root->type=="stmt" && root->children[0]->type=="if_stmt"){
		ifflag = 1;
		if(root->children[0]->children[2]->children[0]->type=="Pexpr"){
			if(root->children[0]->children[2]->children[0]->children[0]->type=="integerLit" && stoi(root->children[0]->children[2]->children[0]->children[0]->children[0]->type)){
				ifline = root->children[0]->children[2]->lno;
				root->children[0] = root->children[0]->children[4]->children[0];
				if_sim=1;
				if_sim1=1;
				return;
			}
			if(root->children[0]->children[2]->children[0]->children[0]->type=="integerLit" && root->children[0]->children[5]!=NULL){
				ifline = root->children[0]->children[2]->lno;
				root->children[0] = root->children[0]->children[6]->children[0];
				if_sim=1;
				if_sim1=0;
				//ifline = root->children[0]->children[2]->lno;
				return;
			}
			if(root->children[0]->children[2]->children[0]->children[0]->type=="integerLit" && root->children[0]->children[5]==NULL){
				ifline = root->children[0]->children[2]->lno;
				root->children[0]=NULL;
				if_sim=1;
				if_sim1=0;
				//ifline = root->children[0]->children[2]->lno;
				return;
			}
		}
		else if(root->children[0]->children[2]->children[0]->type=="||"){
			if(root->children[0]->children[2]->children[0]->children[0]->children[0]->type=="integerLit" && root->children[0]->children[2]->children[0]->children[1]->children[0]->type=="integerLit"){
				int val = stoi(root->children[0]->children[2]->children[0]->children[0]->children[0]->children[0]->type) || stoi(root->children[0]->children[2]->children[0]->children[1]->children[0]->children[0]->type);
				if(val){
					ifline = root->children[0]->children[2]->lno;
					root->children[0] = root->children[0]->children[4]->children[0];
					if_sim=1;
					if_sim1=1;
					//ifline = root->children[0]->children[2]->lno;
					return;
				}
				if(!val && root->children[0]->children[5]!=NULL){
					ifline = root->children[0]->children[2]->lno;
					root->children[0] = root->children[0]->children[6]->children[0];
					if_sim=1;
					if_sim1=0;
					//ifline = root->children[0]->children[2]->lno;
					return;
				}
				if(!val && root->children[0]->children[5]==NULL){
					ifline = root->children[0]->children[2]->lno;
					root->children[0]=NULL;
					if_sim=1;
					if_sim1=0;
					//ifline = root->children[0]->children[2]->lno;
					return;
				}
			}
		}
		else if(root->children[0]->children[2]->children[0]->type=="=="){
			if(root->children[0]->children[2]->children[0]->children[0]->children[0]->type=="integerLit" && root->children[0]->children[2]->children[0]->children[1]->children[0]->type=="integerLit"){
				int val = stoi(root->children[0]->children[2]->children[0]->children[0]->children[0]->children[0]->type) == stoi(root->children[0]->children[2]->children[0]->children[1]->children[0]->children[0]->type);
				if(val){
					ifline = root->children[0]->children[2]->lno;
					root->children[0] = root->children[0]->children[4]->children[0];
					if_sim=1;
					if_sim1=1;
					//ifline = root->children[0]->children[2]->lno;
					return;
				}
				if(!val && root->children[0]->children[5]!=NULL){
					ifline = root->children[0]->children[2]->lno;
					root->children[0] = root->children[0]->children[6]->children[0];
					if_sim=1;
					if_sim1=0;
					//ifline = root->children[0]->children[2]->lno;
					return;
				}
				if(!val && root->children[0]->children[5]==NULL){
				//cout<<"lplplplpl"<<endl;
					ifline = root->children[0]->children[2]->lno;
					root->children[0]=NULL;
					if_sim=1;
					if_sim1=0;
					return;
				}
			}
		}
		else if(root->children[0]->children[2]->children[0]->type=="!="){
			if(root->children[0]->children[2]->children[0]->children[0]->children[0]->type=="integerLit" && root->children[0]->children[2]->children[0]->children[1]->children[0]->type=="integerLit"){
				int val = stoi(root->children[0]->children[2]->children[0]->children[0]->children[0]->children[0]->type) != stoi(root->children[0]->children[2]->children[0]->children[1]->children[0]->children[0]->type);
				if(val){
					ifline = root->children[0]->children[2]->lno;
					root->children[0] = root->children[0]->children[4]->children[0];
					if_sim=1;
					if_sim1=1;
					//ifline = root->children[0]->children[2]->lno;
					return;
				}
				if(!val && root->children[0]->children[5]!=NULL){
					ifline = root->children[0]->children[2]->lno;
					root->children[0] = root->children[0]->children[6]->children[0];
					if_sim=1;
					if_sim1=0;
					return;
				}
				if(!val && root->children[0]->children[5]==NULL){
					ifline = root->children[0]->children[2]->lno;
					root->children[0]=NULL;
					if_sim=1;
					if_sim1=0;
					return;
				}
			}
		}
		else if(root->children[0]->children[2]->children[0]->type=="<"){
			if(root->children[0]->children[2]->children[0]->children[0]->children[0]->type=="integerLit" && root->children[0]->children[2]->children[0]->children[1]->children[0]->type=="integerLit"){
				int val = stoi(root->children[0]->children[2]->children[0]->children[0]->children[0]->children[0]->type) < stoi(root->children[0]->children[2]->children[0]->children[1]->children[0]->children[0]->type);
				if(val){
					ifline = root->children[0]->children[2]->lno;
					root->children[0] = root->children[0]->children[4]->children[0];
					if_sim=1;
					if_sim1=1;
					return;
				}
				if(!val && root->children[0]->children[5]!=NULL){
					ifline = root->children[0]->children[2]->lno;
					root->children[0] = root->children[0]->children[6]->children[0];
					if_sim=1;
					if_sim1=0;
					return;
				}
				if(!val && root->children[0]->children[5]==NULL){
					ifline = root->children[0]->children[2]->lno;
					root->children[0]=NULL;
					if_sim=1;
					if_sim1=0;
					return;
				}
			}
		}
		else if(root->children[0]->children[2]->children[0]->type=="<="){
			if(root->children[0]->children[2]->children[0]->children[0]->children[0]->type=="integerLit" && root->children[0]->children[2]->children[0]->children[1]->children[0]->type=="integerLit"){
				int val = stoi(root->children[0]->children[2]->children[0]->children[0]->children[0]->children[0]->type) <= stoi(root->children[0]->children[2]->children[0]->children[1]->children[0]->children[0]->type);
				if(val){
					ifline = root->children[0]->children[2]->lno;
					root->children[0] = root->children[0]->children[4]->children[0];
					if_sim=1;
					if_sim1=1;
					return;
				}
				if(!val && root->children[0]->children[5]!=NULL){
					ifline = root->children[0]->children[2]->lno;
					root->children[0] = root->children[0]->children[6]->children[0];
					if_sim=1;
					if_sim1=0;
					return;
				}
				if(!val && root->children[0]->children[5]==NULL){
					ifline = root->children[0]->children[2]->lno;
					root->children[0]=NULL;
					if_sim=1;
					if_sim1=0;
					return;
				}
			}
		}
		else if(root->children[0]->children[2]->children[0]->type==">"){
			if(root->children[0]->children[2]->children[0]->children[0]->children[0]->type=="integerLit" && root->children[0]->children[2]->children[0]->children[1]->children[0]->type=="integerLit"){
				int val = stoi(root->children[0]->children[2]->children[0]->children[0]->children[0]->children[0]->type) > stoi(root->children[0]->children[2]->children[0]->children[1]->children[0]->children[0]->type);
				if(val){
					ifline = root->children[0]->children[2]->lno;
					root->children[0] = root->children[0]->children[4]->children[0];
					if_sim=1;
					if_sim1=1;
					return;
				}
				if(!val && root->children[0]->children[5]!=NULL){
				//cout<<"LPLPL"<<endl;
				//cout<<root->type<<root->children[0]->children[6]->type<<endl;
					ifline = root->children[0]->children[2]->lno;
					root->children[0] = root->children[0]->children[6]->children[0];
					if_sim=1;
					if_sim1=0;
					return;
				}
				if(!val && root->children[0]->children[5]==NULL){
					ifline = root->children[0]->children[2]->lno;
					root->children[0]=NULL;
					if_sim=1;
					if_sim1=0;
					return;
				}
			}
		}
		else if(root->children[0]->children[2]->children[0]->type==">="){
			if(root->children[0]->children[2]->children[0]->children[0]->children[0]->type=="integerLit" && root->children[0]->children[2]->children[0]->children[1]->children[0]->type=="integerLit"){
				int val = stoi(root->children[0]->children[2]->children[0]->children[0]->children[0]->children[0]->type) >= stoi(root->children[0]->children[2]->children[0]->children[1]->children[0]->children[0]->type);
				if(val){
					ifline = root->children[0]->children[2]->lno;
					root->children[0] = root->children[0]->children[4]->children[0];
					if_sim=1;
					if_sim1=1;
					return;
				}
				if(!val && root->children[0]->children[5]!=NULL){
					ifline = root->children[0]->children[2]->lno;
					root->children[0] = root->children[0]->children[6]->children[0];
					if_sim=1;
					if_sim1=0;
					return;
				}
				if(!val && root->children[0]->children[5]==NULL){
					ifline = root->children[0]->children[2]->lno;
					root->children[0]=NULL;
					if_sim=1;
					if_sim1=0;
					return;
				}
			}
		}
	}
	for(int i=0;i<10;i++){
		ifblock(root->children[i]);
	}
}


void const_fold(node* root){
	if(root==NULL){
		return;
	}
	else if(root->type=="if_stmt"){
		if(!ifflag){
			const_fold(root->children[2]);
			ffold=1;
		}
		else{
			map<string,int> temp1 = stab;
			map<string,int> temp2 = avail;
			const_fold(root->children[4]);
			stab = temp1;
			avail = temp2;
			const_fold(root->children[6]);
			stab = temp1;
			avail = temp2;
		}
		return;
	}
	for(int i=0;i<10;i++){
		if(!ffold){
			const_fold(root->children[i]);
		}
	}
	if(root->type=="expr"){
		if(root->children[0]->type=="+"){
			if((root->children[0]->children[0]->children[0]->type=="integerLit") && (root->children[0]->children[1]->children[0]->type=="integerLit")){
				int val = stoi(root->children[0]->children[0]->children[0]->children[0]->type) + stoi(root->children[0]->children[1]->children[0]->children[0]->type);
				node* t = mk0(to_string(val));
				t->cf=1;
				t->lno=root->children[0]->children[0]->lno;
				node* m = mk1("integerLit",t);
				m->lno=root->children[0]->children[0]->lno;
				root->children[0]->type="Pexpr";
				root->children[0]->children[0]=m;
				root->children[0]->children[1]=NULL;
				cfold=1;
			}
		}
		if(root->children[0]->type=="-"){
			if((root->children[0]->children[0]->children[0]->type=="integerLit") && (root->children[0]->children[1]->children[0]->type=="integerLit")){
				int val = stoi(root->children[0]->children[0]->children[0]->children[0]->type) - stoi(root->children[0]->children[1]->children[0]->children[0]->type);
				node* t = mk0(to_string(val));
				t->cf=1;
				t->lno = root->children[0]->children[0]->lno;
				node* m = mk1("integerLit",t);
				m->lno=root->children[0]->children[0]->lno;
				root->children[0]->type="Pexpr";
				root->children[0]->children[0]=m;
				root->children[0]->children[1]=NULL;
				cfold=1;
			}
		}
		if(root->children[0]->type=="*"){
			if((root->children[0]->children[0]->children[0]->type=="integerLit") && (root->children[0]->children[1]->children[0]->type=="integerLit")){
				int val = stoi(root->children[0]->children[0]->children[0]->children[0]->type) * stoi(root->children[0]->children[1]->children[0]->children[0]->type);
				node* t = mk0(to_string(val));
				t->cf=1;
				t->lno=root->children[0]->children[0]->lno;
				node* m = mk1("integerLit",t);
				m->lno=root->children[0]->children[0]->lno;
				root->children[0]->type="Pexpr";
				root->children[0]->children[0]=m;
				root->children[0]->children[1]=NULL;
				cfold=1;
			}
		}
		if(root->children[0]->type==">"){
			if((root->children[0]->children[0]->children[0]->type=="integerLit") && (root->children[0]->children[1]->children[0]->type=="integerLit")){
				int val = stoi(root->children[0]->children[0]->children[0]->children[0]->type) > stoi(root->children[0]->children[1]->children[0]->children[0]->type);
				node* t = mk0(to_string(val));
				t->cf=1;
				t->lno=root->children[0]->children[0]->lno;
				node* m = mk1("integerLit",t);
				m->lno=root->children[0]->children[0]->lno;
				root->children[0]->type="Pexpr";
				root->children[0]->children[0]=m;
				root->children[0]->children[1]=NULL;
				cfold=1;
			}
		}
		if(root->children[0]->type==">="){
			if((root->children[0]->children[0]->children[0]->type=="integerLit") && (root->children[0]->children[1]->children[0]->type=="integerLit")){
				int val = stoi(root->children[0]->children[0]->children[0]->children[0]->type) >= stoi(root->children[0]->children[1]->children[0]->children[0]->type);
				node* t = mk0(to_string(val));
				t->cf=1;
				t->lno=root->children[0]->children[0]->lno;
				node* m = mk1("integerLit",t);
				m->lno=root->children[0]->children[0]->lno;
				root->children[0]->type="Pexpr";
				root->children[0]->children[0]=m;
				root->children[0]->children[1]=NULL;
				cfold=1;
			}
		}
		if(root->children[0]->type=="<"){
			if((root->children[0]->children[0]->children[0]->type=="integerLit") && (root->children[0]->children[1]->children[0]->type=="integerLit")){
				int val = stoi(root->children[0]->children[0]->children[0]->children[0]->type) < stoi(root->children[0]->children[1]->children[0]->children[0]->type);
				node* t = mk0(to_string(val));
				t->cf=1;
				t->lno=root->children[0]->children[0]->lno;
				node* m = mk1("integerLit",t);
				m->lno=root->children[0]->children[0]->lno;
				root->children[0]->type="Pexpr";
				root->children[0]->children[0]=m;
				root->children[0]->children[1]=NULL;
				cfold=1;
			}
		}
		if(root->children[0]->type=="<="){
			if((root->children[0]->children[0]->children[0]->type=="integerLit") && (root->children[0]->children[1]->children[0]->type=="integerLit")){
				int val = stoi(root->children[0]->children[0]->children[0]->children[0]->type) <= stoi(root->children[0]->children[1]->children[0]->children[0]->type);
				node* t = mk0(to_string(val));
				t->cf=1;
				t->lno=root->children[0]->children[0]->lno;
				node* m = mk1("integerLit",t);
				m->lno=root->children[0]->children[0]->lno;
				root->children[0]->type="Pexpr";
				root->children[0]->children[0]=m;
				root->children[0]->children[1]=NULL;
				cfold=1;
			}
		}
		if(root->children[0]->type=="=="){
			if((root->children[0]->children[0]->children[0]->type=="integerLit") && (root->children[0]->children[1]->children[0]->type=="integerLit")){
				int val = stoi(root->children[0]->children[0]->children[0]->children[0]->type) == stoi(root->children[0]->children[1]->children[0]->children[0]->type);
				node* t = mk0(to_string(val));
				t->cf=1;
				t->lno=root->children[0]->children[0]->lno;
				node* m = mk1("integerLit",t);
				m->lno=root->children[0]->children[0]->lno;
				root->children[0]->type="Pexpr";
				root->children[0]->children[0]=m;
				root->children[0]->children[1]=NULL;
				cfold=1;
			}
		}
		if(root->children[0]->type=="!="){
			if((root->children[0]->children[0]->children[0]->type=="integerLit") && (root->children[0]->children[1]->children[0]->type=="integerLit")){
				int val = stoi(root->children[0]->children[0]->children[0]->children[0]->type) != stoi(root->children[0]->children[1]->children[0]->children[0]->type);
				node* t = mk0(to_string(val));
				t->cf=1;
				t->lno=root->children[0]->children[0]->lno;
				node* m = mk1("integerLit",t);
				m->lno=root->children[0]->children[0]->lno;
				root->children[0]->type="Pexpr";
				root->children[0]->children[0]=m;
				root->children[0]->children[1]=NULL;
				cfold=1;
			}
		}
	}
	if(root->type=="Pexpr" && root->children[0]->type=="(" && root->children[1]->children[0]->children[0]->type=="integerLit"){
	//cout<<root->children[1]->children[0]->type<<endl;
		root->children[0]=root->children[1]->children[0]->children[0];
		root->children[1]=NULL;
		root->children[2]=NULL;
	}
}

void const_prop(node* root){
	if(root==NULL){
		return;
	}
	if(root->type=="if_stmt"){
		if(!ifflag){
			const_prop(root->children[2]);
			fprop=1;
		}
		else{
			map<string,int> temp1 = stab;
			map<string,int> temp2 = avail;
			const_prop(root->children[4]);
			stab = temp1;
			avail = temp2;
			const_prop(root->children[6]);
			stab = temp1;
			avail = temp2;
		}
		return;
	}
	for(int i=0;i<10;i++){
		if(!fprop){
			const_prop(root->children[i]);
		}
	}
	if(root->type=="="){
		if(root->children[1]->children[0]->children[0]->type=="integerLit"){
			stab[root->children[0]->children[0]->type]=stoi(root->children[1]->children[0]->children[0]->children[0]->type);
			avail[root->children[0]->children[0]->type] = 1;
		}
		else{
			avail[root->children[0]->children[0]->type] = 0;
		}
	}
	if(root->type=="Pexpr" && root->children[0]->type=="IDENTIFIER"){
		if(avail[root->children[0]->children[0]->type]){
			//cout<<root->children[0]->children[0]->type<<endl;
			string var = root->children[0]->children[0]->type;
			root->children[0]->type="integerLit";
			root->children[0]->children[0]->type = to_string(stab[root->children[0]->children[0]->type]);
			cprop=1;
			//cout<<"LOL"<<endl;
			if(cpmap.find(root->lno)!=cpmap.end()){
				vector<pair<string,int> > temp = cpmap[root->lno];
				if(find(temp.begin(),temp.end(),make_pair(var,stab[var]))==temp.end()){
					temp.push_back(make_pair(var,stab[var]));
					cpmap[root->lno] = temp;
				}
			}
			else{
				vector<pair<string,int> > temp;
				temp.push_back(make_pair(var,stab[var]));
				cpmap[root->lno] = temp;
			}
		}
	}
	if(root->type=="scan_stmt"){
	//cout<<"LOL"<<endl;
		avail[root->children[0]->children[0]->type]=0;
	}
	if(root->type=="print_stmt"){
		if(avail[root->children[0]->children[0]->type]){
			string var = root->children[0]->children[0]->type;
			if(cpmap.find(root->lno)!=cpmap.end()){
				vector<pair<string,int> > temp = cpmap[root->lno];
				if(find(temp.begin(),temp.end(),make_pair(var,stab[var]))==temp.end()){
					temp.push_back(make_pair(var,stab[var]));
					cpmap[root->lno] = temp;
				}
			}
			else{
				vector<pair<string,int> > temp;
				temp.push_back(make_pair(var,stab[var]));
				cpmap[root->lno] = temp;
			}
		}
		return;
	}
	//print
}

void unusedvar(node* root){
	if(root==NULL){
		return;
	}
	if(root->type=="local_decl"){
		uvar.push_back(root->children[1]->children[0]->type);
		varlno[root->children[1]->children[0]->type]=root->lno;
	}
	if(root->type=="IDENTIFIER"){
		umap[root->children[0]->type]++;
	}
	for(int i=0;i<10;i++){
		unusedvar(root->children[i]);
	}
}

/*void fold_sum(node* root){
	if(root==NULL){
		return;
	}
	if(root->type=="expr"){
		fold_sum1(root);
		if(maxx!=INT_MIN){
			cfvec.push_back(make_pair(root->lno,maxx));
		}
		maxx=INT_MIN;
		return;
	}
	for(int i=0;i<10;i++){
		fold_sum(root->children[i]);
	}
}

void fold_sum1(node* root){
	if(root==NULL){
		return;
	}
	if(root->cf==1 && stoi(root->type)>maxx){
		maxx=stoi(root->type);
	}
	for(int i=0;i<10;i++){
		fold_sum1(root->children[i]);
	}
}*/

void fold_s(node* root){
	if(root==NULL){
		return;
	}
	if(root->type=="integerLit"){
		fsum[root->lno].push_back(root->children[0]);
		return;
	}
	for(int i=0;i<10;i++){
		fold_s(root->children[i]);
	}
}

bool compare(const pair<string,int> &a, const pair<string,int> &b){
	return varlno[a.first]<varlno[b.first];
}

void sred_sum(node* root){
	if(root==NULL){
		return;
	}
	if(root->type=="*" && root->children[0]->children[0]->type=="integerLit"){
		if(stoi(root->children[0]->children[0]->children[0]->type)<1){
			return;
		}
		int val = ceil(log2(stoi(root->children[0]->children[0]->children[0]->type))) == floor(log2(stoi(root->children[0]->children[0]->children[0]->type)));
		if(val){
			if(sredmap.find(root->lno)!=sredmap.end() && sredmap[root->lno]<log2(stoi(root->children[0]->children[0]->children[0]->type))){
				sredmap[root->lno]=log2(stoi(root->children[0]->children[0]->children[0]->type));
			}
			else if(sredmap.find(root->lno)==sredmap.end()){
				sredmap[root->lno]=log2(stoi(root->children[0]->children[0]->children[0]->type));
			}
		}
		return;
	}
	if(root->type=="*" && root->children[1]->children[0]->type=="integerLit"){
		if(stoi(root->children[1]->children[0]->children[0]->type)<1){
			return;
		}
		int val = ceil(log2(stoi(root->children[1]->children[0]->children[0]->type))) == floor(log2(stoi(root->children[1]->children[0]->children[0]->type)));
		if(val){
			if(sredmap.find(root->lno)!=sredmap.end() && sredmap[root->lno]<log2(stoi(root->children[1]->children[0]->children[0]->type))){
				sredmap[root->lno]=log2(stoi(root->children[1]->children[0]->children[0]->type));
			}
			else if(sredmap.find(root->lno)==sredmap.end()){
				sredmap[root->lno]=log2(stoi(root->children[1]->children[0]->children[0]->type));
			}
		}
		return;
	}
	for(int i=0;i<10;i++){
		sred_sum(root->children[i]);
	}
}

void cse_ssa(node* root){
	if(root==NULL){
		return;
	}
	if(root->type=="IDENTIFIER"){
		root->children[0]->attr=csemap[root->children[0]->type];
		return;
	}
	if(root->type=="="){
		cse_ssa(root->children[1]);
		csemap[root->children[0]->children[0]->type]++;
		root->children[0]->children[0]->attr = csemap[root->children[0]->children[0]->type];
		return;		
	}
	if(root->type=="scan_stmt"){
		csemap[root->children[0]->children[0]->type]++;
		root->children[0]->children[0]->attr = csemap[root->children[0]->children[0]->type];
		return;
	}
	if(root->type=="if_stmt"){
		cse_ssa(root->children[2]);
		map<string,int> temp = csemap;
		cse_ssa(root->children[4]);
		csemap = temp;
		cse_ssa(root->children[6]);
		//csemap=temp;
		return;
	}
	for(int i=0;i<10;i++){
		cse_ssa(root->children[i]);
	}
}

void cse_vecform(node* root){
	if(root==NULL){
		return;
	}
	for(int i=0;i<10;i++){
		cse_vecform(root->children[i]);
	}
	if(root->type=="expr" && root->children[0]->children[0]->type!="integerLit" && root->children[0]->children[0]->type!="IDENTIFIER"){
		csevec.push_back(root);
	}
}

int cse_equal(node* root1,node* root2){
	if((root1==NULL || root1->type=="epsilon") && (root2==NULL || root2->type=="epsilon")){
		return 1;
	}
	if((root1!=NULL && root1->type!="epsilon") && (root2==NULL || root2->type=="epsilon")){
		return 0;
	}
	if((root1==NULL || root1->type=="epsilon") && (root2!=NULL && root2->type!="epsilon")){
		return 0;
	}
	//check
	if(root1->type!=root2->type){
		return 0;
	}
	if(root1->type=="IDENTIFIER" && root2->type=="IDENTIFIER"){
		if((root1->children[0]->type == root2->children[0]->type) && (root1->children[0]->attr == root2->children[0]->attr)){
			return 1;
		}
		else{
			return 0;
		}
	}
	for(int i=0;i<10;i++){
		if(cse_equal(root1->children[i],root2->children[i])==0){
			return 0;
		}
	}
	return 1;
}

bool compare1(const vector<int> &a,const vector<int> &b){
	return a[0]<b[0];
}

// void printtree(node* root) {
//     nn++;
//     printf("%s--->",root->type);
//     for(int i=0;i<root->noc;i++)
//         printf("(%i~~%s)    ",i,root->children[i]->type);
//     printf("\n\n\n");
//     for(int i=0;i<root->noc;i++)
//         printtree(root->children[i]);
// }
