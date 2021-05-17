%{
#include <stdio.h>
#include <iostream>
#include <string>
#include <unordered_map>
#include <cassert>
#include <vector>
#include <deque>
using namespace std;
#define YYSTYPE void *
extern FILE* yyin;
extern FILE* yyout;
extern int yylex();
extern int yylineno;
class WhileLoop;
class Function;
class Var;
void yyerror(const char *msg)
{
    cerr<<"line: "<<yylineno<<"\t" << msg << endl;
    exit(1);
}

bool InRange(int num,int bits)
{
    int low=-(1<<(bits-1));
    int high=(1<<(bits-1))-1;
    return num>=low && num<=high;
}

string indent;
bool TimerOn=false;
const int INT_SIZE=4;

vector<string>pre_eeyore;

void emit(string s)
{
    //cout << indent << s << endl;
    pre_eeyore.push_back(s);
}
class Env
{
public:
    unordered_map<string, Var *> var_table;
    Env *prev;
    bool is_param;
    Env(Env *n,bool IsParam) : prev(n),is_param(IsParam) {}
    void put(string name, Var *p)
    {
        assert(p != NULL);
        if(var_table.find(name)!=var_table.end())
            yyerror("variable redefined");
        if(prev!=NULL && prev->is_param==true)
            if(prev->var_table.find(name)!=prev->var_table.end())
                yyerror("function parameter shadowed");
        var_table.insert(make_pair(name, p));
    }
    Var *get(string name)
    {
        Env *n=this;
        while(n!=NULL)
        {
            auto found=n->var_table.find(name);
            if(found!=n->var_table.end())
                return found->second;
            else
                n=n->prev;
        }
        return NULL;
    }
};
const int MAX_PARAMS=8;
class Function
{
public:
    int param_count;
    int retval;
    int stack_size;
    Function(int p,int rv):param_count(p),retval(rv),stack_size(INT_SIZE*MAX_PARAMS){}
    int STK()
    {
        return ((stack_size/INT_SIZE) / 4 + 1) * 16;
    }
};
class Parser
{
public:
    Env *top;
    vector<WhileLoop*>while_stack;
    unordered_map<string,Function*>func_table;
    Function*cur_func;
    int global_var_cnt;
    Parser() : top(new Env(NULL,false)),cur_func(NULL),global_var_cnt(0) {}
    void NewEnv(bool IsParam)
    {
        top = new Env(top,IsParam);
    }
    void DeleteEnv()
    {
        top = top->prev;
    }
    void PutFunc(string name,Function*f)
    {
        if(func_table.find(name)!=func_table.end())
            yyerror("function redefined\n");
        func_table.insert(make_pair(name,f));
    }
    Function* GetFunc(string name)
    {
        auto found=func_table.find(name);
        if(found==func_table.end())
            return NULL;
        return found->second;
    }
};
Parser parser;
class Var
{
public:
    static int count;
    int SeqNo;
    bool is_param;
    bool is_const;
    int value;//valid only when is_const==true
    deque<int>shape;//judge whether being an array from the size of "shape"
    vector<int>element_value;//valid only when this is an array
    bool is_access;//whether being array access
    Var* array_name;//valid only when is_access==true
    Var* offset;//valid only when is_access==true
    bool is_global;
    int global_no;
    int stack_offset;

    Var() : SeqNo(count++),is_param(false),is_const(false),is_access(false),
    is_global(parser.cur_func==NULL)
    {
        decl();
    }

    Var(int seq):SeqNo(seq),is_param(true),is_const(false),is_access(false),
    is_global(parser.cur_func==NULL){}

    Var(bool IsConst,int v):
    is_const(IsConst),value(v),is_param(false),SeqNo(-1),is_access(false),
    is_global(parser.cur_func==NULL){}

    Var(bool IsConst,deque<int>*dq,
    bool IsParam,int seq=-1,
    bool IsAccess=false,Var *ArrayName=NULL,Var *Off=NULL):
    is_const(IsConst),
    is_param(IsParam),
    is_access(IsAccess),array_name(ArrayName),offset(Off),
    is_global(parser.cur_func==NULL)
    {
        if(dq)
            shape=*dq;

        if(is_access==false)
        {
            if(is_param)
                SeqNo=seq;
            else if(is_const==false || dq->size()>0)
            {
                SeqNo=count++;
                if(dq->size()>0)
                    decl_array();  
                else
                    decl();              
            }
            element_value=vector<int>(size(),0);
        }
    }

    bool is_array()
    {
        return shape.size()!=0;
    }
    int size()
    {
        int ans=1;
        for(int i:shape)
            ans*=i;
        return ans;
    }
    deque<int>* size_of_each_dimension()
    {
        deque<int>*ans=new deque<int>;
        ans->push_front(INT_SIZE);
        for(int i=shape.size()-1;i>=1;i--)
            ans->push_front(ans->front()*shape[i]);
        return ans;
    }
    string getname(int t)
    {
        return "t"+to_string(t);
    }
    void decl()
    {
        is_global=parser.cur_func==NULL;
        if(is_global)
        {
            global_no=parser.global_var_cnt++;
            emit(".comm\tv"+to_string(global_no)+", 4, 4");
        }
        else
        {
            stack_offset=parser.cur_func->stack_size;
            parser.cur_func->stack_size+=size()*INT_SIZE;
        }
    }
    void decl_array()
    {
        is_global=parser.cur_func==NULL;
        if(is_global)
        {
            global_no=parser.global_var_cnt++;
            emit(".comm\tv"+to_string(global_no)+", "+to_string(size()*INT_SIZE)+", 4");
        }
        else
        {
            stack_offset=parser.cur_func->stack_size;
            parser.cur_func->stack_size+=size()*INT_SIZE;
        }        
    }
    void load(string reg)
    {
        if(is_access)
        {
            array_name->load("t3");
            if(offset->is_const&&InRange(offset->value,12))
                emit("addi\tt5, t3, "+to_string(offset->value));
            else
            {
                offset->load("t4");
                //emit("t5 = "+array_name->getname(3)+" + "+offset->getname(4));
                emit("add\tt5, t3, t4");
            }
            //emit(reg+" = t5[0]");
            emit("lw\t"+reg+", 0(t5)");

        }
        else if(is_param)
        {
            //emit("load "+to_string(SeqNo)+" "+reg);
            if(InRange(SeqNo*4,12))
                emit("lw\t"+reg+", "+to_string(SeqNo*4)+"(sp)");
            else
            {
                emit("li\ts0, "+to_string(SeqNo*4));
                emit("add\ts0, s0, sp");
                emit("lw\t"+reg+", 0(s0)");
            }
        }
        else if(is_const&&!is_array())
            emit("li\t"+reg+", "+to_string(value));
        else if(is_global)
        {
            if(is_array())
                emit("la\t"+reg+", v"+to_string(global_no));
            else
            {
                emit("lui\t"+reg+", %hi(v"+to_string(global_no)+")");
                emit("lw\t"+reg+", %lo(v"+to_string(global_no)+")("+reg+")");
            }
        }
        else if(is_array())
        {
            if(InRange(stack_offset,12))
                emit("addi\t"+reg+", sp, "+to_string(stack_offset));
            else
            {
                emit("li\ts0, "+to_string(stack_offset));
                emit("add\t"+reg+", sp, s0");
            }
        }
        else
        {
            if(InRange(stack_offset,12))
                emit("lw\t"+reg+", "+to_string(stack_offset)+"(sp)");
            else
            {
                emit("li\ts0, "+to_string(stack_offset));
                emit("add\ts0, s0, sp");
                emit("lw\t"+reg+", 0(s0)");
            }
        }
    }
    void store(string reg)
    {
        if(is_access)
        {
            array_name->load("t3");
            if(offset->is_const&&InRange(offset->value,12))
                emit("addi\tt5, t3, "+to_string(offset->value));
            else
            {            
                offset->load("t4");
                //emit("t5 = "+array_name->getname(3)+" + "+offset->getname(4));
                emit("add\tt5, t3, t4");
            }
            //emit("t5[0] = "+reg);
            emit("sw\t"+reg+", 0(t5)");
        }
        else if(is_param)
        {
            //emit("store "+reg+" "+to_string(SeqNo));
            if(InRange(SeqNo*4,12))
                emit("sw\t"+reg+", "+to_string(SeqNo*4)+"(sp)");
            else
            {            
                emit("li\ts0, "+to_string(SeqNo*4));
                emit("add\ts0, s0, sp");
                emit("sw\t"+reg+", 0(s0)");
            }
        }
        else if(is_const&&!is_array())
        {
        }
        else if(is_global)
        {
            emit("la\tt3, v"+to_string(global_no));
            emit("sw\t"+reg+", 0(t3)");
        }
        else if(is_array())
        {
        }
        else
        {
            if(InRange(stack_offset,12))
                emit("sw\t"+reg+", "+to_string(stack_offset)+"(sp)");
            else
            {            
                emit("li\ts0, "+to_string(stack_offset));
                emit("add\ts0, s0, sp");
                emit("sw\t"+reg+", 0(s0)");
            }
        }
    }
};
int Var::count = 0;

int NewLabel()
{
    static int labels=0;
    return labels++;
}
void emitLabel(int i)
{
    emit(".l"+to_string(i)+":");
}
class JumpAddr
{
public:
    int TrueLabel;
    int FalseLabel;
    JumpAddr(int t,int f):TrueLabel(t),FalseLabel(f){}
};
class IfStmt
{
public:
    int True;
    int False;
    int After;
    IfStmt(int t,int f,int a):True(t),False(f),After(a){}
};
class WhileLoop
{
public:
    int Begin;
    int Body;
    int After;
    WhileLoop(int be,int bo,int a):Begin(be),Body(bo),After(a){}
};

class Initializer
{
public:
    Var*var_to_init;
    deque<int>batch_size;
    int pos;
    int batch_size_index;
    void compute_batch_size()
    {
        batch_size=var_to_init->shape;
        if(var_to_init->is_array())
            for(int i=batch_size.size()-2;i>=0;i--)
                batch_size[i]*=batch_size[i+1];
    }
    void set(Var*var)
    {
        var_to_init=var;
        compute_batch_size();
        pos=0;
        batch_size_index=-1;
    }
    bool is_array()
    {
        return batch_size.size()>0;
    }
    int get_batch_size()
    {
        return batch_size[batch_size_index];
    }
};
Initializer initializer;
%}

%token INT CONST VOID
%token IF ELSE WHILE BREAK CONTINUE RETURN
%token AND OR EQ NE LE GE
%token IDENT INT_CONST
%%

CompUnits     : CompUnits CompUnit
              |
              ;
CompUnit      : Decl
              | FuncDef
              ;
Decl          : ConstDecl
              | VarDecl
              ;
ConstDecl     : CONST INT ConstDefs ';'
              ;
ConstDefs     : ConstDefs ',' ConstDef
              | ConstDef
              ;
ConstDef      : IDENT ConstExpList
                {
                    string name=*(string*)$1;
                    if(((deque<int>*)$2)->size()==0)//scalar variable
                        $$=new Var(true,0);
                    else//array variable
                        $$=new Var(true,(deque<int>*)$2,false);
                    parser.top->put(name,(Var*)$$);
                    initializer.set((Var*)$$);
                }
                 '=' ConstInitVal
              ;
ConstExpList  : ConstExpList '[' ConstExp ']'
                {
                    $$=$1;
                    ((deque<int>*)$$)->push_back(((Var*)$3)->value);
                }
              | {$$=new deque<int>;}
              ;
ConstInitVal  : ConstExp
                {
                    if(initializer.is_array())
                    {
                        initializer.var_to_init->load("t0");
                        ((Var*)$1)->load("t1");
                        //emit(initializer.var_to_init->getname(0)+
                        //"["+to_string(initializer.pos*INT_SIZE)+"] = "
                        //+((Var*)$1)->getname(1));

                        if(InRange(initializer.pos*INT_SIZE,12))
                            emit("sw\tt1, "+to_string(initializer.pos*INT_SIZE)+"(t0)");
                        else
                        {
                            emit("li\ts0, "+to_string(initializer.pos*INT_SIZE));
                            emit("add\ts0, s0, t0");
                            emit("sw\tt1, 0(s0)");
                        }

                        initializer.var_to_init->element_value[initializer.pos]
                        =((Var*)$1)->value;
                        initializer.pos++;
                    }
                    else
                        initializer.var_to_init->value=((Var*)$1)->value;
                }
              | '{'
              {
                  initializer.batch_size_index++;
              } 
               ConstInitVals '}'
              {
                  for(;initializer.pos%initializer.get_batch_size()!=0;initializer.pos++)
                  {
                        initializer.var_to_init->load("t0");
                        //emit(initializer.var_to_init->getname(0)+
                        //"["+to_string(initializer.pos*INT_SIZE)+"] = x0");

                        if(InRange(initializer.pos*INT_SIZE,12))
                            emit("sw\tx0, "+to_string(initializer.pos*INT_SIZE)+"(t0)");
                        else
                        {                        
                            emit("li\ts0, "+to_string(initializer.pos*INT_SIZE));
                            emit("add\ts0, s0, t0");
                            emit("sw\tx0, 0(s0)");       
                        }                 
                  }
                  initializer.batch_size_index--;
              }               
              | '{' '}'
              {
                  initializer.batch_size_index++;
                  for(int i=0;i<initializer.get_batch_size();i++)
                  {
                        initializer.var_to_init->load("t0");
                        //emit(initializer.var_to_init->getname(0)+
                        //"["+to_string(initializer.pos*INT_SIZE)+"] = x0");

                        if(InRange(initializer.pos*INT_SIZE,12))
                            emit("sw\tx0, "+to_string(initializer.pos*INT_SIZE)+"(t0)");
                        else
                        {                        
                            emit("li\ts0, "+to_string(initializer.pos*INT_SIZE));
                            emit("add\ts0, s0, t0");
                            emit("sw\tx0, 0(s0)");                        
                        }                
                        initializer.pos++;      
                  }
                  initializer.batch_size_index--;
              }
              ;
ConstInitVals : ConstInitVals ',' ConstInitVal
              | ConstInitVal
              ;
VarDecl       : INT VarDefs ';'
              ;
VarDefs       : VarDefs ',' VarDef
              | VarDef
              ;
VarDef        : IDENT ConstExpList {
                    string name=*(string*)$1;
                    if(((deque<int>*)$2)->size()==0)//scalar variable
                    {
                        $$=new Var();
                    }
                    else//array variable
                    {
                        $$=new Var(false,(deque<int>*)$2,false);
                    }
                    parser.top->put(name,(Var*)$$);
                }
                | IDENT ConstExpList {
                    string name=*(string*)$1;
                    if(((deque<int>*)$2)->size()==0)//scalar variable
                        $$=new Var();
                    else//array variable
                        $$=new Var(false,(deque<int>*)$2,false);
                    parser.top->put(name,(Var*)$$);
                    initializer.set((Var*)$$);
                }
                '=' InitVal
              ;
InitVal       : Exp
                {
                    if(initializer.is_array())
                    {
                        initializer.var_to_init->load("t0");
                        ((Var*)$1)->load("t1");
                        //emit(initializer.var_to_init->getname(0)+
                        //"["+to_string(initializer.pos*INT_SIZE)+"] = "
                        //+((Var*)$1)->getname(1));

                        if(InRange(initializer.pos*INT_SIZE,12))
                            emit("sw\tt1, "+to_string(initializer.pos*INT_SIZE)+"(t0)");
                        else
                        {                        
                            emit("li\ts0, "+to_string(initializer.pos*INT_SIZE));
                            emit("add\ts0, s0, t0");
                            emit("sw\tt1, 0(s0)");     
                        }                   
                        initializer.pos++;
                    }
                    else
                    {
                        ((Var*)$1)->load("t0");
                        initializer.var_to_init->store("t0");
                    }
                }
              | '{'
              {
                  initializer.batch_size_index++;
              } 
              InitVals '}'
              {
                  for(;initializer.pos%initializer.get_batch_size()!=0;initializer.pos++)
                  {
                        initializer.var_to_init->load("t0");
                        //emit(initializer.var_to_init->getname(0)+
                        //"["+to_string(initializer.pos*INT_SIZE)+"] = x0");

                        if(InRange(initializer.pos*INT_SIZE,12))
                            emit("sw\tx0, "+to_string(initializer.pos*INT_SIZE)+"(t0)");
                        else
                        {                              
                            emit("li\ts0, "+to_string(initializer.pos*INT_SIZE));
                            emit("add\ts0, s0, t0");
                            emit("sw\tx0, 0(s0)");           
                        }             
                  }
                  initializer.batch_size_index--;
              }
              | '{' '}'
              {
                  initializer.batch_size_index++;
                  for(int i=0;i<initializer.get_batch_size();i++)
                  {
                        initializer.var_to_init->load("t0");
                        //emit(initializer.var_to_init->getname(0)+
                        //"["+to_string(initializer.pos*INT_SIZE)+"] = x0");

                        if(InRange(initializer.pos*INT_SIZE,12))
                            emit("sw\tx0, "+to_string(initializer.pos*INT_SIZE)+"(t0)");
                        else
                        {                              
                            emit("li\ts0, "+to_string(initializer.pos*INT_SIZE));
                            emit("add\ts0, s0, t0");
                            emit("sw\tx0, 0(s0)");     
                        }                   
                        initializer.pos++;                      
                  }
                  initializer.batch_size_index--;
              }
              ;
InitVals      : InitVals ',' InitVal
              | InitVal
              ;

FuncDef       : INT IDENT '('
                {
                    parser.NewEnv(true);
                }
                 FuncFParams ')'
                {
                    string name=*(string*)$2;
                    int param_count=*(int*)$5;

                    emit("f_"+name+" ["+to_string(param_count)+"]");

                    Function*func=new Function(param_count,INT);
                    parser.PutFunc(name,func);
                    parser.cur_func=func;

                    for(int i=0;i<param_count;i++)
                        emit("sw\ta"+to_string(i)+", "+to_string(i*4)+"(sp)");
                } 
                Block
                {
                    parser.DeleteEnv();
                    
                    emit("return");

                    string name=*(string*)$2;
                    emit("end f_"+name);
                    parser.cur_func=NULL;
                }
              | VOID IDENT '('
                {
                    parser.NewEnv(true);
                }
                 FuncFParams ')'
                {
                    string name=*(string*)$2;
                    int param_count=*(int*)$5;

                    emit("f_"+name+" ["+to_string(param_count)+"]");

                    Function*func=new Function(param_count,VOID);
                    parser.PutFunc(name,func);
                    parser.cur_func=func;

                    for(int i=0;i<param_count;i++)
                        emit("sw\ta"+to_string(i)+", "+to_string(i*4)+"(sp)");
                }  
                Block
                {
                    parser.DeleteEnv();
                    
                    emit("return");

                    string name=*(string*)$2;
                    emit("end f_"+name);
                    parser.cur_func=NULL;
                }                
              | INT IDENT '(' ')'
                {
                    string name=*(string*)$2;
                    int param_count=0;

                    emit("f_"+name+" ["+to_string(param_count)+"]");

                    Function*func=new Function(param_count,INT);
                    parser.PutFunc(name,func);
                    parser.cur_func=func;
                } 
                Block
                {               
                    emit("return");

                    string name=*(string*)$2;
                    emit("end f_"+name);
                    parser.cur_func=NULL;
                }
              | VOID IDENT '(' ')'
                {
                    string name=*(string*)$2;
                    int param_count=0;

                    emit("f_"+name+" ["+to_string(param_count)+"]");

                    Function*func=new Function(param_count,VOID);
                    parser.PutFunc(name,func);
                    parser.cur_func=func;
                } 
                  Block
                {               
                    emit("return");

                    string name=*(string*)$2;
                    emit("end f_"+name);
                    parser.cur_func=NULL;
                }             
              ;

FuncFParams   : FuncFParams ',' INT IDENT '[' ']' ConstExpList
                {
                    $$=$1;
                    (*(int*)$$)++;
                    deque<int>*shape=(deque<int>*)$7;
                    shape->push_front(0);
                    parser.top->put(*(string*)$4,new Var(false,shape,true,(*(int*)$$)-1));
                }
              |  FuncFParams ',' INT IDENT 
                {
                    $$=$1;
                    (*(int*)$$)++;
                    parser.top->put(*(string*)$4,new Var((*(int*)$$)-1));
                }                
              | INT IDENT '[' ']' ConstExpList
                {
                    $$=new int;
                    (*(int*)$$)=1;
                    deque<int>*shape=(deque<int>*)$5;
                    shape->push_front(0);
                    parser.top->put(*(string*)$2,new Var(false,shape,true,(*(int*)$$)-1));
                }
              | INT IDENT 
                {
                    $$=new int;
                    (*(int*)$$)=1;
                    parser.top->put(*(string*)$2,new Var((*(int*)$$)-1));
                }
              ;

Block         : '{' 
                {
                    parser.NewEnv(false);indent.push_back('\t');
                }
                BlockItems 
                {
                    parser.DeleteEnv();indent.pop_back();
                }
                '}'
              ;
BlockItems    : BlockItems BlockItem
              |
              ;
BlockItem     : Decl
              | Stmt
              ;
Stmt          : LVal '=' Exp ';'
                {
                    ((Var*)$3)->load("t0");
                    ((Var*)$1)->store("t0");
                }
              | Exp ';'
              | ';'
              | Block
              | IF 
              {
                  $1=new IfStmt(NewLabel(),NewLabel(),NewLabel());
              }
              '('
              {
                  $3=new JumpAddr(((IfStmt*)$1)->True,NewLabel());
              } 
              Cond ')'
              {
                  int FalseLabel=((IfStmt*)$1)->False;
                  emit("j\t.l"+to_string(FalseLabel));

                  emitLabel(((IfStmt*)$1)->True);
              } 
              Stmt DanglingElse
              | WHILE
              {
                  $1=new WhileLoop(NewLabel(),NewLabel(),NewLabel());
                  parser.while_stack.push_back((WhileLoop*)$1);
                  emitLabel(((WhileLoop*)$1)->Begin);
              } 
              '('
              {
                  $3=new JumpAddr(((WhileLoop*)$1)->Body,NewLabel());            
              } 
              Cond ')'
              {
                  int FalseLabel=((WhileLoop*)$1)->After;
                  emit("j\t.l"+to_string(FalseLabel));      

                  emitLabel(((WhileLoop*)$1)->Body);
              } 
              Stmt
              {
                  emit("j\t.l"+to_string(((WhileLoop*)$1)->Begin));   
                  emitLabel(((WhileLoop*)$1)->After);
                  parser.while_stack.pop_back();
              }
              | BREAK ';'
              {
                  if(parser.while_stack.size()==0)
                    yyerror("No While");
                  emit("j\t.l"+to_string(parser.while_stack.back()->After));
              }
              | CONTINUE ';'
              {
                  if(parser.while_stack.size()==0)
                    yyerror("No While");
                  emit("j\t.l"+to_string(parser.while_stack.back()->Begin));
              }
              | RETURN Exp ';'
              {
                  ((Var*)$2)->load("a0");
                  emit("return");
              }
              | RETURN ';' {emit("return");}
              ;
DanglingElse  : {
                  emit("j\t.l"+to_string(((IfStmt*)$-7)->After));
                  emitLabel(((IfStmt*)$-7)->False);
                } 
                ELSE Stmt
                {
                  emitLabel(((IfStmt*)$-7)->After);
                }                
              | {emitLabel(((IfStmt*)$-7)->False);}
              ;

Exp           : AddExp {$$=$1;}
              ;
Cond          : LOrExp 
              ;
LVal          : IDENT ExpList 
                {
                    string name=*(string*)$1;
                    $$=parser.top->get(name);
                    deque<Var*>&subscripts=*(deque<Var*>*)$2;
                    if(subscripts.size()>0)
                    {
                        deque<int>&size_of_each_dimension=
                        *(((Var*)$$)->size_of_each_dimension());
                        bool all_const=true;
                        for(Var*i:subscripts)
                            if(i->is_const==false)
                                all_const=false;
                        if(all_const)
                        {
                            int offset=0;
                            for(int i=0;i<subscripts.size();i++)
                                offset+=(subscripts[i]->value)*size_of_each_dimension[i];
                            if(((Var*)$$)->is_const
                            &&subscripts.size()==size_of_each_dimension.size())
                                $$=new Var(true,((Var*)$$)->element_value[offset/INT_SIZE]);
                            else
                            {
                                Var*var_offset=new Var(true,offset);
                                if(subscripts.size()==size_of_each_dimension.size())
                                    $$=new Var(false,NULL,false,-1,true,(Var*)$$,var_offset);
                                else
                                {
                                    Var*tmp=new Var();
                                    tmp->load("t1");
                                    if(var_offset->is_const&&InRange(var_offset->value,12))
                                        emit("addi\tt0, t1, "+to_string(var_offset->value));
                                    else
                                    {
                                        var_offset->load("t2");
                                        //emit(tmp->getname(0)+" = "+tmp->getname(1)+" + "+var_offset->getname(2));
                                        emit("add\tt0, t1, t2");
                                    }
                                    tmp->store("t0");
                                    $$=tmp;
                                }
                            }
                        }
                        else
                        {
                            Var*var_offset=new Var();
                            var_offset->store("x0");
                            for(int i=0;i<subscripts.size();i++)
                            {
                                Var*mul=new Var();
                                subscripts[i]->load("t1");
                                //emit("t2 = "+to_string(size_of_each_dimension[i]));
                                emit("li\tt2, "+to_string(size_of_each_dimension[i]));
                                //emit(mul->getname(0)+" = "
                                //+subscripts[i]->getname(1)+
                                //" * t2");
                                emit("mul\tt0, t1, t2");
                                mul->store("t0");

                                var_offset->load("t1");
                                mul->load("t2");
                                //emit(var_offset->getname(0)+" = "
                                //+var_offset->getname(1)+" + "+mul->getname(2));
                                emit("add\tt0, t1, t2");
                                var_offset->store("t0");
                            }
                            if(subscripts.size()==size_of_each_dimension.size())
                                $$=new Var(false,NULL,false,-1,true,(Var*)$$,var_offset);
                            else
                            {
                                Var*tmp=new Var();
                                ((Var*)$$)->load("t1");
                                var_offset->load("t2");
                                //emit(tmp->getname(0)+" = "+((Var*)$$)->getname(1)
                                //+" + "+var_offset->getname(2));
                                emit("add\tt0, t1, t2");
                                tmp->store("t0");
                                $$=tmp;
                            }
                        }
                    }
                }
              ;
ExpList       : ExpList '[' Exp ']'
                {
                    $$=$1;
                    ((deque<Var*>*)$$)->push_back((Var*)$3);
                }
              | {$$=new deque<Var*>;}
              ;
PrimaryExp    : '(' Exp ')' {$$=$2;}
              | LVal 
              {
                  if(((Var*)$1)->is_access)
                  {
                    $$=new Var();
                    ((Var*)$1)->load("t0");
                    ((Var*)$$)->store("t0");
                  }
                  else
                    $$=$1;
              }
              | INT_CONST { $$=new Var(true,*(int*)$1); }
              ;
UnaryExp      : PrimaryExp {$$=$1;}
              | IDENT '(' FuncRParams ')'
              {
                  string name=*(string*)$1;
                  auto found=parser.GetFunc(name);
                  if(found==NULL)
                    yyerror("function undefined");

                  vector<Var*>&v=*(vector<Var*>*)$3;
                  for(int i=0;i<v.size();i++)
                    v[i]->load("a"+to_string(i));

                  int retval=found->retval;
                  if(retval==INT)
                  {
                      $$=new Var();
                      emit("call\t"+name);
                      ((Var*)$$)->store("a0");
                  }
                  else if(retval==VOID)
                      emit("call\t"+name);
              }
              | IDENT '(' ')'       
              {
                  string name=*(string*)$1;
                  if(name=="starttime")
                  {
                      if(TimerOn)
                        yyerror("timer has been on");
                      TimerOn=true;
                      emit("li\ta0, "+to_string(yylineno));
                      emit("call\t_sysy_starttime");
                  }
                  else if(name=="stoptime")
                  {
                      if(!TimerOn)
                        yyerror("no timer yet");
                      TimerOn=false;
                      emit("li\ta0, "+to_string(yylineno));
                      emit("call\t_sysy_stoptime");
                  }
                  else
                  {
                        auto found=parser.GetFunc(name);
                        if(found==NULL)
                            yyerror("function undefined");
                        int retval=found->retval;
                        if(retval==INT)
                        {
                            $$=new Var();
                            emit("call\t"+name);
                            ((Var*)$$)->store("a0");
                        }
                        else if(retval==VOID)
                            emit("call\t"+name);
                  }
              }                   
              | '+' UnaryExp {$$=$2;}
              | '-' UnaryExp
                {
                    if(((Var*)$2)->is_const)
                        $$=new Var(true,-(((Var*)$2)->value));
                    else
                    {
                        $$=new Var();
                        ((Var*)$2)->load("t1");
                        //emit(((Var*)$$)->getname(0)+" = - "+((Var*)$2)->getname(1));
                        emit("neg\tt0, t1");
                        ((Var*)$$)->store("t0");
                    }
                }
              | '!' UnaryExp
                {
                    if(((Var*)$2)->is_const)
                        $$=new Var(true,!(((Var*)$2)->value));
                    else
                    {                    
                        $$=new Var();
                        ((Var*)$2)->load("t1");
                        //emit(((Var*)$$)->getname(0)+" = ! "+((Var*)$2)->getname(1));
                        emit("seqz\tt0, t1");
                        ((Var*)$$)->store("t0");
                    }
                }              
              ;
FuncRParams   : FuncRParams ',' Exp
              {
                  $$=$1;
                  ((vector<Var*>*)$$)->push_back((Var*)$3);
              }
              | Exp
              {
                  $$=new vector<Var*>;
                  ((vector<Var*>*)$$)->push_back((Var*)$1);
              }
              ;
MulExp        : UnaryExp {$$=$1;} 
              | MulExp '*' UnaryExp
                {
                    if(((Var*)$1)->is_const&&((Var*)$3)->is_const)
                        $$=new Var(true,((Var*)$1)->value*((Var*)$3)->value);
                    else
                    {
                        $$=new Var();
                        ((Var*)$1)->load("t1");
                        ((Var*)$3)->load("t2");
                        //emit(((Var*)$$)->getname(0)+" = "+((Var*)$1)->getname(1)+" * "+((Var*)$3)->getname(2));
                        emit("mul\tt0, t1, t2");
                        ((Var*)$$)->store("t0");
                    }
                }
              | MulExp '/' UnaryExp
                {
                    if(((Var*)$1)->is_const&&((Var*)$3)->is_const)
                        $$=new Var(true,((Var*)$1)->value/((Var*)$3)->value);
                    else
                    {
                        $$=new Var();
                        ((Var*)$1)->load("t1");
                        ((Var*)$3)->load("t2");
                        //emit(((Var*)$$)->getname(0)+" = "+((Var*)$1)->getname(1)+" / "+((Var*)$3)->getname(2));
                        emit("div\tt0, t1, t2");
                        ((Var*)$$)->store("t0");
                    }
                }         
              | MulExp '%' UnaryExp
                {
                    if(((Var*)$1)->is_const&&((Var*)$3)->is_const)
                        $$=new Var(true,((Var*)$1)->value%((Var*)$3)->value);
                    else
                    {
                        $$=new Var();
                        ((Var*)$1)->load("t1");
                        ((Var*)$3)->load("t2");
                        //emit(((Var*)$$)->getname(0)+" = "+((Var*)$1)->getname(1)+" % "+((Var*)$3)->getname(2));
                        emit("rem\tt0, t1, t2");
                        ((Var*)$$)->store("t0");
                    }
                }
              ;
AddExp        : MulExp {$$=$1;}
              | AddExp '+' MulExp 
                {
                    if(((Var*)$1)->is_const&&((Var*)$3)->is_const)
                        $$=new Var(true,((Var*)$1)->value+((Var*)$3)->value);
                    else
                    {
                        $$=new Var();
                        ((Var*)$1)->load("t1");
                        if(((Var*)$3)->is_const&&InRange(((Var*)$3)->value,12))
                            emit("addi\tt0, t1, "+to_string(((Var*)$3)->value));
                        else
                        {
                            ((Var*)$3)->load("t2");
                            //emit(((Var*)$$)->getname(0)+" = "+((Var*)$1)->getname(1)+" + "+((Var*)$3)->getname(2));
                            emit("add\tt0, t1, t2");
                        }
                        ((Var*)$$)->store("t0");
                    }
                }
              | AddExp '-' MulExp
                {
                    if(((Var*)$1)->is_const&&((Var*)$3)->is_const)
                        $$=new Var(true,((Var*)$1)->value-((Var*)$3)->value);
                    else
                    {
                        $$=new Var();
                        ((Var*)$1)->load("t1");
                        if(((Var*)$3)->is_const&&InRange(-(((Var*)$3)->value),12))
                            emit("addi\tt0, t1, "+to_string(-(((Var*)$3)->value)));
                        else
                        {                        
                            ((Var*)$3)->load("t2");
                            //emit(((Var*)$$)->getname(0)+" = "+((Var*)$1)->getname(1)+" - "+((Var*)$3)->getname(2));
                            emit("sub\tt0, t1, t2");
                        }
                        ((Var*)$$)->store("t0");
                    }
                }
              ;
RelExp        : AddExp {$$=$1;}
              | RelExp '<' AddExp
                {
                    $$=new Var();
                    ((Var*)$1)->load("t1");
                    if(((Var*)$3)->is_const&&InRange(((Var*)$3)->value,12))
                        emit("slti\tt0, t1, "+to_string(((Var*)$3)->value));
                    else
                    {
                        ((Var*)$3)->load("t2");
                        //emit(((Var*)$$)->getname(0)+" = "+((Var*)$1)->getname(1)+" < "+((Var*)$3)->getname(2));
                        emit("slt\tt0, t1, t2");
                    }
                    ((Var*)$$)->store("t0");
                }
              | RelExp '>' AddExp
                {
                    $$=new Var();
                    ((Var*)$1)->load("t1");
                    ((Var*)$3)->load("t2");
                    //emit(((Var*)$$)->getname(0)+" = "+((Var*)$1)->getname(1)+" > "+((Var*)$3)->getname(2));
                    emit("sgt\tt0, t1, t2");
                    ((Var*)$$)->store("t0");
                }
              | RelExp LE AddExp
                {
                    $$=new Var();
                    ((Var*)$1)->load("t1");
                    ((Var*)$3)->load("t2");
                    //emit(((Var*)$$)->getname(0)+" = "+((Var*)$1)->getname(1)+" <= "+((Var*)$3)->getname(2));
                    emit("sgt\tt0, t1, t2");
                    emit("seqz\tt0, t0");
                    ((Var*)$$)->store("t0");
                }
              | RelExp GE AddExp
                {
                    $$=new Var();
                    ((Var*)$1)->load("t1");
                    ((Var*)$3)->load("t2");
                    //emit(((Var*)$$)->getname(0)+" = "+((Var*)$1)->getname(1)+" >= "+((Var*)$3)->getname(2));
                    emit("slt\tt0, t1, t2");
                    emit("seqz\tt0, t0");
                    ((Var*)$$)->store("t0");
                }
              ;
EqExp         : RelExp {$$=$1;}
              | EqExp EQ RelExp
                {
                    $$=new Var();
                    ((Var*)$1)->load("t1");
                    ((Var*)$3)->load("t2");
                    //emit(((Var*)$$)->getname(0)+" = "+((Var*)$1)->getname(1)+" == "+((Var*)$3)->getname(2));
                    emit("xor\tt0, t1, t2");
                    emit("seqz\tt0, t0");
                    ((Var*)$$)->store("t0");
                }
              | EqExp NE RelExp
                {
                    $$=new Var();
                    ((Var*)$1)->load("t1");
                    ((Var*)$3)->load("t2");
                    //emit(((Var*)$$)->getname(0)+" = "+((Var*)$1)->getname(1)+" != "+((Var*)$3)->getname(2));
                    emit("xor\tt0, t1, t2");
                    emit("snez\tt0, t0");
                    ((Var*)$$)->store("t0");
                }
              ;
LAndExp       : EqExp 
                {
                    int FalseLabel=((JumpAddr*)$-1)->FalseLabel;
                    ((Var*)$1)->load("t0");
                    //emit("if "+((Var*)$1)->getname(0)+" == x0 goto l"+to_string(FalseLabel));     
                    emit("beq\tt0, x0, .l"+to_string(FalseLabel));               
                }
              | LAndExp AND
              {
                  int TrueLabel=((JumpAddr*)$-1)->TrueLabel;
                  int FalseLabel=((JumpAddr*)$-1)->FalseLabel;
                  $2=new JumpAddr(TrueLabel,FalseLabel);
              } 
               EqExp
                {
                    int FalseLabel=((JumpAddr*)$-1)->FalseLabel;
                    ((Var*)$4)->load("t0");
                    //emit("if "+((Var*)$4)->getname(0)+" == x0 goto l"+to_string(FalseLabel));
                    emit("beq\tt0, x0, .l"+to_string(FalseLabel));               
                }
              ;
LOrExp        : LAndExp 
              {
                  int TrueLabel=((JumpAddr*)$-1)->TrueLabel;
                  emit("j\t.l"+to_string(TrueLabel));

                  emitLabel(((JumpAddr*)$-1)->FalseLabel);
              }
              | LOrExp OR
              {
                  int TrueLabel=((JumpAddr*)$-1)->TrueLabel;
                  int FalseLabel=NewLabel();
                  $2=new JumpAddr(TrueLabel,FalseLabel);
              } 
              LAndExp 
              {
                  int TrueLabel=((JumpAddr*)$2)->TrueLabel;
                  emit("j\t.l"+to_string(TrueLabel));

                  emitLabel(((JumpAddr*)$2)->FalseLabel);
              }
              ;
ConstExp      : AddExp
                {
                    assert(((Var*)$1)->is_const);
                    $$=$1;
                }
              ;

%%
void output(const string&s,bool tab=1)
{
    if(tab==0)
        cout<<s<<endl;
    else
        cout<<'\t'<<s<<endl;
}
bool is_fun_header(const string & s)
{
    return s.substr(0,2)=="f_";
}
bool is_fun_end(const string & s)
{
    return s.substr(0,3)=="end";
}
bool is_var_def(const string & s)
{
    return s.substr(0,5)==".comm";
}
bool is_label(const string&s)
{
    return s.substr(0,2)==".l";
}
void to_eeyore(const vector<string>&instructions)
{
    vector<string>global_init;

    //definitions of global variables
    bool is_global=true;
    for(auto&i:instructions)
    {
        if(is_fun_header(i))
            is_global=false;
        else if(is_fun_end(i))
            is_global=true;
        else if(is_global&&is_var_def(i))
            output(i);
        else if(is_global&&!is_var_def(i))
            global_init.push_back(i);
    }

    //definitions of functions
    is_global=true;
    for(auto i=instructions.begin(),j=instructions.begin();i!=instructions.end();i++)
        if(is_fun_header(*i))
        {
            for(j=i+1;!is_fun_end(*j);j++);
            
            //function header
            string func_name=i->substr(2,i->find(' ')-2);
            int STK=parser.func_table[func_name]->STK();
            output(".text");
            output(".align\t2");
            output(".global\t"+func_name);
            output(".type\t"+func_name+", @function");
            output(func_name+":",0);

            if(InRange(-STK,12))
                output("addi\tsp, sp, "+to_string(-STK));
            else
            {
                output("li\ts0, "+to_string(-STK));
                output("add\tsp, sp, s0");
            }

            if(InRange(STK-4,12))
                output("sw\tra, "+to_string(STK-4)+"(sp)");
            else
            {
                output("li\ts0, "+to_string(STK-4));
                output("add\ts0, s0, sp");
                output("sw\tra, 0(s0)");
            }

            //special check for "main"
            if(i->substr(2,5)=="main ")//don't forget the following space
                for(auto k:global_init)
                    output(k);

            //other local things
            for(auto k=i+1;k!=j;k++)
                if((*k)=="return")
                {
                    if(InRange(STK-4,12))
                        output("lw\tra, "+to_string(STK-4)+"(sp)");
                    else
                    {                    
                        output("li\ts0, "+to_string(STK-4));
                        output("add\ts0, s0, sp");
                        output("lw\tra, 0(s0)");
                    }
                    
                    if(InRange(STK,12))
                        output("addi\tsp, sp, "+to_string(STK));
                    else
                    {                    
                        output("li\ts0, "+to_string(STK));
                        output("add\tsp, sp, s0");
                    }

                    output("ret");
                }
                else if(is_label(*k))
                    output(*k,0);
                else
                    output(*k);

            //function end
            output(".size\t"+func_name+", .-"+func_name);

            i=j;
        }
}
int main(int argc,char**argv)
{
        if((yyin=fopen(argv[2],"r"))==NULL)
            exit(1);

        if(freopen(argv[4],"w",stdout)==NULL)
            exit(1);

    parser.PutFunc("getint",new Function(0,INT));
    parser.PutFunc("getch",new Function(0,INT));
    parser.PutFunc("getarray",new Function(1,INT));
    parser.PutFunc("putint",new Function(1,VOID));
    parser.PutFunc("putch",new Function(1,VOID));
    parser.PutFunc("putarray",new Function(2,VOID));
    yyparse();

    to_eeyore(pre_eeyore);

    fclose(yyin);
}
