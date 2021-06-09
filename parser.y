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

bool IsPow2(int num)
{
    return num==(num&(-num));
}

int Log2(int num)
{
    assert(IsPow2(num));
    int ans=0;
    for(;num>1;ans++,num>>=1);
    return ans;
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
    bool caller;
    Function(int p,int rv):param_count(p),retval(rv),stack_size(INT_SIZE*MAX_PARAMS),caller(false){}
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
            if(offset->is_const && InRange(offset->value,12))
                emit("sw\t"+reg+", "+to_string(offset->value)+"(t3)");
            else
            {            
                offset->load("t4");
                //emit("t5 = "+array_name->getname(3)+" + "+offset->getname(4));
                emit("add\tt5, t3, t4");
                //emit("t5[0] = "+reg);
                emit("sw\t"+reg+", 0(t5)");
            }
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


class Relation
{
public:    
    Var*src1,*src2;
    string op;
    Relation(Var*s1,Var*s2,string operation)
    {
        assert(s1);
        if(s2==NULL)
        {
            src1=s1;
            src2=NULL;
            op="";
        }
        else if(s1->is_const&&s2->is_const)
        {
            if(operation=="<")
                src1=new Var(true,s1->value < s2->value);
            if(operation==">")
                src1=new Var(true,s1->value > s2->value);
            if(operation=="==")
                src1=new Var(true,s1->value == s2->value);
            if(operation=="!=")
                src1=new Var(true,s1->value != s2->value);
            if(operation=="<=")
                src1=new Var(true,s1->value <= s2->value);
            if(operation==">=")
                src1=new Var(true,s1->value >= s2->value);      

            src2=NULL;
            op="";                                                                          
        }
        else
        {
            src1=s1;
            src2=s2;
            op=operation;
        }
    }

    Var*solve()
    {
        if(src2==NULL)
            return src1;
        
        Var*ans=new Var();
        if(op=="<")
        {
            src1->load("t1");
            src2->load("t0");
            emit("slt\tt0, t1, t0");
            ans->store("t0");
        }
        if(op==">")
        {
            src1->load("t1");
            src2->load("t0");
            emit("sgt\tt0, t1, t0");
            ans->store("t0");
        }        
        if(op=="==")
        {
            src1->load("t1");
            src2->load("t0");
            emit("xor\tt0, t1, t0");
            emit("seqz\tt0, t0");
            ans->store("t0");
        }
        if(op=="!=")
        {
            src1->load("t1");
            src2->load("t0");
            emit("xor\tt0, t1, t0");
            emit("snez\tt0, t0");
            ans->store("t0");
        }
        if(op=="<=")
        {
            src1->load("t0");
            src2->load("t1");
            emit("sgt\tt0, t1, t0");
            ans->store("t0");
        }
        if(op==">=")
        {
            src1->load("t0");
            src2->load("t1");
            emit("slt\tt0, t1, t0");
            ans->store("t0");
        }
        return ans;                                      
    }

    void branch_false(int label)
    {
        if(src2==NULL)
        {
            if(src1->is_const)
            {
                if(src1->value == 0)
                    emit("j\t.l"+to_string(label));
            }
            else
            {
                src1->load("t0");
                emit("beq\tt0, x0, .l"+to_string(label));
            }
        }
        else if(op=="<")
        {
            src1->load("t0");
            src2->load("t1");
            emit("bge\tt0, t1, .l"+to_string(label));
        }
        else if(op==">")
        {
            src1->load("t0");
            src2->load("t1");
            emit("ble\tt0, t1, .l"+to_string(label));
        }
        else if(op=="==")
        {
            src1->load("t0");
            src2->load("t1");
            emit("bne\tt0, t1, .l"+to_string(label));
        }
        else if(op=="!=")
        {
            src1->load("t0");
            src2->load("t1");
            emit("beq\tt0, t1, .l"+to_string(label));
        }
        else if(op=="<=")
        {
            src1->load("t0");
            src2->load("t1");
            emit("bgt\tt0, t1, .l"+to_string(label));
        }
        else if(op==">=")
        {
            src1->load("t0");
            src2->load("t1");
            emit("blt\tt0, t1, .l"+to_string(label));
        }                                        
    }
};
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
                            Var*var_offset=new Var(true,offset);
                            $$=new Var(false,NULL,false,-1,true,(Var*)$$,var_offset);
                        }
                        else
                        {
                            Var*var_offset=new Var();
                            emit("mv\tt0, x0");
                            for(int i=0;i<subscripts.size();i++)
                            {
                                if(subscripts[i]->is_const)
                                {
                                    int mul_ans=subscripts[i]->value*size_of_each_dimension[i];
                                    if(InRange(mul_ans,12))
                                        emit("addi\tt0, t0, "+to_string(mul_ans));
                                    else
                                    {
                                        emit("li\ts0, "+to_string(mul_ans));
                                        emit("add\tt0, t0, s0");
                                    }
                                }
                                else
                                {
                                    subscripts[i]->load("t1");
                                    if(IsPow2(size_of_each_dimension[i]))
                                        emit("slli\tt2, t1, "+to_string(Log2(size_of_each_dimension[i])));
                                    else
                                    {
                                        //emit("t2 = "+to_string(size_of_each_dimension[i]));
                                        emit("li\tt2, "+to_string(size_of_each_dimension[i]));
                                        //emit(mul->getname(0)+" = "
                                        //+subscripts[i]->getname(1)+
                                        //" * t2");
                                        emit("mul\tt2, t1, t2");
                                    }

                                //emit(var_offset->getname(0)+" = "
                                //+var_offset->getname(1)+" + "+mul->getname(2));
                                emit("add\tt0, t0, t2");
                                }
                            }
                            var_offset->store("t0");
                            $$=new Var(false,NULL,false,-1,true,(Var*)$$,var_offset);
                        }
                    }
                }
              ;      
RVal          : IDENT ExpList 
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
                                if(subscripts.size()==size_of_each_dimension.size())
                                {
                                    Var*tmp=new Var();
                                    ((Var*)$$)->load("t1");
                                    if(InRange(offset,12))
                                        emit("lw\tt0, "+to_string(offset)+"(t1)");
                                    else
                                    {
                                        emit("li\tt0, "+to_string(offset));
                                        emit("add\tt0, t0, t1");
                                        emit("lw\tt0, 0(t0)");
                                    }
                                    tmp->store("t0");
                                    $$=tmp;
                                }
                                else
                                {
                                    Var*tmp=new Var();
                                    tmp->load("t1");
                                    if(InRange(offset,12))
                                        emit("addi\tt0, t1, "+to_string(offset));
                                    else
                                    {
                                        emit("li\tt2, "+to_string(offset));
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
                            emit("mv\tt0, x0");
                            for(int i=0;i<subscripts.size();i++)
                            {
                                if(subscripts[i]->is_const)
                                {
                                    int mul_ans=subscripts[i]->value*size_of_each_dimension[i];
                                    if(InRange(mul_ans,12))
                                        emit("addi\tt0, t0, "+to_string(mul_ans));
                                    else
                                    {
                                        emit("li\ts0, "+to_string(mul_ans));
                                        emit("add\tt0, t0, s0");
                                    }
                                }
                                else
                                {
                                    subscripts[i]->load("t1");
                                    if(IsPow2(size_of_each_dimension[i]))
                                        emit("slli\tt2, t1, "+to_string(Log2(size_of_each_dimension[i])));
                                    else
                                    {
                                        //emit("t2 = "+to_string(size_of_each_dimension[i]));
                                        emit("li\tt2, "+to_string(size_of_each_dimension[i]));
                                        //emit(mul->getname(0)+" = "
                                        //+subscripts[i]->getname(1)+
                                        //" * t2");
                                        emit("mul\tt2, t1, t2");
                                    }

                                //emit(var_offset->getname(0)+" = "
                                //+var_offset->getname(1)+" + "+mul->getname(2));
                                emit("add\tt0, t0, t2");
                                }
                            }
                            if(subscripts.size()==size_of_each_dimension.size())
                            {
                                Var*tmp=new Var();
                                ((Var*)$$)->load("t1");
                                emit("add\tt0, t1, t0");
                                emit("lw\tt0, 0(t0)");
                                tmp->store("t0");
                                $$=tmp;
                            }
                            else
                            {
                                Var*tmp=new Var();
                                ((Var*)$$)->load("t1");
                                //emit(tmp->getname(0)+" = "+((Var*)$$)->getname(1)
                                //+" + "+var_offset->getname(2));
                                emit("add\tt0, t1, t0");
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
              | RVal {$$=$1;}
              | INT_CONST { $$=new Var(true,*(int*)$1); }
              ;
UnaryExp      : PrimaryExp {$$=$1;}
              | IDENT '(' FuncRParams ')'
              {
                  parser.cur_func->caller=true;

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
                  parser.cur_func->caller=true;

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
                        ((Var*)$2)->load("t0");
                        //emit(((Var*)$$)->getname(0)+" = - "+((Var*)$2)->getname(1));
                        emit("neg\tt0, t0");
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
                        ((Var*)$2)->load("t0");
                        //emit(((Var*)$$)->getname(0)+" = ! "+((Var*)$2)->getname(1));
                        emit("seqz\tt0, t0");
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
                        ((Var*)$3)->load("t0");
                        //emit(((Var*)$$)->getname(0)+" = "+((Var*)$1)->getname(1)+" * "+((Var*)$3)->getname(2));
                        emit("mul\tt0, t1, t0");
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
                        if(((Var*)$3)->is_const&&((Var*)$3)->value==2)
                        {
                            emit("srli\tt0, t1, 31");
                            emit("add\tt1, t1, t0");
                            emit("srai\tt0, t1, 1");
                        }
                        else
                        {
                            ((Var*)$3)->load("t0");
                            //emit(((Var*)$$)->getname(0)+" = "+((Var*)$1)->getname(1)+" / "+((Var*)$3)->getname(2));
                            emit("div\tt0, t1, t0");
                        }
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
                        ((Var*)$3)->load("t0");
                        //emit(((Var*)$$)->getname(0)+" = "+((Var*)$1)->getname(1)+" % "+((Var*)$3)->getname(2));
                        emit("rem\tt0, t1, t0");
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
                            ((Var*)$3)->load("t0");
                            //emit(((Var*)$$)->getname(0)+" = "+((Var*)$1)->getname(1)+" + "+((Var*)$3)->getname(2));
                            emit("add\tt0, t1, t0");
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
                            ((Var*)$3)->load("t0");
                            //emit(((Var*)$$)->getname(0)+" = "+((Var*)$1)->getname(1)+" - "+((Var*)$3)->getname(2));
                            emit("sub\tt0, t1, t0");
                        }
                        ((Var*)$$)->store("t0");
                    }
                }
              ;
RelExp        : AddExp {$$=new Relation((Var*)$1,NULL,"");}
              | RelExp '<' AddExp {$$=new Relation(((Relation*)$1)->solve(),(Var*)$3,"<");}
              | RelExp '>' AddExp {$$=new Relation(((Relation*)$1)->solve(),(Var*)$3,">");}
              | RelExp LE AddExp {$$=new Relation(((Relation*)$1)->solve(),(Var*)$3,"<=");}
              | RelExp GE AddExp {$$=new Relation(((Relation*)$1)->solve(),(Var*)$3,">=");}
              ;
EqExp         : RelExp {$$=$1;}
              | EqExp EQ RelExp {$$=new Relation(((Relation*)$1)->solve(),((Relation*)$3)->solve(),"==");}
              | EqExp NE RelExp {$$=new Relation(((Relation*)$1)->solve(),((Relation*)$3)->solve(),"!=");}
              ;
LAndExp       : EqExp 
                {
                    int FalseLabel=((JumpAddr*)$-1)->FalseLabel;
                    ((Relation*)$1)->branch_false(FalseLabel);
                }
              | LAndExp AND EqExp
                {
                    int FalseLabel=((JumpAddr*)$-1)->FalseLabel;
                    ((Relation*)$3)->branch_false(FalseLabel);  
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
                  int FalseLabel=NewLabel();
                  $2=new JumpAddr(0,FalseLabel);
              } 
              LAndExp 
              {
                  int TrueLabel=((JumpAddr*)$-1)->TrueLabel;
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
vector<string>riscv;
void output(const string&s,bool tab=1)
{
    /*if(tab==0)
        cout<<s<<endl;
    else
        cout<<'\t'<<s<<endl;*/
    if(tab==0)
        riscv.push_back(s);
    else
        riscv.push_back("\t"+s); 
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
            
            if(parser.func_table[func_name]->caller)
            {
                if(InRange(STK-4,12))
                    output("sw\tra, "+to_string(STK-4)+"(sp)");
                else
                {
                    output("li\ts0, "+to_string(STK-4));
                    output("add\ts0, s0, sp");
                    output("sw\tra, 0(s0)");
                }
            }

            //special check for "main"
            if(i->substr(2,5)=="main ")//don't forget the following space
                for(auto k:global_init)
                    output(k);

            //other local things
            for(auto k=i+1;k!=j;k++)
                if((*k)=="return")
                {
                    if(*(k-1)=="return")
                        continue;
                    
                    if(parser.func_table[func_name]->caller)
                    {
                        if(InRange(STK-4,12))
                            output("lw\tra, "+to_string(STK-4)+"(sp)");
                        else
                        {                    
                            output("li\ts0, "+to_string(STK-4));
                            output("add\ts0, s0, sp");
                            output("lw\tra, 0(s0)");
                        }
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
                else if(k->find("lw")!=string::npos && (k-1)->find("sw")!=string::npos)
                {
                    string tmp=*k;
                    tmp[k->find("lw")]='s';
                    if(tmp!=*(k-1))
                    {
                        int reg_begin,reg_end;

                        reg_begin=k->find("lw\t")+3;
                        reg_end=k->find(",");
                        string reg_lw=k->substr(reg_begin,reg_end-reg_begin);
                        string mem_lw=k->substr(reg_end+2,k->length()-(reg_end+2));

                        reg_begin=(k-1)->find("sw\t")+3;
                        reg_end=(k-1)->find(",");
                        string reg_sw=(k-1)->substr(reg_begin,reg_end-reg_begin);
                        string mem_sw=(k-1)->substr(reg_end+2,(k-1)->length()-(reg_end+2));

                        if(mem_lw==mem_sw && reg_lw!=reg_sw)
                            output("mv\t"+reg_lw+", "+reg_sw);
                        else if(mem_lw!=mem_sw)
                            output(*k);
                    }
                }
                else
                    output(*k);

            //function end
            output(".size\t"+func_name+", .-"+func_name);

            i=j;
        }
}
bool is_beq(string s)
{
    if(s.length()==0)
        return false;
    while(s[0]=='\t')
        s=s.substr(1,s.length()-1);
    return s.substr(0,4)=="beq\t"
         ||s.substr(0,4)=="bne\t"
         ||s.substr(0,4)=="blt\t"
         ||s.substr(0,4)=="bgt\t"
         ||s.substr(0,4)=="ble\t"
         ||s.substr(0,4)=="bge\t";
}
bool is_j(string s)
{
    if(s.length()==0)
        return false;
    while(s[0]=='\t')
        s=s.substr(1,s.length()-1);
    return s.substr(0,2)=="j\t";
}
string get_label(string s)
{
    int pos=s.rfind(".");
    return s.substr(pos,s.length()-pos);
}
bool kill_redundant_store_one_iteration(vector<string>&instructions)
{
    bool changed=false;

    for(auto k=instructions.begin()+1;k!=instructions.end();k++)
    {
        auto instr_last=k-1;
        while(instr_last>instructions.begin()&&*instr_last=="")
            instr_last--;

        if(k->find("lw")==string::npos||instr_last->find("sw")==string::npos)
            continue;
        string tmp=*k;
        tmp[k->find("lw")]='s';
        if(tmp==*(instr_last))
        {
            *k="";
            changed=true;
        }
        else
        {
            int reg_begin,reg_end;

            reg_begin=k->find("lw\t")+3;
            reg_end=k->find(",");
            string reg_lw=k->substr(reg_begin,reg_end-reg_begin);
            string mem_lw=k->substr(reg_end+2,k->length()-(reg_end+2));

            reg_begin=instr_last->find("sw\t")+3;
            reg_end=instr_last->find(",");
            string reg_sw=instr_last->substr(reg_begin,reg_end-reg_begin);
            string mem_sw=instr_last->substr(reg_end+2,instr_last->length()-(reg_end+2));

            if(mem_lw==mem_sw && reg_lw!=reg_sw)
            {
                *k="mv\t"+reg_lw+", "+reg_sw;
                changed=true;
            }
        }
    }


    auto fun_begin=instructions.begin(),fun_end=instructions.begin();
    while(fun_begin!=instructions.end())
    {
        while(*fun_begin!="\t.text")
            fun_begin++;
        fun_begin+=5;
        fun_end=fun_begin+1;
        while(fun_end->substr(0,6)!="\t.size")
            fun_end++;
        
        for(auto instr=fun_begin;instr!=fun_end;instr++)
            if(instr->find("sw")!=string::npos && instr->find("(sp)")!=string::npos)
            {
                int pos=instr->rfind(",");
                pos+=2;
                string mem_pos=instr->substr(pos,instr->length()-pos);

                bool found=false;
                for(auto iter=fun_begin;iter!=fun_end;iter++)
                    if(iter->find(mem_pos)!=string::npos&&iter!=instr)
                    {
                        found=true;
                        break;
                    }
                
                if(!found)
                {
                    *instr="";
                    changed=true;
                }
                else
                {
                    found=false;

                    for(auto iter=instr+1;iter!=fun_end;iter++)
                        if(is_beq(*iter)||is_j(*iter))
                        {
                            string label=get_label(*iter);
                            for(auto tmp=fun_begin;tmp!=instr;tmp++)
                            if(*tmp==label+":")
                            {
                                found=true;
                                break;
                            }
                        }
                        else if(iter->find(mem_pos)!=string::npos)
                        {
                            found=true;
                            break;
                        }
                    if(!found)
                    {
                        *instr="";
                        changed=true;
                    }
                }
            }
        
        fun_begin=fun_end+1;
    }
    return changed;
}
bool kill_redundant_store(vector<string>&instructions)
{
    int epoch=0;
    while(kill_redundant_store_one_iteration(instructions))
        epoch++;
    return epoch;
}

bool kill_redundant_label_and_goto_one_iteration(vector<string>&instructions)
{
    bool changed=false;

    for(auto&instr:instructions)// remove unused labels
        if(instr.substr(0,2)==".l")
        {
            string label=instr.substr(0,instr.length()-1);
            int cnt=0;
            for(const auto&i:instructions)
                if(i.find(label)!=string::npos)
                    cnt++;
            if(cnt==1)
            {
                instr="";
                changed=true;
            }
        }
    
    for(auto instr=instructions.begin()+1;instr!=instructions.end();instr++)//remove unused goto
    {
        auto instr_last=instr-1;
        while(instr_last>instructions.begin()&&*instr_last=="")
            instr_last--;
        if(is_j(*instr) && is_j(*(instr_last)))
        {
            *instr="";
            changed=true;
        }
    }

    for(auto instr=instructions.begin();instr!=instructions.end()-1;instr++)//remove unused goto
    {
        auto instr_next=instr+1;
        while(instr_next<instructions.end()-1 && *instr_next=="")
            instr_next++;
        if(is_j(*instr))
            while(instr_next->substr(0,2)==".l"||*instr_next=="")
                if(*(instr_next)==get_label(*instr)+":")
                {
                    *instr="";
                    changed=true;
                    break;
                }
                else
                    instr_next++;
    }

    return changed;
}
bool kill_redundant_label_and_goto(vector<string>&instructions)
{
    int epoch=0;
    while(kill_redundant_label_and_goto_one_iteration(instructions))
        epoch++;
    return epoch;
}

void kill_redundant(vector<string>&instructions)
{
    while(kill_redundant_label_and_goto(instructions)
    +kill_redundant_store(instructions));
}

int find_label(const vector<string>&instructions,string label)
{
    for(int i=0;i<instructions.size();i++)
        if(instructions[i]==label+":")
            return i;
    assert(0);
}
void kill_cascade_goto(vector<string>&instructions)
{
    for(int j=0;j<instructions.size();j++)
    {
        string & i=instructions[j];
        if(is_beq(i)||is_j(i))
        {
            string label=get_label(i);
            string target_instr=instructions[find_label(instructions,label)+1];
            if(is_j(target_instr))
            {
                string target_label=get_label(target_instr);
                int pos=i.rfind(".");
                i=i.substr(0,pos)+target_label;
                j--;
            }
        }
    }
}
void output_peephole(const vector<string>instructions)
{
    for(const auto&i:instructions)
        if(i!="")
            cout<<i<<endl;
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

    kill_redundant(riscv);

    kill_cascade_goto(riscv);

    kill_redundant(riscv);

    output_peephole(riscv);


    fclose(yyin);
}
