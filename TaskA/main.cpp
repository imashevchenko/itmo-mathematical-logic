#include <iostream>
#include <string>
#include <queue>

using namespace std;

enum type {
    Variable,
    Implication,
    Disjunction,
    Conjunction,
    Denial,
    LBracket,
    RBracket
};

struct lexeme{
    type t;
    string str;
    lexeme(type T, string s): t(T), str(s){}
};

struct node{
    type t;
    string str;
    node* left;
    node* right;
    node(type T, string s): t(T), str(s){};

    string to_string(){
        if (t == Denial)
            return "(!"+left->to_string()+")";
        if (t==Variable)
            return str;
        return "("+str+","+left->to_string()+","+right->to_string()+")";
    };
};

queue<lexeme> lexeme_reader(string str){
    queue<lexeme> lexemes;
    for (int i = 0; i < str.size(); i++){
        string buffer="";
        if (isupper(str[i])){
            for(int j=i;j<str.size();j++){
                if(isupper(str[j]) ||
                   isdigit(str[j]) || (str[j] == '\''))
                    buffer += str[j];
                else{
                    i=j-1;
                    break;
                }
            }
            lexemes.push(lexeme(Variable,buffer));
            continue;
        }
        if (str[i]=='-'){
            lexemes.push(lexeme(Implication,"->"));
            i++;
            continue;
        }
        if (str[i]=='|'){
            lexemes.push(lexeme(Disjunction,"|"));
            continue;
        }
        if (str[i]=='&'){
            lexemes.push(lexeme(Conjunction,"&"));
            continue;
        }
        if (str[i]=='!'){
            lexemes.push(lexeme(Denial,"!"));
            continue;
        }
        if (str[i]=='('){
            lexemes.push(lexeme(LBracket,"("));
            continue;
        }
        if (str[i]==')'){
            lexemes.push(lexeme(RBracket,")"));
            continue;
        }
    }
    return lexemes;
}

node* expression(queue<lexeme> &lexemes);

node* denial(queue<lexeme> &lexemes){
    lexeme lexeme=lexemes.front();
    lexemes.pop();
    if(lexeme.t==Denial){
        node* Node=new node(Denial, "!");
        Node->left=denial(lexemes);
        return Node;
    }
    if (lexeme.t==Variable)
        return new node(Variable,lexeme.str);
    if (lexeme.t==LBracket){
        node* exp=expression(lexemes);
        lexemes.pop();
        return exp;
    }
    return nullptr;
}

node* _conjunction(queue<lexeme> &lexemes){
    node* left=denial(lexemes);
    while(!lexemes.empty()){
        if(lexemes.front().str!="&")
            return left;
        lexemes.pop();
        node* Node=new node(Conjunction,"&");
        Node->left=left;
        Node->right=denial(lexemes);
        left=Node;
    }
    return left;
}

node* _disjunction(queue<lexeme> &lexemes){
    node* left=_conjunction(lexemes);
    while(!lexemes.empty()){
        if(lexemes.front().str!="|")
            return left;
        lexemes.pop();
        node* Node=new node(Disjunction,"|");
        Node->left=left;
        Node->right=_conjunction(lexemes);
        left=Node;
    }
    return left;
}

node* expression(queue<lexeme> &lexemes){
    node* left=_disjunction(lexemes);
    if (lexemes.empty())
        return left;
    if(lexemes.front().str!="->")
        return left;
    lexemes.pop();
    node* Node=new node(Implication,"->");
    Node->left=left;
    Node->right=expression(lexemes);
    return Node;
}

int main(){
    string s;
    getline(cin,s);
    queue<lexeme> lexemes=lexeme_reader(s);
    cout << expression(lexemes)->to_string();
};