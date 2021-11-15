#include <iostream>
#include <list>
#include <string>
#include <utility>
#include <vector>
#include <deque>
#include <unordered_map>

using namespace std;

enum type {
    Variable,
    Implication,
    Disjunction,
    Conjunction,
    Denial,
    OpenBracket,
    CloseBracket
};

class lexeme {
public:
    type Type;
    string str;

    lexeme(type t, string str) : Type(t), str(move(str)) {};
};

class node {
public:
    type t;
    string str;
    node *LeftSon;
    node *RightSon;

    node(string s, type Type) : t(Type), str(move(s)) {};

    node(string s, type Type, node *Leftson, node *Rightson) : t(Type), str(move(s)), LeftSon(Leftson),
                                                               RightSon(Rightson) {};

    string to_answer_string() const {
        string s;
        if (t == Variable)
            s = this->str;
        else if (t == Denial)
            s = "!" + LeftSon->to_string();
        else s = "(" + LeftSon->to_string() + " " + str + " " + RightSon->to_string() + ")";
        return s;
    }

    string to_string() {
        string s;
        if (t == Variable)
            s = this->str;
        else if (this->str == "!")
            s = "!" + LeftSon->to_string();
        else s = "(" + LeftSon->to_string() + str + RightSon->to_string() + ")";
        return s;
    }

    bool not_equals(node other) {
        if (this->t != other.t)
            return true;
        return !(this->to_string() == other.to_string());
    }
};

enum ProveStringType {
    Context,
    Axiom,
    ModusPonens,
    Redundant
};

class ProveString {
public:
    ProveStringType type;
    node tree;
    int axiom;
    int mp1, mp2;
    int context;
    bool is_used = false;

    ProveString(ProveStringType Type, node tree) : tree(tree), type(Type) {}
};

deque<lexeme> LexemeReader(string str) {
    deque<lexeme> lexemes;
    for (int i = 0; i < str.size(); i++) {
        string buffer;
        buffer = "";
        if (isupper(str[i])) {
            for (int j = i; j < str.size(); j++) {
                if (isupper(str[j]) ||
                    isdigit(str[j]) || (str[j] == '\''))
                    buffer += str[j];
                else {
                    i = j - 1;
                    break;
                }
            }
            lexemes.emplace_back(Variable, buffer);
            continue;
        }
        if (str[i] == '-') {
            lexemes.emplace_back(Implication, "->");
            i++;
            continue;
        }
        if (str[i] == '|') {
            lexemes.emplace_back(Disjunction, "|");
            continue;
        }
        if (str[i] == '&') {
            lexemes.emplace_back(Conjunction, "&");
            continue;
        }
        if (str[i] == '!') {
            lexemes.emplace_back(Denial, "!");
            continue;
        }
        if (str[i] == '(') {
            lexemes.emplace_back(OpenBracket, "(");
            continue;
        }
        if (str[i] == ')') {
            lexemes.emplace_back(CloseBracket, ")");
            continue;
        }
    }
    return lexemes;
}

node *_expression(deque<lexeme> &lexemes);

node *_denial(deque<lexeme> &lexemes) {
    lexeme lex = lexemes.front();
    lexemes.pop_front();
    switch (lex.Type) {
        case Denial: {
            node *den = new node("!", Denial, _denial(lexemes), nullptr);
            return den;
        }
        case Variable:
            return new node(lex.str, Variable);
        case OpenBracket: {
            node *expr = _expression(lexemes);
            lexemes.pop_front();
            return expr;
        }
    }
    return nullptr;
}

node *_conjunction(deque<lexeme> &lexemes) {
    node *left = _denial(lexemes); // запоминаем левую часть до знака
    while (lexemes.size() > 0) { // проверяем, не съела ли все предыдущая функция
        if (lexemes.front().Type !=Conjunction)// если это не коньюнкция, то этим должна заниматься функция старшего порядка
            return left; // возвращаем ей
        else lexemes.pop_front(); // достаем лексему "&"
        node *result = new node("&", Conjunction, left,_denial(lexemes)); // создаем новый узел в дереве разбора, отдельно разбираем правую часть
        left = result;
    }
    return left; // переходим на старший уровень
}

node *_disjunction(deque<lexeme> &lexemes) {
    node *left = _conjunction(lexemes);
    while (lexemes.size() > 0) {
        if (lexemes.front().Type != Disjunction)
            return left;
        else lexemes.pop_front();
        node *result = new node("|", Disjunction, left, _conjunction(lexemes));
        left = result;
    }
    return left;
}

node *_expression(deque<lexeme> &lexemes) {
    node *left = _disjunction(lexemes);
    if (lexemes.size() == 0)
        return left;
    if (lexemes.front().Type != Implication)
        return left;
    else lexemes.pop_front();
    return new node("->", Implication, left, _expression(lexemes));;
}

bool axiom1(const node &exp) {
    if (exp.RightSon->t != Implication || exp.LeftSon->not_equals(*exp.RightSon->RightSon))
        return false;
    return true;
}

//(α → β) → (α → β → γ) → (α → γ)
bool axiom2(const node &exp) {
    if (exp.LeftSon->t != Implication || exp.RightSon->t != Implication) {
        return false;
    }
    if (exp.RightSon->LeftSon->t != Implication || exp.RightSon->RightSon->t != Implication) {
        return false;
    }
    if (exp.RightSon->LeftSon->RightSon->t != Implication) {
        return false;
    }
    if (exp.LeftSon->LeftSon->not_equals(*exp.RightSon->LeftSon->LeftSon) ||
        exp.LeftSon->LeftSon->not_equals(*exp.RightSon->RightSon->LeftSon)) {
        return false;
    }
    if (exp.LeftSon->RightSon->not_equals(*exp.RightSon->LeftSon->RightSon->LeftSon)) {
        return false;
    }
    if (exp.RightSon->LeftSon->RightSon->RightSon->not_equals(*exp.RightSon->RightSon->RightSon)) {
        return false;
    }
    return true;
}

//α → β → α&β
bool axiom3(const node &exp) {
    if (exp.RightSon->t != Implication) {
        return false;
    }
    if (exp.RightSon->RightSon->t != Conjunction) {
        return false;
    }
    if (exp.LeftSon->not_equals(*exp.RightSon->RightSon->LeftSon) ||
        exp.RightSon->LeftSon->not_equals(*exp.RightSon->RightSon->RightSon)) {
        return false;
    }
    return true;
}

//α&β → α
bool axiom4(const node &exp) {
    if (exp.LeftSon->t != Conjunction) {
        return false;
    }
    if (exp.LeftSon->LeftSon->not_equals(*exp.RightSon)) {
        return false;
    }
    return true;
}

//α&β → β
bool axiom5(const node &exp) {
    if (exp.LeftSon->t != Conjunction || exp.LeftSon->RightSon->not_equals(*exp.RightSon))
        return false;
    return true;
}

// α → α ∨ β
bool axiom6(const node &exp) {
    if (exp.RightSon->t != Disjunction || exp.LeftSon->not_equals(*exp.RightSon->LeftSon))
        return false;
    return true;
}

//β → α ∨ β
bool axiom7(const node &exp) {
    if (exp.RightSon->t != Disjunction || exp.LeftSon->not_equals(*exp.RightSon->RightSon))
        return false;
    return true;
}

//(α → γ) → (β → γ) → (α ∨ β → γ)
bool axiom8(const node &exp) {
    if (exp.LeftSon->t != Implication || exp.RightSon->t != Implication)
        return false;
    if (exp.RightSon->LeftSon->t != Implication || exp.RightSon->RightSon->t != Implication)
        return false;
    if (exp.RightSon->RightSon->LeftSon->t != Disjunction)
        return false;
    if (exp.LeftSon->LeftSon->not_equals(*exp.RightSon->RightSon->LeftSon->LeftSon))
        return false;
    if (exp.LeftSon->RightSon->not_equals(*exp.RightSon->LeftSon->RightSon)
        || exp.LeftSon->RightSon->not_equals(*exp.RightSon->RightSon->RightSon))
        return false;
    if (exp.RightSon->LeftSon->LeftSon->not_equals(*exp.RightSon->RightSon->LeftSon->RightSon))
        return false;
    return true;
}

//(α → β) → (α → ¬β) → ¬α
bool axiom9(const node &exp) {
    if (exp.LeftSon->t != Implication || exp.RightSon->t != Implication)
        return false;
    if (exp.RightSon->LeftSon->t != Implication || exp.RightSon->RightSon->t != Denial)
        return false;
    if (exp.RightSon->LeftSon->RightSon->t != Denial)
        return false;
    if (exp.LeftSon->LeftSon->not_equals(*exp.RightSon->LeftSon->LeftSon)
        || exp.LeftSon->LeftSon->not_equals(*exp.RightSon->RightSon->LeftSon))
        return false;
    if (exp.LeftSon->RightSon->not_equals(*exp.RightSon->LeftSon->RightSon->LeftSon))
        return false;
    return true;
}

//¬¬α → α
bool axiom10(node exp) {
    if (exp.LeftSon->t != Denial || exp.LeftSon->LeftSon->t != Denial)
        return false;
    if (exp.LeftSon->LeftSon->LeftSon->not_equals(*exp.RightSon))
        return false;
    return true;
}

int axiom_checker(const node &exp) {
    if (axiom1(exp))
        return 1;
    if (axiom2(exp))
        return 2;
    if (axiom3(exp))
        return 3;
    if (axiom4(exp))
        return 4;
    if (axiom5(exp))
        return 5;
    if (axiom6(exp))
        return 6;
    if (axiom7(exp))
        return 7;
    if (axiom8(exp))
        return 8;
    if (axiom9(exp))
        return 9;
    if (axiom10(exp))
        return 10;
    return -1;
}

bool incorrect = false;
vector<node> ContextVector;
string expression_to_prove;
vector<ProveString> ProveStrings;
unordered_map<string, list<node>> MapForMP;
unordered_map<string, int> ProvedStrings;

void FirstLineParser(const string &str) {
    deque<lexeme> expression_to_prove_lexemes;
    int index = str.find("|-", 0);
    string contextString = str.substr(0, index);
    string toProveString = str.substr(index + 2);
    expression_to_prove_lexemes = LexemeReader(toProveString);
    expression_to_prove = _expression(expression_to_prove_lexemes)->to_string();
    while (true) {
        index = contextString.find(',', 0);
        deque<lexeme> context_lexemes;
        if (index == -1) {
            if (contextString.size() == 0) {
                break;
            }
            context_lexemes = LexemeReader(contextString);
            ContextVector.push_back(*_expression(context_lexemes));
            break;
        }
        string part = contextString.substr(0, index);
        if (part.empty()) {
            break;
        }
        context_lexemes = LexemeReader(part);
        ContextVector.push_back(*_expression(context_lexemes));
        contextString = contextString.substr(index + 1);
    }
}

int last_use = 0;

void ProveParser() {
    string s;
    getline(cin,s);
    FirstLineParser(s);
    int k = -1;
    int context_counter = 0;
    bool proven_string_is_found = false;
    while (getline(cin,s)) {
        deque<lexeme> lexemes = LexemeReader(s);
        node *exp = _expression(lexemes);
        string expression_to_string = exp->to_string();

        k++;

        if (ProvedStrings.find(expression_to_string) != ProvedStrings.end()) {
            ProveStrings.emplace_back(Redundant, *exp);
            continue;
        }

        bool flag = false;
        if (context_counter < ContextVector.size()) {
            int i = 0;
            for (node context : ContextVector) {
                if (expression_to_string == context.to_string()) {
                    ProveString proveString = ProveString(Context, *exp);
                    proveString.context = i + 1;
                    ProveStrings.push_back(proveString);
                    flag = true;
                    ProvedStrings.insert(pair<string, int>(expression_to_string, k));
                    if (exp->t == Implication) {
                        string buffer = exp->RightSon->to_string();
                        if (MapForMP.find(buffer) == MapForMP.end()) {
                            MapForMP.insert(
                                    pair<string, list<node>>(buffer,
                                                             list<node>()));
                        }
                        MapForMP.at(buffer).push_back(*exp);
                    }
                    break;
                }
                i++;
            }
            if (flag) {
                if (!proven_string_is_found && expression_to_prove == expression_to_string) {
                    proven_string_is_found = true;
                    last_use = k;
                }
                context_counter++;
                continue;
            }
        }


        if (exp->t == Implication) {
            int ax = axiom_checker(*exp);
            if (ax > 0) {
                ProveString proveString = ProveString(Axiom, *exp);
                proveString.axiom = ax;
                ProveStrings.push_back(proveString);
                ProvedStrings.insert(pair<string, int>(expression_to_string, k));
                if (exp->t == Implication) {
                    string B_string = exp->RightSon->to_string();
                    if (MapForMP.find(B_string) == MapForMP.end()) {
                        MapForMP.insert(pair<string, list<node>>(B_string, list<node>()));
                    }
                    MapForMP.at(B_string).push_back(*exp);
                }
                if (!proven_string_is_found && expression_to_prove == expression_to_string) {
                    proven_string_is_found = true;
                    last_use = k;
                }
                continue;
            }
        }

        flag = false;
        if (MapForMP.find(expression_to_string) == MapForMP.end()) {
            incorrect = true;
            return;
        } else {
            for (node AB_expression : MapForMP[expression_to_string]) {
                string A_string = AB_expression.LeftSon->to_string();
                if (ProvedStrings.find(A_string) != ProvedStrings.end()) {
                    int A_index = ProvedStrings.at(A_string);
                    ProveString proveString = ProveString(ModusPonens, *exp);
                    proveString.mp1 = ProvedStrings[AB_expression.to_string()];
                    proveString.mp2 = A_index;
                    ProveStrings.push_back(proveString);
                    ProvedStrings.insert(pair<string, int>(expression_to_string, k));
                    flag = true;

                    if (exp->t == Implication) {
                        string buffer = exp->RightSon->to_string();
                        if (MapForMP.find(buffer) == MapForMP.end()) {
                            MapForMP.insert(
                                    pair<string, list<node>>(buffer, list<node>()));
                        }
                        MapForMP.at(buffer).push_back(*exp);
                    }
                    break;
                }
            }
        }
        if (!flag) {
            incorrect = true;
            return;
        }
        if (!proven_string_is_found && expression_to_prove == expression_to_string) {
            last_use = k;
            proven_string_is_found = true;
        }
    }
    if (k == -1) {
        incorrect = true;
    }
}

void mark_if_is_used(int n) {
    if (ProveStrings[n].is_used);
    else {
        ProveStrings[n].is_used = true;
        if (ProveStrings[n].type == ModusPonens) {
            mark_if_is_used(ProveStrings[n].mp1);
            mark_if_is_used(ProveStrings[n].mp2);
        }
    }
}

int main() {
    ProveParser();
    if (incorrect) {
        cout << "Proof is incorrect" << endl;
        return 0;
    }
    if (ProveStrings[ProveStrings.size() - 1].tree.to_string() != expression_to_prove) {
        cout << "Proof is incorrect" << endl;
        return 0;
    }


    mark_if_is_used(last_use);

    int k = 1;
    unordered_map<int, int> change;
    for (int i = 0; i < ProveStrings.size(); i++) {
        if (!ProveStrings[i].is_used) {
            continue;
        }
        change.insert(pair<int, int>(i, k));
        k++;
    }

    if (ContextVector.empty()) {
        cout << "|- ";
        deque<lexeme> expression_to_prove_lexemes = LexemeReader(expression_to_prove);
        cout << _expression(expression_to_prove_lexemes)->to_answer_string() << '\n';
    } else {
        cout << ContextVector[0].to_string();
        for (int i = 1; i < ContextVector.size(); i++) {
            printf(", ");
            cout << ContextVector[i].to_answer_string();
        }
        cout << " |- " << expression_to_prove << '\n';
    }

    for (int i = 0; i < ProveStrings.size(); i++) {
        if (!ProveStrings[i].is_used) {
            continue;
        }
        if (ProveStrings[i].type == Axiom) {
            printf("[%d. Ax. sch. %d] ", change[i], ProveStrings[i].axiom);
            cout << ProveStrings[i].tree.to_answer_string() << endl;
            continue;
        }
        if (ProveStrings[i].type == Context) {
            printf("[%d. Hypothesis %d] ", change[i], ProveStrings[i].context);
            cout << ProveStrings[i].tree.to_answer_string() << endl;
            continue;
        }
        if (ProveStrings[i].type == ModusPonens) {
            printf("[%d. M.P. %d, %d] ", change[i], change[ProveStrings[i].mp1], change[ProveStrings[i].mp2]);
            cout << ProveStrings[i].tree.to_answer_string() << endl;
        }
    }
}