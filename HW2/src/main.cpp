#include <iostream>
#include <string>
#include <map>
#include <vector>
#include <cstdio>

#define N 5000

long long prime[N * N];

bool is_variable(const std::string& s) {
    if (s.length() > 0 && s[0] >= 'A' && s[0] <= 'Z') {
        return true;
    }
    return false;
}

struct Node {
    long long hash;
    int vertCnt;
    int ptrCnt;
    std::string s;
    Node * l;
    Node * r;
    Node() : vertCnt(0), ptrCnt(0), l(NULL), r(NULL) {}
    Node(std::string s, Node * l, Node * r) : s(s), l(l), r(r) {
        vertCnt = 1;
        ptrCnt = 0;
        int lCnt = 0, rCnt = 0;
        if (l) {
            lCnt  = l->vertCnt;
            vertCnt += lCnt;
            l->ptrCnt++;
        }
        if (l) {
            rCnt  = r->vertCnt;
            vertCnt += rCnt;
        }
        hash = 0;
        if (l) hash += l->hash;
        hash *= prime[1];
        hash += s[0];
        if (r) {
            hash *= prime[rCnt];
            hash += r->hash;
            r->ptrCnt++;
        }

    }
    ~Node() {
        if (l && l->ptrCnt == 0) delete l;
        if (r && r->ptrCnt == 0) delete r;
    }
    std::string getAsString(bool isMain = true) {
        std::string result = "";
        if (!is_variable(s) && !isMain) {
            result += "(";
        }
        if (l) {
            result += l->getAsString(false);
        }
        result += s;
        if (r) {
            result += r->getAsString(false);
        }
        if (!is_variable(s) && !isMain) {
            result += ")";
        }
        return result;
    }
};

std::string get_string_without_spaces(const std::string & s) {
    // remove_if(s.begin(), s.end(), isspace);
    std::string res;
    for (unsigned int i = 0; i < s.length(); i++) {
        char c = s[i];
        if (!isspace(c)) res += c;
    }
    return res;
}

Node * formulas[N*N], * axioms[10];

bool check_equal_hard(Node * a, Node * b) {
    if ((a->l && !b->l) || (!a->l && b->l)) return false;
    if ((a->r && !b->r) || (!a->r && b->r)) return false;
    if (a->s != b->s) return false;
    if (a->l && b->l && !check_equal_hard(a->l, b->l)) return false;
    if (a->r && b->r && !check_equal_hard(a->r, b->r)) return false;
    return true;
}

bool check_equal(Node * a, Node * b) {
    if (a->hash != b->hash) return false;
    return check_equal_hard(a, b);
}

Node * parse_neg(const std::string &s, int &ptr);
Node * parse_conj(const std::string &s, int &ptr);
Node * parse_disj(const std::string &s, int &ptr);
Node * parse_expr(const std::string &s, int &ptr);
Node * parse_header();

Node * parse_neg(const std::string &s, int &ptr) {
    char c = s[ptr];
    if (c >= 'A' && c <= 'Z') {
        std::string name;
        name += c;
        ptr++;
        while (ptr < s.length() && ((s[ptr] >= '0' && s[ptr] <= '9') || (s[ptr] >= 'A' && s[ptr] <= 'Z'))) {
            name += s[ptr++];
        }
        return new Node(name, NULL, NULL);
    } else if (c == '!') {
        ptr++;
        Node * expr = parse_neg(s, ptr);
        return new Node("!", NULL, expr);
    } else if (c == '(') {
        ptr++;
        Node * expr = parse_expr(s, ptr);
        if (ptr >= s.length() || s[ptr++] != ')') {
            throw "error";
        }
        return expr;
    }
    throw "error";
}

Node * parse_conj(const std::string &s, int &ptr) {
    Node * expr = parse_neg(s, ptr);
    while (ptr < s.length() && s[ptr] == '&') {
        ptr++;
        Node * expr2 = parse_neg(s, ptr);
        expr = new Node("&", expr, expr2);
    }
    return expr;
}

Node * parse_disj(const std::string &s, int &ptr) {
    Node * expr = parse_conj(s, ptr);
    while (ptr < s.length() && s[ptr] == '|') {
        ptr++;
        Node * expr2 = parse_conj(s, ptr);
        expr = new Node("|", expr, expr2);
    }
    return expr;
}

Node * parse_expr(const std::string &s, int &ptr) {
    Node * expr1 = parse_disj(s, ptr);
    if (ptr < s.length() && s[ptr] == '-' && s[++ptr] == '>') {
        ptr++;
        Node * expr2 = parse_expr(s, ptr);
        return new Node("->", expr1, expr2);
    }
    return expr1;
}

std::map <std::string, int> is_assumption;
Node * parse_string_to_formula(const std::string &s) {
    int ptr = 0;
    return parse_expr(s, ptr);
}

void parse_header(const std::string & header, std::vector<Node *> & supposes, Node *& alpha, Node *& betta) {
    std::string loc_s;
    int loc_id = -1;
    for (signed int i = 0; i < header.length(); ) {
        std::string s;
        int ptr = 0;
        while (i < header.length() && header[i] != ',') {
            s += header[i];
            i++;
            if (header[i] == '|' && header[i + 1] == '-') {
                loc_id = i - s.length();
                loc_s = s;
                break;
            }
        }
        Node * expr = parse_expr(s, ptr);
        if (header[i] == ',') {
            i++;
            supposes.push_back(expr);
        } else if (header[i] == '|'){
            i += 2;
            alpha = expr;
        } else {
            betta = expr;
        }
    }
    
}

void Print(Node * v) {
    if (v) {
        std::cout << v->getAsString();
    }
}

bool fill_map(Node * formula, Node * template_, std::map<std::string, std::vector<Node *>> &variableMap) {
    if (formula == NULL && template_ == NULL) {
        return true;
    }
    if (formula == NULL || template_ == NULL) {
        return false;
    }
    if (formula == template_) {
        return true;
    }
    const std::string &tempStr = template_->s;
    if (is_variable(tempStr)) {
        variableMap[tempStr].push_back(formula);
        return true;
    } else {
        if (tempStr != formula->s) {
            return false;
        }
        return fill_map(formula->l, template_->l, variableMap) &&
                fill_map(formula->r, template_->r, variableMap);
    }
}

bool check_formula_is_similar_to_template(Node * formula, Node * template_) {
    std::map<std::string, std::vector<Node*>> variableMap;
    if (fill_map(formula, template_, variableMap)) {
        for (auto& it : variableMap) {
            std::vector<Node*> &nodes = it.second;
            for (Node* node : nodes) {
                if (!check_equal(node, *nodes.begin())) {
                    return false;
                }
            }
        }
        return true;
    }
    return false;
}

int check_is_axiom(Node * v) {
    for (int i = 0; i < 10; i++) {
        if (check_formula_is_similar_to_template(v, axioms[i])) {
            return i + 1;
        }
    }
    return -1;
}

bool check_is_assumption(Node * expr, std::vector<Node *> & supposes) {
    for (unsigned int i = 0; i < supposes.size(); i++) {
        if (check_equal(expr, supposes[i])) {
            return true;
        }
    }
    return false;
}

std::pair<int, int> check_MP(int id) {
    for (int i = id - 1; i >= 0; i--) {
        Node * AB = formulas[i];
        if (AB && AB->s == "->" && AB->r && formulas[id] && check_equal(AB->r, formulas[id])) {
            for (int j = 0; j < id; j++) {
                Node * A = formulas[j];
                if (A && AB->l && check_equal(A, AB->l)) {
                    return std::make_pair(j, i);
                }
            }
        }
    }
    return std::make_pair(-1, -1);
}

void init_axioms() {
    prime[0] = 1;
    prime[1] = 31;
    for (int i = 2; i < N * N; i++) {
        prime[i] = prime[i - 1] * prime[1];
    }
    axioms[0] = parse_string_to_formula("A->B->A");
    axioms[1] = parse_string_to_formula("(A->B)->(A->B->C)->(A->C)");
    axioms[2] = parse_string_to_formula("A->B->A&B");
    axioms[3] = parse_string_to_formula("A&B->A");
    axioms[4] = parse_string_to_formula("A&B->B");
    axioms[5] = parse_string_to_formula("A->A|B");
    axioms[6] = parse_string_to_formula("B->A|B");
    axioms[7] = parse_string_to_formula("(A->C)->(B->C)->(A|B->C)");
    axioms[8] = parse_string_to_formula("(A->B)->(A->!B)->!A");
    axioms[9] = parse_string_to_formula("!!A->A");
}

void init_assumptions(std::string s) {
    if (s[0] == '|') return;
    int ass_cnt = 1;
    for (int i = 0; i < s.length(); i++) {
        std::string var;
        for (int j = 0; i + j < s.length(); j++) {
            // std::cerr << "~~~ " << var << " ~~~\n";
            // std::cerr << "``` " << s[i + j] << " ```\n";
            if (s[i + j] == '|') {
                if (var.length() > 0) {
                    is_assumption[var] = ass_cnt;
                    ass_cnt++;
                }
                return;
            }
            if (s[i + j] == ',') {
                i += j;
                is_assumption[var] = ass_cnt;
                ass_cnt++;
                break;
            }
            var += s[i + j]; 
        }
    }
}

std::string check_brackets (std::string s) {
    if (is_assumption[s]) return s;
    if (s[0] != '(' || s[s.length() - 1] != ')') return "(" + s + ")";
    int cnt = 0;
    for (int i = 0; i < s.length(); i++) {
        if (s[i] == '(') ++cnt;
        if (s[i] == ')') --cnt;
        if (cnt == 0 && i < s.length() - 1) {
            return "(" + s + ")";
        }
    }
    return s;
}

int main() {
    freopen("input.txt" , "r", stdin);
    freopen("output.txt", "w", stdout);

    init_axioms();
    std::string header;
    std::vector<Node *> assumptions;
    Node * alpha;
    Node * betta;
    getline(std::cin, header);
    header = get_string_without_spaces(header);
    parse_header(header, assumptions, alpha, betta);

    int cnt = 1;
    std::string s;
    while (getline(std::cin, s)) {
        s = get_string_without_spaces(s);
        if (s.length() == 0) break;
        Node * expr = parse_string_to_formula(s);
        formulas[cnt - 1] = expr;
        int axiomNumber = check_is_axiom(expr);
        Node * tmp;
        if (axiomNumber != -1 || check_is_assumption(expr, assumptions)) {
            Print(expr); 
            std::cout << std::endl;
            // di -> (a -> di)
            tmp = new Node("->", expr, new Node("->", alpha, expr));
            Print(tmp); 
            std::cout << std::endl;
            delete tmp;
        } else if (check_equal(expr, alpha)) {
//                    out << "2:\n";
            // a -> (a -> a)
            tmp = new Node("->", alpha, new Node("->", alpha, alpha));
            Print(tmp); 
            std::cout << std::endl;
            delete tmp;
            // (a -> (a -> a)) -> (a -> ((a -> a) -> a)) -> (a -> a)
            tmp = new Node("->", new Node("->", alpha, new Node("->", alpha, alpha)), 
                new Node("->", new Node("->", alpha, new Node ("->", 
                new Node("->", alpha, alpha), alpha)), new Node("->", alpha, alpha)));
            Print(tmp); 
            std::cout << std::endl;
            delete tmp;
            // (a -> ((a -> a) -> a)) -> (a -> a)
            tmp =  new Node("->", new Node("->", alpha, new Node ("->", 
                new Node("->", alpha, alpha), alpha)), new Node("->", alpha, alpha));
            Print(tmp); 
            std::cout << std::endl;
            delete tmp;
            // a -> ((a -> a) -> a)
            tmp = new Node("->", alpha, new Node ("->", 
                new Node("->", alpha, alpha), alpha));
            Print(tmp); 
            std::cout << std::endl;
            delete tmp;
        } else {
//                    out << "3:\n";
            std::pair<int, int> mp = check_MP(cnt - 1);
            if (mp.first != -1) {
                Node * dj = formulas[mp.first];
                //Node * dk = formulas[mp.second];
                // (a -> dj) -> ((a -> (dj -> di))) -> (a -> di)
                tmp = new Node("->", new Node("->", alpha, dj), new Node("->", 
                    new Node("->", alpha, new Node("->", dj, expr)), 
                    new Node("->", alpha, expr)));
                Print(tmp);
                std::cout << std::endl;
                delete tmp;
                // ((a -> (dj -> di))) -> (a -> di)
                tmp = new Node("->", new Node("->", alpha, new Node("->", dj, expr)), 
                    new Node("->", alpha, expr));
                Print(tmp);
                std::cout << std::endl;
                delete tmp;
            } else {
                throw "error";
            }
        }
        tmp = new Node("->", alpha, expr);
        Print(tmp);
        std::cout << std::endl;
        delete tmp;
        cnt++;
    }

    return 0;
}




















