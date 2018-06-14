#include <iostream>
#include <string>
#include <map>
#include <vector>
#include <cstdio>

#define N 5000

long long prime[N * N];

struct Node {
    long long hash;
    int vertCnt;
    std::string s;
    Node * l;
    Node * r;
    Node() : hash(0), l(NULL), r(NULL) {}
    Node(std::string s, Node * l, Node * r) : s(s), l(l), r(r) {
        vertCnt = 1;
        int lCnt = 0, rCnt = 0;
        if (l) {
            lCnt  = l->vertCnt;
            vertCnt += lCnt;
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
        }

    }
    ~Node() {
        if (l) delete l;
        if (r) delete r;
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

bool is_variable(const std::string& s) {
    if (s.length() > 0 && s[0] >= 'A' && s[0] <= 'Z') {
        return true;
    }
    return false;
}

Node * formulas[N*N], * axioms[10];

bool check_equal_hard(Node * a, Node * b) {
    if (!a && !b) return true;
    if (!a || !b) return false;
    if (a->s != b->s) return false;
    if (!check_equal_hard(a->l, b->l)) return false;
    if (!check_equal_hard(a->r, b->r)) return false;
    return true;
}

bool check_equal(Node * a, Node * b) {
    if (!a && !b) {
        return true;
    }
    if (!a || !b) {
        return false;
    }
    if (a == b) {
        return true;
    }
    if (a->hash != b->hash) return false;
    return check_equal_hard(a, b);
}

Node * parse_neg(const std::string &s, int &ptr);
Node * parse_conj(const std::string &s, int &ptr);
Node * parse_disj(const std::string &s, int &ptr);
Node * parse_expr(const std::string &s, int &ptr);

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

Node * parse_string_to_formula(const std::string &s) {
    int ptr = 0;
    return parse_expr(s, ptr);
}

void Print(Node * v) {
    if (v->l) {
        std::cout << "(";
        Print(v->l);
        std::cout << ")";
    }
    std::cout << v->s;
    if (v->r) {
        std::cout << "(";
        Print(v->r);
        std::cout << ")";
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

std::map <std::string, int> is_assumption;

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

int main() {
    freopen("input.txt" , "r", stdin);
    freopen("output.txt", "w", stdout);

    int cnt = 1;
    std::string s;
    getline(std::cin, s);
    // remove_if(s.begin(), s.end(), isspace);
    s = get_string_without_spaces(s);
    init_axioms();
    init_assumptions(s);
    while (getline(std::cin, s)) {
        // remove_if(s.begin(), s.end(), isspace);
        s = get_string_without_spaces(s);
        if (s.length() == 0) break;
        std::cout << "(" << cnt << ") " << s;
        Node * expr = parse_string_to_formula(s);
        formulas[cnt - 1] = expr;
        int axiomNumber = check_is_axiom(expr);
        if (axiomNumber != -1) {
            std::cout << " (Сх. акс. " << axiomNumber << ")\n";
        } else {
            std::pair<int, int> mp = check_MP(cnt - 1);
            if (mp.first != -1) {
                std::cout << " (M.P. " << mp.second + 1 << ", " << mp.first + 1 << ")\n";
            } else {
                if (is_assumption[s] > 0) {
                    std::cout << " (Предп. " << is_assumption[s] << ")\n";
                }
                else {
                std::cout << " (Не доказано)\n";
                }
            }
        }
        cnt++;
    }

    return 0;
}