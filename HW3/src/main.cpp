// HW3
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
#include <map>
#include <set>

const int N = 5000;

long long prime[N * N];
std::map<std::string, bool> initial_assumptions;

std::string get_string_without_spaces(const std::string & s) {
    std::string res = "";
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

struct Node {
    long long hash;
    int vertCnt;
    int ptrCnt;
    bool lastValue;
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
        if (r) {
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
    std::string get_as_string(bool isMain = true) {
        std::string result = "";
        if (!is_variable(s) && !isMain) {
            result += "(";
        }
        if (l) {
            result += l->get_as_string(false);
        }
        result += s;
        if (r) {
            result += r->get_as_string(false);
        }
        if (!is_variable(s) && !isMain) {
            result += ")";
        }
        return result;
    }

    bool eval(const std::map<std::string, bool> &values) {
        if (is_variable(s)) {
            auto it = values.find(s);
            if (it == values.end()) throw "There is no this value in map";
            lastValue = it->second;
            return lastValue;
        }
        bool leftValue;
        bool rightValue;
        if (l) leftValue = l->eval(values);
        if (r) rightValue = r->eval(values);
        if (s == "->") {
            return lastValue = rightValue | !leftValue;
        } else if (s == "|") {
            return lastValue = leftValue | rightValue;
        } else if (s == "&") {
            return lastValue = leftValue & rightValue;
        } else if (s == "!") {
            return lastValue = !rightValue;
        }
    }

    void get_variables(std::map<std::string, bool> &values) {
        if (is_variable(s)) {
            values[s] = false;
            return;
        }
        if (l) l->get_variables(values);
        if (r) r->get_variables(values);
    }
};

Node *notX(Node *x) {
    return new Node("!", NULL, x);
}

Node *notNotX(Node *x) {
    return notX(notX(x));
}

Node *axioms[10];

bool check_equal_hard(Node * a, Node * b) {
    if (!a && !b) return true;
    if (!a || !b) return false;
    if (a->s != b->s) return false;
    if (!check_equal_hard(a->l, b->l)) return false;
    if (!check_equal_hard(a->r, b->r)) return false;
    return true;
}

// TODO: for 3 Nodes
// a != NULL && b != NULL
bool check_equal(Node * a, Node * b) {
    if (a->hash != b->hash) return false;
    return check_equal_hard(a, b);
}

Node * parse_title();
Node * parse_expr(const std::string &s, int &ptr);
Node * parse_disj(const std::string &s, int &ptr);
Node * parse_conj(const std::string &s, int &ptr);
Node * parse_unary(const std::string &s, int &ptr);
void getAA(Node *a, std::vector<Node*> &proof);

Node * parse_unary(const std::string &s, int &ptr) {
    char c = s[ptr];
    if (c >= 'A' && c <= 'Z') {
        std::string name;
        name += c;
        ptr++;
        while (ptr < s.length() && s[ptr] >= '0' && s[ptr] <= '9') {
            name += s[ptr++];
        }
        return new Node(name, NULL, NULL);
    } else if (c == '!') {
        ptr++;
        Node * expr = parse_unary(s, ptr);
        return notX(expr);
    } else if (c == '(') {
        ptr++;
        Node * expr = parse_expr(s, ptr);
        if (ptr >= s.length() || s[ptr++] != ')') {
            throw ") doesn't exist";
        }
        return expr;
    }
    throw "incorrect formula";
}

Node * parse_conj(const std::string &s, int &ptr) {
    Node * expr = parse_unary(s, ptr);
    while (ptr < s.length() && s[ptr] == '&') {
        ptr++;
        Node * expr2 = parse_unary(s, ptr);
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
    if (v) {
        std::cout << v->get_as_string();
    }
}

void Print(std::vector<Node *> v) {
    std::cout << "Printing std::vector<Node *>: \n";
    for (size_t i = 0; i < v.size(); ++i) {
        if (v[i]) {
            std::cout << v[i]->get_as_string() << ' ';
        }
    }
    std::cout << std::endl;
}

void Print(std::vector<std::vector<Node *> > v) {
    std::cout << "Printing std::vector<std::vector<Node *>>: \n";
    for (size_t i = 0; i < v.size(); ++i) {
        for (size_t j = 0; j < v[i].size(); ++i) {
            if (v[i][j]) {
                std::cout << v[i][j]->get_as_string() << ' ';
            }
        }
        std::cout << std::endl;
    }
}

bool fill_map(Node * formula, Node * template_, std::map<std::string, std::vector<Node *> > &variableMap) {
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
    std::map<std::string, std::vector<Node*> > variableMap;
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

bool check_is_assumption(Node * expr, const std::vector<Node *> &assumptions, int begin_ = 0, int end_ = -1) {
    if (end_ == -1) {
        end_ = assumptions.size();
    }
    for (unsigned int i = begin_; i < end_; i++) {
        if (check_equal(expr, assumptions[i])) {
            return true;
        }
    }
    return false;
}

std::pair<int, int> check_MP(const std::vector<Node*> &formulas, int id, int begin_ = 0) {
    for (int i = id - 1; i >= begin_; i--) {
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

Node *get_formula_from_template(Node *v, Node *a, Node *b, Node *c) {
    if (!v) return NULL;
    if (v->s == "A") return a;
    if (v->s == "B") return b;
    if (v->s == "C") return c;
    return new Node(v->s,
                    get_formula_from_template(v->l, a, b, c),
                    get_formula_from_template(v->r, a, b, c));
}

Node *get_axiom(int axiomNumber, Node *a = NULL, Node *b = NULL, Node *c = NULL) {
    return get_formula_from_template(axioms[--axiomNumber], a, b, c);
}

void deduction(
        const std::vector<Node*> &formulas,
        const std::vector<Node*> &assumptions,
        Node *alpha,
        Node *betta,
        std::vector<Node*> &proof,
        int supBegin_ = 0, int supEnd_ = -1,
        int forBegin_ = 0, int forEnd_ = -1) {
    std::cerr << "### stage 4.2 (deduction)\n";
    if (supEnd_ == -1) {
        supEnd_ = assumptions.size();
    }
    if (forEnd_ == -1) {
        forEnd_ = formulas.size();
    }

    if (!check_equal(formulas[forEnd_ - 1], betta)) {
        throw "Deduction fail : last formula != betta";
    }

    for (int i = forBegin_; i < forEnd_; i++) {
        Node * expr = formulas[i];
        int axiomNumber = check_is_axiom(expr);
        if (axiomNumber != -1 || check_is_assumption(expr, assumptions, supBegin_, supEnd_)) {
            // di
            proof.push_back(expr);
            // di -> (a -> di)
            proof.push_back(get_axiom(1, expr, alpha));
            proof.push_back(proof.back()->r);
        } else if (check_equal(expr, alpha)) {
            getAA(alpha, proof);
        } else {
            std::pair<int, int> mp = check_MP(formulas, i, forBegin_);
            if (mp.first != -1) {
                Node * dj = formulas[mp.first];
                //Node * dk = formulas[mp.second];
                // (a -> dj) -> ((a -> (dj -> di))) -> (a -> di)
                proof.push_back(get_axiom(2, alpha, dj, expr));
                // ((a -> (dj -> di))) -> (a -> di)
                proof.push_back(proof.back()->r);
                // a -> di
                proof.push_back(proof.back()->r);
            // } else if (initial_assumptions[expr->get_as_string()]) {
            //     proof.push_back(expr);
            } else {
                std::cout << "FAIL: " << "\n" << expr->get_as_string() << "\n";
                throw "there is an error in proof";
            }
        }
    }
}

void total_deduction(const std::vector<Node*> &startFormulas, const std::vector<Node*> &assumptions, const Node *firstBetta, std::vector<Node*> &proof) {
    Node *betta = new Node(firstBetta->s, firstBetta->l, firstBetta->r);
    std::vector<Node*> formulas(startFormulas);
    for (int i = assumptions.size() - 1; i >= 0; i--) {
        std::vector<Node*> tempResult;
        deduction(formulas, assumptions, assumptions[i], betta, (i == 0 ? proof : tempResult), 0, i);
        formulas = tempResult;
        betta = new Node("->", assumptions[i], betta);
    }
}

// α → β → (¬β → ¬α)
void get_contra_positive(Node *a, Node *b, std::vector<Node*> &proof) {
    /*
        α → β, ¬β |- ¬α.
        (2) α → β Допущение
        (1) (α → β) → (α → ¬β) → ¬α Сх. акс. 9
        (3) (α → ¬β) → ¬α M.P. 2,1
        (4) ¬β → (α → ¬β) Сх. акс. 1
        (5) ¬β Допущение
        (6) α → ¬β M.P. 5,4
        (7) ¬α M.P. 6,3
    */
    std::vector<Node*> assumptions;
    std::vector<Node*> formulas;
    assumptions.push_back(new Node("->", a, b));
    assumptions.push_back(notX(b));
    formulas.push_back(assumptions[0]);
    formulas.push_back(get_axiom(9, a, b));
    formulas.push_back(formulas.back()->r);
    formulas.push_back(get_axiom(1, notX(b), a));
    formulas.push_back(assumptions[1]);
    formulas.push_back(new Node("->", a, notX(b)));
    formulas.push_back(notX(a));
    total_deduction(formulas, assumptions, notX(a), proof);
}

void get_third(Node *a, std::vector<Node*> &proof) {
    /*1. Для начала покажем ` ¬(α ∨ ¬α) → ¬α:
    (1) α → α ∨ ¬α Сх. акс. 6
    (2). . .(n + 1) γ1, . . . γn−1,(α → α ∨ ¬α) → (¬(α ∨ ¬α) → ¬α) Д-во из леммы 4.4
    (n + 2) ¬(α ∨ ¬α) → ¬α M.P. 1,n + 1
    */
    proof.push_back(get_axiom(6, a, notX(a)));
    get_contra_positive(a, new Node ("|", a, notX(a)), proof);
    proof.push_back(proof.back()->r);
    /*
    2. Затем докажем ` ¬(α ∨ ¬α) → ¬¬α:
    (1) ¬α → α ∨ ¬α Сх. акс. 7
    (2). . .(k + 1) δ1, . . . δk−1,(¬α → α ∨ ¬α) → (¬(α ∨ ¬α) → ¬¬α) Д-во из леммы 4.4
    (k + 2) ¬(α ∨ ¬α) → ¬¬α M.P. 1,k + 1
    */
    proof.push_back(get_axiom(7, a, notX(a)));
    get_contra_positive(notX(a), new Node ("|", a, notX(a)), proof);
    proof.push_back(proof.back()->r);
    /*
    3. Теперь докажем все вместе:
    (1) ¬(α ∨ ¬α) → ¬α по пункту 1
    (2) ¬(α ∨ ¬α) → ¬¬α по пункту 2
    (3) (¬(α ∨ ¬α) → ¬α) → (¬(α ∨ ¬α) → ¬¬α) → (¬¬(α ∨ ¬α)) Сх. акс. 9
    (4) (¬(α ∨ ¬α) → ¬¬α) → ¬¬(α ∨ ¬α) M.P. 1,3
    (5) ¬¬(α ∨ ¬α) M.P. 2,4
    (6) ¬¬(α ∨ ¬α) → (α ∨ ¬α) Сх. акс. 10
    (7) α ∨ ¬α M.P. 5,6
    */
    proof.push_back(get_axiom(9, notX(new Node("|", a, notX(a))), notX(a)));
    proof.push_back(proof.back()->r);
    proof.push_back(proof.back()->r);
    proof.push_back(get_axiom(10, new Node("|", a, notX(a))));
    proof.push_back(proof.back()->r);
}

void getAA(Node *a, std::vector<Node*> &proof) {
    proof.push_back(get_axiom(1, a, a));
    proof.push_back(get_axiom(1, a, new Node("->", a, a)));
    proof.push_back(get_axiom(2, a, new Node("->", a, a), a));
    proof.push_back(proof.back()->r);
    proof.push_back(proof.back()->r);
}

void get_all_variable_variants(std::set<std::map<std::string, bool> > &variantes, Node *expr) {
    std::map<std::string, bool> variables;
    expr->get_variables(variables);
    std::vector<std::string> variablesNames;
    for (auto &it: variables) {
        variablesNames.push_back(it.first);
    }
    // std::vector<std::map<std::string, bool> > variantes1;
    for (int mask = 0; mask < (1 << variables.size()); mask++) {
        std::map<std::string, bool> loc_variantes;
        // variantes1.push_back(std::map<std::string, bool>());
        expr->get_variables(loc_variantes);
        // expr->get_variables(variantes1.back());
        for (int bit = 0; bit < variablesNames.size(); bit++) {
            auto& vn_ref = variablesNames[bit];
            loc_variantes[vn_ref] = (initial_assumptions[vn_ref] || ((mask & (1 << bit)) != 0));
        }
        variantes.insert(loc_variantes);
    }
}

void print_all_variable_variants(std::set<std::map<std::string, bool> > &variantes) {
    for (auto &i: variantes) {
        for (auto &it: i) {
            std::cout << it.first << "=" << it.second << ", ";
        }
        std::cout << std::endl;
    }
}

void get_assumption(const std::map<std::string, bool> &values, std::vector<Node*> &assumption) {
    for (auto &x : values) {
        assumption.push_back(new Node(x.first, NULL, NULL));
        if (!x.second) {
            assumption.back() = notX(assumption.back());
        }
    }
}

void implFF(Node *a, Node *b, std::vector<Node*> &proof) {
    std::vector<Node*> tmp;
    tmp.push_back(notX(a));
    tmp.push_back(notX(b));
    tmp.push_back(a);
    tmp.push_back(get_axiom(1, a, notX(b)));
    tmp.push_back(tmp.back()->r);
    tmp.push_back(get_axiom(1, notX(a), notX(b)));
    tmp.push_back(tmp.back()->r);
    tmp.push_back(get_axiom(9, notX(b), a));
    tmp.push_back(tmp.back()->r);
    tmp.push_back(tmp.back()->r);
    tmp.push_back(get_axiom(10, b));
    tmp.push_back(tmp.back()->r);
    std::vector<Node*> sup;
    sup.push_back(notX(a));
    sup.push_back(notX(b));
    deduction(tmp, sup, a, b, proof);
}

void make_derivation(Node *expr, std::vector<Node*> &proof, const std::map<std::string, bool> &values, bool firstTime = true) {
    if (firstTime) {
        expr->eval(values);
    }

    if (is_variable(expr->s) || check_is_axiom(expr) != -1) {
        proof.push_back(expr);
        if (!expr->lastValue) {
            proof.back() = notX(proof.back());
        }
        return;
    }

    if (expr->s == "|") {
        Node *a = expr->l;
        Node *b = expr->r;

        if (a->lastValue) {
            make_derivation(a, proof, values, false);
            if (!is_variable(a->s)) proof.push_back(a);
            proof.push_back(get_axiom(6, a, b));
            proof.push_back(proof.back()->r);
        } else if (b->lastValue) {
            make_derivation(b, proof, values, false);
            if (!is_variable(b->s)) proof.push_back(b);
            proof.push_back(get_axiom(7, a, b));
            proof.push_back(proof.back()->r);
        } else {
            make_derivation(notX(a), proof, values, false);
            make_derivation(notX(b), proof, values, false);
            if (!is_variable(a->s)) proof.push_back(notX(a));
            if (!is_variable(b->s)) proof.push_back(notX(b));
            proof.push_back(get_axiom(1, notX(a), expr));
            proof.push_back(proof.back()->r);


            getAA(a, proof);
            implFF(b, a, proof);
            proof.push_back(get_axiom(8, a, b, a));
            proof.push_back(proof.back()->r);
            proof.push_back(proof.back()->r);
            proof.push_back(get_axiom(9, expr, a));
            proof.push_back(proof.back()->r);
            proof.push_back(proof.back()->r);
        }
    } else if (expr->s == "&") {
        Node *a = expr->l;
        Node *b = expr->r;
        if (a->lastValue && b->lastValue) {
            make_derivation(a, proof, values, false);
            make_derivation(b, proof, values, false);
            if (!is_variable(a->s)) proof.push_back(a);
            if (!is_variable(b->s)) proof.push_back(b);
            proof.push_back(get_axiom(3, a, b));
            proof.push_back(proof.back()->r);
            proof.push_back(proof.back()->r);
        } else if (a->lastValue && !b->lastValue) {
            make_derivation(notX(b), proof, values, false);
            proof.push_back(get_axiom(5, a, b));
            if (!is_variable(b->s)) proof.push_back(notX(b));
            proof.push_back(get_axiom(1, notX(b), new Node("&", a, b)));
            proof.push_back(proof.back()->r);
            proof.push_back(get_axiom(9, new Node("&", a, b), b));
            proof.push_back(proof.back()->r);
            proof.push_back(proof.back()->r);
        } else {
            make_derivation(notX(a), proof, values, false);
            proof.push_back(get_axiom(4, a, b));
            if (!is_variable(a->s)) proof.push_back(notX(a));
            proof.push_back(get_axiom(1, notX(a), new Node("&", a, b)));
            proof.push_back(proof.back()->r);
            proof.push_back(get_axiom(9, new Node("&", a, b), a));
            proof.push_back(proof.back()->r);
            proof.push_back(proof.back()->r);
        }
    } else if (expr->s == "->") {
        Node *a = expr->l;
        Node *b = expr->r;

        if (b->lastValue) {
            make_derivation(b, proof, values, false);
            if (!is_variable(b->s)) proof.push_back(b);
            proof.push_back(get_axiom(1, b, a));
            proof.push_back(proof.back()->r);
        } else if (!a->lastValue && !b->lastValue) {
            make_derivation(notX(a), proof, values, false);
            make_derivation(notX(b), proof, values, false);
            implFF(a, b, proof);
        } else if (a->lastValue && !b->lastValue) {
            make_derivation(a, proof, values, false);
            make_derivation(notX(b), proof, values, false);
            if (!is_variable(a->s)) proof.push_back(a);
            if (!is_variable(b->s)) proof.push_back(notX(b));
            proof.push_back(get_axiom(1, notX(b), expr));
            proof.push_back(proof.back()->r);

            std::vector<Node*> sup;
            sup.push_back(a);
            sup.push_back(notX(b));
            std::vector<Node*> tmp;
            tmp.push_back(a);
            tmp.push_back(expr);
            tmp.push_back(b);
            deduction(tmp, sup, expr, b, proof);

            proof.push_back(get_axiom(9, expr, b));
            proof.push_back(proof.back()->r);
            proof.push_back(proof.back()->r);
        }
    } else if (expr->s == "!") {
        if (expr->r->s == "!") {
            Node *a = expr->r->r;
            if (a->lastValue) {
                make_derivation(a, proof, values, false);
                if (!is_variable(a->s)) proof.push_back(a);
                proof.push_back(get_axiom(1, a, notX(a)));
                proof.push_back(proof.back()->r);
                getAA(notX(a), proof);
                proof.push_back(get_axiom(9, notX(a), a));
                proof.push_back(proof.back()->r);
                proof.push_back(proof.back()->r);
            } else {
                make_derivation(notX(a), proof, values, false);
                if (!is_variable(a->s)) proof.push_back(notX(a));
            }
        } else {
            make_derivation(expr->r, proof, values, false);
        }
    }
}

void exclude(const std::vector<Node*> &assumptions, int supBegin, int supEnd,
             Node *p, Node *a,
             const std::vector<Node*> &formulas1, const std::vector<Node*> &formulas2,
             std::vector<Node*> &proof) {
    std::cerr << "### stage 4.1 (excluding)\n"; // debug
    deduction(formulas1, assumptions, notX(p), a, proof, supBegin, supEnd);
    deduction(formulas2, assumptions, p, a, proof, supBegin, supEnd);

    get_third(p, proof);
    proof.push_back(get_axiom(8, p, notX(p), a));
    proof.push_back(proof.back()->r);
    proof.push_back(proof.back()->r);
    proof.push_back(proof.back()->r);
}

int turniket = -1, last_comma = -1;
void parse_header(const std::string & header, Node *& alpha, Node *& betta) {
    if (header[0] == '|' && header[1] == '=') return;
    std::cerr << "parsing..\n"; // debug
    for (int i = 0; i < header.length(); ) {
        std::string s;
        int ptr = 0;
        while (i < header.length() && header[i] != ',') {
            s += header[i];
            i++;
            if (header[i] == '|' && header[i + 1] == '=') {
                std::cerr << "foud turniket\n"; // debug
                turniket = i;
                // last_assumption = s;
                break;
            }
        }
        std::cerr << "assumption: " << s << std::endl; // debug
        Node * expr = parse_expr(s, ptr);
        if (header[i] == ',' || turniket != -1) {
            last_comma = i;
            i++;
            initial_assumptions[expr->get_as_string()] = true;
        } else if (header[i] == '|'){
            i += 2;
            alpha = expr;
        } else {
            betta = expr;
        }
        if (turniket != -1) break;
    }
}

void print_initial_assumptions() {
    for (auto &i: initial_assumptions) {
        std::cout << i.first << " ";
    }
    std::cout << std::endl;
}

void print_header (std::string header) {
    for (int i = 0; i < last_comma; ++i) {
        std::cout << header[i];
    }
    std::cout << "|=";
    std::string left, right;
    for (int i = last_comma + 1; i < turniket; ++i) {
        left += header[i];
    }
    // std::cerr << left << " ";
    left = parse_string_to_formula(left)->get_as_string();
    // std::cerr << left << std::endl;
    for (int i = turniket + 2; i < header.length(); ++i) {
        right += header[i];
    }
    right = parse_string_to_formula("(" + left + ")->" + right)->get_as_string();
    std::cout << right << std::endl;
}

int main() {
    freopen("input.txt" , "r", stdin);
    freopen("output.txt", "w", stdout);
    init_axioms();
    std::vector<Node*> assumptions;
    std::vector<Node*> proof;
    std::vector<Node*> formulas;
    std::string s;
    std::string header;
    Node * alpha;
    Node * betta;
    getline(std::cin, s);
    s = header = get_string_without_spaces(s);
    std::cerr << s << std::endl;
    parse_header(header, alpha, betta);
    
    s = s.erase(0, s.find("|=") + 2);
    // std::cerr << s << std::endl; //debug
    // print_header(header);
    print_initial_assumptions(); // debug
    try {
        std::cerr << s << std::endl; // debug
        Node *expr = parse_string_to_formula(s);

        std::set<std::map<std::string, bool> > variableVariantes; // имя переменной и её значения (все варианты)
        get_all_variable_variants(variableVariantes, expr);
        print_all_variable_variants(variableVariantes); // debug
        std::cerr << "### stage 1\n";
        for (auto &it : variableVariantes) {
            if (!expr->eval(it)) {
                std::cout << "Высказывание ложно при ";
                for (auto var = it.begin(); var != it.end(); ++var) {
                    std::cout << var->first << "=" << (var->second ? "И" : "Л");
                    std::cout << (++var == it.end() ? "\n" : ", ");
                    --var;
                }
                return 0;
            }
        }
        std::cerr << "### stage 2\n"; // debug
        // How to fill assumptions?
        std::vector<std::vector<Node*> > prooves(variableVariantes.size());
        std::vector<std::vector<Node*> > assumptions(variableVariantes.size());
        int ii = 0;
        for (auto &it: variableVariantes) {
            get_assumption(it, assumptions[ii]);
            make_derivation(expr, prooves[ii], it);
            ++ii;
        }
        Print(assumptions);
        std::cerr << "### stage 3\n"; // debug
        int varCnt = variableVariantes.begin()->size();
        int supStep = 2;
        int const totalCnt = varCnt;

        while (varCnt != 0) {
            std::cerr << "### stage 4\n"; // debug
            std::vector<std::vector<Node*> > newProoves;
            for (int i = 0, curSupInd = 0; i < prooves.size(); i += 2, curSupInd += supStep) {
                std::vector<Node*> newProof;
                int curIndP = totalCnt - varCnt;
                exclude(
                            assumptions[curSupInd],
                            curIndP + 1,
                            totalCnt,
                            assumptions.back()[curIndP],
                            expr,
                            prooves[i],
                            prooves[i + 1],
                            newProof
                        );
                newProoves.push_back(newProof);
            }
            prooves = newProoves;
            varCnt--;
            supStep *= 2;
        }
        proof = prooves.back();
        std::cerr << "### stage 5\n"; // debug
        int c = 0;
        for (Node *v : proof) {
            c++;
            std::cout << v->get_as_string() << "\n";
        }
        std::cout << "Finish, " << c << " steps" << "\n";
    } catch (char const * err) {
        std::cerr << err << " in " << s << "\n";
    } catch (...) {
        std::cerr << "something wrong" << " in " << s << "\n";
    }
    return 0;
}