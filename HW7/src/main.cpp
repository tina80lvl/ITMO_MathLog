// HW7
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
#include <map>
#include <set>
#include "NodeParser.h"

std::ifstream cin("input.txt");
    std::ofstream cout("output.txt");

struct SubstituteError {
    Node *x, *y;
    std::string a;
    // y[a:=x]
    SubstituteError(Node *y, const std::string &a, Node *x) : x(x), y(y), a(a) {}
};

struct VariableFreeError {
    Node *x;
    std::string a;
    VariableFreeError(Node *x, const std::string &a) : x(x), a(a) {}
};

struct KvantorError {
    std::string type;
    std::string a;
    Node *x;
    KvantorError(const std::string &type, const std::string &a, Node *x) : type(type), a(a), x(x) {}
};

struct UnknownError {

};


std::vector<Node*> axioms;

bool check_equal(Node * a, Node * b) {
    if (!a && !b) return true;
    if (!a || !b) return false;
    if (a == b) return true;
    if (a->hash != b->hash) return false;
    else return true;
    if (a->terms.size() != b->terms.size()) return false;
    if (a->s != b->s) return false;
    for (int i = 0; i < a->terms.size(); i++) {
        if (!check_equal(a->terms[i], b->terms[i])) {
            return false;
        }
    }
    if (!check_equal(a->l, b->l)) return false;
    if (!check_equal(a->r, b->r)) return false;
    return true;
}

// by predicate or by variable
bool fill_map(Node * formula, Node * template_, std::map<std::string, std::vector<Node *> > &variableMap, bool byPred = true) {
    if (!formula && !template_) return true;
    if (!formula || !template_) return false;
    const std::string &tempStr = template_->s;
    if ((byPred && template_->is_predicate()) || (!byPred && template_->is_variable())) { // added brackets
        variableMap[tempStr].push_back(formula);
        return true;
    } else {
        if (tempStr != formula->s) {
            return false;
        }
        return fill_map(formula->l, template_->l, variableMap, byPred) &&
                fill_map(formula->r, template_->r, variableMap, byPred);
    }
}

// by predicate or by variable
bool check_formula_is_similar_to_template(Node *formula, Node *template_, bool byPred = true) {
    if (!formula && !template_) return true;
    if (!formula || !template_) return false;
    if (formula == template_) return true;
    std::map<std::string, std::vector<Node*> > variableMap;
    if (fill_map(formula, template_, variableMap, byPred)) {
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

// for 11, 12, 21 axioms
bool check_formula_is_similar_to_template2(Node *formula, Node *template_) {
    if (!formula && !template_) return true;
    if (!formula || !template_) return false;
    if (formula == template_) return true;
    if (template_->is_variable()) {
        return formula->is_variable();
    }
    if (template_->is_predicate()) {
        return true;
    }
    if (formula->s != template_->s) {
        return false;
    }
    return check_formula_is_similar_to_template2(formula->l, template_->l) &&
            check_formula_is_similar_to_template2(formula->r, template_->r);
}

Node *get_first_not_bound(Node *formula, Node *template_, const std::string &x) {
    if (!formula || !template_) return NULL;
    if (template_->s == x) {
        return formula;
    }

    if (template_->s != formula->s) {
        return NULL;
    }

    if (template_->terms.size() != formula->terms.size()) {
        return NULL;
    }

    bool isKvant = false;
    if (formula->s == "@" || formula->s == "?") {
        if (formula->l->s == x) {
            return NULL;
        }
        isKvant = true;
    }

    for (int i = 0; i < formula->terms.size(); i++) {
        Node *res = get_first_not_bound(formula->terms[i],
                                     template_->terms[i],
                                     x);
        if (res) return res;
    }

    if (!isKvant) {
        Node *res1 = get_first_not_bound(formula->l, template_->l, x);
        if (res1) return res1;
    }
    Node *res2 = get_first_not_bound(formula->r, template_->r, x);
    if (res2) return res2;
}

bool check_is_free_for_sub(Node *v, const std::map<std::string, int> &bounded) {
    if (!v) return true;
    for (Node *term : v->terms) {
        if  (!check_is_free_for_sub(term, bounded)) {
            return false;
        }
    }
    if (v->is_variable()) {
        auto it = bounded.find(v->s);
        return it == bounded.end() || it->second == 0;
    }
    return check_is_free_for_sub(v->l, bounded) && check_is_free_for_sub(v->r, bounded);
}

bool check_is_not_free(Node *v, const std::string &x, std::map<std::string, int> &bounded) {
    if (!v) return true;
    if (v->s == "@" || v->s == "?") {
        bounded[v->l->s]++;
    }

    if (v->is_variable()) {
        auto it = bounded.find(v->s);
        return it == bounded.end() || it->second != 0;
    }
    bool result = check_is_not_free(v->l, x, bounded) && check_is_not_free(v->r, x, bounded);
    if (v->s == "@" || v->s == "?") {
        bounded[v->l->s]--;
    }
    return result;
}

bool check_is_not_free(Node *v, const std::string &x) {
    std::map<std::string, int> bounded;
    return check_is_not_free(v, x, bounded);
}

Node *substitute(Node *alpha, const std::string &x, Node *tetta, std::map<std::string, int> &bounded, bool &isFree) {
    if (!alpha) return NULL;

    bool isKvant = false;
    if (alpha->s == "@" || alpha->s == "?") {
        if (alpha->l->s == x) {
            return alpha;
        }
        bounded[alpha->l->s]++;
        isKvant = true;
        return new Node(alpha->s,
                        alpha->l,
                        substitute(alpha->r, x, tetta, bounded, isFree));
    }
    Node *result = NULL;
    if (alpha->s == x) {
        if (!check_is_free_for_sub(tetta, bounded)) {
            isFree = false;
        }
        result = tetta;
    } else {
        if (alpha->terms.size() == 0) {
            result = new Node(alpha->s,
                            substitute(alpha->l, x, tetta, bounded, isFree),
                            substitute(alpha->r, x, tetta, bounded, isFree));
        } else {
            std::vector<Node*> terms;
            for (Node *term : alpha->terms) {
                terms.push_back(substitute(term, x, tetta, bounded, isFree));
            }
            result = new Node(alpha->s, terms);
        }
    }
    if (isKvant) {
        bounded[alpha->l->s]--;
    }
    return result;
}

// alpha[x:=tetta]
Node *substitute(Node *alpha, const std::string &x, Node *tetta, bool &isFree) {
    std::map<std::string, int> bounded;
    Node *result = substitute(alpha, x, tetta, bounded, isFree);
    return result;
}

Node *get_formula_from_template(Node *v, Node *a = NULL, Node *b = NULL, Node *c = NULL) {
    if (!v) return NULL;
    if (v->s == "A") return a;
    if (v->s == "B") return b;
    if (v->s == "C") return c;
    return new Node(v->s,
                    get_formula_from_template(v->l, a, b, c),
                    get_formula_from_template(v->r, a, b, c));
}

void init() {
    prime[0] = 1;
    prime[1] = 31;
    for (int i = 2; i < N * N; i++) {
        prime[i] = prime[i - 1] * prime[1];
    }
    axioms = std::vector<Node*>(30);
    axioms[1] = parse_string_to_formula("A->B->A");
    axioms[2] = parse_string_to_formula("(A->B)->(A->B->C)->(A->C)");
    axioms[3] = parse_string_to_formula("A->B->A&B");
    axioms[4] = parse_string_to_formula("A&B->A");
    axioms[5] = parse_string_to_formula("A&B->B");
    axioms[6] = parse_string_to_formula("A->A|B");
    axioms[7] = parse_string_to_formula("B->A|B");
    axioms[8] = parse_string_to_formula("(A->C)->(B->C)->(A|B->C)");
    axioms[9] = parse_string_to_formula("(A->B)->(A->!B)->!A");
    axioms[10] = parse_string_to_formula("!!A->A");

    axioms[11] = parse_string_to_formula("@xA->A(x)");
    axioms[12] = parse_string_to_formula("A(x)->?xA");

    axioms[13] = parse_string_to_formula("a=b->a'=b'");
    axioms[14] = parse_string_to_formula("a=b->a=c->b=c");
    axioms[15] = parse_string_to_formula("a'=b'->a=b");
    axioms[16] = parse_string_to_formula("!a'=0");
    axioms[17] = parse_string_to_formula("a+b'=(a+b)'");
    axioms[18] = parse_string_to_formula("a+0=a");
    axioms[19] = parse_string_to_formula("a*0=0");
    axioms[20] = parse_string_to_formula("a*b'=a*b+a");
    axioms[21] = parse_string_to_formula("A(x)&@x(A->A(x))->A");
}

int check_is_axiom(Node *formula) {
    for (int i = 1; i <= 10; i++) {
        if (check_formula_is_similar_to_template(formula, axioms[i])) {
            return i;
        }
    }
    if (check_formula_is_similar_to_template2(formula, axioms[11])) {
        Node *x = get_first_not_bound(formula->r,
                                   formula->l->r,
                                   formula->l->l->s);
                                   //cout << x << "\n";
        if (x) {
            bool isFree = true;
            Node *sub = substitute(formula->l->r,
                                   formula->l->l->s,
                                   x, isFree);
            if (check_equal(sub, formula->r)) {
                if (isFree) {
                    return 11;
                } else {
                    throw SubstituteError(formula->l->r,
                                          formula->l->l->s,
                                          x);
                }
            }
        } else {
            if (check_equal(formula->l->r, formula->r)) return 11;
        }
    }
    if (check_formula_is_similar_to_template2(formula, axioms[12])) {
        Node *x = get_first_not_bound(formula->l,
                                   formula->r->r,
                                   formula->r->l->s);
        if (x) {
            bool isFree = true;
            Node *sub = substitute(formula->r->r,
                                   formula->r->l->s,
                                   x, isFree);
            if (check_equal(sub, formula->l)) {
                if (isFree) {
                    return 12;
                } else {
                    throw SubstituteError(formula->r->r,
                                          formula->r->l->s,
                                          x);
                }
            }
        } else {
            if (check_equal(formula->r->r, formula->l)) return 12;
        }
    }

    for (int i = 13; i <= 20; i++) {
        //if (check_formula_is_similar_to_template(formula, axioms[i], false)) {
        if (check_equal(formula, axioms[i])) {
            return i;
        }
    }
    if (check_formula_is_similar_to_template2(formula, axioms[21])) {
        if (check_equal(formula->r, formula->l->r->r->l)) {
            const std::string &x = formula->l->r->l->s;
            bool isFree = true;
            Node *sub0 = substitute(formula->r, x, new Node("0", NULL, NULL), isFree);
            if (check_equal(sub0, formula->l->l)) {
                Node *subx = substitute(formula->r, x, new Node("\'", new Node(x, NULL, NULL), NULL), isFree);
                if (check_equal(subx, formula->l->r->r->r)) {
                    return 21;
                }
            }
        }
    }

    return -1;
}

bool check_forall_rule(Node *v, const std::vector<Node*> &formulas) {
    if (v->s == "->" && v->r->s == "@") {
        Node *toFind = new Node("->", v->l, v->r->r);
       /* if (check_is_not_free(v->l, v->r->l->s)) {
            for (Node *formula : formulas) {
                if (check_equal(toFind, formula)) {
                    return true;
                }
            }
        } else {
            throw VariableFreeError(v->l, v->r->l->s);
        }*/
        for (Node *formula : formulas) {
            if (check_equal(toFind, formula)) {
                if (check_is_not_free(v->l, v->r->l->s)) {
                    return true;
                } else {
                    throw VariableFreeError(v->l, v->r->l->s);
                }
            }
        }
    }
    return false;
}

bool check_exists_rule(Node *v, const std::vector<Node*> &formulas) {
    if (v->s == "->" && v->l->s == "?") {
        Node *toFind = new Node("->", v->l->r, v->r);
        /*if (check_is_not_free(v->r, v->l->l->s)) {
            for (Node *formula : formulas) {
                if (check_equal(toFind, formula)) {
                    return true;
                }
            }
        } else {
            throw VariableFreeError(v->r, v->l->l->s);
        }*/
        for (int i = 0; i < formulas.size(); i++) {
            Node *formula = formulas[i];
            if (check_equal(toFind, formula)) {
                //if (count==228)cout << formula->get_as_string() << "\n" << toFind->get_as_string() << "\n" << i + 2 << "\n";
                if (check_is_not_free(v->r, v->l->l->s)) {
                    return true;
                } else {
                    throw VariableFreeError(v->r, v->l->l->s);
                }
            }
        }
    }
    return false;
}

bool parse_title(const std::string &ss, std::vector<Node*> &assumptions, Node *&alpha, Node *&betta) {
    const std::string s = get_string_without_spaces(ss);
    for (int i = 0; i < s.length() - 1; i++) {
        if (s[i] == '|' && s[i+1] == '-') {
            int ptr = i + 2;
            betta = parse_expr(s, ptr);
            if (i == 0) return true;
            const std::string t = s.substr(0, i);
            ptr = 0;
            while (ptr < t.length()) {
                Node *expr = parse_expr(t, ptr);
                if (ptr < t.length() && t[ptr] != ',') throw "bad assumptions list";
                if (ptr < t.length()) {
                    assumptions.push_back(expr);
                } else {
                    alpha = expr;
                }
                ptr++;
            }

            return true;
        }
    }
    return false;
}

bool check_is_assumption(Node *formula, const std::vector<Node*> &assumptions) {
    for (Node *suppose : assumptions) {
        if (check_equal(suppose, formula)) {
            return true;
        }
    }
    return false;
}

Node *check_MP(Node *formula, const std::vector<Node*> &formulas) {
    for (Node *vf : formulas) {
        if (vf->s == "->" && check_equal(vf->r, formula)) {
            for (Node *v : formulas) {
                if (check_equal(v, vf->l)) {
                    return v;
                }
            }
        }
    }
    return NULL;
}

bool check_var_is_free_in_formula(const std::string &a, Node *v, bool isFree = true) {
    if (!v) {
        return false;
    }
    if (v->is_variable()) {
        if (v->s == a) {
            return isFree;
        } else {
            return false;
        }
    }
    for (Node *term : v->terms) {
        if (check_var_is_free_in_formula(a, term, isFree)) {
            return true;
        }
    }
    if (v->s == "@" || v->s == "?") {
        return check_var_is_free_in_formula(a, v->r, (v->l->s == a ? false : true) & isFree);
    }
    if (check_var_is_free_in_formula(a, v->l, isFree) || check_var_is_free_in_formula(a, v->r, isFree)) {
        return true;
    }
    return false;
}

Node *get_axiom(int number, Node *a = NULL, Node *b = NULL, Node *c = NULL) {
    return get_formula_from_template(axioms[number], a, b, c);
}

void getAA(Node *a, std::vector<Node*> &proof) {
    proof.push_back(get_axiom(1, a, a));
    proof.push_back(get_axiom(1, a, new Node("->", a, a)));
    proof.push_back(get_axiom(2, a, new Node("->", a, a), a));
    proof.push_back(proof.back()->r);
    proof.push_back(proof.back()->r);
}

void simple_deduction(
        const std::vector<Node*> &formulas,
        const std::vector<Node*> &assumptions,
        Node *alpha,
        Node *betta,
        std::vector<Node*> &proof,
        int supBegin_ = 0, int supEnd_ = -1,
        int forBegin_ = 0, int forEnd_ = -1) {
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
        if (axiomNumber != -1 || check_is_assumption(expr, assumptions)) {
            // di
            proof.push_back(expr);
            // di -> (a -> di)
            proof.push_back(get_axiom(1, expr, alpha));
            proof.push_back(proof.back()->r);
        } else if (check_equal(expr, alpha)) {
            getAA(alpha, proof);
        } else {
            Node *dj = check_MP(expr, formulas);
            if (dj != NULL) {
                //Node * dk = formulas[mp.second];
                // (a -> dj) -> ((a -> (dj -> di))) -> (a -> di)
                proof.push_back(get_axiom(2, alpha, dj, expr));
                // ((a -> (dj -> di))) -> (a -> di)
                proof.push_back(proof.back()->r);
                // a -> di
                proof.push_back(proof.back()->r);
            } else {
                cout << "OOPS: " << "\n" << expr->get_as_string() << "\n";
                throw "there is an error in proof";
            }
        }
    }
}


int main() {
    int counter = 1;
    Node *formula = NULL;
    // std::ifstream cin("input.txt");
    // std::ofstream cout("output.txt");
    try {
        init();

        std::vector<Node*> assumptions, formulas;
        std::vector<Node*> proof;
        Node *alpha = NULL;
        Node *betta = NULL;
        std::string title;

        getline(std::cin, title);
        bool f = false;
        for (int i = 0; i < title.size() - 1; i++) {
            if (title[i] == '|' && title[i+1] == '-') {
                f = true;
            }
        }
        bool deduction = false;
        if (f) {
            deduction = parse_title(title, assumptions, alpha, betta);
        } else {
            cin.seekg(0, std::ios::beg);
            cin.clear();
        }

        std::string s;

        while (getline(cin, s)) {
            count++;
            //if (count == 224) {
            //    cout << s << "\n";
            //}
            //if (count == 225) {
            //    cout << s << "\n";
            //    break;
            //}
            //continue;
            if (s.length() == 0) continue;
            formula = parse_string_to_formula(s);
//            cout << s << ": ";
            formulas.push_back(formula);
            int axiomNumber = -1;

            axiomNumber = check_is_axiom(formula);
            if (axiomNumber != -1) {
//                cout << "axiom " << axiomNumber << "\n";
                if (axiomNumber == 21 && deduction && alpha != NULL) {
                    if (check_var_is_free_in_formula(formula->l->r->l->s, alpha)) {
                        throw KvantorError("аксиома", formula->l->r->l->s, alpha);
                    }
                }
                if (axiomNumber == 11 && deduction && alpha != NULL) {
                    if (check_var_is_free_in_formula(formula->l->l->s, alpha)) {
                        throw KvantorError("аксиома", formula->l->l->s, alpha);
                    }
                }
                if (axiomNumber == 12 && deduction && alpha != NULL) {
                    if (check_var_is_free_in_formula(formula->r->l->s, alpha)) {
                        throw KvantorError("аксиома", formula->r->l->s, alpha);
                    }
                }
                if (deduction && alpha != NULL) {
                    proof.push_back(formula);
                    proof.push_back(get_axiom(1, formula, alpha));
                    proof.push_back(proof.back()->r);
                }
            } else if (deduction && check_is_assumption(formula, assumptions)) {
//                cout << "suppose" << "\n";
                if (alpha != NULL) {
                    proof.push_back(formula);
                    proof.push_back(get_axiom(1, formula, alpha));
                    proof.push_back(proof.back()->r);
                }
            } else if (deduction && check_equal(formula, alpha)) {
//                cout << "alpha " << "\n";
                getAA(alpha, proof);
            } else if (check_forall_rule(formula, formulas)) {
//                cout << "forall rule" << "\n";
                if (deduction && alpha != NULL) {
                    if (check_var_is_free_in_formula(formula->r->l->s, alpha)) {
                        throw KvantorError("правило", formula->r->l->s, alpha);
                    }
                }
                if (check_var_is_free_in_formula(formula->r->l->s, formula->l)) {
                    throw VariableFreeError(formula->l, formula->r->l->s);
                }
              //  if (deduction) {
              //      for (Node *v : assumptions) {
              //          if (check_var_is_free_in_formula(formula->r->l->s, v)) {
              //              throw VariableFreeError(v, formula->r->l->s);
              //          }
              //      }
              //  }
                if (deduction && alpha != NULL) {
                    std::vector<Node*> tmpassumptions;
                    std::vector<Node*> tmpFormulas;
                    std::vector<Node*> tmpProof;

                    Node *A = alpha;
                    Node *B = formula->l;
                    Node *C = formula->r->r;
                    ////////////////////////////////////////////////////
                    /// A->(B->C), A&B |- C ...
                    tmpassumptions.push_back(new Node("->", A, new Node("->", B, C)));

                    tmpFormulas.push_back(new Node("&", A, B));
                    tmpFormulas.push_back(get_axiom(4, A, B));
                    tmpFormulas.push_back(A);
                    tmpFormulas.push_back(get_axiom(5, A, B));
                    tmpFormulas.push_back(B);
                    tmpFormulas.push_back(tmpassumptions[0]);
                    tmpFormulas.push_back(tmpFormulas.back()->r);
                    tmpFormulas.push_back(tmpFormulas.back()->r);

                    simple_deduction(tmpFormulas, tmpassumptions, tmpFormulas[0], C, proof);
                    /// ... A&B -> C
                    ////////////////////////////////////////////////////
                    /// A&B -> @xC
                    proof.push_back(new Node("->", tmpFormulas[0], formula->r));
                    ////////////////////////////////////////////////////
                    /// A&B->@xC,A,B |- @xC ...
                    tmpassumptions.clear();
                    tmpFormulas.clear();
                    tmpassumptions.push_back(proof.back());
                    tmpassumptions.push_back(A);

                    tmpFormulas.push_back(A);
                    tmpFormulas.push_back(B);
                    tmpFormulas.push_back(get_axiom(3, A, B));
                    tmpFormulas.push_back(tmpFormulas.back()->r);
                    tmpFormulas.push_back(tmpFormulas.back()->r);
                    tmpFormulas.push_back(tmpassumptions[0]);
                    tmpFormulas.push_back(tmpFormulas.back()->r);

                    simple_deduction(tmpFormulas, tmpassumptions, B, formula->r, tmpProof);
                    /// ... A&B->@xC,A |- B->@xC ...
                    tmpassumptions.pop_back();

                    simple_deduction(tmpProof, tmpassumptions, A, tmpProof.back(), proof);
                    /// ... A->B->@xC
                    ////////////////////////////////////////////////////
                }
            } else if (check_exists_rule(formula, formulas)) {
//                cout << "exists rule" << "\n";
                if (deduction && alpha != NULL) {
                    if (check_var_is_free_in_formula(formula->l->l->s, alpha)) {
                        throw KvantorError("правило", formula->l->l->s, alpha);
                    }
                }
                if (check_var_is_free_in_formula(formula->l->l->s, formula->r)) {
                    throw VariableFreeError(formula->r, formula->l->l->s);
                }
             //   if (deduction) {
             //       for (Node *v : assumptions) {
             //           if (check_var_is_free_in_formula(formula->l->l->s, v)) {
             //               throw VariableFreeError(v, formula->l->l->s);
             //           }
             //       }
             //   }
                if (deduction && alpha != NULL) {
                    Node *A = alpha;
                    Node *B = formula->l->r;
                    Node *C = formula->r;
                    std::vector<Node*> tmpassumptions;
                    std::vector<Node*> tmpFormulas;
                    std::vector<Node*> tmpProof;

                    /// A->B->C |- B->A->C
                    /// A->B->C, B, A |- C ...
                    tmpassumptions.push_back(new Node("->", A, new Node("->", B, C)));
                    tmpassumptions.push_back(B);

                    tmpFormulas.push_back(A);
                    tmpFormulas.push_back(B);
                    tmpFormulas.push_back(tmpassumptions[0]);
                    tmpFormulas.push_back(tmpFormulas.back()->r);
                    tmpFormulas.push_back(tmpFormulas.back()->r);

                    simple_deduction(tmpFormulas, tmpassumptions, A, C, tmpProof);
                    /// ... A->B->C, B |- A->C
                    tmpassumptions.pop_back();

                    simple_deduction(tmpProof, tmpassumptions, B, new Node("->", A, C), proof);
                    /// ... A->B->C |- B->(A->C)

                    /// ?xB->(A->C)
                    proof.push_back(new Node("->", formula->l, new Node("->", A, C)));
                    ////////////////////////////////////////////////////
                    /// ?xB->(A->C) |- A->(?xB->C)
                    /// ?xB->(A->C), A, ?xB |- C ...
                    tmpassumptions.clear();
                    tmpFormulas.clear();
                    tmpassumptions.push_back(proof.back());
                    tmpassumptions.push_back(A);

                    tmpFormulas.push_back(A);
                    tmpFormulas.push_back(tmpassumptions[0]->l);
                    tmpFormulas.push_back(tmpassumptions[0]);
                    tmpFormulas.push_back(tmpFormulas.back()->r);
                    tmpFormulas.push_back(tmpFormulas.back()->r);

                    simple_deduction(tmpFormulas, tmpassumptions, tmpassumptions[0]->l, C, tmpProof);
                    /// ... ?xB->(A->C), A |- ?xB->C
                    tmpassumptions.pop_back();
                    simple_deduction(tmpProof, tmpassumptions, A, formula, proof);
                    /// ... A->(?xB->C)
                    ////////////////////////////////////////////////////
                }
            } else {
                Node *v = check_MP(formula, formulas);
                if (v != NULL) {
//                    cout << "modus ponens" << "\n";
                    if (deduction && alpha != NULL) {
                        proof.push_back(get_axiom(2, alpha, v, formula));
                        proof.push_back(proof.back()->r);
                        proof.push_back(proof.back()->r);
                    }
                } else {
//                    cout << "uknown stuff" << "\n";
                    throw UnknownError();
                }
            }
            if (!deduction || !alpha) {
//                cerr << "?????\n";
                proof.push_back(formula);
            }
            counter++;
        }
        for (Node *formula : proof) {
            cout << formula->get_as_string() << "\n";
        }
    } catch (const SubstituteError &e) {
        cout << "Вывод некорректен начиная с формулы " << counter << ": ";
        cout << "терм " << e.x->get_as_string()
             << " не свободен для подстановки в формулу " << e.y->get_as_string()
             << " вместо переменной " << e.a << ".\n";
    } catch (const VariableFreeError &e) {
        cout << "Вывод некорректен начиная с формулы " << counter << ": ";
        cout << "переменная " << e.a << " входит свободно в формулу " << e.x->get_as_string() << ".\n";
    } catch (const KvantorError &e) {
        cout << "Вывод некорректен начиная с формулы " << counter << ": ";
        cout << "используется " << e.type << " с квантором по переменной " << e.a
             << ", входящей свободно в допущение " << e.x->get_as_string() << ".\n";
    } catch (const UnknownError &e) {
        cout << "Вывод некорректен начиная с формулы " << counter << ".\n";
    } catch (const char *c) {
        cout << c << "\n";
    }

  //  cout << "Finish\n";

    return 0;
}