#include <fstream>
#include <iostream>
#include <string>
#include <vector>
#include <map>
#include <set>

#ifndef NODEPARSER_H
#define NODEPARSER_H

const int N = 5000;

int count = 0;
long long prime[N * N];

std::string get_string_without_spaces(const std::string & s) {
    std::string res = "";
    for (unsigned int i = 0; i < s.length(); i++) {
        char c = s[i];
        if (!isspace(c)) res += c;
    }
    return res;
}

struct Node {
    long long hash;
    int vertCnt;
    int ptrCnt;
    bool lastValue;
    std::vector<Node*> terms;
    std::string s;
    Node * l;
    Node * r;
    Node() : vertCnt(0), ptrCnt(0), l(NULL), r(NULL) {}
    Node(std::string s, Node * l, Node * r) : s(s), l(l), r(r) {
        //cout << s << "\n";
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
        for (int i = 0; i < s.length(); i++) {
            hash *= prime[1];
            hash += s[i];
        }
        if (r) {
            hash *= prime[rCnt];
            hash += r->hash;
            r->ptrCnt++;
        }

    }
    Node(std::string s, std::vector<Node*> &terms) : Node(s, NULL, NULL) {
        this->terms = terms;
        hash = terms[0]->hash;
        for (int i = 1; i < terms.size(); i++) {
            hash *= prime[terms[i]->vertCnt];
            hash += terms[i]->hash;
        }
        for (int i = 0; i < s.length(); i++) {
            hash *= prime[1];
            hash += s[i];
        }
    }

    ~Node() {
        if (l && l->ptrCnt == 0) delete l;
        if (r && r->ptrCnt == 0) delete r;
    }

    std::string get_as_string(bool isMain = true) {
        std::string result = "";
        if (!is_variable() && !isMain) {
            result += "(";
        }
        if (s != "@" && s != "?") {
            if (l) {
                result += l->get_as_string(false);
            }
            result += s;
        } else {
            result += s;
            if (l) {
                result += l->get_as_string(false);
            }
        }
        if (r) {
            result += r->get_as_string(false);
        }
        if (terms.size() != 0) {
            result += "(";
            for (int i = 0; i < terms.size() - 1; i++) {
                result += terms[i]->get_as_string() + ",";
            }
            result += terms.back()->get_as_string();
            result += ")";
        }
        if (!is_variable() && !isMain) {
            result += ")";
        }
        return result;
    }    
    
    bool is_variable() {
        if (s.length() > 0 && s[0] >= 'a' && s[0] <= 'z' && terms.size() == 0) {
            return true;
        }
        return false;
    }

    bool is_function() {
        if (s.length() > 0 &&
             (
                (s[0] >= 'a' && s[0] <= 'z' && terms.size() != 0) ||
                    s[0] == '\'' || s[0] == '*' || s[0] == '+' || s[0] == '0'
             )) {
            return true;
        }
        return false;
    }

    bool is_predicate() {
        if (s.length() > 0 && s[0] >= 'A' && s[0] <= 'Z') {
            return true;
        }
        return false;
    }
};
// Node * parse_title();
// Node * parse_expr(const std::string &s, int &ptr);
// Node * parse_disj(const std::string &s, int &ptr);
// Node * parse_conj(const std::string &s, int &ptr);
// Node * parse_unary(const std::string &s, int &ptr);
// void getAA(Node *a, std::vector<Node*> &proof);

Node *parse_expr(const std::string &s, int &ptr);
Node *parse_disj(const std::string &s, int &ptr);
Node *parse_conj(const std::string &s, int &ptr);
Node *parse_unary(const std::string &s, int &ptr);
Node *parse_pred(const std::string &s, int &ptr);
Node *parse_term(const std::string &s, int &ptr);
Node *parse_summ(const std::string &s, int &ptr);
Node *parse_mult(const std::string &s, int &ptr);
Node *parse_low_level_mult(const std::string &s, int &ptr);
void getAA(Node *a, std::vector<Node*> &proof);

Node * parse_low_level_mult(const std::string &s, int &ptr) {
    if (ptr >= s.length()) return NULL;
    char c = s[ptr];
    if (c >= 'a' && c <= 'z') {
        std::string name;
        name += c;
        ptr++;
        while (ptr < s.length() && s[ptr] >= '0' && s[ptr] <= '9') {
            name += s[ptr++];
        }
        if (ptr < s.length() && s[ptr] == '(')  {
            ptr++;
            std::vector<Node*> terms;
            terms.push_back(parse_term(s, ptr));
            while (ptr < s.length() && s[ptr] == ',') {
                ptr++;
                terms.push_back(parse_term(s, ptr));
            }
            if (ptr == s.length() || s[ptr++] != ')') throw ") after function end expected";
            return new Node(name, terms);
        } else {
            return new Node(name, NULL, NULL);
        }
    } else if (c == '(') {
        ptr++;
        Node *res = parse_term(s, ptr);
        if (ptr == s.length() || s[ptr++] != ')') throw ") in parse_mult expected";
        return res;
    } else if (c == '0') {
        ptr++;
        return new Node("0", NULL, NULL);
    }
    throw "Incorrect multiplied";
}

Node * parse_mult(const std::string &s, int &ptr) {
    Node *res = parse_low_level_mult(s, ptr);
    while (ptr < s.length() && s[ptr] == '\'') {
        res = new Node("'", res, NULL);
        ptr++;
    }
    return res;
}

Node * parse_summ(const std::string &s, int &ptr) {
    Node * expr = parse_mult(s, ptr);
    while (ptr < s.length() && s[ptr] == '*') {
        ptr++;
        Node * expr2 = parse_mult(s, ptr);
        expr = new Node("*", expr, expr2);
    }
    return expr;
}

Node * parse_term(const std::string &s, int &ptr) {
    Node * expr = parse_summ(s, ptr);
    while (ptr < s.length() && s[ptr] == '+') {
        ptr++;
        Node * expr2 = parse_summ(s, ptr);
        expr = new Node("+", expr, expr2);
    }
    return expr;
}

Node * parse_pred(const std::string &s, int &ptr) {
    if (ptr >= s.length()) return NULL;
    char c = s[ptr];
    if (c >= 'A' && c <= 'Z') {
        std::string name;
        name += c;
        ptr++;
        while (ptr < s.length() && s[ptr] >= '0' && s[ptr] <= '9') {
            name += s[ptr++];
        }

        if (ptr == s.length() || s[ptr] != '(') {
            return new Node(name, NULL, NULL);
        }
        ptr++;
        std::vector<Node*> terms;
        terms.push_back(parse_term(s, ptr));
        while (ptr < s.length() && s[ptr] == ',') {
            ptr++;
            terms.push_back(parse_term(s, ptr));
        }
        if (ptr == s.length() || s[ptr++] != ')') throw ") after predicate end expected";
        return new Node(name, terms);
    } else {
        Node *term1 = parse_term(s, ptr);
        if (s[ptr++] != '=') throw "= in predicate expected";
        Node *term2 = parse_term(s, ptr);
        return new Node("=", term1, term2);
    }
}

Node *notX(Node *x) {
    return new Node("!", NULL, x);
}

Node *notNotX(Node *x) {
    return notX(notX(x));
}

Node * parse_unary(const std::string &s, int &ptr) {
    if (ptr >= s.length()) return NULL;
    const char c = s[ptr];
    const int fPtr = ptr;

    Node *v1 = NULL;
    try {
        if (c == '@' || c == '?') {
            ptr++;
            if (s[ptr] < 'a' || s[ptr] > 'z') {
                throw std::string("a...z after ") + c + std::string(" expected");
            }
            std::string name;
            name += s[ptr++]; // >= 'a' and <= 'z'
            while (ptr < s.length() && s[ptr] >= '0' && s[ptr] <= '9') {
                name += s[ptr++];
            }
            v1 = new Node(c == '?' ? "?" : "@", new Node(name, NULL, NULL), parse_unary(s, ptr));
        }
    } catch(...) {
        v1 = NULL;
    }
    if (v1) {
        return v1;
    }

    ptr = fPtr;
    try {
        if (c == '!') {
            ptr++;
            Node *expr = parse_unary(s, ptr);
            v1 = notX(expr);
        }
    } catch(...) {
        v1 = NULL;
    }
    if (v1) {
        return v1;
    }

    ptr = fPtr;
    try {
        if (c == '(') {
            ptr++;
            Node * expr = parse_expr(s, ptr);
            if (ptr >= s.length() || s[ptr++] != ')') {
                throw ") doesn't exist";
            }
            return expr;
        }
    } catch(...) {
        v1 = NULL;
    }
    if (v1) {
        return v1;
    }

    ptr = fPtr;
    return parse_pred(s, ptr);

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
    std::string ss = get_string_without_spaces(s);
    return parse_expr(ss, ptr);
}

#endif // NODEPARSER_H