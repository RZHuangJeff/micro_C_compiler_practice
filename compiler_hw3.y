/*	Definition section */
%{
    #include <fcntl.h>
    #include <unistd.h>
    #include "common.h" //Extern variables that communicate with lex
    // #define YYDEBUG 1
    // int yydebug = 1;

    extern int yylineno;
    extern int yylex();
    extern FILE *yyin;

    static bool err = false;

    void yyerror (char const *s)
    {
        printf("error:%d: %s\n", yylineno, s);
        err = true;
    }

    typedef struct table_entry_s {
        uc_type_t type;
        unsigned int lineno;
        unsigned int addr;
        const char *id;
    } table_entry_t;

    typedef struct symbol_table_s {
        struct symbol_table_s *upper;
        unsigned int level;
        unsigned int capacity;
        unsigned int index;
        table_entry_t entries[0];
    } symbol_table_t;

    static symbol_table_t *sym_table = NULL;

    static void symbol_table_inc_scope();
    static void symbol_table_dec_scope();
    static unsigned int symbol_table_insert(const char *id, uc_type_t type, unsigned int lineno);
    static uc_type_t symbol_table_look_up(const char *id, unsigned int *addr);

    static stmt_t *stmts = NULL;

    static void eval_stmt(const stmt_t *stmt);
    static uc_type_t eval_operand(const operand_t *op);

    static const char lstype[] = {
        'i', 'i', 'f', 'i', 'a'
    };

    static unsigned int label_cnt = 0;
%}

//%error-verbose

/* Use variable or self-defined structure to represent
 * nonterminal and token type
 */
%union {
    char *str;

    operand_t *oprnd;
    stmt_t *stmt;
    uc_type_t type;
    
    operator_t op;
}

/* Token without return */
%token INT FLOAT BOOL STRING
%token LPAREN RPAREN LBRACK RBRACK LBRAC RBRAC SEMICOLON
%token PRINT IF ELSE WHILE FOR

%token INC DEC
%left OR AND NOT
%left EQL NEQ LSS LEQ GTR GEQ
%left PLUS MINUS MUL QUO REM
%right ASSIGN ADD_ASSIGN SUB_ASSIGN MUL_ASSIGN QUO_ASSIGN REM_ASSIGN

/* Token with return, which need to sepcify type */
%token <str> Identifier INT_LIT FLOAT_LIT BOOL_LIT STRING_LIT

/* Nonterminal with return, which need to sepcify type */
%type <stmt> Stmt StmtList DeclareStmt AssignStmt IncDecStmt Block IfStmt ElseStmt WhileStmt ForStmt PrintStmt ExprStmt
%type <oprnd> Expr Expr_Index Expr_Basic Expr_prec1 Expr_prec2 Expr_prec3 Expr_prec4 Expr_prec5 Expr_prec6 Expr_prec7
%type <oprnd> AssignExpr IncDecExpr SimpleExpr
%type <oprnd> Literal Operand Init
%type <type> Type
%type <op> comp_op add_op mul_op unary_op incdec_op assign_op
/* Yacc will start at this nonterminal */
%start Program

/* Grammar section */
%%

Program
    : StmtList {
        stmts = to_stmt(build_block_stmt($1, 0));
    }
;

StmtList
    : Stmt StmtList {
        $$ = $1;
        stmt_next($$) = $2;
    }
    | {
        $$ = NULL;
    }
;

Stmt 
    : DeclareStmt
    | AssignStmt
    | IncDecStmt
    | Block
    | IfStmt
    | WhileStmt
    | ForStmt
    | PrintStmt
    | ExprStmt
;

DeclareStmt
    : Type Identifier Init SEMICOLON {
        $$ = to_stmt(build_decl_stmt($1, build_ident($2, yylineno), $3, yylineno));
    }
    | Type Identifier LBRACK Expr RBRACK SEMICOLON {
        $$ = to_stmt(build_decl_array_stmt($1, build_ident($2, yylineno), $4, yylineno));
    }
;

Init
    : ASSIGN Expr {
        $$ = $2;
    }
    | {
        $$ = NULL;
    }
;

AssignStmt
    : AssignExpr SEMICOLON {
        $$ = to_stmt(build_assign_stmt(to_expr($1), yylineno));
    }
;

AssignExpr
    : Expr assign_op Expr {
        $$ = to_operand(build_expr($1, $2, $3, yylineno));
    }
;

assign_op
    : ASSIGN {
        $$ = UC_ASSIGN;
    }
    | ADD_ASSIGN {
        $$ = UC_ADD_ASSIGN;
    }
    | SUB_ASSIGN {
        $$ = UC_SUB_ASSIGN;
    }
    | MUL_ASSIGN {
        $$ = UC_MUL_ASSIGN;
    }
    | QUO_ASSIGN {
        $$ = UC_QUO_ASSIGN;
    }
    | REM_ASSIGN {
        $$ = UC_REM_ASSIGN;
    }
;

IncDecStmt
    : IncDecExpr SEMICOLON {
        $$ = to_stmt(build_incdec_stmt(to_expr($1), yylineno));
    }
;

IncDecExpr
    : Expr incdec_op {
        $$ = to_operand(build_expr($1, $2, NULL, yylineno));
    }
;

incdec_op
    : INC {
        $$ = UC_INC;
    }
    | DEC {
        $$ = UC_DEC;
    }
;

Block
    : LBRAC StmtList RBRAC {
        $$ = to_stmt(build_block_stmt($2, yylineno));
    }
;

IfStmt
    : IF LPAREN Expr RPAREN Block ElseStmt {
        $$ = to_stmt(build_if_stmt($3, $5, $6, yylineno));
    }
;

ElseStmt
    : ELSE IfStmt {
        $$ = $2;
    }
    | ELSE Block {
        $$ = $2;
    }
    | {
        $$ = NULL;
    }
;

WhileStmt
    : WHILE LPAREN Expr RPAREN Block {
        $$ = to_stmt(build_while_stmt($3, $5, yylineno));
    }
;

ForStmt
    : FOR LPAREN SimpleExpr SEMICOLON Expr SEMICOLON SimpleExpr RPAREN Block {
        $$ = to_stmt(build_for_stmt($3, $5, $7, $9, yylineno));
    }
;

SimpleExpr
    : AssignExpr
    | IncDecExpr
    | Expr
;

PrintStmt
    : PRINT LPAREN Expr RPAREN SEMICOLON {
        $$ = to_stmt(build_print_stmt($3, yylineno));
    }
;

ExprStmt
    : Expr SEMICOLON {
        $$ = to_stmt(build_expr_stmt($1, yylineno));
    }
;

Expr
    : Expr_prec7
;

Expr_prec7
    : Expr_prec7 OR Expr_prec6 {
        $$ = to_operand(build_expr($1, UC_OR, $3, yylineno));
    }
    | Expr_prec6
;

Expr_prec6
    : Expr_prec6 AND Expr_prec5 {
        $$ = to_operand(build_expr($1, UC_AND, $3, yylineno));
    }
    | Expr_prec5
;

Expr_prec5
    : Expr_prec5 comp_op Expr_prec4 {
        $$ = to_operand(build_expr($1, $2, $3, yylineno));
    }
    | Expr_prec4
;

comp_op
    : EQL {
        $$ = UC_EQL;
    }
    | NEQ {
        $$ = UC_NEQ;
    }
    | LSS {
        $$ = UC_LSS;
    }
    | LEQ {
        $$ = UC_LEQ;
    }
    | GTR {
        $$ = UC_GTR;
    }
    | GEQ {
        $$ = UC_GEQ;
    }
;

Expr_prec4
    : Expr_prec4 add_op Expr_prec3 {
        $$ = to_operand(build_expr($1, $2, $3, yylineno));
    }
    | Expr_prec3
;

add_op
    : PLUS {
        $$ = UC_ADD;
    }
    | MINUS {
        $$ = UC_SUB;
    }
;

Expr_prec3
    : Expr_prec3 mul_op Expr_prec2 {
        $$ = to_operand(build_expr($1, $2, $3, yylineno));
    }
    | Expr_prec2
;

mul_op
    : MUL {
        $$ = UC_MUL;
    }
    | QUO {
        $$ = UC_QUO;
    }
    | REM {
        $$ = UC_REM;
    }
;

Expr_prec2
    : unary_op Expr_prec2 {
        $$ = to_operand(build_expr($2, $1, NULL, yylineno));
    }
    | Expr_prec1
;

unary_op
    : PLUS {
        $$ = UC_POS;
    }
    | MINUS {
        $$ = UC_NEG;
    }
    | NOT {
        $$ = UC_NOT;
    }
;

Expr_prec1
    : LPAREN Type RPAREN Expr_prec1 {
        $$ = to_operand(build_expr($4, $2 + UC_CONVERT_INT - 1, NULL, yylineno));
    }
    | Expr_Index
;

Expr_Index
    : Expr_Index LBRACK Expr RBRACK {
        $$ = to_operand(build_expr($1, UC_INDEX, $3, yylineno));
    }
    | Expr_Basic
;

Expr_Basic
    : Operand
;

Operand
    : Literal
    | Identifier {
        $$ = to_operand(build_ident($1, yylineno));
    }
    | LPAREN Expr RPAREN {
        $$ = $2;
    }
;

Literal
    : INT_LIT {
        $$ = to_operand(build_liter(UC_INT, $1, yylineno));
    }
    | FLOAT_LIT {
        $$ = to_operand(build_liter(UC_FLOAT, $1, yylineno));
    }
    | BOOL_LIT {
        $$ = to_operand(build_liter(UC_BOOL, $1, yylineno));
    }
    | STRING_LIT {
        $$ = to_operand(build_liter(UC_STRING, $1, yylineno));
    }
;

Type
    : INT {
        $$ = UC_INT;
    }
    | FLOAT {
        $$ = UC_FLOAT;
    }
    | BOOL {
        $$ = UC_BOOL;
    }
    | STRING {
        $$ = UC_STRING;
    }
;

%%

/* C code section */
static inline uc_type_t eval_expr(const expr_t *expr);

static inline void print_header();
static inline void print_tail();

int main(int argc, char *argv[])
{
    if (argc == 2) {
        yyin = fopen(argv[1], "r");
    } else {
        yyin = stdin;
    }

    yyparse();
    
    freopen("hw3.j", "w", stdout);
    print_header();

    eval_stmt(stmts);

    print_tail();
    fclose(stdout);
    if (err)
        remove("hw3.j");


    fclose(yyin);

    return 0;
}

static void symbol_table_inc_scope()
{
    unsigned int def_cap = 10;

    symbol_table_t *st =
        (symbol_table_t *) malloc(sizeof(symbol_table_t) + sizeof(table_entry_t) * def_cap);
    if (st) {
        *st = (symbol_table_t) {
            .level = (sym_table ? sym_table->level + 1 : 0),
            .capacity = def_cap,
            .index = 0,
            .upper = sym_table,
        };
        sym_table = st;
    }
}

static void symbol_table_dec_scope()
{
    if (sym_table) {
        symbol_table_t *st = sym_table;
        sym_table = sym_table->upper;
        free(st);
    }
}

static unsigned int symbol_table_insert(const char *id, uc_type_t type, unsigned int lineno)
{
    static unsigned int address = 0;

    if (!sym_table)
        return 0;

    table_entry_t *ents = sym_table->entries;
    for (unsigned int i = 0; i < sym_table->index; i++)
        if (!strcmp(id, ents[i].id)) {
            printf("error:%u: %s redeclared in this block. previous declaration at line %u\n",
                   lineno, id, ents[i].lineno);
            err = true;
            return 0;
        }

    if (sym_table->index == sym_table->capacity) {
        sym_table =
            (symbol_table_t *) realloc(sym_table, sizeof(symbol_table_t) + sizeof(table_entry_t) * (sym_table->capacity += 10));
    }

    sym_table->entries[sym_table->index++] = (table_entry_t) {
        .id = id,
        .type = type,
        .lineno = lineno,
        .addr = address,
    };

    return address++;
    //printf("> Insert {%s} into symbol table (scope level: %u)\n", id, sym_table->level);
}

static uc_type_t symbol_table_look_up(const char *id, unsigned int *addr)
{
    if (!sym_table)
        return false;

    for (symbol_table_t *st = sym_table; st; st = st->upper) {
        table_entry_t *ents = st->entries;
        for (unsigned int i = 0; i < st->index; i++) {
            if (!strcmp(id, ents[i].id)) {
                *addr = ents[i].addr;
                return ents[i].type;
            }
        }
    }

    return UC_VOID;
}

static inline void do_store(const operand_t *op)
{
    static const char *t_str[] = {
        "v",
        "i",
        "f",
        "i",
        "a",
    };

    ident_t *ident;
    uc_type_t type;
    unsigned int addr;
    if (op->type == UC_EXPRESSION) {
        expr_t *expr = to_expr(op);
        if(expr->oper == UC_INDEX) {
            ident = to_ident(expr->l_op);
            type = symbol_table_look_up(ident->id, &addr);
            if (type != UC_VOID)
                printf("aload %u\nswap\n", addr);
            eval_operand(expr->r_op);
            printf("swap\n");
            printf("%sastore\n", t_str[uc_base_type(type)]);
        }
        return;
    } else {
        ident = to_ident(op);
        type = symbol_table_look_up(ident->id, &addr);
        if (type != UC_VOID)
            printf("%sstore %u\n", t_str[type], addr);
    }
}

static inline void eval_decl_stmt(const decl_stmt_t *decl)
{
    if (decl->array_size) {
        eval_operand(decl->array_size);
        printf("newarray %s\n", uc_array_ele_type(decl->type) == UC_INT ? "int" : "float");
    }

    if (decl->init)
        eval_operand(decl->init);
    else if (!uc_type_is_array(decl->type)) {
        static const char *def_value[] = {
            "0",
            "0",
            "0.0",
            "iconst_1",
            "\"\"",
        };
        printf("ldc %s\n", def_value[decl->type]);
    }

    unsigned int addr = symbol_table_insert(decl->ident->id, decl->type, to_stmt(decl)->line_num);
    static const char stype[] = {
        'i', 'i', 'f', 'i', 'a'
    };
    printf("%cstore %u\n", uc_type_is_array(decl->type) ? 'a' : stype[decl->type], addr);
}

static inline void eval_assign_stmt(const assign_stmt_t *assign)
{
    expr_t *expr = assign->assign_expr;
    if (to_operand(expr->l_op)->type == UC_LITERAL ||
        (to_operand(expr->l_op)->type == UC_EXPRESSION &&
         to_expr(expr->l_op)->oper != UC_INDEX))
        return;

    if (expr->oper == UC_ASSIGN) {
        eval_operand(expr->r_op);
    } else {
        operator_t op = expr->oper - UC_ADD_ASSIGN + UC_ADD;
        expr = build_expr(expr->l_op, op, expr->r_op, to_operand(expr)->line_num);
        eval_expr(expr);
    }

    do_store(expr->l_op);
}

static inline void eval_incdec_stmt(const incdec_stmt_t *incdec)
{
    uc_type_t type = eval_operand(incdec->incdec_expr->l_op);
    if (uc_base_type(type) != UC_INT && uc_base_type(type) != UC_FLOAT)
        return;

    const char *one = uc_base_type(type) == UC_INT ? "1" : "1.0";
    const char *t = uc_base_type(type) == UC_INT ? "i" : "f";
    const char *op = incdec->incdec_expr->oper == UC_INC ? "add" : "sub";

    printf("ldc %s\n", one);
    printf("%s%s\n", t, op);
    do_store(incdec->incdec_expr->l_op);
}

static inline void eval_block_stmt(const block_stmt_t *block)
{
    symbol_table_inc_scope();
    eval_stmt(block->stmt_list);
    symbol_table_dec_scope();
}

static inline void eval_if_stmt(const if_stmt_t *ifs)
{
    static const char *type_str[] = {
        "void",
        "int",
        "float",
        "bool",
        "string",
    };

    static const char *if_template =
        "ifeq L_false_%u\n";
    static const char *else_template = 
        "goto L_final_%u\n"
        "L_false_%u:\n";
    static const char *final_template =
        "L_final_%u:\n";

    uc_type_t t = eval_operand(ifs->cond);
    if (t != UC_BOOL)
        printf("error:%u: non-bool (type %s) used as for condition\n",
               ifs->cond->line_num + 1, type_str[t]);

    unsigned int lb0 = label_cnt++;

    printf(if_template, lb0);
    eval_stmt(ifs->true_body);
    printf(else_template, lb0, lb0);
    if (ifs->false_body)
        eval_stmt(ifs->false_body);
    printf(final_template, lb0);
}

static inline void eval_while_stmt(const while_stmt_t *whiles)
{
    static const char *type_str[] = {
        "void",
        "int",
        "float",
        "bool",
        "string",
    };

    static const char *while_template =
        "goto L_cond_%u\n"
        "L_loop_%u:\n";
    static const char *cond_template =
        "L_cond_%u:\n";
    static const char *final_template =
        "ifne L_loop_%u\n";

    unsigned int lb0 = label_cnt++;
    printf(while_template, lb0, lb0);
    eval_stmt(whiles->body);
    printf(cond_template, lb0);
    uc_type_t t = eval_operand(whiles->cond);
    if (t != UC_BOOL) {
        printf("error:%u: non-bool (type %s) used as for condition\n",
               whiles->cond->line_num + 1, type_str[t]);
        err = true;
    }
    printf(final_template, lb0);
}

static inline void eval_for_stmt(const for_stmt_t *fors)
{
    static const char *type_str[] = {
        "void",
        "int",
        "float",
        "bool",
        "string",
    };

    static const char *start_template =
        "goto L_cond_%u\n"
        "L_loop_%u:\n";
    static const char *cond_template =
        "L_cond_%u:\n";
    static const char *final_template =
        "ifne L_loop_%u\n";

    unsigned int lb0 = label_cnt++;

    eval_operand(fors->init);
    printf(start_template, lb0, lb0);
    eval_stmt(fors->body);
    eval_operand(fors->step);
    printf(cond_template, lb0);
    uc_type_t t = eval_operand(fors->cond);
    if (t != UC_BOOL) {
        printf("error:%u: non-bool (type %s) used as for condition\n",
               fors->cond->line_num + 1, type_str[t]);
        err = true;
    }
    printf(final_template, lb0);
}

static inline void eval_print_stmt(const print_stmt_t *print)
{
    uc_type_t type = eval_operand(print->to_print);

    if (uc_base_type(type) == UC_BOOL) {
        static const char *instr =
            "ifne L_cmp_%u\n"
            "ldc \"false\"\n"
            "goto L_cmp_%u\n"
            "L_cmp_%u:\n"
            "ldc \"true\"\n"
            "L_cmp_%u:\n";

            unsigned int lb0 = label_cnt;
            unsigned int lb1 = label_cnt + 1;
            label_cnt += 2;

            printf(instr, lb0, lb1, lb0, lb1);
    }

    printf("getstatic java/lang/System/out Ljava/io/PrintStream;\n");
    printf("swap\n");

    static const char *pt_str[] = {
        "void",
        "I",
        "F",
        "Ljava/lang/String;",
        "Ljava/lang/String;",
    };

    printf("invokevirtual java/io/PrintStream/print(%s)V\n", pt_str[uc_base_type(type)]);
}

static inline void eval_expr_stmt(const expr_stmt_t *expr)
{
    eval_operand(expr->to_eval);
}

static void eval_stmt(const stmt_t *stmt)
{
    if (!stmt)
        return;

    switch (stmt->type) {
        case UC_DECLARE_STMT:
            eval_decl_stmt(to_decl_stmt(stmt));
            break;
        case UC_ASSIGN_STMT:
            eval_assign_stmt(to_assign_stmt(stmt));
            break;
        case UC_INCDEC_STMT:
            eval_incdec_stmt(to_incdec_stmt(stmt));
            break;
        case UC_BLOCK_STMT:
            eval_block_stmt(to_block_stmt(stmt));
            break;
        case UC_IF_STMT:
            eval_if_stmt(to_if_stmt(stmt));
            break;
        case UC_WHILE_STMT:
            eval_while_stmt(to_while_stmt(stmt));
            break;
        case UC_FOR_STMT:
            eval_for_stmt(to_for_stmt(stmt));
            break;
        case UC_PRINT_STMT:
            eval_print_stmt(to_print_stmt(stmt));
            break;
        case UC_EXPR_STMT:
            eval_expr_stmt(to_expr_stmt(stmt));
            break;
        default:
            break;
    }

    if (stmt->next)
        eval_stmt(stmt->next);
}

static inline uc_type_t eval_liter(const liter_t *liter)
{
    if (liter->type == UC_BOOL)
        printf("iconst_%d\n", strncasecmp(liter->lit_str, "true", 4) ? 0 : 1);
    else {
        printf("ldc ");
        switch (liter->type) {
            case UC_INT:
                printf("%ld\n", atol(liter->lit_str));
                break;
            case UC_FLOAT:
                printf("%lf\n", atof(liter->lit_str));
                break;
            case UC_STRING:
                printf("\"%s\"\n", liter->lit_str);
                break;
            default:
                break;
        }
    }

    return liter->type;
}

static inline uc_type_t eval_ident(const ident_t *ident)
{
    uc_type_t type = UC_VOID;
    unsigned int addr;
    if ((type = symbol_table_look_up(ident->id, &addr))){
        static const char ltype[] = {
            'i', 'i', 'f', 'i', 'a'
        };
        printf("%cload %u\n", uc_type_is_array(type) ? 'a' : ltype[type], addr);

    } else
        printf("error:%u: undefined: %s\n", to_operand(ident)->line_num, ident->id);

    return type;
}

static inline uc_type_t expr_check_type_error(operator_t op, uc_type_t tin1, uc_type_t tin2, uint32_t line_num)
{
    uc_type_t t1 = uc_base_type(tin1);
    uc_type_t t2 = uc_base_type(tin2);

    static const char *type_str[] = {
        "void",
        "int",
        "float",
        "bool",
        "string",
    };

    static const char *operator[] = {
        "OR",
        "AND",
        "NOT",
        "EQL",
        "NEQ",
        "LSS",
        "LEQ",
        "GTR",
        "GEQ",
        "ADD",
        "SUB",
        "MUL",
        "QUO",
        "REM",
        "POS",
        "NEG",
        "INC",
        "DEC",
        "ASSIGN",
        "ADD_ASSIGN",
        "SUB_ASSIGN",
        "MUL_ASSIGN",
        "QUO_ASSIGN",
        "REM_ASSIGN",
    };

    switch (op) {
        case UC_OR:
        case UC_AND:
            if (t1 != UC_BOOL || t2 != UC_BOOL) {
                printf("error:%u: invalid operation: (operator %s not defined on %s)\n",
                       line_num, operator[op], type_str[t1 != UC_BOOL ? t1 : t2]);
                break;
            }
            return UC_BOOL;
        case UC_REM:
            if (t1 != UC_INT || t2 != UC_INT) {
                printf("error:%u: invalid operation: (operator %s not defined on %s)\n",
                       line_num, operator[op], type_str[t1 != UC_INT ? t1 : t2]);
                break;
            }
            return UC_INT;
        case UC_EQL:
        case UC_NEQ:
        case UC_LSS:
        case UC_LEQ:
        case UC_GTR:
        case UC_GEQ:
            return UC_BOOL;
        case UC_ADD:
        case UC_SUB:
        case UC_MUL:
        case UC_QUO:
        case UC_ASSIGN:
        case UC_ADD_ASSIGN:
        case UC_SUB_ASSIGN:
        case UC_MUL_ASSIGN:
        case UC_QUO_ASSIGN:
        case UC_REM_ASSIGN:
            if (t1 != UC_VOID && t1 != t2) {
                printf("error:%u: invalid operation: %s (mismatched types %s and %s)\n",
                       line_num, operator[op], type_str[t1], type_str[t2]);
                break;
            }
            return t1;
        case UC_POS:
        case UC_NEG:
        case UC_NOT:
        case UC_INC:
        case UC_DEC:
        case UC_INDEX:
            if (!t1 && t2 != UC_INT)
                break;
            return t1;
        case UC_CONVERT_INT:
        case UC_CONVERT_FLOAT:
        case UC_CONVERT_BOOL:
        case UC_CONVERT_STRING:
            return op - UC_CONVERT_INT + 1;
        default:
            break;
    }

    err = true;
    return UC_VOID;
}

static inline uc_type_t eval_expr(const expr_t *expr)
{
    uc_type_t res_type;
    uc_type_t t1 = UC_VOID, t2 = UC_VOID;

    if (is_assignment(expr->oper)) {
        assign_stmt_t *assign = build_assign_stmt((expr_t*) expr, to_operand(expr)->line_num);
        eval_assign_stmt(assign);
        free(assign);
        return UC_VOID;
    }

    if (is_incdec(expr->oper)) {
        incdec_stmt_t *incdec = build_incdec_stmt((expr_t*) expr, to_operand(expr)->line_num);
        eval_incdec_stmt(incdec);
        free(incdec);
        return UC_VOID;
    }

    if (expr->l_op)
        t1 = eval_operand(expr->l_op);

    if (expr->r_op)
        t2 = eval_operand(expr->r_op);

    res_type = expr_check_type_error(expr->oper, t1, t2, to_operand(expr)->line_num);

    static const char *type[] = {
        "V",
        "i",
        "f",
        "i",
        "S",
    };

    static const char *operator[] = {
        "or",
        "and",
        "xor",
        "add",
        "sub",
        "mul",
        "div",
        "rem",
        "neg",
    };

    if (is_printable(expr->oper)) {
        if (expr->oper == UC_NOT)
            printf("iconst_1\n");

        printf("%s%s\n", type[uc_base_type(res_type)], operator[expr->oper]);
    }
    
    if (is_compare(expr->oper)) {
        static const char *cond[] = {
            "ifeq",
            "ifne",
            "iflt",
            "ifle",
            "ifgt",
            "ifge",
        };

        static const char *template = 
            "%s L_cmp_%u\n"
            "iconst_0\n"
            "goto L_cmp_%u\n"
            "L_cmp_%u:\n"
            "iconst_1\n"
            "L_cmp_%u:\n";
        
        unsigned int lb0 = label_cnt;
        unsigned int lb1 = label_cnt + 1;
        label_cnt += 2;

        printf("%s\n", uc_base_type(t1) == UC_INT ? "isub" : "fcmpl");
        printf(template, cond[expr->oper - UC_EQL], lb0, lb1, lb0, lb1);
    }

    if (is_convert(expr->oper))
        printf("%s2%s\n", type[uc_base_type(t1)], type[uc_base_type(res_type)]);

    if (expr->oper == UC_INDEX)
        printf("%saload\n", type[uc_base_type(res_type)]);

    return res_type;
}

static uc_type_t eval_operand(const operand_t *op)
{
    if (!op)
        return UC_VOID;

    switch (op->type) {
        case UC_LITERAL:
            return eval_liter(to_liter(op));
        case UC_IDENTIFIER:
            return eval_ident(to_ident(op));
        case UC_EXPRESSION:
            return eval_expr(to_expr(op));
        default:
            return UC_VOID;
    }
}

static inline void print_header()
{
    const char *header =
        ".source hw3.j\n"
        ".class public Main\n"
        ".super java/lang/Object\n"
        ".method public static main([Ljava/lang/String;)V\n"
        ".limit stack 100\n"
        ".limit locals 100\n";

    printf("%s\n", header);
}

static inline void print_tail()
{
    const char *tail = 
        "return\n"
        ".end method";

    printf("\n%s", tail);
}