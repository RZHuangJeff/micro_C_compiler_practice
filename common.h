#ifndef COMMON_H
#define COMMON_H

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define derive_from(parent_type) parent_type __parent

typedef enum uc_type_e {
  UC_VOID,
  UC_INT,
  UC_FLOAT,
  UC_BOOL,
  UC_STRING,

  UC_ARRAY = 0x80,
} uc_type_t;

#define uc_type_to_array(type) (type | UC_ARRAY)
#define uc_base_type(type) (type & ~UC_ARRAY)
#define uc_type_is_array(type) (type & UC_ARRAY)
#define uc_top_type(type)                                                      \
  (uc_type_is_array(type) ? UC_ARRAY : uc_base_type(type))
#define uc_array_ele_type(type)                                                \
  (uc_type_is_array(type) ? uc_base_type(type) : UC_VOID)

typedef enum operator_e {
  UC_OR,
  UC_AND,
  UC_NOT,
  UC_ADD,
  UC_SUB,
  UC_MUL,
  UC_QUO,
  UC_REM,
  UC_NEG,
  UC_POS,
  UC_INC,
  UC_DEC,
  UC_EQL,
  UC_NEQ,
  UC_LSS,
  UC_LEQ,
  UC_GTR,
  UC_GEQ,
  UC_ASSIGN,
  UC_ADD_ASSIGN,
  UC_SUB_ASSIGN,
  UC_MUL_ASSIGN,
  UC_QUO_ASSIGN,
  UC_REM_ASSIGN,
  UC_INDEX,
  UC_CONVERT_INT,
  UC_CONVERT_FLOAT,
  UC_CONVERT_BOOL,
  UC_CONVERT_STRING,
} operator_t;

#define is_assignment(op) (op >= UC_ASSIGN && op <= UC_REM_ASSIGN)
#define is_compare(op) (op >= UC_EQL && op <= UC_GEQ)
#define is_printable(op) (op < UC_POS)
#define is_incdec(op) (op == UC_INC || op == UC_DEC)
#define is_convert(op) (op >= UC_CONVERT_INT)

typedef struct operand_s {
  enum {
    UC_LITERAL,
    UC_IDENTIFIER,
    UC_EXPRESSION,
  } type;

  uint32_t line_num;
} operand_t;

#define op_lit(t, ln)                                                          \
  (operand_t) { .type = t, .line_num = ln }

#define to_operand(__ptr) ((operand_t *)__ptr)

typedef struct liter_s {
  derive_from(operand_t);

  uc_type_t type;
  const char *lit_str;
} liter_t;

#define build_liter(t, st, ln)                                                 \
  ({                                                                           \
    liter_t *__ptr = (liter_t *)malloc(sizeof(liter_t));                       \
    if (__ptr)                                                                 \
      *__ptr = (liter_t){                                                      \
          .__parent = op_lit(UC_LITERAL, ln), .type = t, .lit_str = st};       \
    __ptr;                                                                     \
  })

#define to_liter(__ptr) ((liter_t *)__ptr)

typedef struct ident_s {
  derive_from(operand_t);

  const char *id;
} ident_t;

#define build_ident(i, ln)                                                     \
  ({                                                                           \
    ident_t *__ptr = (ident_t *)malloc(sizeof(ident_t));                       \
    if (__ptr)                                                                 \
      *__ptr = (ident_t){.__parent = op_lit(UC_IDENTIFIER, ln), .id = i};      \
    __ptr;                                                                     \
  })

#define to_ident(__ptr) ((ident_t *)__ptr)

typedef struct expr_s {
  derive_from(operand_t);

  operator_t oper;
  operand_t *l_op;
  operand_t *r_op;
} expr_t;

#define build_expr(l, o, r, ln)                                                \
  ({                                                                           \
    expr_t *__ptr = (expr_t *)malloc(sizeof(expr_t));                          \
    if (__ptr)                                                                 \
      *__ptr = (expr_t){.__parent = op_lit(UC_EXPRESSION, ln),                 \
                        .oper = o,                                             \
                        .l_op = l,                                             \
                        .r_op = r};                                            \
    __ptr;                                                                     \
  })

#define to_expr(__ptr) ((expr_t *)__ptr)

typedef struct stmt_s {
  enum {
    UC_DECLARE_STMT,
    UC_ASSIGN_STMT,
    UC_INCDEC_STMT,
    UC_BLOCK_STMT,
    UC_IF_STMT,
    UC_WHILE_STMT,
    UC_FOR_STMT,
    UC_PRINT_STMT,
    UC_EXPR_STMT,
  } type;
  struct stmt_s *next;

  uint32_t line_num;
} stmt_t;

#define stmt_lit(t, ln)                                                        \
  (stmt_t) { .type = t, .next = NULL, .line_num = ln }

#define to_stmt(__ptr) ((stmt_t *)__ptr)

#define stmt_next(__ptr) to_stmt(__ptr)->next

typedef struct decl_stmt_s {
  derive_from(stmt_t);

  uc_type_t type;
  ident_t *ident;
  operand_t *array_size;
  operand_t *init;
} decl_stmt_t;

#define build_decl_stmt(t, i, in, ln)                                          \
  ({                                                                           \
    decl_stmt_t *__ptr = (decl_stmt_t *)malloc(sizeof(decl_stmt_t));           \
    if (__ptr)                                                                 \
      *__ptr = (decl_stmt_t){.__parent = stmt_lit(UC_DECLARE_STMT, ln),        \
                             .type = t,                                        \
                             .ident = i,                                       \
                             .init = in};                                      \
    __ptr;                                                                     \
  })

#define build_decl_array_stmt(t, i, as, ln)                                    \
  ({                                                                           \
    decl_stmt_t *__ptr = (decl_stmt_t *)malloc(sizeof(decl_stmt_t));           \
    if (__ptr)                                                                 \
      *__ptr = (decl_stmt_t){.__parent = stmt_lit(UC_DECLARE_STMT, ln),        \
                             .type = uc_type_to_array(t),                      \
                             .ident = i,                                       \
                             .array_size = as};                                \
    __ptr;                                                                     \
  })

#define to_decl_stmt(__ptr) ((decl_stmt_t *)__ptr)

typedef struct assign_stmt_s {
  derive_from(stmt_t);

  expr_t *assign_expr;
} assign_stmt_t;

#define build_assign_stmt(ae, ln)                                              \
  ({                                                                           \
    assign_stmt_t *__ptr = (assign_stmt_t *)malloc(sizeof(assign_stmt_t));     \
    if (__ptr)                                                                 \
      *__ptr = (assign_stmt_t){.__parent = stmt_lit(UC_ASSIGN_STMT, ln),       \
                               .assign_expr = ae};                             \
    __ptr;                                                                     \
  })

#define to_assign_stmt(__ptr) ((assign_stmt_t *)__ptr)

typedef struct incdec_stmt_s {
  derive_from(stmt_t);

  expr_t *incdec_expr;
} incdec_stmt_t;

#define build_incdec_stmt(ide, ln)                                             \
  ({                                                                           \
    incdec_stmt_t *__ptr = (incdec_stmt_t *)malloc(sizeof(incdec_stmt_t));     \
    if (__ptr)                                                                 \
      *__ptr = (incdec_stmt_t){.__parent = stmt_lit(UC_INCDEC_STMT, ln),       \
                               .incdec_expr = ide};                            \
    __ptr;                                                                     \
  })

#define to_incdec_stmt(__ptr) ((incdec_stmt_t *)__ptr)

typedef struct block_stmt_s {
  derive_from(stmt_t);

  stmt_t *stmt_list;
} block_stmt_t;

#define build_block_stmt(sl, ln)                                               \
  ({                                                                           \
    block_stmt_t *__ptr = (block_stmt_t *)malloc(sizeof(block_stmt_t));        \
    if (__ptr)                                                                 \
      *__ptr = (block_stmt_t){.__parent = stmt_lit(UC_BLOCK_STMT, ln),         \
                              .stmt_list = sl};                                \
    __ptr;                                                                     \
  })

#define to_block_stmt(__ptr) ((block_stmt_t *)__ptr)

typedef struct if_stmt_s {
  derive_from(stmt_t);

  operand_t *cond;
  stmt_t *true_body;
  stmt_t *false_body;
} if_stmt_t;

#define build_if_stmt(c, tb, fb, ln)                                           \
  ({                                                                           \
    if_stmt_t *__ptr = (if_stmt_t *)malloc(sizeof(if_stmt_t));                 \
    if (__ptr)                                                                 \
      *__ptr = (if_stmt_t){.__parent = stmt_lit(UC_IF_STMT, ln),               \
                           .cond = c,                                          \
                           .true_body = tb,                                    \
                           .false_body = fb};                                  \
    __ptr;                                                                     \
  })

#define to_if_stmt(__ptr) ((if_stmt_t *)__ptr)

typedef struct while_stmt_s {
  derive_from(stmt_t);

  operand_t *cond;
  stmt_t *body;
} while_stmt_t;

#define build_while_stmt(c, b, ln)                                             \
  ({                                                                           \
    while_stmt_t *__ptr = (while_stmt_t *)malloc(sizeof(while_stmt_t));        \
    if (__ptr)                                                                 \
      *__ptr = (while_stmt_t){                                                 \
          .__parent = stmt_lit(UC_WHILE_STMT, ln), .cond = c, .body = b};      \
    __ptr;                                                                     \
  })

#define to_while_stmt(__ptr) ((while_stmt_t *)__ptr)

typedef struct for_stmt_s {
  derive_from(stmt_t);

  operand_t *init;
  operand_t *cond;
  operand_t *step;
  stmt_t *body;
} for_stmt_t;

#define build_for_stmt(i, c, s, b, ln)                                         \
  ({                                                                           \
    for_stmt_t *__ptr = (for_stmt_t *)malloc(sizeof(for_stmt_t));              \
    if (__ptr)                                                                 \
      *__ptr = (for_stmt_t){.__parent = stmt_lit(UC_FOR_STMT, ln),             \
                            .init = i,                                         \
                            .cond = c,                                         \
                            .step = s,                                         \
                            .body = b};                                        \
    __ptr;                                                                     \
  })

#define to_for_stmt(__ptr) ((for_stmt_t *)__ptr)

typedef struct print_stmt_s {
  derive_from(stmt_t);

  operand_t *to_print;
} print_stmt_t;

#define build_print_stmt(tp, ln)                                               \
  ({                                                                           \
    print_stmt_t *__ptr = (print_stmt_t *)malloc(sizeof(print_stmt_t));        \
    if (__ptr)                                                                 \
      *__ptr = (print_stmt_t){.__parent = stmt_lit(UC_PRINT_STMT, ln),         \
                              .to_print = tp};                                 \
    __ptr;                                                                     \
  })

#define to_print_stmt(__ptr) ((print_stmt_t *)__ptr)

typedef struct expr_stmt_s {
  derive_from(stmt_t);

  operand_t *to_eval;
} expr_stmt_t;

#define build_expr_stmt(te, ln)                                                \
  ({                                                                           \
    expr_stmt_t *__ptr = (expr_stmt_t *)malloc(sizeof(expr_stmt_t));           \
    if (__ptr)                                                                 \
      *__ptr = (expr_stmt_t){.__parent = stmt_lit(UC_EXPR_STMT, ln),           \
                             .to_eval = te};                                   \
    __ptr;                                                                     \
  })

#define to_expr_stmt(__ptr) ((expr_stmt_t *)__ptr)

#endif /* COMMON_H */