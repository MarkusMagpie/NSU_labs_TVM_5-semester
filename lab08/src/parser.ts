import { getExprAst } from '../../lab04';
import * as ast from './funny';
import grammar, { FunnyActionDict } from './funny.ohm-bundle';
import { MatchResult, Semantics } from 'ohm-js';

function textOf(x: any) {
    if (typeof x === "string") return x;
    if (!x) return "";
    return x.text;
}

export const getFunnyAst = {
    // write rules here
    /*FUNCTIONS*/
    Type_int(arg0) {
        return "int";
    },
    Type_array(arg0, arg1) {
        return "int[]";  
    },



    /*STATEMENTS/ОПЕРАТОРЫ*/
    Assignment_tuple_assignment(ltargertlist: any, equals, rexprlist: any, semi) {
        const targets = ltargertlist;
        const exprs = rexprlist;
        return { type: "assign", targets, exprs } as ast.AssignStmt;
    },
    Assignment_simple_assignment(ltargert: any, equals, rexpr: any, semi) {
        const target = ltargert;
        const expr = rexpr;
        return { type: "assign", targets: [target], exprs: [expr] } as ast.AssignStmt;
    },
    LValueList(first, comma, rest) {
        
    },
    ExprList(arg0, arg1, arg2) {
        
    },
    // LValue = variable "[" Expr "]" 
    LValue_array_access(name, leftbracket, expr: any, rightbracket) {
        return { type: "larr", name: textOf(name), index: expr } as ast.ArrLValue;
    },
    // LValue = variable 
    LValue_variable(name) {
        return { type: "lvar", name: textOf(name) } as ast.VarLValue;
    },
    // Block = "{" Statement* "}"
    Block(left_brace, statements: any, right_brace) {
        const stmts_list = statements ? statements : [];
        return { type: "block", stmts: statements } as ast.BlockStmt;
    },
    // Conditional = "if" "(" Condition ")" Statement ("else" Statement)?
    
    /*
    export interface ConditionalStmt {
        type: "if";
        condition: Expr;
        then: Statement;
        else: Statement | null;
    }
    */
    Conditional(_if, left_paren, condition: any, right_paren, _then_statement: any, _else, else_statement: any) {
        let _else_statement = _else ? else_statement : null;
        return { type: "if", condition: condition, then: _then_statement, else: else_statement } as ast.ConditionalStmt;
    },
    // While = "while" "(" Condition ")" InvariantOpt Statement
    While(_while, left_paren, condition: any, right_paren, inv: any, _then: any) {
        return { type: "while", condition: condition, invariant: inv, body: _then } as ast.WhileStmt;
    },
    // InvariantOpt = "invariant" Predicate
    InvariantOpt(_inv: any, predicate: any) {
        return predicate;
    },



    /*---ВЫРАЖЕНИЯ/EXPRESSIONS---*/
    // FunctionCall = variable "(" ArgList? ")"
    FunctionCall(name, open_paren, arg_list, close_paren) {
        const nameStr = textOf(name);
        const args = arg_list ? arg_list : [];
        return { type: "funccall", name: nameStr, args} as ast.FuncCallExpr;
    },
    // ArgList = Expr ("," Expr)*
    ArgList(first_expr, comma, rest_expr_list) {

    },
    // ArrayAccess = variable "[" Expr "]"
    ArrayAccess(name, left_bracket, expr: any, right_bracket) {
        return { type: "arraccess", name: textOf(name), index: expr } as ast.ArrAccessExpr;
    },



    /*---CONDITIONS+COMPARISONS---*/
    // Condition = "true"
    Condition_true(t) {
        return { kind: "true" } as ast.TrueCond;
    },
    // Condition = "false"
    Condition_false(f) {
        return { kind: "false" } as ast.FalseCond;
    },
    // Condition = Comparison
    Condition_comparison(arg0) {
        
    },
    // Condition = "not" Condition
    Condition_not(not, cond: any) {
        return { kind: "not", condition: cond } as ast.NotCond;
    },
    // Condition = Condition "and" Condition
    Condition_and(cond1: any, and, cond2: any) {
        return { kind: "and", left: cond1, right: cond2 } as ast.AndCond;
    },
    // Condition = Condition "or" Condition
    Condition_or(cond1: any, or, cond2: any) {
        return { kind: "or", left: cond1, right: cond2 } as ast.OrCond;
    },
    // Condition = Condition "->" Condition
    Condition_implies(cond1: any, implies, cond2: any) {
        // return { kind: "implies", left: cond1, right: cond2 } as ast.ImpliesCond;
        
        // A -> B = (!A) or B 
        let cond1_not = { kind: 'not', condition: cond1 as ast.Condition } as ast.NotCond;
        return { kind: 'or', left: cond1_not, right: cond2 } as ast.OrCond;
    },
    // Condition = "(" Condition ")"
    Condition_paren(left_paren, cond: any, right_paren) {
        return { kind: "paren", inner: cond } as ast.ParenCond;
    },

    /*
    Comparison = Expr "==" Expr                 -- eq
        | Expr "!=" Expr                        -- neq
        | Expr ">=" Expr                        -- ge
        | Expr "<=" Expr                        -- le
        | Expr ">"  Expr                        -- gt
        | Expr "<"  Expr                        -- lt
    */
    Comparison_eq(left_expr: any, eq, right_expr: any) {
        return { kind: "comparison", left: left_expr, op: "==", right: right_expr } as ast.ComparisonCond;
    },
    Comparison_neq(left_expr: any, neq, right_expr: any) {
        return { kind: "comparison", left: left_expr, op: "!=", right: right_expr } as ast.ComparisonCond;
    },
    Comparison_ge(left_expr: any, ge, right_expr: any) {
        return { kind: "comparison", left: left_expr, op: ">=", right: right_expr } as ast.ComparisonCond;
    },
    Comparison_le(left_expr: any, le, right_expr: any) {
        return { kind: "comparison", left: left_expr, op: "<=", right: right_expr } as ast.ComparisonCond;
    },
    Comparison_gt(left_expr: any, gt, right_expr: any) {
        return { kind: "comparison", left: left_expr, op: ">", right: right_expr } as ast.ComparisonCond;
    },
    Comparison_lt(left_expr: any, lt, right_expr: any) {
        return { kind: "comparison", left: left_expr, op: "<", right: right_expr } as ast.ComparisonCond;
    },



    /*---ПРЕДИКАТЫ---*/
    /*
    Predicate = Quantifier                      -- quantifier
        | FormulaRef                            -- formula_ref
        | "true"                                -- true
        | "false"                               -- false
        | Comparison                            -- comparison
        | "not" Predicate                       -- not
        | Predicate "and" Predicate             -- and
        | Predicate "or" Predicate              -- or
        | "(" Predicate ")"                     -- paren
    */
    Predicate_quantifier(arg0) {
        return arg0;
    },
    Predicate_formula_ref(arg0) {
        return arg0;
    },
    // ниже - копия из Condition
    Predicate_true(t) {
        return { kind: "true" } as ast.TrueCond;
    },
    Predicate_false(f) {
        return { kind: "false" } as ast.FalseCond;
    },
    Predicate_comparison(cmp) {
        return cmp;
    },
    Predicate_not(not, pred: any) {
        return { kind: "not", condition: pred } as ast.NotCond;
    },
    Predicate_and(pred1: any, and, pred2: any) {
        return { kind: "and", left: pred1, right: pred2 } as ast.AndCond;
    },
    Predicate_or(pred1: any, or, pred2: any) {
        return { kind: "or", left: pred1, right: pred2 } as ast.OrCond;
    },
    Predicate_paren(left_paren, inner_pred: any, right_paren) {
        return { kind: "paren", inner: inner_pred } as ast.ParenCond;
    },
    /*
    Quantifier = ("forall" | "exists") 
        "(" variable ":" Type "|" Predicate ")"
    */
    Quantifier(quant, left_paren, var_name, colon, var_type: any, bar, predicate: any, right_paren) {
        return {kind: "quantifier", quant: textOf(quant), 
            varName: textOf(var_name), 
            varType: var_type, 
            body: predicate  
        } as ast.Quantifier;
    },
    // FormulaRef = variable "(" ArgList? ")"
    FormulaRef(name, open_paren, arg_list, close_paren) {
        const nameStr = textOf(name);
        const args = arg_list ? arg_list : [];
        return { kind: "formula", name: nameStr, args} as ast.FormulaRef;
    }
} satisfies FunnyActionDict<any>;

export const semantics: FunnySemanticsExt = grammar.Funny.createSemantics() as FunnySemanticsExt;
semantics.addOperation("parse()", getFunnyAst);
export interface FunnySemanticsExt extends Semantics
{
    (match: MatchResult): FunnyActionsExt
}
interface FunnyActionsExt 
{
    parse(): ast.Module;
}

export function parseFunny(source: string): ast.Module
{
    throw "Not implemented";
}