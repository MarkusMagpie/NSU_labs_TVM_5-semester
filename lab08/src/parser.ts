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

    /*---ВЫРАЖЕНИЯ/EXPRESSIONS---*/



    /*---CONDITIONS---*/
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
    Condition_not(arg0, arg1) {
        
    },
    // Condition = Condition "and" Condition
    Condition_and(cond1: any, and, cond2: any) {
        return { kind: "and", left: cond1, right: cond2 } as ast.AndCond;
    },
    // Condition = Condition "or" Condition
    Condition_or(arg0, arg1, arg2) {
        
    },
    // Condition = Condition "implies" Condition
    Condition_implies(arg0, arg1, arg2) {
        
    },
    // Condition = "(" Condition ")"
    Condition_paren(arg0, arg1, arg2) {
        
    },



    /*---ПРЕДИКАТЫ---*/
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