import * as arith from "../../lab04";

export interface Module
{
    type: "module";
    functions: FunctionDef[]
}
// ФУНКЦИИ И ТИПЫ
export interface FunctionDef
{
    type: "fun";
    name: string;
    parameters: ParameterDef[]; // входные параметры
    returns: ParameterDef[]; // возвращаемые параметры
    locals: ParameterDef[]; // локальные переменные
    body: Statement; // тело функции
}

export interface ParameterDef
{
    type: "param";
    name: string;
    varType: "int" | "int[]"; 
}



// STATEMENTS/ОПЕРАТОРЫ
export type Statement = AssignStmt | BlockStmt | ConditionalStmt | WhileStmt | FunctionCallStmt;

export type LValue = VarLValue | ArrLValue;
export interface VarLValue {
  type: "lvar";
  name: string;
}
export interface ArrLValue {
  type: "larr";
  name: string;
  index: Expr;
}
export interface AssignStmt {
    type: "assign";
    targets: LValue[];
    exprs: Expr[];
}
export interface BlockStmt {
    type: "block";
    stmts: Statement[];
}
export interface ConditionalStmt {
    type: "if";
    condition: Condition;
    then: Statement;
    else: Statement | null;
}
export interface WhileStmt {
    type: "while";
    condition: Condition;
    invariant: Predicate | null;
    body: Statement;
}
export interface FunctionCallStmt {
    type: "funccallstmt";
    call: FuncCallExpr;
}



// ВЫРАЖЕНИЯ/EXPRESSIONS
export type Expr = arith.Expr | FuncCallExpr | ArrAccessExpr;
export interface FuncCallExpr {
    type: "funccall";
    name: string;
    args: Expr[]; // аргументы функции
}
export interface ArrAccessExpr {
    type: "arraccess";
    name: string;
    index: Expr;
}



// CONDITIONS
export type Condition = TrueCond | FalseCond | ComparisonCond | NotCond | AndCond | OrCond | ImpliesCond |  ParenCond;
export interface TrueCond {
    kind: "true";
}
export interface FalseCond {
    kind: "false";
}
export interface ComparisonCond {
    kind: "comparison";
    left: Expr;
    op: "==" | "!=" | ">" | "<" | ">=" | "<=";
    right: Expr;
}
export interface NotCond {
    kind: "not";
    condition: Condition;
}
export interface AndCond {
    kind: "and";
    left: Condition;
    right: Condition;
}
export interface OrCond {
    kind: "or";
    left: Condition;
    right: Condition;
}
export interface ImpliesCond {
    kind: "implies";
    left: Condition;
    right: Condition;
}
export interface ParenCond {
    kind: "paren";
    inner: Condition;   
}



// ПРЕДИКАТЫ
export type Predicate = Quantifier | FormulaRef | FalseCond | TrueCond | ComparisonCond | NotPred | AndPred | OrPred | ParenPred | ImpliesPred;
export interface Quantifier {
    kind: "quantifier";
    quant: "forall" | "exists";
    varName: string;
    varType: "int" | "int[]";
    body: Predicate;
}
export interface FormulaRef {
    kind: "formula";
    name: string;
    parameters: ParameterDef[]; // аргументы ссылки на формулу
}
export interface NotPred {
    kind: "not";
    predicate: Predicate;
}
export interface AndPred {
    kind: "and";
    left: Predicate;
    right: Predicate;
}
export interface OrPred {
    kind: "or";
    left: Predicate;
    right: Predicate;
}
export interface ParenPred {
    kind: "paren";
    inner: Predicate;
}

export interface ImpliesPred {
    kind: "implies";
    left: Predicate;
    right: Predicate;
}