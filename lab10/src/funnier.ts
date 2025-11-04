import { Module, ParameterDef, Predicate, FunctionDef, Statement, Condition, Expr } from 'lab08/src';


export interface AnnotatedModule extends Module {
    formulas: Formula[];
}
  
// Formula = "formula" variable "(" ParamList? ")" "=" Predicate ";"
export interface Formula {
    type: "formula";
    name: string;
    parameters: ParameterDef[];
    body: Predicate;
}
  

export interface AnnotatedFunctionDef extends FunctionDef {
    postcondition: Predicate | null;
}
  
/*
export interface WhileStmt {
    type: "while";
    condition: Condition;
    invariant: Predicate | null;
    body: Statement;
}
*/

// расширенный оператор цикла с + вариантом
export interface AnnotatedWhileStmt {
    type: "while";
    condition: Condition;
    invariant: Predicate | null;
    variant: Expr | null;
    body: Statement;
}
  
// расширил Statement 
export type AnnotatedStatement = Statement | AnnotatedWhileStmt;
