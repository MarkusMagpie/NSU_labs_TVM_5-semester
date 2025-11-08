import { Module, ParameterDef, Predicate, FunctionDef, Statement, Condition, Expr } from 'lab08/src';


export interface AnnotatedModule extends Module {
    formulas: Formula[];
    functions: AnnotatedFunctionDef[];
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

// + интерфейс для расширенного оператора while
export interface AnnotatedWhileStmt {
    type: "while";
    condition: Condition;
    invariant: Predicate | null;
    body: Statement;
}

// + обнова Statement чтобы включить AnnotatedWhileStmt
export type AnnotatedStatement = Statement | AnnotatedWhileStmt;