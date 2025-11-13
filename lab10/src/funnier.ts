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
    precondition: Predicate[] | null;
    postcondition: Predicate[] | null;
}