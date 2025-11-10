import { MatchResult, Semantics } from 'ohm-js';
import grammar, { FunnierActionDict } from './funnier.ohm-bundle';
import { AnnotatedModule, Formula, AnnotatedFunctionDef } from './funnier';
import { checkFunctionCalls, checkUniqueNames, collectNamesInNode, getFunnyAst } from '@tvm/lab08';
import { ParameterDef, Statement, Predicate, Expr, TrueCond, FalseCond, ParenCond } from '../../lab08/src/funny';

const getFunnierAst = {
    ...getFunnyAst,

    _iter: (...children) => children,
    // EmptyListOf: (...children) => children,
    EmptyListOf: () => [],
    _terminal: () => null,

    // Module := Formula* Function+
    Module(formulas: any, functions: any){
        const formulasAst = formulas.children.map((x: any) => x.parse());
        const functionsAst = functions.children.map((x: any) => x.parse());
        
        return { 
            type: "module", 
            formulas: formulasAst, 
            functions: functionsAst 
        } as AnnotatedModule;
    },

    // Formula = variable "(" ParamList ")" "=>" Predicate ";"
    Formula(name, _lp, paramsNode, _rp, _arrow, body, _semi) {
        const paramsAst = paramsNode.children.map((c: any) => c.parse());
        
        return {
            type: "formula",
            name: name.sourceString,
            parameters: paramsAst,
            body: body.parse()
        } as Formula;
    },

    // Preopt := "requires" Predicate ("and" Predicate)*
    Preopt(_requires, firstPred, _ands, otherPreds) {
        // console.log("Preopt");
        let conditions = [firstPred.parse()];
        
        if (otherPreds && otherPreds.children && otherPreds.children.length > 0) {
            otherPreds.children.forEach((child: any) => {
                conditions.push(child.parse());
            });
        }

        if (conditions.length === 1) {
            return conditions[0];
        }

        // если conditions.length > 1 строится дерево с оператором "and"
        let result = conditions[0];
        for (let i = 1; i < conditions.length; ++i) {
            result = {
                type: "and",
                left: result,
                right: conditions[i]
            };
        }

        return result;
    },

    // Postopt = "ensures" Predicate ("and" Predicate)*
    Postopt(_ensures, firstPred, _ands, otherPreds) {
        // console.log("Postopt");
        let conditions = [firstPred.parse()];
        
        if (otherPreds && otherPreds.children && otherPreds.children.length > 0) {
            otherPreds.children.forEach((child: any) => {
                conditions.push(child.parse());
            });
        }

        if (conditions.length === 1) {
            return conditions[0];
        }

        // если conditions.length > 1 строится дерево с оператором "and"
        let result = conditions[0];
        for (let i = 1; i < conditions.length; ++i) {
            result = {
                type: "and",
                left: result,
                right: conditions[i]
            };
        }

        return result;
    },

    // InvariantOpt := "invariant" Predicate 
    InvariantOpt(_invariant, firstPred) {
        return firstPred.parse();
    },

    /*
    Function := variable 
        "(" ParamList ")" 
        Preopt? 
        "returns" ("void" | ParamListNonEmpty) 
        Postopt?
        UsesOpt? 
        Statement
    */
    Function(var_name, left_paren, params_opt, right_paren, preopt, returns_str, returns_list, postopt, usesopt, statement: any) {
        const func_name = var_name.sourceString;
        const arr_func_parameters = params_opt.asIteration().children.map(x => x.parse()) as ParameterDef[];

        // Preopt = ("requires" Predicate ("and" Predicate)*)?
        const preopt_ast = preopt.parse ? preopt.parse() : null; 
        // const preopt_ast = preopt.children.length > 0 
        // ? preopt.children[0].children[1].children.map((x: any) => x.parse())
        // : [];

        let arr_return_array: ParameterDef[] = [];
        if (returns_list && returns_list.sourceString && returns_list.sourceString.trim() !== "void") {
            arr_return_array = returns_list.asIteration().children.map(x => x.parse()) as ParameterDef[];
        }

        // Postopt = ("ensures" Predicate ("and" Predicate)*)?
        const postopt_ast = postopt.ast ? postopt.parse() : null;

        // UsesOpt = ("uses" ParamList)? 
        const arr_locals_array = usesopt.children.length > 0
        ? usesopt.children[0].children[1].asIteration().children.map((x: any) => x.parse()) as ParameterDef[]
        : [];

        if (arr_func_parameters.length !== 0) {
            // console.log("checking parameters: ");
            checkUniqueNames(arr_func_parameters, "parameter");
        }
        if (arr_return_array.length !== 0) {
            // console.log("checking return values: ");
            checkUniqueNames(arr_return_array, "return value");
        }
        if (arr_locals_array.length !== 0) {
            // console.log("checking local variables: ");
            checkUniqueNames(arr_locals_array, "local variable");
        }

        const all = [...arr_func_parameters, ...arr_return_array, ...arr_locals_array];
        if (all.length > 0) {
            checkUniqueNames(all, "variable");
        }

        // проверка локальных переменных тела функции
        const declared = new Set<string>();
        for (const i of arr_func_parameters) {
            declared.add(i.name);
        }
        for (const i of arr_return_array) {
            declared.add(i.name);
        }
        for (const i of arr_locals_array) {
            declared.add(i.name);
        }
        const used_in_body = new Set<string>();
        const parsedStatement = statement.parse() as Statement;
        collectNamesInNode(parsedStatement, used_in_body); // заполняю used_in_bidy
        for (const name of used_in_body) {
            if (!declared.has(name)) {
                throw new Error("Function: локальная переменная " + name + " не объявлена");
            }
        }

        return { type: "fun", 
            name: func_name, 
            parameters: arr_func_parameters, 
            returns: arr_return_array, 
            locals: arr_locals_array, 
            precondition: preopt_ast,
            postcondition: postopt_ast,
            body: parsedStatement } as AnnotatedFunctionDef;
        },

    Statement_function_call_statement(func_call, semicolon) {
        return func_call.parse();
    }

} satisfies FunnierActionDict<any>;

export const semantics: FunnySemanticsExt = grammar.Funnier.createSemantics() as FunnySemanticsExt;
semantics.addOperation("parse()", getFunnierAst);
export interface FunnySemanticsExt extends Semantics
{
    (match: MatchResult): FunnyActionsExt
}

interface FunnyActionsExt 
{
    parse(): AnnotatedModule;
}

export function parseFunnier(source: string, origin?: string): AnnotatedModule
{
    const matchResult = grammar.Funnier.match(source, "Module");

    if (!matchResult.succeeded()) {
        throw new SyntaxError(matchResult.message);
    }

    const ast_module = semantics(matchResult).parse();
    checkFunctionCalls(ast_module);
    return ast_module;
}