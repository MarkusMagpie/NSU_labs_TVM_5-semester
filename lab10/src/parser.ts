import { MatchResult, Semantics } from 'ohm-js';
import grammar, { FunnierActionDict } from './funnier.ohm-bundle';
import { AnnotatedModule, Formula, AnnotatedFunctionDef } from './funnier';
import { getFunnyAst } from '@tvm/lab08';
import { ParameterDef, Statement, Predicate, Expr } from '../../lab08/src/funny';

function checkUniqueNames(items: ParameterDef[] | ParameterDef, kind: string) {
    // новая строка - преобразую одиночный объект в массив
    const itemArray = Array.isArray(items) ? items : [items];
    const nameMap = new Map<string, number>();
    
    const filteredItems = itemArray.filter(item => item && typeof item.name === "string");

    filteredItems.forEach((item, idx) => {
        if (nameMap.has(item.name)) {
            throw new Error(`redeclaration of ${kind} '${item.name}' at position ${idx}`);
        }
        nameMap.set(item.name, idx);
    });
}

function checkUniqueNamesInModule(module: AnnotatedModule) {
    const names = new Set<string>();
    
    // проверка имен в формулах
    for (const formula of module.formulas) {
        if (names.has(formula.name)) {
            throw new Error(`duplicate formula name '${formula.name}'`);
        }
        names.add(formula.name);
    }
    
    // проверка имена функций
    for (const func of module.functions) {
        if (names.has(func.name)) {
            throw new Error(`duplicate function name '${func.name}'`);
        }
        names.add(func.name);
    }
}

function collectNamesInNode(node: any, out: Set<string>) {
    if (!node) return;

    // node - массив AST-узлов, обхожу его
    if (Array.isArray(node)) {
        for (const elem of node) {
            collectNamesInNode(elem, out);
        }
        return;
    }

    // AST проверка конкретных узлов
    switch (node.type) {
        case "block":
            if (Array.isArray(node.stmts)) {
                node.stmts.forEach((stmt: any) => collectNamesInNode(stmt, out));
            }
            break;
        case "assign":
            if (Array.isArray(node.targets)) {
                node.targets.forEach((target: any) => collectNamesInNode(target, out));
            }
            if (Array.isArray(node.exprs)) {
                node.exprs.forEach((expr: any) => collectNamesInNode(expr, out));
            }
            break;
        case "lvar":
            if (typeof node.name === "string") {
                // console.log(`collectNamesInNode: found lvar ${node.name}`);
                out.add(node.name);
            }
            break;
        case "larr":
            if (typeof node.name === "string") {
                // console.log(`collectNamesInNode: found larr ${node.name}`);
                out.add(node.name);
            }
            collectNamesInNode(node.index, out);
            break; 
        case "funccall":
            // console.log(`collectNamesInNode: ${node.name} is a function call`);
            if (Array.isArray(node.args)) {
                node.args.forEach((arg: any) => collectNamesInNode(arg, out));
            }
            break;

        // арифметические выражения
        case "var":
            if (typeof node.name === "string") {
                // console.log(`collectNamesInNode: found var ${node.name}`);
                out.add(node.name);
            }
            break;
        case "bin":
            collectNamesInNode(node.left, out);
            collectNamesInNode(node.right, out);
            break;
        // для атмосферы
        case "num":
            break;
        default:
            if (node.left) collectNamesInNode(node.left, out);
            if (node.right) collectNamesInNode(node.right, out);
            break; 
    }
}

function checkFunctionCalls(module: AnnotatedModule) {
    const functionTable = new Map<string, { params: number, returns: number }>();
    // заполняю таблицу названиями функций, количеством параметров и возвращаемых значений
    for (const func of module.functions) {
        functionTable.set(func.name, { 
            params: func.parameters.length, 
            returns: func.returns.length 
        });
    }

    function visitNode(node: any, context: { expectedReturns?: number } = {}) {
        if (!node) return;

        // если узел вызов функции проверяю число параметров по таблице 
        if (node.type === "funccall") {
            const funcName = node.name;
            const argCount = node.args.length;
            // console.log(`visitNode: funccall ${funcName} has ${argCount} arguments`);

            if (!functionTable.has(funcName)) {
                throw new Error(`function ${funcName} is not declared`);
            }
            
            const funcInfo = functionTable.get(funcName)!;

            const expectedArgCount = funcInfo.params;
            if (argCount !== expectedArgCount) {
                throw new Error();
            }

            const returnsCount = funcInfo.returns;
            const expectedReturns = context.expectedReturns;
            if (returnsCount !== expectedReturns) {
                throw new Error();
            }

            if (Array.isArray(node.args)) {
                for (const arg of node.args) {
                    // если аргумент - вызов функции он должен вернуть ровно 1 значение
                    visitNode(arg, { expectedReturns: 1 });
                }
            }

            return;
        } else if (node.type === "block") {
            // console.log(`visitNode: block with ${node.stmts.length} statements`);
            if (Array.isArray(node.stmts)) {
                node.stmts.forEach((stmt: any) => visitNode(stmt));
            }
        } else if (node.type === "assign") {
            // выражения в правой части присваивания
            // console.log(`visitNode: assign with ${node.exprs.length} expressions`);
            if (Array.isArray(node.exprs)) {
                const targetsReturns = node.targets.length;
                if (Array.isArray(node.exprs)) {
                    node.exprs.forEach((expr: any) => visitNode(expr, { expectedReturns: targetsReturns }));
                }
            }
        }
    }

    for (const func of module.functions) {
        visitNode(func.body);
    }
}



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

    // Postopt = "ensures" Predicate
    Postopt(_ensures, predicate) {
        return predicate.parse();
    },

    /*
    Function := variable 
        "(" ParamList ")" 
        Preopt? 
        "returns" ParamListNonEmpty 
        Postopt?
        UsesOpt? 
        Statement
    */
    Function(var_name, left_paren, params_opt, right_paren, preopt, returns_str, returns_list, postopt, usesopt, statement: any) {
        const func_name = var_name.sourceString;
        const arr_func_parameters = params_opt.parse() as ParameterDef[];
        const preopt_ast = preopt.parse ? preopt.parse() : null; // предусловие функции
        const arr_return_array = returns_list.parse() as ParameterDef[];
        const postopt_ast = postopt.ast ? postopt.parse() : null; // постусловие функции

        // UsesOpt = ("uses" ParamList)? 
        const arr_locals_array = usesopt.children.length > 0
        ? usesopt.children[0].children[1].children.map((x: any) => x.parse()) as ParameterDef[]
        : [];

        if (arr_func_parameters.length !== 0) {
            console.log("checking parameters: ");
            checkUniqueNames(arr_func_parameters, "parameter");
        }
        if (arr_return_array.length !== 0) {
            console.log("checking return values: ");
            checkUniqueNames(arr_return_array, "return value");
        }
        if (arr_locals_array.length !== 0) {
            console.log("checking local variables: ");
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
    // НОВОЕ
    // checkUniqueNamesInModule(ast_module);
    checkFunctionCalls(ast_module);
    return ast_module;
}