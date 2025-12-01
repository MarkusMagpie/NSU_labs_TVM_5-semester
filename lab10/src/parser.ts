import { MatchResult, Semantics } from 'ohm-js';
import grammar, { FunnierActionDict } from './funnier.ohm-bundle';
import { AnnotatedModule, Formula, AnnotatedFunctionDef } from './funnier';
import { checkUniqueNames, collectNamesInNode, getFunnyAst } from '@tvm/lab08';
import { ParameterDef, Statement, Predicate, Expr, TrueCond, FalseCond, ParenCond } from '../../lab08/src/funny';

function checkFunctionCalls(module: AnnotatedModule) {
    const functionTable = new Map<string, { params: number, returns: number }>();
    // заполняю таблицу названиями функций, количеством параметров и возвращаемых значений
    for (const func of module.functions) {
        functionTable.set(func.name, { 
            params: func.parameters.length, 
            returns: func.returns.length 
        });
    }

    const builtins = new Map<string, { params: number, returns: number }>([
        ['length', { params: 1, returns: 1 }],
    ]);

    function visitNode(node: any, context: { expectedReturns?: number } = {}) {
        if (!node) return;

        if (node.type === "funccallstmt") {
            const funcCall = node.call;
            const funcName = funcCall.name;
            const argCount = Array.isArray(funcCall.args) ? funcCall.args.length : 0;
            
            const funcInfo = functionTable.get(funcName) ?? builtins.get(funcName);
            if (!funcInfo) {
                throw new Error(`function ${funcName} is not declared`);
            }
    
            const expectedArgCount = funcInfo.params;
            if (argCount !== expectedArgCount) {
                throw new Error();
            }
    
            // для вызова функции как оператора не ожидаю возвращаемых значений
            const returnsCount = funcInfo.returns;
            if (returnsCount !== 0) {
                throw new Error(`function ${funcName} used as statement must return void but returns ${returnsCount} values`);
            }
    
            if (Array.isArray(funcCall.args)) {
                for (const arg of funcCall.args) {
                    visitNode(arg, { expectedReturns: 1 });
                }
            }
            return;
        }

        // если узел вызов функции проверяю число параметров по таблице 
        if (node.type === "funccall") {
            const funcName = node.name;
            const argCount = Array.isArray(node.args) ? node.args.length : 0;
            // console.log(`visitNode: funccall ${funcName} has ${argCount} arguments`);
            
            // const funcInfo = functionTable.get(funcName)!;
            const funcInfo = functionTable.get(funcName) ?? builtins.get(funcName);
            if (!funcInfo) {
                throw new Error(`function ${funcName} is not declared`);
            }

            const expectedArgCount = funcInfo.params;
            if (argCount !== expectedArgCount) {
                throw new Error();
            }

            const returnsCount = funcInfo.returns;
            // const expectedReturns = context.expectedReturns;
            const expectedReturns = (typeof context.expectedReturns === "number") ? context.expectedReturns : 0;
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
        } 
        
        if (node.type === "block") {
            // console.log(`visitNode: block with ${node.stmts.length} statements`);
            if (Array.isArray(node.stmts)) {
                node.stmts.forEach((stmt: any) => visitNode(stmt));
            }
            return;
        } 
        
        if (node.type === "assign") {
            // выражения в правой части присваивания
            // console.log(`visitNode: assign with ${node.exprs.length} expressions`);
            if (Array.isArray(node.exprs)) {
                const targetsReturns = node.targets.length;
                if (Array.isArray(node.exprs)) {
                    node.exprs.forEach((expr: any) => visitNode(expr, { expectedReturns: targetsReturns }));
                }
            }
            return;
        }

        if (node.type === "if") {
            visitNode(node.condition);
            visitNode(node.then);
            visitNode(node.else);
            return;
        }

        if (node.type === "while") {
            visitNode(node.condition);
            visitNode(node.body);
            if (node.invariant) {
                visitNode(node.invariant);
            }
            return;
        }

        if (node.type === "arraccess") {
            visitNode(node.index, { expectedReturns: 1 });
            return;
        }

        if (node.type === "bin") {
            visitNode(node.left, { expectedReturns: 1 });
            visitNode(node.right, { expectedReturns: 1 });
            return;
        }
        
        if (node.type === "unary") {
            visitNode(node.operand, { expectedReturns: 1 });
            return;
        }

        if (node.kind) {
            switch (node.kind) {
                case "comparison":
                    visitNode(node.left, { expectedReturns: 1 });
                    visitNode(node.right, { expectedReturns: 1 });
                    break;
                case "and":
                case "or":
                    visitNode(node.left);
                    visitNode(node.right);
                    break;
                case "not":
                    visitNode(node.condition || node.predicate);
                    break;
                case "paren":
                    visitNode(node.inner);
                    break;
                case "quantifier":
                    visitNode(node.body);
                    break;
                case "formula":
                    // для FormulaRef - аргументы
                    if (Array.isArray(node.parameters)) {
                        node.parameters.forEach((param: any) => visitNode(param, { expectedReturns: 1 }));
                    }
                    break;
                // true/false не требуют проверки
                case "true":
                case "false":
                    break;
                default:
                    console.warn("что за node kind:", node.kind);
            }
            return;
        }

        if (Array.isArray(node)) {
            node.forEach(item => visitNode(item, context));
            return;
        }
    }

    for (const func of module.functions) {
        console.log(`Checking function: ${func.name}`);
        
        visitNode(func.body);
        
        // НОВОЕ: проверка предусловия
        if (func.precondition) {
            console.log(`Checking precondition of ${func.name}`);
            visitNode(func.precondition);
        }
        
        // НОВОЕ: проверка постусловия  
        if (func.postcondition) {
            console.log(`Checking postcondition of ${func.name}`);
            visitNode(func.postcondition);
        }
    }
}

// для получения Predicate из Ohm врапеера или из уже распарсенного объекта
function resolvePredicate(node: any): Predicate | null {
    if (!node) return null;

    // если это уже готовый Predicate
    if (typeof node === "object" && node !== null && typeof (node as any).kind !== "undefined") {
        return node as Predicate;
    }

    // если есть parse() -> попробовать получить результат
    if (typeof node.parse === "function") {
        try {
            const p = node.parse();
            // если parse вернул готовый Predicate 
            if (p && typeof (p as any).kind !== "undefined") {
                return p as Predicate;
            }
            // иначе рекурсивно распаковать результат parse()
            const rec = resolvePredicate(p);
            if (rec) return rec;
        } catch {
            // игнор
        }
    }

    // обычные children (wrapper иногда хранит их здесь)
    if (Array.isArray(node.children) && node.children.length > 0) {
        for (const c of node.children) {
            const r = resolvePredicate(c);
            if (r) return r;
        }
    }

    if (Array.isArray(node)) {
        for (const el of node) {
            const r = resolvePredicate(el);
            if (r) return r;
        }
    }

    return null;
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
                kind: "and",
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
                kind: "and",
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
        // 1
        // const preopt_ast = preopt.parse ? preopt.parse() : null; 
        // 2
        // const preopt_ast = preopt.children.length > 0 
        // ? preopt.children[0].children[1].children.map((x: any) => x.parse())
        // : [];
        // 3
        let preopt_ast: Predicate[] | null = null;
        if (preopt) {
            const resolved = resolvePredicate(preopt);
            if (resolved) preopt_ast = [resolved];
        }

        let arr_return_array: ParameterDef[] = [];
        if (returns_list && returns_list.sourceString && returns_list.sourceString.trim() !== "void") {
            arr_return_array = returns_list.asIteration().children.map(x => x.parse()) as ParameterDef[];
        }

        // Postopt = ("ensures" Predicate ("and" Predicate)*)?        
        let postopt_ast: Predicate[] | null = null;
        if (postopt) {
            const resolved = resolvePredicate(postopt);
            if (resolved) postopt_ast = [resolved];
        }

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