import { MatchResult, Semantics } from 'ohm-js';
import grammar, { FunnierActionDict } from './funnier.ohm-bundle';
import { AnnotatedModule, Formula, AnnotatedFunctionDef, AnnotatedWhileStmt } from './funnier';
import { getFunnyAst } from '@tvm/lab08';
import { ParameterDef, Statement, Predicate, Expr, TrueCond, FalseCond, ParenCond } from '../../lab08/src/funny';

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

    // Preopt := "requires" Predicate ("and" Predicate)*
    Preopt(_requires, firstPred, _ands, otherPreds) {
        console.log("Preopt");
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
        console.log("Postopt");
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

    // While = "while" "(" Condition ")" InvariantOpt? Statement
    While(_while, _lp, condition, _rp, invariantOpt, body) {
        const invariant = invariantOpt.parse ? invariantOpt.parse() : null;
        return {
            type: "while",
            condition: condition.parse(),
            invariant: invariant,
            body: body.parse()
        } as AnnotatedWhileStmt;
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
        const arr_func_parameters = params_opt.asIteration().children.map(x => x.parse()) as ParameterDef[];

        // Preopt = ("requires" Predicate ("and" Predicate)*)?
        const preopt_ast = preopt.parse ? preopt.parse() : null; 
        // const preopt_ast = preopt.children.length > 0 
        // ? preopt.children[0].children[1].children.map((x: any) => x.parse())
        // : [];
        
        const arr_return_array = returns_list.asIteration().children.map(x => x.parse()) as ParameterDef[];

        // Postopt = ("ensures" Predicate ("and" Predicate)*)?
        const postopt_ast = postopt.ast ? postopt.parse() : null;

        // UsesOpt = ("uses" ParamList)? 
        const arr_locals_array = usesopt.children.length > 0
        ? usesopt.children[0].children[1].asIteration().children.map((x: any) => x.parse()) as ParameterDef[]
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

    // OrPred = AndPred ("or" AndPred)*
    OrPred(first, ors, rest: any) {
        let result = first.parse();

        const items = [];
        if (rest) {
            if (rest.children) {
                items.push(...rest.children);
            } else if (Array.isArray(rest)) {
                items.push(...rest);
            }
        }

        for (const item of items) {
            const rightNode = item.children ? item.children[1] : null;
            const right = rightNode.parse();
            result = { type: "or", left: result, right };
        }
        return result;
    },

    // AndPred = NotPred ("and" NotPred)*
    AndPred(first, ands, rest: any) {
        let result = first.parse();

        // const items = rest 
        // ? rest.asIteration().children 
        // : (rest && rest.children) || [];

        const items = [];
        if (rest) {
            if (rest.children) {
                items.push(...rest.children);
            } else if (Array.isArray(rest)) {
                items.push(...rest);
            }
        }

        for (const it of items) {
            const andNode = it.children ? it.children[1] : null;
            const right = andNode.parse();
            result = { type: "and", left: result, right: right };
        }
        return result;
    },

    // NotPred = ("not")* Atom
    NotPred(nots: any, atom: any) {
        let result = atom.parse();

        // const notsArr = nots 
        //     ? nots.asIteration().children
        //     :(Array.isArray(nots) ? nots : []);

        const notsArr = [];
        if (nots) {
            if (nots.children) {
                notsArr.push(...nots.children);
            } else if (Array.isArray(nots)) {
                notsArr.push(...nots);
            }
        }

        for (let i = 0; i < notsArr.length; ++i) {
            result = { type: "not", predicate: result };
        }

        return result;
    },

    /*
    Atom = Quantifier     -- quantifier
        | FormulaRef      -- formula_ref
        | "true"          -- true
        | "false"         -- false
        | Comparison      -- comparison
        | "(" Predicate ")" -- paren
    */
    Atom_quantifier(arg0) {
        return arg0;
    },
    Atom_formula_ref(arg0) {
        return arg0;
    },
    Atom_true(t) {
        return { kind: "true" } as TrueCond;
    },
    Atom_false(f) {
        return { kind: "false" } as FalseCond;
    },
    Atom_comparison(cmp) {
        return cmp;
    },
    Atom_paren(left_paren, inner_pred: any, right_paren) {
        return { kind: "paren", inner: inner_pred } as ParenCond;
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