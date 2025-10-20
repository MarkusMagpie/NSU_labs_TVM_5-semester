import { getExprAst } from '../../lab04';
import * as ast from './funny';
import grammar, { FunnyActionDict } from './funny.ohm-bundle';
import { MatchResult, Semantics } from 'ohm-js';

function checkUniqueNames(items: ast.ParameterDef[] | ast.ParameterDef, kind: string) {
    // новая строка - преобразую одиночный объект в массив
    const itemArray = Array.isArray(items) ? items : [items];
    const nameMap = new Map<string, number>();
    
    itemArray.forEach((item, idx) => {
        if (!item || typeof item.name !== "string") {
            throw new Error("checkUniqueNames: undefined name");
        }
        console.log(`checking ${kind}: ${item.name} at index ${idx}`);
        if (nameMap.has(item.name)) {
            throw new Error(`redeclaration of ${kind} '${item.name}' at position ${idx}`);
        }
        nameMap.set(item.name, idx);
    });
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
                console.log(`collectNamesInNode: found lvar ${node.name}`);
                out.add(node.name);
            }
            break;
        case "larr":
            if (typeof node.name === "string") {
                console.log(`collectNamesInNode: found larr ${node.name}`);
                out.add(node.name);
            }
            collectNamesInNode(node.index, out);
            break; 
        case "funccall":
            console.log(`collectNamesInNode: ${node.name} is a function call`);
            if (Array.isArray(node.args)) {
                node.args.forEach((arg: any) => collectNamesInNode(arg, out));
            }
            break;

        // арифметических выражений
        case "var":
            if (typeof node.name === "string") {
                console.log(`collectNamesInNode: found var ${node.name}`);
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

function checkFunctionCalls(module: ast.Module) {
    const functionTable = new Map<string, { paramCount: number, returnCount: number }>();
    // заполняю таблицу названиями функций, количеством параметров и возвращаемых значений
    for (const func of module.functions) {
        functionTable.set(func.name, { 
            paramCount: func.parameters.length, 
            returnCount: func.returns.length 
        });
        console.log(`function ${func.name} has ${func.parameters.length} parameters and returns ${func.returns.length} values`);
    }

    function visitNode(node: any, context: { expectedReturns?: number } = {}) {
        if (!node) return;

        console.log(`visitNode: ${node.type}`);

        // если узел вызов функции проверяю число параметров по таблице 
        if (node.type === "funccall") {
            const funcName = node.name;
            const argCount = node.args.length;
            console.log(`visitNode: funccall ${funcName} has ${argCount} arguments`);

            if (!functionTable.has(funcName)) {
                throw new Error(`function ${funcName} is not declared`);
            }
            
            const funcInfo = functionTable.get(funcName)!;
            const expectedArgCount = funcInfo.paramCount;
            if (argCount !== expectedArgCount) {
                throw new Error(`function ${funcName} expects ${expectedArgCount} arguments, but ${argCount} were given`);
            }

            const actualReturns = funcInfo.returnCount;
            const expectedReturns = context.expectedReturns;
            if (actualReturns !== expectedReturns) {
                throw new Error(`function ${funcName} returns ${actualReturns} values but ${expectedReturns} expected in this context`);
            }
        }

        if (node.type === "block") {
            console.log(`visitNode: block with ${node.stmts.length} statements`);
            if (Array.isArray(node.stmts)) {
                node.stmts.forEach((stmt: any) => visitNode(stmt));
            }
        }
        else if (node.type === "assign") {
            // обходим выражения в правой части присваивания
            console.log(`visitNode: assign with ${node.exprs.length} expressions`);
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

export const getFunnyAst = {
    // write rules here
    ...getExprAst,

    /*FUNCTIONS*/
    // Module = Function+
    Module(funcs) {
        const functions = funcs.children.map((x: any) => x.parse());
        // const functions = Array.isArray(funcs) ? funcs : [];
        return { type: "module", functions: functions } as ast.Module;
    },
    // Param = variable ":" Type
    Param(name, colon, type: any) {
        let paramName = name.sourceString;
        if (!paramName) {
            throw new Error("Param: undefined name");
        }
        return {type: "param", name: paramName} as ast.ParameterDef;
    },
    // ParamList = Param ("," Param)*
    // ParamList(first_param, comma, rest_params) {
    //     // в каждом массиве [", ", Param] беру второй элемент - параметр
        
    //     // 1 версия
    //     // const tail = rest_params.children.map((x: any) => x.parse());
    //     // const params = [first_param, ...tail];
    //     // checkUniqueNames(params, "parameter");
    //     // return params;

    //     // 2 версия
    //     const first_param_parsed = (typeof(first_param.parse) !== "undefined") ? first_param.parse() : first_param;
    //     const tail = rest_params.children.map((x: any) => {
    //         return (typeof(x.parse) !== "undefined") ? x.parse() : x;
    //     });
    //     const params = [first_param_parsed, ...tail];
    //     checkUniqueNames(params, "parameter");
    //     return params;
    // },
    // 3 версия
    // ParamList = ListOf<Param, ",">
    ParamList(list) {
        const params = list.asIteration().children.map((c: any) => c.parse());
        checkUniqueNames(params, "parameter");
        return params;
    },
    
    // ParamListNonEmpty = Param ("," Param)*
    // ParamListNonEmpty(first_param: any, comma, rest_params) {
    //     // const tail = rest_params ? rest_params.map((x: any) => x[1]) : [];
    //     const tail = rest_params.children.map((x: any) => x.parse());
    //     const params = [first_param, ...tail];
    //     checkUniqueNames(params, "return parameter");
    //     return params;
    // },
    // 2 версия
    // ParamListNonEmpty = ListOf<Param, ",">
    ParamListNonEmpty(list) {
        const params = list.asIteration().children.map((c: any) => c.parse());
        checkUniqueNames(params, "parameter");
        return params;
    },
    EmptyListOf() {
        return [];
    },
    NonemptyListOf(first_param: any, comma, rest_params) {
        const tail = rest_params.children.map((x: any) => x.parse());
        const params = [first_param, ...tail];
        checkUniqueNames(params, "parameter");
        return params;
    },
    // для итерационных узлов (*, +)
    // https://ohmjs.org/docs/releases/ohm-js-16.0#default-semantic-actions
    _iter(...children) {
        return children.map((x: any) => x.parse());
    },

    // Preopt = "requires" Predicate 
    Preopt(requires_str, predicate) {
        const output = predicate ? predicate : null;
        return output;
    },
    // UsesOpt = "uses" ParamList 
    // // 1 версия 
    // UsesOpt(uses_str, params) {
    //     // params уже массив из Param
    //     const output = params ? params : [];
    //     return output;
    // },
    // // 2 версия
    UsesOpt(uses_str, paramsNode) {
        // paramsNode может быть CST-узлом или массивом 
        if (!paramsNode) return [];

        // 1 если CST-узел
        if (typeof paramsNode.parse === "function") {
            return paramsNode.parse();
        }

        // 2 если массив
        if (Array.isArray(paramsNode)) {
            return paramsNode.map((p: any) => (typeof p.parse === "function") ? p.parse() : p);
        }
        
        return [];
    },
    Function(var_name, left_paren, params_opt, right_paren, preopt, returns_str, returns_list, usesopt, statement: any) {
        const func_name = var_name.sourceString;

        const arr_func_parameters = params_opt.asIteration().children.map(p=>p.parse() as ast.ParameterDef);

        const preopt_ast = preopt.parse ? preopt : null; // предусловие функции

        // const return_array = returns_list.parse();
        const arr_return_array = returns_list.asIteration().children.map((x: any) => x.parse());
        
        // const locals_array = (usesopt.children.length > 0) ? usesopt.parse() : [];
        const arr_locals_array = usesopt.children.length 
        ? usesopt.children[0].children[1].asIteration().children.map((x: any) => x.parse()) // normalizeParamList(locals_array);
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
        checkUniqueNames(all, "variable");

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
        const parsedStatement = statement.parse();
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
            body: parsedStatement } as ast.FunctionDef;
    },

    Type_int(arg0) {
        return "int";
    },
    Type_array(arg0, arg1) {
        return "int[]";  
    },



    /*STATEMENTS/ОПЕРАТОРЫ*/
    // Assignment = LValueList "=" ExprList ";"
    Assignment_tuple_assignment(ltargertlist: any, equals, rexprlist: any, semi) {
        const targets = ltargertlist.parse();
        const exprs = rexprlist.parse();
        return { type: "assign", targets: targets, exprs: exprs } as ast.AssignStmt;
    },
    // Assignment = LValue "=" Expr ";" 
    Assignment_simple_assignment(ltargert: any, equals, rexpr: any, semi) {
        const target = ltargert.parse();
        const expr = rexpr.parse();
        return { type: "assign", targets: [target], exprs: [expr] } as ast.AssignStmt;
    },
    // LValueList = LValue ("," LValue)*
    // LValueList(first_value, comma, rest_value) {
    //     const tail = rest_value ? rest_value.map((r: any) => r[1]) : [];
    //     return [first_value, ...tail];
    // },
    // 2 версия
    // LValueList = ListOf<LValue, ",">
    LValueList(list) {
        return list.asIteration().children.map((c: any) => c.parse());
    },

    // ExprList = Expr ("," Expr)*
    // ExprList(first_expr, comma, rest_expr) {
    //     const tail = rest_expr ? rest_expr.map((r: any) => r[1]) : [];
    //     // const tail = rest_expr.children.map((r: any) => r.children[1].parse());
    //     return [first_expr, ...tail];
    // },
    // 2 версия
    // ExprList = ListOf<Expr, ",">
    ExprList(list) {
        return list.asIteration().children.map((c: any) => c.parse());
    },

    // LValue = variable "[" Expr "]" 
    LValue_array_access(name, leftbracket, expr: any, rightbracket) {
        return { type: "larr", name: name.sourceString, index: expr } as ast.ArrLValue;
    },
    // LValue = variable 
    LValue_variable(name) {
        return { type: "lvar", name: name.sourceString } as ast.VarLValue;
    },
    // Block = "{" Statement* "}"
    Block(left_brace, statements: any, right_brace) {
        console.log("Block: ", statements);
        // // AST
        // const stmts_list = Array.isArray(statements) ? statements : [statements];
        // // CST
        const stmts_list: ast.Statement[] = statements.children.map((c: any) => c.parse());
        console.log("Block parsed: ", stmts_list);
        return { type: "block", stmts: stmts_list } as ast.BlockStmt;
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
        // const _else_branch = _else.children.length ? _else.children[1].parse() : null;
        return { type: "if", condition: condition, then: _then_statement, else: _else_statement } as ast.ConditionalStmt;
    },
    // While = "while" "(" Condition ")" InvariantOpt? Statement
    While(_while, left_paren, condition: any, right_paren, inv: any, _then: any) {
        const invariant = inv.children.length > 0 ? inv.children[0].parse() : null;
        return { type: "while", condition: condition, invariant: invariant, body: _then } as ast.WhileStmt;
    },
    // InvariantOpt = "invariant" Predicate
    InvariantOpt(_inv: any, predicate: any) {
        return predicate;
    },



    /*---ВЫРАЖЕНИЯ/EXPRESSIONS---*/
    // FunctionCall = variable "(" ArgList? ")"
    FunctionCall(name, open_paren, arg_list, close_paren) {
        const nameStr = name.sourceString;
        // const args = Array.isArray(arg_list) ? arg_list : [arg_list];
        const args = (arg_list && arg_list.parse) ? arg_list.parse() : [];
        return { type: "funccall", name: nameStr, args} as ast.FuncCallExpr;
    },
    // ArgList = ListOf<Expr, ",">
    ArgList(list) {
        const params = list.asIteration().children.map((c: any) => c.parse());
        // checkUniqueNames(params, "parameter");
        return params;
    },
    // ArrayAccess = variable "[" Expr "]"
    ArrayAccess(name, left_bracket, expr: any, right_bracket) {
        return { type: "arraccess", name: name.sourceString, index: expr } as ast.ArrAccessExpr;
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
        // return {kind: "comparison",  } as ast.ComparisonCond;
        return arg0;
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
        return {
            kind: "quantifier", 
            quant: quant.sourceString, 
            varName: var_name.sourceString, 
            varType: var_type, 
            body: predicate  
        } as ast.Quantifier;
    },
    // FormulaRef = variable "(" ArgList? ")"
    FormulaRef(name, open_paren, arg_list, close_paren) {
        const nameStr = name.sourceString;
        const args = arg_list ? arg_list : [];
        // const args = opt(arg_list, []);
        return { kind: "formula", name: nameStr, args} as ast.FormulaRef;
    },
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
    // throw "Not implemented";
    const matchResult = grammar.Funny.match(source, "Module");

    if (!matchResult.succeeded()) {
        throw new SyntaxError(matchResult.message);
    }

    const ast_module = semantics(matchResult).parse();
    checkFunctionCalls(ast_module);
    return ast_module;
}