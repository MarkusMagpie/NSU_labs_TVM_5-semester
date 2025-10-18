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
    const reserved = ["if", "else", "while", "for", "returns", "uses", "requires", "invariant"];

    /*
    у каждого узла CST есть свойство _node, которое содержит внутреннее представление узла.
    Свойство ctorName - The name of grammar rule that created the node.
    https://ohmjs.org/docs/api-reference
    */

    if (node._node && node._node.ctorName === 'FunctionCall') {
        // FunctionCall = variable "(" ArgList? ")"
        if (node.children && node.children.length >= 3) {
            const argsNode = node.children[2]; // ArgList
            if (argsNode) collectNamesInNode(argsNode, out);
        }
        return;
    }

    // node - CST-узел, обхожу его детей
    if (node.children && Array.isArray(node.children)) {
        for (const i of node.children) {
            collectNamesInNode(i, out);
        }
    }

    // node - массив AST-узлов, обхожу его
    if (Array.isArray(node)) {
        for (const elem of node) {
            collectNamesInNode(elem, out);
        }
        return;
    }

    // ОБЪЯСНИ НА ЗНАЧЕ ПОЧЕМУ НУЖНО НА ПРИМЕРЕ ТЕСТА undeclareddLocalAccess
    // добавление имен из CST узлов!!! 
    if (typeof node.sourceString === "string") {
        let s = node.sourceString;
        if (/^[A-Za-z_]\w*$/.test(s) && !reserved.includes(s)) {
            out.add(node.sourceString);
        } 
    }

    // AST проверка конкретных узлов

    // if (node.type === "funccall") {
    //     console.log(`collectNamesInNode: ${node.name} is a function call`);
    //     if (Array.isArray(node.args)) {
    //         collectNamesInNode(node.args, out);
    //     }
    //     return;
    // }
    // if (node.type === "lvar") {
    //     if (typeof node.name === "string") {
    //         out.add(node.name);
    //     }
    //     return;
    // }
    // if (node.type === "larr") {
    //     // имя массива добавляю
    //     if (typeof node.name === "string") out.add(node.name);
    //     collectNamesInNode(node.index, out);
    //     return;
    // }
}

function normalizeParamList(x: any): ast.ParameterDef[] {
    if (!x) return [];

    // если уже массив то верну как есть
    if (Array.isArray(x)) {
        // [[p,p]] -> вернуть первый элемент
        if (x.length === 1 && Array.isArray(x[0])) {
            return x[0];
        }

        return x;
    }

    // если единичный параметр
    return [x];
}

// работа с AST -> никаких детей не делаю
function checkFunctionCalls(module: ast.Module) {
    const functionTable = new Map<string, number>();
    // заполняю таблицу названиями функций и количеством их параметров
    for (const func of module.functions) {
        functionTable.set(func.name, func.parameters.length);
    }
    let visitedNodes = new Set();
    

    function visitNode(node: any) {
        if (!node) return;

        if (visitedNodes.has(node)) {
            return;
        }
        visitedNodes.add(node);

        if (Array.isArray(node)) {
            // узел - массив -> обхожу все элементы
            for (const item of node) {
                visitNode(item);
            }
            return;
        }

        // если узел вызов функции проверяю число параметров по таблице 
        if (node._node && node._node.ctorName === 'FunctionCall') {
            const funcName = node.name;
            const argCount = node.args.length;
            if (!functionTable.has(funcName)) {
                throw new Error(`visitNode: function ${funcName} is not declared`);
            }
            const expectedArgCount = functionTable.get(funcName)!;
            if (argCount !== expectedArgCount) {
                throw new Error(`visitNode: ошибкав количесте аргментво`);
            }
        }
    }

    for (const func of module.functions) {
        visitedNodes = new Set();
        visitNode(func.body);   
    }
}

export const getFunnyAst = {
    // write rules here

    /*FUNCTIONS*/
    // Module = Function+
    Module(funcs) {
        const functions = funcs.children.map((x: any) => x.parse());
        // const functions = Array.isArray(funcs) ? funcs : [];
        return { type: "module", functions: functions } as ast.Module;
    },
    // Param = variable ":" Type
    /*
    export interface ParameterDef
    {
        type: "param";
        name: string;
    }
    */
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

    /*
    Function = variable 
        "(" ParamList? ")" 
        Preopt? 
        "returns" ParamListNonEmpty 
        UsesOpt? 
        Statement
    */
    /*
    export interface FunctionDef
    {
        type: "fun";
        name: string;
        parameters: ParameterDef[]; // входные параметры
        returns: ParameterDef[]; // возвращаемые параметры
        locals: ParameterDef[]; // локальные переменные
        body: Statement; // тело функции
    }
    */
    Function(var_name, left_paren, params_opt, right_paren, preopt, returns_str, returns_list, usesopt, statement: any) {
        const func_name = var_name.sourceString;

        const func_parameters = (params_opt.children.length > 0) ? params_opt.parse() : [];
        const arr_func_parameters = normalizeParamList(func_parameters);

        const preopt_ast = preopt ? preopt : null; // предусловие функции

        const return_array = returns_list.parse();
        const arr_return_array = normalizeParamList(return_array);
        
        const locals_array = (usesopt.children.length > 0) ? usesopt.parse() : [];
        const arr_locals_array = normalizeParamList(locals_array);

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
        collectNamesInNode(statement, used_in_body); // заполняю used_in_bidy
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
            body: statement } as ast.FunctionDef;
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
        const targets = ltargertlist;
        const exprs = rexprlist;
        return { type: "assign", targets: targets, exprs: exprs } as ast.AssignStmt;
    },
    // Assignment = LValue "=" Expr ";" 
    Assignment_simple_assignment(ltargert: any, equals, rexpr: any, semi) {
        const target = ltargert;
        const expr = rexpr;
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
        const stmts_list = statements ? statements : [];
        // const stmts_list = statements.children.map((c: any) => c.parse());
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
        const args = Array.isArray(arg_list) ? arg_list : [arg_list];
        return { type: "funccall", name: nameStr, args} as ast.FuncCallExpr;
    },
    // ArgList = Expr ("," Expr)*
    ArgList(first_expr, comma, rest_expr_list) {
        const tail = first_expr ? rest_expr_list.map((r: any) => r[1]) : [];
        return [first_expr, ...tail];
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
    }
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