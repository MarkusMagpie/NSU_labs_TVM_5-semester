import { getExprAst } from '../../lab04';
import * as ast from './funny';
import grammar, { FunnyActionDict } from './funny.ohm-bundle';
import { MatchResult, Node, Semantics } from 'ohm-js';

export function checkUniqueNames(items: ast.ParameterDef[] | ast.ParameterDef, kind: string) {
    // новая строка - преобразую одиночный объект в массив
    const itemArray = Array.isArray(items) ? items : [items];
    const nameMap = new Map<string, number>();
    
    itemArray.forEach((item, idx) => {
        if (!item || typeof item.name !== "string") {
            throw new Error("checkUniqueNames: undefined name");
        }
        // console.log(`checking ${kind}: ${item.name} at index ${idx}`);
        if (nameMap.has(item.name)) {
            throw new Error(`redeclaration of ${kind} '${item.name}' at position ${idx}`);
        }
        nameMap.set(item.name, idx);
    });
}

export function collectNamesInNode(node: any, out: Set<string>) {
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
        case "funccallstmt": 
            collectNamesInNode(node.call, out);
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

export const getFunnyAst = {
    ...getExprAst,

    // Module = Function+
    Module(funcs) {
        const functions = funcs.children.map((x: any) => x.parse());
        // const functions = Array.isArray(funcs) ? funcs : [];
        return { type: "module", functions: functions } as ast.Module;
    },
    // Param = variable ":" Type
    Param(name, colon, type: any) {
        let paramName = name.sourceString;
        const typeAst = type.parse();
        const varType = typeAst && typeAst.isArray ? "int[]" : "int";
        return {type: "param", name: paramName, varType: varType} as ast.ParameterDef;
    },
    // ParamList = ListOf<Param, ",">
    ParamList(list) {
        const params = list.asIteration().children.map((c: any) => c.parse());
        checkUniqueNames(params, "parameter");
        return params;
    },
    // ParamListNonEmpty = ListOf<Param, ",">
    ParamListNonEmpty(list) {
        const params = list.asIteration().children.map((c: any) => c.parse());
        checkUniqueNames(params, "parameter");
        return params;
    },
    // Preopt = "requires" Predicate 
    Preopt(requires_str, predicate) {
        return predicate.parse();
    },
    // UsesOpt = "uses" ParamList 
    UsesOpt(uses_str, paramsNode) {
        const params = paramsNode.asIteration().children.map((c: any) => c.parse());
        return params;
    },
    Function(var_name, left_paren, params_opt, right_paren, preopt, returns_str, returns_list, usesopt, statement: any) {
        const func_name = var_name.sourceString;

        const arr_func_parameters = params_opt.asIteration().children.map(x => x.parse() as ast.ParameterDef);

        const preopt_ast = preopt.parse ? preopt : null; // предусловие функции

        const arr_return_array = returns_list.asIteration().children.map(x => x.parse()) as ast.ParameterDef[];
        
        // UsesOpt = ("uses" ParamList)? 
        const arr_locals_array = usesopt.children.length > 0
        ? usesopt.children[0].children[1].asIteration().children.map((x: any) => x.parse()) as ast.ParameterDef[]
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
        const parsedStatement = statement.parse() as ast.Statement;
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

    // Type = "int"    -- int
    Type_int(_int) {
        return { base: "int", isArray: false };
    },

    // Type = "int" "[]"   -- array
    Type_array(_int, _brackets) {
        return { base: "int", isArray: true };
    },



    // STATEMENTS/ОПЕРАТОРЫ
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
    // LValueList = ListOf<LValue, ",">
    LValueList(list) {
        return list.asIteration().children.map((c: any) => c.parse());
    },
    // ExprList = ListOf<Expr, ",">
    ExprList(list) {
        return list.asIteration().children.map((c: any) => c.parse());
    },
    // LValue = variable "[" Expr "]" 
    LValue_array_access(name, leftbracket, expr: any, rightbracket) {
        return { type: "larr", name: name.sourceString, index: expr.parse() } as ast.ArrLValue;
    },
    // LValue = variable 
    LValue_variable(name) {
        return { type: "lvar", name: name.sourceString } as ast.VarLValue;
    },
    // Block = "{" Statement* "}"
    Block(left_brace, statements: any, right_brace) {
        const stmts_list = statements.children.length > 0
        ? statements.children.map((c: any) => c.parse())
        : [];
        return { type: "block", stmts: stmts_list } as ast.BlockStmt;
    },
    // Conditional = "if" "(" Condition ")" Statement ("else" Statement)?
    Conditional(_if, left_paren, condition: any, right_paren, _then: any, _else, _else_statement: any) {
        const condition_parsed = condition.parse();
        let then_parsed = _then.parse();
        let else_statement = _else.children.length > 0 ? _else_statement.children[0].parse() : null;
        return { type: "if", condition: condition_parsed, then: then_parsed, else: else_statement } as ast.ConditionalStmt;
    },
    // While = "while" "(" Condition ")" InvariantOpt? Statement
    While(_while, left_paren, condition: any, right_paren, inv: any, _then: any) {
        const invariant = inv.children.length > 0 ? inv.children[0].parse() : null;
        const condition_parsed = condition.parse();
        const then_parsed = _then.parse();
        return { type: "while", condition: condition_parsed, invariant: invariant, body: then_parsed } as ast.WhileStmt;
    },
    Statement_function_call_statement(funccall: any, semi) {
        const call = funccall.parse();
        return { 
            type: "funccallstmt", 
            call: call 
        } as ast.FunctionCallStmt;
    },
    // InvariantOpt = "invariant" Predicate
    InvariantOpt(_inv, predicate: any) {
        return predicate.parse();
    },



    // ВЫРАЖЕНИЯ/EXPRESSIONS
    // FunctionCall = variable "(" ArgList ")"
    FunctionCall(name, open_paren, arg_list, close_paren) {
        const nameStr = name.sourceString;
        const args = arg_list.children.length > 0 ? arg_list.asIteration().children.map((x: any) => x.parse()) : [];
        return { type: "funccall", name: nameStr, args} as ast.FuncCallExpr;
    },
    // ArgList = ListOf<Expr, ",">
    ArgList(list) {
        const params = list.asIteration().children.map((c: any) => c.parse());
        return params;
    },
    // ArrayAccess = variable "[" Expr "]"
    ArrayAccess(name, left_bracket, expr: any, right_bracket) {
        return { type: "arraccess", name: name.sourceString, index: expr.parse() } as ast.ArrAccessExpr;
    },



    // CONDITIONS+COMPARISONS

    // AndOp<C> = C "and" C
    AndOp(cond1: Node, and, cond2: Node) {
        return { kind: "and", left: cond1.parse(), right: cond2.parse() };
    },
    // OrOp<C> = C "or" C
    OrOp(cond1: Node, or, cond2: Node) {
        return { kind: "or", left: cond1.parse(), right: cond2.parse() };
    },
    // NotOp<C> = "not" C
    NotOp(not, cond: Node) {
        return { kind: "not", condition: cond.parse() };
    },
    // ParenOp<C> = "(" C ")"
    ParenOp(left_paren, cond: Node, right_paren) {
        return { kind: "paren", inner: cond.parse() };
    },

    // ImplyCond = OrCond ("->" ImplyCond)?
    ImplyCond(first, arrows, rest: any) {
        const left = first.parse();

        if (rest && rest.children && rest.children.length > 0) {
            const rightNode = rest.children ? rest.children[0].children[1] : null;
            const right = rightNode.parse();

            // A -> B === (!A) || B
            const notA = { kind: "not", condition: left };
            return { kind: "or", left: notA, right };
        }

        return left;
    },

    // OrCond = AndCond ("or" AndCond)*
    OrCond(first, ors, rest: any) {
        let result = first.parse();

        const items = [];
        if (rest) {
            if (rest.children) {
                items.push(...rest.children);
            }
        }

        for (const item of items) {
            const rightNode = item.children ? item.children[0].children[1] : null;
            const right_parsed = rightNode.parse();
            result = { kind: "or", left: result, right: right_parsed };
        }

        return result;
    },

    // AndCond = NotCond ("and" NotCond)*
    AndCond(first, ands, rest: any) {
        let result = first.parse();

        const items = [];
        if (rest) {
            if (rest.children) {
                items.push(...rest.children);
            } 
        }

        for (const it of items) {
            const andNode = it.children ? it.children[1] : null;
            const right_parsed = andNode.parse();
            result = { kind: "and", left: result, right: right_parsed };
        }
        return result;
    },

    // NotCond = ("not")* AtomCond
    NotCond(nots: any, atom: any) {
        let result = atom.parse();

        const notsArr = [];
        if (nots) {
            if (nots.children) {
                notsArr.push(...nots.children);
            }
        }

        for (let i = 0; i < notsArr.length; ++i) {
            result = { kind: "not", condition: result };
        }

        return result;
    },

    /*
    AtomCond = "true"           -- true
        | "false"               -- false
        | Comparison            -- comparison
        | "(" Condition ")"     -- paren
    */
    AtomCond_true(t) {
        return { kind: "true" } as ast.TrueCond;
    },
    AtomCond_false(f) {
        return { kind: "false" } as ast.FalseCond;
    },
    AtomCond_comparison(arg0) {
        return arg0.parse();
    },
    AtomCond_paren(left_paren, cond: any, right_paren) {
        return { kind: "paren", inner: cond.parse() } as ast.ParenCond;
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
        // const left_parsed = left_expr.children.length > 0 ? left_expr.children[0].parse() : null;
        // const right_parsed = right_expr.children.length > 0 ? right_expr.children[0].parse() : null;
        const left_parsed = left_expr.parse();
        const right_parsed = right_expr.parse();
        return { kind: "comparison", left: left_parsed, op: "==", right: right_parsed } as ast.ComparisonCond;
    },
    Comparison_neq(left_expr: any, neq, right_expr: any) {
        const left_parsed = left_expr.parse();
        const right_parsed = right_expr.parse();
        return { kind: "comparison", left: left_parsed, op: "!=", right: right_parsed } as ast.ComparisonCond;
    },
    Comparison_ge(left_expr: any, ge, right_expr: any) {
        const left_parsed = left_expr.parse();
        const right_parsed = right_expr.parse();
        return { kind: "comparison", left: left_parsed, op: ">=", right: right_parsed } as ast.ComparisonCond;
    },
    Comparison_le(left_expr: any, le, right_expr: any) {
        const left_parsed = left_expr.parse();
        const right_parsed = right_expr.parse();
        return { kind: "comparison", left: left_parsed, op: "<=", right: right_parsed } as ast.ComparisonCond;
    },
    Comparison_gt(left_expr: any, gt, right_expr: any) {
        const left_parsed = left_expr.parse();
        const right_parsed = right_expr.parse();
        return { kind: "comparison", left: left_parsed, op: ">", right: right_parsed } as ast.ComparisonCond;
    },
    Comparison_lt(left_expr: any, lt, right_expr: any) {
        const left_parsed = left_expr.parse();
        const right_parsed = right_expr.parse();
        return { kind: "comparison", left: left_parsed, op: "<", right: right_parsed } as ast.ComparisonCond;
    },



    // ПРЕДИКАТЫ
    // ImplyPred = OrPred ("->" ImplyPred)?
    ImplyPred(first, arrows, rest: any) {
        const left = first.parse();

        if (arrows.sourceString === "->") {
            const right = rest.children[0].children[1].parse();
            console.log("right", right);

            // A -> B === (!A) || B
            const notA = { kind: "not", predicate: left };
            return { kind: "or", left: notA, right };
        }

        return left;
    },

    // OrPred = AndPred ("or" AndPred)*
    OrPred(first, ors, rest: any) {
        let result = first.parse();

        const items = [];
        if (rest) {
            if (rest.children) {
                items.push(...rest.children);
            }
        }

        for (const item of items) {
            const rightNode = item.children ? item.children[0].children[1] : null;
            const right_parsed = rightNode.parse();
            result = { kind: "or", left: result, right: right_parsed };
        }

        return result;
    },

    // AndPred = NotPred ("and" NotPred)*
    AndPred(first, ands, rest: any) {
        let result = first.parse();

        const items = [];
        if (rest) {
            if (rest.children) {
                items.push(...rest.children);
            }
        }

        for (const it of items) {
            const andNode = it.children ? it.children[1] : null;
            const right_parsed = andNode.parse();
            result = { kind: "and", left: result, right: right_parsed };
        }

        return result;
    },

    // NotPred = ("not")* Atom
    NotPred(nots: any, atom: any) {
        let result = atom.parse();

        const notsArr = [];
        if (nots) {
            if (nots.children) {
                notsArr.push(...nots.children);
            }
        }

        for (let i = 0; i < notsArr.length; ++i) {
            result = { kind: "not", predicate: result };
        }

        return result;
    },

    /*
    AtomPred = Quantifier     -- quantifier
        | FormulaRef          -- formula_ref
        | "true"              -- true
        | "false"             -- false
        | Comparison          -- comparison
        | "(" Predicate ")"   -- paren
    */
    AtomPred_quantifier(arg0) {
        return arg0.parse();
    },
    AtomPred_formula_ref(arg0) {
        return arg0.parse();
    },
    AtomPred_true(t) {
        return { kind: "true" };
    },
    AtomPred_false(f) {
        return { kind: "false" };
    },
    AtomPred_comparison(cmp) {
        return cmp.parse();
    },
    AtomPred_paren(left_paren, inner_pred: any, right_paren) {
        return { kind: "paren", inner: inner_pred.parse() };
    },

    /*
    Quantifier = ("forall" | "exists") 
        "(" Param "|" Predicate ")"
    */
    Quantifier(quant, left_paren, param: any, bar, body: any, right_paren) {
        const paramAst = param.parse() as ast.ParameterDef;
        return {
            kind: "quantifier", 
            quant: quant.sourceString, 
            varName: paramAst.name, 
            varType: paramAst.varType, 
            body: body.parse()
        } as ast.Quantifier;
    },
    // FormulaRef = variable "(" ParamList ")"
    FormulaRef(name, open_paren, arg_list, close_paren) {
        const nameStr = name.sourceString;
        const args = arg_list.children.length > 0 
            ? arg_list.children[0].asIteration().children.map((arg: any) => arg.parse())
            : [];
        return { kind: "formula", name: nameStr, parameters: args} as ast.FormulaRef;
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
    const matchResult = grammar.Funny.match(source, "Module");

    if (!matchResult.succeeded()) {
        throw new SyntaxError(matchResult.message);
    }

    const ast_module = semantics(matchResult).parse();
    checkFunctionCalls(ast_module);
    return ast_module;
}