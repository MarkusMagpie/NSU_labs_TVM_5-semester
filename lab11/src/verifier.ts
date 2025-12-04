import { Arith, ArithSort, Bool, Context, init, Model, SMTArray, SMTArraySort } from "z3-solver";

import { printFuncCall } from "./printFuncCall";
import { AnnotatedModule, AnnotatedFunctionDef, Formula } from "../../lab10";
import { error } from "console";
import { 
    Statement, Expr, Predicate, Condition, ParameterDef, 
    AssignStmt, BlockStmt, ConditionalStmt, WhileStmt, FunctionCallStmt,
    LValue, VarLValue, ArrLValue,
    FuncCallExpr, ArrAccessExpr,
    TrueCond, FalseCond, ComparisonCond, NotCond, AndCond, OrCond, ImpliesCond, ParenCond,
    Quantifier, FormulaRef, NotPred, AndPred, OrPred, ParenPred
} from "../../lab08/src/funny";
import exp from "constants";


let z3anchor;
// async function initZ3()
// {
//     if(!z3)
//     {
//         z3anchor = await init();
//         const Z3C = z3anchor.Context;
//         z3 = Z3C('main');        
//     }
// }

let z3Context: Context | null = null;
async function initZ3() {
    if (!z3Context) {
        const { Context } = await init();
        z3Context = Context('main');
    }
    return z3Context;
}

export function flushZ3()
{
    // z3anchor = undefined;
    z3Context = null;
}

export interface VerificationResult {
    function: string;
    verified: boolean;
    error?: string;
    model?: Model;
}

let z3: Context;

export async function verifyModule(module: AnnotatedModule): Promise<VerificationResult[]>
{
    const results: VerificationResult[] = [];
    let has_failure = false;
    for (const func of module.functions) {
        try {
            // 1 вариант
            // const theorem = buildFunctionVerificationConditions(func, module, z3);
            // const result = await proveTheorem(theorem, z3);

            // 2 вариант
            // условие верификации как Predicate
            const verificationCondition = buildFunctionVerificationConditions(func, module);
            
            // конвертация в Z3 только в конце
            z3 = await initZ3();
            const solver = new z3.Solver(); // НОВОЕ
            const environment = buildEnvironment(func, z3);
            const z3Condition = convertPredicateToZ3(verificationCondition, environment, z3, module, solver);
            const result = await proveTheorem(z3Condition, solver);

            const verified = result.result === "unsat";

            results.push(
                {
                    function: func.name,
                    verified,
                    error: result.result === "sat" ? "теорема неверна, так как найден контрпример. Вернул модель, опровергающую теорему." : undefined,
                    model: result.model
                }
            );

            if (!verified) {
                has_failure = true;
            }
        } catch (error) {
            results.push(
                {
                    function: func.name,
                    verified: false,
                    error: error as string
                }
            );
            has_failure = true;
        }
    }

    if (has_failure) {
        const failedNames = results.filter(r => !r.verified).map(r => r.function).join(", ");
        throw new Error(`Verification failed for: ${failedNames}`);
    }

    return results;
}

async function proveTheorem(
    theorem: Bool,
    solver: any
): Promise<{ result: "sat" | "unsat" | "unknown"; model?: Model }> {
    try {
        console.log("Z3 теорема:", theorem.toString());
    } catch (e) {
        console.log("не удалось получить состояние солвера:", e);
    }
    
    // + отрицание теоремы - если оно отрицательно, то теорема верна
    solver.add(z3.Not(theorem));
    
    const result = await solver.check();
    
    if (result === "sat") {
        return {result: "sat", model: solver.model()};
    } else if (result === "unsat") {
        return {result: "unsat"};
    } else {
        return {result: "unknown"};
    }
}

function buildEnvironment(func: AnnotatedFunctionDef, z3: Context): Map<string, Arith> {
    const environment = new Map<string, Arith>();

    // вложение параметров
    for (const param of func.parameters) {
        if (param.varType === "int") {
            environment.set(param.name, z3.Int.const(param.name));
        } else if (param.varType === "int[]") {
            console.log("int[] не сделал");
            throw new Error("int[] не сделал");
            // environment.set(param.name, z3.Int.const(param.name + "_array"));
        }
    }

    // добавление return values
    for (const ret of func.returns) {
        if (ret.varType === "int") {
            environment.set(ret.name, z3.Int.const(ret.name));
        } else if (ret.varType === "int[]") {
            console.log("int[] не сделал");
            throw new Error("int[] не сделал");
            // environment.set(ret.name, z3.Int.const(ret.name + "_array"));
        }
    }

    // добавление локальных переменных
    for (const local of func.locals) {
        if (local.varType === "int") {
            environment.set(local.name, z3.Int.const(local.name));
        } else if (local.varType === "int[]") {
            console.log("int[] не сделал");
            throw new Error("int[] не сделал");
            // environment.set(local.name, z3.Int.const(local.name + "_array"));
        }
    }

    return environment;
}

/*
export interface ImpliesCond {
    kind: "implies";
    left: Condition;
    right: Condition;
}
*/
function buildFunctionVerificationConditions(
    func: AnnotatedFunctionDef,
    module: AnnotatedModule,
//    z3: Context
): Predicate {
    // 1 вариант
    // // предусловие -> Z3 
    // const precondition = convertPredicatesToZ3(func.precondition, environment, z3);

    // const postcondition = convertPredicatesToZ3(func.postcondition, environment, z3);

    // // weakest precondition для тела функции
    // const wpBody = computeWP(func.body, func.postcondition);

    // // условие верификации: pre -> wp
    // return z3.Implies(precondition, wpBody);

    // 2 вариант
    const precondition = combinePredicates(func.precondition);
    const postcondition = combinePredicates(func.postcondition);

    // weakest precondition для тела функции
    const wpBody = computeWP(func.body, postcondition, module);

    // условие верификации: pre -> wp
    return {
        kind: "implies",
        left: precondition,
        right: wpBody
    } as Predicate;
}

function combinePredicates(predicates: Predicate[] | null): Predicate {
    if (!predicates || predicates.length === 0) {
        return { kind: "true" };
    }
    if (predicates.length === 1) {
        return predicates[0];
    }
    
    // объед предикаты с помощью конъюнкции (and)
    let result: Predicate = predicates[0];
    for (let i = 1; i < predicates.length; i++) {
        result = {
            kind: "and",
            left: result,
            right: predicates[i]
        };
    }
    return result;
}

function computeWP(
    statement: Statement, 
    postcondition: Predicate, 
    // env: Map<string, Arith>, 
    // z3: Context
    module: AnnotatedModule
): Predicate {
    let wp: Predicate;

    switch (statement.type) {
        case "assign": 
            wp = computeWPAssignment(statement as AssignStmt, postcondition);
            break;
        case "block":
            wp = computeWPBlock(statement as BlockStmt, postcondition, module);
            break;
        case "if":
            wp = computeWPIf(statement as ConditionalStmt, postcondition, module);
            break;
        case "while":
            wp = computeWPWhile(statement as WhileStmt, postcondition, module);
            break;
        case "funccallstmt":
            // 1) вызов как оператора rev(a,b,n-2) не возвращает ничего -> не изменяет wp
            // 2) вызов как выражения (в правой части присваивания) - возвращает значение и влияет на weakest precondition через подстановку
            
            // 1) 
            wp = postcondition;
            break;
        default:
            console.log(`неизвестный оператор: ${(statement as any).type}`);
            throw new Error(`неизвестный оператор: ${(statement as any).type}`);
    }

    return simplifyPredicate(wp);
}

function simplifyPredicate(predicate: Predicate): Predicate {
    switch (predicate.kind) {
        case "and":
            const left = simplifyPredicate((predicate as AndPred).left);
            const right = simplifyPredicate((predicate as AndPred).right);
            // true && P => P
            if (left.kind === "true") return right;
            if (right.kind === "true") return left;
            // false && P => false
            if (left.kind === "false" || right.kind === "false") return { kind: "false" };
            
            return { kind: "and", left, right };
        case "or":
            const leftOr = simplifyPredicate((predicate as OrPred).left);
            const rightOr = simplifyPredicate((predicate as OrPred).right);
            // true || P => true
            if (leftOr.kind === "true" || rightOr.kind === "true") 
                return { kind: "true" };
            // false || P => P
            if (leftOr.kind === "false") return rightOr;
            if (rightOr.kind === "false") return leftOr;
            
            return { kind: "or", left: leftOr, right: rightOr };
        case "comparison":
            const comp = predicate as ComparisonCond;
            const leftExpr = simplifyExpr(comp.left);
            const rightExpr = simplifyExpr(comp.right);

            // упрощение числовых сравнений
            if (leftExpr.type === "num" && rightExpr.type === "num") {
                const leftVal = leftExpr.value;
                const rightVal = rightExpr.value;
                let result: boolean;
                switch (comp.op) {
                    case "==": result = leftVal === rightVal; break;
                    case "!=": result = leftVal !== rightVal; break;
                    case ">": result = leftVal > rightVal; break;
                    case "<": result = leftVal < rightVal; break;
                    case ">=": result = leftVal >= rightVal; break;
                    case "<=": result = leftVal <= rightVal; break;
                    default: return { ...comp, left: leftExpr, right: rightExpr };
                }
                return result ? { kind: "true" } : { kind: "false" };
            }
            // x == x => true
            if (comp.op === "==" && areExprsEqual(leftExpr, rightExpr)) {
                return { kind: "true" };
            }
            // x != x => false
            if (comp.op === "!=" && areExprsEqual(leftExpr, rightExpr)) {
                return { kind: "false" };
            }

            return { ...comp, left: leftExpr, right: rightExpr };
        case "not":
            const inner = simplifyPredicate((predicate as NotPred).predicate);
            // !!P => P
            if (inner.kind === "not") return (inner as NotPred).predicate;
            // !true => false, !false => true
            if (inner.kind === "true") return { kind: "false" };
            if (inner.kind === "false") return { kind: "true" };
            return { kind: "not", predicate: inner };
        case "paren":
            const innerParen = simplifyPredicate((predicate as ParenPred).inner);
            return innerParen;
        case "implies":
            const leftImpl = simplifyPredicate((predicate as any).left);
            const rightImpl = simplifyPredicate((predicate as any).right);
            // true => P => P
            if (leftImpl.kind === "true") return rightImpl;
            // false => P => true
            if (leftImpl.kind === "false") return { kind: "true" };
            // P => true => true
            if (rightImpl.kind === "true") return { kind: "true" };

            return { kind: "implies", left: leftImpl, right: rightImpl };            
        default:
            return predicate;
    }
}

function simplifyExpr(expr: Expr): Expr {
    switch (expr.type) {
        case "num": 
            return expr;
        case "var": 
            return expr;
        case "neg": {
            const arg = simplifyExpr(expr.arg);
            if (arg.type === "num") {
                return { type: "num", value: -arg.value };
            }
            return { type: "neg", arg } as Expr;
        }
        case "bin": {
            const left = simplifyExpr(expr.left);
            const right = simplifyExpr(expr.right);
            
            // упрощение числовых операций
            if (left.type === "num" && right.type === "num") {
                const leftVal = left.value;
                const rightVal = right.value;
                switch (expr.operation) {
                    case "+": return { type: "num", value: leftVal + rightVal };
                    case "-": return { type: "num", value: leftVal - rightVal };
                    case "*": return { type: "num", value: leftVal * rightVal };
                    case "/": 
                        if (rightVal !== 0) return {type: "num", value: Math.floor(leftVal / rightVal)} as Expr;
                        return { type: "bin", operation: "/", left, right } as Expr;
                    default: return { type: "bin", operation: expr.operation, left, right };
                }
            }
            
            // алгебраические упрощения
            if (expr.operation === "+") {
                // 0 + x => x
                if (left.type === "num" && left.value === 0) return right;
                // x + 0 => x
                if (right.type === "num" && right.value === 0) return left;
            }
            
            if (expr.operation === "-") {
                // x - 0 => x
                if (right.type === "num" && right.value === 0) return left;
                // x - x => 0
                if (areExprsEqual(left, right)) return { type: "num", value: 0 };
            }
            
            if (expr.operation === "*") {
                // 0 * x => 0, x * 0 => 0
                if ((left.type === "num" && left.value === 0) || 
                    (right.type === "num" && right.value === 0)) {
                    return { type: "num", value: 0 };
                }
                // 1 * x => x, x * 1 => x
                if (left.type === "num" && left.value === 1) return right;
                if (right.type === "num" && right.value === 1) return left;
            }
            
            return { type: "bin", operation: expr.operation, left, right } as Expr;
        }
        case "funccall": {
            const args = expr.args.map(arg => simplifyExpr(arg));
            
            // НОВОЕ: упрощение вызовов factorial с константными аргументами
            if (expr.name === "factorial" && args.length === 1 && args[0].type === "num") {
                const n = args[0].value;
                if (n === 0) return { type: "num", value: 1 };
                if (n === 1) return { type: "num", value: 1 };
                // для других константных значений можно тоже вычислить факториал но пох
            }
            
            return { type: "funccall", name: expr.name, args };
        }
        case "arraccess": {
            const index = simplifyExpr(expr.index);
            return { type: "arraccess", name: expr.name, index };
        }
        default:
            return expr;
    }
}

/*
export interface AssignStmt {
    type: "assign";
    targets: LValue[];
    exprs: Expr[];
}
*/
function computeWPAssignment(
    assign: AssignStmt,
    postcondition: Predicate,
    // env: Map<string, Arith>,
    // z3: Context
): Predicate {
    if (assign.targets.length === 1 && assign.exprs.length === 1) {
        const target = assign.targets[0];
        const expr = assign.exprs[0];
        
        if (target.type === "lvar") {
            // подстановка переменной в postcondition на уровне AST перед конвертацией в Z3
            const wp = substituteInPredicate(postcondition, target.name, expr);
            console.log(`WP for assign ${target.name} := ${JSON.stringify(expr)} ->`, JSON.stringify(wp));
            return wp;
        }
        
        /*
        export interface ArrLValue {
            type: "larr";
            name: string;
            index: Expr;
        }
        */
        if (target.type === "larr") {
            // присваивание элементу массива: arr[index] = value
            const arrayName = target.name;
            const indexExpr = target.index;
            
            // выражение доступа к массиву для подстановки
            const arrayAccess: ArrAccessExpr = {
                type: "arraccess",
                name: arrayName,
                index: indexExpr
            };
            
            // подстановка во всем предикате arr[index] на expr
            const wp = substituteArrayAccessInPredicate(postcondition, arrayAccess, expr);
            console.log(`WP for assign ${arrayName}[${JSON.stringify(indexExpr)}] := ${JSON.stringify(expr)} ->`, JSON.stringify(wp));
            return wp;
        }
    }
    
    console.log(`неизвестный assignment: ${assign}`);
    throw new Error(`неизвестный assignment: ${assign}`);
}

function substituteArrayAccessInPredicate(
    predicate: Predicate, 
    arrayAccess: ArrAccessExpr, 
    substitution: Expr
): Predicate {
    // console.log("DEBUG substituteArrayAccessInPredicate:", {
    //     predicateKind: predicate.kind,
    //     predicate: JSON.stringify(predicate),
    //     arrayAccess: JSON.stringify(arrayAccess),
    //     substitution: JSON.stringify(substitution)
    // });
    
    switch (predicate.kind) {
        case "true":
            return predicate;
        case "false":
            return predicate;
        case "comparison":
            return {
                ...predicate,
                left: substituteArrayAccessInExpr(predicate.left, arrayAccess, substitution),
                right: substituteArrayAccessInExpr(predicate.right, arrayAccess, substitution),
            } as Predicate;
        case "and":
            return {
                kind: "and",
                left: substituteArrayAccessInPredicate((predicate as AndPred).left, arrayAccess, substitution),
                right: substituteArrayAccessInPredicate((predicate as AndPred).right, arrayAccess, substitution),
            } as Predicate;
        case "or":
            return {
                kind: "or",
                left: substituteArrayAccessInPredicate((predicate as OrPred).left, arrayAccess, substitution),
                right: substituteArrayAccessInPredicate((predicate as OrPred).right, arrayAccess, substitution),
            } as Predicate;
        case "not":
            return {
                kind: "not",
                predicate: substituteArrayAccessInPredicate((predicate as NotPred).predicate, arrayAccess, substitution),
            } as Predicate;
        case "paren":
            return {
                kind: "paren",
                inner: substituteArrayAccessInPredicate((predicate as ParenPred).inner, arrayAccess, substitution),
            } as Predicate;
        case "quantifier": {
            const q = predicate as Quantifier;
            // переменная квантора совпадает с именем массива -> не подставляю
            if (q.varName === arrayAccess.name) return predicate;
            
            return {
                ...q,
                body: substituteArrayAccessInPredicate(q.body, arrayAccess, substitution),
            } as Predicate;
        }
        case "implies":
            return {
                kind: "implies",
                left: substituteArrayAccessInPredicate((predicate as any).left, arrayAccess, substitution),
                right: substituteArrayAccessInPredicate((predicate as any).right, arrayAccess, substitution),
            } as Predicate;
        default:
            console.log(`неизвестный тип предиката: ${(predicate as any).kind}`);
            throw new Error(`неизвестный тип предиката: ${(predicate as any).kind}`);
    }
}

function substituteArrayAccessInExpr(
    expr: Expr, 
    arrayAccess: ArrAccessExpr, 
    substitution: Expr
): Expr {
    // является ли текущее выражение доступом к тому же массиву и с тем же индексом?
    if (expr.type === "arraccess" && 
        expr.name === arrayAccess.name && 
        areExprsEqual(expr.index, arrayAccess.index)) {
        return substitution;
    }
    
    // рекурсивно обработка других типы выражений
    switch (expr.type) {
        case "num":
            return expr;
        case "var":
            return expr;
        case "neg":
            return {
                type: "neg",
                arg: substituteArrayAccessInExpr(expr.arg, arrayAccess, substitution)
            } as Expr;
        case "bin":
            return {
                type: "bin",
                operation: expr.operation,
                left: substituteArrayAccessInExpr(expr.left, arrayAccess, substitution),
                right: substituteArrayAccessInExpr(expr.right, arrayAccess, substitution)
            } as Expr;
        case "funccall":
            return {
                type: "funccall",
                name: expr.name,
                args: expr.args.map(arg => substituteArrayAccessInExpr(arg, arrayAccess, substitution))
            } as Expr;
        case "arraccess":
            // рекурсивно обработка индекса
            return {
                type: "arraccess", 
                name: expr.name,
                index: substituteArrayAccessInExpr(expr.index, arrayAccess, substitution)
            } as Expr;
        default:
            console.log(`неизвестный тип выражения: ${(expr as any).type}`);
            throw new Error(`неизвестный тип выражения: ${(expr as any).type}`);
    }
}

// для сравнения выражений
function areExprsEqual(expr1: Expr, expr2: Expr): boolean {
    if (expr1.type !== expr2.type) return false;
    
    switch (expr1.type) {
        case "num":
            return (expr2.type === "num" && expr1.value === expr2.value);
        case "var":
            return (expr2.type === "var" && expr1.name === expr2.name);
        case "neg":
            return (expr2.type === "neg" && areExprsEqual(expr1.arg, (expr2 as any).arg));
        case "bin":
            if (expr2.type !== "bin") return false;
            return expr1.operation === expr2.operation &&
                   areExprsEqual(expr1.left, expr2.left) &&
                   areExprsEqual(expr1.right, expr2.right);
        case "funccall":
            if (expr2.type !== "funccall") return false;
            return expr1.name === expr2.name &&
                   expr1.args.length === expr2.args.length &&
                   expr1.args.every((arg, i) => areExprsEqual(arg, expr2.args[i]));
        case "arraccess":
            if (expr2.type !== "arraccess") return false;
            return expr1.name === expr2.name &&
                   areExprsEqual(expr1.index, expr2.index);
        default:
            return false;
    }
}

// подстановка expr всесто varName в postcondition
function substituteInPredicate(postcondition: Predicate, varName: string, expr: Expr): Predicate {
    switch (postcondition.kind) {
        case "true":
        case "false":
            return postcondition;
        case "comparison":
            return {
                ...postcondition,
                left: substituteInExpr(postcondition.left, varName, expr),
                right: substituteInExpr(postcondition.right, varName, expr),
            } as Predicate;
        case "and":
            return {
                kind: "and",
                left: substituteInPredicate((postcondition as AndPred).left, varName, expr),
                right: substituteInPredicate((postcondition as AndPred).right, varName, expr),
            } as Predicate;
        case "or":
            return {
                kind: "or",
                left: substituteInPredicate((postcondition as OrPred).left, varName, expr),
                right: substituteInPredicate((postcondition as OrPred).right, varName, expr),
            } as Predicate;
        case "not":
            return {
                kind: "not",
                predicate: substituteInPredicate((postcondition as NotPred).predicate, varName, expr),
            } as Predicate;
        case "paren":
            return {
                kind: "paren",
                inner: substituteInPredicate((postcondition as ParenPred).inner, varName, expr),
            } as Predicate;
        case "quantifier": {
            const q = postcondition as Quantifier;
            // связанная переменная  не подставляется внутрь
            if (q.varName === varName) {
                return postcondition;
            }
            return {
                ...q,
                body: substituteInPredicate(q.body, varName, expr),
            } as Predicate;
        }
        case "implies":
            return {
                kind: "implies",
                left: substituteInPredicate((postcondition as any).left, varName, expr),
                right: substituteInPredicate((postcondition as any).right, varName, expr),
            } as Predicate;

        case "formula":
            console.log("todo formula");
            throw new Error("kys");

        default:
            console.log(`неизвестный тип предиката: ${(postcondition as any).kind}`);
            throw new Error(`неизвестный тип предиката: ${(postcondition as any).kind}`);
    }
}

function substituteInExpr(expr: Expr, varName: string, substitution: Expr): Expr {
    switch (expr.type) {
        case "num":
            return expr;
        case "var":
            if (expr.name === varName) return substitution;
            return expr;
        case "neg":
            return {
                type: "neg",
                arg: substituteInExpr(expr.arg, varName, substitution)
            } as Expr;
        case "bin":
            return {
                type: "bin",
                operation: expr.operation,
                left: substituteInExpr(expr.left, varName, substitution),
                right: substituteInExpr(expr.right, varName, substitution)
            } as Expr;
        case "funccall":
            return {
                type: "funccall",
                name: expr.name,
                args: expr.args.map(arg => substituteInExpr(arg, varName, substitution))
            } as Expr;
        case "arraccess":
            return {
                type: "arraccess", 
                name: expr.name,
                index: substituteInExpr(expr.index, varName, substitution)
            } as Expr;
        default:
            console.log(`неизвестный тип выражения: ${(expr as any).type}`);
            throw new Error(`неизвестный тип выражения: ${(expr as any).type}`);
    }
}

/*
export interface BlockStmt {
    type: "block";
    stmts: Statement[];
}
*/
function computeWPBlock(
    block: BlockStmt,
    postcondition: Predicate,
    // env: Map<string, Arith>,
    // z3: Context
    module: AnnotatedModule
): Predicate {
    // обработка блоков в обратном порядке
    let currentWP = postcondition;
    for (let i = block.stmts.length - 1; i >= 0; --i) {
        // currentWP = computeWP(block.stmts[i], currentWP, env, z3);
        currentWP = computeWP(block.stmts[i], currentWP, module);
    }

    return currentWP;
}

/*
export interface ConditionalStmt {
    type: "if";
    condition: Condition;
    then: Statement;
    else: Statement | null;
}
*/
function computeWPIf(
    ifStmt: ConditionalStmt,
    postcondition: Predicate,
    // env: Map<string, Arith>,
    // z3: Context
    module: AnnotatedModule
): Predicate {
    // const condition = convertConditionToZ3(ifStmt.condition, env, z3);
    // const thenWP = computeWP(ifStmt.then, postcondition, env, z3);
    // const elseWP = ifStmt.else ? computeWP(ifStmt.else, postcondition, env, z3) : postcondition;

    const condition = convertConditionToPredicate(ifStmt.condition);
    const thenWP = computeWP(ifStmt.then, postcondition, module);
    const elseWP = ifStmt.else ? computeWP(ifStmt.else, postcondition, module) : postcondition;
    
    // return z3.And(
    //     z3.Implies(condition, thenWP),
    //     z3.Implies(z3.Not(condition), elseWP)
    // );

    // WP = (condition & thenWP) || (not(condition) & elseWP)
    return {
        kind: "or",
        left: {
            kind: "and",
            left: condition,
            right: thenWP
        },
        right: {
            kind: "and", 
            left: { kind: "not", predicate: condition },
            right: elseWP
        }
    };
}

function convertConditionToPredicate(condition: Condition): Predicate {
    switch (condition.kind) {
        case "true": return condition;
        case "false": return condition;
        case "comparison": 
            // мб проверка на совместимость типов
            return condition;
        case "not":
            return {
                kind: "not",
                predicate: convertConditionToPredicate(condition.condition)
            };
        case "and":
            return {
                kind: "and",
                left: convertConditionToPredicate(condition.left),
                right: convertConditionToPredicate(condition.right)
            };
        case "or":
            return {
                kind: "or",
                left: convertConditionToPredicate(condition.left),
                right: convertConditionToPredicate(condition.right)
            };
        case "implies":
            return {
                kind: "or",
                left: { 
                    kind: "not", 
                    predicate: convertConditionToPredicate(condition.left) 
                },
                right: convertConditionToPredicate(condition.right)
            };
        case "paren":
            return {
                kind: "paren",
                inner: convertConditionToPredicate(condition.inner)
            };
        default:
            console.log(`неизвестный тип условия: ${(condition as any).kind}`);
            throw new Error(`неизвестный тип условия: ${(condition as any).kind}`);
    }
}

/*
export interface WhileStmt {
    type: "while";
    condition: Condition;
    invariant: Predicate | null;
    body: Statement;
}
*/
function computeWPWhile(whileStmt: WhileStmt, postcondition: Predicate, module: AnnotatedModule): Predicate {
    if (!whileStmt.invariant) {
        throw new Error("while цикл без инварианта");
    }

    const invariant = whileStmt.invariant;
    const condition = convertConditionToPredicate(whileStmt.condition);
    const bodyWP = computeWP(whileStmt.body, invariant, module);

    return {
        kind: "and",
        left: invariant,
        right: {
            kind: "and",
            left: {
                kind: "implies",
                left: {
                    kind: "and",
                    left: invariant,
                    right: condition
                },
                right: bodyWP
            },
            right: {
                kind: "implies",
                left: {
                    kind: "and",
                    left: invariant,
                    right: { kind: "not", predicate: condition }
                },
                right: postcondition
            }
        }
    };
}

// --- конвертация в Z3 ---
function convertPredicateToZ3(
    predicate: Predicate,
    env: Map<string, Arith>,
    z3: Context,
    module: AnnotatedModule,
    solver: any
): Bool {
    switch (predicate.kind) {
        case "true": return z3.Bool.val(true);
        case "false": return z3.Bool.val(false);
        case "comparison": 
            return convertComparisonToZ3(predicate, env, z3, module, solver);
        case "and":
            return z3.And(
                convertPredicateToZ3((predicate as AndPred).left, env, z3, module, solver),
                convertPredicateToZ3((predicate as AndPred).right, env, z3, module, solver)
            );
        case "or":
            return z3.Or(
                convertPredicateToZ3((predicate as OrPred).left, env, z3, module, solver),
                convertPredicateToZ3((predicate as OrPred).right, env, z3, module, solver)
            );
        case "not":
            return z3.Not(convertPredicateToZ3((predicate as NotPred).predicate, env, z3, module, solver));
        case "paren":
            return convertPredicateToZ3((predicate as ParenPred).inner, env, z3, module, solver);
        case "quantifier":
            return convertQuantifierToZ3(predicate as Quantifier, env, z3, module, solver);
        case "implies":
            return z3.Implies(
                convertPredicateToZ3((predicate as any).left, env, z3, module, solver),
                convertPredicateToZ3((predicate as any).right, env, z3, module, solver)
            );
        default:
            console.log(`что за предикат таккой: ${(predicate as any).kind}`);
            throw new Error(`что за предикат таккой: ${(predicate as any).kind}`);
    }
}

function convertComparisonToZ3(
    comparison: ComparisonCond,
    env: Map<string, Arith>,
    z3: Context,
    module: AnnotatedModule,
    solver: any
): Bool {
    const left = convertExprToZ3(comparison.left, env, z3, module, solver);
    const right = convertExprToZ3(comparison.right, env, z3, module, solver);
    
    switch (comparison.op) {
        case "==": return left.eq(right);
        case "!=": return left.neq(right);
        case ">": return left.gt(right);
        case "<": return left.lt(right);
        case ">=": return left.ge(right);
        case "<=": return left.le(right);
        default: 
            console.log(`unnown comparison operator: ${comparison.op}`);
            throw new Error(`unnown comparison operator: ${comparison.op}`);
    }
}

// генерация ключа на основе структуры выражения индекса
function generateIndexKey(indexExpr: Expr): string {
    switch (indexExpr.type) {
        case "num":
            return `const_${indexExpr.value}`;
        case "var":
            return `var_${indexExpr.name}`;
        case "bin":
            const leftKey = generateIndexKey(indexExpr.left);
            const rightKey = generateIndexKey(indexExpr.right);
            
            // ! для некоммутативных операций операнды сортируются [1+j] = [j+1]
            if (indexExpr.operation === "+" || indexExpr.operation === "*") {
                const sorted = [leftKey, rightKey].sort();
                return `bin_${indexExpr.operation}_${sorted[0]}_${sorted[1]}`;
            }
            return `bin_${indexExpr.operation}_${leftKey}_${rightKey}`;
        case "neg":
            return `neg_${generateIndexKey(indexExpr.arg)}`;
        case "funccall":
            const argsKey = indexExpr.args.map(generateIndexKey).join("_");
            return `call_${indexExpr.name}_${argsKey}`;
        case "arraccess":
            return `arr_${indexExpr.name}_${generateIndexKey(indexExpr.index)}`;
        default:
            return `unknown_${Math.random().toString(36).substr(2, 9)}`;
    }
}

function convertExprToZ3(
    expr: Expr,
    env: Map<string, Arith>,
    z3: Context,
    module: AnnotatedModule, // для доступа к спецификациям функций
    solver: any // для добавления аксиом
): Arith {
    switch (expr.type) {
        case "num": return z3.Int.val(expr.value);
        case "var":
            const varExpr = env.get(expr.name);
            if (!varExpr) {
                const arrayExpr = env.get(expr.name + "_array");
                if (arrayExpr) {
                    console.log(`найден массив: ${arrayExpr}`);
                    return arrayExpr;
                }
                console.log(`неизвестная перем: ${expr.name}`);
                throw new Error(`неизвестная перем: ${expr.name}`);
            }
            return varExpr;
        case "neg": return convertExprToZ3(expr.arg, env, z3, module, solver).neg();
        case "bin":
            const left = convertExprToZ3(expr.left, env, z3, module, solver);
            const right = convertExprToZ3(expr.right, env, z3, module, solver);
            switch (expr.operation) {
                case "+": return left.add(right);
                case "-": return left.sub(right);
                case "*": return left.mul(right);
                case "/": return left.div(right);
                default: 
                    console.log(`неизвестный бинарный опер: ${expr.operation}`);
                    throw new Error(`неизвестный бинарный опер: ${expr.operation}`);
            }
        case "funccall":
            // if (expr.name === "foo1") {
            //     return z3.Int.val(42);
            // }
            // if (expr.name === "foo2" && expr.args.length === 1) {
            //     const arg = convertExprToZ3(expr.args[0], env, z3);
            //     return arg.add(1);
            // }

            // конвертация всех аргументов в Z3
            const args = expr.args.map(arg => convertExprToZ3(arg, env, z3, module, solver));

            // уникальное имя для результата функции
            const argString = args.map(a => a.toString()).join('_');
            const funcResultName = `${expr.name}_result_${argString}`;
            
            // не создавали ли уже такую? если да, то возвращаю
            if (env.has(funcResultName)) {
                return env.get(funcResultName)!;
            }
            
            // новая Z3 переменная для результата функции
            const funcResult = z3.Int.const(funcResultName);
            // добавляю ее в окружение для последующего использования
            env.set(funcResultName, funcResult);

            // НОВОЕ - поиск спецификации функции И добавляю ее аксиомы
            const funcSpec = findFunctionSpec(expr.name, module);
            if (funcSpec) {
                addFunctionAxioms(expr.name, funcSpec, args, funcResult, env, z3, solver, module);
            }
            
            return funcResult;
        case "arraccess":
            const arrayName = expr.name; // arr[i] -> "arr"
            // конвертация индекса массива в Z3
            const index = convertExprToZ3(expr.index, env, z3, module, solver);

            // переменная для элемента массива (arr[5] -> "arr_elem_5")
            const indexKey = generateIndexKey(expr.index);
            const elemVarName = `${arrayName}_elem_${indexKey}`;
            
            // не создавали ли уже такую? если да, то возвращаю
            if (env.has(elemVarName)) {
                return env.get(elemVarName)!;
            }
            
            // новая Z3 переменная для элемента массива
            const elemVar = z3.Int.const(elemVarName);
            env.set(elemVarName, elemVar);
            return elemVar;
        default:
            console.log(`неизвестный expression type: ${(expr as any).type}`);
            throw new Error(`неизвестный expression type: ${(expr as any).type}`);
    }
}

function findFunctionSpec(funcName: string, module: AnnotatedModule): AnnotatedFunctionDef | null {
    return module.functions.find(f => f.name === funcName) || null;
}

// поиск внутри Expr вызова функции с именем name
function exprContainsCall(expr: Expr | null, name: string): boolean {
    if (!expr) return false;
    switch (expr.type) {
        case "num": return false;
        case "var": return false;
        case "neg": return exprContainsCall(expr.arg, name);
        case "bin":
            return exprContainsCall(expr.left, name) || exprContainsCall(expr.right, name);
        case "funccall":
            if (expr.name === name) return true;
            return expr.args.some(a => exprContainsCall(a, name));
        case "arraccess":
            return exprContainsCall(expr.index, name);
        default: return false;
    }
}

// поиск внутри Predicate вызова функции с именем name
function predicateContainsCall(pred: Predicate | null, name: string): boolean {
    if (!pred) return false;
    switch (pred.kind) {
        case "true": return false;
        case "false": return false;
        case "comparison":
            return exprContainsCall((pred as ComparisonCond).left, name)
                || exprContainsCall((pred as ComparisonCond).right, name);
        case "and":
        case "or":
            return predicateContainsCall((pred as any).left, name) 
            || predicateContainsCall((pred as any).right, name);
        case "not":
            return predicateContainsCall((pred as NotPred).predicate, name);
        case "paren":
            return predicateContainsCall((pred as ParenPred).inner, name);
        case "quantifier":
            return predicateContainsCall((pred as Quantifier).body, name);
        case "implies":
            return predicateContainsCall((pred as any).left, name) || predicateContainsCall((pred as any).right, name);
        default: return false;
    }
}

// добавление аксиомы на основе постусловия функции
function addFunctionAxioms(
    funcName: string,
    funcSpec: AnnotatedFunctionDef,
    args: Arith[],
    result: Arith,
    env: Map<string, Arith>,
    z3: Context,
    solver: any,
    module: AnnotatedModule
) {
    if (!funcSpec.postcondition) {
        console.log(`функция ${funcName}: нет постусловия -> аксиомы не добавляются`);
        return; 
    }

    // рекурсия -> НЕ добавлять аксиому
    const combinedPost = combinePredicates(funcSpec.postcondition);
    if (predicateContainsCall(combinedPost, funcName)) {
        console.log(`функция ${funcName} рекурсивная -> пропускаю добавление аксиом`);
        return;
    }

    // временное окружение для параметров функции
    const funcEnv = new Map<string, Arith>();
    
    // формальные параметры
    funcSpec.parameters.forEach((param, index) => {
        if (index < args.length) {
            funcEnv.set(param.name, args[index]);
        }
    });
    
    // возвращаемое значение
    if (funcSpec.returns.length === 1) {
        funcEnv.set(funcSpec.returns[0].name, result);
    }
    
    // компбинация постусловий (если их несколько)
    const postcondition = combinePredicates(funcSpec.postcondition);
    
    // постусловие -> Z3 с использованием временного окружения
    const z3Postcondition = convertPredicateToZ3(postcondition, funcEnv, z3, module, solver);
    
    // ++ АКСИОМА: постусловие всегда истинно
    solver.add(z3Postcondition);
}

/*
quantifier = ("forall" | "exists") (* тип квантора *)
    "(" variableDef                (* переменная предиката *)
        "|" predicate              (* предикат *)
    ")";
*/
/*
export interface Quantifier {
    kind: "quantifier";
    quant: "forall" | "exists";
    varName: string;
    varType: "int" | "int[]";
    body: Predicate;
}
*/
function convertQuantifierToZ3(
    quantifier: Quantifier,
    env: Map<string, Arith>,
    z3: Context,
    module: AnnotatedModule,
    solver: any
): Bool {
    // новая переменная для квантора
    const varName = quantifier.varName;
    let varExpr: Arith;

    const varType = quantifier.varType;
    if (varType === "int") {
        varExpr = z3.Int.const(varName);
    } else if (varType === "int[]") {
        // todo
        console.log("в кванторах числовых массивов пока нема");
        throw new Error("в кванторах числовых массивов пока нема");
    } else {
        console.warn(`Неизвестный тип переменной в кванторе: ${varType}, используем int`);
        varExpr = z3.Int.const(varName);
    }

    // + новое окружение С добавленной переменной 
    const new_environment = new Map(env);
    new_environment.set(varName, varExpr);

    const body = convertPredicateToZ3(quantifier.body, new_environment, z3, module, solver);

    if (quantifier.quant === "forall") {
        return z3.ForAll([varExpr], body);
    } else {
        return z3.Exists([varExpr], body);
    }
}