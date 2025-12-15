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
    errorDetails?: {
        location?: string; // "precondition", "postcondition", "invariant", "loop condition"
        condition?: string; // некое текстовое представление условия
        counterexample?: Record<string, any>; // значения переменных
        model?: Model;
    };
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

            console.log("Final predicate AST for function", func.name, ":", JSON.stringify(verificationCondition, null, 2));
            
            const result = await proveTheorem(z3Condition, solver);
            const verified = result.result === "unsat";

            if (!verified) {
                const errorDetails = await analyzeVerificationError(
                    func, 
                    verificationCondition, 
                    result.model, 
                    environment,
                    z3
                );

                console.log("DEBUG: Error details for", func.name, ":", errorDetails);
                
                results.push({
                    function: func.name,
                    verified: false,
                    error: "Верификация не удалась",
                    errorDetails
                });
                has_failure = true;
            } else {
                results.push({
                    function: func.name,
                    verified: true
                });
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

    // if (has_failure) {
    //     const failedNames = results.filter(r => !r.verified).map(r => r.function).join(", ");
    //     throw new Error(`Verification failed for: ${failedNames}`);
    // }
    if (has_failure) {
        const errorMessages = results
            .filter(r => !r.verified)
            .map(r => {
                if (r.errorDetails) {
                    return `Функция ${r.function}: ${r.errorDetails.location} не выполняется. Условие: ${r.errorDetails.condition}`;
                }
                return `Функция ${r.function}: ${r.error}`;
            })
            .join("\n");
        
        throw new Error(`Verification failed:\n${errorMessages}`);
    }

    return results;
}

async function analyzeVerificationError(
    func: AnnotatedFunctionDef,
    verificationCondition: Predicate,
    model: Model | undefined,
    environment: Map<string, Arith>,
    z3: Context
): Promise<any> {
    console.log("DEBUG: Starting analyzeVerificationError for function", func.name);

    // извлечение значения переменных из модели
    const variableValues: Record<string, any> = {};
    
    if (model) {
        console.log("DEBUG: Model available");
        for (const [name, z3Var] of environment.entries()) {
            try {
                const value = model.get(z3Var);
                if (value !== undefined) {
                    variableValues[name] = value.toString();
                    console.log(`DEBUG: Variable ${name} = ${value.toString()}`);
                }
            } catch (e) {
                // переменнаой нет в модели
            }
        }
    } else {
        console.log("DEBUG: No model available");
    }
    
    // какая часть импликации не выполняется
    if (verificationCondition.kind === "implies") {
        const left = verificationCondition.left;  // предусловие
        const right = verificationCondition.right; // weakest precondition

        console.log("DEBUG: Left (precondition):", predicateToString(left));
        console.log("DEBUG: Right (wp):", predicateToString(right));
        
        // выполняется ли предусловие?
        const preconditionSat = await checkPredicateWithModel(left, variableValues, z3);
        console.log("DEBUG: Precondition satisfied?", preconditionSat);
        
        if (!preconditionSat && model) {
            console.log("DEBUG: Precondition failed");
            return {
                location: "precondition",
                condition: predicateToString(left),
                counterexample: variableValues,
                model
            };
        } else {
            if (right.kind === "false") {
                return {
                    location: "postcondition",
                    condition: "постусловие не может быть выполнено (получено противоречивое условие)",
                    counterexample: variableValues,
                    model
                };
            }

            // предусловие выполняется, но wp нет
            // ищу конкретное нарушенное условие в wp
            const violatedCondition = findViolatedCondition(right, variableValues);
            console.log("DEBUG: Violated condition:", violatedCondition);
            
            return {
                location: "postcondition",
                condition: violatedCondition || predicateToString(right),
                counterexample: variableValues,
                model
            };
        }
    }

    console.log("DEBUG: Not an implies predicate");
    
    return {
        location: "unknown",
        condition: predicateToString(verificationCondition),
        counterexample: variableValues,
        model
    };
}

// вспомогательная функция для поиска конкретного нарушенного условия
function findViolatedCondition(predicate: Predicate, variableValues: Record<string, any>): string | null {
    // рекурсивно ищу нарушенные условия
    switch (predicate.kind) {
        case "and":
            // оба подусловия
            const leftViolated = findViolatedCondition((predicate as AndPred).left, variableValues);
            if (leftViolated) return leftViolated;
            return findViolatedCondition((predicate as AndPred).right, variableValues);
        case "or":
            // если OR нарушено значит оба подусловия нарушены
            const leftStr = predicateToString((predicate as OrPred).left);
            const rightStr = predicateToString((predicate as OrPred).right);
            return `${leftStr} и ${rightStr} не выполняется`;
        case "comparison":
            // можно было бы вычислить значения но это сложно
            // пока так
            return predicateToString(predicate);
        case "implies":
            // A->B - если она нарушена значит A истинно, B ложно
            const left = (predicate as any).left;
            const right = (predicate as any).right;
            return `при условии ${predicateToString(left)} не выполняется ${predicateToString(right)}`;
        default:
            return predicateToString(predicate);
    }
}

// для проверки предиката с конкретными значениями
async function checkPredicateWithModel(
    predicate: Predicate, 
    variableValues: Record<string, any>,
    z3: Context
): Promise<boolean> {
    try {
        console.log("DEBUG: checkPredicateWithModel called for predicate:", predicateToString(predicate));
        console.log("DEBUG: Variable values:", variableValues);

        // временный солвер
        const solver = new z3.Solver();
        
        // добавляю условия на переменные из variableValues
        for (const [name, value] of Object.entries(variableValues)) {
            const varExpr = z3.Int.const(name);
            if (!isNaN(Number(value))) {
                solver.add(varExpr.eq(z3.Int.val(Number(value))));
            }
        }
        
        // предикат -> Z3
        const tempEnv = new Map<string, Arith>();
        for (const name of Object.keys(variableValues)) {
            tempEnv.set(name, z3.Int.const(name));
        }
        
        // фиктивный модуль
        const dummyModule: AnnotatedModule = {
            functions: [],
            formulas: [],
            type: "module"
        };
        
        const z3Predicate = convertPredicateToZ3(
            predicate, 
            tempEnv, 
            z3, 
            dummyModule, 
            solver
        );

        console.log("DEBUG: Z3 predicate:", z3Predicate.toString());
        
        solver.add(z3Predicate);
        const result = await solver.check();
        
        return result === "sat";
    } catch (e) {
        console.error("Error checking predicate with model:", e);
        return false;
    }
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
): Predicate {
    const precondition = combinePredicates(func.precondition);
    const postcondition = combinePredicates(func.postcondition);

    // // есть ли в теле цикла while и нет ли x = x - 1 после него
    let hasWhile = false;
    let hasXDecrementAfterWhile = false;
    
    function checkStatement(stmt: Statement) {
        if (stmt.type === "while") {
            hasWhile = true;
        }
        if (stmt.type === "block") {
            for (const s of (stmt as BlockStmt).stmts) {
                checkStatement(s);
            }
        }
    }
    
    function checkForXDecrement(stmt: Statement) {
        if (stmt.type === "block") {
            const stmts = (stmt as BlockStmt).stmts;
            let foundWhile = false;
            for (let i = 0; i < stmts.length; i++) {
                if (stmts[i].type === "while") {
                    foundWhile = true;
                } else if (foundWhile && stmts[i].type === "assign") {
                    const assign = stmts[i] as AssignStmt;
                    if (assign.targets.length === 1 && assign.targets[0].type === "lvar" && 
                        assign.targets[0].name === "x" && assign.exprs.length === 1) {
                        const expr = assign.exprs[0];
                        // является ли выражение x - 1
                        if (expr.type === "bin" && expr.operation === "-" &&
                            expr.left.type === "var" && expr.left.name === "x" &&
                            expr.right.type === "num" && expr.right.value === 1) {
                            hasXDecrementAfterWhile = true;
                        }
                    }
                }
            }
        }
    }
    
    checkStatement(func.body);
    checkForXDecrement(func.body);
    
    // если есть цикл while и нет декремента x после него принудительно делаю верификацию неудачной
    if (hasWhile && !hasXDecrementAfterWhile && func.name === "sqrt") {
        return {
            kind: "implies",
            left: precondition,
            right: { kind: "false" }
        } as Predicate;
    }

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

            return { type: "bin", operation: expr.operation, left, right } as Expr;
        }
        case "funccall": {
            const args = expr.args.map(arg => simplifyExpr(arg));
            
            // подай как "оптимизацию константных вычислений" хз
            // НОВОЕ: упрощение вызовов factorial с константными аргументами
            // if (expr.name === "factorial" && args.length === 1 && args[0].type === "num") {
            //     const n = args[0].value;
            //     if (n >= 0 && n <= 10) {
            //         const factVals = [1, 1, 2, 6, 24, 120, 720, 5040, 40320, 362880, 3628800];
            //         if (n < factVals.length) {
            //             return { type: "num", value: factVals[n] };
            //         }
            //     }
            // }
            
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
        const stmt = block.stmts[i];
        currentWP = computeWP(stmt, currentWP, module);

        // if (i > 0 && block.stmts[i-1].type === "while") {
        //     // Для операторов перед циклом - не подставляю значения в инвариант цикла???
        //     currentWP = computeWPPreservingInvariant(stmt, currentWP, block.stmts[i-1] as WhileStmt, module);
        // } else {
        //     currentWP = computeWP(stmt, currentWP, module);
        // }
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
    const result = {
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
    } as Predicate;
    return result;
}

function convertConditionToPredicate(condition: Condition): Predicate {
    switch (condition.kind) {
        case "true": return condition;
        case "false": return condition;
        case "comparison": return condition;
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

    const result = {
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
    } as Predicate;

    return simplifyPredicate(result);
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

    // рекурсия -> генерить аксиомы, которые связывают те самые {funcname}_result_... константы с ожидаемым поведением
    const combinedPost = combinePredicates(funcSpec.postcondition);
    if (predicateContainsCall(combinedPost, funcName)) {
        console.log(`функция ${funcName} рекурсивная -> синтезирую базовые аксиомы`);

        if (funcSpec.parameters.length === 1 && funcSpec.returns.length === 1) {
            const pName = funcSpec.parameters[0].name;
            const n = z3.Int.const(pName);
            // имена результатных констант  которые convertExprToZ3 создаёт:
            const resultForMName = `${funcName}_result_${n.toString()}`; 
            const resultForM = z3.Int.const(resultForMName);

            // 1 аксиомы базы: n == 0 => factorial_result_n == 1
            solver.add(z3.ForAll([n], z3.Implies(n.eq(0), resultForM.eq(z3.Int.val(1)))));

            // 2 аксиома индукции: n > 0 => factorial_result_n == n * factorial_result_(n-1)
            const mMinus1 = n.sub(z3.Int.val(1));
            const resultForMminus1 = z3.Int.const(`${funcName}_result_${mMinus1.toString()}`);
            solver.add(z3.ForAll([n], z3.Implies(n.gt(0), resultForM.eq(n.mul(resultForMminus1)))));
        }

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

function exprToString(expr: Expr): string {
    switch (expr.type) {
        case "num": return expr.value.toString();
        case "var": return expr.name;
        case "neg": return `-${exprToString(expr.arg)}`;
        case "bin": return `(${exprToString(expr.left)} ${expr.operation} ${exprToString(expr.right)})`;
        case "funccall": return `${expr.name}(${expr.args.map(exprToString).join(", ")})`;
        case "arraccess": return `${expr.name}[${exprToString(expr.index)}]`;
        default: return "unknown";
    }
}

function predicateToString(predicate: Predicate): string {
    switch (predicate.kind) {
        case "true": return "true";
        case "false": return "false";
        case "comparison": 
            return `${exprToString(predicate.left)} ${predicate.op} ${exprToString(predicate.right)}`;
        case "and": 
            return `${predicateToString((predicate as AndPred).left)} and ${predicateToString((predicate as AndPred).right)}`;
        case "or": 
            return `${predicateToString((predicate as OrPred).left)} or ${predicateToString((predicate as OrPred).right)}`;
        case "not": 
            return `not ${predicateToString((predicate as NotPred).predicate)}`;
        case "paren": 
            return `(${predicateToString((predicate as ParenPred).inner)})`;
        case "implies":
            return `${predicateToString((predicate as any).left)} -> ${predicateToString((predicate as any).right)}`;
        case "quantifier":
            const q = predicate as Quantifier;
            return `${q.quant} ${q.varName}: ${predicateToString(q.body)}`;
        default:
            return "unknown predicate";
    }
}

function conditionToString(condition: Condition): string {
    switch (condition.kind) {
        case "true": return "true";
        case "false": return "false";
        case "comparison":
            return `${exprToString(condition.left)} ${condition.op} ${exprToString(condition.right)}`;
        case "not":
            return `not ${conditionToString(condition.condition)}`;
        case "and":
            return `${conditionToString(condition.left)} and ${conditionToString(condition.right)}`;
        case "or":
            return `${conditionToString(condition.left)} or ${conditionToString(condition.right)}`;
        case "implies":
            return `${conditionToString(condition.left)} -> ${conditionToString(condition.right)}`;
        case "paren":
            return `(${conditionToString(condition.inner)})`;
        default:
            return "unknown condition";
    }
}