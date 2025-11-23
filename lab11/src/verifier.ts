import { Arith, ArithSort, Bool, Context, init, Model, SMTArray, SMTArraySort } from "z3-solver";

import { printFuncCall } from "./printFuncCall";
import { AnnotatedModule, AnnotatedFunctionDef, Formula } from "../../lab10";
import { error } from "console";
import { 
    Statement, Expr, Predicate, Condition, ParameterDef, 
    AssignStmt, BlockStmt, ConditionalStmt, WhileStmt,
    LValue, VarLValue, ArrLValue,
    FuncCallExpr, ArrAccessExpr,
    TrueCond, FalseCond, ComparisonCond, NotCond, AndCond, OrCond, ImpliesCond, ParenCond,
    Quantifier, FormulaRef, NotPred, AndPred, OrPred, ParenPred
} from "../../lab08/src/funny";


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
    z3 = await initZ3();
    const results: VerificationResult[] = [];
    // throw "Not implemented"

    for (const func of module.functions) {
        try {
            const theorem = buildFunctionVerificationConditions(func, module, z3);
            const result = await proveTheorem(theorem, z3);
            results.push(
                {
                    function: func.name,
                    verified: result.result === "unsat",
                    error: result.result === "sat" ? "теорема неверна, так как найден контрпример. Вернул модель, опровергающую теорему." : undefined,
                    model: result.model
                }
            );
        } catch (error) {
            results.push(
                {
                    function: func.name,
                    verified: false,
                    error: error as string
                }
            );
        }
    }

    return results;
}

async function proveTheorem(
    theorem: Bool,
    z3: Context
): Promise<{ result: "sat" | "unsat" | "unknown"; model?: Model }> {
    const solver = new z3.Solver();
    
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

function buildFunctionVerificationConditions(
    func: AnnotatedFunctionDef,
    module: AnnotatedModule,
    z3: Context
): Bool {
    const environment = new Map<string, Arith>();

    // вложение параметров
    for (const param of func.parameters) {
        if (param.type === "int" as string) {
            environment.set(param.name, z3.Int.const(param.name));
        } else if (param.type.toString() === "int[]") {
            // todo
            throw new Error("int[] не сделал");
        }
    }

    // добавление return values
    for (const ret of func.returns) {
        if (ret.type.toString() === "int") {
            environment.set(ret.name, z3.Int.const(ret.name));
        }
    }

    // добавление локальных переменных
    for (const local of func.locals) {
        if (local.type.toString() === "int") {
            environment.set(local.name, z3.Int.const(local.name));
        }
    }

    // предусловие -> Z3 
    const precondition = convertPredicatesToZ3(func.precondition, environment, z3);

    const postcondition = convertPredicatesToZ3(func.postcondition, environment, z3);

    // weakest precondition для тела функции
    const wpBody = computeWP(func.body, postcondition, environment, z3);

    // условие верификации: pre -> wp
    return z3.Implies(precondition, wpBody);
}

// объединие массива предикатов в Z3
function convertPredicatesToZ3(
    predicates: Predicate[] | null,
    env: Map<string, Arith>,
    z3: Context
): Bool {
    // пустое условие
    if (!predicates || predicates.length === 0) {
        return z3.Bool.val(true);
    }
    
    let result = convertPredicateToZ3(predicates[0], env, z3);

    if (predicates.length === 1) {
        return result;
    }

    for (let i = 1; i < predicates.length; i++) {
        result = z3.And(result, convertPredicateToZ3(predicates[i], env, z3));
    }
    
    return result;
}

function convertPredicateToZ3(
    predicate: Predicate,
    env: Map<string, Arith>,
    z3: Context
): Bool {
    switch (predicate.kind) {
        case "true": return z3.Bool.val(true);
        case "false": return z3.Bool.val(false);
        case "comparison": 
            return convertComparisonToZ3(predicate, env, z3);
        case "and":
            return z3.And(
                convertPredicateToZ3((predicate as AndPred).left, env, z3),
                convertPredicateToZ3((predicate as AndPred).right, env, z3)
            );
        case "or":
            return z3.Or(
                convertPredicateToZ3((predicate as OrPred).left, env, z3),
                convertPredicateToZ3((predicate as OrPred).right, env, z3)
            );
        case "not":
            return z3.Not(convertPredicateToZ3((predicate as NotPred).predicate, env, z3));
        case "paren":
            return convertPredicateToZ3((predicate as ParenPred).inner, env, z3);
        case "quantifier":
            return convertQuantifierToZ3(predicate as Quantifier, env, z3);
        // case "formula":
        //     return convertFormulaRefToZ3(predicate as FormulaRef, env, z3);
        default:
            throw new Error(`что за предикат таккой: ${(predicate as any).kind}`);
    }
}

function convertComparisonToZ3(
    comparison: ComparisonCond,
    env: Map<string, Arith>,
    z3: Context
): Bool {
    const left = convertExprToZ3(comparison.left, env, z3);
    const right = convertExprToZ3(comparison.right, env, z3);
    
    switch (comparison.op) {
        case "==": return left.eq(right);
        case "!=": return left.neq(right);
        case ">": return left.gt(right);
        case "<": return left.lt(right);
        case ">=": return left.ge(right);
        case "<=": return left.le(right);
        
        default: throw new Error(`unnown comparison operator: ${comparison.op}`);
    }
}

function convertExprToZ3(
    expr: Expr,
    env: Map<string, Arith>,
    z3: Context
): Arith {
    switch (expr.type) {
        case "num": return z3.Int.val(expr.value);
        case "var":
            const varExpr = env.get(expr.name);
            if (!varExpr) {
                throw new Error(`неизвестная перем: ${expr.name}`);
            }

            return varExpr;
        case "neg": return convertExprToZ3(expr.arg, env, z3).neg();
        case "bin":
            const left = convertExprToZ3(expr.left, env, z3);
            const right = convertExprToZ3(expr.right, env, z3);
            switch (expr.operation) {
                case "+": return left.add(right);
                case "-": return left.sub(right);
                case "*": return left.mul(right);
                case "/": return left.div(right);
                default: throw new Error(`неизвестный бинарный опер: ${expr.operation}`);
            }
        case "funccall":
            // todo
            throw new Error("todo funccall");
        case "arraccess":
            // todo
            throw new Error("todo arraccess");
        default:
            throw new Error(`неизвестный expression type: ${(expr as any).type}`);
    }
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
    z3: Context
): Bool {
    // новая переменная для квантора
    const varName = quantifier.varName;
    let varExpr: Arith;
    
    if (quantifier.varType === "int") {
        varExpr = z3.Int.const(varName);
    } else {
        // todo
        throw new Error("в кванторах числовых массивов пока нема");
    }

    // + новое окружение С добавленной переменной 
    const new_environment = new Map(env);
    new_environment.set(varName, varExpr);

    const body = convertPredicateToZ3(quantifier.body, new_environment, z3);

    if (quantifier.quant === "forall") {
        return z3.ForAll([varExpr], body);
    } else {
        return z3.Exists([varExpr], body);
    }
}

function computeWP(
    statement: Statement, 
    postcondition: Bool, 
    env: Map<string, Arith>, 
    z3: Context
): Bool {
    switch (statement.type) {
        case "assign": 
            return computeWPAssignment(statement, postcondition, env, z3);
        case "block":
            return computeWPBlock(statement, postcondition, env, z3);
        case "if":
            return computeWPIf(statement, postcondition, env, z3);
        case "while":
            return computeWPWhile(statement, postcondition, env, z3);
        default:
            throw new Error(`неизвестный оператор: ${(statement as any).type}`);
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
    postcondition: Bool,
    env: Map<string, Arith>,
    z3: Context
): Bool {
    // if (assign.targets.length === 1 && assign.exprs.length === 1) {
    //     const target = assign.targets[0];
    //     const expr = assign.exprs[0];
        
    //     /*
    //     export interface VarLValue {
    //         type: "lvar";
    //         name: string;
    //     }
    //     */
    //     if (target.type === "lvar") {
    //         const varName = target.name;
            
    //         // подстановка переменной на уровне AST перед конвертацией в Z3
    //         return substituteInPredicate(postcondition, varName, expr);
    //     }
        
    //     /*
    //     export interface ArrLValue {
    //         type: "larr";
    //         name: string;
    //         index: Expr;
    //     }
    //     */
    //     // todo
    // }
    
    throw new Error(`неизвестный assignment: ${assign}`);
}

/*
export interface BlockStmt {
    type: "block";
    stmts: Statement[];
}
*/
function computeWPBlock(
    block: BlockStmt,
    postcondition: Bool,
    env: Map<string, Arith>,
    z3: Context
): Bool {
    // обработка блоков в обратном порядке
    let currentWP = postcondition;
    for (let i = block.stmts.length - 1; i >= 0; --i) {
        currentWP = computeWP(block.stmts[i], currentWP, env, z3);
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
    postcondition: Bool,
    env: Map<string, Arith>,
    z3: Context
): Bool {
    const condition = convertConditionToZ3(ifStmt.condition, env, z3);
    const thenWP = computeWP(ifStmt.then, postcondition, env, z3);
    const elseWP = ifStmt.else ? computeWP(ifStmt.else, postcondition, env, z3) : postcondition;
    
    return z3.And(
        z3.Implies(condition, thenWP),
        z3.Implies(z3.Not(condition), elseWP)
    );
}

function convertConditionToZ3(
    condition: Condition,
    env: Map<string, Arith>,
    z3: Context
): Bool {
    switch (condition.kind) {
        case "true": return z3.Bool.val(true);
        case "false": return z3.Bool.val(false);
        case "comparison":
            return convertComparisonToZ3(condition, env, z3);
        case "not":
            return z3.Not(convertConditionToZ3((condition as NotCond).condition, env, z3));
        case "and":
            return z3.And(
                convertConditionToZ3((condition as AndCond).left, env, z3),
                convertConditionToZ3((condition as AndCond).right, env, z3)
            );
        case "or":
            return z3.Or(
                convertConditionToZ3((condition as OrCond).left, env, z3),
                convertConditionToZ3((condition as OrCond).right, env, z3)
            );
        case "implies":
            return z3.Implies(
                convertConditionToZ3((condition as ImpliesCond).left, env, z3),
                convertConditionToZ3((condition as ImpliesCond).right, env, z3)
            );
        case "paren":
            return convertConditionToZ3((condition as ParenCond).inner, env, z3);
        default:
            throw new Error(`такого condition еще нема: ${(condition as any).kind}`);
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
function computeWPWhile(
    whileStmt: WhileStmt,
    postcondition: Bool,
    env: Map<string, Arith>,
    z3: Context
): Bool {
    if (!whileStmt.invariant) {
        throw new Error("while цикл без инварианта");
    }
    
    const condition = convertConditionToZ3(whileStmt.condition, env, z3);
    const invariant = convertPredicateToZ3(whileStmt.invariant, env, z3);
    
    // WP для цикла: I & (I & C -> WP(body, I)) & (I & not(C) -> postcondition)
    const bodyWP = computeWP(whileStmt.body, invariant, env, z3);
    return z3.And(
        invariant, // I выполняется перед циклом
        z3.Implies(z3.And(invariant, condition), bodyWP), // I сохраняется в теле
        z3.Implies(z3.And(invariant, z3.Not(condition)), postcondition) // I -> postcondition при выходе из цикла
    );
}