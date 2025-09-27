import { Expr } from "../../lab04";
// дополнительно импортирую функцию cost
import { cost } from "./cost";



/* функция проверки совпадения двух выражений
    output: 
        null если не совпадают; 
        иначе: словарь показывающий каким выражениям соответствуют переменные в шаблоне pattern; 

        exampple:
            match("x+0", "a+0") => { x: "a" } - переменная x соответсвует выражению а
*/

/* ВАЖНО: сначала проверяю на тип шаблона "var" а потом сверяю типы шаблона и входящего выражения

    потму что переменная в шаблоне есть ЛЮБОЕ выражение независимо от типа

    example:
        pattern: x - var
        expr: a+0 - bin
        если сначала сверить тип шаблона и входящего выражения, то будет возвращено null, но output должен быть { x: "a+0" }
*/
function match(pattern: Expr, expr: Expr): { [key: string]: Expr } | null {
    if (pattern.type === 'var') {
        return { [pattern.name]: expr };
    }

    if (pattern.type !== expr.type) return null;

    switch (pattern.type) {
        case 'num':
            // сравнение значений двух чисел
            const num_expr = expr as any;
            return pattern.value === num_expr.value ? {} : null;
        // case 'var':
        //     // если шаблон переменная то связываю её имя с выражением
        //     return { [pattern.name]: expr };
        case 'neg':
            // рекурсивно проверка совпадения аргументов
            const neg_expr = expr as any;
            return match(pattern.arg, neg_expr.arg);
        case 'bin':
            const bin_expr = expr as any;
            // сначала проверка что операции совпадают
            if (pattern.operation !== bin_expr.operation) return null;

            const left_match = match(pattern.left, bin_expr.left);
            const right_match = match(pattern.right, bin_expr.right);
            
            if (left_match && right_match) {
                // если оба утверждения верны то возвращаю их объединение
                return { ...left_match, ...right_match };   
            } else {
                return null;
            }
        default: 
            return null;
    }
}
 
/* берется expr_to_replace и в него подставляются значения переменных из словаря от match()
    example:
        replace("x", { x: "a" }) => "a"
*/
function replace(expr: Expr, match_res: { [key: string]: Expr }): Expr {
    switch (expr.type) {
        case 'num':
            return expr;
        case 'var':
            // если есть подстановка для этой переменной беру, иначе возвращаю саму переменную
            return match_res[expr.name] || expr;
        case 'neg':
            return {
                type: 'neg',
                arg: replace(expr.arg, match_res)
            };
        case 'bin':
            return {
                type: 'bin',
                operation: expr.operation,
                left: replace(expr.left, match_res),
                right: replace(expr.right, match_res)
            };
        default:
            return expr;
    }
}

/* ЛОГИКА РАБОТЫ SIMPLIFY:
    имеем тождество identity из набора тождеств identities - это пара [pattern, expr_to_replace]
    хотим проверить соответствует ли выражение result pattern-у
    если да то заменяю pattern на expr_to_replace, но при этом 
        заменяются переменные в expr_to_replace на те выражения, 
        которые были сопоставлены с переменными из pattern-а
*/
export function simplify(e: Expr, identities: [Expr, Expr][]): Expr
{
    let result: Expr;
    switch(e.type) {
        case "num":
            return e;
        case "var":
            return e;
        case "neg":
            result = {
                type: "neg",
                arg: simplify(e.arg, identities)
            };
            break;
        case "bin":
            result = {
                type: 'bin',
                operation: e.operation,
                left: simplify(e.left, identities),
                right: simplify(e.right, identities)
            };
            break;
    }

    // тождества из identities применяюся к выражению result пока есть улучшения
    let changed: boolean = true;
    while (changed) {
        changed = false;
        const current_cost = cost(result);

        for (const identity of identities) {
            const pattern = identity[0];
            const expr_to_replace = identity[1];

            // проверка соответствия выражения result pattern-у
            let match_res = match(pattern, result);
            if (match_res !== null) {
                const new_result = replace(expr_to_replace, match_res);
                const new_cost = cost(new_result);
                
                if (new_cost <= current_cost) {
                    result = new_result;
                    changed = true;
                    break; // чтобы начать заново с измененным выражением result
                }
            }
        }
    }

    return result;
}