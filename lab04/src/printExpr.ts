import { Expr, Binary } from "./ast";

function getOperationPriority(e: Expr): number {
    switch (e.type) {
        case 'num': return 0;
        case 'var': return 4;
        case 'neg': return 3;
        case 'bin': 
            switch(e.operation) {
                case '+': return 1;
                case '-': return 1;
                case '*': return 2;
                case '/': return 2;
        }
    }
}

function getOperationPriority2(op: Binary['operation']): number {
    switch (op) {
        case '+': return 1;
        case '-': return 1;
        case '*': return 2;
        case '/': return 2;
    }
}

// нужно ли заключать выражение child в parenthesis?
function needParens(child: Expr, parentOperation: Binary['operation'], isRightChild: boolean): boolean {
    if (child.type !== 'bin') return false;

    const childPriority = getOperationPriority(child);
    const parentPriority = getOperationPriority2(parentOperation);

    // приоритет дочернего выражения выше -> скобки не нужны
    if (childPriority > parentPriority) return false;
    if (childPriority < parentPriority) return true;

    // для сложения скобки никогда не нужны - тест "Parentheses are removed from addition"
    if (parentOperation === '+') return false;
    // для вычитания скобки нужны только для правого операнда с операцией сложения
    // Associativity can be overriden via parentheses: expected: "5 + 2 - (4 + 3) - 1"; given: "(5+2)-(4+3)-1"
    
    // новое: expected: "5 - (4 - 3)"; given: "5-(4-3)"
    if (parentOperation === '-') return isRightChild;
    
    return isRightChild;
}

// тут встроенная рекурсивная функция с доп параметрами
// в isRightChild установил дефолт значение так как единственное место использования - в index.ts и там 1 параметр: e
function printExprRecursive(e: Expr, parentOperation?: Binary['operation'], isRightChild: boolean = false): string {
    switch (e.type) {
        case "num":
            return e.value.toString();
        case "var":
            return e.name;
        case "neg":
            return `-${printExprRecursive(e.arg)}`;
        case "bin":
            // return `${printExpr(e.left)} ${e.op} ${printExpr(e.right)}`;
            // обрабатываю левую и правую части бинарного выражения алалогично данному e
            const leftStr = printExprRecursive(e.left, e.operation, false);
            const rightStr = printExprRecursive(e.right, e.operation, true);
            const str = `${leftStr} ${e.operation} ${rightStr}`;
            
            // нужны ли скобки в бинарном выражении?
            if (parentOperation && needParens(e, parentOperation, isRightChild)) {
                return `(${str})`;
            }
            
            return str;
    }
}

export function printExpr(e: Expr): string {

    return printExprRecursive(e);
}
