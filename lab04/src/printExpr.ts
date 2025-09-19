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

// является ли выражение бинарной операцией содержащей типы operation?
function isBinOperation(e: Expr, operations: Array<Binary['operation']>): e is Binary {
    return e.type === 'bin' && operations.includes(e.operation);
}

// нужно ли заключать выражение child в скобки?
// isRightChild - является ли дочернее выражение правым операндом
function needParens(child: Expr, parentOperation: Binary['operation'], isRightChild: boolean): boolean {
    if (child.type !== 'bin') return false;

    const childPriority = getOperationPriority(child);
    const parentPriority = (parentOperation === '+' || parentOperation === '-') ? 1 : 2;

    // приоритет дочернего выражения выше -> скобки не нужны
    if (childPriority > parentPriority) return false;
    else if (childPriority < parentPriority) return true;
    else {
        // для сложения скобки никогда не нужны - тест "Parentheses are removed from addition"
        if (parentOperation === '+') { return false; }
        // Associativity can be overriden via parentheses: expected: "5 + 2 - (4 + 3) - 1"; given: "(5+2)-(4+3)-1"
        if (parentOperation === '-') return isRightChild && isBinOperation(child, ['+']);
        
        return isRightChild;
    }
}

// в isRightChild установил дефолт значение так как единственное место использования - в index.ts и там 1 параметр: e
export function printExpr(e: Expr, parentOperation?: Binary['operation'], isRightChild: boolean = false):string
{
    switch (e.type) {
        case "num":
            return e.value.toString();
        case "var":
            return e.name;
        case "neg":
            return `-${printExpr(e.arg)}`;
        case "bin":
            // return `${printExpr(e.left)} ${e.op} ${printExpr(e.right)}`;
            // обрабатываю левую и правую части бинарного выражения алалогично данному e
            const leftStr = printExpr(e.left, e.operation, false);
            const rightStr = printExpr(e.right, e.operation, true);
            const str = `${leftStr} ${e.operation} ${rightStr}`;
            
            if (parentOperation && needParens(e, parentOperation, isRightChild)) {
                return `(${str})`;
            }
            
            return str;
        
    }
}
