import { MatchResult } from "ohm-js";
import grammar, { ArithmeticActionDict, ArithmeticSemantics } from "./arith.ohm-bundle";

export const arithSemantics: ArithSemantics = grammar.createSemantics() as ArithSemantics;


const arithCalc = {
    //  семантические правила пиши здесь
    Expr(expr) { return expr.calculate(this.args.params); },

    // ЛЕВОРЕКУРСИВНОЕ РЕШЕНИЕ
    AddExp_binary(left, op, right) {
        // вызывается семантическая опреация calculate(params) -> для доступа к params пишу this.args.paramss
        const leftVal = left.calculate(this.args.params);
        const rightVal = right.calculate(this.args.params);
        switch (op.sourceString) {
            case '+': return leftVal + rightVal;
            case '-': return leftVal - rightVal;
            default: throw new Error();
        }
    },
    AddExp(mulExp) { return mulExp.calculate(this.args.params); },

    // AddExp(first, rest, aux) {
    //     let res = first.calculate(this.args.params);
    //     for (let i = 0; i < rest.children.length; i++) {
    //         const op = rest.children[i][0]; 
    //         const right = rest.children[i][1]; 
    //         const rightVal = right.calculate(this.args.params);

    //         switch (op) {
    //             case '+': res += rightVal;
    //             case '-': res -= rightVal;
    //             default: throw new Error();
    //         }
    //     }

    //     return res;
    // },

    // ЛЕВОРЕКУРСИВНОЕ РЕШЕНИЕ
    MulExp_binary(left, op, right) {
        const leftVal = left.calculate(this.args.params);
        const rightVal = right.calculate(this.args.params);
        switch (op.sourceString) {
            case '*': return leftVal * rightVal;
            case '/': 
                if (rightVal === 0) {
                    throw new Error("аниче тот факт што на ноль делить нельзя");
                }
                return leftVal / rightVal;
            default: throw new Error();
        }
    },
    MulExp(mulExp) { return mulExp.calculate(this.args.params); },

    // MulExp(first, rest, auxilary) {
    //     let res = first.calculate(this.args.params);
    //     for (let i = 0; i < rest.length; i++) {
    //         const op = rest[i][0]; 
    //         const right = rest[i][1]; 
    //         const rightVal = right.calculate(this.args.params);
            
    //         switch (op.sourceString) {
    //             case '*': res *= rightVal; 
    //             case '/': 
    //                 if (rightVal === 0) {
    //                     throw new Error("аниче тот факт што на ноль делить нельзя");
    //                 }
    //                 res /= rightVal;
    //             default: throw new Error();
    //         }
    //     }
    //     return res;
    // },

    PriExp_number(num) { return num.calculate(this.args.params); },
    PriExp_unary_minus(minus, _, expr) { return -expr.calculate(this.args.params); },
    PriExp_variable(name) {
        const varName = this.sourceString;
        // console.log(varName);
        // дано: evaluate("x + 1", {x: 41}); this.args.params = {x: 41} 
        // this.args !== this.args.params
        // была липеременная передана в параметрах?
        if (this.args.params && this.args.params[varName] !== undefined) {
            return this.args.params[varName];
        }

        return NaN; 
    },
    PriExp_paren(open_paren, expr, close_paren) { return expr.calculate(this.args.params); },

    number_fract(whole, dot, digits) {
        return parseFloat(this.sourceString);
    },
    number_whole(whole, digits) {
        return parseInt(this.sourceString, 10);
    },
    number_zero(a) {
        return 0;
    },
} satisfies ArithmeticActionDict<number | undefined>;


arithSemantics.addOperation<Number>("calculate(params)", arithCalc);


export interface ArithActions {
    calculate(params: {[name:string]:number}): number;
}

export interface ArithSemantics extends ArithmeticSemantics
{
    (match: MatchResult): ArithActions;
}
