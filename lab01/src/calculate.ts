import { Dict, MatchResult, Semantics } from "ohm-js";
import grammar, { AddMulActionDict } from "./addmul.ohm-bundle";

/* 
1. To associate a set of semantic actions with a particular grammar (в моем случае AddMul), we first need to create a 
Semantics object for that grammar, using its createSemantics() method:
*/
export const addMulSemantics: AddMulSemantics = grammar.createSemantics() as AddMulSemantics;

const addMulCalc = {
    Expr(input) { return input.calculate(); },

    AddExp_plus(left, plus, right) { return left.calculate() + right.calculate(); },
    AddExp(mulExp) { return mulExp.calculate(); },

    MulExp_times(left, _star, right) { return left.calculate() * right.calculate(); },
    MulExp(priExp) { return priExp.calculate(); },

    PriExp_number(num) { return num.calculate(); },
    PriExp_paren(_open_paren, expr, _close_paren) { return expr.calculate(); },

    number_fract(whole, dot, digits) {
        return parseFloat(this.sourceString);
    },
    number_whole(whole, digits) {
        return parseInt(this.sourceString, 10);
    },
    number_zero(a) {
        return 0;
    },
} satisfies AddMulActionDict<number>

/*
2. Then, we add a new operation to the semantics, by calling its addOperation method with an action dictionary as the argument
*/
addMulSemantics.addOperation<Number>("calculate()", addMulCalc);

interface AddMulDict  extends Dict {
    calculate(): number;
}

interface AddMulSemantics extends Semantics
{
    (match: MatchResult): AddMulDict;
}
