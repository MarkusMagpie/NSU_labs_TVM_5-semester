import { Dict, MatchResult, Semantics } from "ohm-js";
import grammar from "./rpn.ohm-bundle";
import { rpnStackDepth, StackDepth } from "./stackDepth";
import { rpnCalc } from "./calculate";

interface RpnDict  extends Dict {
    // calculate(): number;
    evaluate(): number;
    stackDepth: StackDepth;
    maxStackDepth(): number;
}

interface RpnSemantics extends Semantics
{
    (match: MatchResult): RpnDict;
}

export const rpnSemantics: RpnSemantics = grammar.createSemantics() as RpnSemantics;
// rpnSemantics.addOperation<number>("calculate()", rpnCalc);
rpnSemantics.addOperation<number>("evaluate()", {
    Expr(input) { return input.evaluate(); },

    RpnExpr_plus(a, b, plus) { return a.evaluate() + b.evaluate(); },
    RpnExpr_mult(a, b, times) { return a.evaluate() * b.evaluate(); },
    RpnExpr_number(input) { return input.evaluate(); },
    
    number_fract(whole, dot, digits) {
        return parseFloat(this.sourceString);
    },
    number_whole(whole, digits) {
        return parseInt(this.sourceString, 10);
    },
    number_zero(a) {
        return 0;
    },
});

// returns the max stack depth required for a valid RPN expression or throws a `SyntaxError` for an invalid input
rpnSemantics.addOperation<number>("maxStackDepth()", {
    Expr(expr) { return expr.maxStackDepth(); },
    RpnExpr_plus(a, b, plus) { return this.stackDepth.max; },
    RpnExpr_mult(a, b, times) { return this.stackDepth.max; },
    RpnExpr_number(num) { return this.stackDepth.max; },
});
rpnSemantics.addAttribute<StackDepth>("stackDepth", rpnStackDepth);