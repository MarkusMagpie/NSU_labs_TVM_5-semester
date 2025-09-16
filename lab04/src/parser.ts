import { MatchResult } from 'ohm-js';
import { arithGrammar, ArithmeticActionDict, ArithmeticSemantics, SyntaxError } from '../../lab03';
import { Expr } from './ast';

export const getExprAst: ArithmeticActionDict<Expr> = {
    Expr(expr) { return expr.parse(); },
  
    /*
    AddExp(first, operator, rest) {
        let res = first.calculate(this.args.params);
        const n = operator.children.length;
        for (let i = 0; i < n; i++) {
            const op = operator.child(i).sourceString;
            const rightVal = rest.child(i).calculate(this.args.params);
            switch (op) {
                case '+': 
                    res += rightVal;
                    break;
                case '-': 
                    res -= rightVal;
                    break;
            }
            // res = op === '+' ? res + rightVal : res - rightVal;
        }

        return res;
    },
    */

    AddExp(first, operators, rest) {
        let acc: Expr = first.parse();
        const n = operators.children.length;
        
        for (let i = 0; i < n; i++) {
            const op = operators.child(i).sourceString;
            const operation = op as '+' | '-';
            const rhs: Expr = rest.child(i).parse();
            acc = { type: 'bin', operation, left: acc, right: rhs };
        }
        
        return acc;
    },
  
    MulExp(first, operators, rest) {
        let acc: Expr = first.parse();
        const n = operators.children.length;
      
        for (let i = 0; i < n; i++) {
            const op = operators.child(i).sourceString;
            const operation = op as '*' | '/';
            const rhs: Expr = rest.child(i).parse();
            acc = { type: 'bin', operation, left: acc, right: rhs };
        }
      
        return acc;
    },

    /*
    PriExp_number(num) { return num.calculate(this.args.params); },
    PriExp_unary_minus(minus, expr) { return -expr.calculate(this.args.params); },
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
    */
    
    PriExp_number(num) { return num.parse(); },
    PriExp_unary_minus(minus, expr) { return { type: 'neg', arg: expr.parse() }; },
    PriExp_variable(varNode) {
        return { type: 'var', name: varNode.sourceString };
    },
    PriExp_paren(open_paren, expr, close_paren) { return expr.parse(); },
  
    number_fract(whole, dot, digits) {
        return { type: 'num', value: parseFloat(this.sourceString) };
    },
    number_whole(whole, digits) {
        return { type: 'num', value: parseInt(this.sourceString, 10) };
    },
    number_zero(a) {
        return { type: 'num', value: 0 };
    },
};

export const semantics = arithGrammar.createSemantics();
semantics.addOperation("parse()", getExprAst);

export interface ArithSemanticsExt extends ArithmeticSemantics
{
    (match: MatchResult): ArithActionsExt
}

export interface ArithActionsExt 
{
    parse(): Expr
}

// passes the input string through the grammar and builds the AST using the semantic action parse()
export function parseExpr(source: string): Expr
{
    const matchResult = arithGrammar.match(source, "Expr");

    if (!matchResult.succeeded()) {
        throw new SyntaxError(matchResult.message);
    }
  
    return semantics(matchResult).parse();
}


    
