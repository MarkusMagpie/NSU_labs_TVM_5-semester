import {  MatchResult } from "ohm-js";
import { addMulSemantics } from "./calculate";
import grammar from "./addmul.ohm-bundle";

export function evaluate(content: string): number
{
    return calculate(parse(content));
}
export class SyntaxError extends Error
{
}

/*
We can use the grammar object's match() method to recognize arithmetic expressions in our library. 
match returns a MatchResult object which (among other things) has a succeeded() method.
*/
function parse(content: string): MatchResult {
    const matchResult = grammar.match(content, "Expr");

    // проверка необходима для проверки валидности кода (7/18 тестов)
    if (!matchResult.succeeded()) {
        throw new SyntaxError();
    }

    return matchResult;
}
  
function calculate(expression: MatchResult): number {
    return addMulSemantics(expression).calculate();
}