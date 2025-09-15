import {  MatchResult } from "ohm-js";
import grammar  from "./arith.ohm-bundle";
import { arithSemantics } from "./calculate";

export const arithGrammar = grammar;
export {ArithmeticActionDict, ArithmeticSemantics} from './arith.ohm-bundle';

export function evaluate(content: string, params?: {[name:string]:number}): number
{
    return calculate(parse(content), params ?? {});
}
export class SyntaxError extends Error
{
}

export function parse(content: string): MatchResult
{
    // throw "Not implemented";
    const matchResult = grammar.match(content, "Expr");

    // проверка необходима для проверки валидности кода (7/18 тестов)
    if (!matchResult.succeeded()) {
        throw new SyntaxError();
    }

    return matchResult;
}

//calculate(params: {[name:string]:number}): number; - сигнатура метода 
function calculate(expression: MatchResult, params: {[name:string]: number}): number
{
    // throw "Not implemented";
    return arithSemantics(expression).calculate(params);
}