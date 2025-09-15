import grammar from "./rpn.ohm-bundle";
import { rpnSemantics } from "./semantics";

export class SyntaxError extends Error {}

export function evaluate(source: string): number
{ 
    // throw "Not implemented";
    const matchResult = grammar.match(source);
    if (!matchResult.succeeded()) {
        throw new SyntaxError();
    }

    return rpnSemantics(matchResult).evaluate();
}

export function maxStackDepth(source: string): number
{ 
    // throw "Not implemented";
    const matchResult = grammar.match(source);
    if (!matchResult.succeeded()) {
        throw new SyntaxError();
    }

    return rpnSemantics(matchResult).maxStackDepth();
}
