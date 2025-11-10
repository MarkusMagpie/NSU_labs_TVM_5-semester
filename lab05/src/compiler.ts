import { c as C, Op, I32 } from "@tvm/wasm";
import { Expr } from "@tvm/lab04";
import { buildOneFunctionModule, Fn } from "./emitHelper";
const { i32, get_local} = C;

function collectVariables(e: Expr, variables: string[]) {
    switch(e.type) {
        case 'num':
            // в числах переменных нема
            break;
        case 'var':
            // если ещё нет в списке -> добавляю
            if (!variables.includes(e.name)) {
                variables.push(e.name);
            }
            break;
        case 'neg':
            collectVariables(e.arg, variables);
            break;
        case 'bin':
            collectVariables(e.left, variables);
            collectVariables(e.right, variables);
            break;
    }
}
    
export function getVariables(e: Expr): string[] {
    // throw "Not implemented";
    let variables: string[] = [];

    collectVariables(e, variables);

    return variables;
}

export async function buildFunction(e: Expr, variables: string[]): Promise<Fn<number>>
{
    let expr = wasm(e, variables)
    return await buildOneFunctionModule("test", variables.length, [expr]);
}

function wasm(e: Expr, args: string[]): Op<I32> {
    // throw "Not implemented";
    switch (e.type) {
        case 'num':
            return i32.const(e.value);
        case 'var':
            const index = args.indexOf(e.name);
            if (index === -1) {
                throw new Error();
            }

            return get_local(i32, index);
        case 'neg':
            return i32.mul(i32.const(-1), wasm(e.arg, args));
        case 'bin':
            switch (e.operation) {
                case '+': return i32.add(wasm(e.left, args), wasm(e.right, args));
                case '-': return i32.sub(wasm(e.left, args), wasm(e.right, args));
                case '*': return i32.mul(wasm(e.left, args), wasm(e.right, args));
                case '/': return i32.div_s(wasm(e.left, args), wasm(e.right, args));
            }
    }
}
