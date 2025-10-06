import { Expr } from "../../lab04";

/*
- `x * 0 = 0 * x = 0`
- `x * 1 = 1 * x = x`
- `x / 1 = x`
- `x + 0 = 0 + x = x`
- `x - 0 = x`
- `0 - x = -x`
- `--x = x`
*/
function simplify(e: Expr): Expr {
    let simplified: Expr;

    switch (e.type) {
        case 'num':
            simplified = e;
            break;
        case 'var':
            simplified = e;
            break;
        case 'neg':
            const arg = simplify(e.arg);

            // test("Constant derives to zero 2", 4, parseAndDerive, parseExpr("0"), "-42", "x");
            if (arg.type === 'num') {
                return arg.value === 0 ? { type: 'num', value: 0 } : { type: 'neg', arg };
            }
            if (arg.type === 'neg') {
                return arg.arg;
            }

            simplified = { type: 'neg', arg };
            break;
        case 'bin':
            const left = simplify(e.left);
            const right = simplify(e.right);
            simplified = { type: 'bin', operation: e.operation, left, right };
            if (e.operation === '*') {
                // `x * 0 = 0 * x = 0`
                if (isZero(right) || isZero(left)) return { type: 'num', value: 0 };
                // `x * 1 = 1 * x = x`
                if (isOne(right)) return left;
                if (isOne(left)) return right;
            } else if (e.operation === '/') {
                // `0 / x = 0`
                if (isZero(left)) return { type: "num", value: 0 };
                // `x / 1 = x`
                if (isOne(right)) return left;
                // `-x / y = neg(x / y)`
                if (left.type === 'neg') {
                    return simplify({ type: 'neg', arg: { type: 'bin', operation: '/', left: left.arg, right: right } });
                }
                // `x / -y = neg(x / y)`
                if (right.type === 'neg') {
                    return simplify({ type: 'neg', arg: { type: 'bin', operation: '/', left: left, right: right.arg } });
                }
            } else if (e.operation === '+') {
                // `x + 0 = 0 + x = x`
                if (isZero(right)) return left;
                if (isZero(left)) return right;
            } else if (e.operation === '-') {
                // `x - 0 = x`
                if (isZero(right)) return left;
                // `0 - x = -x`
                if (isZero(left)) {
                    // console.log(left, e.operation, right);
                    // 0 - neg(x) = 0 - (-x) = x
                    // if (right.type == "neg") {
                    //     return right.arg;                
                    // }
                    return simplify({ type: "neg", arg: right });
                }
            }
            break;
    }

    return simplified;
}

/*
varName - имя переменной по которой вычисляется производная. 
При символьном дифференцировании вычисляется производная выражения по конкретной переменной - это именно varName
*/
export function derive(e: Expr, varName: string): Expr
{
    // throw "Not implemented";
    let result: Expr;
    switch(e.type) {
        case 'num':
            // производная константы равна нулю
            result = {type: 'num', value: 0};
            break;
        case 'var':
            result = {type: 'num', value: e.name === varName ? 1 : 0};
            break;
        case 'neg':
            // result = {type: 'num', value: e.arg.type === 'var' && e.arg.name === varName ? -1 : 0};
            result = {type: 'neg', arg: derive(e.arg, varName)};
            break;
        case 'bin':
            // производная бинарных операций
            const left = e.left;
            const right = e.right;
            const difLeft = derive(left, varName);
            const difRight = derive(right, varName);
            
            switch (e.operation) {
                case '+':
                    // d(u+v)/dx = du/dx + dv/dx
                    result = { type: 'bin', operation: '+', left: difLeft, right: difRight };
                    break;
                case '-':
                    // d(u-v)/dx = du/dx - dv/dx
                    result = { type: 'bin', operation: '-', left: difLeft, right: difRight };
                    break;
                case '*':
                    // d(u*v)/dx = u*dv/dx + v*du/dx
                    result = { type: 'bin', operation: '+',
                        // вот это неправильно - от перемены мест слагаемых сумма видимо разная
                        // left: { type: 'bin', operation: '*', left: left, right: difRight },
                        // right: { type: 'bin', operation: '*', left: right, right: difLeft }
                        left: { type: 'bin', operation: '*', left: difLeft, right: right },
                        right: { type: 'bin', operation: '*', left: difRight, right: left }
                    };
                    break;
                case '/':
                    // d(u/v)/dx = (v*du/dx - u*dv/dx) / (v^2 <=> v*v)
                    result = { type: 'bin', operation: '/',
                        left: { type: 'bin', operation: '-',
                            left: { type: 'bin', operation: '*', left: right, right: difLeft },
                            right: { type: 'bin', operation: '*', left: left, right: difRight }
                        },
                        right: { type: 'bin', operation: '*', left: right, right: right }
                    };
                    break;
            }
    }

    return simplify(result);
}

function isZero(e: Expr): boolean { 
    // throw "Not implemented"
    return e.type === 'num' && e.value === 0;
}

function isOne(e: Expr): boolean  { 
    // throw "Not implemented"
    return e.type === 'num' && e.value === 1;
}
