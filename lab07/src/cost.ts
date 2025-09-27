import { Expr } from "../../lab04";

export function cost(e: Expr): number
{
    // throw "Not implemented";
    switch(e.type) {
        case 'num':
            return 0;
        case 'var':
            return 1;
        case 'neg':
            // test("unary minus cost is one", 3, estimate, 2, "-x");
            return cost(e.arg) + 1;
        case 'bin':
            return cost(e.left) + cost(e.right) + 1;
    }
}