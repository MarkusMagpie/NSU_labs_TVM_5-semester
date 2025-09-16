export type Expr = Num | Var | Neg | Bin;

export interface Num {
    type: 'num';
    value: number;
}

export interface Var {
    type: 'var';
    name: string;
}

export interface Neg {
    type: 'neg';
    arg: Expr;
}

export interface Bin {
    type: 'bin';
    operation: '+' | '-' | '*' | '/';
    left: Expr;
    right: Expr;
}