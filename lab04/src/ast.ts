export type Expr = Number | Variable | Negative | Binary;

export interface Number {
    type: 'num';
    value: number;
}

export interface Variable {
    type: 'var';
    name: string;
}

export interface Negative {
    type: 'neg';
    arg: Expr;
}

export interface Binary {
    type: 'bin';
    left: Expr;
    operation: '+' | '-' | '*' | '/';
    right: Expr;
}