import { ReversePolishNotationActionDict } from "./rpn.ohm-bundle";

export const rpnStackDepth = {
    // число занимает одну ячейку в стеке
    RpnExpr_number(n) { 
        return { max: 1, out: 1 }; 
    },

    /* ПРИМЕР "3 4 +"
    a = 3: A.out = 1, A.max = 1
    b = 4: B.out = 1, B.max = 1

    вычисляю a: стек = [3], глубина = 1
    b: стек = [3, 4], глубина = 2
    +: стек = [7], глубина = 1
    out = A.out + B.out - 1 = 1 + 1 - 1 = 1
    max = Math.max(A.max, A.out + B.max) = max(1, 1 + 1) = max(1, 2) = 2
    */
    RpnExpr_plus(a, b, plus) {
        const A = a.stackDepth;
        const B = b.stackDepth;

        // суммирую выходные значения обоих операндов и -1 (тк операция потребляет 2 значения и производит 1)
        const out = A.out + B.out - 1;
        /*
        после вычисления a в стеке остается A.out значений. Максимальная глубина стека при вычислении a: A.max
        
        при вычислении b стек достигает глубины A.out+B.max значений
        после вычисления b в стеке остается A.out+B.out значений
        
        если бы было значение c, то было бы макисмум значений: A.out+B.out+C.max
        */
        const max = Math.max(A.max, A.out + B.max);

        return { max, out };
    },
    
    RpnExpr_mult(a, b, mult) {
        const A = a.stackDepth;
        const B = b.stackDepth;

        const out = A.out + B.out - 1;
        const max = Math.max(A.max, A.out + B.max);

        return { max, out };
    },
} satisfies ReversePolishNotationActionDict<StackDepth>;

// max - максимальная глубина стека достигаемая в процессе вычисления выражения
// out - количество значений которые остаются в стеке после вычисления выражения
export type StackDepth = {max: number, out: number};
