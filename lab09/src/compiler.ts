import { writeFileSync } from "fs";
import { Op, I32, Void, c, BufferedEmitter, LocalEntry, Uint8, Int} from "../../wasm";
import { Module, Statement, Expr, LValue } from "../../lab08";

const { i32, 
    varuint32,
    get_local, local_entry, set_local, call, if_, void_block, void_loop, br_if, str_ascii, export_entry,
    func_type_m, function_body, type_section, function_section, export_section, code_section } = c;
  
export async function compileModule<M extends Module>(m: M, name?: string): Promise<WebAssembly.Exports>
{
    const emitter = new BufferedEmitter(new ArrayBuffer(0));
    
    // секция сигнатур функций 
    const typeSection: any[] = [];
    // секция индексов типов для каждой функции
    const functionSection: any[] = [];
    // секция экспортируемых функций по именам
    const exportSection: any[] = [];
    // секция тел функций с локальными перем
    const codeSection: any[] = [];

    // для быстрого доступа к индексам функций
    const functionIndexMap = new Map<string, number>();

    // 1 - создание типов функций и мапы индексов
    for (let i = 0; i < m.functions.length; i++) {
        const func = m.functions[i];

        functionIndexMap.set(func.name, i);
        
        // тип функции: параметры и возвращаемые значения - все i32
        const paramTypes = func.parameters.map(() => i32);
        const returnTypes = func.returns.map(() => i32);
        
        typeSection.push(c.func_type_m(paramTypes, returnTypes));
        functionSection.push(c.varuint32(i)); 
        exportSection.push(c.export_entry(c.str_ascii(func.name), 0 as any as Uint8, c.varuint32(i)));
    }

    // 2 - генерация тела функций
    for (let i = 0; i < m.functions.length; i++) {
        const func = m.functions[i];
        
        const allLocals: string[] = [
            ...func.parameters.map(p => p.name),
            ...func.returns.map(r => r.name),
            ...func.locals.map(l => l.name)
        ];

        // записи локальных переменных с типом i32
        // const localEntries: LocalEntry[] = allLocals.map(() => local_entry(varuint32(1), i32));
        const localEntries: LocalEntry[] = [
            c.local_entry(c.varuint32(allLocals.length), i32)
        ];

        // обработка тела функции
        const bodyOps: (Op<Void> | Op<I32>)[] = compileStatement(func.body, allLocals, functionIndexMap);

        // возвращаемые значения на стек
        for (const ret of func.returns) {
            const index = allLocals.indexOf(ret.name);
            bodyOps.push(get_local(i32, index));
        }

        codeSection.push(c.function_body(localEntries, bodyOps));
    }

    // создаие модуля WASM из всех секций
    // const mod = c.module([
    //     c.type_section(typeSection), // передача заполненной секции сигнатур функций
    //     c.function_section(functionSection),
    //     c.export_section(exportSection),
    //     c.code_section(codeSection)
    // ]);
    const mod = c.module([
        c.type_section(typeSection.map((type, index) => c.func_type(type.parameters, type.returns))),
        c.function_section(functionSection.map(index => c.varuint32(index))),
        c.export_section(exportSection.map(exp => c.export_entry(exp.field, exp.kind, exp.index))),
        c.code_section(codeSection)
    ]);
    mod.emit(emitter); // запись модуля в буфер
    // компиляция WebAssembly модуля
    const wasmModule = await WebAssembly.instantiate(emitter.buffer);
    // возвращаю экспорты модуля
    return wasmModule.instance.exports;
}



// export type Expr = arith.Expr | FuncCallExpr | ArrAccessExpr;
function compileExpr(expr: Expr, locals: string[], functionIndexMap: Map<string, number>): Op<I32> {
    switch (expr.type) {
        case "num":
            return i32.const(expr.value);
        case "var":
            const index = locals.indexOf(expr.name);
            return get_local(i32, index);
        case "neg":
            return i32.mul(i32.const(-1), compileExpr(expr.arg, locals, functionIndexMap));
        case "bin":
            const left = compileExpr(expr.left, locals, functionIndexMap);
            const right = compileExpr(expr.right, locals, functionIndexMap);
            switch (expr.operation) {
                case '+': return i32.add(left, right);
                case '-': return i32.sub(left, right);
                case '*': return i32.mul(left, right);
                case '/': return i32.div_s(left, right);
                default: throw new Error("провер бинарнуб операцию");
            }
        case "funccall":
            const args = expr.args.map(arg => compileExpr(arg, locals, functionIndexMap));
            const funcIndex = functionIndexMap.get(expr.name);
            // get() возвращает number | undefined -> нужна проверка
            if (funcIndex === undefined) {
                throw new Error(`unknown function: ${expr.name}`);
            }
            return call(i32, c.varuint32(funcIndex), args);
        case "arraccess":
            throw new Error("Array access TODO");
        default:
            throw new Error(`unknown expr type: ${(expr as any).type}`);
    }
}

// export type LValue = VarLValue | ArrLValue;
// возвращается объект с двумя методами - для записи значения и его чтения
function compileLValue(lvalue: LValue, locals: string[]): 
    {   set: (value: Op<I32>) => Op<Void>, 
        get: () => Op<I32> } {
    switch (lvalue.type) {
        case "lvar":
            const index = locals.indexOf(lvalue.name);
            return {
                /*
                операция изменения значения переменной
                */
                set: (value: Op<I32>) => c.set_local(index, value),
                /*
                операция получения доступа к значению переменной 
                    по WASM: загрузить значение переменной на стек, чтобы его можно 
                    было использовать
                */
                get: () => c.get_local(i32, index)
            };
        case "larr":
            const arrayIndex = locals.indexOf(lvalue.name);
            const indexExpr = compileExpr(lvalue.index, locals, new Map());

            // базовый адрес массива
            const baseAddress = c.get_local(i32, arrayIndex);
            
            // вычисляю адрес элемента: baseAddress + index * 4 (каждый int=4)
            const elementOffset = i32.mul(indexExpr, i32.const(4));
            const elementAddress = i32.add(baseAddress, elementOffset);

            return {
                set: (value: Op<I32>) => {
                    // схранение значения по вычисленному адресу в памяти
                    return i32.store(
                        [c.varuint32(4), 0 as any as Int],
                        elementAddress,
                        value
                    );
                },
                get: () => {
                    return i32.load(
                        [c.varuint32(4), 0 as any as Int],
                        elementAddress
                    );
                }
            };
        default:
            throw new Error("неизвестный тпи lvalue");
    }
}

// export type Statement = AssignStmt | BlockStmt | ConditionalStmt | WhileStmt;
function compileStatement(stmt: Statement, locals: string[], functionIndexMap: Map<string, number>): Op<Void>[] {
    const ops: Op<Void>[] = []; // предполагаемый массив инструкций WASM
    
    switch (stmt.type) {
        case "block":
            for (const sub of stmt.stmts) {
                ops.push(...compileStatement(sub, locals, functionIndexMap));
            }
            break;
        case "assign":
            // 1 - вычисление всех выражений справа от равенства
            const exprValues: Op<I32>[] = [];
            for (const expr of stmt.exprs) {
                exprValues.push(compileExpr(expr, locals, functionIndexMap));
            }
            
            // присвоение значения exprValues целевым переменным targets
            for (let i = stmt.targets.length - 1; i >= 0; i--) {
                const target = stmt.targets[i];
                const lvalue = compileLValue(target, locals);
                ops.push(lvalue.set(exprValues[i]));
            }
            break;
        case "if":
            throw new Error("If statement TODO");
        case "while":
            throw new Error("While statement TODO");
        default:
            throw new Error("Unknown type of statement");
    }
    
    return ops;
}

export { FunnyError } from '../../lab08'