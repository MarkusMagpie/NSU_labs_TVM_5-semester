
Funny <: Arithmetic {
    // write rules here
    Module = Function+

    Function = variable 
        "(" ParamList ")" 
        Preopt? 
        "returns" ParamListNonEmpty 
        UsesOpt? 
        Statement

    ParamList = ListOf<Param, ",">
    ParamListNonEmpty = ListOf<Param, ",">
    Param = variable ":" Type
    Preopt = "requires" Predicate 
    UsesOpt = "uses" ParamList 

    Type = "int" "[]" -- array
        | "int" -- int

    // В Funny есть четыре типа операторов: присваивание, блок, условный оператор, цикл. 
    Statement = Assignment
        | Block
        | Conditional
        | While
        | FunctionCall ";" -- function_call_statement
    // прсваивание - обращение к массиву или кортежное присваивание из вызова функции
    Assignment = LValueList "=" ExprList ";"    -- tuple_assignment
        | LValue "=" Expr ";"                   -- simple_assignment
    LValueList = ListOf<LValue, ",">
    ExprList = ListOf<Expr, ",">
    // LValue - имя переменной или обращение к массиву
    LValue = variable "[" Expr "]"              -- array_access
        | variable                               -- variable
    // блок
    Block = "{" Statement* "}"
    // условный опреатор
    Conditional = "if" "(" Condition ")" Statement ("else" Statement)?
    // оператор цикла
    While = "while" "(" Condition ")" InvariantOpt? Statement
    InvariantOpt = "invariant" Predicate 



    // выражения 
    PriExp := FunctionCall
        | ArrayAccess
        | ...
    // вызов функции 
    FunctionCall = variable "(" ArgList ")"
    // ArgList = Expr ("," Expr)*
    ArgList = ListOf<Expr, ",">
    // обращение к элементу массива
    ArrayAccess = variable "[" Expr "]"



    // Conditions (not > and > or > -> (right))

    AndOp<C> = C "and" C
    OrOp<C> = C "or" C
    NotOp<C> = "not" C
    ParenOp<C> = "(" C ")"
    
    Condition = ImplyCond
    // импликация - правоассоциативна
    ImplyCond = OrCond ("->" ImplyCond)?
    // дизъюнкция - левоассоциативна
    OrCond = AndCond ("or" AndCond)*
    // конъюнкция - левоассоциативна
    AndCond = NotCond ("and" NotCond)*
    // отрицания (несколько) + атомы условий
    NotCond = ("not")* AtomCond

    AtomCond = "true"           -- true
        | "false"               -- false
        | Comparison            -- comparison
        | "(" Condition ")"     -- paren

    Comparison = Expr "==" Expr                 -- eq
        | Expr "!=" Expr                        -- neq
        | Expr ">=" Expr                        -- ge
        | Expr "<=" Expr                        -- le
        | Expr ">"  Expr                        -- gt
        | Expr "<"  Expr                        -- lt



    // предикаты (not > and > or > -> (right))
    Predicate = ImplyPred
    ImplyPred = OrPred ("->" ImplyPred)?
    OrPred = AndPred ("or" AndPred)*
    AndPred = NotPred ("and" NotPred)*
    NotPred = ("not")* AtomPred

    AtomPred = Quantifier     -- quantifier
        | FormulaRef          -- formula_ref
        | "true"              -- true
        | "false"             -- false
        | Comparison          -- comparison
        | "(" Predicate ")"   -- paren

    // кванторы
    Quantifier = ("forall" | "exists") 
        "(" Param "|" Predicate ")"
    // ссылки на формулы
    FormulaRef = variable "(" ParamList ")"



    space := " " | "\t" | "\n" | comment | ...
    // (~endOfLine any)* - consume any single character that is not a endOfLine 
    comment = "//" (~endOfLine any)* endOfLine
    endOfLine = "\r" | "\n" | "\r\n"
    spaces := space+ | ...
}
