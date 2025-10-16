
Funny <: Arithmetic {
    // write rules here
    Module = Function+

    Function = variable 
        "(" ParamList? ")" 
        Preopt? 
        "returns" ParamListNonEmpty 
        UsesOpt? 
        Statement

    // ParamList = Param ("," Param)*
    ParamList = ListOf<Param, ",">
    // ParamListNonEmpty = Param ("," Param)*
    ParamListNonEmpty = ListOf<Param, ",">
    Param = variable ":" Type
    Preopt = "requires" Predicate 
    UsesOpt = "uses" ParamList 

    Type = "int"    -- int
        | "int" "[]"   -- array



    // В Funny есть четыре типа операторов: присваивание, блок, условный оператор, цикл. 
    Statement = Assignment
        | Block
        | Conditional
        | While

    // прсваивание - обращение к массиву или кортежное присваивание из вызова функции
    Assignment = LValueList "=" ExprList ";"    -- tuple_assignment
        | LValue "=" Expr ";"                   -- simple_assignment
    // LValueList = LValue ("," LValue)*
    LValueList = ListOf<LValue, ",">
    // ExprList = Expr ("," Expr)*
    ExprList = ListOf<Expr, ",">
    // LValue - имя переменной или обращение к массиву
    LValue = variable "[" Expr "]"              -- array_access
        | variable                               -- variable
    // блок
    Block = "{" Statement* "}"
    // условный опреатор
    Conditional = "if" "(" Condition ")" Statement ("else" Statement)?
    // оператор цикла
    While = "while" "(" Condition ")" InvariantOpt Statement
    InvariantOpt = "invariant" Predicate 



    // выражения 
    PriExp := FunctionCall
        | ArrayAccess
        | ...
    // вызов функции 
    FunctionCall = variable "(" ArgList? ")"
    ArgList = Expr ("," Expr)*
    // обращение к элементу массива
    ArrayAccess = variable "[" Expr "]"



    // условия
    Condition = "true"                          -- true
        | "false"                               -- false
        | Comparison                            -- comparison
        | "not" Condition                       -- not
        | Condition "and" Condition             -- and
        | Condition "or" Condition              -- or
        | Condition "->" Condition              -- implies
        | "(" Condition ")"                     -- paren

    Comparison = Expr "==" Expr                 -- eq
        | Expr "!=" Expr                        -- neq
        | Expr ">=" Expr                        -- ge
        | Expr "<=" Expr                        -- le
        | Expr ">"  Expr                        -- gt
        | Expr "<"  Expr                        -- lt



    // предикаты
    Predicate = Quantifier                      -- quantifier
        | FormulaRef                            -- formula_ref
        | "true"                                -- true
        | "false"                               -- false
        | Comparison                            -- comparison
        | "not" Predicate                       -- not
        | Predicate "and" Predicate             -- and
        | Predicate "or" Predicate              -- or
        | "(" Predicate ")"                     -- paren
    // кванторы
    Quantifier = ("forall" | "exists") 
        "(" variable ":" Type "|" Predicate ")"
    // ссылки на формулы
    FormulaRef = variable "(" ArgList? ")"



    space := " " | "\t" | "\n" | comment | ...
    // (~endOfLine any)* - consume any single character that is not a endOfLine 
    comment = "//" (~endOfLine any)* endOfLine
    endOfLine = "\r" | "\n" | "\r\n"
    spaces := space+ | ...
}
