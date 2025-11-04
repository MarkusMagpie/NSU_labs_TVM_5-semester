
Funnier <: Funny {
    // аннотации модуля (глобальные формулы + аксиомы)
    Module := Formula* Function+
    
    Formula = "formula" variable "(" ParamList ")" "=>" Predicate ";"

    // Formula = identifier "(" ParamList ")" "=>" Predicate ";" 

    // постусловие функции
    Postopt = "ensures" Predicate
    
    // расширение функции для поддержки постусловий
    Function := variable 
        "(" ParamList ")" 
        Preopt? 
        "returns" ParamListNonEmpty 
        Postopt?
        UsesOpt? 
        Statement
    
    // расширение оператора while для поддержки вариантов
    While := "while" "(" Condition ")" InvariantOpt? VariantOpt? Statement

    VariantOpt = "variant" Expr
}
