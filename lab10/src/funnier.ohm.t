
Funnier <: Funny {
    Module := Formula* Function+

    Formula = variable "(" ParamList ")" "=>" Predicate ";"

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
}
