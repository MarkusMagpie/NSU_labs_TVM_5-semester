
Funnier <: Funny {
    Module := Formula* Function+

    Formula = variable "(" ParamList ")" "=>" Predicate ";"

    // предусловие функции
    Preopt := "requires" Predicate ("and" Predicate)*

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
