
Funnier <: Funny {
    Module := Formula* Function+

    Formula = variable "(" ParamList ")" "=>" Predicate ";"

    // предусловие функции
    Preopt := "requires" Predicate ("and" Predicate)*

    // постусловие функции
    Postopt = "ensures" Predicate ("and" Predicate)*
    
    // расширение функции для поддержки постусловий
    Function := variable 
        "(" ParamList ")" 
        Preopt? 
        "returns" ParamListNonEmpty 
        Postopt?
        UsesOpt? 
        Statement

    // пишу обновленный инвариант к правилу: While = "while" "(" Condition ")" InvariantOpt? Statement
    InvariantOpt := "invariant" Predicate ("and" Predicate)* 
}
