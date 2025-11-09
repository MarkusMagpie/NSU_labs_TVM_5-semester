
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

    Predicate := OrPred
    OrPred = AndPred ("or" AndPred)*
    AndPred = NotPred ("and" NotPred)*
    NotPred = ("not")* Atom

    // Atom это базовые варианты предиката
    Atom = Quantifier     -- quantifier
        | FormulaRef      -- formula_ref
        | "true"          -- true
        | "false"         -- false
        | Comparison      -- comparison
        | "(" Predicate ")" -- paren

    // пишу обновленный инвариант к правилу: While
    InvariantOpt := "invariant" Predicate 
    While := "while" "(" Predicate ")" InvariantOpt? Statement
}
