import OSR

/-!
# Tests of the decision of closed conditions
-/

namespace OSRTest.Decide

open OSR

-- Exact rational evaluation of closed arithmetic.
#guard (Expr.ratEval? (.app2 .div (.int 1) (.int 2))) == some (1 / 2)
#guard (Expr.ratEval? (.app2 .add (.int 3) (.int 1))) == some 4
#guard (Expr.ratEval? (.pow (.int 2) (.int (-1)))) == some (1 / 2)
#guard (Expr.ratEval? (.app1 .neg (.int 5))) == some (-5)

-- Undefined or non-closed expressions have no value.
#guard (Expr.ratEval? (.app2 .div (.int 1) (.int 0))).isNone
#guard (Expr.ratEval? (.pow (.int 0) (.int (-1)))).isNone
#guard (Expr.ratEval? (.pow (.int 2) (.app2 .div (.int 1) (.int 2)))).isNone
#guard (Expr.ratEval? (.var "m")).isNone
#guard (Expr.ratEval? (.app1 .ln (.int 1))).isNone

-- Decisions: true, false, or none when a side is not closed.
#guard (Cond.ne (.int 3) (.int (-1))).decide? == some true
#guard (Cond.ne (.int (-1)) (.int (-1))).decide? == some false
#guard (Cond.gt (.int 1) (.int 0)).decide? == some true
#guard (Cond.eq (.app2 .mul (.int 2) (.int 3)) (.int 6)).decide? == some true
#guard (Cond.eq (.int 1) (.int 2)).decide? == some false
#guard (Cond.eq (.var "a") (.int 0)).decide? == none
#guard ((Cond.eq (.var "a") (.int 0)).subst [("a", .int 0)]).decide? == some true
#guard (Cond.eq (.var "a") (.int 0)).symbols == [⟨"relation1", "eq"⟩]
#guard (Cond.gt (.int 0) (.var "n")).decide? == none
#guard (Cond.int (.app2 .div (.int 4) (.int 2))).decide? == some true
#guard (Cond.int (.app2 .div (.int 1) (.int 2))).decide? == some false

-- `relation1#geq` and `logic1#or` (RUBI's LeQ, GeQ, Not[LtQ], Not[GtQ], Or).
#guard (Cond.ge (.int 1) (.int 1)).decide? == some true
#guard (Cond.ge (.int 0) (.int 1)).decide? == some false
#guard (Cond.ge (.var "a") (.int 1)).decide? == none
#guard (Cond.or (.eq (.int 1) (.int 2)) (.gt (.int 3) (.int 2))).decide? == some true
#guard (Cond.or (.eq (.int 1) (.int 2)) (.gt (.int 1) (.int 2))).decide? == some false
#guard (Cond.or (.eq (.var "a") (.int 2)) (.gt (.int 3) (.int 2))).decide? == some true
#guard (Cond.or (.eq (.var "a") (.int 2)) (.gt (.int 1) (.int 2))).decide? == none
#guard (Cond.or (.ge (.var "a") (.int 0)) (.int (.var "b"))).symbols ==
  [⟨"logic1", "or"⟩, ⟨"relation1", "geq"⟩, ⟨"set1", "in"⟩, ⟨"setname1", "Z"⟩]
#guard (Cond.or (.ge (.var "a") (.int 0)) (.int (.var "b"))).vars == ["a", "b"]
#guard ((Cond.or (.ge (.var "a") (.int 0)) (.eq (.int 0) (.int 1))).subst [("a", .int 2)]).decide? == some true

-- Substitution then decision, as the calculus rewriter does.
#guard ((Cond.ne (.var "m") (.int (-1))).subst [("m", .int 3)]).decide? == some true

end OSRTest.Decide
