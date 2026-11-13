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
#guard (Cond.gt (.int 0) (.var "n")).decide? == none
#guard (Cond.int (.app2 .div (.int 4) (.int 2))).decide? == some true
#guard (Cond.int (.app2 .div (.int 1) (.int 2))).decide? == some false

-- Substitution then decision, as the calculus rewriter does.
#guard ((Cond.ne (.var "m") (.int (-1))).subst [("m", .int 3)]).decide? == some true

end OSRTest.Decide
