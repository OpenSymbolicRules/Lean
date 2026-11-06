import OSR

/-!
# OpenMath object tests

The decoder reads symbols only; objects outside the fragment are rejected.
-/

namespace OSRTest.OMObject

open OSR

private def t : OMObj := .omv "t"
private def sinSym : OMSymbol := ⟨"transc1", "sin"⟩

-- Round trip on every catalogue pattern and replacement.
#guard Trigonometry.catalog.all fun e =>
  decode e.rule.lhs.toOM == some e.rule.lhs && decode e.rule.rhs.toOM == some e.rule.rhs

-- Integer literals as second argument of a binary operation are not powers.
#guard decode (.oma ⟨"arith1", "times"⟩ [t, .omi 2]) == some (.app2 .mul (.var "t") (.int 2))
#guard decode (.oma powerSymbol [t, .omi 2]) == some (.powNat (.var "t") 2)

-- Rejected: negative or symbolic exponents, wrong arity, unknown symbols.
#guard decode (.oma powerSymbol [t, .omi (-1)]) == none
#guard decode (.oma powerSymbol [t, t]) == none
#guard decode (.oma sinSym [t, t]) == none
#guard decode (.oma sinSym []) == none
#guard decode (.oma ⟨"arith1", "plus"⟩ [t]) == none
#guard decode (.oma ⟨"transc1", "sinh"⟩ [t]) == none
#guard decode (.oma ⟨"transc1", "exp"⟩ [t]) == some (.app1 .exp (.var "t"))
#guard decode (.oms ⟨"nums1", "e"⟩) == none

-- The registry knows every symbol of the fragment at its arity.
#guard fragmentSymbols.all fun (s, n) => (Registry.lookup s).map (·.arity) == some n

end OSRTest.OMObject
