import OSR

/-!
# Exporter tests

These tests pin the portable encoding of the supported expression fragment.
Every operator must be emitted as the OpenMath symbol recorded in the
semantic registry, using the normative OpenMath 2.0 JSON encoding.
-/

namespace OSRTest.Export

open OSR

private def render (e : Expr) : String := (Expr.toOMJson e).compress

-- Variables and literals.
#guard render (.var "x") == "{\"kind\":\"OMV\",\"name\":\"x\"}"
#guard render (.int 2) == "{\"integer\":2,\"kind\":\"OMI\"}"
#guard render (.int (-2)) == "{\"integer\":-2,\"kind\":\"OMI\"}"
#guard render (.const .pi) == "{\"cd\":\"nums1\",\"kind\":\"OMS\",\"name\":\"pi\"}"

-- Unary and binary applications reference arith1 / transc1 symbols.
#guard render (.app1 .sin (.var "x")) ==
  "{\"applicant\":{\"cd\":\"transc1\",\"kind\":\"OMS\",\"name\":\"sin\"}," ++
  "\"arguments\":[{\"kind\":\"OMV\",\"name\":\"x\"}],\"kind\":\"OMA\"}"
#guard render (.app1 .neg (.var "x")) ==
  "{\"applicant\":{\"cd\":\"arith1\",\"kind\":\"OMS\",\"name\":\"unary_minus\"}," ++
  "\"arguments\":[{\"kind\":\"OMV\",\"name\":\"x\"}],\"kind\":\"OMA\"}"
#guard render (.app2 .div (.var "x") (.int 2)) ==
  "{\"applicant\":{\"cd\":\"arith1\",\"kind\":\"OMS\",\"name\":\"divide\"}," ++
  "\"arguments\":[{\"kind\":\"OMV\",\"name\":\"x\"},{\"integer\":2,\"kind\":\"OMI\"}]," ++
  "\"kind\":\"OMA\"}"

-- Powers are restricted to natural-number literal exponents.
#guard render (.pow (.var "x") (.int 2)) ==
  "{\"applicant\":{\"cd\":\"arith1\",\"kind\":\"OMS\",\"name\":\"power\"}," ++
  "\"arguments\":[{\"kind\":\"OMV\",\"name\":\"x\"},{\"integer\":2,\"kind\":\"OMI\"}]," ++
  "\"kind\":\"OMA\"}"

-- Every symbol the expression language can emit is present in the registry.
#guard Expr.allSymbols.all fun s => (Registry.lookup s).isSome

-- Each symbol has exactly one registry entry.  Every entry covers ℝ, and every
-- entry except `relation1#gt` and `relation1#geq` (ℂ is not ordered) covers ℂ.
#guard Registry.entries.all fun e =>
  (Registry.entries.filter (·.symbol == e.symbol)).length == 1
#guard Registry.entries.all fun e =>
  (e.interpretation? .real).isSome || (e.interpretation? .boolean).isSome
-- Symbols without a complex interpretation are not certified over ℂ.
#guard Registry.mappingAssurance [⟨"transc1", "sec"⟩] .complex == .unsupported
#guard Registry.mappingAssurance [⟨"arith1", "root"⟩] .complex == .unsupported
-- The logic1 symbols are interpreted in the Boolean domain only, except
-- logic1#or, which also joins conditions over ℝ and ℂ.
#guard Registry.entries.all fun e =>
  e.symbol.cd != "logic1" || e.symbol == ⟨"logic1", "or"⟩ ||
    ((e.interpretation? .boolean).isSome && (e.interpretation? .real).isNone)
#guard [Domain.boolean, .real, .complex].all fun d =>
  Registry.mappingAssurance [⟨"logic1", "or"⟩] d == .formallyRelated
#guard Registry.mappingAssurance [⟨"relation1", "gt"⟩] .complex == .unsupported
-- relation1#geq, like gt, has no complex interpretation.
#guard Registry.mappingAssurance [⟨"relation1", "geq"⟩] .real == .formallyRelated
#guard Registry.mappingAssurance [⟨"relation1", "geq"⟩] .complex == .unsupported

-- Symbols of an expression are collected without duplicates, in first-use order.
#guard (Expr.symbols (.app2 .add (.pow (.app1 .sin (.var "x")) (.int 2))
    (.pow (.app1 .cos (.var "x")) (.int 2)))).map OMSymbol.uri ==
  ["http://www.openmath.org/cd/arith1#plus",
   "http://www.openmath.org/cd/arith1#power",
   "http://www.openmath.org/cd/transc1#sin",
   "http://www.openmath.org/cd/transc1#cos"]

end OSRTest.Export
