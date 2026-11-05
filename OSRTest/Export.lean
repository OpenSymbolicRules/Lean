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
#guard render (.powNat (.var "x") 2) ==
  "{\"applicant\":{\"cd\":\"arith1\",\"kind\":\"OMS\",\"name\":\"power\"}," ++
  "\"arguments\":[{\"kind\":\"OMV\",\"name\":\"x\"},{\"integer\":2,\"kind\":\"OMI\"}]," ++
  "\"kind\":\"OMA\"}"

-- Every symbol the expression language can emit is present in the registry.
#guard Expr.allSymbols.all fun s => (Registry.lookup s).isSome

-- Each symbol has exactly one registry entry and every entry covers both domains.
#guard Registry.entries.all fun e =>
  (Registry.entries.filter (·.symbol == e.symbol)).length == 1
#guard Registry.entries.all fun e =>
  [Domain.real, Domain.complex].all fun d => (e.interpretation? d).isSome

-- Symbols of an expression are collected without duplicates, in first-use order.
#guard (Expr.symbols (.app2 .add (.powNat (.app1 .sin (.var "x")) 2)
    (.powNat (.app1 .cos (.var "x")) 2))).map OMSymbol.uri ==
  ["http://www.openmath.org/cd/arith1#plus",
   "http://www.openmath.org/cd/arith1#power",
   "http://www.openmath.org/cd/transc1#sin",
   "http://www.openmath.org/cd/transc1#cos"]

end OSRTest.Export
