import OSR.Semantics

/-!
# OpenMath objects and the exporter

A Lean model of the OpenMath objects the exporter emits, and three facts about
`Expr.toOMJson`:

1. **Shape.**  `Expr.toOMJson e` is exactly the OpenMath 2.0 JSON
   serialization (`OMObj.toJson`) of the object `e.toOM`
   (`toOMJson_eq_toJson_toOM`).
2. **Faithfulness.**  Decoding an object by symbol identity (`cd`, `name`) and
   arity alone, with no access to Lean constructor names, recovers the
   expression (`decode_toOM`).  Reading the exported object through its
   OpenMath symbols therefore yields the value `eval` gives, which is the
   value the rule theorems are about (`evalOM_toOM`).
3. **Registry coverage.**  Every symbol an object can contain has a registry
   entry with the arity it is used with (`registry_covers_toOM`).

The decoding table (`decodeApp`) maps OpenMath symbols to operations; it is the
only place where symbols are read.  What remains trusted is that Lean's
`Json` printer renders `OMObj.toJson` as the JSON text, and that the registry
interpretation of each symbol is the one in `OSR.Interp` (see
`docs/trust-model.md`).
-/

namespace OSR

/-- The OpenMath objects of the OSR fragment: variables, integers, symbols, and
applications of a symbol. -/
inductive OMObj where
  | omv (name : String)
  | omi (value : Int)
  | oms (symbol : OMSymbol)
  | oma (head : OMSymbol) (args : List OMObj)
  deriving Repr, Inhabited

namespace OMObj

open Lean (Json) in
/-- The OpenMath 2.0 JSON encoding of an object. -/
def toJson : OMObj → Json
  | .omv n => Json.mkObj [("kind", Json.str "OMV"), ("name", Json.str n)]
  | .omi z => Expr.omiJson z
  | .oms s => Expr.omsJson s
  | .oma h args => Expr.omaJson h (args.attach.map fun ⟨a, _⟩ => a.toJson)

/-- Symbols occurring in an object (heads and constants). -/
def symbolsWithArity : OMObj → List (OMSymbol × Nat)
  | .omv _ | .omi _ => []
  | .oms s => [(s, 0)]
  | .oma h args => (h, args.length) :: (args.attach.flatMap fun ⟨a, _⟩ => a.symbolsWithArity)

end OMObj

namespace Expr

/-- The OpenMath object of an expression. -/
def toOM : Expr → OMObj
  | .var n => .omv n
  | .int z => .omi z
  | .const c => .oms c.symbol
  | .app1 op a => .oma op.symbol [a.toOM]
  | .app2 op a b => .oma op.symbol [a.toOM, b.toOM]
  | .pow a b => .oma powerSymbol [a.toOM, b.toOM]

theorem toOMJson_eq_toJson_toOM : ∀ e : Expr, e.toOMJson = e.toOM.toJson
  | .var n => by simp [toOMJson, toOM, OMObj.toJson]
  | .int z => by simp [toOMJson, toOM, OMObj.toJson]
  | .const c => by simp [toOMJson, toOM, OMObj.toJson]
  | .app1 op a => by
    simp [toOMJson, toOM, OMObj.toJson, toOMJson_eq_toJson_toOM a]
  | .app2 op a b => by
    simp [toOMJson, toOM, OMObj.toJson, toOMJson_eq_toJson_toOM a, toOMJson_eq_toJson_toOM b]
  | .pow a b => by
    simp [toOMJson, toOM, OMObj.toJson, toOMJson_eq_toJson_toOM a, toOMJson_eq_toJson_toOM b]

end Expr

/-! ## Decoding by symbol identity -/

/-- The constant named by an OpenMath symbol. -/
def decodeConst (s : OMSymbol) : Option Const :=
  if s = ⟨"nums1", "pi"⟩ then some .pi else none

/-- The unary operation named by an OpenMath symbol. -/
def decodeOp1 (s : OMSymbol) : Option Op1 :=
  if s = ⟨"arith1", "unary_minus"⟩ then some .neg
  else if s = ⟨"transc1", "sin"⟩ then some .sin
  else if s = ⟨"transc1", "cos"⟩ then some .cos
  else if s = ⟨"transc1", "tan"⟩ then some .tan
  else if s = ⟨"transc1", "arctan"⟩ then some .arctan
  else if s = ⟨"transc1", "exp"⟩ then some .exp
  else if s = ⟨"transc1", "ln"⟩ then some .ln
  else none

/-- The binary operation named by an OpenMath symbol. -/
def decodeOp2 (s : OMSymbol) : Option Op2 :=
  if s = ⟨"arith1", "plus"⟩ then some .add
  else if s = ⟨"arith1", "minus"⟩ then some .sub
  else if s = ⟨"arith1", "times"⟩ then some .mul
  else if s = ⟨"arith1", "divide"⟩ then some .div
  else none

theorem decodeConst_symbol : ∀ c : Const, decodeConst c.symbol = some c := by
  intro c; cases c; decide

theorem decodeOp1_symbol : ∀ o : Op1, decodeOp1 o.symbol = some o := by
  intro o; cases o <;> decide

theorem decodeOp2_symbol : ∀ o : Op2, decodeOp2 o.symbol = some o := by
  intro o; cases o <;> decide

theorem decodeOp1_power : decodeOp1 powerSymbol = none := by decide
theorem decodeOp2_power : decodeOp2 powerSymbol = none := by decide

/-- Read an object as an expression, using only symbol identities and arities.
Objects outside the fragment decode to `none`. -/
def decode : OMObj → Option Expr
  | .omv n => some (.var n)
  | .omi z => some (.int z)
  | .oms s => (decodeConst s).map .const
  | .oma h [a] => do
    let o ← decodeOp1 h
    return .app1 o (← decode a)
  | .oma h [a, b] =>
    if h = powerSymbol then return .pow (← decode a) (← decode b)
    else do
      let o ← decodeOp2 h
      return .app2 o (← decode a) (← decode b)
  | .oma _ _ => none

/-- **Faithfulness of the exporter.**  Decoding the exported object by symbol
identity recovers the expression. -/
theorem decode_toOM : ∀ e : Expr, decode e.toOM = some e
  | .var n => rfl
  | .int z => rfl
  | .const c => by simp [Expr.toOM, decode, decodeConst_symbol]
  | .app1 o a => by simp [Expr.toOM, decode, decodeOp1_symbol, decode_toOM a]
  | .app2 o a b => by
    have hne : o.symbol ≠ powerSymbol := by cases o <;> decide
    simp [Expr.toOM, decode, decodeOp2_symbol, decode_toOM a, decode_toOM b, hne]
  | .pow a b => by simp [Expr.toOM, decode, decode_toOM a, decode_toOM b]

/-- The value of an OpenMath object read through its symbols. -/
def evalOM {α : Type} [Field α] (I : Interp α) (env : String → α) (o : OMObj) : Option α :=
  (decode o).map (eval I env)

/-- The exported object denotes the value the rule theorems are about. -/
theorem evalOM_toOM {α : Type} [Field α] (I : Interp α) (env : String → α) (e : Expr) :
    evalOM I env e.toOM = some (eval I env e) := by
  simp [evalOM, decode_toOM]

/-- Two expressions with the same export are equal: the export loses nothing. -/
theorem toOM_injective {e f : Expr} (h : e.toOM = f.toOM) : e = f := by
  have := decode_toOM e
  rw [h, decode_toOM f] at this
  exact (Option.some.inj this).symm

/-! ## Registry coverage -/

/-- Symbols with the arity the fragment uses them at. -/
def fragmentSymbols : List (OMSymbol × Nat) :=
  [Op1.neg, .sin, .cos, .tan, .arctan, .exp, .ln].map (fun o => (o.symbol, 1)) ++
  [Op2.add, .sub, .mul, .div].map (fun o => (o.symbol, 2)) ++
  [Const.pi].map (fun c => (c.symbol, 0)) ++ [(powerSymbol, 2)]

theorem symbolsWithArity_toOM_mem :
    ∀ (e : Expr), ∀ p ∈ e.toOM.symbolsWithArity, p ∈ fragmentSymbols
  | .var _ => by simp [Expr.toOM, OMObj.symbolsWithArity]
  | .int _ => by simp [Expr.toOM, OMObj.symbolsWithArity]
  | .const c => by cases c; simp [Expr.toOM, OMObj.symbolsWithArity, fragmentSymbols]
  | .app1 o a => by
    intro p hp
    simp only [Expr.toOM, OMObj.symbolsWithArity, List.mem_cons, List.length_singleton] at hp
    rcases hp with rfl | hp
    · cases o <;> simp [fragmentSymbols]
    · simp only [List.attach_cons, List.attach_nil, List.map_nil, List.flatMap_cons,
        List.flatMap_nil, List.append_nil] at hp
      exact symbolsWithArity_toOM_mem a p hp
  | .app2 o a b => by
    intro p hp
    simp only [Expr.toOM, OMObj.symbolsWithArity, List.mem_cons] at hp
    rcases hp with rfl | hp
    · cases o <;> simp [fragmentSymbols]
    · simp only [List.attach_cons, List.attach_nil, List.map_cons, List.map_nil,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at hp
      rcases hp with hp | hp
      · exact symbolsWithArity_toOM_mem a p hp
      · exact symbolsWithArity_toOM_mem b p hp
  | .pow a b => by
    intro p hp
    simp only [Expr.toOM, OMObj.symbolsWithArity, List.mem_cons] at hp
    rcases hp with rfl | hp
    · simp [fragmentSymbols]
    · simp only [List.attach_cons, List.attach_nil, List.map_cons, List.map_nil,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at hp
      rcases hp with hp | hp
      · exact symbolsWithArity_toOM_mem a p hp
      · exact symbolsWithArity_toOM_mem b p hp

/-- Every symbol of the fragment has a registry entry with the same arity. -/
theorem registry_covers_fragment :
    ∀ p ∈ fragmentSymbols, (Registry.lookup p.1).map (·.arity) = some p.2 := by
  decide

/-- **Registry coverage.**  Every symbol of an exported object has a registry
entry with the arity it is applied at. -/
theorem registry_covers_toOM (e : Expr) :
    ∀ p ∈ e.toOM.symbolsWithArity, (Registry.lookup p.1).map (·.arity) = some p.2 :=
  fun p hp => registry_covers_fragment p (symbolsWithArity_toOM_mem e p hp)

end OSR
