import OSR.Registry

/-!
# OSR expressions

A small, explicitly supported expression fragment.  Arity is enforced by the
constructors, and each operator is tied to exactly one OpenMath symbol.  The
same `Expr` value is used to state the Lean theorem (through `OSR.eval`) and
to produce the portable OpenMath JSON (through `Expr.toOMJson`), so the
theorem and the export cannot drift apart.

Unsupported constructs are not representable.  In particular, powers only take
natural-number literal exponents, which avoids the totalization of `rpow` and
`cpow` and the branch choices of non-integer powers.
-/

namespace OSR

/-- Unary operators of the fragment. -/
inductive Op1 where
  | neg
  | sin
  | cos
  | tan
  | arctan
  | exp
  | ln
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Binary operators of the fragment. -/
inductive Op2 where
  | add
  | sub
  | mul
  | div
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Named constants of the fragment. -/
inductive Const where
  | pi
  deriving DecidableEq, Repr, Inhabited, BEq

/-- The OpenMath symbol of a unary operator. -/
def Op1.symbol : Op1 → OMSymbol
  | .neg => ⟨"arith1", "unary_minus"⟩
  | .sin => ⟨"transc1", "sin"⟩
  | .cos => ⟨"transc1", "cos"⟩
  | .tan => ⟨"transc1", "tan"⟩
  | .arctan => ⟨"transc1", "arctan"⟩
  | .exp => ⟨"transc1", "exp"⟩
  | .ln => ⟨"transc1", "ln"⟩

/-- The OpenMath symbol of a binary operator. -/
def Op2.symbol : Op2 → OMSymbol
  | .add => ⟨"arith1", "plus"⟩
  | .sub => ⟨"arith1", "minus"⟩
  | .mul => ⟨"arith1", "times"⟩
  | .div => ⟨"arith1", "divide"⟩

/-- The OpenMath symbol of a constant. -/
def Const.symbol : Const → OMSymbol
  | .pi => ⟨"nums1", "pi"⟩

/-- The OpenMath symbol used for natural-number powers. -/
def powerSymbol : OMSymbol := ⟨"arith1", "power"⟩

/-- Expressions of the supported fragment. -/
inductive Expr where
  /-- A rule variable. -/
  | var (name : String)
  /-- An integer literal. -/
  | int (value : Int)
  /-- A named constant. -/
  | const (c : Const)
  /-- A unary application. -/
  | app1 (op : Op1) (arg : Expr)
  /-- A binary application. -/
  | app2 (op : Op2) (lhs rhs : Expr)
  /-- A power with a natural-number literal exponent. -/
  | powNat (base : Expr) (exponent : Nat)
  deriving DecidableEq, Repr, Inhabited, BEq

namespace Expr

/-- Variables occurring in an expression, in first-occurrence order. -/
def vars : Expr → List String
  | .var n => [n]
  | .int _ | .const _ => []
  | .app1 _ a => a.vars
  | .app2 _ a b => (a.vars ++ b.vars).eraseDups
  | .powNat a _ => a.vars

/-- OpenMath symbols occurring in an expression, in first-use order. -/
def symbols : Expr → List OMSymbol
  | .var _ | .int _ => []
  | .const c => [c.symbol]
  | .app1 op a => (op.symbol :: a.symbols).eraseDups
  | .app2 op a b => (op.symbol :: a.symbols ++ b.symbols).eraseDups
  | .powNat a _ => (powerSymbol :: a.symbols).eraseDups

/-- Every OpenMath symbol the fragment can emit. -/
def allSymbols : List OMSymbol :=
  [Op1.neg, .sin, .cos, .tan, .arctan, .exp, .ln].map Op1.symbol ++
  [Op2.add, .sub, .mul, .div].map Op2.symbol ++
  [Const.pi].map Const.symbol ++ [powerSymbol]

/-- Whether the expression is a bare variable. -/
def isVar : Expr → Bool
  | .var _ => true
  | _ => false

open Lean (Json) in
/-- An OpenMath symbol in the OpenMath 2.0 JSON encoding (§3.3.3). -/
def omsJson (s : OMSymbol) : Json :=
  Json.mkObj [("kind", Json.str "OMS"), ("cd", Json.str s.cd), ("name", Json.str s.name)]

open Lean (Json) in
/-- An integer in the OpenMath 2.0 JSON encoding (§3.3.5.1). -/
def omiJson (z : Int) : Json :=
  Json.mkObj [("kind", Json.str "OMI"), ("integer", Json.num (Lean.JsonNumber.fromInt z))]

open Lean (Json) in
/-- An application in the OpenMath 2.0 JSON encoding (§3.3.9). -/
def omaJson (s : OMSymbol) (args : List Json) : Json :=
  Json.mkObj [("kind", Json.str "OMA"), ("applicant", omsJson s), ("arguments", Json.arr args.toArray)]

open Lean (Json) in
/-- The expression in the normative OpenMath 2.0 JSON encoding.  Rule
variables are encoded as `OMV`; their binding is given by the enclosing rule. -/
def toOMJson : Expr → Json
  | .var n => Json.mkObj [("kind", Json.str "OMV"), ("name", Json.str n)]
  | .int z => omiJson z
  | .const c => omsJson c.symbol
  | .app1 op a => omaJson op.symbol [a.toOMJson]
  | .app2 op a b => omaJson op.symbol [a.toOMJson, b.toOMJson]
  | .powNat a n => omaJson powerSymbol [a.toOMJson, omiJson n]

end Expr

end OSR
