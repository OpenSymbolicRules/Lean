import OSR.OMObject
import OSR.LogicOps

/-!
# Boolean expressions and their reference rewriter

Quantified Boolean formulas over the `logic1` connectives and the `quant1`
quantifiers, interpreted in `Bool`: a quantifier ranges over the truth values.
Every connective is total, so a rule states equality of truth values
(`BRule.Holds`), with no definedness side condition.

Bound variables make naive substitution unsound (capture), so rule
statements are higher order: a pattern metavariable denotes an arbitrary
function of the whole assignment (`evalM`), and the statement holds for every
renaming of the rule's bound variables (`BExpr.rename`).  Instantiating a
rule then needs no freshness condition (`eval_subst`).

The rewriter mirrors `OSR/Rewrite.lean` (syntactic, non-linear matching;
outermost-leftmost strategy) and is proved sound (`normalize_sound`).
Termination is proved with monotone weights (`BasicWeight`), and the export
is faithful at the OpenMath object level (`decode_toOM`).
-/

namespace OSR.Logic

open OSR

/-- Binary connectives. -/
inductive BOp where
  | and | or | implies | equivalent | nand | nor | xor | xnor
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Propositional formulas. -/
inductive BExpr where
  | var (name : String)
  | tt
  | ff
  | not (a : BExpr)
  | bin (op : BOp) (a b : BExpr)
  /-- `quant1#forall` over the truth values. -/
  | all (x : String) (body : BExpr)
  /-- `quant1#exists` over the truth values. -/
  | ex (x : String) (body : BExpr)
  deriving DecidableEq, Repr, Inhabited, BEq

def BOp.symbol : BOp → OMSymbol
  | .and => ⟨"logic1", "and"⟩
  | .or => ⟨"logic1", "or"⟩
  | .implies => ⟨"logic1", "implies"⟩
  | .equivalent => ⟨"logic1", "equivalent"⟩
  | .nand => ⟨"logic1", "nand"⟩
  | .nor => ⟨"logic1", "nor"⟩
  | .xor => ⟨"logic1", "xor"⟩
  | .xnor => ⟨"logic1", "xnor"⟩

def notSymbol : OMSymbol := ⟨"logic1", "not"⟩
def trueSymbol : OMSymbol := ⟨"logic1", "true"⟩
def falseSymbol : OMSymbol := ⟨"logic1", "false"⟩
def forallSymbol : OMSymbol := ⟨"quant1", "forall"⟩
def existsSymbol : OMSymbol := ⟨"quant1", "exists"⟩

/-- Update an assignment. -/
def upd (ρ : String → Bool) (x : String) (v : Bool) : String → Bool :=
  fun n => if n = x then v else ρ n

/-- The Lean function interpreting a connective (see the registry). -/
def BOp.eval : BOp → Bool → Bool → Bool
  | .and, a, b => a && b
  | .or, a, b => a || b
  | .implies, a, b => OSR.Logic.implies a b
  | .equivalent, a, b => OSR.Logic.equivalent a b
  | .nand, a, b => OSR.Logic.nand a b
  | .nor, a, b => OSR.Logic.nor a b
  | .xor, a, b => Bool.xor a b
  | .xnor, a, b => OSR.Logic.xnor a b

namespace BExpr

/-- Truth value where each variable `n` denotes the function `I n` of the
assignment (a pattern metavariable). -/
def evalM (I : String → (String → Bool) → Bool) (ρ : String → Bool) : BExpr → Bool
  | .var n => I n ρ
  | .tt => true
  | .ff => false
  | .not a => !(a.evalM I ρ)
  | .bin o a b => o.eval (a.evalM I ρ) (b.evalM I ρ)
  | .all x b => forallBool fun v => b.evalM I (upd ρ x v)
  | .ex x b => existsBool fun v => b.evalM I (upd ρ x v)

/-- Truth value of a formula under an assignment of its variables. -/
def eval (ρ : String → Bool) (e : BExpr) : Bool := e.evalM (fun n ρ' => ρ' n) ρ

/-- Rename the bound variables. -/
def rename (ν : String → String) : BExpr → BExpr
  | .var n => .var n
  | .tt => .tt
  | .ff => .ff
  | .not a => .not (a.rename ν)
  | .bin o a b => .bin o (a.rename ν) (b.rename ν)
  | .all x b => .all (ν x) (b.rename ν)
  | .ex x b => .ex (ν x) (b.rename ν)

/-- Variables and bound variables, in first-occurrence order. -/
def vars : BExpr → List String
  | .var n => [n]
  | .tt | .ff => []
  | .not a => a.vars
  | .bin _ a b => (a.vars ++ b.vars).eraseDups
  | .all x b | .ex x b => (x :: b.vars).eraseDups

def symbols : BExpr → List OMSymbol
  | .var _ => []
  | .tt => [trueSymbol]
  | .ff => [falseSymbol]
  | .not a => (notSymbol :: a.symbols).eraseDups
  | .bin o a b => (o.symbol :: a.symbols ++ b.symbols).eraseDups
  | .all _ b => (forallSymbol :: b.symbols).eraseDups
  | .ex _ b => (existsSymbol :: b.symbols).eraseDups

/-- The OpenMath object of a formula. -/
def toOM : BExpr → OMObj
  | .var n => .omv n
  | .tt => .oms trueSymbol
  | .ff => .oms falseSymbol
  | .not a => .oma notSymbol [a.toOM]
  | .bin o a b => .oma o.symbol [a.toOM, b.toOM]
  | .all x b => .ombind forallSymbol [x] b.toOM
  | .ex x b => .ombind existsSymbol [x] b.toOM

/-- The formula in the OpenMath 2.0 JSON encoding. -/
def toOMJson (e : BExpr) : Lean.Json := e.toOM.toJson

end BExpr

/-! ## Decoding by symbol identity -/

def decodeBOp (s : OMSymbol) : Option BOp :=
  if s = ⟨"logic1", "and"⟩ then some .and
  else if s = ⟨"logic1", "or"⟩ then some .or
  else if s = ⟨"logic1", "implies"⟩ then some .implies
  else if s = ⟨"logic1", "equivalent"⟩ then some .equivalent
  else if s = ⟨"logic1", "nand"⟩ then some .nand
  else if s = ⟨"logic1", "nor"⟩ then some .nor
  else if s = ⟨"logic1", "xor"⟩ then some .xor
  else if s = ⟨"logic1", "xnor"⟩ then some .xnor
  else none

theorem decodeBOp_symbol : ∀ o : BOp, decodeBOp o.symbol = some o := by
  intro o; cases o <;> decide

/-- Read an object as a formula, using only symbol identities and arities. -/
def decode : OMObj → Option BExpr
  | .omv n => some (.var n)
  | .oms s =>
    if s = trueSymbol then some .tt else if s = falseSymbol then some .ff else none
  | .oma h [a] => if h = notSymbol then (decode a).map .not else none
  | .oma h [a, b] => do
    let o ← decodeBOp h
    return .bin o (← decode a) (← decode b)
  | .ombind q [x] body =>
    if q = forallSymbol then (decode body).map (.all x)
    else if q = existsSymbol then (decode body).map (.ex x)
    else none
  | _ => none

/-- **Faithfulness of the exporter.** -/
theorem decode_toOM : ∀ e : BExpr, decode e.toOM = some e
  | .var _ => rfl
  | .tt => by decide
  | .ff => by decide
  | .not a => by simp [BExpr.toOM, decode, decode_toOM a]
  | .bin o a b => by simp [BExpr.toOM, decode, decodeBOp_symbol, decode_toOM a, decode_toOM b]
  | .all x b => by simp [BExpr.toOM, decode, decode_toOM b]
  | .ex x b => by simp [BExpr.toOM, decode, decode_toOM b, forallSymbol, existsSymbol]

/-! ## Rules -/

/-- A Boolean rewrite rule. -/
structure BRule where
  id : String
  legacyId : Option String := none
  vars : List String
  lhs : BExpr
  rhs : BExpr
  profiles : List String
  priority : Nat
  description : String
  provenance : Provenance
  /-- Matching constraints: `(p, x)` means that the subterm matched by `p` must
  not mention the variable bound by the binder `x` ("p free of x", v0.1
  `FreeQ`).  This is a constraint on the match, like the treatment of bound
  variables, not a mathematical condition. -/
  independent : List (String × String) := []
  deriving Repr, Inhabited, BEq

/-- The certified statement: both sides have the same truth value for every
renaming of the bound variables, every meaning of the metavariables (any
function of the assignment) and every assignment. -/
def BRule.Holds (r : BRule) : Prop :=
  ∀ (ν : String → String) (I : String → (String → Bool) → Bool) (ρ : String → Bool),
    (∀ q ∈ r.independent, ∀ (ρ' : String → Bool) (v : Bool),
      I q.1 (upd ρ' (ν q.2) v) = I q.1 ρ') →
    (r.lhs.rename ν).evalM I ρ = (r.rhs.rename ν).evalM I ρ

def BRule.symbols (r : BRule) : List OMSymbol := (r.lhs.symbols ++ r.rhs.symbols).eraseDups

/-- Free variables of a formula. -/
def BExpr.free : BExpr → List String
  | .var n => [n]
  | .tt | .ff => []
  | .not a => a.free
  | .bin _ a b => a.free ++ b.free
  | .all x b | .ex x b => b.free.filter (· ≠ x)

theorem upd_same (ρ : String → Bool) (y : String) (v w : Bool) :
    upd (upd ρ y v) y w = upd ρ y w := by
  funext n; simp only [upd]; split <;> rfl

theorem upd_comm (ρ : String → Bool) {x y : String} (h : x ≠ y) (v w : Bool) :
    upd (upd ρ y v) x w = upd (upd ρ x w) y v := by
  funext n; simp only [upd]; split <;> split <;> simp_all

/-- A formula does not depend on a variable that is not free in it. -/
theorem eval_upd_notFree (y : String) (v : Bool) :
    ∀ (e : BExpr) (ρ : String → Bool), y ∉ e.free → e.eval (upd ρ y v) = e.eval ρ
  | .var n, ρ, h => by
    simp only [BExpr.free, List.mem_singleton] at h
    simp [BExpr.eval, BExpr.evalM, upd, Ne.symm h]
  | .tt, _, _ => rfl
  | .ff, _, _ => rfl
  | .not a, ρ, h => by
    have := eval_upd_notFree y v a ρ (by simpa [BExpr.free] using h)
    simp only [BExpr.eval, BExpr.evalM] at this ⊢
    rw [this]
  | .bin o a b, ρ, h => by
    simp only [BExpr.free, List.mem_append, not_or] at h
    have ha := eval_upd_notFree y v a ρ h.1
    have hb := eval_upd_notFree y v b ρ h.2
    simp only [BExpr.eval, BExpr.evalM] at ha hb ⊢
    rw [ha, hb]
  | .all x b, ρ, h => by
    simp only [BExpr.eval, BExpr.evalM]
    congr 1
    funext w
    by_cases hxy : x = y
    · subst hxy; rw [upd_same]
    · rw [upd_comm ρ hxy]
      have hb : y ∉ b.free := by
        intro hm; exact h (by simp [BExpr.free, hm, Ne.symm hxy])
      exact eval_upd_notFree y v b (upd ρ x w) hb
  | .ex x b, ρ, h => by
    simp only [BExpr.eval, BExpr.evalM]
    congr 1
    funext w
    by_cases hxy : x = y
    · subst hxy; rw [upd_same]
    · rw [upd_comm ρ hxy]
      have hb : y ∉ b.free := by
        intro hm; exact h (by simp [BExpr.free, hm, Ne.symm hxy])
      exact eval_upd_notFree y v b (upd ρ x w) hb

/-! ## Matching and substitution -/

abbrev BSubst := List (String × BExpr)

namespace BSubst

def find? : BSubst → String → Option BExpr
  | [], _ => none
  | (k, v) :: σ, n => if k = n then some v else find? σ n

def apply (σ : BSubst) (n : String) : BExpr := (σ.find? n).getD (.var n)

def Extends (σ τ : BSubst) : Prop := ∀ n e, σ.find? n = some e → τ.find? n = some e

theorem Extends.refl (σ : BSubst) : σ.Extends σ := fun _ _ h => h

theorem Extends.trans {σ τ υ : BSubst} (h₁ : σ.Extends τ) (h₂ : τ.Extends υ) : σ.Extends υ :=
  fun n e h => h₂ n e (h₁ n e h)

end BSubst

/-- The name a substitution gives a bound variable. -/
def BSubst.bname (σ : BSubst) (x : String) : String :=
  match σ.find? x with
  | some (.var y) => y
  | _ => x

def BExpr.subst (σ : BSubst) : BExpr → BExpr
  | .var n => σ.apply n
  | .tt => .tt
  | .ff => .ff
  | .not a => .not (a.subst σ)
  | .bin o a b => .bin o (a.subst σ) (b.subst σ)
  | .all x b => .all (σ.bname x) (b.subst σ)
  | .ex x b => .ex (σ.bname x) (b.subst σ)

def matchAux : BExpr → BExpr → BSubst → Option BSubst
  | .var n, e, σ =>
    match σ.find? n with
    | some e' => if e' = e then some σ else none
    | none => some ((n, e) :: σ)
  | .tt, .tt, σ => some σ
  | .ff, .ff, σ => some σ
  | .not a, .not a', σ => matchAux a a' σ
  | .bin o a b, .bin o' a' b', σ =>
    if o = o' then
      match matchAux a a' σ with
      | some σ₁ => matchAux b b' σ₁
      | none => none
    else none
  | .all x b, .all y b', σ =>
    match σ.find? x with
    | some e => if e = .var y then matchAux b b' σ else none
    | none => matchAux b b' ((x, .var y) :: σ)
  | .ex x b, .ex y b', σ =>
    match σ.find? x with
    | some e => if e = .var y then matchAux b b' σ else none
    | none => matchAux b b' ((x, .var y) :: σ)
  | _, _, _ => none

def matchExpr (p e : BExpr) : Option BSubst := matchAux p e []

theorem matchAux_spec : ∀ (p e : BExpr) (σ σ' : BSubst), matchAux p e σ = some σ' →
    σ.Extends σ' ∧ ∀ τ : BSubst, σ'.Extends τ → p.subst τ = e
  | .var n, e, σ, σ', h => by
    unfold matchAux at h
    split at h
    · rename_i e' hf
      split at h
      · rename_i heq
        cases h
        refine ⟨BSubst.Extends.refl _, fun τ hτ => ?_⟩
        simp [BExpr.subst, BSubst.apply, hτ n e' hf, heq]
      · cases h
    · rename_i hf
      cases h
      refine ⟨fun k x hk => ?_, fun τ hτ => ?_⟩
      · simp only [BSubst.find?]
        split
        · rename_i hnk
          subst hnk
          rw [hf] at hk
          cases hk
        · exact hk
      · have : BSubst.find? ((n, e) :: σ) n = some e := by simp [BSubst.find?]
        simp [BExpr.subst, BSubst.apply, hτ n e this]
  | .tt, e, σ, σ', h => by
    cases e <;> simp only [matchAux, reduceCtorEq, Option.some.injEq] at h
    subst h
    exact ⟨BSubst.Extends.refl _, fun _ _ => rfl⟩
  | .ff, e, σ, σ', h => by
    cases e <;> simp only [matchAux, reduceCtorEq, Option.some.injEq] at h
    subst h
    exact ⟨BSubst.Extends.refl _, fun _ _ => rfl⟩
  | .not a, e, σ, σ', h => by
    cases e <;> simp only [matchAux, reduceCtorEq] at h
    rename_i a'
    obtain ⟨hext, hsub⟩ := matchAux_spec a a' σ σ' h
    exact ⟨hext, fun τ hτ => by simp [BExpr.subst, hsub τ hτ]⟩
  | .bin o a b, e, σ, σ', h => by
    cases e <;> simp only [matchAux, reduceCtorEq] at h
    rename_i o' a' b'
    split at h
    · rename_i ho
      split at h
      · rename_i σ₁ h₁
        obtain ⟨hext₁, hsub₁⟩ := matchAux_spec a a' σ σ₁ h₁
        obtain ⟨hext₂, hsub₂⟩ := matchAux_spec b b' σ₁ σ' h
        refine ⟨hext₁.trans hext₂, fun τ hτ => ?_⟩
        simp [BExpr.subst, hsub₁ τ (hext₂.trans hτ), hsub₂ τ hτ, ho]
      · cases h
    · cases h
  | .all x b, e, σ, σ', h => by
    cases e <;> simp only [matchAux, reduceCtorEq] at h
    rename_i y b'
    split at h
    · rename_i e' hf
      split at h
      · rename_i he
        subst he
        obtain ⟨hext, hsub⟩ := matchAux_spec b b' σ σ' h
        refine ⟨hext, fun τ hτ => ?_⟩
        have hx : τ.find? x = some (.var y) := hτ x _ (hext x _ hf)
        simp [BExpr.subst, BSubst.bname, hx, hsub τ hτ]
      · cases h
    · rename_i hf
      obtain ⟨hext, hsub⟩ := matchAux_spec b b' _ σ' h
      refine ⟨fun k v hk => hext k v ?_, fun τ hτ => ?_⟩
      · simp only [BSubst.find?]
        split
        · rename_i hk'
          subst hk'
          rw [hf] at hk
          cases hk
        · exact hk
      · have h0 : BSubst.find? ((x, .var y) :: σ) x = some (.var y) := by simp [BSubst.find?]
        have hx : τ.find? x = some (.var y) := hτ x _ (hext x _ h0)
        simp [BExpr.subst, BSubst.bname, hx, hsub τ hτ]
  | .ex x b, e, σ, σ', h => by
    cases e <;> simp only [matchAux, reduceCtorEq] at h
    rename_i y b'
    split at h
    · rename_i e' hf
      split at h
      · rename_i he
        subst he
        obtain ⟨hext, hsub⟩ := matchAux_spec b b' σ σ' h
        refine ⟨hext, fun τ hτ => ?_⟩
        have hx : τ.find? x = some (.var y) := hτ x _ (hext x _ hf)
        simp [BExpr.subst, BSubst.bname, hx, hsub τ hτ]
      · cases h
    · rename_i hf
      obtain ⟨hext, hsub⟩ := matchAux_spec b b' _ σ' h
      refine ⟨fun k v hk => hext k v ?_, fun τ hτ => ?_⟩
      · simp only [BSubst.find?]
        split
        · rename_i hk'
          subst hk'
          rw [hf] at hk
          cases hk
        · exact hk
      · have h0 : BSubst.find? ((x, .var y) :: σ) x = some (.var y) := by simp [BSubst.find?]
        have hx : τ.find? x = some (.var y) := hτ x _ (hext x _ h0)
        simp [BExpr.subst, BSubst.bname, hx, hsub τ hτ]

theorem matchExpr_subst {p e : BExpr} {σ : BSubst} (h : matchExpr p e = some σ) :
    p.subst σ = e :=
  (matchAux_spec p e [] σ h).2 σ (BSubst.Extends.refl σ)

/-- **Substitution lemma.**  Instantiating a pattern means interpreting each
metavariable by its image (a function of the assignment, so occurrences
under a binder see the bound value) and renaming the bound variables. -/
theorem evalM_subst (σ : BSubst) :
    ∀ (e : BExpr) (ρ : String → Bool),
      (e.subst σ).eval ρ = (e.rename σ.bname).evalM (fun n ρ' => (σ.apply n).eval ρ') ρ
  | .var n, ρ => rfl
  | .tt, _ => rfl
  | .ff, _ => rfl
  | .not a, ρ => by
    have := evalM_subst σ a ρ
    simp only [BExpr.eval, BExpr.subst, BExpr.rename, BExpr.evalM] at this ⊢
    rw [this]
  | .bin o a b, ρ => by
    have ha := evalM_subst σ a ρ
    have hb := evalM_subst σ b ρ
    simp only [BExpr.eval, BExpr.subst, BExpr.rename, BExpr.evalM] at ha hb ⊢
    rw [ha, hb]
  | .all x b, ρ => by
    have hb := fun v => evalM_subst σ b (upd ρ (σ.bname x) v)
    simp only [BExpr.eval, BExpr.subst, BExpr.rename, BExpr.evalM] at hb ⊢
    simp only [hb]
  | .ex x b, ρ => by
    have hb := fun v => evalM_subst σ b (upd ρ (σ.bname x) v)
    simp only [BExpr.eval, BExpr.subst, BExpr.rename, BExpr.evalM] at hb ⊢
    simp only [hb]

/-! ## Reference rewriter -/

/-- The independence constraints of a rule hold for a match. -/
def independentOk (r : BRule) (σ : BSubst) : Bool :=
  r.independent.all fun q => σ.bname q.2 ∉ (σ.apply q.1).free

def rootRewrite : List BRule → BExpr → Option (String × BExpr)
  | [], _ => none
  | r :: rs, e =>
    match matchExpr r.lhs e with
    | some σ => if independentOk r σ then some (r.id, r.rhs.subst σ) else rootRewrite rs e
    | none => rootRewrite rs e

def rewriteStep (rules : List BRule) : BExpr → Option (String × BExpr)
  | .not a =>
    match rootRewrite rules (.not a) with
    | some s => some s
    | none =>
      match rewriteStep rules a with
      | some s => some (s.1, .not s.2)
      | none => none
  | .bin o a b =>
    match rootRewrite rules (.bin o a b) with
    | some s => some s
    | none =>
      match rewriteStep rules a with
      | some s => some (s.1, .bin o s.2 b)
      | none =>
        match rewriteStep rules b with
        | some s => some (s.1, .bin o a s.2)
        | none => none
  | .all x b =>
    match rootRewrite rules (.all x b) with
    | some s => some s
    | none =>
      match rewriteStep rules b with
      | some s => some (s.1, .all x s.2)
      | none => none
  | .ex x b =>
    match rootRewrite rules (.ex x b) with
    | some s => some s
    | none =>
      match rewriteStep rules b with
      | some s => some (s.1, .ex x s.2)
      | none => none
  | e => rootRewrite rules e

structure BNormalization where
  result : BExpr
  trace : List String
  normal : Bool
  deriving Repr, Inhabited, BEq

def normalize (rules : List BRule) : Nat → BExpr → BNormalization
  | 0, e => ⟨e, [], (rewriteStep rules e).isNone⟩
  | fuel + 1, e =>
    match rewriteStep rules e with
    | none => ⟨e, [], true⟩
    | some (id, e') =>
      let n := normalize rules fuel e'
      ⟨n.result, id :: n.trace, n.normal⟩

/-! ## Soundness -/

def RulesHold (rules : List BRule) : Prop := ∀ r ∈ rules, r.Holds

/-- Two formulas have the same truth value under every assignment. -/
def Equiv (a b : BExpr) : Prop := ∀ ρ, a.eval ρ = b.eval ρ

theorem rootRewrite_sound : ∀ (rules : List BRule) (e : BExpr)
    (s : String × BExpr), RulesHold rules → rootRewrite rules e = some s → Equiv s.2 e
  | [], _, _, _, h => by simp [rootRewrite] at h
  | r :: rs, e, s, hr, h => by
    have hrs : RulesHold rs := fun r' h' => hr r' (List.mem_cons_of_mem _ h')
    unfold rootRewrite at h
    split at h
    · rename_i σ hm
      split at h
      · rename_i hind
        simp only [Option.some.injEq] at h
        subst h
        intro ρ
        rw [← matchExpr_subst hm, evalM_subst, evalM_subst]
        refine (hr r List.mem_cons_self _ _ _ fun q hq ρ' v => ?_).symm
        simp only [independentOk, List.all_eq_true, decide_eq_true_eq] at hind
        exact eval_upd_notFree _ v _ ρ' (hind q hq)
      · exact rootRewrite_sound rs e s hrs h
    · exact rootRewrite_sound rs e s hrs h

theorem rewriteStep_sound (rules : List BRule) (hr : RulesHold rules) :
    ∀ (e : BExpr) (s : String × BExpr), rewriteStep rules e = some s → Equiv s.2 e
  | .var n, s, h => rootRewrite_sound rules _ s hr (by simpa [rewriteStep] using h)
  | .tt, s, h => rootRewrite_sound rules _ s hr (by simpa [rewriteStep] using h)
  | .ff, s, h => rootRewrite_sound rules _ s hr (by simpa [rewriteStep] using h)
  | .not a, s, h => by
    simp only [rewriteStep] at h
    split at h
    · rename_i s' hroot
      simp only [Option.some.injEq] at h
      subst h
      exact rootRewrite_sound rules _ s' hr hroot
    · split at h
      · rename_i s' hs
        simp only [Option.some.injEq] at h
        subst h
        intro ρ
        have := rewriteStep_sound rules hr a s' hs ρ
        simp only [BExpr.eval, BExpr.evalM] at this ⊢
        rw [this]
      · cases h
  | .bin o a b, s, h => by
    simp only [rewriteStep] at h
    split at h
    · rename_i s' hroot
      simp only [Option.some.injEq] at h
      subst h
      exact rootRewrite_sound rules _ s' hr hroot
    · split at h
      · rename_i s' hs
        simp only [Option.some.injEq] at h
        subst h
        intro ρ
        have := rewriteStep_sound rules hr a s' hs ρ
        simp only [BExpr.eval, BExpr.evalM] at this ⊢
        rw [this]
      · split at h
        · rename_i s' hs
          simp only [Option.some.injEq] at h
          subst h
          intro ρ
          have := rewriteStep_sound rules hr b s' hs ρ
          simp only [BExpr.eval, BExpr.evalM] at this ⊢
          rw [this]
        · cases h
  | .all x b, s, h => by
    simp only [rewriteStep] at h
    split at h
    · rename_i s' hroot
      simp only [Option.some.injEq] at h
      subst h
      exact rootRewrite_sound rules _ s' hr hroot
    · split at h
      · rename_i s' hs
        simp only [Option.some.injEq] at h
        subst h
        intro ρ
        have := fun v => rewriteStep_sound rules hr b s' hs (upd ρ x v)
        simp only [BExpr.eval, BExpr.evalM] at this ⊢
        simp only [this]
      · cases h
  | .ex x b, s, h => by
    simp only [rewriteStep] at h
    split at h
    · rename_i s' hroot
      simp only [Option.some.injEq] at h
      subst h
      exact rootRewrite_sound rules _ s' hr hroot
    · split at h
      · rename_i s' hs
        simp only [Option.some.injEq] at h
        subst h
        intro ρ
        have := fun v => rewriteStep_sound rules hr b s' hs (upd ρ x v)
        simp only [BExpr.eval, BExpr.evalM] at this ⊢
        simp only [this]
      · cases h

/-- **Engine soundness.**  Normalizing with proved rules preserves the truth
value under every assignment, whatever the step budget. -/
theorem normalize_sound (rules : List BRule) (hr : RulesHold rules) (ρ : String → Bool) :
    ∀ (fuel : Nat) (e : BExpr), (normalize rules fuel e).result.eval ρ = e.eval ρ
  | 0, e => by simp [normalize]
  | fuel + 1, e => by
    simp only [normalize]
    split
    · rfl
    · rename_i id e' hs
      rw [normalize_sound rules hr ρ fuel e']
      exact rewriteStep_sound rules hr e (id, e') hs ρ

/-! ## Termination -/

/-- A weight for formulas, built from weights of negation, conjunction and
disjunction.  Each derived connective weighs one more than its elimination
into those three, so eliminating it always decreases the weight.  The fields
are the inequalities the common rules need. -/
structure BasicWeight where
  nt : Nat → Nat
  conj : Nat → Nat → Nat
  disj : Nat → Nat → Nat
  nt_mono : ∀ a a', a < a' → nt a < nt a'
  conj_monol : ∀ a a' b, a < a' → conj a b < conj a' b
  conj_monor : ∀ a b b', b < b' → conj a b < conj a b'
  disj_monol : ∀ a a' b, a < a' → disj a b < disj a' b
  disj_monor : ∀ a b b', b < b' → disj a b < disj a b'
  nt_gt : ∀ a, a < nt a
  conj_gtl : ∀ a b, a < conj a b
  conj_gtr : ∀ a b, b < conj a b
  disj_gtl : ∀ a b, a < disj a b
  disj_gtr : ∀ a b, b < disj a b
  deMorgan_conj : ∀ a b, disj (nt a) (nt b) < nt (conj a b)
  deMorgan_disj : ∀ a b, conj (nt a) (nt b) < nt (disj a b)

namespace BasicWeight

variable (W : BasicWeight)

/-- Weight of a connective applied to argument weights. -/
def bin : BOp → Nat → Nat → Nat
  | .and, a, b => W.conj a b
  | .or, a, b => W.disj a b
  | .implies, a, b => W.disj (W.nt a) b + 1
  | .equivalent, a, b => W.conj (W.disj (W.nt a) b) (W.disj (W.nt b) a) + 1
  | .nand, a, b => W.nt (W.conj a b) + 1
  | .nor, a, b => W.nt (W.disj a b) + 1
  | .xor, a, b => W.disj (W.conj a (W.nt b)) (W.conj (W.nt a) b) + 1
  | .xnor, a, b => W.conj (W.disj (W.nt a) b) (W.disj (W.nt b) a) + 1

theorem bin_monol (o : BOp) (a a' b : Nat) (h : a < a') : W.bin o a b < W.bin o a' b := by
  have hn := W.nt_mono a a' h
  cases o <;> simp only [bin]
  · exact W.conj_monol _ _ _ h
  · exact W.disj_monol _ _ _ h
  · have := W.disj_monol _ _ b hn; omega
  · have h1 := W.disj_monol _ _ b hn
    have h2 := W.disj_monor (W.nt b) _ _ h
    have := W.conj_monol _ _ (W.disj (W.nt b) a) h1
    have := W.conj_monor (W.disj (W.nt a') b) _ _ h2
    omega
  · have := W.nt_mono _ _ (W.conj_monol _ _ b h); omega
  · have := W.nt_mono _ _ (W.disj_monol _ _ b h); omega
  · have h1 := W.conj_monol _ _ (W.nt b) h
    have h2 := W.conj_monol _ _ b hn
    have := W.disj_monol _ _ (W.conj (W.nt a) b) h1
    have := W.disj_monor (W.conj a' (W.nt b)) _ _ h2
    omega
  · have h1 := W.disj_monol _ _ b hn
    have h2 := W.disj_monor (W.nt b) _ _ h
    have := W.conj_monol _ _ (W.disj (W.nt b) a) h1
    have := W.conj_monor (W.disj (W.nt a') b) _ _ h2
    omega

theorem bin_monor (o : BOp) (a b b' : Nat) (h : b < b') : W.bin o a b < W.bin o a b' := by
  have hn := W.nt_mono b b' h
  cases o <;> simp only [bin]
  · exact W.conj_monor _ _ _ h
  · exact W.disj_monor _ _ _ h
  · have := W.disj_monor (W.nt a) _ _ h; omega
  · have h1 := W.disj_monor (W.nt a) _ _ h
    have h2 := W.disj_monol _ _ a hn
    have := W.conj_monol _ _ (W.disj (W.nt b) a) h1
    have := W.conj_monor (W.disj (W.nt a) b') _ _ h2
    omega
  · have := W.nt_mono _ _ (W.conj_monor a _ _ h); omega
  · have := W.nt_mono _ _ (W.disj_monor a _ _ h); omega
  · have h1 := W.conj_monor a _ _ hn
    have h2 := W.conj_monor (W.nt a) _ _ h
    have := W.disj_monol _ _ (W.conj (W.nt a) b) h1
    have := W.disj_monor (W.conj a (W.nt b')) _ _ h2
    omega
  · have h1 := W.disj_monor (W.nt a) _ _ h
    have h2 := W.disj_monol _ _ a hn
    have := W.conj_monol _ _ (W.disj (W.nt b) a) h1
    have := W.conj_monor (W.disj (W.nt a) b') _ _ h2
    omega

/-- The weight of a formula, given weights of its variables. -/
def weigh (W : BasicWeight) (env : String → Nat) : BExpr → Nat
  | .var n => env n
  | .tt | .ff => 1
  | .not a => W.nt (W.weigh env a)
  | .bin o a b => W.bin o (W.weigh env a) (W.weigh env b)
  | .all _ b | .ex _ b => 2 * W.weigh env b + 6

def Decreases (r : BRule) : Prop := ∀ env, W.weigh env r.rhs < W.weigh env r.lhs

theorem weigh_subst (env : String → Nat) (σ : BSubst) :
    ∀ e : BExpr, W.weigh env (e.subst σ) = W.weigh (fun n => W.weigh env (σ.apply n)) e
  | .var n => by simp [BExpr.subst, weigh]
  | .tt => rfl
  | .ff => rfl
  | .not a => by simp [BExpr.subst, weigh, weigh_subst env σ a]
  | .bin o a b => by simp [BExpr.subst, weigh, weigh_subst env σ a, weigh_subst env σ b]
  | .all x b => by simp [BExpr.subst, weigh, weigh_subst env σ b]
  | .ex x b => by simp [BExpr.subst, weigh, weigh_subst env σ b]

theorem rootRewrite_lt (env : String → Nat) : ∀ (rules : List BRule) (e : BExpr)
    (s : String × BExpr), (∀ r ∈ rules, W.Decreases r) → rootRewrite rules e = some s →
      W.weigh env s.2 < W.weigh env e
  | [], _, _, _, h => by simp [rootRewrite] at h
  | r :: rs, e, s, hr, h => by
    have hrs : ∀ r' ∈ rs, W.Decreases r' := fun r' h' => hr r' (List.mem_cons_of_mem _ h')
    unfold rootRewrite at h
    split at h
    · rename_i σ hm
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        rw [← matchExpr_subst hm, W.weigh_subst, W.weigh_subst]
        exact hr r List.mem_cons_self _
      · exact rootRewrite_lt env rs e s hrs h
    · exact rootRewrite_lt env rs e s hrs h

theorem rewriteStep_lt (env : String → Nat) (rules : List BRule)
    (hr : ∀ r ∈ rules, W.Decreases r) :
    ∀ (e : BExpr) (s : String × BExpr), rewriteStep rules e = some s →
      W.weigh env s.2 < W.weigh env e
  | .var n, s, h => W.rootRewrite_lt env rules _ s hr (by simpa [rewriteStep] using h)
  | .tt, s, h => W.rootRewrite_lt env rules _ s hr (by simpa [rewriteStep] using h)
  | .ff, s, h => W.rootRewrite_lt env rules _ s hr (by simpa [rewriteStep] using h)
  | .not a, s, h => by
    simp only [rewriteStep] at h
    split at h
    · rename_i s' hroot
      simp only [Option.some.injEq] at h
      subst h
      exact W.rootRewrite_lt env rules _ s' hr hroot
    · split at h
      · rename_i s' hs
        simp only [Option.some.injEq] at h
        subst h
        exact W.nt_mono _ _ (rewriteStep_lt env rules hr a s' hs)
      · cases h
  | .bin o a b, s, h => by
    simp only [rewriteStep] at h
    split at h
    · rename_i s' hroot
      simp only [Option.some.injEq] at h
      subst h
      exact W.rootRewrite_lt env rules _ s' hr hroot
    · split at h
      · rename_i s' hs
        simp only [Option.some.injEq] at h
        subst h
        exact W.bin_monol o _ _ _ (rewriteStep_lt env rules hr a s' hs)
      · split at h
        · rename_i s' hs
          simp only [Option.some.injEq] at h
          subst h
          exact W.bin_monor o _ _ _ (rewriteStep_lt env rules hr b s' hs)
        · cases h
  | .all x b, s, h => by
    simp only [rewriteStep] at h
    split at h
    · rename_i s' hroot
      simp only [Option.some.injEq] at h
      subst h
      exact W.rootRewrite_lt env rules _ s' hr hroot
    · split at h
      · rename_i s' hs
        simp only [Option.some.injEq] at h
        subst h
        have := rewriteStep_lt env rules hr b s' hs
        simp only [weigh]; omega
      · cases h
  | .ex x b, s, h => by
    simp only [rewriteStep] at h
    split at h
    · rename_i s' hroot
      simp only [Option.some.injEq] at h
      subst h
      exact W.rootRewrite_lt env rules _ s' hr hroot
    · split at h
      · rename_i s' hs
        simp only [Option.some.injEq] at h
        subst h
        have := rewriteStep_lt env rules hr b s' hs
        simp only [weigh]; omega
      · cases h

theorem normalize_normal (env : String → Nat) (rules : List BRule)
    (hr : ∀ r ∈ rules, W.Decreases r) :
    ∀ (fuel : Nat) (e : BExpr), W.weigh env e ≤ fuel → (normalize rules fuel e).normal = true
  | 0, e, he => by
    simp only [normalize, Option.isNone_iff_eq_none]
    cases hs : rewriteStep rules e with
    | none => rfl
    | some s => have := W.rewriteStep_lt env rules hr e s hs; omega
  | fuel + 1, e, he => by
    simp only [normalize]
    split
    · rfl
    · rename_i id e' hs
      have := W.rewriteStep_lt env rules hr e (id, e') hs
      exact normalize_normal env rules hr fuel e' (by simp at this; omega)

end BasicWeight

/-- Normalizing any formula with `rules` reaches a normal form within its
`W`-weight (variables weigh `0`). -/
def Terminates (rules : List BRule) (W : BasicWeight) : Prop :=
  ∀ e, (normalize rules (W.weigh (fun _ => 0) e) e).normal = true

theorem BasicWeight.terminates (W : BasicWeight) (rules : List BRule)
    (hr : ∀ r ∈ rules, W.Decreases r) : Terminates rules W :=
  fun e => W.normalize_normal _ rules hr _ e le_rfl

end OSR.Logic
