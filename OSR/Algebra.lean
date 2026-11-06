import OSR.Catalog
import OSR.Termination

/-!
# Algebra

Migration of `OpenSymbolicRules/Algebra` at commit
`e8152ba57aa7a10a270a1e9ed16f75bede335ad1`: 16 of its 20 rules.  The other
four use symbolic exponents, which the fragment does not represent
(`notMigrated`).

Changes of representation relative to OSR v0.1, none of which changes the
mathematical statement:

* `Log` and `Exp` become `transc1#ln` and `transc1#exp`;
* `PositiveQ a` becomes the condition `a > 0` (`relation1#gt`), `NonzeroQ x`
  becomes `x ≠ 0` (`relation1#neq`);
* `Power` with a literal integer exponent becomes a natural-number power
  (`powNat`) or a negative one (`powNeg`).

`relation1#gt` has no complex interpretation, so the logarithm-of-a-product
rule is stated and certified over ℝ only.
-/

namespace OSR.Algebra

open OSR

private abbrev x : Expr := .var "x"
private abbrev z : Expr := .var "z"
private abbrev a : Expr := .var "a"
private abbrev b : Expr := .var "b"
private abbrev c : Expr := .var "c"
private abbrev zero : Expr := .int 0
private abbrev one : Expr := .int 1
private abbrev add (e f : Expr) : Expr := .app2 .add e f
private abbrev sub (e f : Expr) : Expr := .app2 .sub e f
private abbrev mul (e f : Expr) : Expr := .app2 .mul e f
private abbrev ln (e : Expr) : Expr := .app1 .ln e
private abbrev exp (e : Expr) : Expr := .app1 .exp e

private def repo : String := "OpenSymbolicRules/Algebra"
private def rev : String := "e8152ba57aa7a10a270a1e9ed16f75bede335ad1"

private def migrated (legacy : String) (orig : List Source := []) : Provenance :=
  { method := .derived,
    sources := { name := repo, locator := legacy, revision := some rev, license := some "MIT" } :: orig }

/-- Every profile of the rule set.  `default` simplifies and expands
products over sums; `factor_polynomials` factors common terms instead.  The
two orientations are kept apart, as in v0.1, so that both terminate. -/
def profiles : List String := ["default", "factor_polynomials"]

/-! ## Powers -/

/-- `x^1 ⟶ x`. -/
def powOne : Rule where
  id := "algebra.power.one"
  legacyId := some "algebra:1-powers/1.1-basic-exponents:3"
  vars := ["x"]
  lhs := .powNat x 1
  rhs := x
  profiles := ["default"]
  priority := 30
  description := "Identity power: x^1 = x"
  provenance := migrated "algebra:1-powers/1.1-basic-exponents:3"

/-- `x^0 ⟶ 1` for `x ≠ 0`. -/
def powZero : Rule where
  id := "algebra.power.zero"
  legacyId := some "algebra:1-powers/1.1-basic-exponents:4"
  vars := ["x"]
  lhs := .powNat x 0
  rhs := one
  conditions := [.ne x zero]
  profiles := ["default"]
  priority := 40
  description := "Zero power: x^0 = 1 for x != 0"
  provenance := migrated "algebra:1-powers/1.1-basic-exponents:4"

/-- `x^(-1) ⟶ 1/x` for `x ≠ 0`. -/
def powNegOne : Rule where
  id := "algebra.power.neg_one"
  legacyId := some "algebra:1-powers/1.1-basic-exponents:5"
  vars := ["x"]
  lhs := .powNeg x 0
  rhs := .app2 .div one x
  conditions := [.ne x zero]
  profiles := ["default"]
  priority := 50
  description := "Inverse power: x^(-1) = 1/x for x != 0"
  provenance := migrated "algebra:1-powers/1.1-basic-exponents:5"

/-! ## Logarithms -/

/-- `ln(a b) ⟶ ln a + ln b` for `a > 0` and `b > 0` (real). -/
def lnMul : Rule where
  id := "algebra.log.ln_mul"
  legacyId := some "algebra:2-logarithms/2.1-basic-logarithms:1"
  vars := ["a", "b"]
  lhs := ln (mul a b)
  rhs := add (ln a) (ln b)
  conditions := [.gt a zero, .gt b zero]
  profiles := ["default"]
  priority := 70
  description := "Log of a product: log(a * b) = log(a) + log(b)"
  provenance := migrated "algebra:2-logarithms/2.1-basic-logarithms:1"

/-- `exp(ln z) ⟶ z` for `z ≠ 0`. -/
def expLn : Rule where
  id := "algebra.log.exp_ln"
  legacyId := some "algebra:2-logarithms/2.1-basic-logarithms:3"
  vars := ["z"]
  lhs := exp (ln z)
  rhs := z
  conditions := [.ne z zero]
  profiles := ["default"]
  priority := 90
  description := "Exponential and principal natural logarithm are inverse for nonzero arguments"
  provenance := migrated "algebra:2-logarithms/2.1-basic-logarithms:3"
    [{ name := "Fungrim MathJSON", locator := "corpus/log.json#d87f6e", license := some "MIT" }]

/-! ## Polynomials -/

/-- `a (b + c) ⟶ a b + a c`. -/
def distribute : Rule where
  id := "algebra.polynomial.distribute"
  legacyId := some "algebra:3-polynomials/3.1-distribution:1"
  vars := ["a", "b", "c"]
  lhs := mul a (add b c)
  rhs := add (mul a b) (mul a c)
  profiles := ["default"]
  priority := 100
  description := "Distributive law: a * (b + c) = a * b + a * c"
  provenance := migrated "algebra:3-polynomials/3.1-distribution:1"

/-- `a b + a c ⟶ a (b + c)`. -/
def factorLeftAdd : Rule where
  id := "algebra.polynomial.factor_left_add"
  legacyId := some "algebra:3-polynomials/3.2-common-factor:1"
  vars := ["a", "b", "c"]
  lhs := add (mul a b) (mul a c)
  rhs := mul a (add b c)
  profiles := ["factor_polynomials"]
  priority := 110
  description := "Factor a common left factor from a sum"
  provenance := migrated "algebra:3-polynomials/3.2-common-factor:1"

/-- `b a + c a ⟶ (b + c) a`. -/
def factorRightAdd : Rule where
  id := "algebra.polynomial.factor_right_add"
  legacyId := some "algebra:3-polynomials/3.2-common-factor:2"
  vars := ["a", "b", "c"]
  lhs := add (mul b a) (mul c a)
  rhs := mul (add b c) a
  profiles := ["factor_polynomials"]
  priority := 120
  description := "Factor a common right factor from a sum"
  provenance := migrated "algebra:3-polynomials/3.2-common-factor:2"

/-- `a b - a c ⟶ a (b - c)`. -/
def factorLeftSub : Rule where
  id := "algebra.polynomial.factor_left_sub"
  legacyId := some "algebra:3-polynomials/3.2-common-factor:3"
  vars := ["a", "b", "c"]
  lhs := sub (mul a b) (mul a c)
  rhs := mul a (sub b c)
  profiles := ["factor_polynomials"]
  priority := 130
  description := "Factor a common left factor from a difference"
  provenance := migrated "algebra:3-polynomials/3.2-common-factor:3"

/-- `b a - c a ⟶ (b - c) a`. -/
def factorRightSub : Rule where
  id := "algebra.polynomial.factor_right_sub"
  legacyId := some "algebra:3-polynomials/3.2-common-factor:4"
  vars := ["a", "b", "c"]
  lhs := sub (mul b a) (mul c a)
  rhs := mul (sub b c) a
  profiles := ["factor_polynomials"]
  priority := 140
  description := "Factor a common right factor from a difference"
  provenance := migrated "algebra:3-polynomials/3.2-common-factor:4"

/-! ## Identities -/

/-- `x + 0 ⟶ x`. -/
def addZero : Rule where
  id := "algebra.identity.add_zero"
  legacyId := some "algebra:4-simplification/4.1-identities:1"
  vars := ["x"]
  lhs := add x zero
  rhs := x
  profiles := profiles
  priority := 150
  description := "Additive identity (right): x + 0 = x"
  provenance := migrated "algebra:4-simplification/4.1-identities:1"

/-- `0 + x ⟶ x`. -/
def zeroAdd : Rule where
  id := "algebra.identity.zero_add"
  legacyId := some "algebra:4-simplification/4.1-identities:2"
  vars := ["x"]
  lhs := add zero x
  rhs := x
  profiles := profiles
  priority := 160
  description := "Additive identity (left): 0 + x = x"
  provenance := migrated "algebra:4-simplification/4.1-identities:2"

/-- `x * 1 ⟶ x`. -/
def mulOne : Rule where
  id := "algebra.identity.mul_one"
  legacyId := some "algebra:4-simplification/4.1-identities:3"
  vars := ["x"]
  lhs := mul x one
  rhs := x
  profiles := profiles
  priority := 170
  description := "Multiplicative identity (right): x * 1 = x"
  provenance := migrated "algebra:4-simplification/4.1-identities:3"

/-- `1 * x ⟶ x`. -/
def oneMul : Rule where
  id := "algebra.identity.one_mul"
  legacyId := some "algebra:4-simplification/4.1-identities:4"
  vars := ["x"]
  lhs := mul one x
  rhs := x
  profiles := profiles
  priority := 180
  description := "Multiplicative identity (left): 1 * x = x"
  provenance := migrated "algebra:4-simplification/4.1-identities:4"

/-- `x * 0 ⟶ 0`. -/
def mulZero : Rule where
  id := "algebra.identity.mul_zero"
  legacyId := some "algebra:4-simplification/4.1-identities:5"
  vars := ["x"]
  lhs := mul x zero
  rhs := zero
  profiles := profiles
  priority := 190
  description := "Multiplication by zero (right): x * 0 = 0"
  provenance := migrated "algebra:4-simplification/4.1-identities:5"

/-- `0 * x ⟶ 0`. -/
def zeroMul : Rule where
  id := "algebra.identity.zero_mul"
  legacyId := some "algebra:4-simplification/4.1-identities:6"
  vars := ["x"]
  lhs := mul zero x
  rhs := zero
  profiles := profiles
  priority := 200
  description := "Multiplication by zero (left): 0 * x = 0"
  provenance := migrated "algebra:4-simplification/4.1-identities:6"

/-! ## Rules not migrated -/

/-- v0.1 rules outside the fragment, with the reason. -/
def notMigrated : List (String × String) := [
  ("algebra:1-powers/1.1-basic-exponents:1",
    "(x^p)^q = x^(p*q) with integer variables p, q: the fragment has no integer-valued variables or symbolic exponents"),
  ("algebra:1-powers/1.1-basic-exponents:2",
    "x^p * x^q = x^(p+q) with integer variables p, q: the fragment has no integer-valued variables or symbolic exponents"),
  ("algebra:1-powers/1.1-basic-exponents:6",
    "1^x = 1 with a symbolic exponent: general arith1#power (exp(a ln x)) is outside the fragment"),
  ("algebra:2-logarithms/2.1-basic-logarithms:2",
    "log(a^b) = b log(a) with a symbolic exponent: general arith1#power is outside the fragment")]

/-! ## Proofs -/

/-- Unfold `Rule.Holds`, keeping the conditions as `hc` and the definedness of
the pattern as `hd`. -/
local macro "alg_intro" r:ident i:ident : tactic => do
  let hc := Lean.mkIdent `hc
  let hd := Lean.mkIdent `hd
  `(tactic|
    (simp only [Rule.Holds, Rule.Sound]
     intro env $hc:ident $hd:ident
     simp only [$r:ident, $i:ident, Defined, eval, Cond.Holds, List.mem_cons, List.mem_nil_iff,
       or_false, forall_eq_or_imp, forall_eq, Int.cast_ofNat, Int.cast_one, Int.cast_zero,
       Int.cast_neg, true_and, and_true] at $hc:ident $hd:ident ⊢))

theorem powOne_real : powOne.Holds .real := by
  alg_intro powOne Interp.real; exact pow_one _

theorem powOne_complex : powOne.Holds .complex := by
  alg_intro powOne Interp.complex; exact pow_one _

theorem powZero_real : powZero.Holds .real := by
  alg_intro powZero Interp.real; exact pow_zero _

theorem powZero_complex : powZero.Holds .complex := by
  alg_intro powZero Interp.complex; exact pow_zero _

theorem powNegOne_real : powNegOne.Holds .real := by
  alg_intro powNegOne Interp.real
  exact ⟨hd, by simp⟩

theorem powNegOne_complex : powNegOne.Holds .complex := by
  alg_intro powNegOne Interp.complex
  exact ⟨hd, by simp⟩

theorem lnMul_real : lnMul.Holds .real := by
  alg_intro lnMul Interp.real
  exact ⟨⟨hc.1, hc.2⟩, Real.log_mul hc.1.ne' hc.2.ne'⟩

/-- Over ℝ, `ln z` is defined only for `z > 0`, which is what `Real.exp_log`
needs.  The v0.1 condition `z ≠ 0` alone would not suffice: Lean's
`Real.log` is even, so `exp (log z) = -z` for `z < 0`. -/
theorem expLn_real : expLn.Holds .real := by
  alg_intro expLn Interp.real; exact Real.exp_log hd

theorem expLn_complex : expLn.Holds .complex := by
  alg_intro expLn Interp.complex; exact Complex.exp_log hd

theorem distribute_real : distribute.Holds .real := by
  alg_intro distribute Interp.real; ring

theorem distribute_complex : distribute.Holds .complex := by
  alg_intro distribute Interp.complex; ring

theorem factorLeftAdd_real : factorLeftAdd.Holds .real := by
  alg_intro factorLeftAdd Interp.real; ring

theorem factorLeftAdd_complex : factorLeftAdd.Holds .complex := by
  alg_intro factorLeftAdd Interp.complex; ring

theorem factorRightAdd_real : factorRightAdd.Holds .real := by
  alg_intro factorRightAdd Interp.real; ring

theorem factorRightAdd_complex : factorRightAdd.Holds .complex := by
  alg_intro factorRightAdd Interp.complex; ring

theorem factorLeftSub_real : factorLeftSub.Holds .real := by
  alg_intro factorLeftSub Interp.real; ring

theorem factorLeftSub_complex : factorLeftSub.Holds .complex := by
  alg_intro factorLeftSub Interp.complex; ring

theorem factorRightSub_real : factorRightSub.Holds .real := by
  alg_intro factorRightSub Interp.real; ring

theorem factorRightSub_complex : factorRightSub.Holds .complex := by
  alg_intro factorRightSub Interp.complex; ring

theorem addZero_real : addZero.Holds .real := by
  alg_intro addZero Interp.real; ring

theorem addZero_complex : addZero.Holds .complex := by
  alg_intro addZero Interp.complex; ring

theorem zeroAdd_real : zeroAdd.Holds .real := by
  alg_intro zeroAdd Interp.real; ring

theorem zeroAdd_complex : zeroAdd.Holds .complex := by
  alg_intro zeroAdd Interp.complex; ring

theorem mulOne_real : mulOne.Holds .real := by
  alg_intro mulOne Interp.real; ring

theorem mulOne_complex : mulOne.Holds .complex := by
  alg_intro mulOne Interp.complex; ring

theorem oneMul_real : oneMul.Holds .real := by
  alg_intro oneMul Interp.real; ring

theorem oneMul_complex : oneMul.Holds .complex := by
  alg_intro oneMul Interp.complex; ring

theorem mulZero_real : mulZero.Holds .real := by
  alg_intro mulZero Interp.real; ring

theorem mulZero_complex : mulZero.Holds .complex := by
  alg_intro mulZero Interp.complex; ring

theorem zeroMul_real : zeroMul.Holds .real := by
  alg_intro zeroMul Interp.real; ring

theorem zeroMul_complex : zeroMul.Holds .complex := by
  alg_intro zeroMul Interp.complex; ring

/-! ## Catalogue -/

private def domainFinding : String :=
  "semantics: x * 0 = 0 and 0 * x = 0 discard x; under defined_pattern the pattern is required to be defined, so x is defined, and the rewrite can only enlarge the domain of definition, never change a value."

/-- The Algebra catalogue, in v0.1 load order (= priority order). -/
def catalog : List CatalogEntry := [
  { rule := powOne, ruleDecl := ``powOne,
    proofs := [(.real, ``powOne_real), (.complex, ``powOne_complex)] },
  { rule := powZero, ruleDecl := ``powZero,
    proofs := [(.real, ``powZero_real), (.complex, ``powZero_complex)],
    findings := ["semantics: x^0 = 1 holds in Lean for every x, including 0; the v0.1 condition x != 0 is kept, so the rule is not strengthened."] },
  { rule := powNegOne, ruleDecl := ``powNegOne,
    proofs := [(.real, ``powNegOne_real), (.complex, ``powNegOne_complex)],
    findings := ["semantics: x^(-1) is defined only for x != 0, so the v0.1 condition repeats the definedness of the pattern; it is kept."] },
  { rule := lnMul, ruleDecl := ``lnMul,
    proofs := [(.real, ``lnMul_real)],
    findings := ["complex: not stated; the condition a > 0 (relation1#gt) has no complex interpretation."] },
  { rule := expLn, ruleDecl := ``expLn,
    proofs := [(.real, ``expLn_real), (.complex, ``expLn_complex)],
    findings := ["real: the v0.1 condition z != 0 (from the complex Fungrim entry d87f6e) does not suffice over ℝ; the rule holds because ln is defined only for z > 0 there, so engines must not apply it to a negative real z."] },
  { rule := distribute, ruleDecl := ``distribute,
    proofs := [(.real, ``distribute_real), (.complex, ``distribute_complex)] },
  { rule := factorLeftAdd, ruleDecl := ``factorLeftAdd,
    proofs := [(.real, ``factorLeftAdd_real), (.complex, ``factorLeftAdd_complex)] },
  { rule := factorRightAdd, ruleDecl := ``factorRightAdd,
    proofs := [(.real, ``factorRightAdd_real), (.complex, ``factorRightAdd_complex)] },
  { rule := factorLeftSub, ruleDecl := ``factorLeftSub,
    proofs := [(.real, ``factorLeftSub_real), (.complex, ``factorLeftSub_complex)] },
  { rule := factorRightSub, ruleDecl := ``factorRightSub,
    proofs := [(.real, ``factorRightSub_real), (.complex, ``factorRightSub_complex)] },
  { rule := addZero, ruleDecl := ``addZero,
    proofs := [(.real, ``addZero_real), (.complex, ``addZero_complex)] },
  { rule := zeroAdd, ruleDecl := ``zeroAdd,
    proofs := [(.real, ``zeroAdd_real), (.complex, ``zeroAdd_complex)] },
  { rule := mulOne, ruleDecl := ``mulOne,
    proofs := [(.real, ``mulOne_real), (.complex, ``mulOne_complex)] },
  { rule := oneMul, ruleDecl := ``oneMul,
    proofs := [(.real, ``oneMul_real), (.complex, ``oneMul_complex)] },
  { rule := mulZero, ruleDecl := ``mulZero,
    proofs := [(.real, ``mulZero_real), (.complex, ``mulZero_complex)],
    findings := [domainFinding] },
  { rule := zeroMul, ruleDecl := ``zeroMul,
    proofs := [(.real, ``zeroMul_real), (.complex, ``zeroMul_complex)],
    findings := [domainFinding] }
]

/-! ## Profiles, engine soundness and termination -/

/-- The rules of a profile, in priority order. -/
def profileRules (p : String) : List Rule :=
  (catalog.map (·.rule)).filter (p ∈ ·.profiles)

theorem profileRules_default :
    profileRules "default" = [powOne, powZero, powNegOne, lnMul, expLn, distribute, addZero, zeroAdd,
      mulOne, oneMul, mulZero, zeroMul] :=
  rfl

theorem profileRules_factor :
    profileRules "factor_polynomials" = [factorLeftAdd, factorRightAdd, factorLeftSub,
      factorRightSub, addZero, zeroAdd, mulOne, oneMul, mulZero, zeroMul] :=
  rfl

/-- Weight of the `default` profile: logarithms weigh exponentially, so
splitting a product pays for the extra sum; products weigh multiplicatively,
so distributing pays for the extra product. -/
def defaultWeight : Weight where
  int _ := 1
  const _ := 1
  op1 o a := match o with
    | .ln => 4 ^ (a + 1)
    | _ => a + 1
  op2 o a b := match o with
    | .mul => (a + 2) * (b + 2)
    | _ => a + b + 5
  pow a k := a + k + 2
  powNeg a k := a + k + 7
  mono1 o a a' h := by
    cases o <;> simp only
    all_goals first | omega | exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  mono2l o a a' b h := by cases o <;> simp only <;> first | omega | nlinarith
  mono2r o a b b' h := by cases o <;> simp only <;> first | omega | nlinarith
  monoPow _ _ _ h := by omega
  monoPowNeg _ _ _ h := by omega

/-- Weight of the `factor_polynomials` profile: every operator adds one, so
factoring removes one occurrence of the common factor. -/
def factorWeight : Weight where
  int _ := 1
  const _ := 1
  op1 _ a := a + 1
  op2 _ a b := a + b + 1
  pow a k := a + k + 1
  powNeg a k := a + k + 2
  mono1 _ _ _ h := by omega
  mono2l _ _ _ _ h := by omega
  mono2r _ _ _ _ h := by omega
  monoPow _ _ _ h := by omega
  monoPowNeg _ _ _ h := by omega

private theorem lnMul_decreases (p q : Nat) :
    4 ^ (p + 1) + 4 ^ (q + 1) + 5 < 4 ^ ((p + 2) * (q + 2) + 1) := by
  have hp : 1 ≤ 4 ^ p := Nat.one_le_pow _ _ (by norm_num)
  have hq : 1 ≤ 4 ^ q := Nat.one_le_pow _ _ (by norm_num)
  have hle : p + q + 5 ≤ (p + 2) * (q + 2) + 1 := by nlinarith
  have hmono : 4 ^ (p + q + 5) ≤ 4 ^ ((p + 2) * (q + 2) + 1) :=
    Nat.pow_le_pow_right (by norm_num) hle
  have hexp : 4 ^ (p + q + 5) = 4 ^ p * 4 ^ q * 1024 := by ring
  rw [hexp] at hmono
  have : 4 ^ (p + 1) + 4 ^ (q + 1) + 5 < 4 ^ p * 4 ^ q * 1024 := by
    rw [pow_succ, pow_succ]; nlinarith
  omega

theorem default_decreasing : ∀ r ∈ profileRules "default", defaultWeight.Decreases r := by
  rw [profileRules_default]
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro env <;>
    simp only [Weight.eval, defaultWeight, powOne, powZero, powNegOne, lnMul, expLn, distribute, addZero,
      zeroAdd, mulOne, oneMul, mulZero, zeroMul]
  · omega
  · omega
  · omega
  · exact lnMul_decreases _ _
  · have : env "z" + 1 < 4 ^ (env "z" + 1) := Nat.lt_pow_self (by norm_num); omega
  all_goals nlinarith

theorem factor_decreasing :
    ∀ r ∈ profileRules "factor_polynomials", factorWeight.Decreases r := by
  rw [profileRules_factor]
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro env <;>
    simp only [Weight.eval, factorWeight, factorLeftAdd, factorRightAdd, factorLeftSub,
      factorRightSub, addZero, zeroAdd, mulOne, oneMul, mulZero, zeroMul] <;> omega

theorem default_terminates : Terminates (profileRules "default") defaultWeight :=
  defaultWeight.terminates _ default_decreasing

theorem factor_terminates : Terminates (profileRules "factor_polynomials") factorWeight :=
  factorWeight.terminates _ factor_decreasing

private theorem catalog_closed : ∀ e ∈ catalog, e.rule.rhsClosed = true := by
  intro e he
  simp only [catalog, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;> decide

private theorem unconditional_holds (d : Domain) :
    ∀ e ∈ catalog, e.rule.conditions.isEmpty → e.rule.Holds d := by
  intro e he hc
  simp only [catalog, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;> simp [powZero, powNegOne, lnMul, expLn] at hc <;> cases d
  all_goals first
    | exact powOne_real | exact powOne_complex | exact distribute_real
    | exact distribute_complex | exact factorLeftAdd_real | exact factorLeftAdd_complex
    | exact factorRightAdd_real | exact factorRightAdd_complex | exact factorLeftSub_real
    | exact factorLeftSub_complex | exact factorRightSub_real | exact factorRightSub_complex
    | exact addZero_real | exact addZero_complex | exact zeroAdd_real | exact zeroAdd_complex
    | exact mulOne_real | exact mulOne_complex | exact oneMul_real | exact oneMul_complex
    | exact mulZero_real | exact mulZero_complex | exact zeroMul_real | exact zeroMul_complex

theorem profileRules_sound_real (p : String) : RulesSound Interp.real (profileRules p) := by
  intro r hr hc
  simp only [profileRules, List.mem_filter, List.mem_map] at hr
  obtain ⟨⟨e, he, rfl⟩, _⟩ := hr
  exact ⟨unconditional_holds .real e he hc, catalog_closed e he⟩

theorem profileRules_sound_complex (p : String) :
    RulesSound Interp.complex (profileRules p) := by
  intro r hr hc
  simp only [profileRules, List.mem_filter, List.mem_map] at hr
  obtain ⟨⟨e, he, rfl⟩, _⟩ := hr
  exact ⟨unconditional_holds .complex e he hc, catalog_closed e he⟩

/-- Running the reference engine with any Algebra profile over ℝ preserves
definedness and value. -/
theorem normalize_sound_real (p : String) (fuel : Nat) (env : String → ℝ) (e : Expr) :
    Preserves Interp.real env e (normalize (profileRules p) fuel e).result :=
  normalize_sound _ (profileRules_sound_real p) fuel e

/-- Running the reference engine with any Algebra profile over ℂ preserves
definedness and value. -/
theorem normalize_sound_complex (p : String) (fuel : Nat) (env : String → ℂ) (e : Expr) :
    Preserves Interp.complex env e (normalize (profileRules p) fuel e).result :=
  normalize_sound _ (profileRules_sound_complex p) fuel e

end OSR.Algebra
