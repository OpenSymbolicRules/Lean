import OSR.Calculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-! # Symbolic derivative

`SymDeriv.d x e` is the derivative of the expression `e` with respect to the variable `x`, for
the fragment built from variables, integers, `π`, `+`, `-`, `*`, `/`, `−`, `sin`, `cos`,
`exp`, `ln`, `tan`, `arctan`, `sinh`, `cosh`, `arcsin`, `arccos`, the square root and powers
with an exponent free of `x`.

`hasStrictDerivAt_eval` proves it sound: wherever `Ok` holds (each logarithm and square root
is applied in its region of differentiability, each divisor is nonzero, and each power has an
integer exponent free of `x` with a nonzero base or a nonnegative exponent), the value of `e`
has strict derivative the value of `d x e`. The derivative facts of an interpretation are
collected in `Calc`; `Calc.real` and `Calc.complex` give them for ℝ and ℂ. -/

namespace OSR.SymDeriv
open OSR OSR.Calculus Filter Topology

/-- The derivative of an expression with respect to `x`. -/
def d (x : String) : Expr → Expr
  | .var n => if n = x then .int 1 else .int 0
  | .int _ => .int 0
  | .const _ => .int 0
  | .app1 .neg a => .app1 .neg (d x a)
  | .app1 .sin a => .app2 .mul (.app1 .cos a) (d x a)
  | .app1 .cos a => .app2 .mul (.app1 .neg (.app1 .sin a)) (d x a)
  | .app1 .exp a => .app2 .mul (.app1 .exp a) (d x a)
  | .app1 .ln a => .app2 .mul (.pow a (.int (-1))) (d x a)
  | .app1 .tan a => .app2 .mul (.app2 .div (.int 1) (.pow (.app1 .cos a) (.int 2))) (d x a)
  | .app1 .arctan a =>
    .app2 .mul (.app2 .div (.int 1) (.app2 .add (.int 1) (.pow a (.int 2)))) (d x a)
  | .app1 .sinh a => .app2 .mul (.app1 .cosh a) (d x a)
  | .app1 .cosh a => .app2 .mul (.app1 .sinh a) (d x a)
  | .app1 .arcsin a => .app2 .mul (.app2 .div (.int 1)
      (.app2 .root (.app2 .sub (.int 1) (.pow a (.int 2))) (.int 2))) (d x a)
  | .app1 .arccos a => .app2 .mul (.app1 .neg (.app2 .div (.int 1)
      (.app2 .root (.app2 .sub (.int 1) (.pow a (.int 2))) (.int 2)))) (d x a)
  | .app1 _ _ => .int 0
  | .app2 .add a b => .app2 .add (d x a) (d x b)
  | .app2 .sub a b => .app2 .sub (d x a) (d x b)
  | .app2 .mul a b => .app2 .add (.app2 .mul (d x a) b) (.app2 .mul a (d x b))
  | .app2 .div a b =>
    .app2 .div (.app2 .sub (.app2 .mul (d x a) b) (.app2 .mul a (d x b))) (.pow b (.int 2))
  | .app2 .root a n =>
    .app2 .mul (.app2 .div (.int 1) (.app2 .mul (.int 2) (.app2 .root a n))) (d x a)
  | .pow a e => .app2 .mul (.app2 .mul e (.pow a (.app2 .add e (.int (-1))))) (d x a)

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

/-- The derivative facts of an interpretation used by `d`. -/
structure Calc (I : Interp 𝕜) where
  /-- Where `ln` is differentiable. -/
  lnOk : 𝕜 → Prop
  /-- Where the square root is differentiable. -/
  rootOk : 𝕜 → Prop
  sin : ∀ z, HasStrictDerivAt I.sin (I.cos z) z
  cos : ∀ z, HasStrictDerivAt I.cos (-I.sin z) z
  exp : ∀ z, HasStrictDerivAt I.exp (I.exp z) z
  ln : ∀ z, lnOk z → HasStrictDerivAt I.ln z⁻¹ z
  root : ∀ z n, rootOk z → I.toInt? n = some 2 →
    HasStrictDerivAt (fun w => I.root w n) (1 / (2 * I.root z n)) z
  /-- `ln` is defined near a point where it is differentiable. -/
  lnOpen : ∀ z, lnOk z → ∀ᶠ w in 𝓝 z, I.lnDefined w
  /-- The square root is defined near a point where it is differentiable. -/
  rootOpen : ∀ z n, rootOk z → I.toInt? n = some 2 → ∀ᶠ w in 𝓝 z, I.rootDefined w n
  /-- Where `tan`, `arctan`, `arcsin`, `arccos` are differentiable. -/
  tanOk : 𝕜 → Prop
  arctanOk : 𝕜 → Prop
  asinOk : 𝕜 → Prop
  acosOk : 𝕜 → Prop
  tan : ∀ z, tanOk z → HasStrictDerivAt I.tan (1 / I.cos z ^ (2 : ℤ)) z
  tanOpen : ∀ z, tanOk z → ∀ᶠ w in 𝓝 z, I.tanDefined w
  arctan : ∀ z, arctanOk z → HasStrictDerivAt I.arctan (1 / (1 + z ^ (2 : ℤ))) z
  arctanOpen : ∀ z, arctanOk z → ∀ᶠ w in 𝓝 z, I.arctanDefined w
  sinh : ∀ z, HasStrictDerivAt (I.fn .sinh) (I.fn .cosh z) z
  cosh : ∀ z, HasStrictDerivAt (I.fn .cosh) (I.fn .sinh z) z
  sinhDef : ∀ z, I.fnDefined .sinh z
  coshDef : ∀ z, I.fnDefined .cosh z
  asin : ∀ z, asinOk z →
    HasStrictDerivAt (I.fn .arcsin) (1 / I.root (1 - z ^ (2 : ℤ)) ((2 : ℤ) : 𝕜)) z
  asinOpen : ∀ z, asinOk z → ∀ᶠ w in 𝓝 z, I.fnDefined .arcsin w
  acos : ∀ z, acosOk z →
    HasStrictDerivAt (I.fn .arccos) (-(1 / I.root (1 - z ^ (2 : ℤ)) ((2 : ℤ) : 𝕜))) z
  acosOpen : ∀ z, acosOk z → ∀ᶠ w in 𝓝 z, I.fnDefined .arccos w

variable {I : Interp 𝕜}

/-- Where `d` is a derivative: the conditions of `hasStrictDerivAt_eval` at the assignment
`ρ` (whose value at `x` is the point). -/
def Ok (C : Calc I) (x : String) (ρ : String → 𝕜) : Expr → Prop
  | .var _ => True
  | .int _ => True
  | .const _ => True
  | .app1 .neg a => Ok C x ρ a
  | .app1 .sin a => Ok C x ρ a
  | .app1 .cos a => Ok C x ρ a
  | .app1 .exp a => Ok C x ρ a
  | .app1 .ln a => Ok C x ρ a ∧ C.lnOk (eval I ρ a)
  | .app1 .tan a => Ok C x ρ a ∧ C.tanOk (eval I ρ a)
  | .app1 .arctan a => Ok C x ρ a ∧ C.arctanOk (eval I ρ a)
  | .app1 .sinh a => Ok C x ρ a
  | .app1 .cosh a => Ok C x ρ a
  | .app1 .arcsin a => Ok C x ρ a ∧ C.asinOk (eval I ρ a)
  | .app1 .arccos a => Ok C x ρ a ∧ C.acosOk (eval I ρ a)
  | .app1 _ _ => False
  | .app2 .add a b => Ok C x ρ a ∧ Ok C x ρ b
  | .app2 .sub a b => Ok C x ρ a ∧ Ok C x ρ b
  | .app2 .mul a b => Ok C x ρ a ∧ Ok C x ρ b
  | .app2 .div a b => Ok C x ρ a ∧ Ok C x ρ b ∧ eval I ρ b ≠ 0
  | .app2 .root a n => Ok C x ρ a ∧ x ∉ n.varList ∧ I.toInt? (eval I ρ n) = some 2 ∧
      C.rootOk (eval I ρ a)
  | .pow a e => Ok C x ρ a ∧ x ∉ e.varList ∧
      ∃ m, I.toInt? (eval I ρ e) = some m ∧ (eval I ρ a ≠ 0 ∨ 0 ≤ m)

/-- An expression free of `x` does not depend on its value. -/
theorem eval_update_free (env : String → 𝕜) {x : String} {e : Expr} (h : x ∉ e.varList)
    (v w : 𝕜) : eval I (Function.update env x v) e = eval I (Function.update env x w) e :=
  Calculus.eval_congr I e fun n hn => by
    have : n ≠ x := fun h' => h (h' ▸ hn)
    simp [Function.update, this]

/-- **Soundness of `d`.** -/
theorem hasStrictDerivAt_eval (C : Calc I) (x : String) (env : String → 𝕜) (t : 𝕜) :
    ∀ e : Expr, Ok C x (Function.update env x t) e →
      HasStrictDerivAt (fun v => eval I (Function.update env x v) e)
        (eval I (Function.update env x t) (d x e)) t := by
  intro e
  induction e with
  | var n =>
    intro _
    by_cases hn : n = x
    · subst hn
      have hf : (fun v => eval I (Function.update env n v) (.var n)) = fun v => v := by
        funext v; simp [eval]
      rw [hf]
      convert hasStrictDerivAt_id t using 1
      all_goals first | rfl | simp [d, eval]
    · have hf : (fun v => eval I (Function.update env x v) (.var n)) = fun _ => env n := by
        funext v; simp [eval, Function.update, hn]
      rw [hf]
      simpa [eval, d, hn] using hasStrictDerivAt_const t (env n)
  | int z =>
    intro _
    simpa [eval, d] using hasStrictDerivAt_const t (z : 𝕜)
  | const c =>
    intro _
    cases c
    simpa [eval, d] using hasStrictDerivAt_const t I.pi
  | app1 o a ih =>
    intro h
    cases o
    case neg => exact (ih h).neg
    case sin => exact (C.sin _).comp t (ih h)
    case cos => exact (C.cos _).comp t (ih h)
    case exp => exact (C.exp _).comp t (ih h)
    case ln =>
      have hm1 : I.toInt? (((-1 : ℤ)) : 𝕜) = some (-1) := Interp.toInt?_cast I (-1)
      convert (C.ln _ h.2).comp t (ih h.1) using 1
      · rfl
      · simp only [d, eval]
        simp only [hm1, zpow_neg_one]
    case sinh => exact (C.sinh _).comp t (ih h)
    case cosh => exact (C.cosh _).comp t (ih h)
    case tan =>
      have h2 : I.toInt? (((2 : ℤ)) : 𝕜) = some 2 := Interp.toInt?_cast I 2
      convert (C.tan _ h.2).comp t (ih h.1) using 1
      · rfl
      · simp only [d, eval, h2, Int.cast_one]
    case arctan =>
      have h2 : I.toInt? (((2 : ℤ)) : 𝕜) = some 2 := Interp.toInt?_cast I 2
      convert (C.arctan _ h.2).comp t (ih h.1) using 1
      · rfl
      · simp only [d, eval, h2, Int.cast_one]
    case arcsin =>
      have h2 : I.toInt? (((2 : ℤ)) : 𝕜) = some 2 := Interp.toInt?_cast I 2
      convert (C.asin _ h.2).comp t (ih h.1) using 1
      · rfl
      · simp only [d, eval, h2, Int.cast_one]
    case arccos =>
      have h2 : I.toInt? (((2 : ℤ)) : 𝕜) = some 2 := Interp.toInt?_cast I 2
      convert (C.acos _ h.2).comp t (ih h.1) using 1
      · rfl
      · simp only [d, eval, h2, Int.cast_one]
    all_goals exact (by simp [Ok] at h)
  | app2 o a b iha ihb =>
    intro h
    cases o
    case add => exact (iha h.1).add (ihb h.2)
    case sub => exact (iha h.1).sub (ihb h.2)
    case mul => exact (iha h.1).mul (ihb h.2)
    case div =>
      have h2 : I.toInt? (((2 : ℤ)) : 𝕜) = some 2 := Interp.toInt?_cast I 2
      convert (iha h.1).div (ihb h.2.1) h.2.2 using 1
      · rfl
      · simp only [d, eval]
        simp only [h2, zpow_ofNat]
    case root =>
      obtain ⟨ha, hx, h2, hr⟩ := h
      have hn : ∀ v, eval I (Function.update env x v) b = eval I (Function.update env x t) b :=
        fun v => eval_update_free env hx v t
      convert (C.root _ _ hr h2).comp t (iha ha) using 1
      · funext v
        simp only [eval, Function.comp_apply, hn v]
      · simp only [d, eval]
        push_cast
        ring
  | pow a e iha ihe =>
    intro h
    obtain ⟨ha, hx, m, hm, h0⟩ := h
    have he : ∀ v, eval I (Function.update env x v) e = eval I (Function.update env x t) e :=
      fun v => eval_update_free env hx v t
    have hE : eval I (Function.update env x t) e = (m : 𝕜) := (I.toInt?_eq _ _).1 hm
    have hm1 : I.toInt? (eval I (Function.update env x t) e + ((-1 : ℤ) : 𝕜)) = some (m - 1) :=
      (I.toInt?_eq _ _).2 (by rw [hE]; push_cast; ring)
    convert (hasStrictDerivAt_zpow m _ h0).comp t (iha ha) using 1
    · funext v
      simp only [eval, Function.comp_apply, he v, hm]
    · simp only [d, eval]
      rw [hm1, hE]

/-- The derivative facts of the real interpretation. -/
noncomputable def Calc.real : Calc Interp.real where
  lnOk z := 0 < z
  rootOk z := 0 < z
  sin z := Real.hasStrictDerivAt_sin z
  cos z := Real.hasStrictDerivAt_cos z
  exp z := Real.hasStrictDerivAt_exp z
  ln z hz := Real.hasStrictDerivAt_log hz.ne'
  root z n hz _ := by simpa [Interp.real] using Real.hasStrictDerivAt_sqrt hz.ne'
  lnOpen z hz := by simpa [Interp.real] using eventually_gt_nhds hz
  rootOpen z n hz hn := by
    filter_upwards [eventually_gt_nhds hz] with w hw
    exact ⟨hn, hw.le⟩
  tanOk z := Real.cos z ≠ 0
  arctanOk _ := True
  asinOk z := -1 < z ∧ z < 1
  acosOk z := -1 < z ∧ z < 1
  tan z hz := by simpa [Interp.real] using Real.hasStrictDerivAt_tan hz
  tanOpen z hz := Real.continuous_cos.continuousAt.eventually_ne hz
  arctan z _ := by simpa [Interp.real] using Real.hasStrictDerivAt_arctan z
  arctanOpen _ _ := Filter.Eventually.of_forall fun _ => trivial
  sinh z := Real.hasStrictDerivAt_sinh z
  cosh z := Real.hasStrictDerivAt_cosh z
  sinhDef _ := trivial
  coshDef _ := trivial
  asin z hz := by
    simpa [Interp.real] using Real.hasStrictDerivAt_arcsin (by linarith [hz.1]) (by linarith [hz.2])
  asinOpen z hz := by
    filter_upwards [Ioo_mem_nhds hz.1 hz.2] with w hw
    exact ⟨hw.1.le, hw.2.le⟩
  acos z hz := by
    simpa [Interp.real] using Real.hasStrictDerivAt_arccos (by linarith [hz.1]) (by linarith [hz.2])
  acosOpen z hz := by
    filter_upwards [Ioo_mem_nhds hz.1 hz.2] with w hw
    exact ⟨hw.1.le, hw.2.le⟩

/-- The derivative facts of the complex interpretation (principal logarithm off the cut; the
square root has no complex interpretation in the fragment). -/
noncomputable def Calc.complex : Calc Interp.complex where
  lnOk z := z ∈ Complex.slitPlane
  rootOk _ := False
  sin z := Complex.hasStrictDerivAt_sin z
  cos z := Complex.hasStrictDerivAt_cos z
  exp z := Complex.hasStrictDerivAt_exp z
  ln _ hz := Complex.hasStrictDerivAt_log hz
  root _ _ hz _ := hz.elim
  lnOpen z hz := by
    filter_upwards [Complex.isOpen_slitPlane.mem_nhds hz] with w hw
    exact Complex.slitPlane_ne_zero hw
  rootOpen _ _ hz _ := hz.elim
  tanOk z := Complex.cos z ≠ 0
  arctanOk _ := False
  asinOk _ := False
  acosOk _ := False
  tan z hz := by simpa [Interp.complex] using Complex.hasStrictDerivAt_tan hz
  tanOpen z hz := Complex.continuous_cos.continuousAt.eventually_ne hz
  arctan _ hz := hz.elim
  arctanOpen _ hz := hz.elim
  sinh z := Complex.hasStrictDerivAt_sinh z
  cosh z := Complex.hasStrictDerivAt_cosh z
  sinhDef _ := trivial
  coshDef _ := trivial
  asin _ hz := hz.elim
  asinOpen _ hz := hz.elim
  acos _ hz := hz.elim
  acosOpen _ hz := hz.elim

/-- Where `Ok` holds, definedness is an open condition: an expression defined at the point is
defined near it. -/
theorem eventually_defined (C : Calc I) (x : String) (env : String → 𝕜) (t : 𝕜) :
    ∀ e : Expr, Ok C x (Function.update env x t) e → Defined I (Function.update env x t) e →
      ∀ᶠ v in 𝓝 t, Defined I (Function.update env x v) e := by
  intro e
  induction e with
  | var n => intro _ _; exact Filter.Eventually.of_forall fun _ => trivial
  | int z => intro _ _; exact Filter.Eventually.of_forall fun _ => trivial
  | const c => intro _ _; exact Filter.Eventually.of_forall fun _ => trivial
  | app1 o a ih =>
    intro h hd
    cases o
    case neg => exact ih h hd
    case sin => exact ih h hd
    case cos => exact ih h hd
    case exp => exact ih h hd
    case ln =>
      have hc := (hasStrictDerivAt_eval C x env t a h.1).hasDerivAt.continuousAt
      filter_upwards [ih h.1 hd.1, hc.eventually (C.lnOpen _ h.2)] with v h1 h2
      exact ⟨h1, h2⟩
    case tan =>
      have hc := (hasStrictDerivAt_eval C x env t a h.1).hasDerivAt.continuousAt
      filter_upwards [ih h.1 hd.1, hc.eventually (C.tanOpen _ h.2)] with v h1 h2
      exact ⟨h1, h2⟩
    case arctan =>
      have hc := (hasStrictDerivAt_eval C x env t a h.1).hasDerivAt.continuousAt
      filter_upwards [ih h.1 hd.1, hc.eventually (C.arctanOpen _ h.2)] with v h1 h2
      exact ⟨h1, h2⟩
    case sinh =>
      filter_upwards [ih h hd.1] with v h1
      exact ⟨h1, C.sinhDef _⟩
    case cosh =>
      filter_upwards [ih h hd.1] with v h1
      exact ⟨h1, C.coshDef _⟩
    case arcsin =>
      have hc := (hasStrictDerivAt_eval C x env t a h.1).hasDerivAt.continuousAt
      filter_upwards [ih h.1 hd.1, hc.eventually (C.asinOpen _ h.2)] with v h1 h2
      exact ⟨h1, h2⟩
    case arccos =>
      have hc := (hasStrictDerivAt_eval C x env t a h.1).hasDerivAt.continuousAt
      filter_upwards [ih h.1 hd.1, hc.eventually (C.acosOpen _ h.2)] with v h1 h2
      exact ⟨h1, h2⟩
    all_goals exact (by simp [Ok] at h)
  | app2 o a b iha ihb =>
    intro h hd
    cases o
    case add =>
      filter_upwards [iha h.1 hd.1, ihb h.2 hd.2] with v h1 h2
      exact ⟨h1, h2⟩
    case sub =>
      filter_upwards [iha h.1 hd.1, ihb h.2 hd.2] with v h1 h2
      exact ⟨h1, h2⟩
    case mul =>
      filter_upwards [iha h.1 hd.1, ihb h.2 hd.2] with v h1 h2
      exact ⟨h1, h2⟩
    case div =>
      have hc := (hasStrictDerivAt_eval C x env t b h.2.1).hasDerivAt.continuousAt
      filter_upwards [iha h.1 hd.1, ihb h.2.1 hd.2.1, hc.eventually_ne h.2.2] with v h1 h2 h3
      exact ⟨h1, h2, h3⟩
    case root =>
      obtain ⟨ha, hx, h2, hr⟩ := h
      have hn : ∀ v, eval I (Function.update env x v) b = eval I (Function.update env x t) b :=
        fun v => eval_update_free env hx v t
      have hnd : ∀ v, Defined I (Function.update env x v) b ↔ Defined I (Function.update env x t) b :=
        fun v => Calculus.defined_congr I b fun n hn' => by
          have : n ≠ x := fun h' => hx (h' ▸ hn')
          simp [Function.update, this]
      have hc := (hasStrictDerivAt_eval C x env t a ha).hasDerivAt.continuousAt
      filter_upwards [iha ha hd.1, hc.eventually (C.rootOpen _ _ hr h2)] with v h1 h3
      exact ⟨h1, (hnd v).2 hd.2.1, by rw [hn v]; exact h3⟩
  | pow a e iha ihe =>
    intro h hd
    obtain ⟨ha, hx, m, hm, h0⟩ := h
    have he : ∀ v, eval I (Function.update env x v) e = eval I (Function.update env x t) e :=
      fun v => eval_update_free env hx v t
    have hed : ∀ v, Defined I (Function.update env x v) e ↔ Defined I (Function.update env x t) e :=
      fun v => Calculus.defined_congr I e fun n hn' => by
        have : n ≠ x := fun h' => hx (h' ▸ hn')
        simp [Function.update, this]
    obtain ⟨hda, hde, m', hm', hne⟩ := hd
    have hmm : m' = m := by rw [hm] at hm'; exact (Option.some.inj hm').symm
    subst hmm
    have hc := (hasStrictDerivAt_eval C x env t a ha).hasDerivAt.continuousAt
    by_cases hneg : m' < 0
    · filter_upwards [iha ha hda, hc.eventually_ne (hne hneg)] with v h1 h3
      exact ⟨h1, (hed v).2 hde, m', by rw [he v]; exact hm, fun _ => h3⟩
    · filter_upwards [iha ha hda] with v h1
      exact ⟨h1, (hed v).2 hde, m', by rw [he v]; exact hm, fun h' => absurd h' hneg⟩

/-! ## Substitution by the chain rule -/

/-- **Substitution `u = g(x)`.** A rule `∫ F dx = K · ∫ H du` with `u = g(x)` holds once, near
every point `t` where `F` is defined, `g` is differentiable in the sense of `Ok` with
`g'(t) ≠ 0`, `g` and `H ∘ g` are defined, and `F(t) = K · H(g(t)) · g'(t)`: the strict
derivative makes `g` a local homeomorphism, which carries the definedness of `H ∘ g` near `t` to
that of `H` near `g(t)`, and the chain rule gives the derivative. -/
theorem antiderivSubst_chain [CompleteSpace 𝕜] (C : Calc I) {cs : List Cond} (F H g K : Expr)
    (hKx : "x" ∉ K.varList) (hKI : "I1" ∉ K.varList)
    (hobl : ∀ env : String → 𝕜, (∀ k ∈ cs, k.Holds I env) → ∀ t : 𝕜,
      (∀ᶠ v in 𝓝 t, Defined I (Function.update env "x" v) F) →
      Defined I env K ∧ Ok C "x" (Function.update env "x" t) g ∧
      eval I (Function.update env "x" t) (d "x" g) ≠ 0 ∧
      (∀ᶠ v in 𝓝 t, Defined I (Function.update env "x" v) g ∧
        Defined I (Function.update env "x" (eval I (Function.update env "x" v) g)) H) ∧
      eval I (Function.update env "x" t) F =
        eval I env K * eval I (Function.update env "x" (eval I (Function.update env "x" t) g)) H *
          eval I (Function.update env "x" t) (d "x" g)) :
    AntiderivSubstHolds I "x" cs F (.app2 .mul K (.var "I1")) [("I1", H)] [("I1", g)] := by
  intro env hcs t hF
  obtain ⟨hK, hok, hd0, hev, heq⟩ := hobl env hcs t hF
  set gf : 𝕜 → 𝕜 := fun v => eval I (Function.update env "x" v) g with hgf
  have hs : HasStrictDerivAt gf (eval I (Function.update env "x" t) (d "x" g)) t :=
    hasStrictDerivAt_eval C "x" env t g hok
  have hsub : ∀ v, substAt I env [("I1", g)] "x" "I1" v = gf v := by
    intro v; simp [substAt, hgf]
  -- `K` does not see the bound variable nor the hole.
  have hKρ : ∀ ρ : String → 𝕜, (∀ n, n ≠ "x" → n ≠ "I1" → ρ n = env n) →
      eval I ρ K = eval I env K ∧ (Defined I ρ K ↔ Defined I env K) := by
    intro ρ hρ
    have h' : ∀ n ∈ K.varList, ρ n = env n := fun n hn =>
      hρ n (fun h => hKx (h ▸ hn)) (fun h => hKI (h ▸ hn))
    exact ⟨Calculus.eval_congr I K h', Calculus.defined_congr I K h'⟩
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    refine ⟨hev.mono fun v hv g' hg' => ?_, ?_⟩
    · simp only [List.lookup_cons, beq_self_eq_true, Option.some.injEq] at hg'
      exact hg' ▸ hv.1
    · rw [hsub, ← hs.map_nhds_eq hd0]
      exact hev.mono fun v hv => hv.2
  · intro Φ hΦ
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    rw [hsub] at hΦ
    have hρ : ∀ v, ∀ n, n ≠ "x" → n ≠ "I1" →
        substEnv I env (([("I1", H)] : List (String × Expr)).map (·.1)) [("I1", g)] Φ "x" v n =
          env n := by
      intro v n hx hI
      simp [substEnv, Function.update, hx, hI]
    refine ⟨Filter.Eventually.of_forall fun v => ?_, ?_⟩
    · simp only [Defined, (hKρ _ (hρ v)).2, hK, true_and]
    · have hfun : (fun v => eval I (substEnv I env (([("I1", H)] : List (String × Expr)).map (·.1))
          [("I1", g)] Φ "x" v) (.app2 .mul K (.var "I1"))) =
          fun v => eval I env K * Φ "I1" (gf v) := by
        funext v
        simp only [eval, (hKρ _ (hρ v)).1]
        simp [substEnv, Function.update, hsub]
      rw [hfun, heq]
      have := (hΦ.comp t hs.hasDerivAt).const_mul (eval I env K)
      convert this using 1
      · rfl
      · simp only [hgf]
        ring

/-- **Substitution `u = g(x)` by openness.** As `antiderivSubst_chain`, but with pointwise
obligations and no condition on `g'(t)`: where `Ok` holds, definedness is open
(`eventually_defined`), so `g` defined at `t` and `H` defined at `g(t)` are defined near them. -/
theorem antiderivSubst_chain_open [CompleteSpace 𝕜] (C : Calc I) {cs : List Cond}
    (F H g K : Expr) (hKx : "x" ∉ K.varList) (hKI : "I1" ∉ K.varList)
    (hobl : ∀ env : String → 𝕜, (∀ k ∈ cs, k.Holds I env) → ∀ t : 𝕜,
      (∀ᶠ v in 𝓝 t, Defined I (Function.update env "x" v) F) →
      Defined I env K ∧ Ok C "x" (Function.update env "x" t) g ∧
      Defined I (Function.update env "x" t) g ∧
      Ok C "x" (Function.update env "x" (eval I (Function.update env "x" t) g)) H ∧
      Defined I (Function.update env "x" (eval I (Function.update env "x" t) g)) H ∧
      eval I (Function.update env "x" t) F =
        eval I env K * eval I (Function.update env "x" (eval I (Function.update env "x" t) g)) H *
          eval I (Function.update env "x" t) (d "x" g)) :
    AntiderivSubstHolds I "x" cs F (.app2 .mul K (.var "I1")) [("I1", H)] [("I1", g)] := by
  intro env hcs t hF
  obtain ⟨hK, hok, hgd, hokH, hHd, heq⟩ := hobl env hcs t hF
  set gf : 𝕜 → 𝕜 := fun v => eval I (Function.update env "x" v) g with hgf
  have hs : HasStrictDerivAt gf (eval I (Function.update env "x" t) (d "x" g)) t :=
    hasStrictDerivAt_eval C "x" env t g hok
  have hsub : ∀ v, substAt I env [("I1", g)] "x" "I1" v = gf v := by
    intro v; simp [substAt, hgf]
  have hKρ : ∀ ρ : String → 𝕜, (∀ n, n ≠ "x" → n ≠ "I1" → ρ n = env n) →
      eval I ρ K = eval I env K ∧ (Defined I ρ K ↔ Defined I env K) := by
    intro ρ hρ
    have h' : ∀ n ∈ K.varList, ρ n = env n := fun n hn =>
      hρ n (fun h => hKx (h ▸ hn)) (fun h => hKI (h ▸ hn))
    exact ⟨Calculus.eval_congr I K h', Calculus.defined_congr I K h'⟩
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    refine ⟨(eventually_defined C "x" env t g hok hgd).mono fun v hv g' hg' => ?_, ?_⟩
    · simp only [List.lookup_cons, beq_self_eq_true, Option.some.injEq] at hg'
      exact hg' ▸ hv
    · rw [hsub]
      exact eventually_defined C "x" env (gf t) H hokH hHd
  · intro Φ hΦ
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    rw [hsub] at hΦ
    have hρ : ∀ v, ∀ n, n ≠ "x" → n ≠ "I1" →
        substEnv I env (([("I1", H)] : List (String × Expr)).map (·.1)) [("I1", g)] Φ "x" v n =
          env n := by
      intro v n hx hI
      simp [substEnv, Function.update, hx, hI]
    refine ⟨Filter.Eventually.of_forall fun v => ?_, ?_⟩
    · simp only [Defined, (hKρ _ (hρ v)).2, hK, true_and]
    · have hfun : (fun v => eval I (substEnv I env (([("I1", H)] : List (String × Expr)).map (·.1))
          [("I1", g)] Φ "x" v) (.app2 .mul K (.var "I1"))) =
          fun v => eval I env K * Φ "I1" (gf v) := by
        funext v
        simp only [eval, (hKρ _ (hρ v)).1]
        simp [substEnv, Function.update, hsub]
      rw [hfun, heq]
      have := (hΦ.comp t hs.hasDerivAt).const_mul (eval I env K)
      convert this using 1
      · rfl
      · simp only [hgf]
        ring

/-! ## Explicit terms plus a residual integral -/

/-- `E` evaluated with the holes of a recursive rule read as antiderivatives, when `E` mentions
no hole. -/
theorem eval_recEnv_free {E : Expr} (hE : "I1" ∉ E.varList) (env : String → 𝕜)
    (Φ : String → 𝕜 → 𝕜) (v : 𝕜) :
    eval I (recEnv env ["I1"] Φ "x" v) E = eval I (Function.update env "x" v) E ∧
      (Defined I (recEnv env ["I1"] Φ "x" v) E ↔ Defined I (Function.update env "x" v) E) := by
  have h : ∀ n ∈ E.varList, recEnv env ["I1"] Φ "x" v n = Function.update env "x" v n := by
    intro n hn
    have hI : n ≠ "I1" := fun h => hE (h ▸ hn)
    simp [recEnv, Function.update, hI]
  exact ⟨Calculus.eval_congr I E h, Calculus.defined_congr I E h⟩

/-- **Explicit term plus `K` times a residual integral**, from pointwise obligations at `t`. -/
theorem antiderivRec_open (C : Calc I) {cs : List Cond} (F E H K : Expr)
    (hEI : "I1" ∉ E.varList) (hKx : "x" ∉ K.varList) (hKI : "I1" ∉ K.varList)
    (hobl : ∀ env : String → 𝕜, (∀ k ∈ cs, k.Holds I env) → ∀ t : 𝕜,
      (∀ᶠ v in 𝓝 t, Defined I (Function.update env "x" v) F) →
      Defined I env K ∧ Ok C "x" (Function.update env "x" t) E ∧
      Defined I (Function.update env "x" t) E ∧ Ok C "x" (Function.update env "x" t) H ∧
      Defined I (Function.update env "x" t) H ∧
      eval I (Function.update env "x" t) F =
        eval I (Function.update env "x" t) (d "x" E) +
          eval I env K * eval I (Function.update env "x" t) H) :
    AntiderivRecHolds I "x" cs F (.app2 .add E (.app2 .mul K (.var "I1"))) [("I1", H)] := by
  intro env hcs t hF
  obtain ⟨hK, hokE, hdE, hokH, hdH, heq⟩ := hobl env hcs t hF
  have hKρ : ∀ v Φ, eval I (recEnv env ["I1"] Φ "x" v) K = eval I env K ∧
      (Defined I (recEnv env ["I1"] Φ "x" v) K ↔ Defined I env K) := by
    intro v Φ
    have h' : ∀ n ∈ K.varList, recEnv env ["I1"] Φ "x" v n = env n := by
      intro n hn
      have hx : n ≠ "x" := fun h => hKx (h ▸ hn)
      have hI : n ≠ "I1" := fun h => hKI (h ▸ hn)
      simp [recEnv, Function.update, hx, hI]
    exact ⟨Calculus.eval_congr I K h', Calculus.defined_congr I K h'⟩
  refine ⟨?_, fun Φ hΦ => ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    exact eventually_defined C "x" env t H hokH hdH
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards [eventually_defined C "x" env t E hokE hdE] with v hv
      simp only [List.map_cons, List.map_nil, Defined, (eval_recEnv_free hEI env Φ v).2,
        (hKρ v Φ).2, hK, hv, true_and]
    · have hfun : (fun v => eval I (recEnv env (([("I1", H)] : List (String × Expr)).map (·.1))
          Φ "x" v) (.app2 .add E (.app2 .mul K (.var "I1")))) =
          fun v => eval I (Function.update env "x" v) E + eval I env K * Φ "I1" v := by
        funext v
        simp only [List.map_cons, List.map_nil, eval, (eval_recEnv_free hEI env Φ v).1,
          (hKρ v Φ).1]
        simp [recEnv]
      rw [hfun, heq]
      exact (hasStrictDerivAt_eval C "x" env t E hokE).hasDerivAt.add (hΦ.const_mul _)

/-- **Explicit term plus a residual integral** (coefficient one). -/
theorem antiderivRec_open1 (C : Calc I) {cs : List Cond} (F E H : Expr)
    (hEI : "I1" ∉ E.varList)
    (hobl : ∀ env : String → 𝕜, (∀ k ∈ cs, k.Holds I env) → ∀ t : 𝕜,
      (∀ᶠ v in 𝓝 t, Defined I (Function.update env "x" v) F) →
      Ok C "x" (Function.update env "x" t) E ∧
      Defined I (Function.update env "x" t) E ∧ Ok C "x" (Function.update env "x" t) H ∧
      Defined I (Function.update env "x" t) H ∧
      eval I (Function.update env "x" t) F =
        eval I (Function.update env "x" t) (d "x" E) + eval I (Function.update env "x" t) H) :
    AntiderivRecHolds I "x" cs F (.app2 .add E (.var "I1")) [("I1", H)] := by
  intro env hcs t hF
  obtain ⟨hokE, hdE, hokH, hdH, heq⟩ := hobl env hcs t hF
  refine ⟨?_, fun Φ hΦ => ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    exact eventually_defined C "x" env t H hokH hdH
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards [eventually_defined C "x" env t E hokE hdE] with v hv
      simp only [List.map_cons, List.map_nil, Defined, (eval_recEnv_free hEI env Φ v).2, hv,
        true_and]
    · have hfun : (fun v => eval I (recEnv env (([("I1", H)] : List (String × Expr)).map (·.1))
          Φ "x" v) (.app2 .add E (.var "I1"))) =
          fun v => eval I (Function.update env "x" v) E + Φ "I1" v := by
        funext v
        simp only [List.map_cons, List.map_nil, eval, (eval_recEnv_free hEI env Φ v).1]
        simp [recEnv]
      rw [hfun, heq]
      exact (hasStrictDerivAt_eval C "x" env t E hokE).hasDerivAt.add hΦ

/-- **Closed-form antiderivative** from pointwise obligations at `t`. -/
theorem antideriv_open (C : Calc I) {cs : List Cond} (F E : Expr)
    (hobl : ∀ env : String → 𝕜, (∀ k ∈ cs, k.Holds I env) → ∀ t : 𝕜,
      (∀ᶠ v in 𝓝 t, Defined I (Function.update env "x" v) F) →
      Ok C "x" (Function.update env "x" t) E ∧ Defined I (Function.update env "x" t) E ∧
      eval I (Function.update env "x" t) F = eval I (Function.update env "x" t) (d "x" E)) :
    AntiderivHoldsUnder I "x" cs F E := by
  intro env hcs t hF
  obtain ⟨hokE, hdE, heq⟩ := hobl env hcs t hF
  refine ⟨eventually_defined C "x" env t E hokE hdE, ?_⟩
  rw [heq]
  exact (hasStrictDerivAt_eval C "x" env t E hokE).hasDerivAt

/-! ## Several residual integrals -/

/-- An expression free of `x` and of the holes reads the same under `recEnv` as under `env`. -/
theorem eval_recEnv_const {K : Expr} {holes : List String} (hKx : "x" ∉ K.varList)
    (hK : ∀ h ∈ holes, h ∉ K.varList) (env : String → 𝕜) (Φ : String → 𝕜 → 𝕜) (v : 𝕜) :
    eval I (recEnv env holes Φ "x" v) K = eval I env K ∧
      (Defined I (recEnv env holes Φ "x" v) K ↔ Defined I env K) := by
  have h' : ∀ n ∈ K.varList, recEnv env holes Φ "x" v n = env n := by
    intro n hn
    have hx : n ≠ "x" := fun h => hKx (h ▸ hn)
    have hh : n ∉ holes := fun h => hK n h hn
    simp [recEnv, Function.update, hx, hh]
  exact ⟨Calculus.eval_congr I K h', Calculus.defined_congr I K h'⟩

/-- An expression free of the holes reads the same under `recEnv` as under `update env x v`. -/
theorem eval_recEnv_free' {E : Expr} {holes : List String} (hE : ∀ h ∈ holes, h ∉ E.varList)
    (env : String → 𝕜) (Φ : String → 𝕜 → 𝕜) (v : 𝕜) :
    eval I (recEnv env holes Φ "x" v) E = eval I (Function.update env "x" v) E ∧
      (Defined I (recEnv env holes Φ "x" v) E ↔ Defined I (Function.update env "x" v) E) := by
  have h' : ∀ n ∈ E.varList, recEnv env holes Φ "x" v n = Function.update env "x" v n := by
    intro n hn
    have hh : n ∉ holes := fun h => hE n h hn
    by_cases hx : n = "x"
    · subst hx; simp [recEnv]
    · simp [recEnv, Function.update, hx, hh]
  exact ⟨Calculus.eval_congr I E h', Calculus.defined_congr I E h'⟩

/-- **Explicit term plus two residual integrals** `E + K₁ I₁ + K₂ I₂`, from pointwise
obligations at `t`. -/
theorem antiderivRec_open2 (C : Calc I) {cs : List Cond} (F E H₁ H₂ K₁ K₂ : Expr)
    (hE : ∀ h ∈ ["I1", "I2"], h ∉ E.varList)
    (hK₁ : "x" ∉ K₁.varList ∧ ∀ h ∈ ["I1", "I2"], h ∉ K₁.varList)
    (hK₂ : "x" ∉ K₂.varList ∧ ∀ h ∈ ["I1", "I2"], h ∉ K₂.varList)
    (hobl : ∀ env : String → 𝕜, (∀ k ∈ cs, k.Holds I env) → ∀ t : 𝕜,
      (∀ᶠ v in 𝓝 t, Defined I (Function.update env "x" v) F) →
      Defined I env K₁ ∧ Defined I env K₂ ∧ Ok C "x" (Function.update env "x" t) E ∧
      Defined I (Function.update env "x" t) E ∧ Ok C "x" (Function.update env "x" t) H₁ ∧
      Defined I (Function.update env "x" t) H₁ ∧ Ok C "x" (Function.update env "x" t) H₂ ∧
      Defined I (Function.update env "x" t) H₂ ∧
      eval I (Function.update env "x" t) F =
        eval I (Function.update env "x" t) (d "x" E) +
          eval I env K₁ * eval I (Function.update env "x" t) H₁ +
          eval I env K₂ * eval I (Function.update env "x" t) H₂) :
    AntiderivRecHolds I "x" cs F
      (.app2 .add (.app2 .add E (.app2 .mul K₁ (.var "I1"))) (.app2 .mul K₂ (.var "I2")))
      [("I1", H₁), ("I2", H₂)] := by
  intro env hcs t hF
  obtain ⟨hk₁, hk₂, hokE, hdE, hok₁, hd₁, hok₂, hd₂, heq⟩ := hobl env hcs t hF
  refine ⟨?_, fun Φ hΦ => ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact eventually_defined C "x" env t H₁ hok₁ hd₁
    · exact eventually_defined C "x" env t H₂ hok₂ hd₂
  · have hΦ₁ : HasDerivAt (Φ "I1") (eval I (Function.update env "x" t) H₁) t := hΦ ("I1", H₁) (by simp)
    have hΦ₂ : HasDerivAt (Φ "I2") (eval I (Function.update env "x" t) H₂) t := hΦ ("I2", H₂) (by simp)
    refine ⟨?_, ?_⟩
    · filter_upwards [eventually_defined C "x" env t E hokE hdE] with v hv
      simp only [List.map_cons, List.map_nil, Defined, (eval_recEnv_free' hE env Φ v).2,
        (eval_recEnv_const hK₁.1 hK₁.2 env Φ v).2, (eval_recEnv_const hK₂.1 hK₂.2 env Φ v).2,
        hk₁, hk₂, hv, true_and]
    · have hfun : (fun v => eval I (recEnv env
          (([("I1", H₁), ("I2", H₂)] : List (String × Expr)).map (·.1)) Φ "x" v)
          (.app2 .add (.app2 .add E (.app2 .mul K₁ (.var "I1"))) (.app2 .mul K₂ (.var "I2")))) =
          fun v => eval I (Function.update env "x" v) E + eval I env K₁ * Φ "I1" v +
            eval I env K₂ * Φ "I2" v := by
        funext v
        simp only [List.map_cons, List.map_nil, eval, (eval_recEnv_free' hE env Φ v).1,
          (eval_recEnv_const hK₁.1 hK₁.2 env Φ v).1, (eval_recEnv_const hK₂.1 hK₂.2 env Φ v).1]
        simp [recEnv]
      rw [hfun, heq]
      exact ((hasStrictDerivAt_eval C "x" env t E hokE).hasDerivAt.add
        (hΦ₁.const_mul _)).add (hΦ₂.const_mul _)

/-- **Two residual integrals** `K₁ I₁ + K₂ I₂`: the integrand is pointwise
`K₁ H₁ + K₂ H₂`. -/
theorem antiderivRec_lin2 (C : Calc I) {cs : List Cond} (F H₁ H₂ K₁ K₂ : Expr)
    (hK₁ : "x" ∉ K₁.varList ∧ ∀ h ∈ ["I1", "I2"], h ∉ K₁.varList)
    (hK₂ : "x" ∉ K₂.varList ∧ ∀ h ∈ ["I1", "I2"], h ∉ K₂.varList)
    (hobl : ∀ env : String → 𝕜, (∀ k ∈ cs, k.Holds I env) → ∀ t : 𝕜,
      (∀ᶠ v in 𝓝 t, Defined I (Function.update env "x" v) F) →
      Defined I env K₁ ∧ Defined I env K₂ ∧ Ok C "x" (Function.update env "x" t) H₁ ∧
      Defined I (Function.update env "x" t) H₁ ∧ Ok C "x" (Function.update env "x" t) H₂ ∧
      Defined I (Function.update env "x" t) H₂ ∧
      eval I (Function.update env "x" t) F =
        eval I env K₁ * eval I (Function.update env "x" t) H₁ +
          eval I env K₂ * eval I (Function.update env "x" t) H₂) :
    AntiderivRecHolds I "x" cs F
      (.app2 .add (.app2 .mul K₁ (.var "I1")) (.app2 .mul K₂ (.var "I2")))
      [("I1", H₁), ("I2", H₂)] := by
  intro env hcs t hF
  obtain ⟨hk₁, hk₂, hok₁, hd₁, hok₂, hd₂, heq⟩ := hobl env hcs t hF
  refine ⟨?_, fun Φ hΦ => ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact eventually_defined C "x" env t H₁ hok₁ hd₁
    · exact eventually_defined C "x" env t H₂ hok₂ hd₂
  · have hΦ₁ : HasDerivAt (Φ "I1") (eval I (Function.update env "x" t) H₁) t := hΦ ("I1", H₁) (by simp)
    have hΦ₂ : HasDerivAt (Φ "I2") (eval I (Function.update env "x" t) H₂) t := hΦ ("I2", H₂) (by simp)
    refine ⟨Filter.Eventually.of_forall fun v => ?_, ?_⟩
    · simp only [List.map_cons, List.map_nil, Defined,
        (eval_recEnv_const hK₁.1 hK₁.2 env Φ v).2, (eval_recEnv_const hK₂.1 hK₂.2 env Φ v).2,
        hk₁, hk₂, true_and]
    · have hfun : (fun v => eval I (recEnv env
          (([("I1", H₁), ("I2", H₂)] : List (String × Expr)).map (·.1)) Φ "x" v)
          (.app2 .add (.app2 .mul K₁ (.var "I1")) (.app2 .mul K₂ (.var "I2")))) =
          fun v => eval I env K₁ * Φ "I1" v + eval I env K₂ * Φ "I2" v := by
        funext v
        simp only [List.map_cons, List.map_nil, eval,
          (eval_recEnv_const hK₁.1 hK₁.2 env Φ v).1, (eval_recEnv_const hK₂.1 hK₂.2 env Φ v).1]
        simp [recEnv]
      rw [hfun, heq]
      exact (hΦ₁.const_mul _).add (hΦ₂.const_mul _)

/-- **One residual integral times a constant** `K I₁`: the integrand is pointwise `K H`. -/
theorem antiderivRec_lin1 (C : Calc I) {cs : List Cond} (F H K : Expr)
    (hK : "x" ∉ K.varList ∧ ∀ h ∈ ["I1"], h ∉ K.varList)
    (hobl : ∀ env : String → 𝕜, (∀ k ∈ cs, k.Holds I env) → ∀ t : 𝕜,
      (∀ᶠ v in 𝓝 t, Defined I (Function.update env "x" v) F) →
      Defined I env K ∧ Ok C "x" (Function.update env "x" t) H ∧
      Defined I (Function.update env "x" t) H ∧
      eval I (Function.update env "x" t) F =
        eval I env K * eval I (Function.update env "x" t) H) :
    AntiderivRecHolds I "x" cs F (.app2 .mul K (.var "I1")) [("I1", H)] := by
  intro env hcs t hF
  obtain ⟨hk, hok, hd, heq⟩ := hobl env hcs t hF
  refine ⟨?_, fun Φ hΦ => ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    exact eventually_defined C "x" env t H hok hd
  · have hΦ₁ : HasDerivAt (Φ "I1") (eval I (Function.update env "x" t) H) t := hΦ ("I1", H) (by simp)
    refine ⟨Filter.Eventually.of_forall fun v => ?_, ?_⟩
    · simp only [List.map_cons, List.map_nil, Defined, (eval_recEnv_const hK.1 hK.2 env Φ v).2,
        hk, true_and]
    · have hfun : (fun v => eval I (recEnv env (([("I1", H)] : List (String × Expr)).map (·.1))
          Φ "x" v) (.app2 .mul K (.var "I1"))) = fun v => eval I env K * Φ "I1" v := by
        funext v
        simp only [List.map_cons, List.map_nil, eval, (eval_recEnv_const hK.1 hK.2 env Φ v).1]
        simp [recEnv]
      rw [hfun, heq]
      exact hΦ₁.const_mul _

end OSR.SymDeriv
