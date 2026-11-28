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
`exp`, `ln`, the square root and powers with an exponent free of `x`.

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

end OSR.SymDeriv
