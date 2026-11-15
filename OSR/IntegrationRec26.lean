import OSR.IntegrationRec25

/-!
# Integration (RUBI): the branch cut of the complex logarithm

Several rules with `log` were left unproved over ℂ: the principal logarithm is
defined for `z ≠ 0` but jumps by `2 π i` across the negative real axis
(`log (-1) = π i`, while `log z → -π i` as `z → -1` from below,
`Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero`).  An
antiderivative is differentiable, hence continuous; so wherever the
integrand is defined near `x = -1` but the result is `Ψ(x, log x)` with
`Ψ(-1, π i) ≠ Ψ(-1, -π i)`, the rule is refuted over ℂ (`not_continuous_clog`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec26

open OSR OSR.Calculus Filter Topology

/-- A continuous expression of `w` and `log w` that takes different values on
the two sides of the cut is discontinuous at `-1`. -/
theorem not_continuous_clog (Ψ : ℂ → ℂ → ℂ)
    (hΨ : ContinuousAt (fun p : ℂ × ℂ => Ψ p.1 p.2) (-1, -(Real.pi * Complex.I)))
    (hne : Ψ (-1) (Real.pi * Complex.I) ≠ Ψ (-1) (-(Real.pi * Complex.I))) :
    ¬ ContinuousAt (fun w => Ψ w (Complex.log w)) (-1) := by
  intro hc
  have : (𝓝[{z : ℂ | z.im < 0}] (-1 : ℂ)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 (by rw [Complex.closure_setOfPred_im_lt]; simp)
  have hlim : Tendsto Complex.log (𝓝[{z : ℂ | z.im < 0}] (-1)) (𝓝 (-(Real.pi * Complex.I))) := by
    have h := Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero (z := -1)
      (by norm_num) (by norm_num)
    simpa [sub_eq_add_neg] using h
  have hid : Tendsto (fun w : ℂ => w) (𝓝[{z : ℂ | z.im < 0}] (-1)) (𝓝 (-1)) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have h1 : Tendsto (fun w => Ψ w (Complex.log w)) (𝓝[{z : ℂ | z.im < 0}] (-1))
      (𝓝 (Ψ (-1) (-(Real.pi * Complex.I)))) := hΨ.tendsto.comp (hid.prodMk_nhds hlim)
  have h2 : Tendsto (fun w => Ψ w (Complex.log w)) (𝓝[{z : ℂ | z.im < 0}] (-1))
      (𝓝 (Ψ (-1) (Real.pi * Complex.I))) := by
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {z : ℂ | z.im < 0}))
    simpa [Complex.log_neg_one] using this
  exact hne (tendsto_nhds_unique h2 h1)

section Witness
variable {α : Type} [Field α] [CharZero α]
private theorem iv0 : intValue? (0 : α) = some 0 := by simpa using intValue?_intCast (α := α) 0
private theorem iv1 : intValue? (1 : α) = some 1 := by simpa using intValue?_intCast (α := α) 1
private theorem ivm1 : intValue? (-1 : α) = some (-1) := by
  simpa using intValue?_intCast (α := α) (-1)
end Witness

/-- A recursive rule is refuted by a point near which the integrand is defined
and a choice of antiderivatives for which the result is not continuous there. -/
theorem not_antiderivRecHolds_discont {𝕜 : Type} [NontriviallyNormedField 𝕜] {I : Interp 𝕜}
    {x : String} {cs : List Cond} {F G : Expr} {ints : List (String × Expr)}
    (env : String → 𝕜) (t : 𝕜) (hc : ∀ c ∈ cs, c.Holds I env)
    (hF : ∀ᶠ v in 𝓝 t, Defined I (Function.update env x v) F) (Φ : String → 𝕜 → 𝕜)
    (hΦ : ∀ i ∈ ints, HasDerivAt (Φ i.1) (eval I (Function.update env x t) i.2) t)
    (hnc : ¬ ContinuousAt (fun v => eval I (recEnv env (ints.map (·.1)) Φ x v) G) t) :
    ¬ AntiderivRecHolds I x cs F G ints :=
  fun h => hnc (((h env hc t hF).2 Φ hΦ).2.continuousAt)

/-- **Counterexample** over ℂ to RUBI 3.1.5 (`∫ (a + b log(c (d + e x)))/x`
split): at `a = c = d = 1` and the other metavariables `0` the integrand `1/x`
is defined near `x = -1`, and the result is `log x`. -/
theorem logLinOverX_counterexample_complex :
    ¬ OSR.IntegrationRec2.logLinOverX.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" OSR.IntegrationRec2.logLinOverX.conditions
    OSR.IntegrationRec2.logLinOverX.body OSR.IntegrationRec2.logLinOverX.result
    OSR.IntegrationRec2.logLinOverX.integrals
  obtain ⟨hΦ, hΦd⟩ : ∃ Φ : String → ℂ → ℂ, Φ = fun h w =>
      w * (((OSR.IntegrationRec2.logLinOverX.integrals.lookup h).map
        (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "c" ∨ s = "d" then (1 : ℂ)
          else 0) "x" (-1)))).getD 0) := ⟨_, rfl⟩
  refine not_antiderivRecHolds_discont (fun s => if s = "a" ∨ s = "c" ∨ s = "d" then 1 else 0)
    (-1) ?_ ?_ hΦ ?_ ?_
  · simp [OSR.IntegrationRec2.logLinOverX, Cond.Holds, Defined, eval, Interp.complex, iv1]
  · filter_upwards [eventually_ne_nhds (by norm_num : (-1 : ℂ) ≠ 0)] with v hv
    simp [OSR.IntegrationRec2.logLinOverX, Defined, eval, Interp.complex, iv1, ivm1, hv]
  · simp only [OSR.IntegrationRec2.logLinOverX, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq]
    simp [hΦd, List.lookup]
    exact hasDerivAt_mul_const _
  · have hfun : (fun v => eval Interp.complex (recEnv (fun s => if s = "a" ∨ s = "c" ∨ s = "d"
        then 1 else 0) (OSR.IntegrationRec2.logLinOverX.integrals.map (·.1)) hΦ "x" v)
        OSR.IntegrationRec2.logLinOverX.result) = fun w => Complex.log w := by
      funext w
      simp [OSR.IntegrationRec2.logLinOverX, eval, recEnv, Interp.complex, hΦd]
    rw [hfun]
    exact not_continuous_clog (fun _ l => l) (by fun_prop) (by
      intro h; have := congrArg Complex.im h; simp at this; linarith [Real.pi_pos])

/-- **Counterexample** over ℂ to RUBI 3.3 (`∫ (a + b log(c x))/(d + e x)`):
at `a = c = d = 1`, `e = -1` (so `-c d/e = 1 > 0`) the integrand `1/(1 - x)`
is defined near `x = 2`, and the result is `-log(1 - x)`, discontinuous at
`x = 2` where `1 - x = -1`. -/
theorem logOverLin_counterexample_complex :
    ¬ OSR.IntegrationRec2.logOverLin.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" OSR.IntegrationRec2.logOverLin.conditions
    OSR.IntegrationRec2.logOverLin.body OSR.IntegrationRec2.logOverLin.result
    OSR.IntegrationRec2.logOverLin.integrals
  obtain ⟨hΦ, hΦd⟩ : ∃ Φ : String → ℂ → ℂ, Φ = fun h w =>
      w * (((OSR.IntegrationRec2.logOverLin.integrals.lookup h).map
        (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "c" ∨ s = "d" then (1 : ℂ)
          else if s = "e" then -1 else 0) "x" 2))).getD 0) := ⟨_, rfl⟩
  refine not_antiderivRecHolds_discont (fun s => if s = "a" ∨ s = "c" ∨ s = "d" then 1
    else if s = "e" then -1 else 0) 2 ?_ ?_ hΦ ?_ ?_
  · simp [OSR.IntegrationRec2.logOverLin, Cond.Holds, Defined, eval, Interp.complex, iv1, ivm1]
  · have hq : ∀ᶠ v in 𝓝 (2 : ℂ), 1 + -v ≠ 0 := by
      have hc : ContinuousAt (fun v : ℂ => 1 + -v) 2 := by fun_prop
      exact hc.eventually_ne (by norm_num)
    filter_upwards [eventually_ne_nhds (by norm_num : (2 : ℂ) ≠ 0), hq] with v hv hv2
    simp [OSR.IntegrationRec2.logOverLin, Defined, eval, Interp.complex, iv1, ivm1, hv, hv2]
  · simp only [OSR.IntegrationRec2.logOverLin, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq]
    simp [hΦd, List.lookup]
    exact hasDerivAt_mul_const _
  · have hfun : (fun v => eval Interp.complex (recEnv (fun s => if s = "a" ∨ s = "c" ∨ s = "d"
        then 1 else if s = "e" then -1 else 0) (OSR.IntegrationRec2.logOverLin.integrals.map (·.1))
        hΦ "x" v) OSR.IntegrationRec2.logOverLin.result) = fun w => -Complex.log (1 + -w) := by
      funext w
      simp [OSR.IntegrationRec2.logOverLin, eval, recEnv, Interp.complex, hΦd, iv1, ivm1]
    rw [hfun]
    intro hc
    apply not_continuous_clog (fun _ l => -l) (by fun_prop) (by
      intro h; have := congrArg Complex.im h; simp at this; linarith [Real.pi_pos])
    have h2 : ContinuousAt (fun u : ℂ => -Complex.log (1 + -(1 + -u))) (-1) :=
      ContinuousAt.comp_of_eq (g := fun w : ℂ => -Complex.log (1 + -w)) hc (by fun_prop)
        (by norm_num)
    simpa using h2

end OSR.IntegrationRec26
