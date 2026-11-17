import OSR.IntegrationNum1
import OSR.IntegrationRec7

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, twenty-seventh batch

Proofs over ℝ of strengthened variants first distributed unproved
(`OSR.IntegrationNum1`, which keeps their definitions): 3.1.3 #7, the
integration by parts of `(d + e x)^q (a + b log (c xⁿ))^p` with `p < -1` and
`q > 0`.  The proof uses the real logarithm; the complex domain stays
unproved.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec75

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem toInt?_neg_one (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem zpow_succ_of (A : 𝕜) (k : ℤ) (h : A ≠ 0 ∨ 0 ≤ k) : A ^ (k + 1) = A ^ k * A := by
  rcases h with h | h
  · exact zpow_add_one₀ h k
  · lift k to ℕ using h
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
      pow_succ]

private theorem toInt?_two (I : Interp 𝕜) : I.toInt? (2 : 𝕜) = some 2 :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem toInt?_four (I : Interp 𝕜) : I.toInt? (4 : 𝕜) = some 4 :=
  (I.toInt?_eq _ _).2 (by simp)








/-- **3.1.3 #7** with `b n (p + 1) ≠ 0`, `p < -1` and `q > 0`, over ℝ: integration by parts,
the terms in `(a + b log (c xⁿ))^(p+1)` cancel and `x (n/x) = n`. -/
theorem rubi313r7Nondeg_real : rubi313r7Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi313r7Nondeg.conditions rubi313r7Nondeg.body
    rubi313r7Nondeg.result rubi313r7Nondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hW : env "b" * env "n" * (env "p" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi313r7Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hgp := hc (.gt (.int (-1)) (.var "p")) (by simp [rubi313r7Nondeg])
  have hgq := hc (.gt (.var "q") (.int 0)) (by simp [rubi313r7Nondeg])
  rcases hkq : intValue? (env "q") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi313r7Nondeg, Defined, eval, Interp.real, hkq] at h
  rcases hkp : intValue? (env "p") with _ | i
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi313r7Nondeg, Defined, eval, Interp.real, hkq, hkp] at h
  rcases hkn : intValue? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi313r7Nondeg, Defined, eval, Interp.real, hkq, hkp, hkn] at h
  have hq : env "q" = (l : ℝ) := (intValue?_eq _ _).1 hkq
  have hp : env "p" = (i : ℝ) := (intValue?_eq _ _).1 hkp
  have hn : env "n" = (j : ℝ) := (intValue?_eq _ _).1 hkn
  have hi : i < -1 := by
    simp only [Cond.Holds, Defined, eval, Interp.real, true_and] at hgp
    rw [hp] at hgp; exact_mod_cast hgp
  have hl : 0 < l := by
    simp only [Cond.Holds, Defined, eval, Interp.real, true_and] at hgq
    rw [hq] at hgq; exact_mod_cast hgq
  have e1 : intValue? (env "q" + -1 * 1) = some (l - 1) := (intValue?_eq _ _).2 (by rw [hq]; push_cast; ring)
  have e1' : intValue? (env "q" + -1) = some (l - 1) := (intValue?_eq _ _).2 (by rw [hq]; push_cast; ring)
  have e2 : intValue? (env "p" + 1) = some (i + 1) := (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi313r7Nondeg.body →
      ((j < 0 → ¬w = 0) ∧ 0 < env "c" * w ^ j) ∧ env "a" + env "b" * Real.log (env "c" * w ^ j) ≠ 0 := by
    intro w h
    simp [rubi313r7Nondeg, Defined, eval, Interp.real, hkq, hkp, hkn] at h
    first | exact ⟨h.2.1, h.2.2 (by omega)⟩ | exact ⟨⟨h.2.1.1, h.2.1.2⟩, h.2.2 (by omega)⟩ | (trace_state; sorry)
  have hW' := hW
  simp only [ne_eq, mul_eq_zero, not_or] at hW'
  refine ⟨fun i' hi' => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi313r7Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi'
    rcases hi' with rfl | rfl
    all_goals
      filter_upwards [hF] with w hw
      obtain ⟨h1, h2⟩ := hD w hw
      simp [Defined, eval, Interp.real, hkq, hkn, e1, e1', e2]
      first
        | exact ⟨fun h => absurd h (by omega), h1, fun _ => h2⟩
        | exact ⟨fun h => absurd h (by omega), h1.1, h1.2, fun _ => h2⟩
        | exact ⟨fun h => absurd h (by omega), ⟨h1, fun _ => h2⟩⟩
        | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h2⟩ := hD w hw
    simp [rubi313r7Nondeg, Defined, eval, Interp.real, recEnv, hkq, hkn, e2, hm1]
    first
      | exact ⟨⟨fun h => absurd h (by omega), h1, fun _ => h2⟩, hW'⟩
      | exact ⟨⟨⟨fun h => absurd h (by omega), h1, fun _ => h2⟩, hW'⟩, hW'⟩
      | (trace_state; sorry)
  · simp only [rubi313r7Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    obtain ⟨⟨-, hc0⟩, hL0⟩ := hD t hF.self_of_nhds
    have hΦ1' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t) ^ (l - 1) * (env "a" + env "b" * Real.log (env "c" * t ^ j)) ^ (i + 1)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkn, e1, e1', e2]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "d" + env "e" * t) ^ l * (env "a" + env "b" * Real.log (env "c" * t ^ j)) ^ (i + 1)) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkq, hkn, e2]
    have hEF : eval Interp.real (Function.update env "x" t) rubi313r7Nondeg.body =
        (env "d" + env "e" * t) ^ l * (env "a" + env "b" * Real.log (env "c" * t ^ j)) ^ i := by
      simp [rubi313r7Nondeg, eval, Interp.real, hkq, hkp, hkn]
    set u := (env "b" * env "n" * (env "p" + 1))⁻¹ with hu_def
    have hU : env "b" * env "n" * (env "p" + 1) * u = 1 := by rw [hu_def]; exact mul_inv_cancel₀ hW
    have hfun : (fun w => eval Interp.real (recEnv env (rubi313r7Nondeg.integrals.map (·.1)) Φ "x" w) rubi313r7Nondeg.result) =
        fun w => w * (env "d" + env "e" * w) ^ l * (env "a" + env "b" * Real.log (env "c" * w ^ j)) ^ (i + 1) * u +
          env "d" * env "q" * u * Φ "I1" w + -1 * (env "q" + 1) * u * Φ "I2" w := by
      funext w
      simp [rubi313r7Nondeg, eval, Interp.real, recEnv, hkq, hkn, e2, hm1, hu_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hd1 : HasDerivAt (fun w => env "a" + env "b" * Real.log (env "c" * w ^ j)) (env "b" * ((j : ℝ) / t)) t :=
      ((OSR.IntegrationRec7.hasDerivAt_log_monomial _ t j hc0).const_mul _).const_add _
    have hlin : HasDerivAt (fun w => env "d" + env "e" * w) (env "e") t := by
      have := ((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d")
      convert this using 1 <;> first | ring1 | rfl | (funext w; simp only [id])
    have hDd := HasDerivAt.comp t (hasDerivAt_zpow l _ (Or.inr hl.le)) hlin
    have hLd := (hasDerivAt_zpow (i + 1) _ (Or.inl hL0)).comp t hd1
    refine (((((hasDerivAt_id' t).mul hDd).mul hLd).mul_const u).add (hΦ1'.const_mul _) |>.add (hΦ2'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right, Pi.mul_apply, id]
    have hZ : (env "d" + env "e" * t) ^ l = (env "d" + env "e" * t) ^ (l - 1) * (env "d" + env "e" * t) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    rw [hZ, zpow_succ_of _ _ (Or.inl hL0)]
    have htX := OSR.IntegrationRec7.mul_div_of_log_monomial _ t j hc0
    generalize (env "d" + env "e" * t) ^ (l - 1) = Z
    generalize (env "a" + env "b" * Real.log (env "c" * t ^ j)) ^ i = Y
    generalize Real.log (env "c" * t ^ j) = Lg at htX ⊢
    generalize (j : ℝ) / t = X at htX ⊢
    clear_value u
    simp only [hq, hp, hn] at hU ⊢
    push_cast
    linear_combination (Z * (env "d" + env "e" * t) * Y) * hU + (Z * (env "d" + env "e" * t) * Y * ((i : ℝ) + 1) * env "b" * u) * htX

end Proofs

end OSR.IntegrationRec75
