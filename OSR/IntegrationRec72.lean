import OSR.IntegrationNum1
import OSR.IntegrationRec7

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, twenty-fourth batch

Proofs over ℝ of strengthened variants first distributed unproved
(`OSR.IntegrationNum1`, which keeps their definitions): the variant of
`log_power_over_linear_square`, from `d/dx [x / (d (d + e x))] = 1/(d + e x)²`.
The proof uses the real logarithm; the complex domain stays unproved.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec72

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








/-- **log_power_over_linear_square** with `d ≠ 0` and `p > 0`, over ℝ:
`d/dx [x / (d (d + e x))] = 1/(d + e x)²` and `x (n/x) = n`. -/
theorem logPowOverSqNondeg_real : logPowOverSqNondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" logPowOverSqNondeg.conditions logPowOverSqNondeg.body
    logPowOverSqNondeg.result logPowOverSqNondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have hd0 : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [logPowOverSqNondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hg := hc (.gt (.var "p") (.int 0)) (by simp [logPowOverSqNondeg])
  rcases hkp : intValue? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [logPowOverSqNondeg, Defined, eval, Interp.real, hkp] at h
  rcases hkn : intValue? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [logPowOverSqNondeg, Defined, eval, Interp.real, hkp, hkn] at h
  have hp : env "p" = (q : ℝ) := (intValue?_eq _ _).1 hkp
  have hn : env "n" = (j : ℝ) := (intValue?_eq _ _).1 hkn
  have hq : 0 < q := by
    simp only [Cond.Holds, Defined, eval, Interp.real, true_and] at hg
    rw [hp] at hg; exact_mod_cast hg
  have e1 : intValue? (env "p" + -1 * 1) = some (q - 1) := (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have e1' : intValue? (env "p" + -1) = some (q - 1) := (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) logPowOverSqNondeg.body →
      ((j < 0 → ¬w = 0) ∧ 0 < env "c" * w ^ j) ∧ env "d" + env "e" * w ≠ 0 := by
    intro w h
    simp [logPowOverSqNondeg, Defined, eval, Interp.real, hkp, hkn, h2, hm1] at h
    first | exact ⟨h.1.1, h.2⟩ | exact ⟨h.1, h.2⟩ | (trace_state; sorry)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [logPowOverSqNondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2'⟩ := hD w hw
    simp [Defined, eval, Interp.real, hkn, e1, e1', hm1]
    first | exact ⟨⟨h1, fun h => absurd h (by omega)⟩, h2'⟩ | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h2'⟩ := hD w hw
    simp [logPowOverSqNondeg, Defined, eval, Interp.real, recEnv, hkp, hkn, hm1]
    first | exact ⟨⟨⟨h1, fun h => absurd h (by omega)⟩, hd0, h2'⟩, hd0⟩ | exact ⟨⟨h1, fun h => absurd h (by omega)⟩, hd0, h2'⟩
  · simp only [logPowOverSqNondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨⟨-, hc0⟩, hD0⟩ := hD t hF.self_of_nhds
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" * Real.log (env "c" * t ^ j)) ^ (q - 1) * (env "d" + env "e" * t)⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkn, e1, e1', hm1]
    have hEF : eval Interp.real (Function.update env "x" t) logPowOverSqNondeg.body =
        (env "a" + env "b" * Real.log (env "c" * t ^ j)) ^ q * ((env "d" + env "e" * t) ^ 2)⁻¹ := by
      simp [logPowOverSqNondeg, eval, Interp.real, hkp, hkn, h2, hm1]
    have hfun : (fun w => eval Interp.real (recEnv env (logPowOverSqNondeg.integrals.map (·.1)) Φ "x" w) logPowOverSqNondeg.result) =
        fun w => w * (env "a" + env "b" * Real.log (env "c" * w ^ j)) ^ q * (env "d" * (env "d" + env "e" * w))⁻¹ +
          -1 * env "b" * env "n" * env "p" * (env "d")⁻¹ * Φ "I1" w := by
      funext w
      simp [logPowOverSqNondeg, eval, Interp.real, recEnv, hkp, hkn, hm1]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hd1 : HasDerivAt (fun w => env "a" + env "b" * Real.log (env "c" * w ^ j)) (env "b" * ((j : ℝ) / t)) t :=
      ((OSR.IntegrationRec7.hasDerivAt_log_monomial _ t j hc0).const_mul _).const_add _
    have hP := (hasDerivAt_zpow q _ (Or.inr hq.le)).comp t hd1
    have hC : HasDerivAt (fun w => env "d" * (env "d" + env "e" * w)) (env "d" * env "e") t := by
      have := (((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d")).const_mul (env "d")
      convert this using 1 <;> first | ring1 | rfl | (funext w; simp only [id])
    have hCi := hC.inv (mul_ne_zero hd0 hD0)
    refine ((((hasDerivAt_id' t).mul hP).mul hCi).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, Pi.inv_apply, id]
    have hLq : (env "a" + env "b" * Real.log (env "c" * t ^ j)) ^ q =
        (env "a" + env "b" * Real.log (env "c" * t ^ j)) ^ (q - 1) * (env "a" + env "b" * Real.log (env "c" * t ^ j)) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    rw [hLq]
    have r1 : ((env "d" * (env "d" + env "e" * t)) ^ 2)⁻¹ = (env "d")⁻¹ ^ 2 * (env "d" + env "e" * t)⁻¹ ^ 2 := by
      rw [mul_pow, mul_inv, inv_pow, inv_pow]
    have r2 : (env "d" * (env "d" + env "e" * t))⁻¹ = (env "d")⁻¹ * (env "d" + env "e" * t)⁻¹ := mul_inv _ _
    have r3 : ((env "d" + env "e" * t) ^ 2)⁻¹ = (env "d" + env "e" * t)⁻¹ ^ 2 := (inv_pow _ _).symm
    rw [show -(env "d" * env "e") / (env "d" * (env "d" + env "e" * t)) ^ 2 =
        -(env "d" * env "e") * ((env "d")⁻¹ ^ 2 * (env "d" + env "e" * t)⁻¹ ^ 2) by rw [div_eq_mul_inv, r1], r2, r3]
    have htX := OSR.IntegrationRec7.mul_div_of_log_monomial _ t j hc0
    have hdd := mul_inv_cancel₀ hd0
    have hDD := mul_inv_cancel₀ hD0
    generalize (env "a" + env "b" * Real.log (env "c" * t ^ j)) ^ (q - 1) = Y
    generalize Real.log (env "c" * t ^ j) = Lg at htX ⊢
    generalize (j : ℝ) / t = X at htX ⊢
    generalize (env "d")⁻¹ = di at hdd ⊢
    generalize (env "d" + env "e" * t)⁻¹ = Di at hDD ⊢
    simp only [hp, hn]
    linear_combination ((q : ℝ) * Y * env "b" * di * Di) * htX +
      (Y * (env "a" + env "b" * Lg) * Di * (Di - t * env "e" * di * Di)) * hdd -
      (Y * (env "a" + env "b" * Lg) * Di * di) * hDD

end Proofs

end OSR.IntegrationRec72
