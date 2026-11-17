import OSR.IntegrationNum1

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, thirty-third batch

Proofs of strengthened variants first distributed unproved
(`OSR.IntegrationNum1`, which keeps their definitions): 2.1 #9 and #10, the
reductions of `(c + d x)^m (a + b (F^(g (e + f x)))ⁿ)^p` that split off the
constant `a`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec81

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem toInt?_neg_one (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

/-- **2.1 #9** with `a d (m + 1) ≠ 0`, `a ≠ 0` and `m > 0`. -/
theorem rubi21r9Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi21r9Nondeg.conditions rubi21r9Nondeg.body rubi21r9Nondeg.result rubi21r9Nondeg.integrals := by
  intro env hc t hF
  have hW : env "a" * env "d" * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi21r9Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have ha : env "a" ≠ 0 := by
    have h := hc (.ne (.var "a") (.int 0)) (by simp [rubi21r9Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hg := hc (.gt (.var "m") (.int 0)) (by simp [rubi21r9Nondeg])
  rcases hkm : I.toInt? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi21r9Nondeg, Defined, eval, hkm] at h
  have h_m : env "m" = (j : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hj : 0 < j := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg
    rw [h_m] at hg
    have h' : I.lt ((((0 : ℤ)) : ℚ) : 𝕜) ((j : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg
    exact_mod_cast (hlt _ _).1 h'
  have e2 : I.toInt? (env "m" + 1) = some (j + 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi21r9Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi21r9Nondeg, Defined, eval, hkm, toInt?_neg_one] at hw ⊢
    first | tauto | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [rubi21r9Nondeg, Defined, eval, recEnv, hkm, e2, toInt?_neg_one] at hw ⊢
    have hW' := hW
    simp only [ne_eq, mul_eq_zero, not_or] at hW'
    exact ⟨⟨fun h => absurd h (by omega), ⟨hW'.1.1, hW'.1.2⟩, hW'.2⟩, ha⟩
  · simp only [rubi21r9Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hU : env "a" + env "b" * eval I (Function.update env "x" t) (.pow (.pow (.var "F") (.app2 .mul (.var "g") (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n")) ≠ 0 := by
      have h := hF.self_of_nhds
      simp [rubi21r9Nondeg, Defined, eval, hkm, toInt?_neg_one] at h ⊢
      first | exact h.2 | tauto | (trace_state; sorry)
    have hEF : eval I (Function.update env "x" t) rubi21r9Nondeg.body = (env "c" + env "d" * t) ^ j * (env "a" + env "b" * eval I (Function.update env "x" t) (.pow (.pow (.var "F") (.app2 .mul (.var "g") (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n")))⁻¹ := by
      simp [rubi21r9Nondeg, eval, hkm, toInt?_neg_one]
    have hΦ' : HasDerivAt (Φ "I1") ((env "c" + env "d" * t) ^ j * eval I (Function.update env "x" t) (.pow (.pow (.var "F") (.app2 .mul (.var "g") (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n")) * (env "a" + env "b" * eval I (Function.update env "x" t) (.pow (.pow (.var "F") (.app2 .mul (.var "g") (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n")))⁻¹) t := by
      convert hΦ using 1
      simp [eval, hkm, toInt?_neg_one]
    have hfun : (fun w => eval I (recEnv env (rubi21r9Nondeg.integrals.map (·.1)) Φ "x" w) rubi21r9Nondeg.result) =
        fun w => (env "c" + env "d" * w) ^ (j + 1) * (env "a" * env "d" * (env "m" + 1))⁻¹ + -1 * env "b" * (env "a")⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi21r9Nondeg, eval, recEnv, hkm, e2, toInt?_neg_one]
      try first | ring1 | simp
    rw [hfun, hEF]
    generalize eval I (Function.update env "x" t) (.pow (.pow (.var "F") (.app2 .mul (.var "g") (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n")) = G at hU hΦ'
    have hL : HasDerivAt (fun w => env "c" + env "d" * w) (env "d") t := by
      simpa using ((hasDerivAt_id' t).const_mul (env "d")).const_add (env "c")
    have hP := (hasDerivAt_zpow (j + 1) _ (Or.inr (by omega))).comp t hL
    have hWW : env "a" * env "d" * (env "m" + 1) * (env "a" * env "d" * (env "m" + 1))⁻¹ = 1 := mul_inv_cancel₀ hW
    have hai : env "a" * (env "a")⁻¹ = 1 := mul_inv_cancel₀ ha
    have hui : (env "a" + env "b" * G) * (env "a" + env "b" * G)⁻¹ = 1 := mul_inv_cancel₀ hU
    refine ((hP.mul_const (env "a" * env "d" * (env "m" + 1))⁻¹).add (hΦ'.const_mul (-1 * env "b" * (env "a")⁻¹))).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    generalize (env "a" * env "d" * (env "m" + 1))⁻¹ = Wi at hWW ⊢
    rw [h_m] at hWW
    push_cast
    linear_combination ((env "c" + env "d" * t) ^ j * (env "a")⁻¹) * hWW + ((env "c" + env "d" * t) ^ j * (env "a" + env "b" * G)⁻¹ - (env "c" + env "d" * t) ^ j * ((j : 𝕜) + 1) * env "d" * Wi) * hai - ((env "c" + env "d" * t) ^ j * (env "a")⁻¹) * hui

/-- **2.1 #10** with `a ≠ 0`, `p < 0` and `m > 0`. -/
theorem rubi21r10Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi21r10Nondeg.conditions rubi21r10Nondeg.body rubi21r10Nondeg.result rubi21r10Nondeg.integrals := by
  intro env hc t hF
  have ha : env "a" ≠ 0 := by
    have h := hc (.ne (.var "a") (.int 0)) (by simp [rubi21r10Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hgm := hc (.gt (.var "m") (.int 0)) (by simp [rubi21r10Nondeg])
  have hgp := hc (.gt (.int 0) (.var "p")) (by simp [rubi21r10Nondeg])
  rcases hkm : I.toInt? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi21r10Nondeg, Defined, eval, hkm] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi21r10Nondeg, Defined, eval, hkm, hkp] at h
  have h_m : env "m" = (j : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have h_p : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hj : 0 < j := by
    simp only [Cond.Holds, Defined, eval, true_and] at hgm
    rw [h_m] at hgm
    have h' : I.lt ((((0 : ℤ)) : ℚ) : 𝕜) ((j : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hgm
    exact_mod_cast (hlt _ _).1 h'
  have hq : q < 0 := by
    simp only [Cond.Holds, Defined, eval, true_and] at hgp
    rw [h_p] at hgp
    have h' : I.lt ((q : ℚ) : 𝕜) ((((0 : ℤ)) : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hgp
    exact_mod_cast (hlt _ _).1 h'
  have e2 : I.toInt? (env "p" + 1) = some (q + 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi21r10Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
      simp [rubi21r10Nondeg, Defined, eval, hkm, hkp, e2] at hw ⊢ <;>
      first | exact ⟨hw.1, hw.2.1, fun _ => hw.2.2 hq⟩ | exact ⟨⟨hw.1, hw.2.1⟩, hw.2.1, hw.2.2⟩ | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [rubi21r10Nondeg, Defined, eval, recEnv, hkm, hkp, e2, toInt?_neg_one] at hw ⊢
    exact ha
  · simp only [rubi21r10Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    have hU : (env "a" + env "b" * eval I (Function.update env "x" t) (.pow (.pow (.var "F") (.app2 .mul (.var "g") (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n"))) ≠ 0 := by
      have h := hF.self_of_nhds
      simp [rubi21r10Nondeg, Defined, eval, hkm, hkp] at h ⊢
      first | exact h.2 hq | tauto | (trace_state; sorry)
    have hEF : eval I (Function.update env "x" t) rubi21r10Nondeg.body = (env "c" + env "d" * t) ^ j * (env "a" + env "b" * eval I (Function.update env "x" t) (.pow (.pow (.var "F") (.app2 .mul (.var "g") (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n"))) ^ q := by
      simp [rubi21r10Nondeg, eval, hkm, hkp]
    have hΦ1 : HasDerivAt (Φ "I1") ((env "c" + env "d" * t) ^ j * (env "a" + env "b" * eval I (Function.update env "x" t) (.pow (.pow (.var "F") (.app2 .mul (.var "g") (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n"))) ^ (q + 1)) t := by
      convert hΦ.1 using 1
      simp [eval, hkm, e2]
    have hΦ2 : HasDerivAt (Φ "I2") ((env "c" + env "d" * t) ^ j * eval I (Function.update env "x" t) (.pow (.pow (.var "F") (.app2 .mul (.var "g") (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n")) * (env "a" + env "b" * eval I (Function.update env "x" t) (.pow (.pow (.var "F") (.app2 .mul (.var "g") (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n"))) ^ q) t := by
      convert hΦ.2 using 1
      simp [eval, hkm, hkp]
    have hfun : (fun w => eval I (recEnv env (rubi21r10Nondeg.integrals.map (·.1)) Φ "x" w) rubi21r10Nondeg.result) =
        fun w => 1 * (env "a")⁻¹ * Φ "I1" w + -1 * env "b" * (env "a")⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi21r10Nondeg, eval, recEnv, toInt?_neg_one]
      try first | ring1 | simp
    rw [hfun, hEF]
    generalize eval I (Function.update env "x" t) (.pow (.pow (.var "F") (.app2 .mul (.var "g") (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n")) = G at hU hΦ1 hΦ2
    have hai : env "a" * (env "a")⁻¹ = 1 := mul_inv_cancel₀ ha
    refine ((hΦ1.const_mul (1 * (env "a")⁻¹)).add (hΦ2.const_mul (-1 * env "b" * (env "a")⁻¹))).congr_deriv ?_
    rw [zpow_add_one₀ hU]
    linear_combination ((env "c" + env "d" * t) ^ j * (env "a" + env "b" * G) ^ q) * hai

theorem rubi21r9Nondeg_real : rubi21r9Nondeg.Holds .real :=
  rubi21r9Nondeg_holds Interp.real Interp.real_lt_rat
theorem rubi21r9Nondeg_complex : rubi21r9Nondeg.Holds .complex :=
  rubi21r9Nondeg_holds Interp.complex Interp.complex_lt_rat
theorem rubi21r10Nondeg_real : rubi21r10Nondeg.Holds .real :=
  rubi21r10Nondeg_holds Interp.real Interp.real_lt_rat
theorem rubi21r10Nondeg_complex : rubi21r10Nondeg.Holds .complex :=
  rubi21r10Nondeg_holds Interp.complex Interp.complex_lt_rat

end Proofs

end OSR.IntegrationRec81
