import OSR.IntegrationNum1

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, sixteenth batch

Proofs of strengthened variants first distributed unproved
(`OSR.IntegrationNum1`, which keeps their definitions): 4.1.13 #1 and #2,
where `b² = 4 a c` makes `(b + 2 c x)² / (4 c)` equal to `a + b x + c x²`, and the integrations by
parts 4.1.13 #13 to #16 and #19 to #22, from
`e (b + 2 c x) = (b e - 2 c d) + 2 c (d + e x)`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec64

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








/-- **4.1.13 #1** with `4 c ≠ 0`: when `b² = 4 a c`, `(b + 2 c x)² / (4 c) = a + b x + c x²`. -/
theorem rubi4113r1Nondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi4113r1Nondeg.conditions rubi4113r1Nondeg.body rubi4113r1Nondeg.result rubi4113r1Nondeg.integrals := by
  intro env hc t hF
  have h4c : 4 * env "c" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.int 4) (.var "c")) (.int 0)) (by simp [rubi4113r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hdisc : env "b" ^ 2 + -1 * 4 * env "a" * env "c" = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)) (by simp [rubi4113r1Nondeg])
    simp [Cond.Holds, Defined, eval, toInt?_two] at h
    linear_combination h
  have h4c' := h4c
  simp only [ne_eq, mul_eq_zero, not_or] at h4c'
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4113r1Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    exact Eventually.of_forall fun w => by
      simp [Defined, eval, toInt?_two, toInt?_neg_one]
      first | done | exact h4c' | simpa using h4c
  · exact Eventually.of_forall fun w => by simp [rubi4113r1Nondeg, Defined, eval, recEnv]
  · simp only [rubi4113r1Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (rubi4113r1Nondeg.integrals.map (·.1)) Φ "x" w) rubi4113r1Nondeg.result) = Φ "I1" := by
      funext w
      simp [rubi4113r1Nondeg, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    simp [rubi4113r1Nondeg, eval, toInt?_two, toInt?_neg_one]
    congr 1
    have hu : 4 * env "c" * (4 * env "c")⁻¹ = 1 := mul_inv_cancel₀ h4c
    rw [mul_inv] at hu
    linear_combination (4⁻¹ * (env "c")⁻¹) * hdisc + (env "a" + env "b" * t + env "c" * t ^ 2) * hu

theorem rubi4113r1Nondeg_real : rubi4113r1Nondeg.Holds .real :=
  rubi4113r1Nondeg_holds Interp.real

theorem rubi4113r1Nondeg_complex : rubi4113r1Nondeg.Holds .complex :=
  rubi4113r1Nondeg_holds Interp.complex

/-- **4.1.13 #2** with `4 c ≠ 0`: when `b² = 4 a c`, `(b + 2 c x)² / (4 c) = a + b x + c x²`. -/
theorem rubi4113r2Nondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi4113r2Nondeg.conditions rubi4113r2Nondeg.body rubi4113r2Nondeg.result rubi4113r2Nondeg.integrals := by
  intro env hc t hF
  have h4c : 4 * env "c" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.int 4) (.var "c")) (.int 0)) (by simp [rubi4113r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hdisc : env "b" ^ 2 + -1 * 4 * env "a" * env "c" = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)) (by simp [rubi4113r2Nondeg])
    simp [Cond.Holds, Defined, eval, toInt?_two] at h
    linear_combination h
  have h4c' := h4c
  simp only [ne_eq, mul_eq_zero, not_or] at h4c'
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4113r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    exact Eventually.of_forall fun w => by
      simp [Defined, eval, toInt?_two, toInt?_neg_one]
      first | done | exact h4c' | simpa using h4c
  · exact Eventually.of_forall fun w => by simp [rubi4113r2Nondeg, Defined, eval, recEnv]
  · simp only [rubi4113r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (rubi4113r2Nondeg.integrals.map (·.1)) Φ "x" w) rubi4113r2Nondeg.result) = Φ "I1" := by
      funext w
      simp [rubi4113r2Nondeg, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    simp [rubi4113r2Nondeg, eval, toInt?_two, toInt?_neg_one]
    congr 1
    have hu : 4 * env "c" * (4 * env "c")⁻¹ = 1 := mul_inv_cancel₀ h4c
    rw [mul_inv] at hu
    linear_combination (4⁻¹ * (env "c")⁻¹) * hdisc + (env "a" + env "b" * t + env "c" * t ^ 2) * hu

theorem rubi4113r2Nondeg_real : rubi4113r2Nondeg.Holds .real :=
  rubi4113r2Nondeg_holds Interp.real

theorem rubi4113r2Nondeg_complex : rubi4113r2Nondeg.Holds .complex :=
  rubi4113r2Nondeg_holds Interp.complex

/-- **4.1.13 #13**: integration by parts, from `e (b + 2 c x) = (b e - 2 c d) + 2 c (d + e x)`. -/
theorem rubi4113r13Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (hs : ∀ u : 𝕜, HasDerivAt I.sin (I.cos u) u) (hcs : ∀ u : 𝕜, HasDerivAt I.cos (-I.sin u) u) :
    AntiderivRecHolds I "x" rubi4113r13Nondeg.conditions rubi4113r13Nondeg.body rubi4113r13Nondeg.result rubi4113r13Nondeg.integrals := by
  intro env hc t hF
  have hcnd : 2 * env "c" * env "d" + -1 * env "b" * env "e" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0)) (by simp [rubi4113r13Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hW : 2 * env "c" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.int 2) (.var "c")) (.int 0)) (by simp [rubi4113r13Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hg := hc (.gt (.var "m") (.int 1)) (by simp [rubi4113r13Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4113r13Nondeg, Defined, eval, hk_m] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have hk : 1 < k := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg
    rw [h_m] at hg
    have h' : I.lt ((((1 : ℤ)) : ℚ) : 𝕜) ((k : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg
    exact_mod_cast (hlt _ _).1 h'
  have e1 : I.toInt? (env "m" + -1 * 1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have e1' : I.toInt? (env "m" + -1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have e2 : I.toInt? (env "m" + -1 * 2) = some (k - 2) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have e2' : I.toInt? (env "m" + -2) = some (k - 2) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi4113r13Nondeg.body → (k < 0 → (env "d" + env "e" * w) ≠ 0) := by
    intro w h
    simp [rubi4113r13Nondeg, Defined, eval, hk_m, toInt?_two] at h
    exact h
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4113r13Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, e1, e1', e2, e2', toInt?_two]
    first | done | exact fun h' => h (by omega) | exact fun h' => absurd h' (by omega) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      have hW' := hW
      simp only [ne_eq, mul_eq_zero, not_or] at hW'
      simp [rubi4113r13Nondeg, Defined, eval, recEnv, e1, e1', e2, e2', toInt?_two, toInt?_neg_one]
      first | done | exact hW' | exact fun h' => absurd h' (by omega) | exact ⟨fun h' => absurd h' (by omega), hW'⟩ | (trace_state; sorry)
  · simp only [rubi4113r13Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t) ^ (k - 2) * I.cos (env "a" + env "b" * t + env "c" * t ^ 2)) t := by
      convert hΦ using 1
      simp [eval, e1, e1', e2, e2', toInt?_two]
    have hEF : eval I (Function.update env "x" t) rubi4113r13Nondeg.body = (env "d" + env "e" * t) ^ k * I.sin (env "a" + env "b" * t + env "c" * t ^ 2) := by
      simp [rubi4113r13Nondeg, eval, hk_m, toInt?_two]
    set u := (2 * env "c")⁻¹ with hu_def
    have hu : 2 * env "c" * u = 1 := by rw [hu_def]; exact mul_inv_cancel₀ hW
    have hfun : (fun w => eval I (recEnv env (rubi4113r13Nondeg.integrals.map (·.1)) Φ "x" w) rubi4113r13Nondeg.result) =
        fun w => (-1 * env "e") * (env "d" + env "e" * w) ^ (k - 1) * I.cos (env "a" + env "b" * w + env "c" * w ^ 2) * u + env "e" ^ 2 * (env "m" + -1 * 1) * u * Φ "I1" w := by
      funext w
      simp [rubi4113r13Nondeg, eval, recEnv, e1, e1', e2, e2', toInt?_two, toInt?_neg_one, hu_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hlin : HasDerivAt (fun w => (env "d" + env "e" * w)) (env "e") t := by
      have := ((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d")
      convert this using 1 <;> first | ring1 | rfl | (funext w; simp only [id])
    have hQ : HasDerivAt (fun w => (env "a" + env "b" * w + env "c" * w ^ 2)) (env "b" + env "c" * (2 * t)) t := by
      have := (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add ((hasDerivAt_pow 2 t).const_mul (env "c"))
      convert this using 1 <;> first | (norm_num; ring1) | ring1 | rfl | (funext w; simp only [id]) | (funext w; ring1)
    have hSd : HasDerivAt (fun w => I.sin (env "a" + env "b" * w + env "c" * w ^ 2)) (I.cos (env "a" + env "b" * t + env "c" * t ^ 2) * (env "b" + env "c" * (2 * t))) t := HasDerivAt.comp t (hs _) hQ
    have hCd : HasDerivAt (fun w => I.cos (env "a" + env "b" * w + env "c" * w ^ 2)) (-I.sin (env "a" + env "b" * t + env "c" * t ^ 2) * (env "b" + env "c" * (2 * t))) t := HasDerivAt.comp t (hcs _) hQ
    have hz : (env "d" + env "e" * t) ≠ 0 ∨ 0 ≤ k - 1 := Or.inr (by omega)
    refine ((((HasDerivAt.comp t (hasDerivAt_zpow (k - 1) _ hz) hlin).const_mul _).mul hCd).mul_const u |>.add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def]
    rw [show k - 1 - 1 = k - 2 by ring]
    have hZ1 : (env "d" + env "e" * t) ^ (k - 1) = (env "d" + env "e" * t) ^ (k - 2) * (env "d" + env "e" * t) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega))]; congr 1; ring
    have hZ2 : (env "d" + env "e" * t) ^ k = (env "d" + env "e" * t) ^ (k - 2) * (env "d" + env "e" * t) ^ 2 := by
      rw [← zpow_natCast, ← zpow_add' (Or.inr (Or.inl (by omega)))]; congr 1; push_cast; ring
    rw [hZ1, hZ2]
    generalize (env "d" + env "e" * t) ^ (k - 2) = Z
    clear_value u
    simp only [h_m] at hu ⊢
    push_cast
    linear_combination (Z * (env "d" + env "e" * t) * I.sin (env "a" + env "b" * t + env "c" * t ^ 2)) * ((env "d" + env "e" * t) * hu - u * hcnd)

theorem rubi4113r13Nondeg_real : rubi4113r13Nondeg.Holds .real :=
  rubi4113r13Nondeg_holds Interp.real Interp.real_lt_rat Real.hasDerivAt_sin Real.hasDerivAt_cos

theorem rubi4113r13Nondeg_complex : rubi4113r13Nondeg.Holds .complex :=
  rubi4113r13Nondeg_holds Interp.complex Interp.complex_lt_rat Complex.hasDerivAt_sin Complex.hasDerivAt_cos

/-- **4.1.13 #14**: integration by parts, from `e (b + 2 c x) = (b e - 2 c d) + 2 c (d + e x)`. -/
theorem rubi4113r14Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (hs : ∀ u : 𝕜, HasDerivAt I.sin (I.cos u) u) (hcs : ∀ u : 𝕜, HasDerivAt I.cos (-I.sin u) u) :
    AntiderivRecHolds I "x" rubi4113r14Nondeg.conditions rubi4113r14Nondeg.body rubi4113r14Nondeg.result rubi4113r14Nondeg.integrals := by
  intro env hc t hF
  have hcnd : 2 * env "c" * env "d" + -1 * env "b" * env "e" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0)) (by simp [rubi4113r14Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hW : 2 * env "c" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.int 2) (.var "c")) (.int 0)) (by simp [rubi4113r14Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hg := hc (.gt (.var "m") (.int 1)) (by simp [rubi4113r14Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4113r14Nondeg, Defined, eval, hk_m] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have hk : 1 < k := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg
    rw [h_m] at hg
    have h' : I.lt ((((1 : ℤ)) : ℚ) : 𝕜) ((k : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg
    exact_mod_cast (hlt _ _).1 h'
  have e1 : I.toInt? (env "m" + -1 * 1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have e1' : I.toInt? (env "m" + -1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have e2 : I.toInt? (env "m" + -1 * 2) = some (k - 2) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have e2' : I.toInt? (env "m" + -2) = some (k - 2) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi4113r14Nondeg.body → (k < 0 → (env "d" + env "e" * w) ≠ 0) := by
    intro w h
    simp [rubi4113r14Nondeg, Defined, eval, hk_m, toInt?_two] at h
    exact h
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4113r14Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, e1, e1', e2, e2', toInt?_two]
    first | done | exact fun h' => h (by omega) | exact fun h' => absurd h' (by omega) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      have hW' := hW
      simp only [ne_eq, mul_eq_zero, not_or] at hW'
      simp [rubi4113r14Nondeg, Defined, eval, recEnv, e1, e1', e2, e2', toInt?_two, toInt?_neg_one]
      first | done | exact hW' | exact fun h' => absurd h' (by omega) | exact ⟨fun h' => absurd h' (by omega), hW'⟩ | (trace_state; sorry)
  · simp only [rubi4113r14Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t) ^ (k - 2) * I.sin (env "a" + env "b" * t + env "c" * t ^ 2)) t := by
      convert hΦ using 1
      simp [eval, e1, e1', e2, e2', toInt?_two]
    have hEF : eval I (Function.update env "x" t) rubi4113r14Nondeg.body = (env "d" + env "e" * t) ^ k * I.cos (env "a" + env "b" * t + env "c" * t ^ 2) := by
      simp [rubi4113r14Nondeg, eval, hk_m, toInt?_two]
    set u := (2 * env "c")⁻¹ with hu_def
    have hu : 2 * env "c" * u = 1 := by rw [hu_def]; exact mul_inv_cancel₀ hW
    have hfun : (fun w => eval I (recEnv env (rubi4113r14Nondeg.integrals.map (·.1)) Φ "x" w) rubi4113r14Nondeg.result) =
        fun w => env "e" * (env "d" + env "e" * w) ^ (k - 1) * I.sin (env "a" + env "b" * w + env "c" * w ^ 2) * u + -1 * env "e" ^ 2 * (env "m" + -1 * 1) * u * Φ "I1" w := by
      funext w
      simp [rubi4113r14Nondeg, eval, recEnv, e1, e1', e2, e2', toInt?_two, toInt?_neg_one, hu_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hlin : HasDerivAt (fun w => (env "d" + env "e" * w)) (env "e") t := by
      have := ((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d")
      convert this using 1 <;> first | ring1 | rfl | (funext w; simp only [id])
    have hQ : HasDerivAt (fun w => (env "a" + env "b" * w + env "c" * w ^ 2)) (env "b" + env "c" * (2 * t)) t := by
      have := (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add ((hasDerivAt_pow 2 t).const_mul (env "c"))
      convert this using 1 <;> first | (norm_num; ring1) | ring1 | rfl | (funext w; simp only [id]) | (funext w; ring1)
    have hSd : HasDerivAt (fun w => I.sin (env "a" + env "b" * w + env "c" * w ^ 2)) (I.cos (env "a" + env "b" * t + env "c" * t ^ 2) * (env "b" + env "c" * (2 * t))) t := HasDerivAt.comp t (hs _) hQ
    have hCd : HasDerivAt (fun w => I.cos (env "a" + env "b" * w + env "c" * w ^ 2)) (-I.sin (env "a" + env "b" * t + env "c" * t ^ 2) * (env "b" + env "c" * (2 * t))) t := HasDerivAt.comp t (hcs _) hQ
    have hz : (env "d" + env "e" * t) ≠ 0 ∨ 0 ≤ k - 1 := Or.inr (by omega)
    refine ((((HasDerivAt.comp t (hasDerivAt_zpow (k - 1) _ hz) hlin).const_mul _).mul hSd).mul_const u |>.add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def]
    rw [show k - 1 - 1 = k - 2 by ring]
    have hZ1 : (env "d" + env "e" * t) ^ (k - 1) = (env "d" + env "e" * t) ^ (k - 2) * (env "d" + env "e" * t) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega))]; congr 1; ring
    have hZ2 : (env "d" + env "e" * t) ^ k = (env "d" + env "e" * t) ^ (k - 2) * (env "d" + env "e" * t) ^ 2 := by
      rw [← zpow_natCast, ← zpow_add' (Or.inr (Or.inl (by omega)))]; congr 1; push_cast; ring
    rw [hZ1, hZ2]
    generalize (env "d" + env "e" * t) ^ (k - 2) = Z
    clear_value u
    simp only [h_m] at hu ⊢
    push_cast
    linear_combination (Z * (env "d" + env "e" * t) * I.cos (env "a" + env "b" * t + env "c" * t ^ 2)) * ((env "d" + env "e" * t) * hu - u * hcnd)

theorem rubi4113r14Nondeg_real : rubi4113r14Nondeg.Holds .real :=
  rubi4113r14Nondeg_holds Interp.real Interp.real_lt_rat Real.hasDerivAt_sin Real.hasDerivAt_cos

theorem rubi4113r14Nondeg_complex : rubi4113r14Nondeg.Holds .complex :=
  rubi4113r14Nondeg_holds Interp.complex Interp.complex_lt_rat Complex.hasDerivAt_sin Complex.hasDerivAt_cos

/-- **4.1.13 #19**: integration by parts, from `e (b + 2 c x) = (b e - 2 c d) + 2 c (d + e x)`. -/
theorem rubi4113r19Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (hs : ∀ u : 𝕜, HasDerivAt I.sin (I.cos u) u) (hcs : ∀ u : 𝕜, HasDerivAt I.cos (-I.sin u) u) :
    AntiderivRecHolds I "x" rubi4113r19Nondeg.conditions rubi4113r19Nondeg.body rubi4113r19Nondeg.result rubi4113r19Nondeg.integrals := by
  intro env hc t hF
  have hW : 2 * env "c" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.int 2) (.var "c")) (.int 0)) (by simp [rubi4113r19Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hg := hc (.gt (.var "m") (.int 1)) (by simp [rubi4113r19Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4113r19Nondeg, Defined, eval, hk_m] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have hk : 1 < k := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg
    rw [h_m] at hg
    have h' : I.lt ((((1 : ℤ)) : ℚ) : 𝕜) ((k : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg
    exact_mod_cast (hlt _ _).1 h'
  have e1 : I.toInt? (env "m" + -1 * 1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have e1' : I.toInt? (env "m" + -1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have e2 : I.toInt? (env "m" + -1 * 2) = some (k - 2) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have e2' : I.toInt? (env "m" + -2) = some (k - 2) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi4113r19Nondeg.body → (k < 0 → (env "d" + env "e" * w) ≠ 0) := by
    intro w h
    simp [rubi4113r19Nondeg, Defined, eval, hk_m, toInt?_two] at h
    exact h
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4113r19Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, e1, e1', e2, e2', toInt?_two]
      first | done | exact fun h' => h (by omega) | exact fun h' => absurd h' (by omega) | (trace_state; sorry)
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, e1, e1', e2, e2', toInt?_two]
      first | done | exact fun h' => h (by omega) | exact fun h' => absurd h' (by omega) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      have hW' := hW
      simp only [ne_eq, mul_eq_zero, not_or] at hW'
      simp [rubi4113r19Nondeg, Defined, eval, recEnv, e1, e1', e2, e2', toInt?_two, toInt?_neg_one]
      first | done | exact hW' | exact fun h' => absurd h' (by omega) | exact ⟨fun h' => absurd h' (by omega), hW'⟩ | (trace_state; sorry)
  · simp only [rubi4113r19Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t) ^ (k - 1) * I.sin (env "a" + env "b" * t + env "c" * t ^ 2)) t := by
      convert hΦ1 using 1
      simp [eval, e1, e1', e2, e2', toInt?_two]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "d" + env "e" * t) ^ (k - 2) * I.cos (env "a" + env "b" * t + env "c" * t ^ 2)) t := by
      convert hΦ2 using 1
      simp [eval, e1, e1', e2, e2', toInt?_two]
    have hEF : eval I (Function.update env "x" t) rubi4113r19Nondeg.body = (env "d" + env "e" * t) ^ k * I.sin (env "a" + env "b" * t + env "c" * t ^ 2) := by
      simp [rubi4113r19Nondeg, eval, hk_m, toInt?_two]
    set u := (2 * env "c")⁻¹ with hu_def
    have hu : 2 * env "c" * u = 1 := by rw [hu_def]; exact mul_inv_cancel₀ hW
    have hfun : (fun w => eval I (recEnv env (rubi4113r19Nondeg.integrals.map (·.1)) Φ "x" w) rubi4113r19Nondeg.result) =
        fun w => (-1 * env "e") * (env "d" + env "e" * w) ^ (k - 1) * I.cos (env "a" + env "b" * w + env "c" * w ^ 2) * u + -1 * (env "b" * env "e" + -1 * 2 * env "c" * env "d") * u * Φ "I1" w + env "e" ^ 2 * (env "m" + -1 * 1) * u * Φ "I2" w := by
      funext w
      simp [rubi4113r19Nondeg, eval, recEnv, e1, e1', e2, e2', toInt?_two, toInt?_neg_one, hu_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hlin : HasDerivAt (fun w => (env "d" + env "e" * w)) (env "e") t := by
      have := ((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d")
      convert this using 1 <;> first | ring1 | rfl | (funext w; simp only [id])
    have hQ : HasDerivAt (fun w => (env "a" + env "b" * w + env "c" * w ^ 2)) (env "b" + env "c" * (2 * t)) t := by
      have := (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add ((hasDerivAt_pow 2 t).const_mul (env "c"))
      convert this using 1 <;> first | (norm_num; ring1) | ring1 | rfl | (funext w; simp only [id]) | (funext w; ring1)
    have hSd : HasDerivAt (fun w => I.sin (env "a" + env "b" * w + env "c" * w ^ 2)) (I.cos (env "a" + env "b" * t + env "c" * t ^ 2) * (env "b" + env "c" * (2 * t))) t := HasDerivAt.comp t (hs _) hQ
    have hCd : HasDerivAt (fun w => I.cos (env "a" + env "b" * w + env "c" * w ^ 2)) (-I.sin (env "a" + env "b" * t + env "c" * t ^ 2) * (env "b" + env "c" * (2 * t))) t := HasDerivAt.comp t (hcs _) hQ
    have hz : (env "d" + env "e" * t) ≠ 0 ∨ 0 ≤ k - 1 := Or.inr (by omega)
    refine ((((HasDerivAt.comp t (hasDerivAt_zpow (k - 1) _ hz) hlin).const_mul _).mul hCd).mul_const u |>.add (hΦ1'.const_mul _) |>.add (hΦ2'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def]
    rw [show k - 1 - 1 = k - 2 by ring]
    have hZ1 : (env "d" + env "e" * t) ^ (k - 1) = (env "d" + env "e" * t) ^ (k - 2) * (env "d" + env "e" * t) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega))]; congr 1; ring
    have hZ2 : (env "d" + env "e" * t) ^ k = (env "d" + env "e" * t) ^ (k - 2) * (env "d" + env "e" * t) ^ 2 := by
      rw [← zpow_natCast, ← zpow_add' (Or.inr (Or.inl (by omega)))]; congr 1; push_cast; ring
    rw [hZ1, hZ2]
    generalize (env "d" + env "e" * t) ^ (k - 2) = Z
    clear_value u
    simp only [h_m] at hu ⊢
    push_cast
    linear_combination (Z * (env "d" + env "e" * t) * I.sin (env "a" + env "b" * t + env "c" * t ^ 2) * (env "d" + env "e" * t)) * hu

theorem rubi4113r19Nondeg_real : rubi4113r19Nondeg.Holds .real :=
  rubi4113r19Nondeg_holds Interp.real Interp.real_lt_rat Real.hasDerivAt_sin Real.hasDerivAt_cos

theorem rubi4113r19Nondeg_complex : rubi4113r19Nondeg.Holds .complex :=
  rubi4113r19Nondeg_holds Interp.complex Interp.complex_lt_rat Complex.hasDerivAt_sin Complex.hasDerivAt_cos

/-- **4.1.13 #20**: integration by parts, from `e (b + 2 c x) = (b e - 2 c d) + 2 c (d + e x)`. -/
theorem rubi4113r20Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (hs : ∀ u : 𝕜, HasDerivAt I.sin (I.cos u) u) (hcs : ∀ u : 𝕜, HasDerivAt I.cos (-I.sin u) u) :
    AntiderivRecHolds I "x" rubi4113r20Nondeg.conditions rubi4113r20Nondeg.body rubi4113r20Nondeg.result rubi4113r20Nondeg.integrals := by
  intro env hc t hF
  have hW : 2 * env "c" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.int 2) (.var "c")) (.int 0)) (by simp [rubi4113r20Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hg := hc (.gt (.var "m") (.int 1)) (by simp [rubi4113r20Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4113r20Nondeg, Defined, eval, hk_m] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have hk : 1 < k := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg
    rw [h_m] at hg
    have h' : I.lt ((((1 : ℤ)) : ℚ) : 𝕜) ((k : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg
    exact_mod_cast (hlt _ _).1 h'
  have e1 : I.toInt? (env "m" + -1 * 1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have e1' : I.toInt? (env "m" + -1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have e2 : I.toInt? (env "m" + -1 * 2) = some (k - 2) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have e2' : I.toInt? (env "m" + -2) = some (k - 2) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi4113r20Nondeg.body → (k < 0 → (env "d" + env "e" * w) ≠ 0) := by
    intro w h
    simp [rubi4113r20Nondeg, Defined, eval, hk_m, toInt?_two] at h
    exact h
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4113r20Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, e1, e1', e2, e2', toInt?_two]
      first | done | exact fun h' => h (by omega) | exact fun h' => absurd h' (by omega) | (trace_state; sorry)
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, e1, e1', e2, e2', toInt?_two]
      first | done | exact fun h' => h (by omega) | exact fun h' => absurd h' (by omega) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      have hW' := hW
      simp only [ne_eq, mul_eq_zero, not_or] at hW'
      simp [rubi4113r20Nondeg, Defined, eval, recEnv, e1, e1', e2, e2', toInt?_two, toInt?_neg_one]
      first | done | exact hW' | exact fun h' => absurd h' (by omega) | exact ⟨fun h' => absurd h' (by omega), hW'⟩ | (trace_state; sorry)
  · simp only [rubi4113r20Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t) ^ (k - 1) * I.cos (env "a" + env "b" * t + env "c" * t ^ 2)) t := by
      convert hΦ1 using 1
      simp [eval, e1, e1', e2, e2', toInt?_two]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "d" + env "e" * t) ^ (k - 2) * I.sin (env "a" + env "b" * t + env "c" * t ^ 2)) t := by
      convert hΦ2 using 1
      simp [eval, e1, e1', e2, e2', toInt?_two]
    have hEF : eval I (Function.update env "x" t) rubi4113r20Nondeg.body = (env "d" + env "e" * t) ^ k * I.cos (env "a" + env "b" * t + env "c" * t ^ 2) := by
      simp [rubi4113r20Nondeg, eval, hk_m, toInt?_two]
    set u := (2 * env "c")⁻¹ with hu_def
    have hu : 2 * env "c" * u = 1 := by rw [hu_def]; exact mul_inv_cancel₀ hW
    have hfun : (fun w => eval I (recEnv env (rubi4113r20Nondeg.integrals.map (·.1)) Φ "x" w) rubi4113r20Nondeg.result) =
        fun w => env "e" * (env "d" + env "e" * w) ^ (k - 1) * I.sin (env "a" + env "b" * w + env "c" * w ^ 2) * u + -1 * (env "b" * env "e" + -1 * 2 * env "c" * env "d") * u * Φ "I1" w + -1 * env "e" ^ 2 * (env "m" + -1 * 1) * u * Φ "I2" w := by
      funext w
      simp [rubi4113r20Nondeg, eval, recEnv, e1, e1', e2, e2', toInt?_two, toInt?_neg_one, hu_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hlin : HasDerivAt (fun w => (env "d" + env "e" * w)) (env "e") t := by
      have := ((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d")
      convert this using 1 <;> first | ring1 | rfl | (funext w; simp only [id])
    have hQ : HasDerivAt (fun w => (env "a" + env "b" * w + env "c" * w ^ 2)) (env "b" + env "c" * (2 * t)) t := by
      have := (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add ((hasDerivAt_pow 2 t).const_mul (env "c"))
      convert this using 1 <;> first | (norm_num; ring1) | ring1 | rfl | (funext w; simp only [id]) | (funext w; ring1)
    have hSd : HasDerivAt (fun w => I.sin (env "a" + env "b" * w + env "c" * w ^ 2)) (I.cos (env "a" + env "b" * t + env "c" * t ^ 2) * (env "b" + env "c" * (2 * t))) t := HasDerivAt.comp t (hs _) hQ
    have hCd : HasDerivAt (fun w => I.cos (env "a" + env "b" * w + env "c" * w ^ 2)) (-I.sin (env "a" + env "b" * t + env "c" * t ^ 2) * (env "b" + env "c" * (2 * t))) t := HasDerivAt.comp t (hcs _) hQ
    have hz : (env "d" + env "e" * t) ≠ 0 ∨ 0 ≤ k - 1 := Or.inr (by omega)
    refine ((((HasDerivAt.comp t (hasDerivAt_zpow (k - 1) _ hz) hlin).const_mul _).mul hSd).mul_const u |>.add (hΦ1'.const_mul _) |>.add (hΦ2'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def]
    rw [show k - 1 - 1 = k - 2 by ring]
    have hZ1 : (env "d" + env "e" * t) ^ (k - 1) = (env "d" + env "e" * t) ^ (k - 2) * (env "d" + env "e" * t) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega))]; congr 1; ring
    have hZ2 : (env "d" + env "e" * t) ^ k = (env "d" + env "e" * t) ^ (k - 2) * (env "d" + env "e" * t) ^ 2 := by
      rw [← zpow_natCast, ← zpow_add' (Or.inr (Or.inl (by omega)))]; congr 1; push_cast; ring
    rw [hZ1, hZ2]
    generalize (env "d" + env "e" * t) ^ (k - 2) = Z
    clear_value u
    simp only [h_m] at hu ⊢
    push_cast
    linear_combination (Z * (env "d" + env "e" * t) * I.cos (env "a" + env "b" * t + env "c" * t ^ 2) * (env "d" + env "e" * t)) * hu

theorem rubi4113r20Nondeg_real : rubi4113r20Nondeg.Holds .real :=
  rubi4113r20Nondeg_holds Interp.real Interp.real_lt_rat Real.hasDerivAt_sin Real.hasDerivAt_cos

theorem rubi4113r20Nondeg_complex : rubi4113r20Nondeg.Holds .complex :=
  rubi4113r20Nondeg_holds Interp.complex Interp.complex_lt_rat Complex.hasDerivAt_sin Complex.hasDerivAt_cos

/-- **4.1.13 #15**: integration by parts, from `e (b + 2 c x) = (b e - 2 c d) + 2 c (d + e x)`. -/
theorem rubi4113r15Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (hs : ∀ u : 𝕜, HasDerivAt I.sin (I.cos u) u) (hcs : ∀ u : 𝕜, HasDerivAt I.cos (-I.sin u) u) :
    AntiderivRecHolds I "x" rubi4113r15Nondeg.conditions rubi4113r15Nondeg.body rubi4113r15Nondeg.result rubi4113r15Nondeg.integrals := by
  intro env hc t hF
  have hcnd : 2 * env "c" * env "d" + -1 * env "b" * env "e" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0)) (by simp [rubi4113r15Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hW1 : env "e" * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi4113r15Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW2 : env "e" ^ 2 * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi4113r15Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  have hg := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi4113r15Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4113r15Nondeg, Defined, eval, hk_m] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have hk : k < -1 := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg
    rw [h_m] at hg
    have h' : I.lt ((k : ℚ) : 𝕜) ((((-1 : ℤ)) : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg
    exact_mod_cast (hlt _ _).1 h'
  have e1 : I.toInt? (env "m" + 1) = some (k + 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have e2 : I.toInt? (env "m" + 2) = some (k + 2) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi4113r15Nondeg.body → (k < 0 → (env "d" + env "e" * w) ≠ 0) := by
    intro w h
    simp [rubi4113r15Nondeg, Defined, eval, hk_m, toInt?_two] at h
    exact h
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4113r15Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, e1, e2, toInt?_two]
    first | done | exact fun h' => h (by omega) | exact fun h' => absurd h' (by omega) | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    have h := hD w hw
    have hW1' := hW1
    have hW2' := hW2
    simp only [ne_eq, mul_eq_zero, not_or] at hW1' hW2'
    simp [rubi4113r15Nondeg, Defined, eval, recEnv, e1, e2, toInt?_two, toInt?_neg_one]
    exact ⟨fun h' => h (by omega), hW1'⟩
  · simp only [rubi4113r15Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t) ^ (k + 2) * I.cos (env "a" + env "b" * t + env "c" * t ^ 2)) t := by
      convert hΦ using 1
      simp [eval, e1, e2, toInt?_two]
    have hEF : eval I (Function.update env "x" t) rubi4113r15Nondeg.body = (env "d" + env "e" * t) ^ k * I.sin (env "a" + env "b" * t + env "c" * t ^ 2) := by
      simp [rubi4113r15Nondeg, eval, hk_m, toInt?_two]
    set u1 := (env "e" * (env "m" + 1))⁻¹ with hu1_def
    set u2 := (env "e" ^ 2 * (env "m" + 1))⁻¹ with hu2_def
    have hu1 : env "e" * (env "m" + 1) * u1 = 1 := by rw [hu1_def]; exact mul_inv_cancel₀ hW1
    have hu2 : env "e" ^ 2 * (env "m" + 1) * u2 = 1 := by rw [hu2_def]; exact mul_inv_cancel₀ hW2
    have hfun : (fun w => eval I (recEnv env (rubi4113r15Nondeg.integrals.map (·.1)) Φ "x" w) rubi4113r15Nondeg.result) =
        fun w => (env "d" + env "e" * w) ^ (k + 1) * I.sin (env "a" + env "b" * w + env "c" * w ^ 2) * u1 + (-1 * 2 * env "c") * u2 * Φ "I1" w := by
      funext w
      simp [rubi4113r15Nondeg, eval, recEnv, e1, e2, toInt?_two, toInt?_neg_one, hu1_def, hu2_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hlin : HasDerivAt (fun w => (env "d" + env "e" * w)) (env "e") t := by
      have := ((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d")
      convert this using 1 <;> first | ring1 | rfl | (funext w; simp only [id])
    have hQ : HasDerivAt (fun w => (env "a" + env "b" * w + env "c" * w ^ 2)) (env "b" + env "c" * (2 * t)) t := by
      have := (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add ((hasDerivAt_pow 2 t).const_mul (env "c"))
      convert this using 1 <;> first | (norm_num; ring1) | ring1 | rfl | (funext w; simp only [id]) | (funext w; ring1)
    have hSd : HasDerivAt (fun w => I.sin (env "a" + env "b" * w + env "c" * w ^ 2)) (I.cos (env "a" + env "b" * t + env "c" * t ^ 2) * (env "b" + env "c" * (2 * t))) t := HasDerivAt.comp t (hs _) hQ
    have hCd : HasDerivAt (fun w => I.cos (env "a" + env "b" * w + env "c" * w ^ 2)) (-I.sin (env "a" + env "b" * t + env "c" * t ^ 2) * (env "b" + env "c" * (2 * t))) t := HasDerivAt.comp t (hcs _) hQ
    have hD0 : (env "d" + env "e" * t) ≠ 0 := ht (by omega)
    refine (((HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (Or.inl hD0)) hlin).mul hSd).mul_const u1 |>.add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have hZ1 : (env "d" + env "e" * t) ^ (k + 1) = (env "d" + env "e" * t) ^ k * (env "d" + env "e" * t) := zpow_succ_of _ _ (Or.inl hD0)
    have hZ2 : (env "d" + env "e" * t) ^ (k + 2) = (env "d" + env "e" * t) ^ k * (env "d" + env "e" * t) ^ 2 := by
      rw [zpow_add₀ hD0]; norm_cast
    rw [hZ1, hZ2]
    generalize (env "d" + env "e" * t) ^ k = Y
    clear_value u1 u2
    simp only [h_m] at hu1 hu2 ⊢
    push_cast
    linear_combination (Y * (I.sin (env "a" + env "b" * t + env "c" * t ^ 2) + (env "d" + env "e" * t) * I.cos (env "a" + env "b" * t + env "c" * t ^ 2) * (env "b" + 2 * env "c" * t) * env "e" * u2)) * hu1 + (-(Y * (env "d" + env "e" * t) * I.cos (env "a" + env "b" * t + env "c" * t ^ 2) * (env "b" + 2 * env "c" * t) * u1)) * hu2 + (-(Y * (env "d" + env "e" * t) * I.cos (env "a" + env "b" * t + env "c" * t ^ 2) * u2)) * hcnd

theorem rubi4113r15Nondeg_real : rubi4113r15Nondeg.Holds .real :=
  rubi4113r15Nondeg_holds Interp.real Interp.real_lt_rat Real.hasDerivAt_sin Real.hasDerivAt_cos

theorem rubi4113r15Nondeg_complex : rubi4113r15Nondeg.Holds .complex :=
  rubi4113r15Nondeg_holds Interp.complex Interp.complex_lt_rat Complex.hasDerivAt_sin Complex.hasDerivAt_cos

/-- **4.1.13 #16**: integration by parts, from `e (b + 2 c x) = (b e - 2 c d) + 2 c (d + e x)`. -/
theorem rubi4113r16Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (hs : ∀ u : 𝕜, HasDerivAt I.sin (I.cos u) u) (hcs : ∀ u : 𝕜, HasDerivAt I.cos (-I.sin u) u) :
    AntiderivRecHolds I "x" rubi4113r16Nondeg.conditions rubi4113r16Nondeg.body rubi4113r16Nondeg.result rubi4113r16Nondeg.integrals := by
  intro env hc t hF
  have hcnd : 2 * env "c" * env "d" + -1 * env "b" * env "e" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0)) (by simp [rubi4113r16Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hW1 : env "e" * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi4113r16Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW2 : env "e" ^ 2 * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi4113r16Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  have hg := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi4113r16Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4113r16Nondeg, Defined, eval, hk_m] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have hk : k < -1 := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg
    rw [h_m] at hg
    have h' : I.lt ((k : ℚ) : 𝕜) ((((-1 : ℤ)) : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg
    exact_mod_cast (hlt _ _).1 h'
  have e1 : I.toInt? (env "m" + 1) = some (k + 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have e2 : I.toInt? (env "m" + 2) = some (k + 2) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi4113r16Nondeg.body → (k < 0 → (env "d" + env "e" * w) ≠ 0) := by
    intro w h
    simp [rubi4113r16Nondeg, Defined, eval, hk_m, toInt?_two] at h
    exact h
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4113r16Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, e1, e2, toInt?_two]
    first | done | exact fun h' => h (by omega) | exact fun h' => absurd h' (by omega) | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    have h := hD w hw
    have hW1' := hW1
    have hW2' := hW2
    simp only [ne_eq, mul_eq_zero, not_or] at hW1' hW2'
    simp [rubi4113r16Nondeg, Defined, eval, recEnv, e1, e2, toInt?_two, toInt?_neg_one]
    exact ⟨fun h' => h (by omega), hW1'⟩
  · simp only [rubi4113r16Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t) ^ (k + 2) * I.sin (env "a" + env "b" * t + env "c" * t ^ 2)) t := by
      convert hΦ using 1
      simp [eval, e1, e2, toInt?_two]
    have hEF : eval I (Function.update env "x" t) rubi4113r16Nondeg.body = (env "d" + env "e" * t) ^ k * I.cos (env "a" + env "b" * t + env "c" * t ^ 2) := by
      simp [rubi4113r16Nondeg, eval, hk_m, toInt?_two]
    set u1 := (env "e" * (env "m" + 1))⁻¹ with hu1_def
    set u2 := (env "e" ^ 2 * (env "m" + 1))⁻¹ with hu2_def
    have hu1 : env "e" * (env "m" + 1) * u1 = 1 := by rw [hu1_def]; exact mul_inv_cancel₀ hW1
    have hu2 : env "e" ^ 2 * (env "m" + 1) * u2 = 1 := by rw [hu2_def]; exact mul_inv_cancel₀ hW2
    have hfun : (fun w => eval I (recEnv env (rubi4113r16Nondeg.integrals.map (·.1)) Φ "x" w) rubi4113r16Nondeg.result) =
        fun w => (env "d" + env "e" * w) ^ (k + 1) * I.cos (env "a" + env "b" * w + env "c" * w ^ 2) * u1 + (2 * env "c") * u2 * Φ "I1" w := by
      funext w
      simp [rubi4113r16Nondeg, eval, recEnv, e1, e2, toInt?_two, toInt?_neg_one, hu1_def, hu2_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hlin : HasDerivAt (fun w => (env "d" + env "e" * w)) (env "e") t := by
      have := ((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d")
      convert this using 1 <;> first | ring1 | rfl | (funext w; simp only [id])
    have hQ : HasDerivAt (fun w => (env "a" + env "b" * w + env "c" * w ^ 2)) (env "b" + env "c" * (2 * t)) t := by
      have := (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add ((hasDerivAt_pow 2 t).const_mul (env "c"))
      convert this using 1 <;> first | (norm_num; ring1) | ring1 | rfl | (funext w; simp only [id]) | (funext w; ring1)
    have hSd : HasDerivAt (fun w => I.sin (env "a" + env "b" * w + env "c" * w ^ 2)) (I.cos (env "a" + env "b" * t + env "c" * t ^ 2) * (env "b" + env "c" * (2 * t))) t := HasDerivAt.comp t (hs _) hQ
    have hCd : HasDerivAt (fun w => I.cos (env "a" + env "b" * w + env "c" * w ^ 2)) (-I.sin (env "a" + env "b" * t + env "c" * t ^ 2) * (env "b" + env "c" * (2 * t))) t := HasDerivAt.comp t (hcs _) hQ
    have hD0 : (env "d" + env "e" * t) ≠ 0 := ht (by omega)
    refine (((HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (Or.inl hD0)) hlin).mul hCd).mul_const u1 |>.add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have hZ1 : (env "d" + env "e" * t) ^ (k + 1) = (env "d" + env "e" * t) ^ k * (env "d" + env "e" * t) := zpow_succ_of _ _ (Or.inl hD0)
    have hZ2 : (env "d" + env "e" * t) ^ (k + 2) = (env "d" + env "e" * t) ^ k * (env "d" + env "e" * t) ^ 2 := by
      rw [zpow_add₀ hD0]; norm_cast
    rw [hZ1, hZ2]
    generalize (env "d" + env "e" * t) ^ k = Y
    clear_value u1 u2
    simp only [h_m] at hu1 hu2 ⊢
    push_cast
    linear_combination (Y * (I.cos (env "a" + env "b" * t + env "c" * t ^ 2) - (env "d" + env "e" * t) * I.sin (env "a" + env "b" * t + env "c" * t ^ 2) * (env "b" + 2 * env "c" * t) * env "e" * u2)) * hu1 + (Y * (env "d" + env "e" * t) * I.sin (env "a" + env "b" * t + env "c" * t ^ 2) * (env "b" + 2 * env "c" * t) * u1) * hu2 + (Y * (env "d" + env "e" * t) * I.sin (env "a" + env "b" * t + env "c" * t ^ 2) * u2) * hcnd

theorem rubi4113r16Nondeg_real : rubi4113r16Nondeg.Holds .real :=
  rubi4113r16Nondeg_holds Interp.real Interp.real_lt_rat Real.hasDerivAt_sin Real.hasDerivAt_cos

theorem rubi4113r16Nondeg_complex : rubi4113r16Nondeg.Holds .complex :=
  rubi4113r16Nondeg_holds Interp.complex Interp.complex_lt_rat Complex.hasDerivAt_sin Complex.hasDerivAt_cos

/-- **4.1.13 #21**: integration by parts, from `e (b + 2 c x) = (b e - 2 c d) + 2 c (d + e x)`. -/
theorem rubi4113r21Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (hs : ∀ u : 𝕜, HasDerivAt I.sin (I.cos u) u) (hcs : ∀ u : 𝕜, HasDerivAt I.cos (-I.sin u) u) :
    AntiderivRecHolds I "x" rubi4113r21Nondeg.conditions rubi4113r21Nondeg.body rubi4113r21Nondeg.result rubi4113r21Nondeg.integrals := by
  intro env hc t hF
  have hW1 : env "e" * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi4113r21Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW2 : env "e" ^ 2 * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi4113r21Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  have hg := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi4113r21Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4113r21Nondeg, Defined, eval, hk_m] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have hk : k < -1 := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg
    rw [h_m] at hg
    have h' : I.lt ((k : ℚ) : 𝕜) ((((-1 : ℤ)) : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg
    exact_mod_cast (hlt _ _).1 h'
  have e1 : I.toInt? (env "m" + 1) = some (k + 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have e2 : I.toInt? (env "m" + 2) = some (k + 2) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi4113r21Nondeg.body → (k < 0 → (env "d" + env "e" * w) ≠ 0) := by
    intro w h
    simp [rubi4113r21Nondeg, Defined, eval, hk_m, toInt?_two] at h
    exact h
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4113r21Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, e1, e2, toInt?_two]
      first | done | exact fun h' => h (by omega) | exact fun h' => absurd h' (by omega) | (trace_state; sorry)
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, e1, e2, toInt?_two]
      first | done | exact fun h' => h (by omega) | exact fun h' => absurd h' (by omega) | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    have h := hD w hw
    have hW1' := hW1
    have hW2' := hW2
    simp only [ne_eq, mul_eq_zero, not_or] at hW1' hW2'
    simp [rubi4113r21Nondeg, Defined, eval, recEnv, e1, e2, toInt?_two, toInt?_neg_one]
    exact ⟨fun h' => h (by omega), hW1'⟩
  · simp only [rubi4113r21Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t) ^ (k + 1) * I.cos (env "a" + env "b" * t + env "c" * t ^ 2)) t := by
      convert hΦ1 using 1
      simp [eval, e1, e2, toInt?_two]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "d" + env "e" * t) ^ (k + 2) * I.cos (env "a" + env "b" * t + env "c" * t ^ 2)) t := by
      convert hΦ2 using 1
      simp [eval, e1, e2, toInt?_two]
    have hEF : eval I (Function.update env "x" t) rubi4113r21Nondeg.body = (env "d" + env "e" * t) ^ k * I.sin (env "a" + env "b" * t + env "c" * t ^ 2) := by
      simp [rubi4113r21Nondeg, eval, hk_m, toInt?_two]
    set u1 := (env "e" * (env "m" + 1))⁻¹ with hu1_def
    set u2 := (env "e" ^ 2 * (env "m" + 1))⁻¹ with hu2_def
    have hu1 : env "e" * (env "m" + 1) * u1 = 1 := by rw [hu1_def]; exact mul_inv_cancel₀ hW1
    have hu2 : env "e" ^ 2 * (env "m" + 1) * u2 = 1 := by rw [hu2_def]; exact mul_inv_cancel₀ hW2
    have hfun : (fun w => eval I (recEnv env (rubi4113r21Nondeg.integrals.map (·.1)) Φ "x" w) rubi4113r21Nondeg.result) =
        fun w => (env "d" + env "e" * w) ^ (k + 1) * I.sin (env "a" + env "b" * w + env "c" * w ^ 2) * u1 + -1 * (env "b" * env "e" + -1 * 2 * env "c" * env "d") * u2 * Φ "I1" w + -1 * 2 * env "c" * u2 * Φ "I2" w := by
      funext w
      simp [rubi4113r21Nondeg, eval, recEnv, e1, e2, toInt?_two, toInt?_neg_one, hu1_def, hu2_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hlin : HasDerivAt (fun w => (env "d" + env "e" * w)) (env "e") t := by
      have := ((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d")
      convert this using 1 <;> first | ring1 | rfl | (funext w; simp only [id])
    have hQ : HasDerivAt (fun w => (env "a" + env "b" * w + env "c" * w ^ 2)) (env "b" + env "c" * (2 * t)) t := by
      have := (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add ((hasDerivAt_pow 2 t).const_mul (env "c"))
      convert this using 1 <;> first | (norm_num; ring1) | ring1 | rfl | (funext w; simp only [id]) | (funext w; ring1)
    have hSd : HasDerivAt (fun w => I.sin (env "a" + env "b" * w + env "c" * w ^ 2)) (I.cos (env "a" + env "b" * t + env "c" * t ^ 2) * (env "b" + env "c" * (2 * t))) t := HasDerivAt.comp t (hs _) hQ
    have hCd : HasDerivAt (fun w => I.cos (env "a" + env "b" * w + env "c" * w ^ 2)) (-I.sin (env "a" + env "b" * t + env "c" * t ^ 2) * (env "b" + env "c" * (2 * t))) t := HasDerivAt.comp t (hcs _) hQ
    have hD0 : (env "d" + env "e" * t) ≠ 0 := ht (by omega)
    refine (((HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (Or.inl hD0)) hlin).mul hSd).mul_const u1 |>.add (hΦ1'.const_mul _) |>.add (hΦ2'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have hZ1 : (env "d" + env "e" * t) ^ (k + 1) = (env "d" + env "e" * t) ^ k * (env "d" + env "e" * t) := zpow_succ_of _ _ (Or.inl hD0)
    have hZ2 : (env "d" + env "e" * t) ^ (k + 2) = (env "d" + env "e" * t) ^ k * (env "d" + env "e" * t) ^ 2 := by
      rw [zpow_add₀ hD0]; norm_cast
    rw [hZ1, hZ2]
    generalize (env "d" + env "e" * t) ^ k = Y
    clear_value u1 u2
    simp only [h_m] at hu1 hu2 ⊢
    push_cast
    linear_combination (Y * (I.sin (env "a" + env "b" * t + env "c" * t ^ 2) + (env "d" + env "e" * t) * I.cos (env "a" + env "b" * t + env "c" * t ^ 2) * (env "b" + 2 * env "c" * t) * env "e" * u2)) * hu1 + (-(Y * (env "d" + env "e" * t) * I.cos (env "a" + env "b" * t + env "c" * t ^ 2) * (env "b" + 2 * env "c" * t) * u1)) * hu2

theorem rubi4113r21Nondeg_real : rubi4113r21Nondeg.Holds .real :=
  rubi4113r21Nondeg_holds Interp.real Interp.real_lt_rat Real.hasDerivAt_sin Real.hasDerivAt_cos

theorem rubi4113r21Nondeg_complex : rubi4113r21Nondeg.Holds .complex :=
  rubi4113r21Nondeg_holds Interp.complex Interp.complex_lt_rat Complex.hasDerivAt_sin Complex.hasDerivAt_cos

/-- **4.1.13 #22**: integration by parts, from `e (b + 2 c x) = (b e - 2 c d) + 2 c (d + e x)`. -/
theorem rubi4113r22Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (hs : ∀ u : 𝕜, HasDerivAt I.sin (I.cos u) u) (hcs : ∀ u : 𝕜, HasDerivAt I.cos (-I.sin u) u) :
    AntiderivRecHolds I "x" rubi4113r22Nondeg.conditions rubi4113r22Nondeg.body rubi4113r22Nondeg.result rubi4113r22Nondeg.integrals := by
  intro env hc t hF
  have hW1 : env "e" * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi4113r22Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW2 : env "e" ^ 2 * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi4113r22Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  have hg := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi4113r22Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4113r22Nondeg, Defined, eval, hk_m] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have hk : k < -1 := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg
    rw [h_m] at hg
    have h' : I.lt ((k : ℚ) : 𝕜) ((((-1 : ℤ)) : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg
    exact_mod_cast (hlt _ _).1 h'
  have e1 : I.toInt? (env "m" + 1) = some (k + 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have e2 : I.toInt? (env "m" + 2) = some (k + 2) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi4113r22Nondeg.body → (k < 0 → (env "d" + env "e" * w) ≠ 0) := by
    intro w h
    simp [rubi4113r22Nondeg, Defined, eval, hk_m, toInt?_two] at h
    exact h
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4113r22Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, e1, e2, toInt?_two]
      first | done | exact fun h' => h (by omega) | exact fun h' => absurd h' (by omega) | (trace_state; sorry)
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, e1, e2, toInt?_two]
      first | done | exact fun h' => h (by omega) | exact fun h' => absurd h' (by omega) | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    have h := hD w hw
    have hW1' := hW1
    have hW2' := hW2
    simp only [ne_eq, mul_eq_zero, not_or] at hW1' hW2'
    simp [rubi4113r22Nondeg, Defined, eval, recEnv, e1, e2, toInt?_two, toInt?_neg_one]
    exact ⟨fun h' => h (by omega), hW1'⟩
  · simp only [rubi4113r22Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t) ^ (k + 1) * I.sin (env "a" + env "b" * t + env "c" * t ^ 2)) t := by
      convert hΦ1 using 1
      simp [eval, e1, e2, toInt?_two]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "d" + env "e" * t) ^ (k + 2) * I.sin (env "a" + env "b" * t + env "c" * t ^ 2)) t := by
      convert hΦ2 using 1
      simp [eval, e1, e2, toInt?_two]
    have hEF : eval I (Function.update env "x" t) rubi4113r22Nondeg.body = (env "d" + env "e" * t) ^ k * I.cos (env "a" + env "b" * t + env "c" * t ^ 2) := by
      simp [rubi4113r22Nondeg, eval, hk_m, toInt?_two]
    set u1 := (env "e" * (env "m" + 1))⁻¹ with hu1_def
    set u2 := (env "e" ^ 2 * (env "m" + 1))⁻¹ with hu2_def
    have hu1 : env "e" * (env "m" + 1) * u1 = 1 := by rw [hu1_def]; exact mul_inv_cancel₀ hW1
    have hu2 : env "e" ^ 2 * (env "m" + 1) * u2 = 1 := by rw [hu2_def]; exact mul_inv_cancel₀ hW2
    have hfun : (fun w => eval I (recEnv env (rubi4113r22Nondeg.integrals.map (·.1)) Φ "x" w) rubi4113r22Nondeg.result) =
        fun w => (env "d" + env "e" * w) ^ (k + 1) * I.cos (env "a" + env "b" * w + env "c" * w ^ 2) * u1 + (env "b" * env "e" + -1 * 2 * env "c" * env "d") * u2 * Φ "I1" w + 2 * env "c" * u2 * Φ "I2" w := by
      funext w
      simp [rubi4113r22Nondeg, eval, recEnv, e1, e2, toInt?_two, toInt?_neg_one, hu1_def, hu2_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hlin : HasDerivAt (fun w => (env "d" + env "e" * w)) (env "e") t := by
      have := ((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d")
      convert this using 1 <;> first | ring1 | rfl | (funext w; simp only [id])
    have hQ : HasDerivAt (fun w => (env "a" + env "b" * w + env "c" * w ^ 2)) (env "b" + env "c" * (2 * t)) t := by
      have := (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add ((hasDerivAt_pow 2 t).const_mul (env "c"))
      convert this using 1 <;> first | (norm_num; ring1) | ring1 | rfl | (funext w; simp only [id]) | (funext w; ring1)
    have hSd : HasDerivAt (fun w => I.sin (env "a" + env "b" * w + env "c" * w ^ 2)) (I.cos (env "a" + env "b" * t + env "c" * t ^ 2) * (env "b" + env "c" * (2 * t))) t := HasDerivAt.comp t (hs _) hQ
    have hCd : HasDerivAt (fun w => I.cos (env "a" + env "b" * w + env "c" * w ^ 2)) (-I.sin (env "a" + env "b" * t + env "c" * t ^ 2) * (env "b" + env "c" * (2 * t))) t := HasDerivAt.comp t (hcs _) hQ
    have hD0 : (env "d" + env "e" * t) ≠ 0 := ht (by omega)
    refine (((HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (Or.inl hD0)) hlin).mul hCd).mul_const u1 |>.add (hΦ1'.const_mul _) |>.add (hΦ2'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have hZ1 : (env "d" + env "e" * t) ^ (k + 1) = (env "d" + env "e" * t) ^ k * (env "d" + env "e" * t) := zpow_succ_of _ _ (Or.inl hD0)
    have hZ2 : (env "d" + env "e" * t) ^ (k + 2) = (env "d" + env "e" * t) ^ k * (env "d" + env "e" * t) ^ 2 := by
      rw [zpow_add₀ hD0]; norm_cast
    rw [hZ1, hZ2]
    generalize (env "d" + env "e" * t) ^ k = Y
    clear_value u1 u2
    simp only [h_m] at hu1 hu2 ⊢
    push_cast
    linear_combination (Y * (I.cos (env "a" + env "b" * t + env "c" * t ^ 2) - (env "d" + env "e" * t) * I.sin (env "a" + env "b" * t + env "c" * t ^ 2) * (env "b" + 2 * env "c" * t) * env "e" * u2)) * hu1 + (Y * (env "d" + env "e" * t) * I.sin (env "a" + env "b" * t + env "c" * t ^ 2) * (env "b" + 2 * env "c" * t) * u1) * hu2

theorem rubi4113r22Nondeg_real : rubi4113r22Nondeg.Holds .real :=
  rubi4113r22Nondeg_holds Interp.real Interp.real_lt_rat Real.hasDerivAt_sin Real.hasDerivAt_cos

theorem rubi4113r22Nondeg_complex : rubi4113r22Nondeg.Holds .complex :=
  rubi4113r22Nondeg_holds Interp.complex Interp.complex_lt_rat Complex.hasDerivAt_sin Complex.hasDerivAt_cos

end Proofs

end OSR.IntegrationRec64
