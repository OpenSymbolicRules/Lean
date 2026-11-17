import OSR.IntegrationNum1

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, eighteenth batch

Proofs of strengthened variants first distributed unproved
(`OSR.IntegrationNum1`, which keeps their definitions): the logarithmic
splittings 3.1.4 #9, #17 and #18 and 3.1.5 #13, #16 and #17, where
`a + b log (c xⁿ)` is an atom and the identities are rational, such as
`(d + e x)/x - e = d/x`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec66

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








/-- **3.1.4 #17** with `d ≠ 0`: `(d + e x)/x - e = d/x`.** -/
theorem rubi314r17Nondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi314r17Nondeg.conditions rubi314r17Nondeg.body rubi314r17Nondeg.result rubi314r17Nondeg.integrals := by
  intro env hc t hF
  have hd0 : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi314r17Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hk_p : I.toInt? (env "p") with _ | i
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi314r17Nondeg, Defined, eval, hk_p] at h
  have h_p : env "p" = (i : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  rcases hk_q : I.toInt? (env "q") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi314r17Nondeg, Defined, eval, hk_p, hk_q] at h
  have h_q : env "q" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_q
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi314r17Nondeg, Defined, eval, hk_p, hk_q, hk_n] at h
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have e1 : I.toInt? (env "q" + 1) = some (k + 1) := (I.toInt?_eq _ _).2 (by rw [h_q]; push_cast; ring)
  have h0 := hF.self_of_nhds
  simp [rubi314r17Nondeg, Defined, eval, hk_p, hk_q, hk_n, toInt?_neg_one] at h0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi314r17Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    all_goals
      filter_upwards [hF] with w hw
      simp [rubi314r17Nondeg, Defined, eval, hk_p, hk_q, hk_n, toInt?_neg_one] at hw
      simp [Defined, eval, hk_p, hk_q, hk_n, e1, toInt?_neg_one]
      first
        | done
        | exact hw.1
        | exact ⟨⟨fun h => hw.1.1 (by omega), hw.1.2⟩, hw.2⟩
        | exact ⟨hw.1, hw.2.1⟩
        | exact ⟨hw.1, hw.2.2⟩
        | exact ⟨⟨fun h => by
            by_cases hm : mm < 0
            · exact hw.1.1 hm
            · exact hw.2.1 (by omega), hw.1.2⟩, hw.2⟩
        | exact ⟨⟨⟨hw.1.1.1, fun h => hw.1.1.2 (by omega)⟩, hw.1.2⟩, hw.2⟩
        | exact ⟨⟨fun _ => hw.2, hw.1.1.1, hw.1.1.2⟩, hw.1.2⟩
  · exact Eventually.of_forall fun w => by simp [rubi314r17Nondeg, Defined, eval, recEnv, toInt?_neg_one, hd0]
  · simp only [rubi314r17Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((((env "d" + (env "e" * t)) ^ (k + 1) * (env "a" + (env "b" * I.ln (env "c" * t ^ j))) ^ i) * (t)⁻¹)) t := by
      convert hΦ1 using 1
      simp [eval, hk_p, hk_q, hk_n, e1, toInt?_neg_one]
    have hΦ2' : HasDerivAt (Φ "I2") (((env "d" + (env "e" * t)) ^ k * (env "a" + (env "b" * I.ln (env "c" * t ^ j))) ^ i)) t := by
      convert hΦ2 using 1
      simp [eval, hk_p, hk_q, hk_n, e1, toInt?_neg_one]
    have hEF : eval I (Function.update env "x" t) rubi314r17Nondeg.body = (((env "d" + (env "e" * t)) ^ k * (env "a" + (env "b" * I.ln (env "c" * t ^ j))) ^ i) * (t)⁻¹) := by
      simp [rubi314r17Nondeg, eval, hk_p, hk_q, hk_n, toInt?_neg_one]
    have hfun : (fun w => eval I (recEnv env (rubi314r17Nondeg.integrals.map (·.1)) Φ "x" w) rubi314r17Nondeg.result) =
        fun w => (((1 * (env "d")⁻¹) * Φ "I1" w) + ((((-1) * env "e") * (env "d")⁻¹) * Φ "I2" w)) := by
      funext w
      simp [rubi314r17Nondeg, eval, recEnv, toInt?_neg_one]
      try first | ring1 | simp
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have hD0 : (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (fun h' => by simp_all)
      · exact Or.inr (by omega)
    rw [zpow_succ_of _ _ hD0]
    have hx : t * t⁻¹ = 1 := mul_inv_cancel₀ (by simp_all)
    have hd : env "d" * (env "d")⁻¹ = 1 := mul_inv_cancel₀ hd0
    generalize (env "d" + (env "e" * t)) ^ k = Y
    generalize (env "a" + (env "b" * I.ln (env "c" * t ^ j))) ^ i = Lp
    generalize t⁻¹ = xi at hx ⊢
    generalize (env "d")⁻¹ = di at hd ⊢
    linear_combination (Y * Lp * xi) * hd + (Y * Lp * env "e" * di) * hx

theorem rubi314r17Nondeg_real : rubi314r17Nondeg.Holds .real :=
  rubi314r17Nondeg_holds Interp.real

theorem rubi314r17Nondeg_complex : rubi314r17Nondeg.Holds .complex :=
  rubi314r17Nondeg_holds Interp.complex

/-- **3.1.5 #16** with `d ≠ 0`: `(d + e x)/x - e = d/x`.** -/
theorem rubi315r16Nondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi315r16Nondeg.conditions rubi315r16Nondeg.body rubi315r16Nondeg.result rubi315r16Nondeg.integrals := by
  intro env hc t hF
  have hd0 : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi315r16Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hk_p : I.toInt? (env "p") with _ | i
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi315r16Nondeg, Defined, eval, hk_p] at h
  have h_p : env "p" = (i : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  rcases hk_q : I.toInt? (env "q") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi315r16Nondeg, Defined, eval, hk_p, hk_q] at h
  have h_q : env "q" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_q
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi315r16Nondeg, Defined, eval, hk_p, hk_q, hk_n] at h
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have e1 : I.toInt? (env "q" + 1) = some (k + 1) := (I.toInt?_eq _ _).2 (by rw [h_q]; push_cast; ring)
  have h0 := hF.self_of_nhds
  simp [rubi315r16Nondeg, Defined, eval, hk_p, hk_q, hk_n, toInt?_neg_one] at h0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi315r16Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    all_goals
      filter_upwards [hF] with w hw
      simp [rubi315r16Nondeg, Defined, eval, hk_p, hk_q, hk_n, toInt?_neg_one] at hw
      simp [Defined, eval, hk_p, hk_q, hk_n, e1, toInt?_neg_one]
      first
        | done
        | exact hw.1
        | exact ⟨⟨fun h => hw.1.1 (by omega), hw.1.2⟩, hw.2⟩
        | exact ⟨hw.1, hw.2.1⟩
        | exact ⟨hw.1, hw.2.2⟩
        | exact ⟨⟨fun h => by
            by_cases hm : mm < 0
            · exact hw.1.1 hm
            · exact hw.2.1 (by omega), hw.1.2⟩, hw.2⟩
        | exact ⟨⟨⟨hw.1.1.1, fun h => hw.1.1.2 (by omega)⟩, hw.1.2⟩, hw.2⟩
        | exact ⟨⟨fun _ => hw.2, hw.1.1.1, hw.1.1.2⟩, hw.1.2⟩
  · exact Eventually.of_forall fun w => by simp [rubi315r16Nondeg, Defined, eval, recEnv, toInt?_neg_one, hd0]
  · simp only [rubi315r16Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((((env "d" + (env "e" * t)) ^ (k + 1) * (env "a" + (env "b" * I.ln (env "c" * t ^ j))) ^ i) * (t)⁻¹)) t := by
      convert hΦ1 using 1
      simp [eval, hk_p, hk_q, hk_n, e1, toInt?_neg_one]
    have hΦ2' : HasDerivAt (Φ "I2") (((env "d" + (env "e" * t)) ^ k * (env "a" + (env "b" * I.ln (env "c" * t ^ j))) ^ i)) t := by
      convert hΦ2 using 1
      simp [eval, hk_p, hk_q, hk_n, e1, toInt?_neg_one]
    have hEF : eval I (Function.update env "x" t) rubi315r16Nondeg.body = (((env "d" + (env "e" * t)) ^ k * (env "a" + (env "b" * I.ln (env "c" * t ^ j))) ^ i) * (t)⁻¹) := by
      simp [rubi315r16Nondeg, eval, hk_p, hk_q, hk_n, toInt?_neg_one]
    have hfun : (fun w => eval I (recEnv env (rubi315r16Nondeg.integrals.map (·.1)) Φ "x" w) rubi315r16Nondeg.result) =
        fun w => (((1 * (env "d")⁻¹) * Φ "I1" w) + ((((-1) * env "e") * (env "d")⁻¹) * Φ "I2" w)) := by
      funext w
      simp [rubi315r16Nondeg, eval, recEnv, toInt?_neg_one]
      try first | ring1 | simp
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have hD0 : (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (fun h' => by simp_all)
      · exact Or.inr (by omega)
    rw [zpow_succ_of _ _ hD0]
    have hx : t * t⁻¹ = 1 := mul_inv_cancel₀ (by simp_all)
    have hd : env "d" * (env "d")⁻¹ = 1 := mul_inv_cancel₀ hd0
    generalize (env "d" + (env "e" * t)) ^ k = Y
    generalize (env "a" + (env "b" * I.ln (env "c" * t ^ j))) ^ i = Lp
    generalize t⁻¹ = xi at hx ⊢
    generalize (env "d")⁻¹ = di at hd ⊢
    linear_combination (Y * Lp * xi) * hd + (Y * Lp * env "e" * di) * hx

theorem rubi315r16Nondeg_real : rubi315r16Nondeg.Holds .real :=
  rubi315r16Nondeg_holds Interp.real

theorem rubi315r16Nondeg_complex : rubi315r16Nondeg.Holds .complex :=
  rubi315r16Nondeg_holds Interp.complex

/-- **3.1.5 #13** with `d ≠ 0`: `1/x - e/(d + e x) = d/(x (d + e x))`.** -/
theorem rubi315r13Nondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi315r13Nondeg.conditions rubi315r13Nondeg.body rubi315r13Nondeg.result rubi315r13Nondeg.integrals := by
  intro env hc t hF
  have hd0 : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi315r13Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hk_p : I.toInt? (env "p") with _ | i
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi315r13Nondeg, Defined, eval, hk_p] at h
  have h_p : env "p" = (i : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi315r13Nondeg, Defined, eval, hk_p, hk_n] at h
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have h0 := hF.self_of_nhds
  simp [rubi315r13Nondeg, Defined, eval, hk_p, hk_n, toInt?_neg_one] at h0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi315r13Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    all_goals
      filter_upwards [hF] with w hw
      simp [rubi315r13Nondeg, Defined, eval, hk_p, hk_n, toInt?_neg_one] at hw
      simp [Defined, eval, hk_p, hk_n, toInt?_neg_one]
      first
        | done
        | exact hw.1
        | exact ⟨⟨fun h => hw.1.1 (by omega), hw.1.2⟩, hw.2⟩
        | exact ⟨hw.1, hw.2.1⟩
        | exact ⟨hw.1, hw.2.2⟩
        | exact ⟨⟨fun h => by
            by_cases hm : mm < 0
            · exact hw.1.1 hm
            · exact hw.2.1 (by omega), hw.1.2⟩, hw.2⟩
        | exact ⟨⟨⟨hw.1.1.1, fun h => hw.1.1.2 (by omega)⟩, hw.1.2⟩, hw.2⟩
        | exact ⟨⟨fun _ => hw.2, hw.1.1.1, hw.1.1.2⟩, hw.1.2⟩
  · exact Eventually.of_forall fun w => by simp [rubi315r13Nondeg, Defined, eval, recEnv, toInt?_neg_one, hd0]
  · simp only [rubi315r13Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") (((env "a" + (env "b" * I.ln (env "c" * t ^ j))) ^ i * (t)⁻¹)) t := by
      convert hΦ1 using 1
      simp [eval, hk_p, hk_n, toInt?_neg_one]
    have hΦ2' : HasDerivAt (Φ "I2") (((env "a" + (env "b" * I.ln (env "c" * t ^ j))) ^ i * (env "d" + (env "e" * t))⁻¹)) t := by
      convert hΦ2 using 1
      simp [eval, hk_p, hk_n, toInt?_neg_one]
    have hEF : eval I (Function.update env "x" t) rubi315r13Nondeg.body = ((env "a" + (env "b" * I.ln (env "c" * t ^ j))) ^ i * (t * (env "d" + (env "e" * t)))⁻¹) := by
      simp [rubi315r13Nondeg, eval, hk_p, hk_n, toInt?_neg_one]
    have hfun : (fun w => eval I (recEnv env (rubi315r13Nondeg.integrals.map (·.1)) Φ "x" w) rubi315r13Nondeg.result) =
        fun w => (((1 * (env "d")⁻¹) * Φ "I1" w) + ((((-1) * env "e") * (env "d")⁻¹) * Φ "I2" w)) := by
      funext w
      simp [rubi315r13Nondeg, eval, recEnv, toInt?_neg_one]
      try first | ring1 | simp
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    rw [mul_inv]
    have hx : t * t⁻¹ = 1 := mul_inv_cancel₀ (by simp_all)
    have hD : (env "d" + (env "e" * t)) * (env "d" + (env "e" * t))⁻¹ = 1 := mul_inv_cancel₀ (by simp_all)
    have hd : env "d" * (env "d")⁻¹ = 1 := mul_inv_cancel₀ hd0
    generalize (env "a" + (env "b" * I.ln (env "c" * t ^ j))) ^ i = Lp
    generalize t⁻¹ = xi at hx ⊢
    generalize (env "d" + (env "e" * t))⁻¹ = Di at hD ⊢
    generalize (env "d")⁻¹ = di at hd ⊢
    linear_combination (Lp * xi * Di) * hd + (Lp * env "e" * di * Di) * hx - (Lp * di * xi) * hD

theorem rubi315r13Nondeg_real : rubi315r13Nondeg.Holds .real :=
  rubi315r13Nondeg_holds Interp.real

theorem rubi315r13Nondeg_complex : rubi315r13Nondeg.Holds .complex :=
  rubi315r13Nondeg_holds Interp.complex

/-- **3.1.4 #9** with `d ≠ 0`: `1 - e xʳ/(d + e xʳ) = d/(d + e xʳ)`.** -/
theorem rubi314r9Nondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi314r9Nondeg.conditions rubi314r9Nondeg.body rubi314r9Nondeg.result rubi314r9Nondeg.integrals := by
  intro env hc t hF
  have hd0 : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi314r9Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hk_p : I.toInt? (env "p") with _ | i
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi314r9Nondeg, Defined, eval, hk_p] at h
  have h_p : env "p" = (i : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  rcases hk_r : I.toInt? (env "r") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi314r9Nondeg, Defined, eval, hk_p, hk_r] at h
  have h_r : env "r" = (l : 𝕜) := (I.toInt?_eq _ _).1 hk_r
  rcases hk_m : I.toInt? (env "m") with _ | mm
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi314r9Nondeg, Defined, eval, hk_p, hk_r, hk_m] at h
  have h_m : env "m" = (mm : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi314r9Nondeg, Defined, eval, hk_p, hk_r, hk_m, hk_n] at h
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have e1 : I.toInt? (env "m" + env "r") = some (mm + l) := (I.toInt?_eq _ _).2 (by rw [h_m, h_r]; push_cast; ring)
  have h0 := hF.self_of_nhds
  simp [rubi314r9Nondeg, Defined, eval, hk_p, hk_r, hk_m, hk_n, toInt?_neg_one] at h0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi314r9Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    all_goals
      filter_upwards [hF] with w hw
      simp [rubi314r9Nondeg, Defined, eval, hk_p, hk_r, hk_m, hk_n, toInt?_neg_one] at hw
      simp [Defined, eval, hk_p, hk_r, hk_m, hk_n, e1, toInt?_neg_one]
      first
        | done
        | exact hw.1
        | exact ⟨⟨fun h => hw.1.1 (by omega), hw.1.2⟩, hw.2⟩
        | exact ⟨hw.1, hw.2.1⟩
        | exact ⟨hw.1, hw.2.2⟩
        | exact ⟨⟨fun h => by
            by_cases hm : mm < 0
            · exact hw.1.1 hm
            · exact hw.2.1 (by omega), hw.1.2⟩, hw.2⟩
        | exact ⟨⟨⟨hw.1.1.1, fun h => hw.1.1.2 (by omega)⟩, hw.1.2⟩, hw.2⟩
        | exact ⟨⟨fun _ => hw.2, hw.1.1.1, hw.1.1.2⟩, hw.1.2⟩
  · exact Eventually.of_forall fun w => by simp [rubi314r9Nondeg, Defined, eval, recEnv, toInt?_neg_one, hd0]
  · simp only [rubi314r9Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((t ^ mm * (env "a" + (env "b" * I.ln (env "c" * t ^ j))) ^ i)) t := by
      convert hΦ1 using 1
      simp [eval, hk_p, hk_r, hk_m, hk_n, e1, toInt?_neg_one]
    have hΦ2' : HasDerivAt (Φ "I2") (((t ^ (mm + l) * (env "a" + (env "b" * I.ln (env "c" * t ^ j))) ^ i) * (env "d" + (env "e" * t ^ l))⁻¹)) t := by
      convert hΦ2 using 1
      simp [eval, hk_p, hk_r, hk_m, hk_n, e1, toInt?_neg_one]
    have hEF : eval I (Function.update env "x" t) rubi314r9Nondeg.body = ((t ^ mm * (env "a" + (env "b" * I.ln (env "c" * t ^ j))) ^ i) * (env "d" + (env "e" * t ^ l))⁻¹) := by
      simp [rubi314r9Nondeg, eval, hk_p, hk_r, hk_m, hk_n, toInt?_neg_one]
    have hfun : (fun w => eval I (recEnv env (rubi314r9Nondeg.integrals.map (·.1)) Φ "x" w) rubi314r9Nondeg.result) =
        fun w => (((1 * (env "d")⁻¹) * Φ "I1" w) + ((((-1) * env "e") * (env "d")⁻¹) * Φ "I2" w)) := by
      funext w
      simp [rubi314r9Nondeg, eval, recEnv, toInt?_neg_one]
      try first | ring1 | simp
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have hz : t ≠ 0 ∨ mm + l ≠ 0 ∨ mm = 0 ∧ l = 0 := by
      by_cases ht0 : t = 0
      · right
        have hm : 0 ≤ mm := by by_contra hm; simp_all
        have hl : 0 ≤ l := by by_contra hl; simp_all
        omega
      · exact Or.inl ht0
    rw [zpow_add' hz]
    have hA : (env "d" + (env "e" * t ^ l)) * (env "d" + (env "e" * t ^ l))⁻¹ = 1 := mul_inv_cancel₀ (by simp_all)
    have hd : env "d" * (env "d")⁻¹ = 1 := mul_inv_cancel₀ hd0
    generalize (env "d" + (env "e" * t ^ l))⁻¹ = Ai at hA ⊢
    generalize t ^ mm = X
    generalize t ^ l = Xr at hA ⊢
    generalize (env "a" + (env "b" * I.ln (env "c" * t ^ j))) ^ i = Lp
    generalize (env "d")⁻¹ = di at hd ⊢
    linear_combination (-(X * Lp * di)) * hA + (X * Lp * Ai) * hd

theorem rubi314r9Nondeg_real : rubi314r9Nondeg.Holds .real :=
  rubi314r9Nondeg_holds Interp.real

theorem rubi314r9Nondeg_complex : rubi314r9Nondeg.Holds .complex :=
  rubi314r9Nondeg_holds Interp.complex

/-- **3.1.4 #18** with `d ≠ 0`: `(d + e xʳ)/x - e xʳ⁻¹ = d/x`.** -/
theorem rubi314r18Nondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi314r18Nondeg.conditions rubi314r18Nondeg.body rubi314r18Nondeg.result rubi314r18Nondeg.integrals := by
  intro env hc t hF
  have hd0 : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi314r18Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hk_p : I.toInt? (env "p") with _ | i
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi314r18Nondeg, Defined, eval, hk_p] at h
  have h_p : env "p" = (i : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  rcases hk_q : I.toInt? (env "q") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi314r18Nondeg, Defined, eval, hk_p, hk_q] at h
  have h_q : env "q" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_q
  rcases hk_r : I.toInt? (env "r") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi314r18Nondeg, Defined, eval, hk_p, hk_q, hk_r] at h
  have h_r : env "r" = (l : 𝕜) := (I.toInt?_eq _ _).1 hk_r
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi314r18Nondeg, Defined, eval, hk_p, hk_q, hk_r, hk_n] at h
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have e1 : I.toInt? (env "q" + 1) = some (k + 1) := (I.toInt?_eq _ _).2 (by rw [h_q]; push_cast; ring)
  have e2 : I.toInt? (env "r" + -1 * 1) = some (l + -1 * 1) := (I.toInt?_eq _ _).2 (by rw [h_r]; push_cast; ring)
  have e2' : I.toInt? (env "r" + -1) = some (l + -1 * 1) := (I.toInt?_eq _ _).2 (by rw [h_r]; push_cast; ring)
  have h0 := hF.self_of_nhds
  simp [rubi314r18Nondeg, Defined, eval, hk_p, hk_q, hk_r, hk_n, toInt?_neg_one] at h0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi314r18Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    all_goals
      filter_upwards [hF] with w hw
      simp [rubi314r18Nondeg, Defined, eval, hk_p, hk_q, hk_r, hk_n, toInt?_neg_one] at hw
      simp [Defined, eval, hk_p, hk_q, hk_r, hk_n, e1, e2, e2', toInt?_neg_one]
      first
        | done
        | exact hw.1
        | exact ⟨⟨fun h => hw.1.1 (by omega), hw.1.2⟩, hw.2⟩
        | exact ⟨hw.1, hw.2.1⟩
        | exact ⟨hw.1, hw.2.2⟩
        | exact ⟨⟨fun h => by
            by_cases hm : mm < 0
            · exact hw.1.1 hm
            · exact hw.2.1 (by omega), hw.1.2⟩, hw.2⟩
        | exact ⟨⟨⟨hw.1.1.1, fun h => hw.1.1.2 (by omega)⟩, hw.1.2⟩, hw.2⟩
        | exact ⟨⟨fun _ => hw.2, hw.1.1.1, hw.1.1.2⟩, hw.1.2⟩
  · exact Eventually.of_forall fun w => by simp [rubi314r18Nondeg, Defined, eval, recEnv, toInt?_neg_one, hd0]
  · simp only [rubi314r18Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((((env "d" + (env "e" * t ^ l)) ^ (k + 1) * (env "a" + (env "b" * I.ln (env "c" * t ^ j))) ^ i) * (t)⁻¹)) t := by
      convert hΦ1 using 1
      simp [eval, hk_p, hk_q, hk_r, hk_n, e1, e2, e2', toInt?_neg_one]
    have hΦ2' : HasDerivAt (Φ "I2") (((t ^ (l + ((-1) * 1)) * (env "d" + (env "e" * t ^ l)) ^ k) * (env "a" + (env "b" * I.ln (env "c" * t ^ j))) ^ i)) t := by
      convert hΦ2 using 1
      simp [eval, hk_p, hk_q, hk_r, hk_n, e1, e2, e2', toInt?_neg_one]
    have hEF : eval I (Function.update env "x" t) rubi314r18Nondeg.body = (((env "d" + (env "e" * t ^ l)) ^ k * (env "a" + (env "b" * I.ln (env "c" * t ^ j))) ^ i) * (t)⁻¹) := by
      simp [rubi314r18Nondeg, eval, hk_p, hk_q, hk_r, hk_n, toInt?_neg_one]
    have hfun : (fun w => eval I (recEnv env (rubi314r18Nondeg.integrals.map (·.1)) Φ "x" w) rubi314r18Nondeg.result) =
        fun w => (((1 * (env "d")⁻¹) * Φ "I1" w) + ((((-1) * env "e") * (env "d")⁻¹) * Φ "I2" w)) := by
      funext w
      simp [rubi314r18Nondeg, eval, recEnv, toInt?_neg_one]
      try first | ring1 | simp
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have ht0 : t ≠ 0 := by simp_all
    have hD0 : (env "d" + (env "e" * t ^ l)) ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (fun h' => by simp_all)
      · exact Or.inr (by omega)
    rw [zpow_succ_of _ _ hD0, show l + -1 * 1 = l - 1 by ring, zpow_sub_one₀ ht0]
    have hd : env "d" * (env "d")⁻¹ = 1 := mul_inv_cancel₀ hd0
    generalize (env "d" + (env "e" * t ^ l)) ^ k = Y
    generalize (env "a" + (env "b" * I.ln (env "c" * t ^ j))) ^ i = Lp
    generalize t ^ l = Xr
    generalize t⁻¹ = xi
    generalize (env "d")⁻¹ = di at hd ⊢
    linear_combination (Y * Lp * xi) * hd

theorem rubi314r18Nondeg_real : rubi314r18Nondeg.Holds .real :=
  rubi314r18Nondeg_holds Interp.real

theorem rubi314r18Nondeg_complex : rubi314r18Nondeg.Holds .complex :=
  rubi314r18Nondeg_holds Interp.complex

/-- **3.1.5 #17** with `d ≠ 0`: `(d + e xʳ)/x - e xʳ⁻¹ = d/x`.** -/
theorem rubi315r17Nondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi315r17Nondeg.conditions rubi315r17Nondeg.body rubi315r17Nondeg.result rubi315r17Nondeg.integrals := by
  intro env hc t hF
  have hd0 : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi315r17Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hk_p : I.toInt? (env "p") with _ | i
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi315r17Nondeg, Defined, eval, hk_p] at h
  have h_p : env "p" = (i : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  rcases hk_q : I.toInt? (env "q") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi315r17Nondeg, Defined, eval, hk_p, hk_q] at h
  have h_q : env "q" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_q
  rcases hk_r : I.toInt? (env "r") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi315r17Nondeg, Defined, eval, hk_p, hk_q, hk_r] at h
  have h_r : env "r" = (l : 𝕜) := (I.toInt?_eq _ _).1 hk_r
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi315r17Nondeg, Defined, eval, hk_p, hk_q, hk_r, hk_n] at h
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have e1 : I.toInt? (env "q" + 1) = some (k + 1) := (I.toInt?_eq _ _).2 (by rw [h_q]; push_cast; ring)
  have e2 : I.toInt? (env "r" + -1 * 1) = some (l + -1 * 1) := (I.toInt?_eq _ _).2 (by rw [h_r]; push_cast; ring)
  have e2' : I.toInt? (env "r" + -1) = some (l + -1 * 1) := (I.toInt?_eq _ _).2 (by rw [h_r]; push_cast; ring)
  have h0 := hF.self_of_nhds
  simp [rubi315r17Nondeg, Defined, eval, hk_p, hk_q, hk_r, hk_n, toInt?_neg_one] at h0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi315r17Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    all_goals
      filter_upwards [hF] with w hw
      simp [rubi315r17Nondeg, Defined, eval, hk_p, hk_q, hk_r, hk_n, toInt?_neg_one] at hw
      simp [Defined, eval, hk_p, hk_q, hk_r, hk_n, e1, e2, e2', toInt?_neg_one]
      first
        | done
        | exact hw.1
        | exact ⟨⟨fun h => hw.1.1 (by omega), hw.1.2⟩, hw.2⟩
        | exact ⟨hw.1, hw.2.1⟩
        | exact ⟨hw.1, hw.2.2⟩
        | exact ⟨⟨fun h => by
            by_cases hm : mm < 0
            · exact hw.1.1 hm
            · exact hw.2.1 (by omega), hw.1.2⟩, hw.2⟩
        | exact ⟨⟨⟨hw.1.1.1, fun h => hw.1.1.2 (by omega)⟩, hw.1.2⟩, hw.2⟩
        | exact ⟨⟨fun _ => hw.2, hw.1.1.1, hw.1.1.2⟩, hw.1.2⟩
  · exact Eventually.of_forall fun w => by simp [rubi315r17Nondeg, Defined, eval, recEnv, toInt?_neg_one, hd0]
  · simp only [rubi315r17Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((((env "d" + (env "e" * t ^ l)) ^ (k + 1) * (env "a" + (env "b" * I.ln (env "c" * t ^ j))) ^ i) * (t)⁻¹)) t := by
      convert hΦ1 using 1
      simp [eval, hk_p, hk_q, hk_r, hk_n, e1, e2, e2', toInt?_neg_one]
    have hΦ2' : HasDerivAt (Φ "I2") (((t ^ (l + ((-1) * 1)) * (env "d" + (env "e" * t ^ l)) ^ k) * (env "a" + (env "b" * I.ln (env "c" * t ^ j))) ^ i)) t := by
      convert hΦ2 using 1
      simp [eval, hk_p, hk_q, hk_r, hk_n, e1, e2, e2', toInt?_neg_one]
    have hEF : eval I (Function.update env "x" t) rubi315r17Nondeg.body = (((env "d" + (env "e" * t ^ l)) ^ k * (env "a" + (env "b" * I.ln (env "c" * t ^ j))) ^ i) * (t)⁻¹) := by
      simp [rubi315r17Nondeg, eval, hk_p, hk_q, hk_r, hk_n, toInt?_neg_one]
    have hfun : (fun w => eval I (recEnv env (rubi315r17Nondeg.integrals.map (·.1)) Φ "x" w) rubi315r17Nondeg.result) =
        fun w => (((1 * (env "d")⁻¹) * Φ "I1" w) + ((((-1) * env "e") * (env "d")⁻¹) * Φ "I2" w)) := by
      funext w
      simp [rubi315r17Nondeg, eval, recEnv, toInt?_neg_one]
      try first | ring1 | simp
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have ht0 : t ≠ 0 := by simp_all
    have hD0 : (env "d" + (env "e" * t ^ l)) ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (fun h' => by simp_all)
      · exact Or.inr (by omega)
    rw [zpow_succ_of _ _ hD0, show l + -1 * 1 = l - 1 by ring, zpow_sub_one₀ ht0]
    have hd : env "d" * (env "d")⁻¹ = 1 := mul_inv_cancel₀ hd0
    generalize (env "d" + (env "e" * t ^ l)) ^ k = Y
    generalize (env "a" + (env "b" * I.ln (env "c" * t ^ j))) ^ i = Lp
    generalize t ^ l = Xr
    generalize t⁻¹ = xi
    generalize (env "d")⁻¹ = di at hd ⊢
    linear_combination (Y * Lp * xi) * hd

theorem rubi315r17Nondeg_real : rubi315r17Nondeg.Holds .real :=
  rubi315r17Nondeg_holds Interp.real

theorem rubi315r17Nondeg_complex : rubi315r17Nondeg.Holds .complex :=
  rubi315r17Nondeg_holds Interp.complex

end Proofs

end OSR.IntegrationRec66
