import OSR.IntegrationNum1

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, eighth batch

Proofs of strengthened variants first distributed unproved
(`OSR.IntegrationNum1`, which keeps their definitions): the reductions
1.2.1.3 #15 (`p < -1`), 1.2.1.1 #5 (`p > 0`, from
`(b + 2 c x)² - (b² - 4 a c) = 4 c (a + b x + c x²)`) and 1.2.2.2 #17
(`m < -1`, from `(a + b x² + c x⁴) - x² (b + c x²) = a`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec56

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








/-- **1.2.1.3 #15** with `c (p + 1) (b² - 4 a c) ≠ 0`: the classical reduction of `p < -1`. -/
theorem rubi1213r15Nondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi1213r15Nondeg.conditions rubi1213r15Nondeg.body rubi1213r15Nondeg.result rubi1213r15Nondeg.integrals := by
  intro env hc t hF
  have hW : (env "c" * (env "p" + 1) * (env "b" ^ 2 + -1 * 4 * env "a" * env "c")) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.var "p") (.int 1))) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int 0)) (by simp [rubi1213r15Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r15Nondeg, Defined, eval, hkp] at h
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkp1 : I.toInt? (env "p" + 1) = some (q + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1213r15Nondeg.body →
      (q < 0 → (env "a" + env "b" * w + env "c" * w ^ 2) ≠ 0) := by
    intro w h
    simp [rubi1213r15Nondeg, Defined, eval, hkp, toInt?_two] at h
    exact h
  have ht := hD t hF.self_of_nhds
  have hW' := hW
  simp only [ne_eq, mul_eq_zero, not_or] at hW'
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1213r15Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, hkp1, toInt?_two]
    exact fun h' => h (by omega)
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1213r15Nondeg, Defined, eval, recEnv, hkp1, toInt?_two, toInt?_neg_one]
    refine ⟨fun h' => h (by omega), ?_⟩
    simpa using hW'
  · simp only [rubi1213r15Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" * t + env "c" * t ^ 2) ^ (q + 1)) t := by
      convert hΦ using 1
      simp [eval, hkp1, toInt?_two]
      try ring
    have hEF : eval I (Function.update env "x" t) rubi1213r15Nondeg.body =
        (env "d" + env "e" * t) * (env "f" + env "g" * t) * (env "a" + env "b" * t + env "c" * t ^ 2) ^ q := by
      simp [rubi1213r15Nondeg, eval, hkp, toInt?_two]
    set u := (env "c" * (env "p" + 1) * (env "b" ^ 2 + -1 * 4 * env "a" * env "c"))⁻¹ with hu_def
    have hU : (env "c" * (env "p" + 1) * (env "b" ^ 2 + -1 * 4 * env "a" * env "c")) * u = 1 := by rw [hu_def]; exact mul_inv_cancel₀ hW
    have hfun : (fun w => eval I (recEnv env (rubi1213r15Nondeg.integrals.map (·.1)) Φ "x" w) rubi1213r15Nondeg.result) =
        fun w => ((env "a"*env "b"*env "e"*env "g" - 2*env "a"*env "c"*env "d"*env "g" - 2*env "a"*env "c"*env "e"*env "f" + env "b"*env "c"*env "d"*env "f") + (-2*env "a"*env "c"*env "e"*env "g" + env "b"^2*env "e"*env "g" - env "b"*env "c"*env "d"*env "g" - env "b"*env "c"*env "e"*env "f" + 2*env "c"^2*env "d"*env "f") * w) * u * (env "a" + env "b" * w + env "c" * w ^ 2) ^ (q + 1) + ((-1) * (((((env "b" ^ 2 * env "e") * env "g") * (env "p" + 2)) + ((((((-1) * 2) * env "a") * env "c") * env "e") * env "g")) + ((env "c" * ((((2 * env "c") * env "d") * env "f") + (((-1) * env "b") * ((env "e" * env "f") + (env "d" * env "g"))))) * ((2 * env "p") + 3)))) * u * Φ "I1" w := by
      funext w
      simp [rubi1213r15Nondeg, eval, recEnv, hkp1, toInt?_two, toInt?_neg_one, hu_def]
      try ring
    rw [hfun, hEF]
    have hA1 : (env "a" + env "b" * t + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ q + 1 := by
      by_cases h : q + 1 < 0
      · exact Or.inl (ht (by omega))
      · exact Or.inr (by omega)
    have hA0 : (env "a" + env "b" * t + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ q := by
      by_cases h : q < 0
      · exact Or.inl (ht h)
      · exact Or.inr (by omega)
    have hin : HasDerivAt (fun w => (env "a" + env "b" * w + env "c" * w ^ 2)) (env "b" + env "c" * (2 * t)) t := by
      have := (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add ((hasDerivAt_pow 2 t).const_mul (env "c"))
      convert this using 1 <;> first | (norm_num; done) | (norm_num; ring) | ring | (funext w; simp only [id]; ring) | (funext w; simp only [id])
    have hN : HasDerivAt (fun w => (env "a"*env "b"*env "e"*env "g" - 2*env "a"*env "c"*env "d"*env "g" - 2*env "a"*env "c"*env "e"*env "f" + env "b"*env "c"*env "d"*env "f") + (-2*env "a"*env "c"*env "e"*env "g" + env "b"^2*env "e"*env "g" - env "b"*env "c"*env "d"*env "g" - env "b"*env "c"*env "e"*env "f" + 2*env "c"^2*env "d"*env "f") * w) (-2*env "a"*env "c"*env "e"*env "g" + env "b"^2*env "e"*env "g" - env "b"*env "c"*env "d"*env "g" - env "b"*env "c"*env "e"*env "f" + 2*env "c"^2*env "d"*env "f") t := by
      have := ((hasDerivAt_id' t).const_mul (-2*env "a"*env "c"*env "e"*env "g" + env "b"^2*env "e"*env "g" - env "b"*env "c"*env "d"*env "g" - env "b"*env "c"*env "e"*env "f" + 2*env "c"^2*env "d"*env "f")).const_add (env "a"*env "b"*env "e"*env "g" - 2*env "a"*env "c"*env "d"*env "g" - 2*env "a"*env "c"*env "e"*env "f" + env "b"*env "c"*env "d"*env "f")
      convert this using 1 <;> first | ring | (funext w; simp only [id])
    refine (((hN.mul_const u).mul (HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ hA1) hin)).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    rw [zpow_succ_of _ _ hA0]
    generalize (env "a" + env "b" * t + env "c" * t ^ 2) ^ q = Y
    clear_value u
    simp only [hp] at hU ⊢
    push_cast
    linear_combination (Y * (env "d" + env "e" * t) * (env "f" + env "g" * t)) * hU

theorem rubi1213r15Nondeg_real : rubi1213r15Nondeg.Holds .real :=
  rubi1213r15Nondeg_holds Interp.real

theorem rubi1213r15Nondeg_complex : rubi1213r15Nondeg.Holds .complex :=
  rubi1213r15Nondeg_holds Interp.complex

/-- **1.2.1.1 #5** with `2 c (2 p + 1) ≠ 0` and `p > 0`: `(b + 2 c x)² - (b² - 4 a c) = 4 c (a + b x + c x²)`. -/
theorem rubi1211r5Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi1211r5Nondeg.conditions rubi1211r5Nondeg.body rubi1211r5Nondeg.result rubi1211r5Nondeg.integrals := by
  intro env hc t hF
  have hW : (2 * env "c" * (2 * env "p" + 1)) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1))) (.int 0)) (by simp [rubi1211r5Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hgp := hc (.gt (.var "p") (.int 0)) (by simp [rubi1211r5Nondeg])
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1211r5Nondeg, Defined, eval, hkp] at h
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hq1 : 0 < q := by
    simp only [Cond.Holds, Defined, eval, true_and] at hgp
    rw [hp] at hgp
    have h' : I.lt ((0 : ℚ) : 𝕜) ((q : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_zero]; simpa using hgp
    exact_mod_cast (hlt _ _).1 h'
  have e3 : I.toInt? (env "p" + -1) = some (q - 1) := (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have e4 : I.toInt? (env "p" - 1) = some (q - 1) := (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have e5 : I.toInt? (env "p" + -1 * 1) = some (q - 1) := (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hW' := hW
  simp only [ne_eq, mul_eq_zero, not_or] at hW'
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1211r5Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    exact Eventually.of_forall fun w => by
      simp [Defined, eval, e3, e4, e5, toInt?_two]
      first | done | (intro h; omega) | omega
  · exact Eventually.of_forall fun w => by
      simp [rubi1211r5Nondeg, Defined, eval, recEnv, hkp, toInt?_two, toInt?_neg_one]
      first | done | exact ⟨⟨fun h' => absurd h' (by omega), hW'⟩, hW'⟩ | exact ⟨fun h' => absurd h' (by omega), hW'⟩ | tauto
  · simp only [rubi1211r5Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" * t + env "c" * t ^ 2) ^ (q - 1)) t := by
      convert hΦ using 1
      simp [eval, e3, e4, e5, toInt?_two]
      try ring
    have hEF : eval I (Function.update env "x" t) rubi1211r5Nondeg.body = (env "a" + env "b" * t + env "c" * t ^ 2) ^ q := by
      simp [rubi1211r5Nondeg, eval, hkp, toInt?_two]
    set u := (2 * env "c" * (2 * env "p" + 1))⁻¹ with hu_def
    have hU : (2 * env "c" * (2 * env "p" + 1)) * u = 1 := by rw [hu_def]; exact mul_inv_cancel₀ hW
    have hfun : (fun w => eval I (recEnv env (rubi1211r5Nondeg.integrals.map (·.1)) Φ "x" w) rubi1211r5Nondeg.result) =
        fun w => (env "b" + 2 * env "c" * w) * u * (env "a" + env "b" * w + env "c" * w ^ 2) ^ q + -1 * env "p" * (env "b" ^ 2 + -1 * 4 * env "a" * env "c") * u * Φ "I1" w := by
      funext w
      simp [rubi1211r5Nondeg, eval, recEnv, hkp, toInt?_two, toInt?_neg_one, hu_def]
      try ring
    rw [hfun, hEF]
    have hin : HasDerivAt (fun w => (env "a" + env "b" * w + env "c" * w ^ 2)) (env "b" + env "c" * (2 * t)) t := by
      have := (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add ((hasDerivAt_pow 2 t).const_mul (env "c"))
      convert this using 1 <;> first | (norm_num; done) | (norm_num; ring) | ring | (funext w; simp only [id]; ring) | (funext w; simp only [id])
    have hN : HasDerivAt (fun w => env "b" + 2 * env "c" * w) (2 * env "c") t := by
      have := ((hasDerivAt_id' t).const_mul (2 * env "c")).const_add (env "b")
      convert this using 1 <;> first | (norm_num; done) | (norm_num; ring) | ring | (funext w; simp only [id]; ring) | (funext w; simp only [id])
    refine (((hN.mul_const u).mul (HasDerivAt.comp t (hasDerivAt_zpow q _ (Or.inr (by omega))) hin)).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def]
    have hYA : (env "a" + env "b" * t + env "c" * t ^ 2) ^ q = (env "a" + env "b" * t + env "c" * t ^ 2) ^ (q - 1) * (env "a" + env "b" * t + env "c" * t ^ 2) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    rw [hYA]
    generalize (env "a" + env "b" * t + env "c" * t ^ 2) ^ (q - 1) = Y
    clear_value u
    simp only [hp] at hU ⊢
    push_cast
    linear_combination (Y * (env "a" + env "b" * t + env "c" * t ^ 2)) * hU

theorem rubi1211r5Nondeg_real : rubi1211r5Nondeg.Holds .real :=
  rubi1211r5Nondeg_holds Interp.real Interp.real_lt_rat

theorem rubi1211r5Nondeg_complex : rubi1211r5Nondeg.Holds .complex :=
  rubi1211r5Nondeg_holds Interp.complex Interp.complex_lt_rat

/-- **1.2.2.2 #17** with `a d (m + 1) ≠ 0` and `a d² ≠ 0`: `(a + b x² + c x⁴) - x² (b + c x²) = a`. -/
theorem rubi1222r17Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi1222r17Nondeg.conditions rubi1222r17Nondeg.body rubi1222r17Nondeg.result rubi1222r17Nondeg.integrals := by
  intro env hc t hF
  have hW1 : env "a" * env "d" * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi1222r17Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW2 : env "a" * env "d" ^ 2 ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "a") (.pow (.var "d") (.int 2))) (.int 0)) (by simp [rubi1222r17Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  have hgm := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi1222r17Nondeg])
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1222r17Nondeg, Defined, eval, hkm] at h
  have hm : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hk0 : k < -1 := by
    simp only [Cond.Holds, Defined, eval, true_and] at hgm
    rw [hm] at hgm
    have h' : I.lt ((k : ℚ) : 𝕜) ((((-1 : ℤ)) : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hgm
    exact_mod_cast (hlt _ _).1 h'
  have hkm1 : I.toInt? (env "m" + 1) = some (k + 1) := (I.toInt?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hkm2 : I.toInt? (env "m" + 2) = some (k + 2) := (I.toInt?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1222r17Nondeg.body →
      env "d" * w ≠ 0 ∧ (env "a" + env "b" * w ^ 2 + env "c" * w ^ 4) ≠ 0 := by
    intro w h
    simp [rubi1222r17Nondeg, Defined, eval, hkm, toInt?_two, toInt?_four, toInt?_neg_one] at h
    have h1 := h.1 (by omega)
    refine ⟨?_, ?_⟩ <;> first | exact h.2 | (simp only [ne_eq, mul_eq_zero, not_or]; tauto) | tauto
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1222r17Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hd0, hQ0⟩ := hD w hw
    have hd0' := hd0
    simp only [ne_eq, mul_eq_zero, not_or] at hd0'
    simp [Defined, eval, hkm2, toInt?_two, toInt?_four, toInt?_neg_one, hd0', hQ0]
    first | done | omega | tauto
  · filter_upwards [hF] with w hw
    obtain ⟨hd0, hQ0⟩ := hD w hw
    have hd0' := hd0
    simp only [ne_eq, mul_eq_zero, not_or] at hd0'
    have hW1' := hW1
    have hW2' := hW2
    simp only [ne_eq, mul_eq_zero, not_or, pow_eq_zero_iff, OfNat.ofNat_ne_zero, not_false_eq_true] at hW1' hW2'
    simp [rubi1222r17Nondeg, Defined, eval, recEnv, hkm1, toInt?_two, toInt?_neg_one, hd0']
    first | done | tauto | simp_all
  · simp only [rubi1222r17Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" * t) ^ (k + 2) * (env "b" + env "c" * t ^ 2) * (env "a" + env "b" * t ^ 2 + env "c" * t ^ 4)⁻¹) t := by
      convert hΦ using 1
      simp [eval, hkm2, toInt?_two, toInt?_four, toInt?_neg_one]
      try ring
    have hEF : eval I (Function.update env "x" t) rubi1222r17Nondeg.body = (env "d" * t) ^ k * (env "a" + env "b" * t ^ 2 + env "c" * t ^ 4)⁻¹ := by
      simp [rubi1222r17Nondeg, eval, hkm, toInt?_two, toInt?_four, toInt?_neg_one]
    set u1 := (env "a" * env "d" * (env "m" + 1))⁻¹ with hu1_def
    set u2 := (env "a" * env "d" ^ 2)⁻¹ with hu2_def
    have hU1 : env "a" * env "d" * (env "m" + 1) * u1 = 1 := by rw [hu1_def]; exact mul_inv_cancel₀ hW1
    have hU2 : env "a" * env "d" ^ 2 * u2 = 1 := by rw [hu2_def]; exact mul_inv_cancel₀ hW2
    have hfun : (fun w => eval I (recEnv env (rubi1222r17Nondeg.integrals.map (·.1)) Φ "x" w) rubi1222r17Nondeg.result) =
        fun w => (env "d" * w) ^ (k + 1) * u1 + -1 * u2 * Φ "I1" w := by
      funext w
      simp [rubi1222r17Nondeg, eval, recEnv, hkm1, toInt?_two, toInt?_neg_one, hu1_def, hu2_def]
      try ring
    rw [hfun, hEF]
    refine (((HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (Or.inl ht.1)) ((hasDerivAt_id' t).const_mul (env "d"))).mul_const u1).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have hFs : (env "d" * t) ^ (k + 2) = (env "d" * t) ^ k * (env "d" * t) ^ 2 := by
      rw [zpow_add₀ ht.1]; norm_cast
    rw [hFs]
    have hA : (env "a" + env "b" * t ^ 2 + env "c" * t ^ 4) * (env "a" + env "b" * t ^ 2 + env "c" * t ^ 4)⁻¹ = 1 := mul_inv_cancel₀ ht.2
    generalize (env "d" * t) ^ k = C
    generalize (env "a" + env "b" * t ^ 2 + env "c" * t ^ 4)⁻¹ = Ai at hA ⊢
    clear_value u1 u2
    simp only [hm] at hU1 ⊢
    push_cast
    linear_combination C * ((-(((k : 𝕜) + 1) * env "d" * u1)) * hA +
      (Ai * (1 + t ^ 2 * (env "b" + env "c" * t ^ 2) * env "d" ^ 2 * u2)) * hU1 +
      (-(Ai * t ^ 2 * (env "b" + env "c" * t ^ 2) * (((k : 𝕜) + 1) * env "d" * u1))) * hU2)

theorem rubi1222r17Nondeg_real : rubi1222r17Nondeg.Holds .real :=
  rubi1222r17Nondeg_holds Interp.real Interp.real_lt_rat

theorem rubi1222r17Nondeg_complex : rubi1222r17Nondeg.Holds .complex :=
  rubi1222r17Nondeg_holds Interp.complex Interp.complex_lt_rat

end Proofs

end OSR.IntegrationRec56
