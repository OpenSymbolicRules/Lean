import OSR.IntegrationNum1

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, sixth batch

Proofs of strengthened variants first distributed unproved
(`OSR.IntegrationNum1`, which keeps their definitions): 1.2.1.6 #9 with
`e ≠ 0` and `f ≠ 0`, where `c e² - b e f + a f² = 0` makes `x (a + b x + c x²)`
equal to `(a/e + c x/f) (e x + f x²)`, and 1.2.1.3 #36 with `f ≠ 0` and
`g ≠ 0`, where `c f² - b f g + a g² = 0` factors `a + b x + c x²` as
`(f + g x) (a/f + c x/g)`; and 1.2.2.4 #55 to #58 (partial fractions in
`x²`, using `p > 0` and `m < 0`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec54

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








/-- **1.2.1.6 #9** with `e ≠ 0` and `f ≠ 0`: `x (a + b x + c x²) = (a/e + c x/f) (e x + f x²)`. -/
theorem rubi1216r9Nondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi1216r9Nondeg.conditions rubi1216r9Nondeg.body rubi1216r9Nondeg.result rubi1216r9Nondeg.integrals := by
  intro env hc t hF
  have he : env "e" ≠ 0 := by
    have h := hc (.ne (.var "e") (.int 0)) (by simp [rubi1216r9Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hf : env "f" ≠ 0 := by
    have h := hc (.ne (.var "f") (.int 0)) (by simp [rubi1216r9Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have h1 : env "c" * env "e" ^ 2 - env "b" * env "e" * env "f" + env "a" * env "f" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "e") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")) (.var "f"))) (.app2 .mul (.var "a") (.pow (.var "f") (.int 2)))) (.int 0)) (by simp [rubi1216r9Nondeg])
    simp [Cond.Holds, Defined, eval, toInt?_two] at h
    linear_combination h
  have hei : env "e" * (env "e")⁻¹ = 1 := mul_inv_cancel₀ he
  have hfi : env "f" * (env "f")⁻¹ = 1 := mul_inv_cancel₀ hf
  have hQ : ∀ w : 𝕜, w * (env "a" + env "b" * w + env "c" * w ^ 2) = (env "a" * (env "e")⁻¹ + env "c" * (env "f")⁻¹ * w) * (env "e" * w + env "f" * w ^ 2) := fun w => by
    linear_combination (-w ^ 2 * (env "e")⁻¹ * (env "f")⁻¹) * h1 +
      (-env "a" * w + w ^ 2 * env "c" * env "e" * (env "f")⁻¹ - env "b" * w ^ 2) * hei +
      (-env "c" * w ^ 3 + w ^ 2 * env "a" * env "f" * (env "e")⁻¹ - env "b" * w ^ 2 * env "e" * (env "e")⁻¹) * hfi
  rcases hkp : I.toInt? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1216r9Nondeg, Defined, eval, hkp] at h
  rcases hkq : I.toInt? (env "q") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1216r9Nondeg, Defined, eval, hkp, hkq] at h
  have hp : env "p" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hq' : env "q" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkq
  have hkpq : I.toInt? (env "p" + env "q") = some (k + q) :=
    (I.toInt?_eq _ _).2 (by rw [hp, hq']; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1216r9Nondeg.body →
      (k < 0 → w ≠ 0) ∧ (k < 0 → (env "a" + env "b" * w + env "c" * w ^ 2) ≠ 0) ∧ (q < 0 → (env "e" * w + env "f" * w ^ 2) ≠ 0) := by
    intro w h
    simp [rubi1216r9Nondeg, Defined, eval, hkp, hkq, toInt?_two] at h
    tauto
  have hR : ∀ w, Defined I (Function.update env "x" w) rubi1216r9Nondeg.body →
      (k < 0 → (env "a" * (env "e")⁻¹ + env "c" * (env "f")⁻¹ * w) ≠ 0) ∧ (k + q < 0 → (env "e" * w + env "f" * w ^ 2) ≠ 0) := by
    intro w hw
    obtain ⟨h1', h2', h3'⟩ := hD w hw
    refine ⟨fun hk hQ0 => mul_ne_zero (h1' hk) (h2' hk) (by rw [hQ w, hQ0, zero_mul]), fun hkq hB0 => ?_⟩
    by_cases hq : q < 0
    · exact h3' hq hB0
    · exact mul_ne_zero (h1' (by omega)) (h2' (by omega)) (by rw [hQ w, hB0, mul_zero])
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1216r9Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hr1, hr2⟩ := hR w hw
    simp [Defined, eval, hkp, hkpq, toInt?_neg_one, toInt?_two, he, hf]
    first | exact ⟨hr1, hr2⟩ | exact ⟨hr2, hr1⟩ | tauto
  · exact Eventually.of_forall fun w => by simp [rubi1216r9Nondeg, Defined, eval, recEnv]
  · simp only [rubi1216r9Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (rubi1216r9Nondeg.integrals.map (·.1)) Φ "x" w) rubi1216r9Nondeg.result) =
        Φ "I1" := by
      funext w
      simp [rubi1216r9Nondeg, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    have hz : (env "e" * t + env "f" * t ^ 2) ≠ 0 ∨ k + q ≠ 0 ∨ k = 0 ∧ q = 0 := by
      by_cases hB0 : (env "e" * t + env "f" * t ^ 2) = 0
      · have hq : 0 ≤ q := by
          by_contra hq
          exact ht.2.2 (by omega) hB0
        have hk : 0 ≤ k := by
          by_contra hk
          exact mul_ne_zero (ht.1 (by omega)) (ht.2.1 (by omega)) (by rw [hQ t, hB0, mul_zero])
        by_cases hkq : k + q = 0
        · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
        · exact Or.inr (Or.inl hkq)
      · exact Or.inl hB0
    have e1 : t ^ k * (env "a" + env "b" * t + env "c" * t ^ 2) ^ k = (env "a" * (env "e")⁻¹ + env "c" * (env "f")⁻¹ * t) ^ k * (env "e" * t + env "f" * t ^ 2) ^ k := by
      rw [← mul_zpow, ← mul_zpow, hQ t]
    have e2 : (env "e" * t + env "f" * t ^ 2) ^ (k + q) = (env "e" * t + env "f" * t ^ 2) ^ k * (env "e" * t + env "f" * t ^ 2) ^ q := zpow_add' hz
    simp [rubi1216r9Nondeg, eval, hkp, hkq, hkpq, toInt?_neg_one, toInt?_two]
    rw [e2]
    linear_combination (-(env "e" * t + env "f" * t ^ 2) ^ q) * e1

theorem rubi1216r9Nondeg_real : rubi1216r9Nondeg.Holds .real :=
  rubi1216r9Nondeg_holds Interp.real

theorem rubi1216r9Nondeg_complex : rubi1216r9Nondeg.Holds .complex :=
  rubi1216r9Nondeg_holds Interp.complex

/-- **1.2.1.3 #36** with `f ≠ 0` and `g ≠ 0`: `a + b x + c x² = (f + g x) (a/f + c x/g)`. -/
theorem rubi1213r36Nondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi1213r36Nondeg.conditions rubi1213r36Nondeg.body rubi1213r36Nondeg.result rubi1213r36Nondeg.integrals := by
  intro env hc t hF
  have hf : env "f" ≠ 0 := by
    have h := hc (.ne (.var "f") (.int 0)) (by simp [rubi1213r36Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hg : env "g" ≠ 0 := by
    have h := hc (.ne (.var "g") (.int 0)) (by simp [rubi1213r36Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have h1 : env "c" * env "f" ^ 2 - env "b" * env "f" * env "g" + env "a" * env "g" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "f") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "f")) (.var "g"))) (.app2 .mul (.var "a") (.pow (.var "g") (.int 2)))) (.int 0)) (by simp [rubi1213r36Nondeg])
    simp [Cond.Holds, Defined, eval, toInt?_two] at h
    linear_combination h
  have hfi : env "f" * (env "f")⁻¹ = 1 := mul_inv_cancel₀ hf
  have hgi : env "g" * (env "g")⁻¹ = 1 := mul_inv_cancel₀ hg
  have hQ : ∀ w : 𝕜, env "a" + env "b" * w + env "c" * w ^ 2 = (env "f" + env "g" * w) * (env "a" * (env "f")⁻¹ + env "c" * (env "g")⁻¹ * w) := fun w => by
    linear_combination (-w * (env "f")⁻¹ * (env "g")⁻¹) * h1 +
      (-env "a" + w * env "c" * env "f" * (env "g")⁻¹ - env "b" * w) * hfi +
      (-env "c" * w ^ 2 + w * env "a" * env "g" * (env "f")⁻¹ - env "b" * w * env "f" * (env "f")⁻¹) * hgi
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r36Nondeg, Defined, eval, hkm] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r36Nondeg, Defined, eval, hkm, hkp] at h
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkp1 : I.toInt? (env "p" + 1) = some (q + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1213r36Nondeg.body →
      (k < 0 → (env "d" + env "e" * w) ≠ 0) ∧ (q < 0 → (env "a" + env "b" * w + env "c" * w ^ 2) ≠ 0) := by
    intro w h
    simp [rubi1213r36Nondeg, Defined, eval, hkm, hkp, toInt?_two] at h
    tauto
  have hR : ∀ w, Defined I (Function.update env "x" w) rubi1213r36Nondeg.body →
      (k < 0 → (env "d" + env "e" * w) ≠ 0) ∧ (q + 1 < 0 → (env "f" + env "g" * w) ≠ 0) ∧
        (q < 0 → (env "a" * (env "f")⁻¹ + env "c" * (env "g")⁻¹ * w) ≠ 0) := by
    intro w hw
    obtain ⟨h1', h2'⟩ := hD w hw
    exact ⟨h1', fun hq hF0 => h2' (by omega) (by rw [hQ w, hF0, zero_mul]),
      fun hq hQ0 => h2' hq (by rw [hQ w, hQ0, mul_zero])⟩
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1213r36Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hr1, hr2, hr3⟩ := hR w hw
    simp [Defined, eval, hkm, hkp, hkp1, toInt?_neg_one, hf, hg]
    first | exact ⟨⟨hr1, hr2⟩, hr3⟩ | exact ⟨hr1, hr2, hr3⟩ | tauto
  · exact Eventually.of_forall fun w => by simp [rubi1213r36Nondeg, Defined, eval, recEnv]
  · simp only [rubi1213r36Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (rubi1213r36Nondeg.integrals.map (·.1)) Φ "x" w) rubi1213r36Nondeg.result) =
        Φ "I1" := by
      funext w
      simp [rubi1213r36Nondeg, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    have hz : (env "f" + env "g" * t) ≠ 0 ∨ 0 ≤ q := by
      by_cases hq : q < 0
      · exact Or.inl fun hF0 => ht.2 hq (by rw [hQ t, hF0, zero_mul])
      · exact Or.inr (by omega)
    have e1 : (env "a" + env "b" * t + env "c" * t ^ 2) ^ q = (env "f" + env "g" * t) ^ q * (env "a" * (env "f")⁻¹ + env "c" * (env "g")⁻¹ * t) ^ q := by
      rw [hQ t, mul_zpow]
    have e2 : (env "f" + env "g" * t) ^ (q + 1) = (env "f" + env "g" * t) ^ q * (env "f" + env "g" * t) := zpow_succ_of _ _ hz
    simp [rubi1213r36Nondeg, eval, hkm, hkp, hkp1, toInt?_neg_one, toInt?_two]
    rw [e2]
    linear_combination (-((env "d" + env "e" * t) ^ k * (env "f" + env "g" * t))) * e1

theorem rubi1213r36Nondeg_real : rubi1213r36Nondeg.Holds .real :=
  rubi1213r36Nondeg_holds Interp.real

theorem rubi1213r36Nondeg_complex : rubi1213r36Nondeg.Holds .complex :=
  rubi1213r36Nondeg_holds Interp.complex

/-- **1.2.2.4 #55**: partial fractions in `x²` with the converted conditions. -/
theorem rubi1224r55Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi1224r55Nondeg.conditions rubi1224r55Nondeg.body rubi1224r55Nondeg.result rubi1224r55Nondeg.integrals := by
  intro env hc t hF
  have hW1 : env "d" ^ 2 ≠ 0 := by
    have h := hc (.ne (.pow (.var "d") (.int 2)) (.int 0)) (by simp [rubi1224r55Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  have hW2 : (env "d" ^ 2 * env "f" ^ 4) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.var "d") (.int 2)) (.pow (.var "f") (.int 4))) (.int 0)) (by simp [rubi1224r55Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two, toInt?_four] using h
  have hf0 : env "f" ≠ 0 := fun h => hW2 (by rw [h]; ring)
  have hgp := hc (.gt (.var "p") (.int 0)) (by simp [rubi1224r55Nondeg])
  have hgm := hc (.gt (.int (-2)) (.var "m")) (by simp [rubi1224r55Nondeg])
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1224r55Nondeg, Defined, eval, hkm] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1224r55Nondeg, Defined, eval, hkm, hkp] at h
  have hm : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hq1 : 0 < q := by
    simp only [Cond.Holds, Defined, eval, true_and] at hgp
    rw [hp] at hgp
    have h' : I.lt ((0 : ℚ) : 𝕜) ((q : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_zero]; simpa using hgp
    exact_mod_cast (hlt _ _).1 h'
  have hk0 : k < 0 := by
    simp only [Cond.Holds, Defined, eval, true_and] at hgm
    rw [hm] at hgm
    have h' : I.lt ((k : ℚ) : 𝕜) ((((-2 : ℤ)) : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hgm
    have := (hlt _ _).1 h'
    have : k < -2 := by exact_mod_cast this
    omega
  have e3 : I.toInt? (env "p" + -1) = some (q - 1) := (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have e4 : I.toInt? (env "p" - 1) = some (q - 1) := (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have e5 : I.toInt? (env "p" + -1 * 1) = some (q - 1) := (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have e6 : I.toInt? (env "m" + 4) = some (k + 4) := (I.toInt?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1224r55Nondeg.body →
      w ≠ 0 ∧ (env "d" + env "e" * w ^ 2) ≠ 0 := by
    intro w h
    simp [rubi1224r55Nondeg, Defined, eval, hkm, hkp, toInt?_two, toInt?_four, toInt?_neg_one] at h
    constructor <;> tauto
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1224r55Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      obtain ⟨hw0, hB0⟩ := hD w hw
      simp [Defined, eval, hkm, e3, e4, e5, toInt?_two, toInt?_four, hf0, hw0]
      first | done | omega | tauto
    · filter_upwards [hF] with w hw
      obtain ⟨hw0, hB0⟩ := hD w hw
      simp [Defined, eval, e6, e3, e4, e5, toInt?_two, toInt?_four, toInt?_neg_one, hf0, hw0, hB0]
      first | done | omega | tauto
  · exact Eventually.of_forall fun w => by
      simp [rubi1224r55Nondeg, Defined, eval, recEnv, toInt?_neg_one, toInt?_two, toInt?_four]
      first | done | exact ⟨hW1, hW2⟩ | tauto | simp_all
  · simp only [rubi1224r55Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "f" * t) ^ k * (env "a" * env "d" + (env "b" * env "d" + -1 * env "a" * env "e") * t ^ 2) * (env "a" + env "b" * t ^ 2 + env "c" * t ^ 4) ^ (q - 1)) t := by
      convert hΦ1 using 1
      simp [eval, hkm, e3, e4, e5, toInt?_two, toInt?_four]
      try ring
    have hΦ2' : HasDerivAt (Φ "I2") ((env "f" * t) ^ (k + 4) * (env "a" + env "b" * t ^ 2 + env "c" * t ^ 4) ^ (q - 1) * (env "d" + env "e" * t ^ 2)⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, e6, e3, e4, e5, toInt?_two, toInt?_four, toInt?_neg_one]
      try ring
    have hEF : eval I (Function.update env "x" t) rubi1224r55Nondeg.body =
        (env "f" * t) ^ k * (env "a" + env "b" * t ^ 2 + env "c" * t ^ 4) ^ q * (env "d" + env "e" * t ^ 2)⁻¹ := by
      simp [rubi1224r55Nondeg, eval, hkm, hkp, toInt?_two, toInt?_four, toInt?_neg_one]
    have hfun : (fun w => eval I (recEnv env (rubi1224r55Nondeg.integrals.map (·.1)) Φ "x" w) rubi1224r55Nondeg.result) =
        fun w => 1 * (env "d" ^ 2)⁻¹ * Φ "I1" w + (env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2) * ((env "d" ^ 2 * env "f" ^ 4))⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi1224r55Nondeg, eval, recEnv, toInt?_neg_one, toInt?_two, toInt?_four]
      try ring
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have hYA : (env "a" + env "b" * t ^ 2 + env "c" * t ^ 4) ^ q = (env "a" + env "b" * t ^ 2 + env "c" * t ^ 4) ^ (q - 1) * (env "a" + env "b" * t ^ 2 + env "c" * t ^ 4) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    have hFs : (env "f" * t) ^ (k + 4) = (env "f" * t) ^ k * (env "f" * t) ^ 4 := by
      rw [zpow_add₀ (mul_ne_zero hf0 ht.1)]; norm_cast
    rw [hYA, hFs]
    have hB : (env "d" + env "e" * t ^ 2) * (env "d" + env "e" * t ^ 2)⁻¹ = 1 := mul_inv_cancel₀ ht.2
    have hu1 : env "d" ^ 2 * (env "d" ^ 2)⁻¹ = 1 := mul_inv_cancel₀ hW1
    have hu2 : (env "d" ^ 2 * env "f" ^ 4) * ((env "d" ^ 2 * env "f" ^ 4))⁻¹ = 1 := mul_inv_cancel₀ hW2
    generalize (env "f" * t) ^ k = C
    generalize (env "a" + env "b" * t ^ 2 + env "c" * t ^ 4) ^ (q - 1) = Y
    generalize (env "d" + env "e" * t ^ 2)⁻¹ = Bi at hB ⊢
    generalize (env "d" ^ 2)⁻¹ = u1 at hu1 ⊢
    generalize ((env "d" ^ 2 * env "f" ^ 4))⁻¹ = u2 at hu2 ⊢
    linear_combination (C * Y) * ((-(1) * u1 * (env "a" * env "d" + (env "b" * env "d" + -1 * env "a" * env "e") * t ^ 2)) * hB +
      ((env "a" + env "b" * t ^ 2 + env "c" * t ^ 4) * Bi - (env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2) * t ^ 4 * Bi * env "f" ^ 4 * u2) * hu1 +
      ((env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2) * t ^ 4 * Bi * u1) * hu2)

theorem rubi1224r55Nondeg_real : rubi1224r55Nondeg.Holds .real :=
  rubi1224r55Nondeg_holds Interp.real Interp.real_lt_rat

theorem rubi1224r55Nondeg_complex : rubi1224r55Nondeg.Holds .complex :=
  rubi1224r55Nondeg_holds Interp.complex Interp.complex_lt_rat

/-- **1.2.2.4 #56**: partial fractions in `x²` with the converted conditions. -/
theorem rubi1224r56Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi1224r56Nondeg.conditions rubi1224r56Nondeg.body rubi1224r56Nondeg.result rubi1224r56Nondeg.integrals := by
  intro env hc t hF
  have hW1 : env "d" ^ 2 ≠ 0 := by
    have h := hc (.ne (.pow (.var "d") (.int 2)) (.int 0)) (by simp [rubi1224r56Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  have hW2 : (env "d" ^ 2 * env "f" ^ 4) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.var "d") (.int 2)) (.pow (.var "f") (.int 4))) (.int 0)) (by simp [rubi1224r56Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two, toInt?_four] using h
  have hf0 : env "f" ≠ 0 := fun h => hW2 (by rw [h]; ring)
  have hgp := hc (.gt (.var "p") (.int 0)) (by simp [rubi1224r56Nondeg])
  have hgm := hc (.gt (.int (-2)) (.var "m")) (by simp [rubi1224r56Nondeg])
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1224r56Nondeg, Defined, eval, hkm] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1224r56Nondeg, Defined, eval, hkm, hkp] at h
  have hm : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hq1 : 0 < q := by
    simp only [Cond.Holds, Defined, eval, true_and] at hgp
    rw [hp] at hgp
    have h' : I.lt ((0 : ℚ) : 𝕜) ((q : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_zero]; simpa using hgp
    exact_mod_cast (hlt _ _).1 h'
  have hk0 : k < 0 := by
    simp only [Cond.Holds, Defined, eval, true_and] at hgm
    rw [hm] at hgm
    have h' : I.lt ((k : ℚ) : 𝕜) ((((-2 : ℤ)) : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hgm
    have := (hlt _ _).1 h'
    have : k < -2 := by exact_mod_cast this
    omega
  have e3 : I.toInt? (env "p" + -1) = some (q - 1) := (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have e4 : I.toInt? (env "p" - 1) = some (q - 1) := (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have e5 : I.toInt? (env "p" + -1 * 1) = some (q - 1) := (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have e6 : I.toInt? (env "m" + 4) = some (k + 4) := (I.toInt?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1224r56Nondeg.body →
      w ≠ 0 ∧ (env "d" + env "e" * w ^ 2) ≠ 0 := by
    intro w h
    simp [rubi1224r56Nondeg, Defined, eval, hkm, hkp, toInt?_two, toInt?_four, toInt?_neg_one] at h
    constructor <;> tauto
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1224r56Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      obtain ⟨hw0, hB0⟩ := hD w hw
      simp [Defined, eval, hkm, e3, e4, e5, toInt?_two, toInt?_four, hf0, hw0]
      first | done | omega | tauto
    · filter_upwards [hF] with w hw
      obtain ⟨hw0, hB0⟩ := hD w hw
      simp [Defined, eval, e6, e3, e4, e5, toInt?_two, toInt?_four, toInt?_neg_one, hf0, hw0, hB0]
      first | done | omega | tauto
  · exact Eventually.of_forall fun w => by
      simp [rubi1224r56Nondeg, Defined, eval, recEnv, toInt?_neg_one, toInt?_two, toInt?_four]
      first | done | exact ⟨hW1, hW2⟩ | tauto | simp_all
  · simp only [rubi1224r56Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "f" * t) ^ k * (env "d" + -1 * env "e" * t ^ 2) * (env "a" + env "c" * t ^ 4) ^ (q - 1)) t := by
      convert hΦ1 using 1
      simp [eval, hkm, e3, e4, e5, toInt?_two, toInt?_four]
      try ring
    have hΦ2' : HasDerivAt (Φ "I2") ((env "f" * t) ^ (k + 4) * (env "a" + env "c" * t ^ 4) ^ (q - 1) * (env "d" + env "e" * t ^ 2)⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, e6, e3, e4, e5, toInt?_two, toInt?_four, toInt?_neg_one]
      try ring
    have hEF : eval I (Function.update env "x" t) rubi1224r56Nondeg.body =
        (env "f" * t) ^ k * (env "a" + env "c" * t ^ 4) ^ q * (env "d" + env "e" * t ^ 2)⁻¹ := by
      simp [rubi1224r56Nondeg, eval, hkm, hkp, toInt?_two, toInt?_four, toInt?_neg_one]
    have hfun : (fun w => eval I (recEnv env (rubi1224r56Nondeg.integrals.map (·.1)) Φ "x" w) rubi1224r56Nondeg.result) =
        fun w => env "a" * (env "d" ^ 2)⁻¹ * Φ "I1" w + (env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2) * ((env "d" ^ 2 * env "f" ^ 4))⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi1224r56Nondeg, eval, recEnv, toInt?_neg_one, toInt?_two, toInt?_four]
      try ring
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have hYA : (env "a" + env "c" * t ^ 4) ^ q = (env "a" + env "c" * t ^ 4) ^ (q - 1) * (env "a" + env "c" * t ^ 4) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    have hFs : (env "f" * t) ^ (k + 4) = (env "f" * t) ^ k * (env "f" * t) ^ 4 := by
      rw [zpow_add₀ (mul_ne_zero hf0 ht.1)]; norm_cast
    rw [hYA, hFs]
    have hB : (env "d" + env "e" * t ^ 2) * (env "d" + env "e" * t ^ 2)⁻¹ = 1 := mul_inv_cancel₀ ht.2
    have hu1 : env "d" ^ 2 * (env "d" ^ 2)⁻¹ = 1 := mul_inv_cancel₀ hW1
    have hu2 : (env "d" ^ 2 * env "f" ^ 4) * ((env "d" ^ 2 * env "f" ^ 4))⁻¹ = 1 := mul_inv_cancel₀ hW2
    generalize (env "f" * t) ^ k = C
    generalize (env "a" + env "c" * t ^ 4) ^ (q - 1) = Y
    generalize (env "d" + env "e" * t ^ 2)⁻¹ = Bi at hB ⊢
    generalize (env "d" ^ 2)⁻¹ = u1 at hu1 ⊢
    generalize ((env "d" ^ 2 * env "f" ^ 4))⁻¹ = u2 at hu2 ⊢
    linear_combination (C * Y) * ((-(env "a") * u1 * (env "d" + -1 * env "e" * t ^ 2)) * hB +
      ((env "a" + env "c" * t ^ 4) * Bi - (env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2) * t ^ 4 * Bi * env "f" ^ 4 * u2) * hu1 +
      ((env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2) * t ^ 4 * Bi * u1) * hu2)

theorem rubi1224r56Nondeg_real : rubi1224r56Nondeg.Holds .real :=
  rubi1224r56Nondeg_holds Interp.real Interp.real_lt_rat

theorem rubi1224r56Nondeg_complex : rubi1224r56Nondeg.Holds .complex :=
  rubi1224r56Nondeg_holds Interp.complex Interp.complex_lt_rat

/-- **1.2.2.4 #57**: partial fractions in `x²` with the converted conditions. -/
theorem rubi1224r57Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi1224r57Nondeg.conditions rubi1224r57Nondeg.body rubi1224r57Nondeg.result rubi1224r57Nondeg.integrals := by
  intro env hc t hF
  have hW1 : (env "d" * env "e") ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "d") (.var "e")) (.int 0)) (by simp [rubi1224r57Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  have hW2 : ((env "d" * env "e") * env "f" ^ 2) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.pow (.var "f") (.int 2))) (.int 0)) (by simp [rubi1224r57Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two, toInt?_four] using h
  have hf0 : env "f" ≠ 0 := fun h => hW2 (by rw [h]; ring)
  have hgp := hc (.gt (.var "p") (.int 0)) (by simp [rubi1224r57Nondeg])
  have hgm := hc (.gt (.int 0) (.var "m")) (by simp [rubi1224r57Nondeg])
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1224r57Nondeg, Defined, eval, hkm] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1224r57Nondeg, Defined, eval, hkm, hkp] at h
  have hm : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hq1 : 0 < q := by
    simp only [Cond.Holds, Defined, eval, true_and] at hgp
    rw [hp] at hgp
    have h' : I.lt ((0 : ℚ) : 𝕜) ((q : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_zero]; simpa using hgp
    exact_mod_cast (hlt _ _).1 h'
  have hk0 : k < 0 := by
    simp only [Cond.Holds, Defined, eval, true_and] at hgm
    rw [hm] at hgm
    have h' : I.lt ((k : ℚ) : 𝕜) ((((0 : ℤ)) : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hgm
    have := (hlt _ _).1 h'
    have : k < 0 := by exact_mod_cast this
    omega
  have e3 : I.toInt? (env "p" + -1) = some (q - 1) := (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have e4 : I.toInt? (env "p" - 1) = some (q - 1) := (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have e5 : I.toInt? (env "p" + -1 * 1) = some (q - 1) := (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have e6 : I.toInt? (env "m" + 2) = some (k + 2) := (I.toInt?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1224r57Nondeg.body →
      w ≠ 0 ∧ (env "d" + env "e" * w ^ 2) ≠ 0 := by
    intro w h
    simp [rubi1224r57Nondeg, Defined, eval, hkm, hkp, toInt?_two, toInt?_four, toInt?_neg_one] at h
    constructor <;> tauto
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1224r57Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      obtain ⟨hw0, hB0⟩ := hD w hw
      simp [Defined, eval, hkm, e3, e4, e5, toInt?_two, toInt?_four, hf0, hw0]
      first | done | omega | tauto
    · filter_upwards [hF] with w hw
      obtain ⟨hw0, hB0⟩ := hD w hw
      simp [Defined, eval, e6, e3, e4, e5, toInt?_two, toInt?_four, toInt?_neg_one, hf0, hw0, hB0]
      first | done | omega | tauto
  · exact Eventually.of_forall fun w => by
      simp [rubi1224r57Nondeg, Defined, eval, recEnv, toInt?_neg_one, toInt?_two, toInt?_four]
      first | done | exact ⟨hW1, hW2⟩ | tauto | simp_all
  · simp only [rubi1224r57Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "f" * t) ^ k * (env "a" * env "e" + env "c" * env "d" * t ^ 2) * (env "a" + env "b" * t ^ 2 + env "c" * t ^ 4) ^ (q - 1)) t := by
      convert hΦ1 using 1
      simp [eval, hkm, e3, e4, e5, toInt?_two, toInt?_four]
      try ring
    have hΦ2' : HasDerivAt (Φ "I2") ((env "f" * t) ^ (k + 2) * (env "a" + env "b" * t ^ 2 + env "c" * t ^ 4) ^ (q - 1) * (env "d" + env "e" * t ^ 2)⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, e6, e3, e4, e5, toInt?_two, toInt?_four, toInt?_neg_one]
      try ring
    have hEF : eval I (Function.update env "x" t) rubi1224r57Nondeg.body =
        (env "f" * t) ^ k * (env "a" + env "b" * t ^ 2 + env "c" * t ^ 4) ^ q * (env "d" + env "e" * t ^ 2)⁻¹ := by
      simp [rubi1224r57Nondeg, eval, hkm, hkp, toInt?_two, toInt?_four, toInt?_neg_one]
    have hfun : (fun w => eval I (recEnv env (rubi1224r57Nondeg.integrals.map (·.1)) Φ "x" w) rubi1224r57Nondeg.result) =
        fun w => 1 * ((env "d" * env "e"))⁻¹ * Φ "I1" w + (-1 * (env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2)) * (((env "d" * env "e") * env "f" ^ 2))⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi1224r57Nondeg, eval, recEnv, toInt?_neg_one, toInt?_two, toInt?_four]
      try ring
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have hYA : (env "a" + env "b" * t ^ 2 + env "c" * t ^ 4) ^ q = (env "a" + env "b" * t ^ 2 + env "c" * t ^ 4) ^ (q - 1) * (env "a" + env "b" * t ^ 2 + env "c" * t ^ 4) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    have hFs : (env "f" * t) ^ (k + 2) = (env "f" * t) ^ k * (env "f" * t) ^ 2 := by
      rw [zpow_add₀ (mul_ne_zero hf0 ht.1)]; norm_cast
    rw [hYA, hFs]
    have hB : (env "d" + env "e" * t ^ 2) * (env "d" + env "e" * t ^ 2)⁻¹ = 1 := mul_inv_cancel₀ ht.2
    have hu1 : (env "d" * env "e") * ((env "d" * env "e"))⁻¹ = 1 := mul_inv_cancel₀ hW1
    have hu2 : ((env "d" * env "e") * env "f" ^ 2) * (((env "d" * env "e") * env "f" ^ 2))⁻¹ = 1 := mul_inv_cancel₀ hW2
    generalize (env "f" * t) ^ k = C
    generalize (env "a" + env "b" * t ^ 2 + env "c" * t ^ 4) ^ (q - 1) = Y
    generalize (env "d" + env "e" * t ^ 2)⁻¹ = Bi at hB ⊢
    generalize ((env "d" * env "e"))⁻¹ = u1 at hu1 ⊢
    generalize (((env "d" * env "e") * env "f" ^ 2))⁻¹ = u2 at hu2 ⊢
    linear_combination (C * Y) * ((-(1) * u1 * (env "a" * env "e" + env "c" * env "d" * t ^ 2)) * hB +
      ((env "a" + env "b" * t ^ 2 + env "c" * t ^ 4) * Bi - (-1 * (env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2)) * t ^ 2 * Bi * env "f" ^ 2 * u2) * hu1 +
      ((-1 * (env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2)) * t ^ 2 * Bi * u1) * hu2)

theorem rubi1224r57Nondeg_real : rubi1224r57Nondeg.Holds .real :=
  rubi1224r57Nondeg_holds Interp.real Interp.real_lt_rat

theorem rubi1224r57Nondeg_complex : rubi1224r57Nondeg.Holds .complex :=
  rubi1224r57Nondeg_holds Interp.complex Interp.complex_lt_rat

/-- **1.2.2.4 #58**: partial fractions in `x²` with the converted conditions. -/
theorem rubi1224r58Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi1224r58Nondeg.conditions rubi1224r58Nondeg.body rubi1224r58Nondeg.result rubi1224r58Nondeg.integrals := by
  intro env hc t hF
  have hW1 : (env "d" * env "e") ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "d") (.var "e")) (.int 0)) (by simp [rubi1224r58Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  have hW2 : ((env "d" * env "e") * env "f" ^ 2) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.pow (.var "f") (.int 2))) (.int 0)) (by simp [rubi1224r58Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two, toInt?_four] using h
  have hf0 : env "f" ≠ 0 := fun h => hW2 (by rw [h]; ring)
  have hgp := hc (.gt (.var "p") (.int 0)) (by simp [rubi1224r58Nondeg])
  have hgm := hc (.gt (.int 0) (.var "m")) (by simp [rubi1224r58Nondeg])
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1224r58Nondeg, Defined, eval, hkm] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1224r58Nondeg, Defined, eval, hkm, hkp] at h
  have hm : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hq1 : 0 < q := by
    simp only [Cond.Holds, Defined, eval, true_and] at hgp
    rw [hp] at hgp
    have h' : I.lt ((0 : ℚ) : 𝕜) ((q : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_zero]; simpa using hgp
    exact_mod_cast (hlt _ _).1 h'
  have hk0 : k < 0 := by
    simp only [Cond.Holds, Defined, eval, true_and] at hgm
    rw [hm] at hgm
    have h' : I.lt ((k : ℚ) : 𝕜) ((((0 : ℤ)) : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hgm
    have := (hlt _ _).1 h'
    have : k < 0 := by exact_mod_cast this
    omega
  have e3 : I.toInt? (env "p" + -1) = some (q - 1) := (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have e4 : I.toInt? (env "p" - 1) = some (q - 1) := (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have e5 : I.toInt? (env "p" + -1 * 1) = some (q - 1) := (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have e6 : I.toInt? (env "m" + 2) = some (k + 2) := (I.toInt?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1224r58Nondeg.body →
      w ≠ 0 ∧ (env "d" + env "e" * w ^ 2) ≠ 0 := by
    intro w h
    simp [rubi1224r58Nondeg, Defined, eval, hkm, hkp, toInt?_two, toInt?_four, toInt?_neg_one] at h
    constructor <;> tauto
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1224r58Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      obtain ⟨hw0, hB0⟩ := hD w hw
      simp [Defined, eval, hkm, e3, e4, e5, toInt?_two, toInt?_four, hf0, hw0]
      first | done | omega | tauto
    · filter_upwards [hF] with w hw
      obtain ⟨hw0, hB0⟩ := hD w hw
      simp [Defined, eval, e6, e3, e4, e5, toInt?_two, toInt?_four, toInt?_neg_one, hf0, hw0, hB0]
      first | done | omega | tauto
  · exact Eventually.of_forall fun w => by
      simp [rubi1224r58Nondeg, Defined, eval, recEnv, toInt?_neg_one, toInt?_two, toInt?_four]
      first | done | exact ⟨hW1, hW2⟩ | tauto | simp_all
  · simp only [rubi1224r58Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "f" * t) ^ k * (env "a" * env "e" + env "c" * env "d" * t ^ 2) * (env "a" + env "c" * t ^ 4) ^ (q - 1)) t := by
      convert hΦ1 using 1
      simp [eval, hkm, e3, e4, e5, toInt?_two, toInt?_four]
      try ring
    have hΦ2' : HasDerivAt (Φ "I2") ((env "f" * t) ^ (k + 2) * (env "a" + env "c" * t ^ 4) ^ (q - 1) * (env "d" + env "e" * t ^ 2)⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, e6, e3, e4, e5, toInt?_two, toInt?_four, toInt?_neg_one]
      try ring
    have hEF : eval I (Function.update env "x" t) rubi1224r58Nondeg.body =
        (env "f" * t) ^ k * (env "a" + env "c" * t ^ 4) ^ q * (env "d" + env "e" * t ^ 2)⁻¹ := by
      simp [rubi1224r58Nondeg, eval, hkm, hkp, toInt?_two, toInt?_four, toInt?_neg_one]
    have hfun : (fun w => eval I (recEnv env (rubi1224r58Nondeg.integrals.map (·.1)) Φ "x" w) rubi1224r58Nondeg.result) =
        fun w => 1 * ((env "d" * env "e"))⁻¹ * Φ "I1" w + (-1 * (env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2)) * (((env "d" * env "e") * env "f" ^ 2))⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi1224r58Nondeg, eval, recEnv, toInt?_neg_one, toInt?_two, toInt?_four]
      try ring
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have hYA : (env "a" + env "c" * t ^ 4) ^ q = (env "a" + env "c" * t ^ 4) ^ (q - 1) * (env "a" + env "c" * t ^ 4) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    have hFs : (env "f" * t) ^ (k + 2) = (env "f" * t) ^ k * (env "f" * t) ^ 2 := by
      rw [zpow_add₀ (mul_ne_zero hf0 ht.1)]; norm_cast
    rw [hYA, hFs]
    have hB : (env "d" + env "e" * t ^ 2) * (env "d" + env "e" * t ^ 2)⁻¹ = 1 := mul_inv_cancel₀ ht.2
    have hu1 : (env "d" * env "e") * ((env "d" * env "e"))⁻¹ = 1 := mul_inv_cancel₀ hW1
    have hu2 : ((env "d" * env "e") * env "f" ^ 2) * (((env "d" * env "e") * env "f" ^ 2))⁻¹ = 1 := mul_inv_cancel₀ hW2
    generalize (env "f" * t) ^ k = C
    generalize (env "a" + env "c" * t ^ 4) ^ (q - 1) = Y
    generalize (env "d" + env "e" * t ^ 2)⁻¹ = Bi at hB ⊢
    generalize ((env "d" * env "e"))⁻¹ = u1 at hu1 ⊢
    generalize (((env "d" * env "e") * env "f" ^ 2))⁻¹ = u2 at hu2 ⊢
    linear_combination (C * Y) * ((-(1) * u1 * (env "a" * env "e" + env "c" * env "d" * t ^ 2)) * hB +
      ((env "a" + env "c" * t ^ 4) * Bi - (-1 * (env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2)) * t ^ 2 * Bi * env "f" ^ 2 * u2) * hu1 +
      ((-1 * (env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2)) * t ^ 2 * Bi * u1) * hu2)

theorem rubi1224r58Nondeg_real : rubi1224r58Nondeg.Holds .real :=
  rubi1224r58Nondeg_holds Interp.real Interp.real_lt_rat

theorem rubi1224r58Nondeg_complex : rubi1224r58Nondeg.Holds .complex :=
  rubi1224r58Nondeg_holds Interp.complex Interp.complex_lt_rat

end Proofs

end OSR.IntegrationRec54
