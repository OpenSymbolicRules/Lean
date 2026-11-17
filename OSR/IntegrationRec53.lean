import OSR.IntegrationNum1

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, fifth batch

Proofs of strengthened variants first distributed unproved
(`OSR.IntegrationNum1`, which keeps their definitions): 1.2.1.6 #5 to #8 with
`a ≠ 0` and `c ≠ 0`, where the converted conditions make
`(g + h x) (d + e x + f x²)` equal to `(d g/a + f h x/c) (a + b x + c x²)`, and
1.2.1.6 #10 with `e ≠ 0` and `f ≠ 0`, where `c e² + a f² = 0` makes
`x (a + c x²)` equal to `(a/e + c x/f) (e x + f x²)`.  Proved
over ℝ and ℂ for every choice of antiderivatives of the residual integrand.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec53

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








/-- **1.2.1.6 #5** with `a ≠ 0` and `c ≠ 0`: `(g + h x) (d + e x + f x^2)` is `(d g/a + f h x/c) (a + b x + c x^2)`. -/
theorem rubi1216r5Nondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi1216r5Nondeg.conditions rubi1216r5Nondeg.body rubi1216r5Nondeg.result rubi1216r5Nondeg.integrals := by
  intro env hc t hF
  have ha : env "a" ≠ 0 := by
    have h := hc (.ne (.var "a") (.int 0)) (by simp [rubi1216r5Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hc0 : env "c" ≠ 0 := by
    have h := hc (.ne (.var "c") (.int 0)) (by simp [rubi1216r5Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have h1 : env "a"*env "h"^2 - env "b"*env "g"*env "h" + env "c"*env "g"^2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "g") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "g")) (.var "h"))) (.app2 .mul (.var "a") (.pow (.var "h") (.int 2)))) (.int 0)) (by simp [rubi1216r5Nondeg])
    simp [Cond.Holds, Defined, eval, toInt?_two] at h
    linear_combination h
  have h2 : env "a"^2*env "f"*env "h"^2 - env "a"*env "c"*env "e"*env "g"*env "h" + env "c"^2*env "d"*env "g"^2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.pow (.var "g") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "c")) (.var "e")) (.var "g")) (.var "h"))) (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.var "f")) (.pow (.var "h") (.int 2)))) (.int 0)) (by simp [rubi1216r5Nondeg])
    simp [Cond.Holds, Defined, eval, toInt?_two] at h
    linear_combination h
  have hai : env "a" * (env "a")⁻¹ = 1 := mul_inv_cancel₀ ha
  have hci : env "c" * (env "c")⁻¹ = 1 := mul_inv_cancel₀ hc0
  have hQ : ∀ w : 𝕜, (env "g" + env "h"*w) * (env "d" + env "e"*w + env "f"*w^2) = (env "d" * env "g" * (env "a")⁻¹ + env "f" * env "h" * w * (env "c")⁻¹) * (env "a" + env "b"*w + env "c"*w^2) := fun w => by
    by_cases hh : env "h" = 0
    · have hg2 : env "c" * env "g" ^ 2 = 0 := by rw [hh] at h1; linear_combination h1
      have hg : env "g" = 0 := by simpa [hc0] using hg2
      rw [hh, hg]; ring
    · have hK : env "a" * env "c" * (env "a" * env "h" ^ 2) ≠ 0 :=
        mul_ne_zero (mul_ne_zero ha hc0) (mul_ne_zero ha (pow_ne_zero 2 hh))
      have hE : env "a" * env "c" * (env "a" * env "h" ^ 2) * ((env "g" + env "h"*w) * (env "d" + env "e"*w + env "f"*w^2) - (env "d" * env "g" * (env "a")⁻¹ + env "f" * env "h" * w * (env "c")⁻¹) * (env "a" + env "b"*w + env "c"*w^2)) = 0 := by
        linear_combination (env "a"*env "c"*env "d"*env "h"*w + w^2*(env "a"*env "c"*env "e"*env "h" - env "c"^2*env "d"*env "g")) * h1 + (-env "a"*env "h"*w + w^2*(-env "b"*env "h" + env "c"*env "g")) * h2 + (-env "a"*env "c"*env "d"*env "g"*env "h"^2*(env "a" + env "b"*w + env "c"*w^2)) * hai + (-env "a"^2*env "f"*env "h"^3*w*(env "a" + env "b"*w + env "c"*w^2)) * hci
      exact sub_eq_zero.1 ((mul_eq_zero.1 hE).resolve_left hK)
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1216r5Nondeg, Defined, eval, hkm] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1216r5Nondeg, Defined, eval, hkm, hkp] at h
  have hm : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkmp : I.toInt? (env "m" + env "p") = some (k + q) :=
    (I.toInt?_eq _ _).2 (by rw [hm, hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1216r5Nondeg.body →
      (k < 0 → (env "g" + env "h"*w) ≠ 0) ∧ (q < 0 → (env "a" + env "b"*w + env "c"*w^2) ≠ 0) ∧ (k < 0 → (env "d" + env "e"*w + env "f"*w^2) ≠ 0) := by
    intro w h
    simp [rubi1216r5Nondeg, Defined, eval, hkm, hkp, toInt?_two] at h
    tauto
  have hR : ∀ w, Defined I (Function.update env "x" w) rubi1216r5Nondeg.body →
      (k < 0 → (env "d" * env "g" * (env "a")⁻¹ + env "f" * env "h" * w * (env "c")⁻¹) ≠ 0) ∧ (k + q < 0 → (env "a" + env "b"*w + env "c"*w^2) ≠ 0) := by
    intro w hw
    obtain ⟨h1', h2', h3'⟩ := hD w hw
    refine ⟨fun hk hQ0 => mul_ne_zero (h1' hk) (h3' hk) (by rw [hQ w, hQ0, zero_mul]), fun hkq hA0 => ?_⟩
    by_cases hq : q < 0
    · exact h2' hq hA0
    · exact mul_ne_zero (h1' (by omega)) (h3' (by omega)) (by rw [hQ w, hA0, mul_zero])
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1216r5Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hr1, hr2⟩ := hR w hw
    simp [Defined, eval, hkm, hkmp, toInt?_neg_one, toInt?_two, ha, hc0]
    first | exact ⟨hr1, hr2⟩ | exact ⟨hr2, hr1⟩ | tauto
  · exact Eventually.of_forall fun w => by simp [rubi1216r5Nondeg, Defined, eval, recEnv]
  · simp only [rubi1216r5Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (rubi1216r5Nondeg.integrals.map (·.1)) Φ "x" w) rubi1216r5Nondeg.result) =
        Φ "I1" := by
      funext w
      simp [rubi1216r5Nondeg, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    have hz : (env "a" + env "b"*t + env "c"*t^2) ≠ 0 ∨ k + q ≠ 0 ∨ k = 0 ∧ q = 0 := by
      by_cases hA0 : (env "a" + env "b"*t + env "c"*t^2) = 0
      · have hq : 0 ≤ q := by
          by_contra hq
          exact ht.2.1 (by omega) hA0
        have hk : 0 ≤ k := by
          by_contra hk
          exact mul_ne_zero (ht.1 (by omega)) (ht.2.2 (by omega)) (by rw [hQ t, hA0, mul_zero])
        by_cases hkq : k + q = 0
        · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
        · exact Or.inr (Or.inl hkq)
      · exact Or.inl hA0
    have e1 : (env "g" + env "h"*t) ^ k * (env "d" + env "e"*t + env "f"*t^2) ^ k = (env "d" * env "g" * (env "a")⁻¹ + env "f" * env "h" * t * (env "c")⁻¹) ^ k * (env "a" + env "b"*t + env "c"*t^2) ^ k := by
      rw [← mul_zpow, ← mul_zpow, hQ t]
    have e2 : (env "a" + env "b"*t + env "c"*t^2) ^ (k + q) = (env "a" + env "b"*t + env "c"*t^2) ^ k * (env "a" + env "b"*t + env "c"*t^2) ^ q := zpow_add' hz
    simp [rubi1216r5Nondeg, eval, hkm, hkp, hkmp, toInt?_neg_one, toInt?_two]
    rw [e2]
    linear_combination (-(env "a" + env "b"*t + env "c"*t^2) ^ q) * e1

theorem rubi1216r5Nondeg_real : rubi1216r5Nondeg.Holds .real :=
  rubi1216r5Nondeg_holds Interp.real

theorem rubi1216r5Nondeg_complex : rubi1216r5Nondeg.Holds .complex :=
  rubi1216r5Nondeg_holds Interp.complex

/-- **1.2.1.6 #6** with `a ≠ 0` and `c ≠ 0`: `(g + h x) (d + e x + f x^2)` is `(d g/a + f h x/c) (a + c x^2)`. -/
theorem rubi1216r6Nondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi1216r6Nondeg.conditions rubi1216r6Nondeg.body rubi1216r6Nondeg.result rubi1216r6Nondeg.integrals := by
  intro env hc t hF
  have ha : env "a" ≠ 0 := by
    have h := hc (.ne (.var "a") (.int 0)) (by simp [rubi1216r6Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hc0 : env "c" ≠ 0 := by
    have h := hc (.ne (.var "c") (.int 0)) (by simp [rubi1216r6Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have h1 : env "a"*env "h"^2 + env "c"*env "g"^2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "g") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "h") (.int 2)))) (.int 0)) (by simp [rubi1216r6Nondeg])
    simp [Cond.Holds, Defined, eval, toInt?_two] at h
    linear_combination h
  have h2 : env "a"^2*env "f"*env "h"^2 - env "a"*env "c"*env "e"*env "g"*env "h" + env "c"^2*env "d"*env "g"^2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.pow (.var "g") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "c")) (.var "e")) (.var "g")) (.var "h"))) (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.var "f")) (.pow (.var "h") (.int 2)))) (.int 0)) (by simp [rubi1216r6Nondeg])
    simp [Cond.Holds, Defined, eval, toInt?_two] at h
    linear_combination h
  have hai : env "a" * (env "a")⁻¹ = 1 := mul_inv_cancel₀ ha
  have hci : env "c" * (env "c")⁻¹ = 1 := mul_inv_cancel₀ hc0
  have hQ : ∀ w : 𝕜, (env "g" + env "h"*w) * (env "d" + env "e"*w + env "f"*w^2) = (env "d" * env "g" * (env "a")⁻¹ + env "f" * env "h" * w * (env "c")⁻¹) * (env "a" + env "c"*w^2) := fun w => by
    by_cases hh : env "h" = 0
    · have hg2 : env "c" * env "g" ^ 2 = 0 := by rw [hh] at h1; linear_combination h1
      have hg : env "g" = 0 := by simpa [hc0] using hg2
      rw [hh, hg]; ring
    · have hK : env "a" * env "c" * (env "a" * env "h" ^ 2) ≠ 0 :=
        mul_ne_zero (mul_ne_zero ha hc0) (mul_ne_zero ha (pow_ne_zero 2 hh))
      have hE : env "a" * env "c" * (env "a" * env "h" ^ 2) * ((env "g" + env "h"*w) * (env "d" + env "e"*w + env "f"*w^2) - (env "d" * env "g" * (env "a")⁻¹ + env "f" * env "h" * w * (env "c")⁻¹) * (env "a" + env "c"*w^2)) = 0 := by
        linear_combination (env "a"*env "c"*env "d"*env "h"*w + w^2*(env "a"*env "c"*env "e"*env "h" - env "c"^2*env "d"*env "g")) * h1 + (-env "a"*env "h"*w + env "c"*env "g"*w^2) * h2 + (-env "a"*env "c"*env "d"*env "g"*env "h"^2*(env "a" + env "c"*w^2)) * hai + (-env "a"^2*env "f"*env "h"^3*w*(env "a" + env "c"*w^2)) * hci
      exact sub_eq_zero.1 ((mul_eq_zero.1 hE).resolve_left hK)
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1216r6Nondeg, Defined, eval, hkm] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1216r6Nondeg, Defined, eval, hkm, hkp] at h
  have hm : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkmp : I.toInt? (env "m" + env "p") = some (k + q) :=
    (I.toInt?_eq _ _).2 (by rw [hm, hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1216r6Nondeg.body →
      (k < 0 → (env "g" + env "h"*w) ≠ 0) ∧ (q < 0 → (env "a" + env "c"*w^2) ≠ 0) ∧ (k < 0 → (env "d" + env "e"*w + env "f"*w^2) ≠ 0) := by
    intro w h
    simp [rubi1216r6Nondeg, Defined, eval, hkm, hkp, toInt?_two] at h
    tauto
  have hR : ∀ w, Defined I (Function.update env "x" w) rubi1216r6Nondeg.body →
      (k < 0 → (env "d" * env "g" * (env "a")⁻¹ + env "f" * env "h" * w * (env "c")⁻¹) ≠ 0) ∧ (k + q < 0 → (env "a" + env "c"*w^2) ≠ 0) := by
    intro w hw
    obtain ⟨h1', h2', h3'⟩ := hD w hw
    refine ⟨fun hk hQ0 => mul_ne_zero (h1' hk) (h3' hk) (by rw [hQ w, hQ0, zero_mul]), fun hkq hA0 => ?_⟩
    by_cases hq : q < 0
    · exact h2' hq hA0
    · exact mul_ne_zero (h1' (by omega)) (h3' (by omega)) (by rw [hQ w, hA0, mul_zero])
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1216r6Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hr1, hr2⟩ := hR w hw
    simp [Defined, eval, hkm, hkmp, toInt?_neg_one, toInt?_two, ha, hc0]
    first | exact ⟨hr1, hr2⟩ | exact ⟨hr2, hr1⟩ | tauto
  · exact Eventually.of_forall fun w => by simp [rubi1216r6Nondeg, Defined, eval, recEnv]
  · simp only [rubi1216r6Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (rubi1216r6Nondeg.integrals.map (·.1)) Φ "x" w) rubi1216r6Nondeg.result) =
        Φ "I1" := by
      funext w
      simp [rubi1216r6Nondeg, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    have hz : (env "a" + env "c"*t^2) ≠ 0 ∨ k + q ≠ 0 ∨ k = 0 ∧ q = 0 := by
      by_cases hA0 : (env "a" + env "c"*t^2) = 0
      · have hq : 0 ≤ q := by
          by_contra hq
          exact ht.2.1 (by omega) hA0
        have hk : 0 ≤ k := by
          by_contra hk
          exact mul_ne_zero (ht.1 (by omega)) (ht.2.2 (by omega)) (by rw [hQ t, hA0, mul_zero])
        by_cases hkq : k + q = 0
        · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
        · exact Or.inr (Or.inl hkq)
      · exact Or.inl hA0
    have e1 : (env "g" + env "h"*t) ^ k * (env "d" + env "e"*t + env "f"*t^2) ^ k = (env "d" * env "g" * (env "a")⁻¹ + env "f" * env "h" * t * (env "c")⁻¹) ^ k * (env "a" + env "c"*t^2) ^ k := by
      rw [← mul_zpow, ← mul_zpow, hQ t]
    have e2 : (env "a" + env "c"*t^2) ^ (k + q) = (env "a" + env "c"*t^2) ^ k * (env "a" + env "c"*t^2) ^ q := zpow_add' hz
    simp [rubi1216r6Nondeg, eval, hkm, hkp, hkmp, toInt?_neg_one, toInt?_two]
    rw [e2]
    linear_combination (-(env "a" + env "c"*t^2) ^ q) * e1

theorem rubi1216r6Nondeg_real : rubi1216r6Nondeg.Holds .real :=
  rubi1216r6Nondeg_holds Interp.real

theorem rubi1216r6Nondeg_complex : rubi1216r6Nondeg.Holds .complex :=
  rubi1216r6Nondeg_holds Interp.complex

/-- **1.2.1.6 #7** with `a ≠ 0` and `c ≠ 0`: `(g + h x) (d + f x^2)` is `(d g/a + f h x/c) (a + b x + c x^2)`. -/
theorem rubi1216r7Nondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi1216r7Nondeg.conditions rubi1216r7Nondeg.body rubi1216r7Nondeg.result rubi1216r7Nondeg.integrals := by
  intro env hc t hF
  have ha : env "a" ≠ 0 := by
    have h := hc (.ne (.var "a") (.int 0)) (by simp [rubi1216r7Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hc0 : env "c" ≠ 0 := by
    have h := hc (.ne (.var "c") (.int 0)) (by simp [rubi1216r7Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have h1 : env "a"*env "h"^2 - env "b"*env "g"*env "h" + env "c"*env "g"^2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "g") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "g")) (.var "h"))) (.app2 .mul (.var "a") (.pow (.var "h") (.int 2)))) (.int 0)) (by simp [rubi1216r7Nondeg])
    simp [Cond.Holds, Defined, eval, toInt?_two] at h
    linear_combination h
  have h2 : env "a"^2*env "f"*env "h"^2 + env "c"^2*env "d"*env "g"^2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.pow (.var "g") (.int 2))) (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.var "f")) (.pow (.var "h") (.int 2)))) (.int 0)) (by simp [rubi1216r7Nondeg])
    simp [Cond.Holds, Defined, eval, toInt?_two] at h
    linear_combination h
  have hai : env "a" * (env "a")⁻¹ = 1 := mul_inv_cancel₀ ha
  have hci : env "c" * (env "c")⁻¹ = 1 := mul_inv_cancel₀ hc0
  have hQ : ∀ w : 𝕜, (env "g" + env "h"*w) * (env "d" + env "f"*w^2) = (env "d" * env "g" * (env "a")⁻¹ + env "f" * env "h" * w * (env "c")⁻¹) * (env "a" + env "b"*w + env "c"*w^2) := fun w => by
    by_cases hh : env "h" = 0
    · have hg2 : env "c" * env "g" ^ 2 = 0 := by rw [hh] at h1; linear_combination h1
      have hg : env "g" = 0 := by simpa [hc0] using hg2
      rw [hh, hg]; ring
    · have hK : env "a" * env "c" * (env "a" * env "h" ^ 2) ≠ 0 :=
        mul_ne_zero (mul_ne_zero ha hc0) (mul_ne_zero ha (pow_ne_zero 2 hh))
      have hE : env "a" * env "c" * (env "a" * env "h" ^ 2) * ((env "g" + env "h"*w) * (env "d" + env "f"*w^2) - (env "d" * env "g" * (env "a")⁻¹ + env "f" * env "h" * w * (env "c")⁻¹) * (env "a" + env "b"*w + env "c"*w^2)) = 0 := by
        linear_combination (env "a"*env "c"*env "d"*env "h"*w - env "c"^2*env "d"*env "g"*w^2) * h1 + (-env "a"*env "h"*w + w^2*(-env "b"*env "h" + env "c"*env "g")) * h2 + (-env "a"*env "c"*env "d"*env "g"*env "h"^2*(env "a" + env "b"*w + env "c"*w^2)) * hai + (-env "a"^2*env "f"*env "h"^3*w*(env "a" + env "b"*w + env "c"*w^2)) * hci
      exact sub_eq_zero.1 ((mul_eq_zero.1 hE).resolve_left hK)
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1216r7Nondeg, Defined, eval, hkm] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1216r7Nondeg, Defined, eval, hkm, hkp] at h
  have hm : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkmp : I.toInt? (env "m" + env "p") = some (k + q) :=
    (I.toInt?_eq _ _).2 (by rw [hm, hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1216r7Nondeg.body →
      (k < 0 → (env "g" + env "h"*w) ≠ 0) ∧ (q < 0 → (env "a" + env "b"*w + env "c"*w^2) ≠ 0) ∧ (k < 0 → (env "d" + env "f"*w^2) ≠ 0) := by
    intro w h
    simp [rubi1216r7Nondeg, Defined, eval, hkm, hkp, toInt?_two] at h
    tauto
  have hR : ∀ w, Defined I (Function.update env "x" w) rubi1216r7Nondeg.body →
      (k < 0 → (env "d" * env "g" * (env "a")⁻¹ + env "f" * env "h" * w * (env "c")⁻¹) ≠ 0) ∧ (k + q < 0 → (env "a" + env "b"*w + env "c"*w^2) ≠ 0) := by
    intro w hw
    obtain ⟨h1', h2', h3'⟩ := hD w hw
    refine ⟨fun hk hQ0 => mul_ne_zero (h1' hk) (h3' hk) (by rw [hQ w, hQ0, zero_mul]), fun hkq hA0 => ?_⟩
    by_cases hq : q < 0
    · exact h2' hq hA0
    · exact mul_ne_zero (h1' (by omega)) (h3' (by omega)) (by rw [hQ w, hA0, mul_zero])
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1216r7Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hr1, hr2⟩ := hR w hw
    simp [Defined, eval, hkm, hkmp, toInt?_neg_one, toInt?_two, ha, hc0]
    first | exact ⟨hr1, hr2⟩ | exact ⟨hr2, hr1⟩ | tauto
  · exact Eventually.of_forall fun w => by simp [rubi1216r7Nondeg, Defined, eval, recEnv]
  · simp only [rubi1216r7Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (rubi1216r7Nondeg.integrals.map (·.1)) Φ "x" w) rubi1216r7Nondeg.result) =
        Φ "I1" := by
      funext w
      simp [rubi1216r7Nondeg, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    have hz : (env "a" + env "b"*t + env "c"*t^2) ≠ 0 ∨ k + q ≠ 0 ∨ k = 0 ∧ q = 0 := by
      by_cases hA0 : (env "a" + env "b"*t + env "c"*t^2) = 0
      · have hq : 0 ≤ q := by
          by_contra hq
          exact ht.2.1 (by omega) hA0
        have hk : 0 ≤ k := by
          by_contra hk
          exact mul_ne_zero (ht.1 (by omega)) (ht.2.2 (by omega)) (by rw [hQ t, hA0, mul_zero])
        by_cases hkq : k + q = 0
        · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
        · exact Or.inr (Or.inl hkq)
      · exact Or.inl hA0
    have e1 : (env "g" + env "h"*t) ^ k * (env "d" + env "f"*t^2) ^ k = (env "d" * env "g" * (env "a")⁻¹ + env "f" * env "h" * t * (env "c")⁻¹) ^ k * (env "a" + env "b"*t + env "c"*t^2) ^ k := by
      rw [← mul_zpow, ← mul_zpow, hQ t]
    have e2 : (env "a" + env "b"*t + env "c"*t^2) ^ (k + q) = (env "a" + env "b"*t + env "c"*t^2) ^ k * (env "a" + env "b"*t + env "c"*t^2) ^ q := zpow_add' hz
    simp [rubi1216r7Nondeg, eval, hkm, hkp, hkmp, toInt?_neg_one, toInt?_two]
    rw [e2]
    linear_combination (-(env "a" + env "b"*t + env "c"*t^2) ^ q) * e1

theorem rubi1216r7Nondeg_real : rubi1216r7Nondeg.Holds .real :=
  rubi1216r7Nondeg_holds Interp.real

theorem rubi1216r7Nondeg_complex : rubi1216r7Nondeg.Holds .complex :=
  rubi1216r7Nondeg_holds Interp.complex

/-- **1.2.1.6 #8** with `a ≠ 0` and `c ≠ 0`: `(g + h x) (d + f x^2)` is `(d g/a + f h x/c) (a + c x^2)`. -/
theorem rubi1216r8Nondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi1216r8Nondeg.conditions rubi1216r8Nondeg.body rubi1216r8Nondeg.result rubi1216r8Nondeg.integrals := by
  intro env hc t hF
  have ha : env "a" ≠ 0 := by
    have h := hc (.ne (.var "a") (.int 0)) (by simp [rubi1216r8Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hc0 : env "c" ≠ 0 := by
    have h := hc (.ne (.var "c") (.int 0)) (by simp [rubi1216r8Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have h1 : env "a"*env "h"^2 + env "c"*env "g"^2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "g") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "h") (.int 2)))) (.int 0)) (by simp [rubi1216r8Nondeg])
    simp [Cond.Holds, Defined, eval, toInt?_two] at h
    linear_combination h
  have h2 : env "a"^2*env "f"*env "h"^2 + env "c"^2*env "d"*env "g"^2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.pow (.var "g") (.int 2))) (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.var "f")) (.pow (.var "h") (.int 2)))) (.int 0)) (by simp [rubi1216r8Nondeg])
    simp [Cond.Holds, Defined, eval, toInt?_two] at h
    linear_combination h
  have hai : env "a" * (env "a")⁻¹ = 1 := mul_inv_cancel₀ ha
  have hci : env "c" * (env "c")⁻¹ = 1 := mul_inv_cancel₀ hc0
  have hQ : ∀ w : 𝕜, (env "g" + env "h"*w) * (env "d" + env "f"*w^2) = (env "d" * env "g" * (env "a")⁻¹ + env "f" * env "h" * w * (env "c")⁻¹) * (env "a" + env "c"*w^2) := fun w => by
    by_cases hh : env "h" = 0
    · have hg2 : env "c" * env "g" ^ 2 = 0 := by rw [hh] at h1; linear_combination h1
      have hg : env "g" = 0 := by simpa [hc0] using hg2
      rw [hh, hg]; ring
    · have hK : env "a" * env "c" * (env "a" * env "h" ^ 2) ≠ 0 :=
        mul_ne_zero (mul_ne_zero ha hc0) (mul_ne_zero ha (pow_ne_zero 2 hh))
      have hE : env "a" * env "c" * (env "a" * env "h" ^ 2) * ((env "g" + env "h"*w) * (env "d" + env "f"*w^2) - (env "d" * env "g" * (env "a")⁻¹ + env "f" * env "h" * w * (env "c")⁻¹) * (env "a" + env "c"*w^2)) = 0 := by
        linear_combination (env "a"*env "c"*env "d"*env "h"*w - env "c"^2*env "d"*env "g"*w^2) * h1 + (-env "a"*env "h"*w + env "c"*env "g"*w^2) * h2 + (-env "a"*env "c"*env "d"*env "g"*env "h"^2*(env "a" + env "c"*w^2)) * hai + (-env "a"^2*env "f"*env "h"^3*w*(env "a" + env "c"*w^2)) * hci
      exact sub_eq_zero.1 ((mul_eq_zero.1 hE).resolve_left hK)
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1216r8Nondeg, Defined, eval, hkm] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1216r8Nondeg, Defined, eval, hkm, hkp] at h
  have hm : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkmp : I.toInt? (env "m" + env "p") = some (k + q) :=
    (I.toInt?_eq _ _).2 (by rw [hm, hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1216r8Nondeg.body →
      (k < 0 → (env "g" + env "h"*w) ≠ 0) ∧ (q < 0 → (env "a" + env "c"*w^2) ≠ 0) ∧ (k < 0 → (env "d" + env "f"*w^2) ≠ 0) := by
    intro w h
    simp [rubi1216r8Nondeg, Defined, eval, hkm, hkp, toInt?_two] at h
    tauto
  have hR : ∀ w, Defined I (Function.update env "x" w) rubi1216r8Nondeg.body →
      (k < 0 → (env "d" * env "g" * (env "a")⁻¹ + env "f" * env "h" * w * (env "c")⁻¹) ≠ 0) ∧ (k + q < 0 → (env "a" + env "c"*w^2) ≠ 0) := by
    intro w hw
    obtain ⟨h1', h2', h3'⟩ := hD w hw
    refine ⟨fun hk hQ0 => mul_ne_zero (h1' hk) (h3' hk) (by rw [hQ w, hQ0, zero_mul]), fun hkq hA0 => ?_⟩
    by_cases hq : q < 0
    · exact h2' hq hA0
    · exact mul_ne_zero (h1' (by omega)) (h3' (by omega)) (by rw [hQ w, hA0, mul_zero])
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1216r8Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hr1, hr2⟩ := hR w hw
    simp [Defined, eval, hkm, hkmp, toInt?_neg_one, toInt?_two, ha, hc0]
    first | exact ⟨hr1, hr2⟩ | exact ⟨hr2, hr1⟩ | tauto
  · exact Eventually.of_forall fun w => by simp [rubi1216r8Nondeg, Defined, eval, recEnv]
  · simp only [rubi1216r8Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (rubi1216r8Nondeg.integrals.map (·.1)) Φ "x" w) rubi1216r8Nondeg.result) =
        Φ "I1" := by
      funext w
      simp [rubi1216r8Nondeg, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    have hz : (env "a" + env "c"*t^2) ≠ 0 ∨ k + q ≠ 0 ∨ k = 0 ∧ q = 0 := by
      by_cases hA0 : (env "a" + env "c"*t^2) = 0
      · have hq : 0 ≤ q := by
          by_contra hq
          exact ht.2.1 (by omega) hA0
        have hk : 0 ≤ k := by
          by_contra hk
          exact mul_ne_zero (ht.1 (by omega)) (ht.2.2 (by omega)) (by rw [hQ t, hA0, mul_zero])
        by_cases hkq : k + q = 0
        · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
        · exact Or.inr (Or.inl hkq)
      · exact Or.inl hA0
    have e1 : (env "g" + env "h"*t) ^ k * (env "d" + env "f"*t^2) ^ k = (env "d" * env "g" * (env "a")⁻¹ + env "f" * env "h" * t * (env "c")⁻¹) ^ k * (env "a" + env "c"*t^2) ^ k := by
      rw [← mul_zpow, ← mul_zpow, hQ t]
    have e2 : (env "a" + env "c"*t^2) ^ (k + q) = (env "a" + env "c"*t^2) ^ k * (env "a" + env "c"*t^2) ^ q := zpow_add' hz
    simp [rubi1216r8Nondeg, eval, hkm, hkp, hkmp, toInt?_neg_one, toInt?_two]
    rw [e2]
    linear_combination (-(env "a" + env "c"*t^2) ^ q) * e1

theorem rubi1216r8Nondeg_real : rubi1216r8Nondeg.Holds .real :=
  rubi1216r8Nondeg_holds Interp.real

theorem rubi1216r8Nondeg_complex : rubi1216r8Nondeg.Holds .complex :=
  rubi1216r8Nondeg_holds Interp.complex

/-- **1.2.1.6 #10** with `e ≠ 0` and `f ≠ 0`: `x (a + c x²) = (a/e + c x/f) (e x + f x²)`. -/
theorem rubi1216r10Nondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi1216r10Nondeg.conditions rubi1216r10Nondeg.body rubi1216r10Nondeg.result rubi1216r10Nondeg.integrals := by
  intro env hc t hF
  have he : env "e" ≠ 0 := by
    have h := hc (.ne (.var "e") (.int 0)) (by simp [rubi1216r10Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hf : env "f" ≠ 0 := by
    have h := hc (.ne (.var "f") (.int 0)) (by simp [rubi1216r10Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have h1 : env "c" * env "e" ^ 2 + env "a" * env "f" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "e") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "f") (.int 2)))) (.int 0)) (by simp [rubi1216r10Nondeg])
    simp [Cond.Holds, Defined, eval, toInt?_two] at h
    linear_combination h
  have hei : env "e" * (env "e")⁻¹ = 1 := mul_inv_cancel₀ he
  have hfi : env "f" * (env "f")⁻¹ = 1 := mul_inv_cancel₀ hf
  have hQ : ∀ w : 𝕜, w * (env "a" + env "c" * w ^ 2) = (env "a" * (env "e")⁻¹ + env "c" * (env "f")⁻¹ * w) * (env "e" * w + env "f" * w ^ 2) := fun w => by
    linear_combination (-w ^ 2 * (env "e")⁻¹ * (env "f")⁻¹) * h1 +
      (-env "a" * w + w ^ 2 * env "c" * env "e" * (env "f")⁻¹) * hei +
      (-env "c" * w ^ 3 + w ^ 2 * env "a" * env "f" * (env "e")⁻¹) * hfi
  rcases hkp : I.toInt? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1216r10Nondeg, Defined, eval, hkp] at h
  rcases hkq : I.toInt? (env "q") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1216r10Nondeg, Defined, eval, hkp, hkq] at h
  have hp : env "p" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hq' : env "q" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkq
  have hkpq : I.toInt? (env "p" + env "q") = some (k + q) :=
    (I.toInt?_eq _ _).2 (by rw [hp, hq']; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1216r10Nondeg.body →
      (k < 0 → w ≠ 0) ∧ (k < 0 → (env "a" + env "c" * w ^ 2) ≠ 0) ∧ (q < 0 → (env "e" * w + env "f" * w ^ 2) ≠ 0) := by
    intro w h
    simp [rubi1216r10Nondeg, Defined, eval, hkp, hkq, toInt?_two] at h
    tauto
  have hR : ∀ w, Defined I (Function.update env "x" w) rubi1216r10Nondeg.body →
      (k < 0 → (env "a" * (env "e")⁻¹ + env "c" * (env "f")⁻¹ * w) ≠ 0) ∧ (k + q < 0 → (env "e" * w + env "f" * w ^ 2) ≠ 0) := by
    intro w hw
    obtain ⟨h1', h2', h3'⟩ := hD w hw
    refine ⟨fun hk hQ0 => mul_ne_zero (h1' hk) (h2' hk) (by rw [hQ w, hQ0, zero_mul]), fun hkq hB0 => ?_⟩
    by_cases hq : q < 0
    · exact h3' hq hB0
    · exact mul_ne_zero (h1' (by omega)) (h2' (by omega)) (by rw [hQ w, hB0, mul_zero])
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1216r10Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hr1, hr2⟩ := hR w hw
    simp [Defined, eval, hkp, hkpq, toInt?_neg_one, toInt?_two, he, hf]
    first | exact ⟨hr1, hr2⟩ | exact ⟨hr2, hr1⟩ | tauto
  · exact Eventually.of_forall fun w => by simp [rubi1216r10Nondeg, Defined, eval, recEnv]
  · simp only [rubi1216r10Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (rubi1216r10Nondeg.integrals.map (·.1)) Φ "x" w) rubi1216r10Nondeg.result) =
        Φ "I1" := by
      funext w
      simp [rubi1216r10Nondeg, eval, recEnv]
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
    have e1 : t ^ k * (env "a" + env "c" * t ^ 2) ^ k = (env "a" * (env "e")⁻¹ + env "c" * (env "f")⁻¹ * t) ^ k * (env "e" * t + env "f" * t ^ 2) ^ k := by
      rw [← mul_zpow, ← mul_zpow, hQ t]
    have e2 : (env "e" * t + env "f" * t ^ 2) ^ (k + q) = (env "e" * t + env "f" * t ^ 2) ^ k * (env "e" * t + env "f" * t ^ 2) ^ q := zpow_add' hz
    simp [rubi1216r10Nondeg, eval, hkp, hkq, hkpq, toInt?_neg_one, toInt?_two]
    rw [e2]
    linear_combination (-(env "e" * t + env "f" * t ^ 2) ^ q) * e1

theorem rubi1216r10Nondeg_real : rubi1216r10Nondeg.Holds .real :=
  rubi1216r10Nondeg_holds Interp.real

theorem rubi1216r10Nondeg_complex : rubi1216r10Nondeg.Holds .complex :=
  rubi1216r10Nondeg_holds Interp.complex

end Proofs

end OSR.IntegrationRec53
