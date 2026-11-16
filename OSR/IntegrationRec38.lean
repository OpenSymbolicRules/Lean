import OSR.IntegrationRec37

/-!
# Integration (RUBI): corrected variants, second batch

Strengthened variants (Specification V1-R-005e) of the refuted RUBI rules
1.1.1.2 #1, 1.1.3.2 #3, 1.1.3.1 #3 and 1.1.3.2 #6, with a non-degeneracy
condition appended to the converted conditions.  Proved over ℝ
and ℂ; the refutations of the rules as stated are kept.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec38

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 1.1.1.2 #1 when b (m + 2) ≠ 0 -/
def rubi1112r1Nondeg : CRule where
  id := "integration.rubi_1_1_1_2_r1_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.2 (a+b x)^m (c+d x)^n:1"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "m")) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "x")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "m") (.int 2))) (.int (-1))))
  independent := ["a", "b", "c", "d", "m"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "a") (.var "d")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.app2 .add (.var "m") (.int 2)))) (.int 0),
    .ne (.app2 .mul (.var "b") (.app2 .add (.var "m") (.int 2))) (.int 0)]
  priority := 7040
  description := "RUBI 1.1.1.2 #1 when b (m + 2) ≠ 0"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.2 (a+b x)^m (c+d x)^n:1" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.2 (a+b x)^m (c+d x)^n.m#1"

/-- RUBI 1.1.3.2 #3 when b n (p + 1) ≠ 0 -/
def rubi1132r3Nondeg : CRule where
  id := "integration.rubi_1_1_3_2_r3_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.2 (c x)^m (a+b x^n)^p:3"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")))
  result := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1))))
  independent := ["a", "b", "m", "n", "p"]
  conditions := [.eq (.var "m") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))),
    .ne (.var "p") (.int (-1)),
    .ne (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 0)]
  priority := 7050
  description := "RUBI 1.1.3.2 #3 when b n (p + 1) ≠ 0"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.2 (c x)^m (a+b x^n)^p:3" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.2 (c x)^m (a+b x^n)^p.m#3"

/-- RUBI 1.1.3.1 #3 when a ≠ 0 -/
def rubi1131r3Nondeg : CRule where
  id := "integration.rubi_1_1_3_1_r3_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.1 (a+b x^n)^p:3"
  shape := .antideriv; x := "x"
  body := (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))
  result := (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.var "a") (.int (-1))))
  independent := ["a", "b", "n", "p"]
  conditions := [.eq (.app2 .add (.app2 .add (.app2 .mul (.int 1) (.pow (.var "n") (.int (-1)))) (.var "p")) (.int 1)) (.int 0),
    .ne (.var "a") (.int 0)]
  priority := 7060
  description := "RUBI 1.1.3.1 #3 when a ≠ 0"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.1 (a+b x^n)^p:3" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.1 (a+b x^n)^p.m#3"

/-- RUBI 1.1.3.2 #6 when a c (m + 1) ≠ 0 -/
def rubi1132r6Nondeg : CRule where
  id := "integration.rubi_1_1_3_2_r6_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.2 (c x)^m (a+b x^n)^p:6"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "c") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "c") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.app2 .add (.var "m") (.int 1))) (.int (-1))))
  independent := ["a", "b", "c", "m", "n", "p"]
  conditions := [.eq (.app2 .add (.app2 .add (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.pow (.var "n") (.int (-1)))) (.var "p")) (.int 1)) (.int 0),
    .ne (.var "m") (.int (-1)),
    .ne (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.app2 .add (.var "m") (.int 1))) (.int 0)]
  priority := 7070
  description := "RUBI 1.1.3.2 #6 when a c (m + 1) ≠ 0"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.2 (c x)^m (a+b x^n)^p:6" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.2 (c x)^m (a+b x^n)^p.m#6"

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

/-- **1.1.1.2 #1** with `b (m + 2) ≠ 0`. -/
theorem rubi1112r1Nondeg_holds (I : Interp 𝕜) :
    AntiderivHoldsUnder I "x" rubi1112r1Nondeg.conditions rubi1112r1Nondeg.body
      rubi1112r1Nondeg.result := by
  intro env hc t hF
  have hbm : env "b" * (env "m" + 2) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "b") (.app2 .add (.var "m") (.int 2))) (.int 0))
      (by simp [rubi1112r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have heq : env "a" * env "d" + -1 * env "b" * env "c" * (env "m" + 2) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "a") (.var "d")) (.app2 .mul (.app2 .mul
      (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.app2 .add (.var "m") (.int 2)))) (.int 0))
      (by simp [rubi1112r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hk : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1112r1Nondeg, Defined, eval, hk] at h
  have hmk : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk
  have hk1 : I.toInt? (env "m" + 1) = some (k + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hmk]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1112r1Nondeg.body ↔
      (k < 0 → env "a" + env "b" * w ≠ 0) := by
    intro w
    simp [rubi1112r1Nondeg, Defined, eval, hk]
  have hDG : ∀ w, Defined I (Function.update env "x" w) rubi1112r1Nondeg.result ↔
      (k + 1 < 0 → env "a" + env "b" * w ≠ 0) := by
    intro w
    simp [rubi1112r1Nondeg, Defined, eval, hk1, toInt?_neg_one, hbm]
  have hE : ∀ w, eval I (Function.update env "x" w) rubi1112r1Nondeg.result =
      env "d" * w * (env "a" + env "b" * w) ^ (k + 1) * (env "b" * (env "m" + 2))⁻¹ := by
    intro w
    simp [rubi1112r1Nondeg, eval, hk1, toInt?_neg_one]
  have hEF : eval I (Function.update env "x" t) rubi1112r1Nondeg.body =
      (env "a" + env "b" * t) ^ k * (env "c" + env "d" * t) := by
    simp [rubi1112r1Nondeg, eval, hk]
  have ht := (hD t).1 hF.self_of_nhds
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    exact (hDG w).2 fun h => (hD w).1 hw (by omega)
  · have hne : env "a" + env "b" * t ≠ 0 ∨ 0 ≤ k + 1 := by
      by_cases h : k + 1 < 0
      · exact Or.inl (ht (by omega))
      · exact Or.inr (by omega)
    have hne0 : env "a" + env "b" * t ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (ht h)
      · exact Or.inr (by omega)
    rw [hEF, show (fun w => eval I (Function.update env "x" w) rubi1112r1Nondeg.result) =
        fun w => env "d" * w * (env "a" + env "b" * w) ^ (k + 1) *
          (env "b" * (env "m" + 2))⁻¹ from funext hE]
    refine ((((hasDerivAt_id' t).const_mul (env "d")).mul (HasDerivAt.comp t
      (hasDerivAt_zpow (k + 1) _ hne)
      (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")))).mul_const _).congr_deriv ?_
    simp only [Function.comp_def]
    rw [add_sub_cancel_right, zpow_succ_of _ _ hne0]
    rw [hmk] at hbm heq ⊢
    generalize (env "a" + env "b" * t) ^ k = P
    push_cast
    rw [mul_inv_eq_iff_eq_mul₀ hbm]
    linear_combination P * heq

theorem rubi1112r1Nondeg_real : rubi1112r1Nondeg.Holds .real :=
  rubi1112r1Nondeg_holds Interp.real

theorem rubi1112r1Nondeg_complex : rubi1112r1Nondeg.Holds .complex :=
  rubi1112r1Nondeg_holds Interp.complex

/-- **1.1.3.2 #3** with `b n (p + 1) ≠ 0`. -/
theorem rubi1132r3Nondeg_holds (I : Interp 𝕜) :
    AntiderivHoldsUnder I "x" rubi1132r3Nondeg.conditions rubi1132r3Nondeg.body
      rubi1132r3Nondeg.result := by
  intro env hc t hF
  have hbn : env "b" * env "n" * (env "p" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p")
      (.int 1))) (.int 0)) (by simp [rubi1132r3Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hmn : env "m" = env "n" + -1 * 1 := by
    have h := hc (.eq (.var "m") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))
      (by simp [rubi1132r3Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1132r3Nondeg, Defined, eval, hkm] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1132r3Nondeg, Defined, eval, hkp] at h
  have hmk : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hpq : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkn : I.toInt? (env "n") = some (k + 1) :=
    (I.toInt?_eq _ _).2 (by rw [show env "n" = env "m" + 1 by rw [hmn]; ring, hmk]; push_cast; ring)
  have hkp1 : I.toInt? (env "p" + 1) = some (q + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hpq]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1132r3Nondeg.body →
      (k < 0 → w ≠ 0) ∧ (q < 0 → env "a" + env "b" * w ^ (k + 1) ≠ 0) := by
    intro w h
    simp [rubi1132r3Nondeg, Defined, eval, hkm, hkp, hkn] at h
    refine ⟨h.1, fun hq => ?_⟩
    have := h.2
    tauto
  have hDG : ∀ w, (k < 0 → w ≠ 0) → (q < 0 → env "a" + env "b" * w ^ (k + 1) ≠ 0) →
      Defined I (Function.update env "x" w) rubi1132r3Nondeg.result := by
    intro w h1 h2
    simp [rubi1132r3Nondeg, Defined, eval, hkn, hkp1, toInt?_neg_one, hbn]
    exact ⟨fun h => h1 (by omega), fun h => h2 (by omega)⟩
  have ht := hD t hF.self_of_nhds
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    exact hDG w (hD w hw).1 (hD w hw).2
  · have hE : ∀ w, eval I (Function.update env "x" w) rubi1132r3Nondeg.result =
        (env "a" + env "b" * w ^ (k + 1)) ^ (q + 1) * (env "b" * env "n" * (env "p" + 1))⁻¹ := by
      intro w
      simp [rubi1132r3Nondeg, eval, hkn, hkp1, toInt?_neg_one]
    have hEF : eval I (Function.update env "x" t) rubi1132r3Nondeg.body =
        t ^ k * (env "a" + env "b" * t ^ (k + 1)) ^ q := by
      simp [rubi1132r3Nondeg, eval, hkm, hkp, hkn]
    rw [hEF, show (fun w => eval I (Function.update env "x" w) rubi1132r3Nondeg.result) =
        fun w => (env "a" + env "b" * w ^ (k + 1)) ^ (q + 1) *
          (env "b" * env "n" * (env "p" + 1))⁻¹ from funext hE]
    have hx : t ≠ 0 ∨ 0 ≤ k + 1 := by
      by_cases h : k + 1 < 0
      · exact Or.inl (ht.1 (by omega))
      · exact Or.inr (by omega)
    have hu : env "a" + env "b" * t ^ (k + 1) ≠ 0 ∨ 0 ≤ q + 1 := by
      by_cases h : q + 1 < 0
      · exact Or.inl (ht.2 (by omega))
      · exact Or.inr (by omega)
    have hin : HasDerivAt (fun w => env "a" + env "b" * w ^ (k + 1))
        (env "b" * (((k + 1 : ℤ) : 𝕜) * t ^ (k + 1 - 1))) t :=
      ((hasDerivAt_zpow (k + 1) t hx).const_mul (env "b")).const_add (env "a")
    refine ((HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ hu) hin).mul_const _).congr_deriv ?_
    simp only [add_sub_cancel_right]
    have hn : env "n" = (k : 𝕜) + 1 := by
      rw [show env "n" = env "m" + 1 by rw [hmn]; ring, hmk]
    rw [hn, hpq] at hbn ⊢
    generalize t ^ k = X
    generalize (env "a" + env "b" * t ^ (k + 1)) ^ q = U
    push_cast
    rw [mul_inv_eq_iff_eq_mul₀ hbn]
    ring

theorem rubi1132r3Nondeg_real : rubi1132r3Nondeg.Holds .real :=
  rubi1132r3Nondeg_holds Interp.real

theorem rubi1132r3Nondeg_complex : rubi1132r3Nondeg.Holds .complex :=
  rubi1132r3Nondeg_holds Interp.complex

/-- **1.1.3.1 #3** with `a ≠ 0`. -/
theorem rubi1131r3Nondeg_holds (I : Interp 𝕜) :
    AntiderivHoldsUnder I "x" rubi1131r3Nondeg.conditions rubi1131r3Nondeg.body
      rubi1131r3Nondeg.result := by
  intro env hc t hF
  have ha : env "a" ≠ 0 := by
    have h := hc (.ne (.var "a") (.int 0)) (by simp [rubi1131r3Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have heq := hc (.eq (.app2 .add (.app2 .add (.app2 .mul (.int 1) (.pow (.var "n") (.int (-1))))
    (.var "p")) (.int 1)) (.int 0)) (by simp [rubi1131r3Nondeg])
  simp [Cond.Holds, Defined, eval, toInt?_neg_one] at heq
  rcases hkn : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1131r3Nondeg, Defined, eval, hkn] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1131r3Nondeg, Defined, eval, hkp] at h
  have hn : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hkn
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkp1 : I.toInt? (env "p" + 1) = some (q + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hj0 : (j : 𝕜) ≠ 0 := hn ▸ heq.1
  have hqj : ((q : 𝕜) + 1) * j = -1 := by
    have h2 := heq.2
    rw [hn, hp] at h2
    field_simp at h2
    linear_combination h2
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1131r3Nondeg.body →
      (j < 0 → w ≠ 0) ∧ (q < 0 → env "a" + env "b" * w ^ j ≠ 0) := by
    intro w h
    simp [rubi1131r3Nondeg, Defined, eval, hkn, hkp] at h
    tauto
  have hDG : ∀ w, (j < 0 → w ≠ 0) → (q < 0 → env "a" + env "b" * w ^ j ≠ 0) →
      Defined I (Function.update env "x" w) rubi1131r3Nondeg.result := by
    intro w h1 h2
    simp [rubi1131r3Nondeg, Defined, eval, hkn, hkp1, toInt?_neg_one, ha]
    exact ⟨fun h => h1 h, fun h => h2 (by omega)⟩
  have ht := hD t hF.self_of_nhds
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    exact hDG w (hD w hw).1 (hD w hw).2
  · have hE : ∀ w, eval I (Function.update env "x" w) rubi1131r3Nondeg.result =
        w * (env "a" + env "b" * w ^ j) ^ (q + 1) * (env "a")⁻¹ := by
      intro w
      simp [rubi1131r3Nondeg, eval, hkn, hkp1, toInt?_neg_one]
    have hEF : eval I (Function.update env "x" t) rubi1131r3Nondeg.body =
        (env "a" + env "b" * t ^ j) ^ q := by
      simp [rubi1131r3Nondeg, eval, hkn, hkp]
    rw [hEF, show (fun w => eval I (Function.update env "x" w) rubi1131r3Nondeg.result) =
        fun w => w * (env "a" + env "b" * w ^ j) ^ (q + 1) * (env "a")⁻¹ from funext hE]
    have hj : j ≠ 0 := fun h => hj0 (by rw [h]; simp)
    have hx : t ≠ 0 ∨ 0 ≤ j := by
      by_cases h : j < 0
      · exact Or.inl (ht.1 h)
      · exact Or.inr (by omega)
    have hx1 : t ≠ 0 ∨ 0 ≤ j - 1 := by
      by_cases h : j < 0
      · exact Or.inl (ht.1 h)
      · exact Or.inr (by omega)
    have hu : env "a" + env "b" * t ^ j ≠ 0 ∨ 0 ≤ q + 1 := by
      by_cases h : q + 1 < 0
      · exact Or.inl (ht.2 (by omega))
      · exact Or.inr (by omega)
    have hu0 : env "a" + env "b" * t ^ j ≠ 0 ∨ 0 ≤ q := by
      by_cases h : q < 0
      · exact Or.inl (ht.2 h)
      · exact Or.inr (by omega)
    have htj : t ^ j = t ^ (j - 1) * t := by
      rw [← zpow_succ_of _ _ hx1, sub_add_cancel]
    have hin : HasDerivAt (fun w => env "a" + env "b" * w ^ j)
        (env "b" * ((j : 𝕜) * t ^ (j - 1))) t :=
      ((hasDerivAt_zpow j t hx).const_mul (env "b")).const_add (env "a")
    refine (((hasDerivAt_id' t).mul (HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ hu)
      hin)).mul_const _).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    rw [zpow_succ_of _ _ hu0]
    generalize (env "a" + env "b" * t ^ j) ^ q = V
    rw [htj]
    generalize t ^ (j - 1) = T
    push_cast
    rw [mul_inv_eq_iff_eq_mul₀ ha]
    linear_combination (V * env "b" * T * t) * hqj

theorem rubi1131r3Nondeg_real : rubi1131r3Nondeg.Holds .real :=
  rubi1131r3Nondeg_holds Interp.real

theorem rubi1131r3Nondeg_complex : rubi1131r3Nondeg.Holds .complex :=
  rubi1131r3Nondeg_holds Interp.complex

/-- **1.1.3.2 #6** with `a c (m + 1) ≠ 0`. -/
theorem rubi1132r6Nondeg_holds (I : Interp 𝕜) :
    AntiderivHoldsUnder I "x" rubi1132r6Nondeg.conditions rubi1132r6Nondeg.body
      rubi1132r6Nondeg.result := by
  intro env hc t hF
  have hac : env "a" * env "c" * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.app2 .add (.var "m")
      (.int 1))) (.int 0)) (by simp [rubi1132r6Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have heq := hc (.eq (.app2 .add (.app2 .add (.app2 .mul (.app2 .add (.var "m") (.int 1))
    (.pow (.var "n") (.int (-1)))) (.var "p")) (.int 1)) (.int 0)) (by simp [rubi1132r6Nondeg])
  simp [Cond.Holds, Defined, eval, toInt?_neg_one] at heq
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1132r6Nondeg, Defined, eval, hkm] at h
  rcases hkn : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1132r6Nondeg, Defined, eval, hkn] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1132r6Nondeg, Defined, eval, hkp] at h
  have hm : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hn : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hkn
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkm1 : I.toInt? (env "m" + 1) = some (k + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hkp1 : I.toInt? (env "p" + 1) = some (q + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hj0 : (j : 𝕜) ≠ 0 := hn ▸ heq.1
  have hqj : ((k : 𝕜) + 1) + ((q : 𝕜) + 1) * j = 0 := by
    have h2 := heq.2
    rw [hn, hp, hm] at h2
    field_simp at h2
    linear_combination h2
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1132r6Nondeg.body →
      (k < 0 → env "c" ≠ 0 ∧ w ≠ 0) ∧ (j < 0 → w ≠ 0) ∧
        (q < 0 → env "a" + env "b" * w ^ j ≠ 0) := by
    intro w h
    simp [rubi1132r6Nondeg, Defined, eval, hkm, hkn, hkp] at h
    exact h
  have hDG : ∀ w, (k < 0 → env "c" ≠ 0 ∧ w ≠ 0) → (j < 0 → w ≠ 0) →
      (q < 0 → env "a" + env "b" * w ^ j ≠ 0) →
      Defined I (Function.update env "x" w) rubi1132r6Nondeg.result := by
    intro w h1 h2 h3
    simp [rubi1132r6Nondeg, Defined, eval, hkm1, hkn, hkp1, toInt?_neg_one, hac]
    exact ⟨fun h => h1 (by omega), h2, fun h => h3 (by omega)⟩
  have ht := hD t hF.self_of_nhds
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    exact hDG w (hD w hw).1 (hD w hw).2.1 (hD w hw).2.2
  · have hE : ∀ w, eval I (Function.update env "x" w) rubi1132r6Nondeg.result =
        (env "c" * w) ^ (k + 1) * (env "a" + env "b" * w ^ j) ^ (q + 1) *
          (env "a" * env "c" * (env "m" + 1))⁻¹ := by
      intro w
      simp [rubi1132r6Nondeg, eval, hkm1, hkn, hkp1, toInt?_neg_one]
    have hEF : eval I (Function.update env "x" t) rubi1132r6Nondeg.body =
        (env "c" * t) ^ k * (env "a" + env "b" * t ^ j) ^ q := by
      simp [rubi1132r6Nondeg, eval, hkm, hkn, hkp]
    rw [hEF, show (fun w => eval I (Function.update env "x" w) rubi1132r6Nondeg.result) =
        fun w => (env "c" * w) ^ (k + 1) * (env "a" + env "b" * w ^ j) ^ (q + 1) *
          (env "a" * env "c" * (env "m" + 1))⁻¹ from funext hE]
    have hj : j ≠ 0 := fun h => hj0 (by rw [h]; simp)
    have hct : env "c" * t ≠ 0 ∨ 0 ≤ k + 1 := by
      by_cases h : k < 0
      · exact Or.inl (mul_ne_zero (ht.1 h).1 (ht.1 h).2)
      · exact Or.inr (by omega)
    have hct0 : env "c" * t ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (mul_ne_zero (ht.1 h).1 (ht.1 h).2)
      · exact Or.inr (by omega)
    have hx : t ≠ 0 ∨ 0 ≤ j := by
      by_cases h : j < 0
      · exact Or.inl (ht.2.1 h)
      · exact Or.inr (by omega)
    have hx1 : t ≠ 0 ∨ 0 ≤ j - 1 := by
      by_cases h : j < 0
      · exact Or.inl (ht.2.1 h)
      · exact Or.inr (by omega)
    have hu : env "a" + env "b" * t ^ j ≠ 0 ∨ 0 ≤ q + 1 := by
      by_cases h : q + 1 < 0
      · exact Or.inl (ht.2.2 (by omega))
      · exact Or.inr (by omega)
    have hu0 : env "a" + env "b" * t ^ j ≠ 0 ∨ 0 ≤ q := by
      by_cases h : q < 0
      · exact Or.inl (ht.2.2 h)
      · exact Or.inr (by omega)
    have htj : t ^ j = t ^ (j - 1) * t := by
      rw [← zpow_succ_of _ _ hx1, sub_add_cancel]
    have hin : HasDerivAt (fun w => env "a" + env "b" * w ^ j)
        (env "b" * ((j : 𝕜) * t ^ (j - 1))) t :=
      ((hasDerivAt_zpow j t hx).const_mul (env "b")).const_add (env "a")
    refine (((HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ hct)
      ((hasDerivAt_id' t).const_mul (env "c"))).mul (HasDerivAt.comp t
        (hasDerivAt_zpow (q + 1) _ hu) hin)).mul_const _).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    rw [zpow_succ_of _ _ hct0, zpow_succ_of _ _ hu0]
    generalize (env "c" * t) ^ k = C
    generalize (env "a" + env "b" * t ^ j) ^ q = V
    rw [htj]
    generalize t ^ (j - 1) = T
    rw [hm] at hac ⊢
    push_cast
    rw [mul_inv_eq_iff_eq_mul₀ hac]
    linear_combination (C * V * env "c" * env "b" * T * t) * hqj

theorem rubi1132r6Nondeg_real : rubi1132r6Nondeg.Holds .real :=
  rubi1132r6Nondeg_holds Interp.real

theorem rubi1132r6Nondeg_complex : rubi1132r6Nondeg.Holds .complex :=
  rubi1132r6Nondeg_holds Interp.complex

end Proofs

end OSR.IntegrationRec38
