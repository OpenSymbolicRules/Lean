import OSR.IntegrationRec46

/-!
# Integration (RUBI): strengthened variants of rules with residual integrals

Strengthened variants (Specification V1-R-005e) of refuted RUBI rules whose
result contains residual integrals, with a non-degeneracy condition appended
to the converted conditions.  Proved over ℝ and ℂ for every choice of
antiderivatives of the residual integrands; the refutations of the rules as
stated are kept.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec47

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 1.2.1.2 #20 with a non-degeneracy condition -/
def rubi1212r20Nondeg : CRule where
  id := "integration.rubi_1_2_1_2_r20_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:20"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.pow (.app2 .add (.app2 .mul (.var "b") (.var "x")) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.int 1) (.pow (.pow (.var "e") (.var "p")) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.var "p"))) (.pow (.app2 .add (.var "b") (.app2 .mul (.var "c") (.var "x"))) (.var "p"))))]
  independent := ["b", "c", "e", "m", "p"]
  conditions := [.int (.var "p"),
    .ne (.pow (.var "e") (.var "p")) (.int 0)]
  priority := 7320
  description := "RUBI 1.2.1.2 #20 with a non-degeneracy condition"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:20" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#20"

/-- RUBI 1.2.1.2 #103 with a non-degeneracy condition -/
def rubi1212r103Nondeg : CRule where
  id := "integration.rubi_1_2_1_2_r103_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:103"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.pow (.app2 .mul (.int 2) (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "m", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .ne (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .ne (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3)) (.int 0),
    .ne (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))))) (.int 0),
    .ne (.app2 .mul (.int 2) (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))))) (.int 0)]
  priority := 73103
  description := "RUBI 1.2.1.2 #103 with a non-degeneracy condition"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:103" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#103"

/-- RUBI 1.2.1.2 #104 with a non-degeneracy condition -/
def rubi1212r104Nondeg : CRule where
  id := "integration.rubi_1_2_1_2_r104_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:104"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.var "d")) (.pow (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))))]
  independent := ["a", "c", "d", "e", "m", "p"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3)) (.int 0),
    .ne (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))))) (.int 0)]
  priority := 73104
  description := "RUBI 1.2.1.2 #104 with a non-degeneracy condition"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:104" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#104"

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





/-- **1.2.1.2 #20** with `eᵖ ≠ 0`. -/
theorem rubi1212r20Nondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi1212r20Nondeg.conditions rubi1212r20Nondeg.body rubi1212r20Nondeg.result rubi1212r20Nondeg.integrals := by
  intro env hc t hF
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1212r20Nondeg, Defined, eval, hkm] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1212r20Nondeg, Defined, eval, hkp] at h
  have hm : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkmp : I.toInt? (env "m" + env "p") = some (k + q) :=
    (I.toInt?_eq _ _).2 (by rw [hm, hp]; push_cast; ring)
  have hep : env "e" ^ q ≠ 0 := by
    have h := hc (.ne (.pow (.var "e") (.var "p")) (.int 0)) (by simp [rubi1212r20Nondeg])
    simp [Cond.Holds, Defined, eval, hkp] at h
    exact h.2
  have he0 : q ≠ 0 → env "e" ≠ 0 := fun hq he => hep (by rw [he, zero_zpow q hq])
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1212r20Nondeg.body →
      (k < 0 → env "e" * w ≠ 0) ∧ (q < 0 → env "b" * w + env "c" * w ^ 2 ≠ 0) := by
    intro w h
    simp [rubi1212r20Nondeg, Defined, eval, hkm, hkp, toInt?_two] at h
    exact ⟨fun hk => mul_ne_zero (h.1 hk).1 (h.1 hk).2, h.2⟩
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1212r20Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2⟩ := hD w hw
    simp [Defined, eval, hkmp, hkp]
    refine ⟨fun hkq => ?_, fun hq hb => h2 hq (by
      rw [show env "b" * w + env "c" * w ^ 2 = w * (env "b" + env "c" * w) by ring, hb, mul_zero])⟩
    by_cases hq : q < 0
    · have hw : w ≠ 0 := fun hw => h2 hq (by rw [hw]; ring)
      exact ⟨he0 (by omega), hw⟩
    · have := h1 (by omega)
      exact ⟨left_ne_zero_of_mul this, right_ne_zero_of_mul this⟩
  · exact Eventually.of_forall fun w => by
      simp [rubi1212r20Nondeg, Defined, eval, recEnv, hkp, toInt?_neg_one]
      exact ⟨fun hq => he0 (by omega), hep⟩
  · simp only [rubi1212r20Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (rubi1212r20Nondeg.integrals.map (·.1)) Φ "x" w) rubi1212r20Nondeg.result) =
        fun w => 1 * (env "e" ^ q)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi1212r20Nondeg, eval, recEnv, hkp, toInt?_neg_one]
    rw [hfun]
    refine (hΦ.const_mul _).congr_deriv ?_
    simp [rubi1212r20Nondeg, eval, hkm, hkp, hkmp, toInt?_two]
    have hzp : env "e" * t ≠ 0 ∨ k + q ≠ 0 ∨ k = 0 ∧ q = 0 := by
      by_cases het : env "e" * t = 0
      · have hk : 0 ≤ k := by
          by_contra hk
          exact ht.1 (by omega) het
        have hq : 0 ≤ q := by
          by_contra hq
          have hw : t ≠ 0 := fun hw => ht.2 (by omega) (by rw [hw]; ring)
          exact mul_ne_zero (he0 (by omega)) hw het
        by_cases hkq : k + q = 0
        · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
        · exact Or.inr (Or.inl hkq)
      · exact Or.inl het
    rw [zpow_add' hzp, mul_zpow (env "e") t q,
      show env "b" * t + env "c" * t ^ 2 = t * (env "b" + env "c" * t) by ring, mul_zpow t _ q,
      inv_mul_eq_iff_eq_mul₀ hep]
    ring

theorem rubi1212r20Nondeg_real : rubi1212r20Nondeg.Holds .real :=
  rubi1212r20Nondeg_holds Interp.real

theorem rubi1212r20Nondeg_complex : rubi1212r20Nondeg.Holds .complex :=
  rubi1212r20Nondeg_holds Interp.complex

/-- **1.2.1.2 #103** with `(m + 1) (c d² - b d e + a e²) ≠ 0`. -/
theorem rubi1212r103Nondeg_holds [CharZero 𝕜] (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi1212r103Nondeg.conditions rubi1212r103Nondeg.body rubi1212r103Nondeg.result rubi1212r103Nondeg.integrals := by
  intro env hc t hF
  have hW : (env "m" + 1) * (env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))))) (.int 0)) (by simp [rubi1212r103Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  have h2 : env "m" + 2 * env "p" + 3 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3)) (.int 0)) (by simp [rubi1212r103Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hP : (env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2) ≠ 0 := right_ne_zero_of_mul hW
  have h2P : (2 * (env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2)) ≠ 0 := mul_ne_zero two_ne_zero hP
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1212r103Nondeg, Defined, eval, hkm] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1212r103Nondeg, Defined, eval, hkp] at h
  have hm : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkm1 : I.toInt? (env "m" + 1) = some (k + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hkp1 : I.toInt? (env "p" + 1) = some (q + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1212r103Nondeg.body →
      (k < 0 → (env "d" + env "e" * w) ≠ 0) ∧ (q < 0 → (env "a" + env "b" * w + env "c" * w ^ 2) ≠ 0) := by
    intro w h
    simp [rubi1212r103Nondeg, Defined, eval, hkm, hkp, toInt?_two] at h
    tauto
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1212r103Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2⟩ := hD w hw
    simp [Defined, eval, hkm1, hkp, toInt?_two]
    exact ⟨fun h => h1 (by omega), h2⟩
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h2⟩ := hD w hw
    simp [rubi1212r103Nondeg, Defined, eval, recEnv, hkm1, hkp1, toInt?_neg_one, toInt?_two]
    have hP' : ¬env "c" * env "d" ^ 2 + -(env "b" * env "d" * env "e") + env "a" * env "e" ^ 2 = 0 :=
      fun h => hP (by linear_combination h)
    exact ⟨⟨⟨fun h => h1 (by omega), fun h => h2 (by omega)⟩, left_ne_zero_of_mul hW, hP'⟩, hP'⟩
  · simp only [rubi1212r103Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (rubi1212r103Nondeg.integrals.map (·.1)) Φ "x" w) rubi1212r103Nondeg.result) =
        fun w => env "e" * (env "d" + env "e" * w) ^ (k + 1) * (env "a" + env "b" * w + env "c" * w ^ 2) ^ (q + 1) * ((env "m" + 1) * (env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2))⁻¹ +
          (2 * env "c" * env "d" + -1 * env "b" * env "e") * (2 * (env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi1212r103Nondeg, eval, recEnv, hkm1, hkp1, toInt?_neg_one, toInt?_two]
    rw [hfun]
    have hA : (env "d" + env "e" * t) ≠ 0 ∨ 0 ≤ k + 1 := by
      by_cases h : k + 1 < 0
      · exact Or.inl (ht.1 (by omega))
      · exact Or.inr (by omega)
    have hA0 : (env "d" + env "e" * t) ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (ht.1 h)
      · exact Or.inr (by omega)
    have hB : (env "a" + env "b" * t + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ q + 1 := by
      by_cases h : q + 1 < 0
      · exact Or.inl (ht.2 (by omega))
      · exact Or.inr (by omega)
    have hB0 : (env "a" + env "b" * t + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ q := by
      by_cases h : q < 0
      · exact Or.inl (ht.2 h)
      · exact Or.inr (by omega)
    have hQ : HasDerivAt (fun w => env "a" + env "b" * w + env "c" * w ^ 2) (env "b" * 1 + env "c" * (↑2 * t ^ (2 - 1) * 1)) t :=
      (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add
        (((hasDerivAt_id' t).pow 2).const_mul (env "c"))
    have hEF : eval I (Function.update env "x" t) rubi1212r103Nondeg.body =
        (env "d" + env "e" * t) ^ k * (env "a" + env "b" * t + env "c" * t ^ 2) ^ q := by
      simp [rubi1212r103Nondeg, eval, hkm, hkp, toInt?_two]
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t) ^ (k + 1) * (env "a" + env "b" * t + env "c" * t ^ 2) ^ q) t := by
      convert hΦ using 1
      simp [eval, hkm1, hkp, toInt?_two]
    rw [hEF]
    refine (((((HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ hA)
      (((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d"))).const_mul (env "e")).mul
        (HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ hB) hQ)).mul_const _).add
          (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    rw [zpow_succ_of _ _ hA0, zpow_succ_of _ _ hB0]
    generalize (env "d" + env "e" * t) ^ k = X
    generalize (env "a" + env "b" * t + env "c" * t ^ 2) ^ q = Y
    simp only [hm, hp] at h2 hW ⊢
    push_cast at hW ⊢
    set u := (((k : 𝕜) + 1) * (env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2))⁻¹ with hu_def
    have hu : ((k : 𝕜) + 1) * (env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2) * u = 1 := by rw [hu_def]; exact mul_inv_cancel₀ hW
    set v := (2 * (env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2))⁻¹ with hv_def
    have hv : (2 * (env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2)) * v = 1 := by rw [hv_def]; exact mul_inv_cancel₀ h2P
    have huv : ((q : 𝕜) + 1) * u + v = 0 := by
      have h0 : (2 * (env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2)) * (((q : 𝕜) + 1) * u + v) = 0 := by
        linear_combination ((env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2) * u) * h2 - hu + hv
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd h h2P
      · exact h
    linear_combination (X * Y) * hu + (X * Y * u * (env "d" + env "e" * t) * (env "b" * env "e" - env "c" * env "d" + env "c" * env "e" * t)) * h2 + (X * Y * (2 * env "c" * env "d" + -1 * env "b" * env "e") * (env "d" + env "e" * t)) * huv

theorem rubi1212r103Nondeg_real : rubi1212r103Nondeg.Holds .real :=
  rubi1212r103Nondeg_holds Interp.real

theorem rubi1212r103Nondeg_complex : rubi1212r103Nondeg.Holds .complex :=
  rubi1212r103Nondeg_holds Interp.complex

/-- **1.2.1.2 #104** with `(m + 1) (c d² + a e²) ≠ 0`. -/
theorem rubi1212r104Nondeg_holds [CharZero 𝕜] (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi1212r104Nondeg.conditions rubi1212r104Nondeg.body rubi1212r104Nondeg.result rubi1212r104Nondeg.integrals := by
  intro env hc t hF
  have hW : (env "m" + 1) * (env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))))) (.int 0)) (by simp [rubi1212r104Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  have h2 : env "m" + 2 * env "p" + 3 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3)) (.int 0)) (by simp [rubi1212r104Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hP : (env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2) ≠ 0 := right_ne_zero_of_mul hW
  have h2P : (env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2) ≠ 0 := hP
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1212r104Nondeg, Defined, eval, hkm] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1212r104Nondeg, Defined, eval, hkp] at h
  have hm : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkm1 : I.toInt? (env "m" + 1) = some (k + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hkp1 : I.toInt? (env "p" + 1) = some (q + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1212r104Nondeg.body →
      (k < 0 → (env "d" + env "e" * w) ≠ 0) ∧ (q < 0 → (env "a" + env "c" * w ^ 2) ≠ 0) := by
    intro w h
    simp [rubi1212r104Nondeg, Defined, eval, hkm, hkp, toInt?_two] at h
    tauto
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1212r104Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2⟩ := hD w hw
    simp [Defined, eval, hkm1, hkp, toInt?_two]
    exact ⟨fun h => h1 (by omega), h2⟩
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h2⟩ := hD w hw
    simp [rubi1212r104Nondeg, Defined, eval, recEnv, hkm1, hkp1, toInt?_neg_one, toInt?_two]
    exact ⟨⟨⟨fun h => h1 (by omega), fun h => h2 (by omega)⟩, left_ne_zero_of_mul hW, hP⟩, hP⟩
  · simp only [rubi1212r104Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (rubi1212r104Nondeg.integrals.map (·.1)) Φ "x" w) rubi1212r104Nondeg.result) =
        fun w => env "e" * (env "d" + env "e" * w) ^ (k + 1) * (env "a" + env "c" * w ^ 2) ^ (q + 1) * ((env "m" + 1) * (env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2))⁻¹ +
          (env "c" * env "d") * (env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi1212r104Nondeg, eval, recEnv, hkm1, hkp1, toInt?_neg_one, toInt?_two]
    rw [hfun]
    have hA : (env "d" + env "e" * t) ≠ 0 ∨ 0 ≤ k + 1 := by
      by_cases h : k + 1 < 0
      · exact Or.inl (ht.1 (by omega))
      · exact Or.inr (by omega)
    have hA0 : (env "d" + env "e" * t) ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (ht.1 h)
      · exact Or.inr (by omega)
    have hB : (env "a" + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ q + 1 := by
      by_cases h : q + 1 < 0
      · exact Or.inl (ht.2 (by omega))
      · exact Or.inr (by omega)
    have hB0 : (env "a" + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ q := by
      by_cases h : q < 0
      · exact Or.inl (ht.2 h)
      · exact Or.inr (by omega)
    have hQ : HasDerivAt (fun w => env "a" + env "c" * w ^ 2) (env "c" * (↑2 * t ^ (2 - 1) * 1)) t :=
      (((hasDerivAt_id' t).pow 2).const_mul (env "c")).const_add (env "a")
    have hEF : eval I (Function.update env "x" t) rubi1212r104Nondeg.body =
        (env "d" + env "e" * t) ^ k * (env "a" + env "c" * t ^ 2) ^ q := by
      simp [rubi1212r104Nondeg, eval, hkm, hkp, toInt?_two]
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t) ^ (k + 1) * (env "a" + env "c" * t ^ 2) ^ q) t := by
      convert hΦ using 1
      simp [eval, hkm1, hkp, toInt?_two]
    rw [hEF]
    refine (((((HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ hA)
      (((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d"))).const_mul (env "e")).mul
        (HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ hB) hQ)).mul_const _).add
          (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    rw [zpow_succ_of _ _ hA0, zpow_succ_of _ _ hB0]
    generalize (env "d" + env "e" * t) ^ k = X
    generalize (env "a" + env "c" * t ^ 2) ^ q = Y
    simp only [hm, hp] at h2 hW ⊢
    push_cast at hW ⊢
    set u := (((k : 𝕜) + 1) * (env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2))⁻¹ with hu_def
    have hu : ((k : 𝕜) + 1) * (env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2) * u = 1 := by rw [hu_def]; exact mul_inv_cancel₀ hW
    set v := (env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2)⁻¹ with hv_def
    have hv : (env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2) * v = 1 := by rw [hv_def]; exact mul_inv_cancel₀ h2P
    have huv : 2 * ((q : 𝕜) + 1) * u + v = 0 := by
      have h0 : (env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2) * (2 * ((q : 𝕜) + 1) * u + v) = 0 := by
        linear_combination ((env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2) * u) * h2 - hu + hv
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd h h2P
      · exact h
    linear_combination (X * Y) * hu + (X * Y * env "c" * u * (env "e" * t - env "d") * (env "d" + env "e" * t)) * h2 + (X * Y * env "c" * env "d" * (env "d" + env "e" * t)) * huv

theorem rubi1212r104Nondeg_real : rubi1212r104Nondeg.Holds .real :=
  rubi1212r104Nondeg_holds Interp.real

theorem rubi1212r104Nondeg_complex : rubi1212r104Nondeg.Holds .complex :=
  rubi1212r104Nondeg_holds Interp.complex

end Proofs

end OSR.IntegrationRec47
