import OSR.IntegrationRec47

/-!
# Integration (RUBI): strengthened variants with residual integrals, second batch

Strengthened variants (Specification V1-R-005e) of the refuted RUBI rules
1.2.1.2 #1, 1.2.1.3 #19 and #20.  For #1 and #20 the converted condition
`c d² - b d e + a e² = 0` factors the trinomial as `(d + e x) (a/d + c x/e)`,
which needs both `d ≠ 0` and `e ≠ 0`.  Proved over ℝ and ℂ for every choice of
antiderivatives of the residual integrands; the refutations of the rules as
stated are kept.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec48

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 1.2.1.2 #1 when d ≠ 0 and e ≠ 0 -/
def rubi1212r1Nondeg : CRule where
  id := "integration.rubi_1_2_1_2_r1_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:1"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.var "p"))) (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "e") (.int (-1)))) (.var "x"))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "m", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .int (.var "p"),
    .ne (.var "d") (.int 0),
    .ne (.var "e") (.int 0)]
  priority := 7401
  description := "RUBI 1.2.1.2 #1 when d ≠ 0 and e ≠ 0"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:1" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#1"

/-- RUBI 1.2.1.3 #20 when d ≠ 0 and e ≠ 0 -/
def rubi1213r20Nondeg : CRule where
  id := "integration.rubi_1_2_1_3_r20_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:20"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.var "p"))) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "e") (.int (-1)))) (.var "x"))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .int (.var "p"),
    .ne (.var "d") (.int 0),
    .ne (.var "e") (.int 0)]
  priority := 7402
  description := "RUBI 1.2.1.3 #20 when d ≠ 0 and e ≠ 0"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:20" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.m#20"

/-- RUBI 1.2.1.3 #19 when e^p ≠ 0 -/
def rubi1213r19Nondeg : CRule where
  id := "integration.rubi_1_2_1_3_r19_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:19"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.app2 .mul (.var "b") (.var "x")) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.int 1) (.pow (.pow (.var "e") (.var "p")) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.var "p"))) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.var "b") (.app2 .mul (.var "c") (.var "x"))) (.var "p"))))]
  independent := ["b", "c", "e", "f", "g", "m", "p"]
  conditions := [.int (.var "p"),
    .ne (.pow (.var "e") (.var "p")) (.int 0)]
  priority := 7403
  description := "RUBI 1.2.1.3 #19 when e^p ≠ 0"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:19" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.m#19"

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






/-- **1.2.1.2 #1** with `d ≠ 0` and `e ≠ 0`: `a + b x + c x² = (d + e x) (a/d + c x/e)`. -/
theorem rubi1212r1Nondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi1212r1Nondeg.conditions rubi1212r1Nondeg.body rubi1212r1Nondeg.result rubi1212r1Nondeg.integrals := by
  intro env hc t hF
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi1212r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have he : env "e" ≠ 0 := by
    have h := hc (.ne (.var "e") (.int 0)) (by simp [rubi1212r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have h1 : env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1212r1Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  have hdi : env "d" * (env "d")⁻¹ = 1 := mul_inv_cancel₀ hd
  have hei : env "e" * (env "e")⁻¹ = 1 := mul_inv_cancel₀ he
  have hQ : ∀ w : 𝕜, (env "a" + env "b" * w + env "c" * w ^ 2) = (env "d" + env "e" * w) * (env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * w) := fun w => by
    linear_combination (-w * (env "d")⁻¹ * (env "e")⁻¹) * h1 +
      (env "c" * env "d" * (env "e")⁻¹ * w - env "b" * w * env "e" * (env "e")⁻¹) * hdi +
      (env "a" * env "e" * (env "d")⁻¹ * w - env "b" * w) * hei - env "a" * hdi - env "c" * w ^ 2 * hei
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1212r1Nondeg, Defined, eval, hkm] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1212r1Nondeg, Defined, eval, hkp] at h
  have hm : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkmp : I.toInt? (env "m" + env "p") = some (k + q) :=
    (I.toInt?_eq _ _).2 (by rw [hm, hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1212r1Nondeg.body →
      (k < 0 → (env "d" + env "e" * w) ≠ 0) ∧ (q < 0 → (env "a" + env "b" * w + env "c" * w ^ 2) ≠ 0) := by
    intro w h
    simp [rubi1212r1Nondeg, Defined, eval, hkm, hkp, toInt?_two] at h
    tauto
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1212r1Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1', h2'⟩ := hD w hw
    simp [Defined, eval, hkmp, hkp, toInt?_neg_one, hd, he]
    refine ⟨fun hkq hD0 => ?_, fun hq hL => h2' hq (by rw [hQ w, hL, mul_zero])⟩
    by_cases hq : q < 0
    · exact h2' hq (by rw [hQ w, hD0, zero_mul])
    · exact h1' (by omega) hD0
  · exact Eventually.of_forall fun w => by simp [rubi1212r1Nondeg, Defined, eval, recEnv]
  · simp only [rubi1212r1Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (rubi1212r1Nondeg.integrals.map (·.1)) Φ "x" w) rubi1212r1Nondeg.result) =
        Φ "I1" := by
      funext w
      simp [rubi1212r1Nondeg, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    simp [rubi1212r1Nondeg, eval, hkm, hkp, hkmp, toInt?_neg_one, toInt?_two]
    have hz : env "d" + env "e" * t ≠ 0 ∨ k + q ≠ 0 ∨ k = 0 ∧ q = 0 := by
      by_cases hD0 : env "d" + env "e" * t = 0
      · have hk : 0 ≤ k := by
          by_contra hk
          exact ht.1 (by omega) hD0
        have hq : 0 ≤ q := by
          by_contra hq
          exact ht.2 (by omega) (by rw [hQ t, hD0, zero_mul])
        by_cases hkq : k + q = 0
        · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
        · exact Or.inr (Or.inl hkq)
      · exact Or.inl hD0
    rw [hQ t, mul_zpow, zpow_add' hz]
    ring

theorem rubi1212r1Nondeg_real : rubi1212r1Nondeg.Holds .real :=
  rubi1212r1Nondeg_holds Interp.real

theorem rubi1212r1Nondeg_complex : rubi1212r1Nondeg.Holds .complex :=
  rubi1212r1Nondeg_holds Interp.complex

/-- **1.2.1.3 #20** with `d ≠ 0` and `e ≠ 0`: `a + b x + c x² = (d + e x) (a/d + c x/e)`. -/
theorem rubi1213r20Nondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi1213r20Nondeg.conditions rubi1213r20Nondeg.body rubi1213r20Nondeg.result rubi1213r20Nondeg.integrals := by
  intro env hc t hF
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi1213r20Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have he : env "e" ≠ 0 := by
    have h := hc (.ne (.var "e") (.int 0)) (by simp [rubi1213r20Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have h1 : env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1213r20Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  have hdi : env "d" * (env "d")⁻¹ = 1 := mul_inv_cancel₀ hd
  have hei : env "e" * (env "e")⁻¹ = 1 := mul_inv_cancel₀ he
  have hQ : ∀ w : 𝕜, (env "a" + env "b" * w + env "c" * w ^ 2) = (env "d" + env "e" * w) * (env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * w) := fun w => by
    linear_combination (-w * (env "d")⁻¹ * (env "e")⁻¹) * h1 +
      (env "c" * env "d" * (env "e")⁻¹ * w - env "b" * w * env "e" * (env "e")⁻¹) * hdi +
      (env "a" * env "e" * (env "d")⁻¹ * w - env "b" * w) * hei - env "a" * hdi - env "c" * w ^ 2 * hei
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r20Nondeg, Defined, eval, hkm] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r20Nondeg, Defined, eval, hkp] at h
  have hm : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkmp : I.toInt? (env "m" + env "p") = some (k + q) :=
    (I.toInt?_eq _ _).2 (by rw [hm, hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1213r20Nondeg.body →
      (k < 0 → (env "d" + env "e" * w) ≠ 0) ∧ (q < 0 → (env "a" + env "b" * w + env "c" * w ^ 2) ≠ 0) := by
    intro w h
    simp [rubi1213r20Nondeg, Defined, eval, hkm, hkp, toInt?_two] at h
    tauto
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1213r20Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1', h2'⟩ := hD w hw
    simp [Defined, eval, hkmp, hkp, toInt?_neg_one, hd, he]
    refine ⟨fun hkq hD0 => ?_, fun hq hL => h2' hq (by rw [hQ w, hL, mul_zero])⟩
    by_cases hq : q < 0
    · exact h2' hq (by rw [hQ w, hD0, zero_mul])
    · exact h1' (by omega) hD0
  · exact Eventually.of_forall fun w => by simp [rubi1213r20Nondeg, Defined, eval, recEnv]
  · simp only [rubi1213r20Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (rubi1213r20Nondeg.integrals.map (·.1)) Φ "x" w) rubi1213r20Nondeg.result) =
        Φ "I1" := by
      funext w
      simp [rubi1213r20Nondeg, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    simp [rubi1213r20Nondeg, eval, hkm, hkp, hkmp, toInt?_neg_one, toInt?_two]
    have hz : env "d" + env "e" * t ≠ 0 ∨ k + q ≠ 0 ∨ k = 0 ∧ q = 0 := by
      by_cases hD0 : env "d" + env "e" * t = 0
      · have hk : 0 ≤ k := by
          by_contra hk
          exact ht.1 (by omega) hD0
        have hq : 0 ≤ q := by
          by_contra hq
          exact ht.2 (by omega) (by rw [hQ t, hD0, zero_mul])
        by_cases hkq : k + q = 0
        · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
        · exact Or.inr (Or.inl hkq)
      · exact Or.inl hD0
    rw [hQ t, mul_zpow, zpow_add' hz]
    ring

theorem rubi1213r20Nondeg_real : rubi1213r20Nondeg.Holds .real :=
  rubi1213r20Nondeg_holds Interp.real

theorem rubi1213r20Nondeg_complex : rubi1213r20Nondeg.Holds .complex :=
  rubi1213r20Nondeg_holds Interp.complex

/-- **1.2.1.3 #19** with `eᵖ ≠ 0`. -/
theorem rubi1213r19Nondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi1213r19Nondeg.conditions rubi1213r19Nondeg.body rubi1213r19Nondeg.result rubi1213r19Nondeg.integrals := by
  intro env hc t hF
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r19Nondeg, Defined, eval, hkm] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r19Nondeg, Defined, eval, hkp] at h
  have hm : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkmp : I.toInt? (env "m" + env "p") = some (k + q) :=
    (I.toInt?_eq _ _).2 (by rw [hm, hp]; push_cast; ring)
  have hep : env "e" ^ q ≠ 0 := by
    have h := hc (.ne (.pow (.var "e") (.var "p")) (.int 0)) (by simp [rubi1213r19Nondeg])
    simp [Cond.Holds, Defined, eval, hkp] at h
    exact h.2
  have he0 : q ≠ 0 → env "e" ≠ 0 := fun hq he => hep (by rw [he, zero_zpow q hq])
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1213r19Nondeg.body →
      (k < 0 → env "e" * w ≠ 0) ∧ (q < 0 → env "b" * w + env "c" * w ^ 2 ≠ 0) := by
    intro w h
    simp [rubi1213r19Nondeg, Defined, eval, hkm, hkp, toInt?_two] at h
    exact ⟨fun hk => mul_ne_zero (h.1 hk).1 (h.1 hk).2, h.2⟩
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1213r19Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
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
      simp [rubi1213r19Nondeg, Defined, eval, recEnv, hkp, toInt?_neg_one]
      exact ⟨fun hq => he0 (by omega), hep⟩
  · simp only [rubi1213r19Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (rubi1213r19Nondeg.integrals.map (·.1)) Φ "x" w) rubi1213r19Nondeg.result) =
        fun w => 1 * (env "e" ^ q)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi1213r19Nondeg, eval, recEnv, hkp, toInt?_neg_one]
    rw [hfun]
    refine (hΦ.const_mul _).congr_deriv ?_
    simp [rubi1213r19Nondeg, eval, hkm, hkp, hkmp, toInt?_two]
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

theorem rubi1213r19Nondeg_real : rubi1213r19Nondeg.Holds .real :=
  rubi1213r19Nondeg_holds Interp.real

theorem rubi1213r19Nondeg_complex : rubi1213r19Nondeg.Holds .complex :=
  rubi1213r19Nondeg_holds Interp.complex

end Proofs

end OSR.IntegrationRec48
