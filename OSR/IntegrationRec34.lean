import OSR.IntegrationRec33

/-!
# Integration (RUBI): flipping a binomial in `x^(-n)`

RUBI 4.16.1 1.1.3.5 #41 rewrites `(c + d x^(-n))^q` as `(d + c xⁿ)^q / x^(n q)`
(`neg_flip`), valid for `x ≠ 0` or `n = 0`, which the integrand guarantees.
Proved over ℝ and ℂ.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec34

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- (c + d x^(-n))^q = (d + c x^n)^q / x^(n q) under the integral -/
def binomTripleNegFlip : CRule where
  id := "integration.binomial_triple_negative_flip"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:41"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "mn")))) (.var "q"))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.var "n")))) (.var "r")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "q"))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.var "n")))) (.var "r"))) (.pow (.pow (.var "x") (.app2 .mul (.var "n") (.var "q"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "n", "p", "r", "mn", "q"]
  conditions := [.eq (.var "mn") (.app2 .mul (.int (-1)) (.var "n")),
    .int (.var "q")]
  priority := 6300
  description := "(c + d x^(-n))^q = (d + c x^n)^q / x^(n q) under the integral"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:41" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r.m#41"

/-- x^m (c + d x^(-n))^q = x^(m - n q) (d + c x^n)^q under the integral -/
def monoBinomTripleNegFlip : CRule where
  id := "integration.monomial_binomial_triple_negative_flip"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.6 (g x)^m (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:29"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "mn")))) (.var "q"))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.var "n")))) (.var "r")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.var "n")) (.var "q")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "q"))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.var "n")))) (.var "r"))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "p", "r", "mn", "q"]
  conditions := [.eq (.var "mn") (.app2 .mul (.int (-1)) (.var "n")),
    .int (.var "q")]
  priority := 6310
  description := "x^m (c + d x^(-n))^q = x^(m - n q) (d + c x^n)^q under the integral"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.6 (g x)^m (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:29" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.6 (g x)^m (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r.m#29"

/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem toInt?_val {I : Interp 𝕜} {v : 𝕜} {k : ℤ} (h : I.toInt? v = some k) :
    v = (k : 𝕜) := (I.toInt?_eq _ _).1 h

private theorem toInt?_neg_one (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

/-- `(c + d x^(-n))^q = (d + c xⁿ)^q (x^(n q))⁻¹` for `x ≠ 0` or `n = 0`. -/
theorem neg_flip (w c d : 𝕜) (n q : ℤ) (h : w ≠ 0 ∨ n = 0) :
    (c + d * w ^ (-n)) ^ q = (d + c * w ^ n) ^ q * (w ^ (n * q))⁻¹ := by
  rcases h with hw | rfl
  · have hn : w ^ n ≠ 0 := zpow_ne_zero n hw
    have h1 : c + d * w ^ (-n) = (d + c * w ^ n) * (w ^ n)⁻¹ := by
      rw [zpow_neg]; field_simp; ring
    rw [h1, mul_zpow, inv_zpow, ← zpow_mul]
  · simp [add_comm]

theorem binomTripleNegFlip_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" binomTripleNegFlip.conditions binomTripleNegFlip.body
      binomTripleNegFlip.result binomTripleNegFlip.integrals := by
  intro env hc t hF
  have heq := hc (.eq (.var "mn") (.app2 .mul (.int (-1)) (.var "n")))
    (by simp [binomTripleNegFlip])
  have hmn : env "mn" = -env "n" := by simpa [Cond.Holds, Defined, eval] using heq.2.2
  rcases hkn : I.toInt? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [binomTripleNegFlip, Defined, eval, hkn] at h
  have T : ∀ (v : 𝕜) (z : ℤ), v = (z : 𝕜) → I.toInt? v = some z :=
    fun v z h => (I.toInt?_eq _ _).2 h
  have hn := toInt?_val hkn
  have kmn : I.toInt? (env "mn") = some (-n) := T _ _ (by rw [hmn, hn]; push_cast; ring)
  have kmn' : I.toInt? (-env "n") = some (-n) := T _ _ (by rw [hn]; push_cast; ring)
  rcases hkp : I.toInt? (env "p") with _ | p
  · exfalso
    have h := hF.self_of_nhds
    simp [binomTripleNegFlip, Defined, eval, hkn, kmn, hkp] at h
  rcases hkq : I.toInt? (env "q") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [binomTripleNegFlip, Defined, eval, hkn, kmn, hkq] at h
  rcases hkr : I.toInt? (env "r") with _ | r
  · exfalso
    have h := hF.self_of_nhds
    simp [binomTripleNegFlip, Defined, eval, hkn, kmn, hkr] at h
  have hq := toInt?_val hkq
  have knq : I.toInt? (env "n" * env "q") = some (n * q) := T _ _ (by rw [hn, hq]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) binomTripleNegFlip.body →
      (w ≠ 0 ∨ n = 0) ∧ (p < 0 → env "a" + env "b" * w ^ n ≠ 0) ∧
        (q < 0 → env "c" + env "d" * (w ^ n)⁻¹ ≠ 0) ∧ (r < 0 → env "e" + env "f" * w ^ n ≠ 0) := by
    intro w h
    simp [binomTripleNegFlip, Defined, eval, hkn, kmn, hkp, hkq, hkr] at h
    obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, -, h5⟩ := h
    refine ⟨?_, h2, h4, h5⟩
    rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
    · exact Or.inl (h1 hn0)
    · exact Or.inr hn0
    · exact Or.inl (h3 hn0)
  have hflip : ∀ w : 𝕜, (w ≠ 0 ∨ n = 0) → env "c" + env "d" * (w ^ n)⁻¹ ≠ 0 →
      env "d" + env "c" * w ^ n ≠ 0 := by
    intro w hw h0 h1
    apply h0
    rcases hw with hw | rfl
    · have hn' : w ^ n ≠ 0 := zpow_ne_zero n hw
      field_simp
      linear_combination h1
    · simp at h1 ⊢; linear_combination h1
  have hpow : ∀ w : 𝕜, (w ≠ 0 ∨ n = 0) → w ^ (n * q) ≠ 0 := by
    intro w hw
    rcases hw with hw | rfl
    · exact zpow_ne_zero _ hw
    · simp
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [binomTripleNegFlip, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h0, h2, h4, h5⟩ := hD w hw
    simp [Defined, eval, hkn, hkp, hkq, hkr, knq, toInt?_neg_one]
    have hw' : n < 0 → w ≠ 0 := fun hn0 => h0.resolve_right (by omega)
    have hwq : n * q < 0 → w ≠ 0 := fun hnq => h0.resolve_right (fun h => by subst h; simp at hnq)
    exact ⟨⟨⟨⟨hw', h2⟩, hw', fun hq0 => hflip w h0 (h4 hq0)⟩, hw', h5⟩, hwq, hpow w h0⟩
  · exact Eventually.of_forall fun _ => by simp [binomTripleNegFlip, Defined]
  · simp only [binomTripleNegFlip, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (binomTripleNegFlip.integrals.map (·.1)) Φ "x" w)
        binomTripleNegFlip.result) = Φ "I1" := by
      funext w
      simp [binomTripleNegFlip, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    obtain ⟨h0, -, -, -⟩ := hD t hF.self_of_nhds
    simp [binomTripleNegFlip, eval, hkn, hkp, hkq, hkr, kmn, knq, toInt?_neg_one]
    rw [show env "c" + env "d" * (t ^ n)⁻¹ = env "c" + env "d" * t ^ (-n) by rw [zpow_neg],
      neg_flip t (env "c") (env "d") n q h0]
    ring

theorem binomTripleNegFlip_real : binomTripleNegFlip.Holds .real :=
  binomTripleNegFlip_holds Interp.real

theorem binomTripleNegFlip_complex : binomTripleNegFlip.Holds .complex :=
  binomTripleNegFlip_holds Interp.complex

theorem monoBinomTripleNegFlip_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" monoBinomTripleNegFlip.conditions monoBinomTripleNegFlip.body
      monoBinomTripleNegFlip.result monoBinomTripleNegFlip.integrals := by
  intro env hc t hF
  have heq := hc (.eq (.var "mn") (.app2 .mul (.int (-1)) (.var "n")))
    (by simp [monoBinomTripleNegFlip])
  have hmn : env "mn" = -env "n" := by simpa [Cond.Holds, Defined, eval] using heq.2.2
  rcases hkn : I.toInt? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [monoBinomTripleNegFlip, Defined, eval, hkn] at h
  have T : ∀ (v : 𝕜) (z : ℤ), v = (z : 𝕜) → I.toInt? v = some z :=
    fun v z h => (I.toInt?_eq _ _).2 h
  have hn := toInt?_val hkn
  have kmn : I.toInt? (env "mn") = some (-n) := T _ _ (by rw [hmn, hn]; push_cast; ring)
  have kmn' : I.toInt? (-env "n") = some (-n) := T _ _ (by rw [hn]; push_cast; ring)
  rcases hkm : I.toInt? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [monoBinomTripleNegFlip, Defined, eval, hkn, kmn, hkm] at h
  rcases hkp : I.toInt? (env "p") with _ | p
  · exfalso
    have h := hF.self_of_nhds
    simp [monoBinomTripleNegFlip, Defined, eval, hkn, kmn, hkp] at h
  rcases hkq : I.toInt? (env "q") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [monoBinomTripleNegFlip, Defined, eval, hkn, kmn, hkq] at h
  rcases hkr : I.toInt? (env "r") with _ | r
  · exfalso
    have h := hF.self_of_nhds
    simp [monoBinomTripleNegFlip, Defined, eval, hkn, kmn, hkr] at h
  have hq := toInt?_val hkq
  have hm := toInt?_val hkm
  have knq : I.toInt? (env "m" + -(env "n" * env "q")) = some (m - n * q) :=
    T _ _ (by rw [hm, hn, hq]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) monoBinomTripleNegFlip.body →
      (m < 0 → w ≠ 0) ∧ (w ≠ 0 ∨ n = 0) ∧ (p < 0 → env "a" + env "b" * w ^ n ≠ 0) ∧
        (q < 0 → env "c" + env "d" * (w ^ n)⁻¹ ≠ 0) ∧ (r < 0 → env "e" + env "f" * w ^ n ≠ 0) := by
    intro w h
    simp [monoBinomTripleNegFlip, Defined, eval, hkn, kmn, hkm, hkp, hkq, hkr] at h
    obtain ⟨⟨⟨h1, h1', h2⟩, h3, h4⟩, -, h5⟩ := h
    refine ⟨h1, ?_, h2, h4, h5⟩
    rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
    · exact Or.inl (h1' hn0)
    · exact Or.inr hn0
    · exact Or.inl (h3 hn0)
  have hflip : ∀ w : 𝕜, (w ≠ 0 ∨ n = 0) → env "c" + env "d" * (w ^ n)⁻¹ ≠ 0 →
      env "d" + env "c" * w ^ n ≠ 0 := by
    intro w hw h0 h1
    apply h0
    rcases hw with hw | rfl
    · have hn' : w ^ n ≠ 0 := zpow_ne_zero n hw
      field_simp
      linear_combination h1
    · simp at h1 ⊢; linear_combination h1
  have hpow : ∀ w : 𝕜, (w ≠ 0 ∨ n = 0) → w ^ (n * q) ≠ 0 := by
    intro w hw
    rcases hw with hw | rfl
    · exact zpow_ne_zero _ hw
    · simp
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [monoBinomTripleNegFlip, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hm0, h0, h2, h4, h5⟩ := hD w hw
    simp [Defined, eval, hkn, hkp, hkq, hkr, knq, toInt?_neg_one]
    have hw' : n < 0 → w ≠ 0 := fun hn0 => h0.resolve_right (by omega)
    have hwm : m < n * q → w ≠ 0 := fun hmq => by
      rcases h0 with hw | hn0
      · exact hw
      · subst hn0; exact hm0 (by simpa using hmq)
    exact ⟨⟨⟨hwm, hw', h2⟩, hw', fun hq0 => hflip w h0 (h4 hq0)⟩, hw', h5⟩
  · exact Eventually.of_forall fun _ => by simp [monoBinomTripleNegFlip, Defined]
  · simp only [monoBinomTripleNegFlip, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (monoBinomTripleNegFlip.integrals.map (·.1)) Φ "x" w)
        monoBinomTripleNegFlip.result) = Φ "I1" := by
      funext w
      simp [monoBinomTripleNegFlip, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    obtain ⟨hm0, h0, -, -, -⟩ := hD t hF.self_of_nhds
    simp [monoBinomTripleNegFlip, eval, hkn, hkm, hkp, hkq, hkr, kmn, knq, toInt?_neg_one]
    left
    rw [show env "c" + env "d" * (t ^ n)⁻¹ = env "c" + env "d" * t ^ (-n) by rw [zpow_neg],
      neg_flip t (env "c") (env "d") n q h0]
    rcases h0 with ht | rfl
    · rw [zpow_sub₀ ht]; ring
    · simp

theorem monoBinomTripleNegFlip_real : monoBinomTripleNegFlip.Holds .real :=
  monoBinomTripleNegFlip_holds Interp.real

theorem monoBinomTripleNegFlip_complex : monoBinomTripleNegFlip.Holds .complex :=
  monoBinomTripleNegFlip_holds Interp.complex


end Proofs

end OSR.IntegrationRec34
