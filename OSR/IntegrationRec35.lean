import OSR.IntegrationRec34

/-!
# Integration (RUBI): flipping binomials in `xⁿ`

RUBI 4.16.1 1.1.3.5 #42 and 1.1.3.6 #30 rewrite `(a + b xⁿ)^p` as
`x^(n p) (b + a x^(-n))^p` (`pos_flip`, valid for `x ≠ 0` or `n = 0`, which the
integrand guarantees) for the two binomials in `xⁿ`, when the third is in
`x^(-n)`.  Proved over ℝ and ℂ.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec35

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- (a + b x^n)^p (e + f x^n)^r = x^(n (p + r)) (b + a x^(-n))^p (f + e x^(-n))^r under the integral -/
def binomTriplePosFlip : CRule where
  id := "integration.binomial_triple_positive_flip"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:42"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "mn")))) (.var "q"))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.var "n")))) (.var "r")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.var "r")))) (.pow (.app2 .add (.var "b") (.app2 .mul (.var "a") (.pow (.var "x") (.app2 .mul (.int (-1)) (.var "n"))))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.app2 .mul (.int (-1)) (.var "n"))))) (.var "q"))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "e") (.pow (.var "x") (.app2 .mul (.int (-1)) (.var "n"))))) (.var "r"))))]
  independent := ["a", "b", "c", "d", "e", "f", "n", "q", "mn", "p", "r"]
  conditions := [.eq (.var "mn") (.app2 .mul (.int (-1)) (.var "n")),
    .int (.var "p"),
    .int (.var "r")]
  priority := 6400
  description := "(a + b x^n)^p (e + f x^n)^r = x^(n (p + r)) (b + a x^(-n))^p (f + e x^(-n))^r under the integral"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:42" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r.m#42"

/-- x^m (a + b x^n)^p (e + f x^n)^r = x^(m + n (p + r)) (b + a x^(-n))^p (f + e x^(-n))^r under the integral -/
def monoBinomTriplePosFlip : CRule where
  id := "integration.monomial_binomial_triple_positive_flip"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.6 (g x)^m (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:30"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "mn")))) (.var "q"))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.var "n")))) (.var "r")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.var "r"))))) (.pow (.app2 .add (.var "b") (.app2 .mul (.var "a") (.pow (.var "x") (.app2 .mul (.int (-1)) (.var "n"))))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.app2 .mul (.int (-1)) (.var "n"))))) (.var "q"))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "e") (.pow (.var "x") (.app2 .mul (.int (-1)) (.var "n"))))) (.var "r"))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "q", "mn", "p", "r"]
  conditions := [.eq (.var "mn") (.app2 .mul (.int (-1)) (.var "n")),
    .int (.var "p"),
    .int (.var "r")]
  priority := 6410
  description := "x^m (a + b x^n)^p (e + f x^n)^r = x^(m + n (p + r)) (b + a x^(-n))^p (f + e x^(-n))^r under the integral"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.6 (g x)^m (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:30" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.6 (g x)^m (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r.m#30"

/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem toInt?_val {I : Interp 𝕜} {v : 𝕜} {k : ℤ} (h : I.toInt? v = some k) :
    v = (k : 𝕜) := (I.toInt?_eq _ _).1 h

private theorem toInt?_neg_one (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

/-- `(a + b xⁿ)^p = x^(n p) (b + a x^(-n))^p` for `x ≠ 0` or `n = 0`. -/
theorem pos_flip (w a b : 𝕜) (n p : ℤ) (h : w ≠ 0 ∨ n = 0) :
    (a + b * w ^ n) ^ p = w ^ (n * p) * (b + a * w ^ (-n)) ^ p := by
  rcases h with hw | rfl
  · have hn : w ^ n ≠ 0 := zpow_ne_zero n hw
    have h1 : b + a * w ^ (-n) = (a + b * w ^ n) * (w ^ n)⁻¹ := by
      rw [zpow_neg]; field_simp; ring
    have hz : w ^ (n * p) ≠ 0 := zpow_ne_zero _ hw
    rw [h1, mul_zpow, inv_zpow, ← zpow_mul]
    field_simp
  · simp [add_comm]

theorem binomTriplePosFlip_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" binomTriplePosFlip.conditions binomTriplePosFlip.body
      binomTriplePosFlip.result binomTriplePosFlip.integrals := by
  intro env hc t hF
  have heq := hc (.eq (.var "mn") (.app2 .mul (.int (-1)) (.var "n")))
    (by simp [binomTriplePosFlip])
  have hmn : env "mn" = -env "n" := by simpa [Cond.Holds, Defined, eval] using heq.2.2
  rcases hkn : I.toInt? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [binomTriplePosFlip, Defined, eval, hkn] at h
  have T : ∀ (v : 𝕜) (z : ℤ), v = (z : 𝕜) → I.toInt? v = some z :=
    fun v z h => (I.toInt?_eq _ _).2 h
  have hn := toInt?_val hkn
  have kmn : I.toInt? (env "mn") = some (-n) := T _ _ (by rw [hmn, hn]; push_cast; ring)
  have kmn' : I.toInt? (-env "n") = some (-n) := T _ _ (by rw [hn]; push_cast; ring)
  rcases hkp : I.toInt? (env "p") with _ | p
  · exfalso
    have h := hF.self_of_nhds
    simp [binomTriplePosFlip, Defined, eval, hkn, kmn, hkp] at h
  rcases hkq : I.toInt? (env "q") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [binomTriplePosFlip, Defined, eval, hkn, kmn, hkq] at h
  rcases hkr : I.toInt? (env "r") with _ | r
  · exfalso
    have h := hF.self_of_nhds
    simp [binomTriplePosFlip, Defined, eval, hkn, kmn, hkr] at h
  have hp := toInt?_val hkp
  have hr := toInt?_val hkr
  have knpr : I.toInt? (env "n" * (env "p" + env "r")) = some (n * (p + r)) :=
    T _ _ (by rw [hn, hp, hr]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) binomTriplePosFlip.body →
      (w ≠ 0 ∨ n = 0) ∧ (p < 0 → env "a" + env "b" * w ^ n ≠ 0) ∧
        (q < 0 → env "c" + env "d" * (w ^ n)⁻¹ ≠ 0) ∧ (r < 0 → env "e" + env "f" * w ^ n ≠ 0) := by
    intro w h
    simp [binomTriplePosFlip, Defined, eval, hkn, kmn, hkp, hkq, hkr] at h
    obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, -, h5⟩ := h
    refine ⟨?_, h2, h4, h5⟩
    rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
    · exact Or.inl (h1 hn0)
    · exact Or.inr hn0
    · exact Or.inl (h3 hn0)
  have bflip : ∀ w a b : 𝕜, (w ≠ 0 ∨ n = 0) → a + b * w ^ n ≠ 0 → b + a * (w ^ n)⁻¹ ≠ 0 := by
    intro w a b hw h0 h1
    apply h0
    rcases hw with hw | rfl
    · have hn' : w ^ n ≠ 0 := zpow_ne_zero n hw
      field_simp at h1
      linear_combination h1
    · simp at h1 ⊢; linear_combination h1
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [binomTriplePosFlip, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h0, h2, h4, h5⟩ := hD w hw
    simp [Defined, eval, hkn, hkp, hkq, hkr, knpr, kmn', toInt?_neg_one]
    have hw'' : 0 < n → w ≠ 0 := fun hn0 => h0.resolve_right (by omega)
    have hwp : n * (p + r) < 0 → w ≠ 0 := fun h => h0.resolve_right (fun hn => by subst hn; simp at h)
    exact ⟨⟨⟨hwp, hw'', fun hp0 => bflip w _ _ h0 (h2 hp0)⟩, hw'', h4⟩, hw'',
      fun hr0 => bflip w _ _ h0 (h5 hr0)⟩
  · exact Eventually.of_forall fun _ => by simp [binomTriplePosFlip, Defined]
  · simp only [binomTriplePosFlip, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (binomTriplePosFlip.integrals.map (·.1)) Φ "x" w)
        binomTriplePosFlip.result) = Φ "I1" := by
      funext w
      simp [binomTriplePosFlip, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    simp [binomTriplePosFlip, eval, hkn, hkp, hkq, hkr, kmn, kmn', knpr, toInt?_neg_one]
    obtain ⟨h0, -, -, -⟩ := hD t hF.self_of_nhds
    rw [pos_flip t (env "a") (env "b") n p h0, pos_flip t (env "e") (env "f") n r h0]
    simp only [zpow_neg]
    rcases h0 with ht | rfl
    · rw [mul_add, zpow_add₀ ht]; ring
    · simp

theorem binomTriplePosFlip_real : binomTriplePosFlip.Holds .real :=
  binomTriplePosFlip_holds Interp.real

theorem binomTriplePosFlip_complex : binomTriplePosFlip.Holds .complex :=
  binomTriplePosFlip_holds Interp.complex

theorem monoBinomTriplePosFlip_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" monoBinomTriplePosFlip.conditions monoBinomTriplePosFlip.body
      monoBinomTriplePosFlip.result monoBinomTriplePosFlip.integrals := by
  intro env hc t hF
  have heq := hc (.eq (.var "mn") (.app2 .mul (.int (-1)) (.var "n")))
    (by simp [monoBinomTriplePosFlip])
  have hmn : env "mn" = -env "n" := by simpa [Cond.Holds, Defined, eval] using heq.2.2
  rcases hkn : I.toInt? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [monoBinomTriplePosFlip, Defined, eval, hkn] at h
  have T : ∀ (v : 𝕜) (z : ℤ), v = (z : 𝕜) → I.toInt? v = some z :=
    fun v z h => (I.toInt?_eq _ _).2 h
  have hn := toInt?_val hkn
  have kmn : I.toInt? (env "mn") = some (-n) := T _ _ (by rw [hmn, hn]; push_cast; ring)
  have kmn' : I.toInt? (-env "n") = some (-n) := T _ _ (by rw [hn]; push_cast; ring)
  rcases hkm : I.toInt? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [monoBinomTriplePosFlip, Defined, eval, hkn, kmn, hkm] at h
  rcases hkp : I.toInt? (env "p") with _ | p
  · exfalso
    have h := hF.self_of_nhds
    simp [monoBinomTriplePosFlip, Defined, eval, hkn, kmn, hkp] at h
  rcases hkq : I.toInt? (env "q") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [monoBinomTriplePosFlip, Defined, eval, hkn, kmn, hkq] at h
  rcases hkr : I.toInt? (env "r") with _ | r
  · exfalso
    have h := hF.self_of_nhds
    simp [monoBinomTriplePosFlip, Defined, eval, hkn, kmn, hkr] at h
  have hp := toInt?_val hkp
  have hr := toInt?_val hkr
  have hm := toInt?_val hkm
  have knpr : I.toInt? (env "m" + env "n" * (env "p" + env "r")) = some (m + n * (p + r)) :=
    T _ _ (by rw [hm, hn, hp, hr]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) monoBinomTriplePosFlip.body →
      (m < 0 → w ≠ 0) ∧ (w ≠ 0 ∨ n = 0) ∧ (p < 0 → env "a" + env "b" * w ^ n ≠ 0) ∧
        (q < 0 → env "c" + env "d" * (w ^ n)⁻¹ ≠ 0) ∧ (r < 0 → env "e" + env "f" * w ^ n ≠ 0) := by
    intro w h
    simp [monoBinomTriplePosFlip, Defined, eval, hkn, kmn, hkm, hkp, hkq, hkr] at h
    obtain ⟨⟨⟨h1, h1', h2⟩, h3, h4⟩, -, h5⟩ := h
    refine ⟨h1, ?_, h2, h4, h5⟩
    rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
    · exact Or.inl (h1' hn0)
    · exact Or.inr hn0
    · exact Or.inl (h3 hn0)
  have bflip : ∀ w a b : 𝕜, (w ≠ 0 ∨ n = 0) → a + b * w ^ n ≠ 0 → b + a * (w ^ n)⁻¹ ≠ 0 := by
    intro w a b hw h0 h1
    apply h0
    rcases hw with hw | rfl
    · have hn' : w ^ n ≠ 0 := zpow_ne_zero n hw
      field_simp at h1
      linear_combination h1
    · simp at h1 ⊢; linear_combination h1
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [monoBinomTriplePosFlip, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hm0, h0, h2, h4, h5⟩ := hD w hw
    simp [Defined, eval, hkn, hkp, hkq, hkr, knpr, kmn', toInt?_neg_one]
    have hw'' : 0 < n → w ≠ 0 := fun hn0 => h0.resolve_right (by omega)
    have hwp : m + n * (p + r) < 0 → w ≠ 0 := fun h => by
      rcases h0 with hw | hn
      · exact hw
      · subst hn; exact hm0 (by simpa using h)
    exact ⟨⟨⟨hwp, hw'', fun hp0 => bflip w _ _ h0 (h2 hp0)⟩, hw'', h4⟩, hw'',
      fun hr0 => bflip w _ _ h0 (h5 hr0)⟩
  · exact Eventually.of_forall fun _ => by simp [monoBinomTriplePosFlip, Defined]
  · simp only [monoBinomTriplePosFlip, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (monoBinomTriplePosFlip.integrals.map (·.1)) Φ "x" w)
        monoBinomTriplePosFlip.result) = Φ "I1" := by
      funext w
      simp [monoBinomTriplePosFlip, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    simp [monoBinomTriplePosFlip, eval, hkn, hkm, hkp, hkq, hkr, kmn, kmn', knpr, toInt?_neg_one]
    obtain ⟨-, h0, -, -, -⟩ := hD t hF.self_of_nhds
    rw [pos_flip t (env "a") (env "b") n p h0, pos_flip t (env "e") (env "f") n r h0]
    simp only [zpow_neg]
    rcases h0 with ht | rfl
    · rw [zpow_add₀ ht, mul_add, zpow_add₀ ht]; ring
    · simp

theorem monoBinomTriplePosFlip_real : monoBinomTriplePosFlip.Holds .real :=
  monoBinomTriplePosFlip_holds Interp.real

theorem monoBinomTriplePosFlip_complex : monoBinomTriplePosFlip.Holds .complex :=
  monoBinomTriplePosFlip_holds Interp.complex


end Proofs

end OSR.IntegrationRec35
