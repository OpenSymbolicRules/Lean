import OSR.IntegrationRec23

/-!
# Integration (RUBI): a by-parts rule for a product of two binomials

RUBI 4.16.1 1.1.3.2 #69 integrates `x^m (a₁ + b₁ xⁿ)^p (a₂ + b₂ xⁿ)^p` by parts
when `a₂ b₁ + a₁ b₂ = 0` and `(m + 1)/(2 n) + p = 0`, `p > 0`: then
`b₁ (a₂ + b₂ xⁿ) + b₂ (a₁ + b₁ xⁿ) = 2 b₁ b₂ xⁿ`.  The point `x = 0` is never
in the domain: the condition needs `n ≠ 0`, and either `n < 0` or
`m = -2 n p - 1 < 0`.  Proved over ℝ and ℂ.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec24

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- x^m (a1 + b1 x^n)^p (a2 + b2 x^n)^p by parts when a2 b1 + a1 b2 = 0 -/
def monoBinomPairByParts : CRule where
  id := "integration.monomial_binomial_pair_by_parts"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.2 (c x)^m (a+b x^n)^p:69"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "a1") (.app2 .mul (.var "b1") (.pow (.var "x") (.var "n")))) (.var "p"))) (.pow (.app2 .add (.var "a2") (.app2 .mul (.var "b2") (.pow (.var "x") (.var "n")))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a1") (.app2 .mul (.var "b1") (.pow (.var "x") (.var "n")))) (.var "p"))) (.pow (.app2 .add (.var "a2") (.app2 .mul (.var "b2") (.pow (.var "x") (.var "n")))) (.var "p"))) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "b1")) (.var "b2")) (.var "n")) (.var "p")) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "n")))) (.pow (.app2 .add (.var "a1") (.app2 .mul (.var "b1") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a2") (.app2 .mul (.var "b2") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))))]
  independent := ["a1", "b1", "a2", "b2", "m", "n", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "a2") (.var "b1")) (.app2 .mul (.var "a1") (.var "b2"))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.pow (.app2 .mul (.int 2) (.var "n")) (.int (-1)))) (.var "p")) (.int 0),
    .gt (.var "p") (.int 0)]
  priority := 4400
  description := "x^m (a1 + b1 x^n)^p (a2 + b2 x^n)^p by parts when a2 b1 + a1 b2 = 0"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.2 (c x)^m (a+b x^n)^p:69" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.2 (c x)^m (a+b x^n)^p.m#69"

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

private theorem toInt?_val {I : Interp 𝕜} {v : 𝕜} {k : ℤ} (h : I.toInt? v = some k) :
    v = (k : 𝕜) := (I.toInt?_eq _ _).1 h

/-- **1.1.3.2 #69.** -/
theorem monoBinomPairByParts_holds [CharZero 𝕜] (I : Interp 𝕜)
    (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" monoBinomPairByParts.conditions monoBinomPairByParts.body
      monoBinomPairByParts.result monoBinomPairByParts.integrals := by
  intro env hc t hF
  have hE1 := hc (.eq (.app2 .add (.app2 .mul (.var "a2") (.var "b1")) (.app2 .mul (.var "a1")
    (.var "b2"))) (.int 0)) (by simp [monoBinomPairByParts])
  have hE2 := hc (.eq (.app2 .add (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.pow (.app2 .mul
    (.int 2) (.var "n")) (.int (-1)))) (.var "p")) (.int 0)) (by simp [monoBinomPairByParts])
  have hG := hc (.gt (.var "p") (.int 0)) (by simp [monoBinomPairByParts])
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [monoBinomPairByParts, Defined, eval, hkm] at h
  rcases hkn : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [monoBinomPairByParts, Defined, eval, hkn] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [monoBinomPairByParts, Defined, eval, hkp] at h
  have hm := toInt?_val hkm
  have hn := toInt?_val hkn
  have hp := toInt?_val hkp
  have hab : env "a2" * env "b1" + env "a1" * env "b2" = 0 := by
    simpa [Cond.Holds, Defined, eval] using hE1.2.2
  have hq0 : 0 < q := by
    have h := hG.2.2
    simp only [eval] at h
    rw [hp] at h
    have h' : I.lt ((0 : ℚ) : 𝕜) ((q : ℚ) : 𝕜) := by simpa using h
    exact_mod_cast (hlt _ _).1 h'
  have hE2' := hE2
  obtain ⟨hD2, -, hv2⟩ := hE2'
  simp [Defined, eval, toInt?_neg_one] at hD2 hv2
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hD2 (by rw [hn]; simp)
  have hj0' : (j : 𝕜) ≠ 0 := by exact_mod_cast hj0
  have hk : k = -2 * j * q - 1 := by
    rw [hm, hn, hp] at hv2
    field_simp at hv2
    have h' : ((k + 1 + 2 * j * q : ℤ) : 𝕜) = 0 := by
      push_cast
      linear_combination hv2
    have := (Int.cast_eq_zero (α := 𝕜)).1 h'
    linear_combination this
  subst hk
  have T : ∀ (v : 𝕜) (z : ℤ), v = (z : 𝕜) → I.toInt? v = some z :=
    fun v z h => (I.toInt?_eq _ _).2 h
  have hX : ∀ w, Defined I (Function.update env "x" w) monoBinomPairByParts.body → w ≠ 0 := by
    intro w h hw
    subst hw
    simp [monoBinomPairByParts, Defined, eval, hkm, hkn, hkp] at h
    obtain ⟨⟨h1, h2, -⟩, -⟩ := h
    nlinarith
  have e1 : I.toInt? (env "m" + 1) = some (-2 * j * q - 1 + 1) := T _ _ (by rw [hm]; push_cast; ring)
  have e2 : I.toInt? (env "m" + 2 * env "n") = some (-2 * j * q - 1 + 2 * j) :=
    T _ _ (by rw [hm, hn]; push_cast; ring)
  have e3 : I.toInt? (env "p" + -1) = some (q - 1) := T _ _ (by rw [hp]; push_cast; ring)
  have e4 : I.toInt? (env "p" - 1) = some (q - 1) := T _ _ (by rw [hp]; push_cast; ring)
  have hm1 : env "m" + 1 ≠ 0 := by
    rw [hm]
    have : ((-2 * j * q - 1 + 1 : ℤ) : 𝕜) ≠ 0 := by
      have : -2 * j * q - 1 + 1 ≠ 0 := by
        have := mul_ne_zero hj0 (ne_of_gt hq0)
        intro h; apply this; linarith
      exact_mod_cast this
    push_cast at this ⊢
    exact this
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [monoBinomPairByParts, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h0 := hX w hw
    simp [Defined, eval, hkn, e2, e3, e4, h0]
    exact ⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
  · filter_upwards [hF] with w hw
    have h0 := hX w hw
    simp [monoBinomPairByParts, Defined, eval, recEnv, hkn, hkp, e1, toInt?_neg_one, h0, hm1]
    exact ⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
  · simp only [monoBinomPairByParts, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have ht0 := hX t hF.self_of_nhds
    have hfun : (fun v => eval I (recEnv env (monoBinomPairByParts.integrals.map (·.1)) Φ "x" v)
        monoBinomPairByParts.result) = fun w =>
          w ^ (-2 * j * q - 1 + 1) * (env "a1" + env "b1" * w ^ j) ^ q *
            (env "a2" + env "b2" * w ^ j) ^ q * (env "m" + 1)⁻¹ +
          -1 * 2 * env "b1" * env "b2" * env "n" * env "p" * (env "m" + 1)⁻¹ * Φ "I1" w := by
      funext w
      simp [monoBinomPairByParts, eval, recEnv, hkn, hkp, e1, toInt?_neg_one]
    rw [hfun]
    have hN := hasDerivAt_zpow j t (Or.inl ht0)
    have hA := (hN.const_mul (env "b1")).const_add (env "a1")
    have hB := (hN.const_mul (env "b2")).const_add (env "a2")
    have hAq := (hasDerivAt_zpow q _ (Or.inr hq0.le)).comp t hA
    have hBq := (hasDerivAt_zpow q _ (Or.inr hq0.le)).comp t hB
    have hX1 := hasDerivAt_zpow (-2 * j * q - 1 + 1) t (Or.inl ht0)
    refine ((((hX1.mul hAq).mul hBq).mul_const _).add (hΦ.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def]
    have f1 : I.toInt? (-(2 * (j : 𝕜) * q) - 1 + 2 * j) = some (-(2 * j * q) - 1 + 2 * j) :=
      T _ _ (by push_cast; ring)
    have f2 : I.toInt? ((q : 𝕜) + -1) = some (q - 1) := T _ _ (by push_cast; ring)
    have f3 : I.toInt? (-(2 * (j : 𝕜) * q) - 1) = some (-(2 * j * q) - 1) :=
      T _ _ (by push_cast; ring)
    simp [monoBinomPairByParts, eval, hkm, hkn, hkp, e2, e3, e4, hm, hn, hp, I.toInt?_cast,
      f1, f2, f3]
    have hq0' : (q : 𝕜) ≠ 0 := by exact_mod_cast hq0.ne'
    have r1 : (t ^ (2 * j * q))⁻¹ = t ^ (-(2 * j * q) - 1) * t := by
      rw [← zpow_neg, ← zpow_add_one₀ ht0]; ring_nf
    have r2 : t ^ (j - 1) = t ^ j * t⁻¹ := zpow_sub_one₀ ht0 j
    have r3 : t ^ (-(2 * j * q) - 1 + 2 * j) = t ^ (-(2 * j * q) - 1) * t ^ j * t ^ j := by
      rw [zpow_add₀ ht0, show 2 * j = j + j by ring, zpow_add₀ ht0]; ring
    have r4 : ∀ A : 𝕜, A ^ q = A ^ (q - 1) * A := fun A => by
      have := zpow_succ_of A (q - 1) (Or.inr (by omega))
      rwa [sub_add_cancel] at this
    rw [r1, r2, r3, r4 (env "a1" + env "b1" * t ^ j), r4 (env "a2" + env "b2" * t ^ j)]
    field_simp
    linear_combination (-((env "a1" + env "b1" * t ^ j) ^ (q - 1) *
      (env "a2" + t ^ j * env "b2") ^ (q - 1) * t ^ j)) * hab

theorem monoBinomPairByParts_real : monoBinomPairByParts.Holds .real :=
  monoBinomPairByParts_holds Interp.real Interp.real_lt_rat

theorem monoBinomPairByParts_complex : monoBinomPairByParts.Holds .complex :=
  monoBinomPairByParts_holds Interp.complex Interp.complex_lt_rat

end Proofs

end OSR.IntegrationRec24
