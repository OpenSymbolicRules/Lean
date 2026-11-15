import OSR.IntegrationRec15

/-!
# Integration (RUBI): proofs of rules with `EqQ` conditions

Rules that a numerical check found to behave as identities where they are
defined, proved here over every interpretation having the needed
trigonometric identities.  The rule declarations are transcribed by a tool
and checked by the Integration repository's `scripts/v1_faithfulness.py`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec16

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- (a + b x)^m (c + d x)^n for m + n + 2 = 0 -/
def linLinPow : CRule where
  id := "integration.linear_linear_power"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.2 (a+b x)^m (c+d x)^n:4"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n")))
  result := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.app2 .add (.var "m") (.int 1))) (.int (-1))))
  independent := ["a", "b", "c", "d", "m", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 2)) (.int 0),
    .ne (.var "m") (.int (-1))]
  priority := 3600
  description := "(a + b x)^m (c + d x)^n for m + n + 2 = 0"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.2 (a+b x)^m (c+d x)^n:4" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.2 (a+b x)^m (c+d x)^n.m#4"

/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem toInt?_val {I : Interp 𝕜} {v : 𝕜} {k : ℤ} (h : I.toInt? v = some k) :
    v = (k : 𝕜) := (I.toInt?_eq _ _).1 h

private theorem toInt?_m1 (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

/-- `A^(k+1) = A^k A` when `A ≠ 0` or `k ≥ 0`. -/
private theorem zpow_succ_of (A : 𝕜) (k : ℤ) (h : A ≠ 0 ∨ 0 ≤ k) : A ^ (k + 1) = A ^ k * A := by
  rcases h with h | h
  · exact zpow_add_one₀ h k
  · lift k to ℕ using h
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
      pow_succ]

/-- `((a + b x)^(m+1) (c + d x)^(n+1))' = (m + 1) (b c - a d) (a + b x)^m (c + d x)^n`
when `m + n + 2 = 0`. -/
theorem linLinPow_holds [CharZero 𝕜] (I : Interp 𝕜) :
    AntiderivHoldsUnder I "x" linLinPow.conditions linLinPow.body linLinPow.result := by
  intro env hc t hF
  have hK := hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul
    (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [linLinPow])
  have hE := hc (.eq (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 2)) (.int 0))
    (by simp [linLinPow])
  have hM := hc (.ne (.var "m") (.int (-1))) (by simp [linLinPow])
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [linLinPow, Defined, eval, hkm] at h
  rcases hkn : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [linLinPow, Defined, eval, hkn] at h
  have hm := toInt?_val hkm
  have hn := toInt?_val hkn
  have hjk : j = -k - 2 := by
    have := hE.2.2
    simp [eval, hm, hn] at this
    have h' : ((k + j + 2 : ℤ) : 𝕜) = 0 := by push_cast; linear_combination this
    have := (Int.cast_eq_zero (α := 𝕜)).1 h'
    omega
  subst hjk
  have hk1 : k ≠ -1 := by
    intro h; apply hM.2.2; simp [eval, hm, h]
  have hKv : env "b" * env "c" + -(env "a" * env "d") ≠ 0 := by
    have := hK.2.2; simpa [eval] using this
  have T : ∀ (v : 𝕜) (z : ℤ), v = (z : 𝕜) → I.toInt? v = some z :=
    fun v z h => (I.toInt?_eq _ _).2 h
  have e1 : I.toInt? ((k : 𝕜) + 1) = some (k + 1) := T _ _ (by push_cast; ring)
  have e2 : I.toInt? (-(k : 𝕜) - 2 + 1) = some (-k - 1) := T _ _ (by push_cast; ring)
  have e3 : I.toInt? (-(k : 𝕜) - 2) = some (-k - 2) := T _ _ (by push_cast; ring)
  have e4 : I.toInt? (-1 + -(k : 𝕜)) = some (-1 - k) := T _ _ (by push_cast; ring)
  have e5 : I.toInt? (-2 - (k : 𝕜)) = some (-2 - k) := T _ _ (by push_cast; ring)
  have hm1 : (k : 𝕜) + 1 ≠ 0 := by
    have : (k : 𝕜) + 1 = ((k + 1 : ℤ) : 𝕜) := by push_cast; ring
    rw [this]; exact_mod_cast (show k + 1 ≠ 0 by omega)
  simp only [hm, hn] at hkm hkn
  have hD : ∀ w, Defined I (Function.update env "x" w) linLinPow.body →
      (k < 0 → env "a" + env "b" * w ≠ 0) ∧ (-k - 2 < 0 → env "c" + env "d" * w ≠ 0) := by
    intro w h
    simp [linLinPow, Defined, eval, hm, hn, I.toInt?_cast, e1, e2, e3, e4, e5] at h
    exact ⟨h.1, fun hk => h.2 (by omega)⟩
  have ht := hD t hF.self_of_nhds
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    obtain ⟨hA, hC⟩ := hD w hw
    simp [linLinPow, Defined, eval, hm, hn, I.toInt?_cast, e1, e2, e3, e4, e5, toInt?_m1 I, hKv,
      hm1]
    exact ⟨fun h => hA (by omega), fun h => hC (by omega)⟩
  · have hAt : env "a" + env "b" * t ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (ht.1 h)
      · exact Or.inr (by omega)
    have hCt : env "c" + env "d" * t ≠ 0 ∨ 0 ≤ -k - 2 := by
      by_cases h : -k - 2 < 0
      · exact Or.inl (ht.2 h)
      · exact Or.inr (by omega)
    have hfun : (fun w => eval I (Function.update env "x" w) linLinPow.result) = fun w =>
        (env "a" + env "b" * w) ^ (k + 1) * (env "c" + env "d" * w) ^ (-k - 2 + 1) *
          ((env "b" * env "c" + -(env "a" * env "d")) * ((k : 𝕜) + 1))⁻¹ := by
      funext w
      simp [linLinPow, eval, hm, hn, I.toInt?_cast, e1, e2, e3, e4, e5, toInt?_m1 I]
      try ring_nf
      try simp
    rw [hfun]
    have hA' : HasDerivAt (fun w : 𝕜 => env "a" + env "b" * w) (env "b") t := by
      simpa using ((hasDerivAt_id t).const_mul (env "b")).const_add (env "a")
    have hC' : HasDerivAt (fun w : 𝕜 => env "c" + env "d" * w) (env "d") t := by
      simpa using ((hasDerivAt_id t).const_mul (env "d")).const_add (env "c")
    have hPA := (hasDerivAt_zpow (k + 1) _ (by
      rcases hAt with h | h
      · exact Or.inl h
      · exact Or.inr (by omega))).comp t hA'
    have hPC := (hasDerivAt_zpow (-k - 2 + 1) _ (by
      rcases hCt with h | h
      · exact Or.inl h
      · exact Or.inr (by omega))).comp t hC'
    refine ((hPA.mul hPC).mul_const _).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    simp [linLinPow, eval, hm, hn, I.toInt?_cast, e1, e2, e3, e4, e5]
    rw [zpow_succ_of _ k hAt, zpow_succ_of _ (-k - 2) hCt]
    have hDi := mul_inv_cancel₀ hKv
    have hPi := mul_inv_cancel₀ hm1
    linear_combination ((env "a" + env "b" * t) ^ k * (env "c" + env "d" * t) ^ (-k - 2) *
        ((k : 𝕜) + 1) * ((k : 𝕜) + 1)⁻¹) * hDi +
      ((env "a" + env "b" * t) ^ k * (env "c" + env "d" * t) ^ (-k - 2)) * hPi

theorem linLinPow_real : linLinPow.Holds .real := linLinPow_holds Interp.real

theorem linLinPow_complex : linLinPow.Holds .complex := linLinPow_holds Interp.complex

end Proofs

end OSR.IntegrationRec16
