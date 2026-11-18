import OSR.IntegrationRec91

/-!
# Integration (RUBI): 1.2.1.2 #93, #94 and #95

Reduction rules for `∫ (d + e x)^m (a + b x + c x²)^p` when `m + 2 p + 2 = 0`.
The derivative identity is polynomial once `m = -2 p - 2` is substituted
(checked exactly with Giac).  For #93 and #94 (`p > 0`, so `m < 0`) the
integrand forces `d + e x ≠ 0`; for #95 (`p < -1`, so `m ≥ 2`) every power of
`d + e x` that occurs has a nonnegative exponent.  Proved over ℝ and ℂ, as
RUBI states them.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec119

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 1.2.1.2 #93 -/
def rubi1212r93 : CRule where
  id := "integration.rubi_1_2_1_2_r93"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:93"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1)))) (.app2 .add (.app2 .add (.app2 .mul (.var "d") (.var "b")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "a")) (.var "e"))) (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.var "x")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "p") (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 2))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))))]
  independent := ["a", "b", "c", "d", "e", "m", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .ne (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .ne (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2)) (.int 0),
    .gt (.var "p") (.int 0)]
  priority := 9401
  description := "RUBI 1.2.1.2 #93"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:93" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#93"

/-- RUBI 1.2.1.2 #94 -/
def rubi1212r94 : CRule where
  id := "integration.rubi_1_2_1_2_r94"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:94"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1)))) (.app2 .add (.app2 .mul (.app2 .mul (.int (-2)) (.var "a")) (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.var "x")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")) (.var "p")) (.pow (.app2 .mul (.app2 .mul (.int 2) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))))]
  independent := ["a", "c", "d", "e", "m", "p"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2)) (.int 0),
    .gt (.var "p") (.int 0)]
  priority := 9402
  description := "RUBI 1.2.1.2 #94"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:94" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#94"

/-- RUBI 1.2.1.2 #95 -/
def rubi1212r95 : CRule where
  id := "integration.rubi_1_2_1_2_r95"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:95"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.app2 .add (.app2 .add (.app2 .mul (.var "d") (.var "b")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "a")) (.var "e"))) (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.var "x")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .add (.var "p") (.int 1)) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3))) (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))))) (.pow (.app2 .mul (.app2 .add (.var "p") (.int 1)) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "m", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .ne (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .ne (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2)) (.int 0),
    .gt (.int (-1)) (.var "p")]
  priority := 9403
  description := "RUBI 1.2.1.2 #95"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:95" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#95"

/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem toInt?_two (I : Interp 𝕜) : I.toInt? (2 : 𝕜) = some 2 :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem toInt?_neg_one (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem zpow_succ_of (A : 𝕜) (k : ℤ) (h : A ≠ 0 ∨ 0 ≤ k) : A ^ (k + 1) = A ^ k * A := by
  rcases h with h | h
  · exact zpow_add_one₀ h k
  · lift k to ℕ using h
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
      pow_succ]

theorem rubi1212r93_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (hint : ∀ n : ℤ, n ≠ 0 → 1 ≤ ‖(n : 𝕜)‖) :
    AntiderivRecHolds I "x" rubi1212r93.conditions rubi1212r93.body rubi1212r93.result rubi1212r93.integrals := by
  intro env hc t hF
  have ord : ∀ (x y : ℤ), I.lt (x : 𝕜) (y : 𝕜) → x < y := by
    intro x y h
    have h' : I.lt ((x : ℚ) : 𝕜) ((y : ℚ) : 𝕜) := by rw [Rat.cast_intCast, Rat.cast_intCast]; exact h
    exact_mod_cast (hlt _ _).1 h'
  have icast : ∀ n : ℤ, n ≠ 0 → (n : 𝕜) ≠ 0 := by
    intro n hn h; have := hint n hn; rw [h, norm_zero] at this; linarith
  have hdisc0 := hc (.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)) (by simp [rubi1212r93])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hdisc0
  have hdisc : (env "b" ^ 2 + -1 * 4 * env "a" * env "c") ≠ 0 := by intro h0; apply hdisc0; linear_combination h0
  have hD0 := hc (.ne (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1212r93])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hD0
  have hD : (env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2) ≠ 0 := by intro h0; apply hD0; linear_combination h0
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi1212r93, Defined, eval, hk_m] at h
  rcases hk_p : I.toInt? (env "p") with _ | q
  · exfalso; have h := hF.self_of_nhds; simp [rubi1212r93, Defined, eval, hk_m, hk_p] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have h_p : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have hkq : k = -2 * q - 2 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2)) (.int 0)) (by simp [rubi1212r93])
    simp [Cond.Holds, Defined, eval, h_m, h_p] at h
    have : ((k + 2 * q + 2 : ℤ) : 𝕜) = 0 := by push_cast; linear_combination h
    have := (icast (k + 2 * q + 2)).mt (not_not.2 this)
    omega
  have hq : 0 < q := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi1212r93])
    simp only [Cond.Holds, Defined, eval, true_and] at h; rw [h_p] at h; exact ord _ _ (by simpa using h)
  have h2 : (2 : 𝕜) ≠ 0 := by have := icast 2 (by norm_num); push_cast at this; exact this
  have hk1 : (k : 𝕜) + 1 ≠ 0 := by
    have := icast (k + 1) (by omega); push_cast at this; exact this
  have hq1 : (q : 𝕜) + 1 ≠ 0 := by
    have := icast (q + 1) (by omega); push_cast at this; exact this
  have hm1' : env "m" + 1 ≠ 0 := by rw [h_m]; exact hk1
  have hp1' : env "p" + 1 ≠ 0 := by rw [h_p]; exact hq1
  have em1 : I.toInt? (env "m" + 1) = some (k + 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em2 : I.toInt? (env "m" + 2) = some (k + 2) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em1' : I.toInt? (env "m" + -1 * 1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em2' : I.toInt? (env "m" + -1 * 2) = some (k - 2) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em1'' : I.toInt? (env "m" + -1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em2'' : I.toInt? (env "m" + -2) = some (k - 2) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have ep1 : I.toInt? (env "p" + -1 * 1) = some (q - 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have ep1' : I.toInt? (env "p" + -1) = some (q - 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have ep2 : I.toInt? (env "p" + 1) = some (q + 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have hk0 : k < 0 := by omega
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi1212r93.body → (env "d" + env "e" * w) ≠ 0 := by
    intro w h
    simp [rubi1212r93, Defined, eval, hk_m, hk_p, toInt?_two, hk0] at h
    first | exact h | exact h.1 | tauto
  have hL0 := hBody t hF.self_of_nhds
  have eL1 : (env "d" + env "e" * t) ^ (k + 1) = (env "d" + env "e" * t) ^ k * (env "d" + env "e" * t) := zpow_add_one₀ hL0 k
  have eL2 : (env "d" + env "e" * t) ^ (k + 2) = (env "d" + env "e" * t) ^ k * (env "d" + env "e" * t) * (env "d" + env "e" * t) := by
    rw [← zpow_add_one₀ hL0, ← zpow_add_one₀ hL0]; congr 1; ring
  have eP1 : (env "a" + env "b" * t + env "c" * t ^ 2) ^ q = (env "a" + env "b" * t + env "c" * t ^ 2) ^ (q - 1) * (env "a" + env "b" * t + env "c" * t ^ 2) := by
    rw [← zpow_succ_of _ _ (Or.inr (by omega))]; congr 1; ring
  have hLor : (env "d" + env "e" * t) ≠ 0 ∨ 0 ≤ k + 1 := Or.inl hL0
  have hPor : (env "a" + env "b" * t + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ q := Or.inr (by omega)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1212r93, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h1 := hBody w hw
    simp [Defined, eval, hk_m, hk_p, em1, em2, em1', em2', em1'', em2'', ep1, ep1', ep2, toInt?_two, h1, show ¬ q < 0 by omega, show ¬ q - 1 < 0 by omega, show k < 0 by omega, show k + 1 < 0 by omega, show k + 2 < 0 by omega]
    first | done | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    have h1 := hBody w hw
    simp [rubi1212r93, Defined, eval, recEnv, hk_m, hk_p, em1, em2, em1', em2', em1'', em2'', ep1, ep1', ep2, toInt?_two, toInt?_neg_one, h1, hdisc, hD, hdisc0, hD0, hk1, hq1, hm1', hp1', h2, show ¬ q < 0 by omega, show ¬ q - 1 < 0 by omega, show k < 0 by omega, show k + 1 < 0 by omega, show k + 2 < 0 by omega]
    first | done | (trace_state; sorry)
  · simp only [rubi1212r93, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (rubi1212r93.integrals.map (·.1)) Φ "x" w) rubi1212r93.result) =
        fun w => (-1 * (2 * (env "m" + 1) * (env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2))⁻¹) * (env "d" + env "e" * w) ^ (k + 1) * (env "d" * env "b" + -1 * 2 * env "a" * env "e" + (2 * env "c" * env "d" + -1 * env "b" * env "e") * w) * (env "a" + env "b" * w + env "c" * w ^ 2) ^ (q) + (env "p" * (env "b" ^ 2 + -1 * 4 * env "a" * env "c") * (2 * (env "m" + 1) * (env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi1212r93, eval, recEnv, hk_m, hk_p, em1, em2, em1', em2', em1'', em2'', ep1, ep1', ep2, toInt?_two, toInt?_neg_one, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | (trace_state; sorry)
    have hEF : eval I (Function.update env "x" t) rubi1212r93.body = (env "d" + env "e" * t) ^ k * (env "a" + env "b" * t + env "c" * t ^ 2) ^ q := by
      simp [rubi1212r93, eval, hk_m, hk_p, toInt?_two]
    rw [hfun, hEF]
    have hl : HasDerivAt (fun w => (env "d" + env "e" * w)) (env "e") t := by
      simpa using ((hasDerivAt_id t).const_mul (env "e")).const_add (env "d")
    have hA : HasDerivAt (fun w => (env "d" * env "b" + -1 * 2 * env "a" * env "e" + (2 * env "c" * env "d" + -1 * env "b" * env "e") * w)) (2 * env "c" * env "d" + -1 * env "b" * env "e") t := by
      have := ((hasDerivAt_id t).const_mul (2 * env "c" * env "d" + -1 * env "b" * env "e")).const_add (env "d" * env "b" + -1 * 2 * env "a" * env "e")
      first | (convert this using 1 <;> simp) | (convert this using 1 <;> first | (funext w; simp; ring) | simp | ring)
    have hp : HasDerivAt (fun w => (env "a" + env "b" * w + env "c" * w ^ 2)) (env "b" + 2 * env "c" * t) t := by
      have h2 := (hasDerivAt_id t).pow 2
      convert ((((hasDerivAt_id t).const_mul (env "b")).const_add (env "a")).add (h2.const_mul (env "c"))) using 1 <;> first | (funext w; simp) | (simp; ring)
    have hLk := (hasDerivAt_zpow (k + 1) _ hLor).comp t hl
    have hPq := (hasDerivAt_zpow (q) _ hPor).comp t hp
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t) ^ (k + 2) * (env "a" + env "b" * t + env "c" * t ^ 2) ^ (q - 1)) t := by
      convert hΦ using 1
      simp [eval, hk_m, hk_p, em1, em2, em1', em2', em1'', em2'', ep1, ep1', ep2, toInt?_two]
    refine ((((hLk.const_mul (-1 * (2 * (env "m" + 1) * (env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2))⁻¹)).mul hA).mul hPq).add (hΦ'.const_mul (env "p" * (env "b" ^ 2 + -1 * 4 * env "a" * env "c") * (2 * (env "m" + 1) * (env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2))⁻¹))).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, add_sub_cancel_right]
    rw [eL1, eL2, eP1]
    try rw [h_m]
    try rw [h_p]
    generalize (env "d" + env "e" * t) ^ k = Lk
    generalize (env "a" + env "b" * t + env "c" * t ^ 2) ^ (q - 1) = Pk
    generalize hhdisce : (env "b" ^ 2 + -1 * 4 * env "a" * env "c") = hdiscX at hdisc ⊢
    generalize hhDe : (env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2) = hDX at hD ⊢
    field_simp
    subst hhdisce
    subst hhDe
    subst hkq
    push_cast
    ring

theorem rubi1212r94_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (hint : ∀ n : ℤ, n ≠ 0 → 1 ≤ ‖(n : 𝕜)‖) :
    AntiderivRecHolds I "x" rubi1212r94.conditions rubi1212r94.body rubi1212r94.result rubi1212r94.integrals := by
  intro env hc t hF
  have ord : ∀ (x y : ℤ), I.lt (x : 𝕜) (y : 𝕜) → x < y := by
    intro x y h
    have h' : I.lt ((x : ℚ) : 𝕜) ((y : ℚ) : 𝕜) := by rw [Rat.cast_intCast, Rat.cast_intCast]; exact h
    exact_mod_cast (hlt _ _).1 h'
  have icast : ∀ n : ℤ, n ≠ 0 → (n : 𝕜) ≠ 0 := by
    intro n hn h; have := hint n hn; rw [h, norm_zero] at this; linarith
  have hD0 := hc (.ne (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1212r94])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hD0
  have hD : (env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2) ≠ 0 := by intro h0; apply hD0; linear_combination h0
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi1212r94, Defined, eval, hk_m] at h
  rcases hk_p : I.toInt? (env "p") with _ | q
  · exfalso; have h := hF.self_of_nhds; simp [rubi1212r94, Defined, eval, hk_m, hk_p] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have h_p : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have hkq : k = -2 * q - 2 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2)) (.int 0)) (by simp [rubi1212r94])
    simp [Cond.Holds, Defined, eval, h_m, h_p] at h
    have : ((k + 2 * q + 2 : ℤ) : 𝕜) = 0 := by push_cast; linear_combination h
    have := (icast (k + 2 * q + 2)).mt (not_not.2 this)
    omega
  have hq : 0 < q := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi1212r94])
    simp only [Cond.Holds, Defined, eval, true_and] at h; rw [h_p] at h; exact ord _ _ (by simpa using h)
  have h2 : (2 : 𝕜) ≠ 0 := by have := icast 2 (by norm_num); push_cast at this; exact this
  have hk1 : (k : 𝕜) + 1 ≠ 0 := by
    have := icast (k + 1) (by omega); push_cast at this; exact this
  have hq1 : (q : 𝕜) + 1 ≠ 0 := by
    have := icast (q + 1) (by omega); push_cast at this; exact this
  have hm1' : env "m" + 1 ≠ 0 := by rw [h_m]; exact hk1
  have hp1' : env "p" + 1 ≠ 0 := by rw [h_p]; exact hq1
  have em1 : I.toInt? (env "m" + 1) = some (k + 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em2 : I.toInt? (env "m" + 2) = some (k + 2) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em1' : I.toInt? (env "m" + -1 * 1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em2' : I.toInt? (env "m" + -1 * 2) = some (k - 2) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em1'' : I.toInt? (env "m" + -1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em2'' : I.toInt? (env "m" + -2) = some (k - 2) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have ep1 : I.toInt? (env "p" + -1 * 1) = some (q - 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have ep1' : I.toInt? (env "p" + -1) = some (q - 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have ep2 : I.toInt? (env "p" + 1) = some (q + 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have hk0 : k < 0 := by omega
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi1212r94.body → (env "d" + env "e" * w) ≠ 0 := by
    intro w h
    simp [rubi1212r94, Defined, eval, hk_m, hk_p, toInt?_two, hk0] at h
    first | exact h | exact h.1 | tauto
  have hL0 := hBody t hF.self_of_nhds
  have eL1 : (env "d" + env "e" * t) ^ (k + 1) = (env "d" + env "e" * t) ^ k * (env "d" + env "e" * t) := zpow_add_one₀ hL0 k
  have eL2 : (env "d" + env "e" * t) ^ (k + 2) = (env "d" + env "e" * t) ^ k * (env "d" + env "e" * t) * (env "d" + env "e" * t) := by
    rw [← zpow_add_one₀ hL0, ← zpow_add_one₀ hL0]; congr 1; ring
  have eP1 : (env "a" + env "c" * t ^ 2) ^ q = (env "a" + env "c" * t ^ 2) ^ (q - 1) * (env "a" + env "c" * t ^ 2) := by
    rw [← zpow_succ_of _ _ (Or.inr (by omega))]; congr 1; ring
  have hLor : (env "d" + env "e" * t) ≠ 0 ∨ 0 ≤ k + 1 := Or.inl hL0
  have hPor : (env "a" + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ q := Or.inr (by omega)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1212r94, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h1 := hBody w hw
    simp [Defined, eval, hk_m, hk_p, em1, em2, em1', em2', em1'', em2'', ep1, ep1', ep2, toInt?_two, h1, show ¬ q < 0 by omega, show ¬ q - 1 < 0 by omega, show k < 0 by omega, show k + 1 < 0 by omega, show k + 2 < 0 by omega]
    first | done | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    have h1 := hBody w hw
    simp [rubi1212r94, Defined, eval, recEnv, hk_m, hk_p, em1, em2, em1', em2', em1'', em2'', ep1, ep1', ep2, toInt?_two, toInt?_neg_one, h1, hD, hD0, hk1, hq1, hm1', hp1', h2, show ¬ q < 0 by omega, show ¬ q - 1 < 0 by omega, show k < 0 by omega, show k + 1 < 0 by omega, show k + 2 < 0 by omega]
    first | done | (trace_state; sorry)
  · simp only [rubi1212r94, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (rubi1212r94.integrals.map (·.1)) Φ "x" w) rubi1212r94.result) =
        fun w => (-1 * (2 * (env "m" + 1) * (env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2))⁻¹) * (env "d" + env "e" * w) ^ (k + 1) * (-2 * env "a" * env "e" + 2 * env "c" * env "d" * w) * (env "a" + env "c" * w ^ 2) ^ (q) + (-1 * 4 * env "a" * env "c" * env "p" * (2 * (env "m" + 1) * (env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi1212r94, eval, recEnv, hk_m, hk_p, em1, em2, em1', em2', em1'', em2'', ep1, ep1', ep2, toInt?_two, toInt?_neg_one, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | (trace_state; sorry)
    have hEF : eval I (Function.update env "x" t) rubi1212r94.body = (env "d" + env "e" * t) ^ k * (env "a" + env "c" * t ^ 2) ^ q := by
      simp [rubi1212r94, eval, hk_m, hk_p, toInt?_two]
    rw [hfun, hEF]
    have hl : HasDerivAt (fun w => (env "d" + env "e" * w)) (env "e") t := by
      simpa using ((hasDerivAt_id t).const_mul (env "e")).const_add (env "d")
    have hA : HasDerivAt (fun w => (-2 * env "a" * env "e" + 2 * env "c" * env "d" * w)) (2 * env "c" * env "d") t := by
      have := ((hasDerivAt_id t).const_mul (2 * env "c" * env "d")).const_add (-2 * env "a" * env "e")
      first | (convert this using 1 <;> simp) | (convert this using 1 <;> first | (funext w; simp; ring) | simp | ring)
    have hp : HasDerivAt (fun w => (env "a" + env "c" * w ^ 2)) (2 * env "c" * t) t := by
      have h2 := (hasDerivAt_id t).pow 2
      convert ((h2.const_mul (env "c")).const_add (env "a")) using 1 <;> first | (funext w; simp) | (simp; ring)
    have hLk := (hasDerivAt_zpow (k + 1) _ hLor).comp t hl
    have hPq := (hasDerivAt_zpow (q) _ hPor).comp t hp
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t) ^ (k + 2) * (env "a" + env "c" * t ^ 2) ^ (q - 1)) t := by
      convert hΦ using 1
      simp [eval, hk_m, hk_p, em1, em2, em1', em2', em1'', em2'', ep1, ep1', ep2, toInt?_two]
    refine ((((hLk.const_mul (-1 * (2 * (env "m" + 1) * (env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2))⁻¹)).mul hA).mul hPq).add (hΦ'.const_mul (-1 * 4 * env "a" * env "c" * env "p" * (2 * (env "m" + 1) * (env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2))⁻¹))).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, add_sub_cancel_right]
    rw [eL1, eL2, eP1]
    try rw [h_m]
    try rw [h_p]
    generalize (env "d" + env "e" * t) ^ k = Lk
    generalize (env "a" + env "c" * t ^ 2) ^ (q - 1) = Pk
    generalize hhDe : (env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2) = hDX at hD ⊢
    field_simp
    subst hhDe
    subst hkq
    push_cast
    ring

theorem rubi1212r95_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (hint : ∀ n : ℤ, n ≠ 0 → 1 ≤ ‖(n : 𝕜)‖) :
    AntiderivRecHolds I "x" rubi1212r95.conditions rubi1212r95.body rubi1212r95.result rubi1212r95.integrals := by
  intro env hc t hF
  have ord : ∀ (x y : ℤ), I.lt (x : 𝕜) (y : 𝕜) → x < y := by
    intro x y h
    have h' : I.lt ((x : ℚ) : 𝕜) ((y : ℚ) : 𝕜) := by rw [Rat.cast_intCast, Rat.cast_intCast]; exact h
    exact_mod_cast (hlt _ _).1 h'
  have icast : ∀ n : ℤ, n ≠ 0 → (n : 𝕜) ≠ 0 := by
    intro n hn h; have := hint n hn; rw [h, norm_zero] at this; linarith
  have hdisc0 := hc (.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)) (by simp [rubi1212r95])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hdisc0
  have hdisc : (env "b" ^ 2 + -1 * 4 * env "a" * env "c") ≠ 0 := by intro h0; apply hdisc0; linear_combination h0
  have hD0 := hc (.ne (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1212r95])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hD0
  have hD : (env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2) ≠ 0 := by intro h0; apply hD0; linear_combination h0
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi1212r95, Defined, eval, hk_m] at h
  rcases hk_p : I.toInt? (env "p") with _ | q
  · exfalso; have h := hF.self_of_nhds; simp [rubi1212r95, Defined, eval, hk_m, hk_p] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have h_p : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have hkq : k = -2 * q - 2 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2)) (.int 0)) (by simp [rubi1212r95])
    simp [Cond.Holds, Defined, eval, h_m, h_p] at h
    have : ((k + 2 * q + 2 : ℤ) : 𝕜) = 0 := by push_cast; linear_combination h
    have := (icast (k + 2 * q + 2)).mt (not_not.2 this)
    omega
  have hq : q < -1 := by
    have h := hc (.gt (.int (-1)) (.var "p")) (by simp [rubi1212r95])
    simp only [Cond.Holds, Defined, eval, true_and] at h; rw [h_p] at h; exact ord _ _ (by simpa using h)
  have h2 : (2 : 𝕜) ≠ 0 := by have := icast 2 (by norm_num); push_cast at this; exact this
  have hk1 : (k : 𝕜) + 1 ≠ 0 := by
    have := icast (k + 1) (by omega); push_cast at this; exact this
  have hq1 : (q : 𝕜) + 1 ≠ 0 := by
    have := icast (q + 1) (by omega); push_cast at this; exact this
  have hm1' : env "m" + 1 ≠ 0 := by rw [h_m]; exact hk1
  have hp1' : env "p" + 1 ≠ 0 := by rw [h_p]; exact hq1
  have em1 : I.toInt? (env "m" + 1) = some (k + 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em2 : I.toInt? (env "m" + 2) = some (k + 2) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em1' : I.toInt? (env "m" + -1 * 1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em2' : I.toInt? (env "m" + -1 * 2) = some (k - 2) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em1'' : I.toInt? (env "m" + -1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em2'' : I.toInt? (env "m" + -2) = some (k - 2) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have ep1 : I.toInt? (env "p" + -1 * 1) = some (q - 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have ep1' : I.toInt? (env "p" + -1) = some (q - 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have ep2 : I.toInt? (env "p" + 1) = some (q + 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have hk0 : 2 ≤ k := by omega
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi1212r95.body → (env "a" + env "b" * w + env "c" * w ^ 2) ≠ 0 := by
    intro w h
    simp [rubi1212r95, Defined, eval, hk_m, hk_p, toInt?_two, show ¬ k < 0 by omega, show q < 0 by omega] at h
    first | exact h | exact h.2 | tauto
  have hP0 := hBody t hF.self_of_nhds
  have eL1 : (env "d" + env "e" * t) ^ (k - 1) = (env "d" + env "e" * t) ^ (k - 2) * (env "d" + env "e" * t) := by
    rw [← zpow_succ_of _ _ (Or.inr (by omega))]; congr 1; ring
  have eL0 : (env "d" + env "e" * t) ^ (k - 1 - 1) = (env "d" + env "e" * t) ^ (k - 2) := by congr 1; ring
  have eLk : (env "d" + env "e" * t) ^ k = (env "d" + env "e" * t) ^ (k - 2) * (env "d" + env "e" * t) * (env "d" + env "e" * t) := by
    rw [← zpow_succ_of _ _ (Or.inr (by omega)), ← zpow_succ_of _ _ (Or.inr (by omega))]; congr 1; ring
  have eP1 : (env "a" + env "b" * t + env "c" * t ^ 2) ^ (q + 1) = (env "a" + env "b" * t + env "c" * t ^ 2) ^ q * (env "a" + env "b" * t + env "c" * t ^ 2) := zpow_succ_of _ _ (Or.inl hP0)
  have hLor : (env "d" + env "e" * t) ≠ 0 ∨ 0 ≤ k - 1 := Or.inr (by omega)
  have hPor : (env "a" + env "b" * t + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ q + 1 := Or.inl hP0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1212r95, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h1 := hBody w hw
    simp [Defined, eval, hk_m, hk_p, em1, em2, em1', em2', em1'', em2'', ep1, ep1', ep2, toInt?_two, h1, show ¬ k < 0 by omega, show ¬ k - 1 < 0 by omega, show ¬ k - 2 < 0 by omega, show q < 0 by omega, show q + 1 < 0 by omega]
    first | done | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    have h1 := hBody w hw
    simp [rubi1212r95, Defined, eval, recEnv, hk_m, hk_p, em1, em2, em1', em2', em1'', em2'', ep1, ep1', ep2, toInt?_two, toInt?_neg_one, h1, hdisc, hD, hdisc0, hD0, hk1, hq1, hm1', hp1', h2, show ¬ k < 0 by omega, show ¬ k - 1 < 0 by omega, show ¬ k - 2 < 0 by omega, show q < 0 by omega, show q + 1 < 0 by omega]
    first | done | (trace_state; sorry)
  · simp only [rubi1212r95, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (rubi1212r95.integrals.map (·.1)) Φ "x" w) rubi1212r95.result) =
        fun w => (((env "p" + 1) * (env "b" ^ 2 + -1 * 4 * env "a" * env "c"))⁻¹) * (env "d" + env "e" * w) ^ (k - 1) * (env "d" * env "b" + -1 * 2 * env "a" * env "e" + (2 * env "c" * env "d" + -1 * env "b" * env "e") * w) * (env "a" + env "b" * w + env "c" * w ^ 2) ^ (q + 1) + (-1 * 2 * (2 * env "p" + 3) * (env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2) * ((env "p" + 1) * (env "b" ^ 2 + -1 * 4 * env "a" * env "c"))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi1212r95, eval, recEnv, hk_m, hk_p, em1, em2, em1', em2', em1'', em2'', ep1, ep1', ep2, toInt?_two, toInt?_neg_one, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | (trace_state; sorry)
    have hEF : eval I (Function.update env "x" t) rubi1212r95.body = (env "d" + env "e" * t) ^ k * (env "a" + env "b" * t + env "c" * t ^ 2) ^ q := by
      simp [rubi1212r95, eval, hk_m, hk_p, toInt?_two]
    rw [hfun, hEF]
    have hl : HasDerivAt (fun w => (env "d" + env "e" * w)) (env "e") t := by
      simpa using ((hasDerivAt_id t).const_mul (env "e")).const_add (env "d")
    have hA : HasDerivAt (fun w => (env "d" * env "b" + -1 * 2 * env "a" * env "e" + (2 * env "c" * env "d" + -1 * env "b" * env "e") * w)) (2 * env "c" * env "d" + -1 * env "b" * env "e") t := by
      have := ((hasDerivAt_id t).const_mul (2 * env "c" * env "d" + -1 * env "b" * env "e")).const_add (env "d" * env "b" + -1 * 2 * env "a" * env "e")
      first | (convert this using 1 <;> simp) | (convert this using 1 <;> first | (funext w; simp; ring) | simp | ring)
    have hp : HasDerivAt (fun w => (env "a" + env "b" * w + env "c" * w ^ 2)) (env "b" + 2 * env "c" * t) t := by
      have h2 := (hasDerivAt_id t).pow 2
      convert ((((hasDerivAt_id t).const_mul (env "b")).const_add (env "a")).add (h2.const_mul (env "c"))) using 1 <;> first | (funext w; simp) | (simp; ring)
    have hLk := (hasDerivAt_zpow (k - 1) _ hLor).comp t hl
    have hPq := (hasDerivAt_zpow (q + 1) _ hPor).comp t hp
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t) ^ (k - 2) * (env "a" + env "b" * t + env "c" * t ^ 2) ^ (q + 1)) t := by
      convert hΦ using 1
      simp [eval, hk_m, hk_p, em1, em2, em1', em2', em1'', em2'', ep1, ep1', ep2, toInt?_two]
    refine ((((hLk.const_mul (((env "p" + 1) * (env "b" ^ 2 + -1 * 4 * env "a" * env "c"))⁻¹)).mul hA).mul hPq).add (hΦ'.const_mul (-1 * 2 * (2 * env "p" + 3) * (env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2) * ((env "p" + 1) * (env "b" ^ 2 + -1 * 4 * env "a" * env "c"))⁻¹))).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, add_sub_cancel_right]
    rw [eL0, eL1, eLk, eP1]
    try rw [h_m]
    try rw [h_p]
    generalize (env "d" + env "e" * t) ^ (k - 2) = Lk
    generalize (env "a" + env "b" * t + env "c" * t ^ 2) ^ q = Pk
    generalize hhdisce : (env "b" ^ 2 + -1 * 4 * env "a" * env "c") = hdiscX at hdisc ⊢
    generalize hhDe : (env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2) = hDX at hD ⊢
    field_simp
    subst hhdisce
    subst hhDe
    subst hkq
    push_cast
    ring

theorem rubi1212r93_real : rubi1212r93.Holds .real :=
  rubi1212r93_holds Interp.real Interp.real_lt_rat (fun n hn => by rw [Int.norm_cast_real, Int.norm_eq_abs]; exact_mod_cast Int.one_le_abs hn)
theorem rubi1212r93_complex : rubi1212r93.Holds .complex :=
  rubi1212r93_holds Interp.complex Interp.complex_lt_rat (fun n hn => by
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real, Int.norm_cast_real, Int.norm_eq_abs]
    exact_mod_cast Int.one_le_abs hn)
theorem rubi1212r94_real : rubi1212r94.Holds .real :=
  rubi1212r94_holds Interp.real Interp.real_lt_rat (fun n hn => by rw [Int.norm_cast_real, Int.norm_eq_abs]; exact_mod_cast Int.one_le_abs hn)
theorem rubi1212r94_complex : rubi1212r94.Holds .complex :=
  rubi1212r94_holds Interp.complex Interp.complex_lt_rat (fun n hn => by
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real, Int.norm_cast_real, Int.norm_eq_abs]
    exact_mod_cast Int.one_le_abs hn)
theorem rubi1212r95_real : rubi1212r95.Holds .real :=
  rubi1212r95_holds Interp.real Interp.real_lt_rat (fun n hn => by rw [Int.norm_cast_real, Int.norm_eq_abs]; exact_mod_cast Int.one_le_abs hn)
theorem rubi1212r95_complex : rubi1212r95.Holds .complex :=
  rubi1212r95_holds Interp.complex Interp.complex_lt_rat (fun n hn => by
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real, Int.norm_cast_real, Int.norm_eq_abs]
    exact_mod_cast Int.one_le_abs hn)

end Proofs

end OSR.IntegrationRec119
