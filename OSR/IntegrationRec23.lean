import OSR.IntegrationRec22

/-!
# Integration (RUBI): splitting a logarithm of a quotient

RUBI 4.16.1 3.3 #15 splits `log(c/(d + e x)) = log(c/(2 d)) + log(2 d/(d + e x))`
under `∫ (a + b log(c/(d + e x)))/(f + g x²)`, given `c/(2 d) > 0`.  Over ℝ
the two logarithms add for nonzero arguments (`Real.log_mul`); over ℂ the
first factor is a positive real, so they add as well
(`Complex.log_ofReal_mul`).  The condition `e² f + d² g = 0` is not needed.

RUBI 4.16.1 1.2.1.2 #101 (`m + 2 p + 3 = 0`, `p < -1`) is proved over ℝ and ℂ:
its derivative identity reduces to `(b + 2 c x)² - 4 c (a + b x + c x²) = b² - 4 a c`.

RUBI 4.16.1 1.2.1.2 #103 is refuted over ℝ and ℂ at `m = p = -1` (allowed by
`m + 2 p + 3 = 0`), `a = b = e = 1`, the other metavariables `0`: the
integrand `1/(x (1 + x))` is defined near `x = 1`, but the result divides by
`m + 1 = 0`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec23

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- log(c/(d + e x)) = log(c/(2 d)) + log(2 d/(d + e x)) over f + g x² -/
def logQuotSplit : CRule where
  id := "integration.log_quotient_split"; legacyId := some "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:15"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1))))))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .mul (.int 2) (.var "d")) (.int (-1))))))) (.var "I1")) (.app2 .mul (.var "b") (.var "I2")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2)))) (.int (-1))))),
    ("I2", (.app2 .mul (.app1 .ln (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1))))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "e") (.int 2)) (.var "f")) (.app2 .mul (.pow (.var "d") (.int 2)) (.var "g"))) (.int 0),
    .gt (.app2 .mul (.var "c") (.pow (.app2 .mul (.int 2) (.var "d")) (.int (-1)))) (.int 0)]
  priority := 4300
  description := "log(c/(d + e x)) = log(c/(2 d)) + log(2 d/(d + e x)) over f + g x²"
  provenance := migrated "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:15" "3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p.m#15"

/-- RUBI 1.2.1.2 #103 -/
def rubi1212r103 : CRule where
  id := "integration.rubi_1_2_1_2_r103"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:103"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.pow (.app2 .mul (.int 2) (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "m", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .ne (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .ne (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3)) (.int 0)]
  priority := 4310
  description := "RUBI 1.2.1.2 #103"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:103" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#103"

/-- (d + e x)^m (a + b x + c x²)^p reduced when m + 2 p + 3 = 0 -/
def linQuadPowEqReduce : CRule where
  id := "integration.linear_quadratic_power_eq_reduction"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:101"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "x")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .add (.var "p") (.int 1)) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "m") (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")))) (.pow (.app2 .mul (.app2 .add (.var "p") (.int 1)) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "m", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .ne (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .ne (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3)) (.int 0),
    .gt (.int (-1)) (.var "p")]
  priority := 4320
  description := "(d + e x)^m (a + b x + c x²)^p reduced when m + 2 p + 3 = 0"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:101" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#101"

/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem toInt?_neg_one (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem toInt?_two (I : Interp 𝕜) : I.toInt? (2 : 𝕜) = some 2 :=
  (I.toInt?_eq _ _).2 (by simp)

/-- **3.3 #15**, in an interpretation whose logarithm adds when the first
factor is positive. -/
theorem logQuotSplit_holds (I : Interp 𝕜)
    (hpos : ∀ p : 𝕜, I.lt 0 p → p ≠ 0 ∧ I.lnDefined p)
    (hsplit : ∀ p q : 𝕜, I.lt 0 p → I.lnDefined (p * q) →
      I.lnDefined q ∧ I.ln (p * q) = I.ln p + I.ln q) :
    AntiderivRecHolds I "x" logQuotSplit.conditions logQuotSplit.body logQuotSplit.result
      logQuotSplit.integrals := by
  intro env hc t hF
  have hgt := hc (.gt (.app2 .mul (.var "c") (.pow (.app2 .mul (.int 2) (.var "d")) (.int (-1))))
    (.int 0)) (by simp [logQuotSplit])
  obtain ⟨hpd, -, hlt⟩ := hgt
  simp [Defined, eval, toInt?_neg_one] at hpd hlt
  have hd : env "d" ≠ 0 := hpd.2
  have hP := hpos _ hlt
  have hD : ∀ w, Defined I (Function.update env "x" w) logQuotSplit.body →
      env "d" + env "e" * w ≠ 0 ∧ I.lnDefined (env "c" * (env "d" + env "e" * w)⁻¹) ∧
        env "f" + env "g" * w ^ 2 ≠ 0 := by
    intro w h
    simp [logQuotSplit, Defined, eval, toInt?_neg_one, toInt?_two] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  have h2 : (2 : 𝕜) ≠ 0 := hpd.1
  have key : ∀ w, env "d" + env "e" * w ≠ 0 → env "c" * (env "d" + env "e" * w)⁻¹ =
      env "c" * ((env "d")⁻¹ * 2⁻¹) * (2 * env "d" * (env "d" + env "e" * w)⁻¹) := by
    intro w hw
    field_simp
    try ring
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [logQuotSplit, List.mem_cons, List.not_mem_nil, or_false] at hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2, h3⟩ := hD w hw
    have hq := (hsplit _ _ hlt (by rw [← key w h1]; exact h2)).1
    rcases hi with rfl | rfl <;> simp [Defined, eval, toInt?_neg_one, toInt?_two, h1, h3, hd]
    exact hq
  · exact Eventually.of_forall fun _ => by
      simp [logQuotSplit, Defined, eval, recEnv, toInt?_neg_one, hd, hP.2]
      exact h2
  · simp only [logQuotSplit, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (logQuotSplit.integrals.map (·.1)) Φ "x" w)
        logQuotSplit.result) = fun w =>
          (env "a" + env "b" * I.ln (env "c" * ((env "d")⁻¹ * 2⁻¹))) * Φ "I1" w +
            env "b" * Φ "I2" w := by
      funext w
      simp [logQuotSplit, eval, recEnv, toInt?_neg_one]
    rw [hfun]
    refine ((hΦ.1.const_mul _).add (hΦ.2.const_mul _)).congr_deriv ?_
    obtain ⟨h1, h2, h3⟩ := hD t hF.self_of_nhds
    have hs := hsplit _ _ hlt (by rw [← key t h1]; exact h2)
    simp [logQuotSplit, eval, toInt?_neg_one, toInt?_two]
    rw [key t h1, hs.2]
    ring

private theorem toInt?_val {I : Interp 𝕜} {v : 𝕜} {k : ℤ} (h : I.toInt? v = some k) :
    v = (k : 𝕜) := (I.toInt?_eq _ _).1 h

private theorem zpow_succ_of (A : 𝕜) (k : ℤ) (h : A ≠ 0 ∨ 0 ≤ k) : A ^ (k + 1) = A ^ k * A := by
  rcases h with h | h
  · exact zpow_add_one₀ h k
  · lift k to ℕ using h
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
      pow_succ]

/-- **1.2.1.2 #101**: `(b + 2 c x)² - 4 c (a + b x + c x²) = b² - 4 a c`. -/
theorem linQuadPowEqReduce_holds [CharZero 𝕜] (I : Interp 𝕜)
    (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" linQuadPowEqReduce.conditions linQuadPowEqReduce.body
      linQuadPowEqReduce.result linQuadPowEqReduce.integrals := by
  intro env hc t hF
  have hΔ := hc (.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul
    (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)) (by simp [linQuadPowEqReduce])
  have hE := hc (.eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p")))
    (.int 3)) (.int 0)) (by simp [linQuadPowEqReduce])
  have hG := hc (.gt (.int (-1)) (.var "p")) (by simp [linQuadPowEqReduce])
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [linQuadPowEqReduce, Defined, eval, hkm] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [linQuadPowEqReduce, Defined, eval, hkp] at h
  have hm := toInt?_val hkm
  have hp := toInt?_val hkp
  have hq1 : q < -1 := by
    have h := hG.2.2
    simp only [eval] at h
    rw [hp] at h
    have h' : I.lt ((q : ℚ) : 𝕜) ((-1 : ℚ) : 𝕜) := by simpa using h
    exact_mod_cast (hlt _ _).1 h'
  have hkq : k = -2 * q - 3 := by
    have h := hE.2.2
    simp [eval, hm, hp] at h
    have h' : ((k + 2 * q + 3 : ℤ) : 𝕜) = 0 := by push_cast; linear_combination h
    have := (Int.cast_eq_zero (α := 𝕜)).1 h'
    omega
  subst hkq
  have hΔv : env "b" ^ 2 + -(4 * env "a" * env "c") ≠ 0 := by
    have h := hΔ.2.2
    simpa [eval, toInt?_two] using h
  have T : ∀ (v : 𝕜) (z : ℤ), v = (z : 𝕜) → I.toInt? v = some z :=
    fun v z h => (I.toInt?_eq _ _).2 h
  have e1 : I.toInt? (env "p" + 1) = some (q + 1) := T _ _ (by rw [hp]; push_cast; ring)
  have e2 : I.toInt? (env "m" + -1) = some (-2 * q - 4) := T _ _ (by rw [hm]; push_cast; ring)
  have e3 : I.toInt? (env "m" - 1) = some (-2 * q - 4) := T _ _ (by rw [hm]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) linQuadPowEqReduce.body →
      env "a" + env "b" * w + env "c" * w ^ 2 ≠ 0 := by
    intro w h
    simp [linQuadPowEqReduce, Defined, eval, hkm, hkp, toInt?_two] at h
    exact h.2 (by omega)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [linQuadPowEqReduce, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hQ := hD w hw
    simp [Defined, eval, e1, e2, e3, toInt?_two, hQ]
    intro h
    omega
  · filter_upwards [hF] with w hw
    have hQ := hD w hw
    simp [linQuadPowEqReduce, Defined, eval, recEnv, hkm, e1, e2, e3, toInt?_two, toInt?_neg_one, hQ,
      hΔv]
    refine ⟨fun h => absurd h (by omega), ?_⟩
    have h1 : ((q + 1 : ℤ) : 𝕜) ≠ 0 := by exact_mod_cast (show q + 1 ≠ 0 by omega)
    rw [hp]
    push_cast at h1
    exact h1
  · simp only [linQuadPowEqReduce, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hQt := hD t hF.self_of_nhds
    have hfun : (fun v => eval I (recEnv env (linQuadPowEqReduce.integrals.map (·.1)) Φ "x" v)
        linQuadPowEqReduce.result) = fun w =>
          (env "d" + env "e" * w) ^ (-2 * q - 3) * (env "b" + 2 * env "c" * w) *
            (env "a" + env "b" * w + env "c" * w ^ 2) ^ (q + 1) *
            ((env "p" + 1) * (env "b" ^ 2 + -(4 * env "a" * env "c")))⁻¹ +
          env "m" * (2 * env "c" * env "d" + -(env "b" * env "e")) *
            ((env "p" + 1) * (env "b" ^ 2 + -(4 * env "a" * env "c")))⁻¹ * Φ "I1" w := by
      funext w
      simp [linQuadPowEqReduce, eval, recEnv, hkm, e1, toInt?_two, toInt?_neg_one]
    rw [hfun]
    have hL : HasDerivAt (fun w => env "d" + env "e" * w) (env "e") t := by
      simpa using ((hasDerivAt_id t).const_mul (env "e")).const_add (env "d")
    have hB : HasDerivAt (fun w => env "b" + 2 * env "c" * w) (2 * env "c") t := by
      simpa using ((hasDerivAt_id t).const_mul (2 * env "c")).const_add (env "b")
    have hQd : HasDerivAt (fun w => env "a" + env "b" * w + env "c" * w ^ 2)
        (env "b" + env "c" * (2 * t)) t := by
      refine ((((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add
        ((hasDerivAt_pow 2 t).const_mul (env "c"))).congr_deriv ?_
      simp
    have hPL := (hasDerivAt_zpow (-2 * q - 3) (env "d" + env "e" * t) (Or.inr (by omega))).comp t hL
    have hPQ := (hasDerivAt_zpow (q + 1) (env "a" + env "b" * t + env "c" * t ^ 2)
      (Or.inl hQt)).comp t hQd
    refine ((((hPL.mul hB).mul hPQ).mul_const _).add (hΦ.const_mul _)).congr_deriv ?_
    have f1 : I.toInt? (-(2 * (q : 𝕜)) - 3 + -1) = some (-2 * q - 4) := T _ _ (by push_cast; ring)
    have f2 : I.toInt? ((q : 𝕜) + 1) = some (q + 1) := T _ _ (by push_cast; ring)
    have f3 : I.toInt? (-(2 * (q : 𝕜)) - 3) = some (-2 * q - 3) := T _ _ (by push_cast; ring)
    simp only [Function.comp_def]
    simp [linQuadPowEqReduce, eval, hkm, hkp, e1, e2, e3, toInt?_two, toInt?_neg_one, hm, hp,
      f1, f2, f3, I.toInt?_cast]
    have hq0 : (q : 𝕜) + 1 ≠ 0 := by
      have h1 : ((q + 1 : ℤ) : 𝕜) ≠ 0 := by exact_mod_cast (show q + 1 ≠ 0 by omega)
      push_cast at h1
      exact h1
    rw [show -(2 * q) - 3 - 1 = -(2 * q) - 4 by ring,
      show -(2 * q) - 3 = -(2 * q) - 4 + 1 by ring,
      zpow_succ_of (env "d" + env "e" * t) _ (Or.inr (by omega)),
      zpow_succ_of (env "a" + env "b" * t + env "c" * t ^ 2) q (Or.inl hQt)]
    have hΔs : env "b" ^ 2 - 4 * env "a" * env "c" ≠ 0 := by
      intro h; apply hΔv; linear_combination h
    have hΔt : -(env "a" * env "c" * 4) + env "b" ^ 2 ≠ 0 := by
      intro h; apply hΔv; linear_combination h
    have hΔu : env "b" ^ 2 + -(env "c" * env "a" * 4) ≠ 0 := by
      intro h; apply hΔv; linear_combination h
    field_simp [hΔv, hΔs, hΔt, hq0]
    ring

theorem linQuadPowEqReduce_real : linQuadPowEqReduce.Holds .real :=
  linQuadPowEqReduce_holds Interp.real Interp.real_lt_rat

theorem linQuadPowEqReduce_complex : linQuadPowEqReduce.Holds .complex :=
  linQuadPowEqReduce_holds Interp.complex Interp.complex_lt_rat

theorem logQuotSplit_real : logQuotSplit.Holds .real := by
  refine logQuotSplit_holds Interp.real (fun p hp => ?_) (fun p q hp hpq => ?_)
  · simp only [Interp.real] at hp ⊢
    exact ⟨hp.ne', hp⟩
  · simp only [Interp.real] at hp hpq ⊢
    have hq : 0 < q := pos_of_mul_pos_right hpq hp.le
    exact ⟨hq, Real.log_mul hp.ne' hq.ne'⟩

theorem logQuotSplit_complex : logQuotSplit.Holds .complex := by
  refine logQuotSplit_holds Interp.complex (fun p hp => ?_) (fun p q hp hpq => ?_)
  · simp only [Interp.complex] at hp ⊢
    obtain ⟨-, him, hre⟩ := hp
    have hp0 : p ≠ 0 := fun h => by simp [h] at hre
    exact ⟨hp0, hp0⟩
  · simp only [Interp.complex] at hp hpq ⊢
    obtain ⟨-, him, hre⟩ := hp
    simp only [Complex.zero_re] at hre
    have hpr : p = ((p.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    have hq : q ≠ 0 := right_ne_zero_of_mul hpq
    refine ⟨hq, ?_⟩
    rw [hpr, Complex.log_ofReal_mul hre hq, Complex.ofReal_log hre.le]

end Proofs

/-! ## Refutations -/

section
variable {α : Type} [Field α] [CharZero α]
private theorem iv0 : intValue? (0 : α) = some 0 := by simpa using intValue?_intCast (α := α) 0
private theorem iv1 : intValue? (1 : α) = some 1 := by simpa using intValue?_intCast (α := α) 1
private theorem iv2 : intValue? (2 : α) = some 2 := by simpa using intValue?_intCast (α := α) 2
private theorem iv3 : intValue? (3 : α) = some 3 := by simpa using intValue?_intCast (α := α) 3
private theorem iv4 : intValue? (4 : α) = some 4 := by simpa using intValue?_intCast (α := α) 4
private theorem ivm1 : intValue? (-1 : α) = some (-1) := by simpa using intValue?_intCast (α := α) (-1)
private theorem ivm2 : intValue? (-2 : α) = some (-2) := by simpa using intValue?_intCast (α := α) (-2)
private theorem ivm3 : intValue? (-3 : α) = some (-3) := by simpa using intValue?_intCast (α := α) (-3)
private theorem ivnat (n : ℕ) [n.AtLeastTwo] : intValue? (OfNat.ofNat n : α) = some (OfNat.ofNat n) := by
  simpa using intValue?_intCast (α := α) (OfNat.ofNat n : ℤ)
private theorem ivneg (n : ℕ) [n.AtLeastTwo] :
    intValue? (-(OfNat.ofNat n : α)) = some (-(OfNat.ofNat n)) := by
  simpa using intValue?_intCast (α := α) (-(OfNat.ofNat n : ℤ))
private theorem ivm6 : intValue? (-6 : α) = some (-6) := by simpa using intValue?_intCast (α := α) (-6)
private theorem ivex2 : ∃ n, intValue? (2 : α) = some n ∧ 0 ≤ n := ⟨2, iv2, by norm_num⟩
private theorem ivexInt (z : ℤ) : ∃ n, intValue? (z : α) = some n := ⟨z, intValue?_intCast z⟩
private theorem ivexm1 : ∃ n, intValue? (-1 : α) = some n := ⟨_, ivm1⟩
private theorem ivm4 : intValue? (-4 : α) = some (-4) := by simpa using intValue?_intCast (α := α) (-4)
private theorem ivexm4 : ∃ n, intValue? (-4 : α) = some n := ⟨_, ivm4⟩
private theorem ivexm6 : ∃ n, intValue? (-6 : α) = some n := ⟨_, ivm6⟩
end

theorem rubi1212r103_counterexample_real : ¬ rubi1212r103.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1212r103.conditions rubi1212r103.body rubi1212r103.result rubi1212r103.integrals
  have hq : ∀ᶠ w in 𝓝 (1 : ℝ), 1 + w ≠ 0 := by
    have hc : ContinuousAt (fun w : ℝ => 1 + w) 1 := by fun_prop
    exact hc.eventually_ne (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "m" ∨ s = "p" then -1 else if s = "a" ∨ s = "b" ∨ s = "e" then 1 else 0) (1 : ℝ) (by simp [rubi1212r103, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num), hq] with w hw hw2; simp [rubi1212r103, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, hw, hw2])
    (fun h w => w * (((rubi1212r103.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "m" ∨ s = "p" then -1 else if s = "a" ∨ s = "b" ∨ s = "e" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1212r103, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1212r103, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1212r103_counterexample_complex : ¬ rubi1212r103.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1212r103.conditions rubi1212r103.body rubi1212r103.result rubi1212r103.integrals
  have hq : ∀ᶠ w in 𝓝 (1 : ℂ), 1 + w ≠ 0 := by
    have hc : ContinuousAt (fun w : ℂ => 1 + w) 1 := by fun_prop
    exact hc.eventually_ne (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "m" ∨ s = "p" then -1 else if s = "a" ∨ s = "b" ∨ s = "e" then 1 else 0) (1 : ℂ) (by simp [rubi1212r103, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num), hq] with w hw hw2; simp [rubi1212r103, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, hw, hw2])
    (fun h w => w * (((rubi1212r103.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "m" ∨ s = "p" then -1 else if s = "a" ∨ s = "b" ∨ s = "e" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1212r103, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1212r103, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

end OSR.IntegrationRec23
