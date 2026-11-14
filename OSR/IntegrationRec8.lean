import OSR.IntegrationRec7

/-!
# Integration (RUBI): reduction of `x^m sinᵖ(a + b xⁿ)` and `x^m cosᵖ(a + b xⁿ)` by parts

Rules that a numerical check found to behave as identities where they are
defined, proved here over every interpretation having the needed
trigonometric identities.  The rule declarations are transcribed by a tool
and checked by the Integration repository's `scripts/v1_faithfulness.py`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec8

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- x^m sin(a + b x^n)^p reduced by parts twice, for m < -2n + 1 -/
def powSinPowReduce : CRule where
  id := "integration.power_sin_power_reduction"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:47"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p")))
  result := (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 1))) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p"))) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "n")) (.var "p")) (.pow (.var "x") (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1)))) (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))))) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.pow (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.var "p")) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "n")))) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p")))),
    ("I2", (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "n")))) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2))))))]
  independent := ["a", "b", "m", "n", "p"]
  conditions := [.gt (.var "p") (.int 1),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .int (.var "m"),
    .gt (.app2 .add (.app2 .mul (.int (-2)) (.var "n")) (.int 1)) (.var "m"),
    .ne (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1)) (.int 0)]
  priority := 2700
  description := "x^m sin(a + b x^n)^p reduced by parts twice, for m < -2n + 1"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:47" "4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p.m#47"

/-- x^m cos(a + b x^n)^p reduced by parts twice, for m < -2n + 1 -/
def powCosPowReduce : CRule where
  id := "integration.power_cos_power_reduction"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:48"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p")))
  result := (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 1))) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p"))) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "p")) (.pow (.var "x") (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1)))) (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))))) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.pow (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.var "p")) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "n")))) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p")))),
    ("I2", (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "n")))) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2))))))]
  independent := ["a", "b", "m", "n", "p"]
  conditions := [.gt (.var "p") (.int 1),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .int (.var "m"),
    .gt (.app2 .add (.app2 .mul (.int (-2)) (.var "n")) (.int 1)) (.var "m"),
    .ne (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1)) (.int 0)]
  priority := 2710
  description := "x^m cos(a + b x^n)^p reduced by parts twice, for m < -2n + 1"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:48" "4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p.m#48"

/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem toInt?_val {I : Interp 𝕜} {v : 𝕜} {k : ℤ} (h : I.toInt? v = some k) :
    v = (k : 𝕜) := (I.toInt?_eq _ _).1 h

private theorem toInt?_m1 (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem toInt?_2 (I : Interp 𝕜) : I.toInt? (2 : 𝕜) = some 2 :=
  (I.toInt?_eq _ _).2 (by simp)

/-- `∫ x^m sinᵖ(a + b xⁿ)` integrated by parts twice, for integers `p ≥ 2`,
`n > 0`, `m < -2n + 1` and `m + n + 1 ≠ 0`. -/
theorem powSinPowReduce_holds [CharZero 𝕜] (I : Interp 𝕜)
    (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (hs : ∀ u : 𝕜, HasDerivAt I.sin (I.cos u) u)
    (hc : ∀ u : 𝕜, HasDerivAt I.cos (-I.sin u) u)
    (hsc : ∀ u : 𝕜, I.sin u ^ 2 + I.cos u ^ 2 = 1) :
    AntiderivRecHolds I "x" powSinPowReduce.conditions powSinPowReduce.body
      powSinPowReduce.result powSinPowReduce.integrals := by
  intro env hcond t hF
  have hgp := hcond (.gt (.var "p") (.int 1)) (by simp [powSinPowReduce])
  have hgn := hcond (.gt (.var "n") (.int 0)) (by simp [powSinPowReduce])
  have hgm := hcond (.gt (.app2 .add (.app2 .mul (.int (-2)) (.var "n")) (.int 1)) (.var "m"))
    (by simp [powSinPowReduce])
  have hne := hcond (.ne (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1)) (.int 0))
    (by simp [powSinPowReduce])
  rcases hkm : I.toInt? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [powSinPowReduce, Defined, eval, hkm] at h
  rcases hkn : I.toInt? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [powSinPowReduce, Defined, eval, hkn] at h
  rcases hkp : I.toInt? (env "p") with _ | p
  · exfalso
    have h := hF.self_of_nhds
    simp [powSinPowReduce, Defined, eval, hkp] at h
  have hm := toInt?_val hkm
  have hn := toInt?_val hkn
  have hp := toInt?_val hkp
  have hplt : 1 < p := by
    simp only [Cond.Holds, Defined, eval, true_and] at hgp
    rw [hp] at hgp
    have h' : I.lt ((1 : ℚ) : 𝕜) ((p : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_one]; simpa using hgp
    exact_mod_cast (hlt _ _).1 h'
  have hnpos : 0 < n := by
    simp only [Cond.Holds, Defined, eval, true_and] at hgn
    rw [hn] at hgn
    have h' : I.lt ((0 : ℚ) : 𝕜) ((n : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_zero]; simpa using hgn
    exact_mod_cast (hlt _ _).1 h'
  have hmlt : m < -2 * n + 1 := by
    simp only [Cond.Holds, Defined, eval, true_and] at hgm
    rw [hm, hn] at hgm
    have h' : I.lt ((m : ℚ) : 𝕜) (((-2 * n + 1 : ℤ) : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; push_cast; simpa using hgm
    exact_mod_cast (hlt _ _).1 h'
  have hmn1' : (m : 𝕜) + n + 1 ≠ 0 := by
    have := hne.2.2
    simpa [eval, hm, hn] using this
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = k + 2 := ⟨(p - 2).toNat, by omega⟩
  have hm1' : (m : 𝕜) + 1 ≠ 0 := by
    have : (m : 𝕜) + 1 = ((m + 1 : ℤ) : 𝕜) := by push_cast; ring
    rw [this]; exact_mod_cast (show m + 1 ≠ 0 by omega)
  have T : ∀ (v : 𝕜) (z : ℤ), v = (z : 𝕜) → I.toInt? v = some z :=
    fun v z h => (I.toInt?_eq _ _).2 h
  have e1 : I.toInt? ((m : 𝕜) + 1) = some (m + 1) := T _ _ (by push_cast; ring)
  have e2 : I.toInt? ((m : 𝕜) + n + 1) = some (m + n + 1) := T _ _ (by push_cast; ring)
  have e3 : I.toInt? ((m : 𝕜) + 2 * n) = some (m + 2 * n) := T _ _ (by push_cast; ring)
  have e4 : I.toInt? ((k : 𝕜) + 2 + -1) = some (k + 1) := T _ _ (by push_cast; ring)
  have e5 : I.toInt? ((k : 𝕜) + 2 - 1) = some (k + 1) := T _ _ (by push_cast; ring)
  have e6 : I.toInt? ((k : 𝕜) + 2 + -2) = some k := T _ _ (by push_cast; ring)
  have e7 : I.toInt? ((k : 𝕜) + 2 - 2) = some k := T _ _ (by push_cast; ring)
  have e8 : I.toInt? ((k : 𝕜) + 1) = some (k + 1) := T _ _ (by push_cast; ring)
  have e9 : I.toInt? (k : 𝕜) = some k := T _ _ (by push_cast; ring)
  have e10 : I.toInt? ((k : 𝕜) + 2) = some (k + 2) := T _ _ (by push_cast; ring)
  have z2 : ∀ x : 𝕜, x ^ ((k : ℤ) + 2) = x ^ (k + 2) := fun x => by
    rw [show ((k : ℤ) + 2) = ((k + 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have z1 : ∀ x : 𝕜, x ^ ((k : ℤ) + 1) = x ^ (k + 1) := fun x => by
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have hk2 : ¬ ((k : ℤ) + 2 < 0) := by omega
  have hk1 : ¬ ((k : ℤ) + 1 < 0) := by omega
  have hD : ∀ w, Defined I (Function.update env "x" w) powSinPowReduce.body → w ≠ 0 := by
    intro w h
    simp [powSinPowReduce, Defined, eval, hkm, hkn, hkp] at h
    exact h.1 (by omega)
  have ht0 := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [powSinPowReduce, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    all_goals
      filter_upwards [hF] with w hw
      have hw0 := hD w hw
      simp [Defined, eval, hm, hn, hp, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, I.toInt?_cast, hk1, hk2, toInt?_2 I,
        toInt?_m1 I, hw0]
  · filter_upwards [hF] with w hw
    have hw0 := hD w hw
    simp [powSinPowReduce, Defined, eval, recEnv, toInt?_m1 I, toInt?_2 I, hw0, hm, hn, hp,
      e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, I.toInt?_cast, hk1, hk2, hm1', hmn1', zpow_ne_zero]
  · simp only [powSinPowReduce, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hfun : (fun w => eval I (recEnv env (powSinPowReduce.integrals.map (·.1)) Φ "x" w)
        powSinPowReduce.result) = fun w =>
          w ^ (m + 1) * I.sin (env "a" + env "b" * w ^ n) ^ (k + 2) * ((m : 𝕜) + 1)⁻¹ +
          -1 * env "b" * (n : 𝕜) * ((k : 𝕜) + 2) * w ^ (m + n + 1) *
            I.cos (env "a" + env "b" * w ^ n) * I.sin (env "a" + env "b" * w ^ n) ^ (k + 1) *
            (((m : 𝕜) + 1) * ((m : 𝕜) + n + 1))⁻¹ +
          -1 * env "b" ^ 2 * (n : 𝕜) ^ 2 * ((k : 𝕜) + 2) ^ 2 *
            (((m : 𝕜) + 1) * ((m : 𝕜) + n + 1))⁻¹ * Φ "I1" w +
          env "b" ^ 2 * (n : 𝕜) ^ 2 * ((k : 𝕜) + 2) * ((k : 𝕜) + 2 - 1) *
            (((m : 𝕜) + 1) * ((m : 𝕜) + n + 1))⁻¹ * Φ "I2" w := by
      funext w
      simp [powSinPowReduce, eval, recEnv, toInt?_m1 I, toInt?_2 I, hm, hn, hp, e1, e2, e3, e4,
        e5, e6, e7, e8, e9, e10, I.toInt?_cast, hk1, hk2, z1, z2]
      try ring_nf
      try simp
    rw [hfun]
    set u : 𝕜 → 𝕜 := fun w => env "a" + env "b" * w ^ n with hu
    have hU : HasDerivAt u (env "b" * ((n : 𝕜) * t ^ (n - 1))) t := by
      have := ((hasDerivAt_zpow n t (Or.inl ht0)).const_mul (env "b")).const_add (env "a")
      convert this using 1
    have hA : HasDerivAt (fun w : 𝕜 => w ^ (m + 1)) (((m : 𝕜) + 1) * t ^ m) t := by
      have := hasDerivAt_zpow (m + 1) t (Or.inl ht0)
      convert this using 1; push_cast; simp
    have hB : HasDerivAt (fun w : 𝕜 => w ^ (m + n + 1)) (((m : 𝕜) + n + 1) * t ^ (m + n)) t := by
      have := hasDerivAt_zpow (m + n + 1) t (Or.inl ht0)
      convert this using 1; push_cast; simp
    have hS : HasDerivAt (fun w => I.sin (u w)) (I.cos (u t) * (env "b" * ((n : 𝕜) * t ^ (n - 1)))) t :=
      (hs (u t)).comp t hU
    have hC : HasDerivAt (fun w => I.cos (u w)) (-I.sin (u t) * (env "b" * ((n : 𝕜) * t ^ (n - 1)))) t :=
      (hc (u t)).comp t hU
    have hS2 := hS.pow (k + 2)
    have hS1 := hS.pow (k + 1)
    simp only [Nat.add_sub_cancel, show k + 2 - 1 = k + 1 by omega] at hS2 hS1
    refine (((((hA.mul hS2).mul_const _).add
      ((((hB.const_mul (-1 * env "b" * (n : 𝕜) * ((k : 𝕜) + 2))).mul hC).mul hS1).mul_const _)).add
      (hΦ1.const_mul _)).add (hΦ2.const_mul _)).congr_deriv ?_
    simp [powSinPowReduce, eval, hm, hn, hp, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, I.toInt?_cast, hk1, hk2, z1, z2,
      toInt?_2 I, toInt?_m1 I, u]
    have h2n : t ^ (2 * n) = t ^ n * t ^ n := by rw [two_mul, zpow_add₀ ht0]
    simp only [zpow_add₀ ht0, zpow_sub_one₀ ht0, zpow_one, h2n]
    have h1 := mul_inv_cancel₀ hm1'
    have h2 := mul_inv_cancel₀ hmn1'
    have h3 := mul_inv_cancel₀ ht0
    have hsc' := hsc (env "a" + env "b" * t ^ n)
    set s := I.sin (env "a" + env "b" * t ^ n)
    set c := I.cos (env "a" + env "b" * t ^ n)
    set X := t ^ m
    set Y := t ^ n
    set ti := t⁻¹
    set i1 := ((m : 𝕜) + 1)⁻¹
    set i2 := ((m : 𝕜) + n + 1)⁻¹
    set K := (k : 𝕜)
    set N := (n : 𝕜)
    set M := (m : 𝕜)
    set B := env "b"
    linear_combination (-X*s ^ k*(-K^2*N*Y^2*B^2*c^2*i2*t*ti - K^2*N*Y^2*B^2*i2*s^2 + K^2*N*Y^2*B^2*i2 - 3*K*N*Y^2*B^2*c^2*i2*t*ti + K*N*Y^2*B^2*i2*s^2*t*ti - 4*K*N*Y^2*B^2*i2*s^2 + 3*K*N*Y^2*B^2*i2 - 2*N*Y^2*B^2*c^2*i2*t*ti + 2*N*Y^2*B^2*i2*s^2*t*ti - 4*N*Y^2*B^2*i2*s^2 + 2*N*Y^2*B^2*i2 - s^2)) * h1 +
      (X*Y*B*s ^ k*(K + 2)*(-K*N*Y*B*c^2*i1*t*ti - K*N*Y*B*i1*s^2 + K*N*Y*B*i1 + K*Y*B*c^2*t*ti + K*Y*B*s^2 - K*Y*B - N*Y*B*c^2*i1*t*ti + N*Y*B*i1*s^2*t*ti - 2*N*Y*B*i1*s^2 + N*Y*B*i1 - N*c*i1*s + Y*B*c^2*t*ti - Y*B*s^2*t*ti + 2*Y*B*s^2 - Y*B)) * h2 +
      (X*Y*B*s ^ k*(K + 2)*(-K*M*Y*B*c^2*i2 - K*N*Y*B*c^2*i1 - K*Y*B*c^2*i2 + K*Y*B*c^2 - M*Y*B*c^2*i2 + M*Y*B*i2*s^2 - N*Y*B*c^2*i1 + N*Y*B*i1*s^2 + N*c*i1*s - Y*B*c^2*i2 + Y*B*c^2 + Y*B*i2*s^2 - Y*B*s^2)) * h3 +
      (-X*Y^2*B^2*s ^ k*(K + 1)*(K + 2)*(M*i2 + N*i1 + i2 - 1)) * hsc'

theorem powSinPowReduce_real : powSinPowReduce.Holds .real :=
  powSinPowReduce_holds Interp.real Interp.real_lt_rat Real.hasDerivAt_sin Real.hasDerivAt_cos
    Real.sin_sq_add_cos_sq

theorem powSinPowReduce_complex : powSinPowReduce.Holds .complex :=
  powSinPowReduce_holds Interp.complex Interp.complex_lt_rat Complex.hasDerivAt_sin
    Complex.hasDerivAt_cos Complex.sin_sq_add_cos_sq

/-- `∫ x^m cosᵖ(a + b xⁿ)` integrated by parts twice, for integers `p ≥ 2`,
`n > 0`, `m < -2n + 1` and `m + n + 1 ≠ 0`. -/
theorem powCosPowReduce_holds [CharZero 𝕜] (I : Interp 𝕜)
    (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (hs : ∀ u : 𝕜, HasDerivAt I.sin (I.cos u) u)
    (hc : ∀ u : 𝕜, HasDerivAt I.cos (-I.sin u) u)
    (hsc : ∀ u : 𝕜, I.sin u ^ 2 + I.cos u ^ 2 = 1) :
    AntiderivRecHolds I "x" powCosPowReduce.conditions powCosPowReduce.body
      powCosPowReduce.result powCosPowReduce.integrals := by
  intro env hcond t hF
  have hgp := hcond (.gt (.var "p") (.int 1)) (by simp [powCosPowReduce])
  have hgn := hcond (.gt (.var "n") (.int 0)) (by simp [powCosPowReduce])
  have hgm := hcond (.gt (.app2 .add (.app2 .mul (.int (-2)) (.var "n")) (.int 1)) (.var "m"))
    (by simp [powCosPowReduce])
  have hne := hcond (.ne (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1)) (.int 0))
    (by simp [powCosPowReduce])
  rcases hkm : I.toInt? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [powCosPowReduce, Defined, eval, hkm] at h
  rcases hkn : I.toInt? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [powCosPowReduce, Defined, eval, hkn] at h
  rcases hkp : I.toInt? (env "p") with _ | p
  · exfalso
    have h := hF.self_of_nhds
    simp [powCosPowReduce, Defined, eval, hkp] at h
  have hm := toInt?_val hkm
  have hn := toInt?_val hkn
  have hp := toInt?_val hkp
  have hplt : 1 < p := by
    simp only [Cond.Holds, Defined, eval, true_and] at hgp
    rw [hp] at hgp
    have h' : I.lt ((1 : ℚ) : 𝕜) ((p : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_one]; simpa using hgp
    exact_mod_cast (hlt _ _).1 h'
  have hnpos : 0 < n := by
    simp only [Cond.Holds, Defined, eval, true_and] at hgn
    rw [hn] at hgn
    have h' : I.lt ((0 : ℚ) : 𝕜) ((n : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_zero]; simpa using hgn
    exact_mod_cast (hlt _ _).1 h'
  have hmlt : m < -2 * n + 1 := by
    simp only [Cond.Holds, Defined, eval, true_and] at hgm
    rw [hm, hn] at hgm
    have h' : I.lt ((m : ℚ) : 𝕜) (((-2 * n + 1 : ℤ) : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; push_cast; simpa using hgm
    exact_mod_cast (hlt _ _).1 h'
  have hmn1' : (m : 𝕜) + n + 1 ≠ 0 := by
    have := hne.2.2
    simpa [eval, hm, hn] using this
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = k + 2 := ⟨(p - 2).toNat, by omega⟩
  have hm1' : (m : 𝕜) + 1 ≠ 0 := by
    have : (m : 𝕜) + 1 = ((m + 1 : ℤ) : 𝕜) := by push_cast; ring
    rw [this]; exact_mod_cast (show m + 1 ≠ 0 by omega)
  have T : ∀ (v : 𝕜) (z : ℤ), v = (z : 𝕜) → I.toInt? v = some z :=
    fun v z h => (I.toInt?_eq _ _).2 h
  have e1 : I.toInt? ((m : 𝕜) + 1) = some (m + 1) := T _ _ (by push_cast; ring)
  have e2 : I.toInt? ((m : 𝕜) + n + 1) = some (m + n + 1) := T _ _ (by push_cast; ring)
  have e3 : I.toInt? ((m : 𝕜) + 2 * n) = some (m + 2 * n) := T _ _ (by push_cast; ring)
  have e4 : I.toInt? ((k : 𝕜) + 2 + -1) = some (k + 1) := T _ _ (by push_cast; ring)
  have e5 : I.toInt? ((k : 𝕜) + 2 - 1) = some (k + 1) := T _ _ (by push_cast; ring)
  have e6 : I.toInt? ((k : 𝕜) + 2 + -2) = some k := T _ _ (by push_cast; ring)
  have e7 : I.toInt? ((k : 𝕜) + 2 - 2) = some k := T _ _ (by push_cast; ring)
  have e8 : I.toInt? ((k : 𝕜) + 1) = some (k + 1) := T _ _ (by push_cast; ring)
  have e9 : I.toInt? (k : 𝕜) = some k := T _ _ (by push_cast; ring)
  have e10 : I.toInt? ((k : 𝕜) + 2) = some (k + 2) := T _ _ (by push_cast; ring)
  have z2 : ∀ x : 𝕜, x ^ ((k : ℤ) + 2) = x ^ (k + 2) := fun x => by
    rw [show ((k : ℤ) + 2) = ((k + 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have z1 : ∀ x : 𝕜, x ^ ((k : ℤ) + 1) = x ^ (k + 1) := fun x => by
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have hk2 : ¬ ((k : ℤ) + 2 < 0) := by omega
  have hk1 : ¬ ((k : ℤ) + 1 < 0) := by omega
  have hD : ∀ w, Defined I (Function.update env "x" w) powCosPowReduce.body → w ≠ 0 := by
    intro w h
    simp [powCosPowReduce, Defined, eval, hkm, hkn, hkp] at h
    exact h.1 (by omega)
  have ht0 := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [powCosPowReduce, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    all_goals
      filter_upwards [hF] with w hw
      have hw0 := hD w hw
      simp [Defined, eval, hm, hn, hp, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, I.toInt?_cast, hk1, hk2, toInt?_2 I,
        toInt?_m1 I, hw0]
  · filter_upwards [hF] with w hw
    have hw0 := hD w hw
    simp [powCosPowReduce, Defined, eval, recEnv, toInt?_m1 I, toInt?_2 I, hw0, hm, hn, hp,
      e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, I.toInt?_cast, hk1, hk2, hm1', hmn1', zpow_ne_zero]
  · simp only [powCosPowReduce, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hfun : (fun w => eval I (recEnv env (powCosPowReduce.integrals.map (·.1)) Φ "x" w)
        powCosPowReduce.result) = fun w =>
          w ^ (m + 1) * I.cos (env "a" + env "b" * w ^ n) ^ (k + 2) * ((m : 𝕜) + 1)⁻¹ +
          env "b" * (n : 𝕜) * ((k : 𝕜) + 2) * w ^ (m + n + 1) *
            I.sin (env "a" + env "b" * w ^ n) * I.cos (env "a" + env "b" * w ^ n) ^ (k + 1) *
            (((m : 𝕜) + 1) * ((m : 𝕜) + n + 1))⁻¹ +
          -1 * env "b" ^ 2 * (n : 𝕜) ^ 2 * ((k : 𝕜) + 2) ^ 2 *
            (((m : 𝕜) + 1) * ((m : 𝕜) + n + 1))⁻¹ * Φ "I1" w +
          env "b" ^ 2 * (n : 𝕜) ^ 2 * ((k : 𝕜) + 2) * ((k : 𝕜) + 2 - 1) *
            (((m : 𝕜) + 1) * ((m : 𝕜) + n + 1))⁻¹ * Φ "I2" w := by
      funext w
      simp [powCosPowReduce, eval, recEnv, toInt?_m1 I, toInt?_2 I, hm, hn, hp, e1, e2, e3, e4,
        e5, e6, e7, e8, e9, e10, I.toInt?_cast, hk1, hk2, z1, z2]
      try ring_nf
      try simp
    rw [hfun]
    set u : 𝕜 → 𝕜 := fun w => env "a" + env "b" * w ^ n with hu
    have hU : HasDerivAt u (env "b" * ((n : 𝕜) * t ^ (n - 1))) t := by
      have := ((hasDerivAt_zpow n t (Or.inl ht0)).const_mul (env "b")).const_add (env "a")
      convert this using 1
    have hA : HasDerivAt (fun w : 𝕜 => w ^ (m + 1)) (((m : 𝕜) + 1) * t ^ m) t := by
      have := hasDerivAt_zpow (m + 1) t (Or.inl ht0)
      convert this using 1; push_cast; simp
    have hB : HasDerivAt (fun w : 𝕜 => w ^ (m + n + 1)) (((m : 𝕜) + n + 1) * t ^ (m + n)) t := by
      have := hasDerivAt_zpow (m + n + 1) t (Or.inl ht0)
      convert this using 1; push_cast; simp
    have hS : HasDerivAt (fun w => I.sin (u w)) (I.cos (u t) * (env "b" * ((n : 𝕜) * t ^ (n - 1)))) t :=
      (hs (u t)).comp t hU
    have hC : HasDerivAt (fun w => I.cos (u w)) (-I.sin (u t) * (env "b" * ((n : 𝕜) * t ^ (n - 1)))) t :=
      (hc (u t)).comp t hU
    have hS2 := hC.pow (k + 2)
    have hS1 := hC.pow (k + 1)
    simp only [Nat.add_sub_cancel, show k + 2 - 1 = k + 1 by omega] at hS2 hS1
    refine (((((hA.mul hS2).mul_const _).add
      ((((hB.const_mul (env "b" * (n : 𝕜) * ((k : 𝕜) + 2))).mul hS).mul hS1).mul_const _)).add
      (hΦ1.const_mul _)).add (hΦ2.const_mul _)).congr_deriv ?_
    simp [powCosPowReduce, eval, hm, hn, hp, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, I.toInt?_cast, hk1, hk2, z1, z2,
      toInt?_2 I, toInt?_m1 I, u]
    have h2n : t ^ (2 * n) = t ^ n * t ^ n := by rw [two_mul, zpow_add₀ ht0]
    simp only [zpow_add₀ ht0, zpow_sub_one₀ ht0, zpow_one, h2n]
    have h1 := mul_inv_cancel₀ hm1'
    have h2 := mul_inv_cancel₀ hmn1'
    have h3 := mul_inv_cancel₀ ht0
    have hsc' := hsc (env "a" + env "b" * t ^ n)
    set s := I.sin (env "a" + env "b" * t ^ n)
    set c := I.cos (env "a" + env "b" * t ^ n)
    set X := t ^ m
    set Y := t ^ n
    set ti := t⁻¹
    set i1 := ((m : 𝕜) + 1)⁻¹
    set i2 := ((m : 𝕜) + n + 1)⁻¹
    set K := (k : 𝕜)
    set N := (n : 𝕜)
    set M := (m : 𝕜)
    set B := env "b"
    linear_combination (X*c ^ k*(B^2*K^2*N*Y^2*c^2*i2 + B^2*K^2*N*Y^2*i2*s^2*t*ti - B^2*K^2*N*Y^2*i2 - B^2*K*N*Y^2*c^2*i2*t*ti + 4*B^2*K*N*Y^2*c^2*i2 + 3*B^2*K*N*Y^2*i2*s^2*t*ti - 3*B^2*K*N*Y^2*i2 - 2*B^2*N*Y^2*c^2*i2*t*ti + 4*B^2*N*Y^2*c^2*i2 + 2*B^2*N*Y^2*i2*s^2*t*ti - 2*B^2*N*Y^2*i2 + c^2)) * h1 +
      (-B*X*Y*c ^ k*(K + 2)*(B*K*N*Y*c^2*i1 + B*K*N*Y*i1*s^2*t*ti - B*K*N*Y*i1 - B*K*Y*c^2 - B*K*Y*s^2*t*ti + B*K*Y - B*N*Y*c^2*i1*t*ti + 2*B*N*Y*c^2*i1 + B*N*Y*i1*s^2*t*ti - B*N*Y*i1 + B*Y*c^2*t*ti - 2*B*Y*c^2 - B*Y*s^2*t*ti + B*Y - N*c*i1*s)) * h2 +
      (-B*X*Y*c ^ k*(K + 2)*(B*K*M*Y*i2*s^2 + B*K*N*Y*i1*s^2 + B*K*Y*i2*s^2 - B*K*Y*s^2 - B*M*Y*c^2*i2 + B*M*Y*i2*s^2 - B*N*Y*c^2*i1 + B*N*Y*i1*s^2 - B*Y*c^2*i2 + B*Y*c^2 + B*Y*i2*s^2 - B*Y*s^2 + N*c*i1*s)) * h3 +
      (-B^2*X*Y^2*c ^ k*(K + 1)*(K + 2)*(M*i2 + N*i1 + i2 - 1)) * hsc'

theorem powCosPowReduce_real : powCosPowReduce.Holds .real :=
  powCosPowReduce_holds Interp.real Interp.real_lt_rat Real.hasDerivAt_sin Real.hasDerivAt_cos
    Real.sin_sq_add_cos_sq

theorem powCosPowReduce_complex : powCosPowReduce.Holds .complex :=
  powCosPowReduce_holds Interp.complex Interp.complex_lt_rat Complex.hasDerivAt_sin
    Complex.hasDerivAt_cos Complex.sin_sq_add_cos_sq

end Proofs

end OSR.IntegrationRec8
