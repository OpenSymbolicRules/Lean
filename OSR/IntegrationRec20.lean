import OSR.IntegrationRec19

/-!
# Integration (RUBI): EqQ leftovers proved by pointwise identities

Four RUBI 4.16.1 rules whose `EqQ` condition makes a trigonometric identity
apply under the integral are proved over ℝ and ℂ:

* 4.7.9 #9 and #10: when `a² = b²`,
  `cosⁿ u/(a + b sin u) = cosⁿ⁻² u (1/a - sin u/b)` (and the same with `sin`
  and `cos` exchanged), since `(b - a s)(a + b s) = a b (1 - s²)`;
* 4.7.7 #26 and #27: when `g = f` (resp. `g = -f`),
  `f + g cos u = 2 f cos²(u/2)` (resp. `2 f sin²(u/2)`).

4.7.7 #32 is refuted at `m = n = 0`, `e = 1`: the integrand is defined
everywhere, but the residual integrand `tan(x/2)⁰` is not defined at `x = π`.
Variables that RUBI constrains by numeric predicates but does not list in
`FreeQ` are declared independent of `x`, with an `independence:` finding.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec20

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- cosⁿ u/(a + b sin u) = cosⁿ⁻² u (1/a - sin u/b) when a² = b² -/
def cosPowOverSin : CRule where
  id := "integration.cos_power_over_sin_binomial"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:9"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "a") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))))) (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.int (.var "n"),
    .gt (.var "n") (.int 1),
    .eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)]
  priority := 3000
  description := "cosⁿ u/(a + b sin u) = cosⁿ⁻² u (1/a - sin u/b) when a² = b²"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:9" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#9"
/-- sinⁿ u/(a + b cos u) = sinⁿ⁻² u (1/a - cos u/b) when a² = b² -/
def sinPowOverCos : CRule where
  id := "integration.sin_power_over_cos_binomial"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:10"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "a") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))))) (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.int (.var "n"),
    .gt (.var "n") (.int 1),
    .eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)]
  priority := 3010
  description := "sinⁿ u/(a + b cos u) = sinⁿ⁻² u (1/a - cos u/b) when a² = b²"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:10" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#10"
/-- f + f cos u = 2 f cos²(u/2) under the integral -/
def expOnePlusCos : CRule where
  id := "integration.exp_one_plus_cos_power"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.7 F^(c (a+b x)) trig(d+e x)^n:26"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.var "n")))
  result := (.app2 .mul (.app2 .mul (.pow (.int 2) (.var "n")) (.pow (.var "f") (.var "n"))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .cos (.app2 .add (.app2 .mul (.var "d") (.pow (.int 2) (.int (-1)))) (.app2 .mul (.app2 .mul (.var "e") (.var "x")) (.pow (.int 2) (.int (-1)))))) (.app2 .mul (.int 2) (.var "n")))))]
  independent := ["F", "a", "b", "c", "d", "e", "f", "g", "n"]
  conditions := [.eq (.app2 .add (.var "f") (.app2 .mul (.int (-1)) (.var "g"))) (.int 0),
    .int (.var "n"),
    .gt (.int 0) (.var "n")]
  priority := 3020
  description := "f + f cos u = 2 f cos²(u/2) under the integral"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.7 F^(c (a+b x)) trig(d+e x)^n:26" "4 Trig functions/4.7 Miscellaneous/4.7.7 F^(c (a+b x)) trig(d+e x)^n.m#26"
/-- f - f cos u = 2 f sin²(u/2) under the integral -/
def expOneMinusCos : CRule where
  id := "integration.exp_one_minus_cos_power"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.7 F^(c (a+b x)) trig(d+e x)^n:27"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.var "n")))
  result := (.app2 .mul (.app2 .mul (.pow (.int 2) (.var "n")) (.pow (.var "f") (.var "n"))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .sin (.app2 .add (.app2 .mul (.var "d") (.pow (.int 2) (.int (-1)))) (.app2 .mul (.app2 .mul (.var "e") (.var "x")) (.pow (.int 2) (.int (-1)))))) (.app2 .mul (.int 2) (.var "n")))))]
  independent := ["F", "a", "b", "c", "d", "e", "f", "g", "n"]
  conditions := [.eq (.app2 .add (.var "f") (.var "g")) (.int 0),
    .int (.var "n"),
    .gt (.int 0) (.var "n")]
  priority := 3030
  description := "f - f cos u = 2 f sin²(u/2) under the integral"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.7 F^(c (a+b x)) trig(d+e x)^n:27" "4 Trig functions/4.7 Miscellaneous/4.7.7 F^(c (a+b x)) trig(d+e x)^n.m#27"
/-- RUBI 4.7.7 #32 -/
def rubi477r32 : CRule where
  id := "integration.rubi_4_7_7_r32"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.7 F^(c (a+b x)) trig(d+e x)^n:32"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "m"))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.var "n")))
  result := (.app2 .mul (.pow (.var "f") (.var "n")) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .tan (.app2 .add (.app2 .mul (.var "d") (.pow (.int 2) (.int (-1)))) (.app2 .mul (.app2 .mul (.var "e") (.var "x")) (.pow (.int 2) (.int (-1)))))) (.var "m"))))]
  independent := ["F", "a", "b", "c", "d", "e", "f", "g", "m", "n"]
  conditions := [.eq (.app2 .add (.var "f") (.app2 .mul (.int (-1)) (.var "g"))) (.int 0),
    .int (.var "m"),
    .int (.var "n"),
    .eq (.app2 .add (.var "m") (.var "n")) (.int 0)]
  priority := 3040
  description := "RUBI 4.7.7 #32"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.7 F^(c (a+b x)) trig(d+e x)^n:32" "4 Trig functions/4.7 Miscellaneous/4.7.7 F^(c (a+b x)) trig(d+e x)^n.m#32"

/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem toInt?_val {I : Interp 𝕜} {v : 𝕜} {k : ℤ} (h : I.toInt? v = some k) :
    v = (k : 𝕜) := (I.toInt?_eq _ _).1 h

/-- The integer value of a metavariable constrained by `.int` and `.gt`. -/
private theorem int_gt [CharZero 𝕜] {I : Interp 𝕜}
    (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) {v : 𝕜} {k : ℤ}
    (hk : I.toInt? v = some k) (z : ℤ) (h : I.lt (z : 𝕜) v) : z < k := by
  rw [toInt?_val hk] at h
  have h' : I.lt ((z : ℚ) : 𝕜) ((k : ℚ) : 𝕜) := by simpa using h
  exact_mod_cast (hlt _ _).1 h'

/-- `(b - a s)(a + b s) = a b c²` when `a² = b²` and `s² + c² = 1`, rearranged. -/
private theorem quot_core {a b s c P : 𝕜} (j : ℕ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hD : a + b * s ≠ 0) (hab : a ^ 2 = b ^ 2) (hP : s ^ 2 + c ^ 2 = 1) :
    a⁻¹ * (P * c ^ j) - b⁻¹ * (P * c ^ j * s) = P * c ^ (j + 2) * (a + b * s)⁻¹ := by
  field_simp
  linear_combination (-(P * c ^ j * a * b)) * hP + (-(P * c ^ j * s)) * hab

private theorem toInt?_two (I : Interp 𝕜) : I.toInt? (2 : 𝕜) = some 2 :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem toInt?_neg_one (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

/-- **4.7.9 #9.** -/
theorem cosPowOverSin_holds [CharZero 𝕜] (I : Interp 𝕜)
    (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (hP : ∀ u, I.sin u ^ 2 + I.cos u ^ 2 = 1) :
    AntiderivRecHolds I "x" cosPowOverSin.conditions cosPowOverSin.body cosPowOverSin.result
      cosPowOverSin.integrals := by
  intro env hc t hF
  have hgt := hc (.gt (.var "n") (.int 1)) (by simp [cosPowOverSin])
  have heq := hc (.eq (.app2 .add (.pow (.var "a") (.int 2))
    (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [cosPowOverSin])
  rcases hkn : I.toInt? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [cosPowOverSin, Defined, eval, hkn] at h
  rcases hkm : I.toInt? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [cosPowOverSin, Defined, eval, hkm] at h
  have hn1 : 1 < n := int_gt hlt hkn 1 (by simpa [Cond.Holds, Defined, eval] using hgt.2.2)
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = (j : ℤ) + 2 := ⟨(n - 2).toNat, by omega⟩
  have hab : env "a" ^ 2 = env "b" ^ 2 := by
    simp [Cond.Holds, Defined, eval, toInt?_two] at heq
    linear_combination heq
  have hn2 : I.toInt? (env "n" + -2) = some (j : ℤ) :=
    (I.toInt?_eq _ _).2 (by rw [toInt?_val hkn]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) cosPowOverSin.body →
      (m < 0 → env "e" + env "f" * w ≠ 0) ∧
        env "a" + env "b" * I.sin (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [cosPowOverSin, Defined, eval, hkn, hkm, toInt?_neg_one] at h
    exact ⟨by tauto, by tauto⟩
  have hab0 : env "a" ≠ 0 ∧ env "b" ≠ 0 := by
    obtain ⟨-, hd⟩ := hD t hF.self_of_nhds
    constructor
    · intro ha
      have hb : env "b" = 0 := by
        have : env "b" ^ 2 = 0 := by rw [← hab, ha]; ring
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      exact hd (by rw [ha, hb]; ring)
    · intro hb
      have ha : env "a" = 0 := by
        have : env "a" ^ 2 = 0 := by rw [hab, hb]; ring
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      exact hd (by rw [ha, hb]; ring)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [cosPowOverSin, List.mem_cons, List.not_mem_nil, or_false] at hi
    filter_upwards [hF] with w hw
    obtain ⟨hm0, -⟩ := hD w hw
    rcases hi with rfl | rfl <;> simp [Defined, eval, hkm] <;>
      exact ⟨hm0, j, hn2, fun h => absurd h (by omega)⟩
  · exact Eventually.of_forall fun _ => by
      simp [cosPowOverSin, Defined, eval, recEnv, toInt?_neg_one, hab0.1, hab0.2]
  · simp only [cosPowOverSin, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (cosPowOverSin.integrals.map (·.1)) Φ "x" w)
        cosPowOverSin.result) = fun w =>
          1 * env "a" ^ (-1 : ℤ) * Φ "I1" w + -1 * 1 * env "b" ^ (-1 : ℤ) * Φ "I2" w := by
      funext w
      simp [cosPowOverSin, eval, recEnv, toInt?_neg_one]
    rw [hfun]
    refine ((hΦ.1.const_mul _).add (hΦ.2.const_mul _)).congr_deriv ?_
    obtain ⟨-, hd⟩ := hD t hF.self_of_nhds
    simp [cosPowOverSin, eval, hkm, hkn, hn2, toInt?_neg_one]
    have := quot_core (P := (env "e" + env "f" * t) ^ m) j hab0.1 hab0.2 hd hab
      (hP (env "c" + env "d" * t))
    rw [show ((j : ℤ) + 2) = ((j + 2 : ℕ) : ℤ) by push_cast; ring]
    simp only [zpow_natCast]
    rw [← this]
    ring

theorem cosPowOverSin_real : cosPowOverSin.Holds .real :=
  cosPowOverSin_holds Interp.real Interp.real_lt_rat fun u => Real.sin_sq_add_cos_sq u

theorem cosPowOverSin_complex : cosPowOverSin.Holds .complex :=
  cosPowOverSin_holds Interp.complex Interp.complex_lt_rat fun u => Complex.sin_sq_add_cos_sq u

/-- **4.7.9 #10.** -/
theorem sinPowOverCos_holds [CharZero 𝕜] (I : Interp 𝕜)
    (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (hP : ∀ u, I.sin u ^ 2 + I.cos u ^ 2 = 1) :
    AntiderivRecHolds I "x" sinPowOverCos.conditions sinPowOverCos.body sinPowOverCos.result
      sinPowOverCos.integrals := by
  intro env hc t hF
  have hgt := hc (.gt (.var "n") (.int 1)) (by simp [sinPowOverCos])
  have heq := hc (.eq (.app2 .add (.pow (.var "a") (.int 2))
    (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [sinPowOverCos])
  rcases hkn : I.toInt? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [sinPowOverCos, Defined, eval, hkn] at h
  rcases hkm : I.toInt? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [sinPowOverCos, Defined, eval, hkm] at h
  have hn1 : 1 < n := int_gt hlt hkn 1 (by simpa [Cond.Holds, Defined, eval] using hgt.2.2)
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = (j : ℤ) + 2 := ⟨(n - 2).toNat, by omega⟩
  have hab : env "a" ^ 2 = env "b" ^ 2 := by
    simp [Cond.Holds, Defined, eval, toInt?_two] at heq
    linear_combination heq
  have hn2 : I.toInt? (env "n" + -2) = some (j : ℤ) :=
    (I.toInt?_eq _ _).2 (by rw [toInt?_val hkn]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) sinPowOverCos.body →
      (m < 0 → env "e" + env "f" * w ≠ 0) ∧
        env "a" + env "b" * I.cos (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [sinPowOverCos, Defined, eval, hkn, hkm, toInt?_neg_one] at h
    exact ⟨by tauto, by tauto⟩
  have hab0 : env "a" ≠ 0 ∧ env "b" ≠ 0 := by
    obtain ⟨-, hd⟩ := hD t hF.self_of_nhds
    constructor
    · intro ha
      have hb : env "b" = 0 := by
        have : env "b" ^ 2 = 0 := by rw [← hab, ha]; ring
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      exact hd (by rw [ha, hb]; ring)
    · intro hb
      have ha : env "a" = 0 := by
        have : env "a" ^ 2 = 0 := by rw [hab, hb]; ring
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      exact hd (by rw [ha, hb]; ring)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [sinPowOverCos, List.mem_cons, List.not_mem_nil, or_false] at hi
    filter_upwards [hF] with w hw
    obtain ⟨hm0, -⟩ := hD w hw
    rcases hi with rfl | rfl <;> simp [Defined, eval, hkm] <;>
      exact ⟨hm0, j, hn2, fun h => absurd h (by omega)⟩
  · exact Eventually.of_forall fun _ => by
      simp [sinPowOverCos, Defined, eval, recEnv, toInt?_neg_one, hab0.1, hab0.2]
  · simp only [sinPowOverCos, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (sinPowOverCos.integrals.map (·.1)) Φ "x" w)
        sinPowOverCos.result) = fun w =>
          1 * env "a" ^ (-1 : ℤ) * Φ "I1" w + -1 * 1 * env "b" ^ (-1 : ℤ) * Φ "I2" w := by
      funext w
      simp [sinPowOverCos, eval, recEnv, toInt?_neg_one]
    rw [hfun]
    refine ((hΦ.1.const_mul _).add (hΦ.2.const_mul _)).congr_deriv ?_
    obtain ⟨-, hd⟩ := hD t hF.self_of_nhds
    simp [sinPowOverCos, eval, hkm, hkn, hn2, toInt?_neg_one]
    have := quot_core (P := (env "e" + env "f" * t) ^ m) j hab0.1 hab0.2 hd hab
      (by rw [add_comm]; exact hP (env "c" + env "d" * t))
    rw [show ((j : ℤ) + 2) = ((j + 2 : ℕ) : ℤ) by push_cast; ring]
    simp only [zpow_natCast]
    rw [← this]
    ring

theorem sinPowOverCos_real : sinPowOverCos.Holds .real :=
  sinPowOverCos_holds Interp.real Interp.real_lt_rat fun u => Real.sin_sq_add_cos_sq u

theorem sinPowOverCos_complex : sinPowOverCos.Holds .complex :=
  sinPowOverCos_holds Interp.complex Interp.complex_lt_rat fun u => Complex.sin_sq_add_cos_sq u

/-- The integer value of a metavariable constrained to lie below `z`. -/
private theorem int_lt [CharZero 𝕜] {I : Interp 𝕜}
    (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) {v : 𝕜} {k : ℤ}
    (hk : I.toInt? v = some k) (z : ℤ) (h : I.lt v (z : 𝕜)) : k < z := by
  rw [toInt?_val hk] at h
  have h' : I.lt ((k : ℚ) : 𝕜) ((z : ℚ) : 𝕜) := by simpa using h
  exact_mod_cast (hlt _ _).1 h'

/-- **4.7.7 #26.** -/
theorem expOnePlusCos_holds [CharZero 𝕜] (I : Interp 𝕜)
    (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (hC : ∀ v, I.cos (2 * v) = 2 * I.cos v ^ 2 - 1) :
    AntiderivRecHolds I "x" expOnePlusCos.conditions expOnePlusCos.body expOnePlusCos.result
      expOnePlusCos.integrals := by
  intro env hc t hF
  have hgt := hc (.gt (.int 0) (.var "n")) (by simp [expOnePlusCos])
  have heq := hc (.eq (.app2 .add (.var "f") (.app2 .mul (.int (-1)) (.var "g"))) (.int 0))
    (by simp [expOnePlusCos])
  rcases hkn : I.toInt? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [expOnePlusCos, Defined, eval, hkn] at h
  have hneg : n < 0 := int_lt hlt hkn 0 (by simpa [Cond.Holds, Defined, eval] using hgt.2.2)
  have hg : env "g" = env "f" := by
    simp [Cond.Holds, Defined, eval] at heq
    linear_combination -heq
  have h2n : I.toInt? (2 * env "n") = some (2 * n) :=
    (I.toInt?_eq _ _).2 (by rw [toInt?_val hkn]; push_cast; ring)
  have hid : ∀ w, env "f" + env "g" * I.cos (env "d" + env "e" * w) =
      2 * env "f" * I.cos (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) ^ 2 := by
    intro w
    rw [hg, show env "d" + env "e" * w = 2 * (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) by ring, hC]
    ring
  have hD : ∀ w, Defined I (Function.update env "x" w) expOnePlusCos.body →
      env "f" + env "g" * I.cos (env "d" + env "e" * w) ≠ 0 := by
    intro w h
    have h2 := h.2
    simp [Defined, eval, hkn, hneg] at h2
    exact h2
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [expOnePlusCos, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hne := hD w hw
    rw [hid w] at hne
    refine ⟨hw.1, ?_⟩
    simp [Defined, eval, h2n, toInt?_neg_one]
    intro _ h0
    exact hne (by rw [h0]; ring)
  · have hne := hD t hF.self_of_nhds
    rw [hid t] at hne
    have hf0 : env "f" ≠ 0 := fun h => hne (by rw [h]; ring)
    exact Eventually.of_forall fun _ => by
      simp [expOnePlusCos, Defined, eval, recEnv, hkn, hf0]
  · simp only [expOnePlusCos, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (expOnePlusCos.integrals.map (·.1)) Φ "x" w)
        expOnePlusCos.result) = fun w => 2 ^ n * env "f" ^ n * Φ "I1" w := by
      funext w
      simp [expOnePlusCos, eval, recEnv, hkn]
    rw [hfun]
    refine (hΦ.const_mul _).congr_deriv ?_
    simp [expOnePlusCos, eval, hkn, h2n, toInt?_neg_one]
    rw [hid t, zpow_mul, zpow_ofNat, mul_zpow, mul_zpow]
    ring

theorem expOnePlusCos_real : expOnePlusCos.Holds .real :=
  expOnePlusCos_holds Interp.real Interp.real_lt_rat fun v => Real.cos_two_mul v

theorem expOnePlusCos_complex : expOnePlusCos.Holds .complex :=
  expOnePlusCos_holds Interp.complex Interp.complex_lt_rat fun v => Complex.cos_two_mul v

/-- **4.7.7 #27.** -/
theorem expOneMinusCos_holds [CharZero 𝕜] (I : Interp 𝕜)
    (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (hC : ∀ v, I.cos (2 * v) = 1 - 2 * I.sin v ^ 2) :
    AntiderivRecHolds I "x" expOneMinusCos.conditions expOneMinusCos.body expOneMinusCos.result
      expOneMinusCos.integrals := by
  intro env hc t hF
  have hgt := hc (.gt (.int 0) (.var "n")) (by simp [expOneMinusCos])
  have heq := hc (.eq (.app2 .add (.var "f") (.var "g")) (.int 0))
    (by simp [expOneMinusCos])
  rcases hkn : I.toInt? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [expOneMinusCos, Defined, eval, hkn] at h
  have hneg : n < 0 := int_lt hlt hkn 0 (by simpa [Cond.Holds, Defined, eval] using hgt.2.2)
  have hg : env "g" = -env "f" := by
    simp [Cond.Holds, Defined, eval] at heq
    linear_combination heq
  have h2n : I.toInt? (2 * env "n") = some (2 * n) :=
    (I.toInt?_eq _ _).2 (by rw [toInt?_val hkn]; push_cast; ring)
  have hid : ∀ w, env "f" + env "g" * I.cos (env "d" + env "e" * w) =
      2 * env "f" * I.sin (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) ^ 2 := by
    intro w
    rw [hg, show env "d" + env "e" * w = 2 * (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) by ring, hC]
    ring
  have hD : ∀ w, Defined I (Function.update env "x" w) expOneMinusCos.body →
      env "f" + env "g" * I.cos (env "d" + env "e" * w) ≠ 0 := by
    intro w h
    have h2 := h.2
    simp [Defined, eval, hkn, hneg] at h2
    exact h2
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [expOneMinusCos, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hne := hD w hw
    rw [hid w] at hne
    refine ⟨hw.1, ?_⟩
    simp [Defined, eval, h2n, toInt?_neg_one]
    intro _ h0
    exact hne (by rw [h0]; ring)
  · have hne := hD t hF.self_of_nhds
    rw [hid t] at hne
    have hf0 : env "f" ≠ 0 := fun h => hne (by rw [h]; ring)
    exact Eventually.of_forall fun _ => by
      simp [expOneMinusCos, Defined, eval, recEnv, hkn, hf0]
  · simp only [expOneMinusCos, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (expOneMinusCos.integrals.map (·.1)) Φ "x" w)
        expOneMinusCos.result) = fun w => 2 ^ n * env "f" ^ n * Φ "I1" w := by
      funext w
      simp [expOneMinusCos, eval, recEnv, hkn]
    rw [hfun]
    refine (hΦ.const_mul _).congr_deriv ?_
    simp [expOneMinusCos, eval, hkn, h2n, toInt?_neg_one]
    rw [hid t, zpow_mul, zpow_ofNat, mul_zpow, mul_zpow]
    ring

theorem expOneMinusCos_real : expOneMinusCos.Holds .real :=
  expOneMinusCos_holds Interp.real Interp.real_lt_rat fun v => by
    simp only [Interp.real]
    rw [Real.cos_two_mul]; linear_combination 2 * Real.sin_sq_add_cos_sq v

theorem expOneMinusCos_complex : expOneMinusCos.Holds .complex :=
  expOneMinusCos_holds Interp.complex Interp.complex_lt_rat fun v => by
    simp only [Interp.complex]
    rw [Complex.cos_two_mul]; linear_combination 2 * Complex.sin_sq_add_cos_sq v

section Witness
variable {α : Type} [Field α] [CharZero α]
private theorem iv0 : intValue? (0 : α) = some 0 := by simpa using intValue?_intCast (α := α) 0
private theorem iv1 : intValue? (1 : α) = some 1 := by simpa using intValue?_intCast (α := α) 1
private theorem iv2 : intValue? (2 : α) = some 2 := by simpa using intValue?_intCast (α := α) 2
private theorem ivm1 : intValue? (-1 : α) = some (-1) := by
  simpa using intValue?_intCast (α := α) (-1)
end Witness

/-- **Counterexample** to 4.7.7 #32: at `e = 1` and the other metavariables
`0`, the integrand `0⁰ sin(x)⁰ (0 + 0 cos x)⁰` is defined everywhere, but the
residual integrand `0⁰ tan(x/2)⁰` is not defined at `x = π`. -/
theorem rubi477r32_counterexample_real : ¬ rubi477r32.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi477r32.conditions rubi477r32.body
    rubi477r32.result rubi477r32.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "e" then 1 else 0) Real.pi ?_ ?_
    ⟨rubi477r32.integrals[0]!, by simp [rubi477r32], ?_⟩
  · simp [rubi477r32, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, ivm1]
  · exact Eventually.of_forall fun w => by
      simp [rubi477r32, Defined, eval, Interp.real, iv0, iv1, ivm1]
  · have h : Real.cos (Real.pi * 2⁻¹) = 0 := by rw [← div_eq_mul_inv]; exact Real.cos_pi_div_two
    simp [rubi477r32, Defined, eval, Interp.real, iv0, iv1, iv2, ivm1, h]

theorem rubi477r32_counterexample_complex : ¬ rubi477r32.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi477r32.conditions rubi477r32.body
    rubi477r32.result rubi477r32.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "e" then 1 else 0) (Real.pi : ℂ) ?_ ?_
    ⟨rubi477r32.integrals[0]!, by simp [rubi477r32], ?_⟩
  · simp [rubi477r32, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, ivm1]
  · exact Eventually.of_forall fun w => by
      simp [rubi477r32, Defined, eval, Interp.complex, iv0, iv1, ivm1]
  · have h : Complex.cos ((Real.pi : ℂ) * 2⁻¹) = 0 := by
      rw [← div_eq_mul_inv]; exact Complex.cos_pi_div_two
    simp [rubi477r32, Defined, eval, Interp.complex, iv0, iv1, iv2, ivm1, h]

end Proofs

end OSR.IntegrationRec20
