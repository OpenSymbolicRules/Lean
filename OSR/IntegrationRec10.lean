import OSR.IntegrationRec9

/-!
# Integration (RUBI): reduction of quadratic powers

Rules that a numerical check found to behave as identities where they are
defined, proved here over every interpretation having the needed
trigonometric identities.  The rule declarations are transcribed by a tool
and checked by the Integration repository's `scripts/v1_faithfulness.py`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec10

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- (a + b x + c x^2)^p reduced to p + 1, for p < -1 -/
def quadPowReduce : CRule where
  id := "integration.quadratic_power_reduction"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.1 (a+b x+c x^2)^p:7"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "x"))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .add (.var "p") (.int 1)) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3))) (.pow (.app2 .mul (.app2 .add (.var "p") (.int 1)) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1))))]
  independent := ["a", "b", "c", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .gt (.int (-1)) (.var "p"),
    .ne (.var "p") (.app2 .mul (.int (-3)) (.pow (.int 2) (.int (-1)))),
    .int (.app2 .mul (.int 4) (.var "p"))]
  priority := 2730
  description := "(a + b x + c x^2)^p reduced to p + 1, for p < -1"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.1 (a+b x+c x^2)^p:7" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.1 (a+b x+c x^2)^p.m#7"

/-- (d + e x) (a + b x + c x^2)^p reduced to p + 1, for p < -1 -/
def linQuadPowReduce : CRule where
  id := "integration.linear_quadratic_power_reduction"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:11"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.var "b") (.var "d")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "a")) (.var "e"))) (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.var "x"))) (.pow (.app2 .mul (.app2 .add (.var "p") (.int 1)) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int (-1)))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3))) (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")))) (.pow (.app2 .mul (.app2 .add (.var "p") (.int 1)) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1))))]
  independent := ["a", "b", "c", "d", "e", "p"]
  conditions := [.ne (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0),
    .ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .gt (.int (-1)) (.var "p"),
    .ne (.var "p") (.app2 .mul (.int (-3)) (.pow (.int 2) (.int (-1))))]
  priority := 2740
  description := "(d + e x) (a + b x + c x^2)^p reduced to p + 1, for p < -1"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:11" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#11"

/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem toInt?_val {I : Interp 𝕜} {v : 𝕜} {k : ℤ} (h : I.toInt? v = some k) :
    v = (k : 𝕜) := (I.toInt?_eq _ _).1 h

private theorem toInt?_m1 (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem toInt?_2 (I : Interp 𝕜) : I.toInt? (2 : 𝕜) = some 2 :=
  (I.toInt?_eq _ _).2 (by simp)

/-- `((b + 2 c x) Qᵖ⁺¹)' = 2 c Qᵖ⁺¹ + (p + 1) (4 c Q + b² - 4 a c) Qᵖ` for
`Q = a + b x + c x²`, so `∫ Qᵖ` reduces to `∫ Qᵖ⁺¹` for `p < -1`. -/
theorem quadPowReduce_holds [CharZero 𝕜] (I : Interp 𝕜)
    (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" quadPowReduce.conditions quadPowReduce.body
      quadPowReduce.result quadPowReduce.integrals := by
  intro env hcond t hF
  have hgp := hcond (.gt (.int (-1)) (.var "p")) (by simp [quadPowReduce])
  have hnD := hcond (.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul
    (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)) (by simp [quadPowReduce])
  rcases hkp : I.toInt? (env "p") with _ | p
  · exfalso
    have h := hF.self_of_nhds
    simp [quadPowReduce, Defined, eval, hkp] at h
  have hp := toInt?_val hkp
  have hplt : p < -1 := by
    simp only [Cond.Holds, Defined, eval, true_and] at hgp
    rw [hp] at hgp
    have h' : I.lt ((p : ℚ) : 𝕜) ((-1 : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast]; push_cast; simpa using hgp
    exact_mod_cast (hlt _ _).1 h'
  have hD : env "b" ^ 2 - 4 * env "a" * env "c" ≠ 0 := by
    have := hnD.2.2
    simp [eval, toInt?_2 I] at this
    intro h; apply this; linear_combination h
  have hp1 : (p : 𝕜) + 1 ≠ 0 := by
    have : (p : 𝕜) + 1 = ((p + 1 : ℤ) : 𝕜) := by push_cast; ring
    rw [this]; exact_mod_cast (show p + 1 ≠ 0 by omega)
  have T : ∀ (v : 𝕜) (z : ℤ), v = (z : 𝕜) → I.toInt? v = some z :=
    fun v z h => (I.toInt?_eq _ _).2 h
  have e1 : I.toInt? ((p : 𝕜) + 1) = some (p + 1) := T _ _ (by push_cast; ring)
  set Q : 𝕜 → 𝕜 := fun w => env "a" + env "b" * w + env "c" * w ^ 2 with hQdef
  have hQ : ∀ w, Defined I (Function.update env "x" w) quadPowReduce.body → Q w ≠ 0 := by
    intro w h
    simp [quadPowReduce, Defined, eval, hkp, toInt?_2 I] at h
    exact h (by omega)
  have hQt := hQ t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [quadPowReduce, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hw0 := hQ w hw
    simp [Defined, eval, hp, e1, toInt?_2 I, I.toInt?_cast]
    intro _; exact hw0
  · filter_upwards [hF] with w hw
    have hw0 := hQ w hw
    simp [quadPowReduce, Defined, eval, recEnv, toInt?_m1 I, toInt?_2 I, hp, e1, I.toInt?_cast]
    exact ⟨fun _ => hw0, hp1, fun h => hD (by linear_combination h)⟩
  · simp only [quadPowReduce, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hK : ((p : 𝕜) + 1) * (env "b" ^ 2 + -(4 * env "a" * env "c")) ≠ 0 :=
      mul_ne_zero hp1 (fun h => hD (by linear_combination h))
    have hfun : (fun w => eval I (recEnv env (quadPowReduce.integrals.map (·.1)) Φ "x" w)
        quadPowReduce.result) = fun w =>
          (env "b" + 2 * env "c" * w) * Q w ^ (p + 1) *
            (((p : 𝕜) + 1) * (env "b" ^ 2 + -(4 * env "a" * env "c")))⁻¹ +
          -(2 * env "c" * (2 * (p : 𝕜) + 3)) *
            (((p : 𝕜) + 1) * (env "b" ^ 2 + -(4 * env "a" * env "c")))⁻¹ * Φ "I1" w := by
      funext w
      simp [quadPowReduce, eval, recEnv, toInt?_m1 I, toInt?_2 I, hp, e1, I.toInt?_cast, hQdef]
      try ring_nf
      try simp
    rw [hfun]
    have hQd : HasDerivAt Q (env "b" + 2 * env "c" * t) t := by
      have := (((hasDerivAt_id t).const_mul (env "b")).const_add (env "a")).add
        ((hasDerivAt_pow 2 t).const_mul (env "c"))
      convert this using 1 <;> first | rfl | (simp; ring)
    have hZ : HasDerivAt (fun w => Q w ^ (p + 1))
        (((p : 𝕜) + 1) * Q t ^ p * (env "b" + 2 * env "c" * t)) t := by
      have := (hasDerivAt_zpow (p + 1) (Q t) (Or.inl hQt)).comp t hQd
      convert this using 1 <;> first | rfl | (rw [add_sub_cancel_right]; push_cast; ring)
    have hL : HasDerivAt (fun w : 𝕜 => env "b" + 2 * env "c" * w) (2 * env "c") t := by
      simpa using ((hasDerivAt_id t).const_mul (2 * env "c")).const_add (env "b")
    refine (((hL.mul hZ).mul_const _).add (hΦ.const_mul _)).congr_deriv ?_
    simp [quadPowReduce, eval, toInt?_2 I, hp, e1, I.toInt?_cast]
    simp only [show env "a" + env "b" * t + env "c" * t ^ 2 = Q t from rfl, zpow_add_one₀ hQt]
    have hQv : Q t = env "a" + env "b" * t + env "c" * t ^ 2 := rfl
    have hDi := mul_inv_cancel₀ (show env "b" ^ 2 + -(4 * env "a" * env "c") ≠ 0 from
      fun h => hD (by linear_combination h))
    have hPi := mul_inv_cancel₀ hp1
    linear_combination (Q t ^ p * ((p : 𝕜) + 1) * ((p : 𝕜) + 1)⁻¹) * hDi + Q t ^ p * hPi +
      (-4 * env "c" * ((p : 𝕜) + 1) *
        (((p : 𝕜) + 1) * (env "b" ^ 2 + -(4 * env "a" * env "c")))⁻¹ * Q t ^ p) * hQv

theorem quadPowReduce_real : quadPowReduce.Holds .real :=
  quadPowReduce_holds Interp.real Interp.real_lt_rat

theorem quadPowReduce_complex : quadPowReduce.Holds .complex :=
  quadPowReduce_holds Interp.complex Interp.complex_lt_rat

/-- With `L = b d - 2 a e + (2 c d - b e) x`, `L Q' - 2 (2 c d - b e) Q = (b² - 4 a c) (d + e x)`
for `Q = a + b x + c x²`, so `∫ (d + e x) Qᵖ` reduces to `∫ Qᵖ⁺¹` for `p < -1`. -/
theorem linQuadPowReduce_holds [CharZero 𝕜] (I : Interp 𝕜)
    (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" linQuadPowReduce.conditions linQuadPowReduce.body
      linQuadPowReduce.result linQuadPowReduce.integrals := by
  intro env hcond t hF
  have hgp := hcond (.gt (.int (-1)) (.var "p")) (by simp [linQuadPowReduce])
  have hnD := hcond (.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul
    (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)) (by simp [linQuadPowReduce])
  rcases hkp : I.toInt? (env "p") with _ | p
  · exfalso
    have h := hF.self_of_nhds
    simp [linQuadPowReduce, Defined, eval, hkp] at h
  have hp := toInt?_val hkp
  have hplt : p < -1 := by
    simp only [Cond.Holds, Defined, eval, true_and] at hgp
    rw [hp] at hgp
    have h' : I.lt ((p : ℚ) : 𝕜) ((-1 : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast]; push_cast; simpa using hgp
    exact_mod_cast (hlt _ _).1 h'
  have hD : env "b" ^ 2 - 4 * env "a" * env "c" ≠ 0 := by
    have := hnD.2.2
    simp [eval, toInt?_2 I] at this
    intro h; apply this; linear_combination h
  have hp1 : (p : 𝕜) + 1 ≠ 0 := by
    have : (p : 𝕜) + 1 = ((p + 1 : ℤ) : 𝕜) := by push_cast; ring
    rw [this]; exact_mod_cast (show p + 1 ≠ 0 by omega)
  have T : ∀ (v : 𝕜) (z : ℤ), v = (z : 𝕜) → I.toInt? v = some z :=
    fun v z h => (I.toInt?_eq _ _).2 h
  have e1 : I.toInt? ((p : 𝕜) + 1) = some (p + 1) := T _ _ (by push_cast; ring)
  set Q : 𝕜 → 𝕜 := fun w => env "a" + env "b" * w + env "c" * w ^ 2 with hQdef
  have hQ : ∀ w, Defined I (Function.update env "x" w) linQuadPowReduce.body → Q w ≠ 0 := by
    intro w h
    simp [linQuadPowReduce, Defined, eval, hkp, toInt?_2 I] at h
    first | exact h (by omega) | exact h.2 (by omega) | exact h.2.2 (by omega)
  have hQt := hQ t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [linQuadPowReduce, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hw0 := hQ w hw
    simp [Defined, eval, hp, e1, toInt?_2 I, I.toInt?_cast]
    intro _; exact hw0
  · filter_upwards [hF] with w hw
    have hw0 := hQ w hw
    simp [linQuadPowReduce, Defined, eval, recEnv, toInt?_m1 I, toInt?_2 I, hp, e1, I.toInt?_cast]
    have hD2 : ¬ env "b" ^ 2 + -(4 * env "a" * env "c") = 0 := fun h => hD (by linear_combination h)
    exact ⟨⟨⟨hp1, hD2⟩, fun _ => hw0⟩, hp1, hD2⟩
  · simp only [linQuadPowReduce, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hK : ((p : 𝕜) + 1) * (env "b" ^ 2 + -(4 * env "a" * env "c")) ≠ 0 :=
      mul_ne_zero hp1 (fun h => hD (by linear_combination h))
    have hfun : (fun w => eval I (recEnv env (linQuadPowReduce.integrals.map (·.1)) Φ "x" w)
        linQuadPowReduce.result) = fun w =>
          (env "b" * env "d" + -(2 * env "a" * env "e") + (2 * env "c" * env "d" + -(env "b" * env "e")) * w) *
            (((p : 𝕜) + 1) * (env "b" ^ 2 + -(4 * env "a" * env "c")))⁻¹ * Q w ^ (p + 1) +
          -(2 * (p : 𝕜) + 3) * (2 * env "c" * env "d" + -(env "b" * env "e")) *
            (((p : 𝕜) + 1) * (env "b" ^ 2 + -(4 * env "a" * env "c")))⁻¹ * Φ "I1" w := by
      funext w
      simp [linQuadPowReduce, eval, recEnv, toInt?_m1 I, toInt?_2 I, hp, e1, I.toInt?_cast, hQdef]
      try ring_nf
      try simp
    rw [hfun]
    have hQd : HasDerivAt Q (env "b" + 2 * env "c" * t) t := by
      have := (((hasDerivAt_id t).const_mul (env "b")).const_add (env "a")).add
        ((hasDerivAt_pow 2 t).const_mul (env "c"))
      convert this using 1 <;> first | rfl | (simp; ring)
    have hZ : HasDerivAt (fun w => Q w ^ (p + 1))
        (((p : 𝕜) + 1) * Q t ^ p * (env "b" + 2 * env "c" * t)) t := by
      have := (hasDerivAt_zpow (p + 1) (Q t) (Or.inl hQt)).comp t hQd
      convert this using 1 <;> first | rfl | (rw [add_sub_cancel_right]; push_cast; ring)
    have hL : HasDerivAt (fun w : 𝕜 => env "b" * env "d" + -(2 * env "a" * env "e") +
        (2 * env "c" * env "d" + -(env "b" * env "e")) * w)
        (2 * env "c" * env "d" + -(env "b" * env "e")) t := by
      simpa using ((hasDerivAt_id t).const_mul (2 * env "c" * env "d" + -(env "b" * env "e"))).const_add
        (env "b" * env "d" + -(2 * env "a" * env "e"))
    refine (((hL.mul_const _).mul hZ).add (hΦ.const_mul _)).congr_deriv ?_
    simp [linQuadPowReduce, eval, toInt?_2 I, hp, e1, I.toInt?_cast]
    simp only [show env "a" + env "b" * t + env "c" * t ^ 2 = Q t from rfl, zpow_add_one₀ hQt]
    have hQv : Q t = env "a" + env "b" * t + env "c" * t ^ 2 := rfl
    have hDi := mul_inv_cancel₀ (show env "b" ^ 2 + -(4 * env "a" * env "c") ≠ 0 from
      fun h => hD (by linear_combination h))
    have hPi := mul_inv_cancel₀ hp1
    linear_combination (Q t ^ p * (env "d" + env "e" * t) * ((p : 𝕜) + 1) * ((p : 𝕜) + 1)⁻¹) * hDi +
      Q t ^ p * (env "d" + env "e" * t) * hPi +
      (-2 * (2 * env "c" * env "d" - env "b" * env "e") * ((p : 𝕜) + 1) *
        (((p : 𝕜) + 1) * (env "b" ^ 2 + -(4 * env "a" * env "c")))⁻¹ * Q t ^ p) * hQv

theorem linQuadPowReduce_real : linQuadPowReduce.Holds .real :=
  linQuadPowReduce_holds Interp.real Interp.real_lt_rat

theorem linQuadPowReduce_complex : linQuadPowReduce.Holds .complex :=
  linQuadPowReduce_holds Interp.complex Interp.complex_lt_rat

end Proofs

end OSR.IntegrationRec10
