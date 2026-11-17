import OSR.IntegrationRec91

/-!
# Integration (RUBI): strengthened variant of 1.1.1.3 #53

RUBI 1.1.1.3 #53 splits `∫ (a + b x)^m (c + d x)^n / (e + f x)²` into two
residual integrals with `(a + b x)^(m-1) (c + d x)^(n-1)`.  RUBI's `m + n > 0`
allows `n = 0` (or `m = 0`), where a residual integrand has a pole that the
integrand does not.  With `m > 0`, `n > 0` and RUBI's own `f² ≠ 0` the split
holds, since `2 b d e = f (b c + a d)` gives `f² (a + b x)(c + d x) = b d (e +
f x)² + (b e - a f)(d e - c f)`.  Proved over ℝ and ℂ.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec115

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- rubi_1_1_1_3_r53 with NeQ[Power[f, 2], 0]; GtQ[m, 0]; GtQ[n, 0] -/
def rubi1113r53Nondeg : CRule where
  id := "integration.rubi_1_1_1_3_r53_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p:53"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n"))) (.pow (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.pow (.pow (.var "f") (.int 2)) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f"))) (.app2 .add (.app2 .mul (.var "d") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f")))) (.pow (.pow (.var "f") (.int 2)) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.int (.app2 .add (.var "m") (.var "n")),
    .gt (.app2 .add (.var "m") (.var "n")) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "d")) (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a") (.var "d"))))) (.int 0),
    .ne (.pow (.var "f") (.int 2)) (.int 0),
    .gt (.var "m") (.int 0),
    .gt (.var "n") (.int 0)]
  priority := 9331
  description := "rubi_1_1_1_3_r53 with NeQ[Power[f, 2], 0]; GtQ[m, 0]; GtQ[n, 0]"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p:53" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p.m#53"

/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem toInt?_neg_one (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem toInt?_two (I : Interp 𝕜) : I.toInt? (2 : 𝕜) = some 2 :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem zpow_succ_of (A : 𝕜) (k : ℤ) (h : A ≠ 0 ∨ 0 ≤ k) : A ^ (k + 1) = A ^ k * A := by
  rcases h with h | h
  · exact zpow_add_one₀ h k
  · lift k to ℕ using h
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
      pow_succ]

theorem rubi1113r53Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi1113r53Nondeg.conditions rubi1113r53Nondeg.body rubi1113r53Nondeg.result rubi1113r53Nondeg.integrals := by
  intro env hc t hF
  have ord : ∀ (x y : ℤ), I.lt (x : 𝕜) (y : 𝕜) → x < y := by
    intro x y h
    have h' : I.lt ((x : ℚ) : 𝕜) ((y : ℚ) : 𝕜) := by rw [Rat.cast_intCast, Rat.cast_intCast]; exact h
    exact_mod_cast (hlt _ _).1 h'
  have heq0 := hc (.eq (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "d")) (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a") (.var "d"))))) (.int 0)) (by simp [rubi1113r53Nondeg])
  simp [Cond.Holds, Defined, eval] at heq0
  have heq : 2 * env "b" * env "d" * env "e" - env "f" * (env "b" * env "c" + env "a" * env "d") = 0 := by
    linear_combination heq0
  have gm := hc (.gt (.var "m") (.int 0)) (by simp [rubi1113r53Nondeg])
  have gn := hc (.gt (.var "n") (.int 0)) (by simp [rubi1113r53Nondeg])
  have hA := hc (.ne (.pow (.var "f") (.int 2)) (.int 0)) (by simp [rubi1113r53Nondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hA
  have hf0 : env "f" ≠ 0 := by
    intro h0; apply hA; simp [h0]
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi1113r53Nondeg, Defined, eval, hk_m] at h
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso; have h := hF.self_of_nhds; simp [rubi1113r53Nondeg, Defined, eval, hk_m, hk_n] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have hk : 0 < k := by
    simp only [Cond.Holds, Defined, eval, true_and] at gm; rw [h_m] at gm; exact ord _ _ (by push_cast; simpa using gm)
  have hj : 0 < j := by
    simp only [Cond.Holds, Defined, eval, true_and] at gn; rw [h_n] at gn; exact ord _ _ (by push_cast; simpa using gn)
  have em : I.toInt? (env "m" + -1 * 1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em' : I.toInt? (env "m" + -1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have en : I.toInt? (env "n" + -1 * 1) = some (j - 1) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have en' : I.toInt? (env "n" + -1) = some (j - 1) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have hk0 : ¬ k < 0 := by omega
  have hj0 : ¬ j < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have hj1 : ¬ j - 1 < 0 := by omega
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi1113r53Nondeg.body → (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simp [rubi1113r53Nondeg, Defined, eval, hk_m, hk_n, hk0, hj0, toInt?_two, toInt?_neg_one] at h
    first | exact h | exact h.2 | exact h.2.2 | (trace_state; sorry)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1113r53Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    · have h1 := hBody w hw
      simp [Defined, eval, hk_m, hk_n, em, em', en, en', hk1, hj1, toInt?_two, toInt?_neg_one, h1]
  · exact Eventually.of_forall fun w => by
      simp [rubi1113r53Nondeg, Defined, eval, recEnv, toInt?_neg_one, toInt?_two, hf0]
  · simp only [rubi1113r53Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hE0 := hBody t hF.self_of_nhds
    have hΦ1' : HasDerivAt (Φ "I1") ((env "a" + env "b" * t) ^ (k - 1) * (env "c" + env "d" * t) ^ (j - 1)) t := by
      convert hΦ1 using 1
      simp [eval, hk_m, hk_n, em, em', en, en']
    have hΦ2' : HasDerivAt (Φ "I2") ((env "a" + env "b" * t) ^ (k - 1) * (env "c" + env "d" * t) ^ (j - 1) * ((env "e" + env "f" * t) ^ 2)⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, hk_m, hk_n, em, em', en, en', toInt?_two, toInt?_neg_one]
    have hEF : eval I (Function.update env "x" t) rubi1113r53Nondeg.body = (env "a" + env "b" * t) ^ k * (env "c" + env "d" * t) ^ j * ((env "e" + env "f" * t) ^ 2)⁻¹ := by
      simp [rubi1113r53Nondeg, eval, hk_m, hk_n, toInt?_two, toInt?_neg_one]
    have hfun : (fun w => eval I (recEnv env (rubi1113r53Nondeg.integrals.map (·.1)) Φ "x" w) rubi1113r53Nondeg.result) =
        fun w => env "b" * env "d" * (env "f" ^ 2)⁻¹ * Φ "I1" w + (env "b" * env "e" + -1 * env "a" * env "f") * (env "d" * env "e" + -1 * env "c" * env "f") * (env "f" ^ 2)⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi1113r53Nondeg, eval, recEnv, toInt?_neg_one, toInt?_two, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have key : env "f" ^ 2 * ((env "a" + env "b" * t) * (env "c" + env "d" * t)) = env "b" * env "d" * (env "e" + env "f" * t) ^ 2 + (env "b" * env "e" + -1 * env "a" * env "f") * (env "d" * env "e" + -1 * env "c" * env "f") := by
      linear_combination (-(env "e" + env "f" * t)) * heq
    rw [show (env "a" + env "b" * t) ^ k = (env "a" + env "b" * t) ^ (k - 1) * (env "a" + env "b" * t) by rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel],
      show (env "c" + env "d" * t) ^ j = (env "c" + env "d" * t) ^ (j - 1) * (env "c" + env "d" * t) by rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]]
    generalize (env "a" + env "b" * t) ^ (k - 1) = Ak at key ⊢
    generalize (env "c" + env "d" * t) ^ (j - 1) = Cj at key ⊢
    field_simp
    first | linear_combination (Ak * Cj) * key | linear_combination (-(Ak * Cj)) * key | (trace_state; sorry)

theorem rubi1113r53Nondeg_real : rubi1113r53Nondeg.Holds .real := rubi1113r53Nondeg_holds Interp.real Interp.real_lt_rat
theorem rubi1113r53Nondeg_complex : rubi1113r53Nondeg.Holds .complex := rubi1113r53Nondeg_holds Interp.complex Interp.complex_lt_rat

end Proofs

end OSR.IntegrationRec115
