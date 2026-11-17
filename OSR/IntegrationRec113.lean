import OSR.IntegrationRec91

/-!
# Integration (RUBI): strengthened variants of refuted named rules, 1.2.2.4 #59–62

RUBI 1.2.2.4 #59–62 split `∫ (f x)^m (a + b x² + c x⁴)^p / (d + e x²)` into two
residual integrals with `(f x)^(m-4)` (#59, #60) or `(f x)^(m-2)` (#61, #62).
RUBI's `m > 2` (resp. `m > 0`) leaves the integer `m = 3` (resp. `m = 1`), where
the residual integrands have a pole at `x = 0` that the integrand does not.
With `m > 3` (resp. `m > 1`) and RUBI's own `c d² - b d e + a e² ≠ 0` the
split holds, since `d² P - (a d + (b d - a e) x²)(d + e x²) = (c d² - b d e +
a e²) x⁴` (and its analogues).  Proved over ℝ and ℂ.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec113

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/
/-- rubi_1_2_2_4_r59 with NeQ[Add[Multiply[c, Power[d, 2]], Multiply[-1, b, d, e], Multiply[a, Power[e, 2]]], 0]; GtQ[m, 3] -/
def rubi1224r59Nondeg : CRule where
  id := "integration.rubi_1_2_2_4_r59_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:59"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "f") (.int 4))) (.pow (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "d") (.int 2)) (.pow (.var "f") (.int 4))) (.pow (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 4)))) (.app2 .add (.app2 .mul (.var "a") (.var "d")) (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "e"))) (.pow (.var "x") (.int 2))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.var "p")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 4)))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .gt (.int (-1)) (.var "p"),
    .gt (.var "m") (.int 2),
    .ne (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .gt (.var "m") (.int 3)]
  priority := 9311
  description := "rubi_1_2_2_4_r59 with NeQ[Add[Multiply[c, Power[d, 2]], Multiply[-1, b, d, e], Multiply[a, Power[e, 2]]], 0]; GtQ[m, 3]"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:59" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p.m#59"

/-- rubi_1_2_2_4_r60 with NeQ[Add[Multiply[c, Power[d, 2]], Multiply[a, Power[e, 2]]], 0]; GtQ[m, 3] -/
def rubi1224r60Nondeg : CRule where
  id := "integration.rubi_1_2_2_4_r60_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:60"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.var "f") (.int 4))) (.pow (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "d") (.int 2)) (.pow (.var "f") (.int 4))) (.pow (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 4)))) (.app2 .add (.var "d") (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.var "x") (.int 2))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.var "p")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 4)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "c", "d", "e", "f", "m", "p"]
  conditions := [.gt (.int (-1)) (.var "p"),
    .gt (.var "m") (.int 2),
    .ne (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .gt (.var "m") (.int 3)]
  priority := 9312
  description := "rubi_1_2_2_4_r60 with NeQ[Add[Multiply[c, Power[d, 2]], Multiply[a, Power[e, 2]]], 0]; GtQ[m, 3]"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:60" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p.m#60"

/-- rubi_1_2_2_4_r61 with NeQ[Add[Multiply[c, Power[d, 2]], Multiply[-1, b, d, e], Multiply[a, Power[e, 2]]], 0]; GtQ[m, 1] -/
def rubi1224r61Nondeg : CRule where
  id := "integration.rubi_1_2_2_4_r61_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:61"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "f") (.int 2)) (.pow (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "e")) (.pow (.var "f") (.int 2))) (.pow (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.app2 .add (.app2 .mul (.var "a") (.var "e")) (.app2 .mul (.app2 .mul (.var "c") (.var "d")) (.pow (.var "x") (.int 2))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.var "p")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .gt (.int (-1)) (.var "p"),
    .gt (.var "m") (.int 0),
    .ne (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .gt (.var "m") (.int 1)]
  priority := 9313
  description := "rubi_1_2_2_4_r61 with NeQ[Add[Multiply[c, Power[d, 2]], Multiply[-1, b, d, e], Multiply[a, Power[e, 2]]], 0]; GtQ[m, 1]"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:61" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p.m#61"

/-- rubi_1_2_2_4_r62 with NeQ[Add[Multiply[c, Power[d, 2]], Multiply[a, Power[e, 2]]], 0]; GtQ[m, 1] -/
def rubi1224r62Nondeg : CRule where
  id := "integration.rubi_1_2_2_4_r62_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:62"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "f") (.int 2)) (.pow (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "e")) (.pow (.var "f") (.int 2))) (.pow (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.app2 .add (.app2 .mul (.var "a") (.var "e")) (.app2 .mul (.app2 .mul (.var "c") (.var "d")) (.pow (.var "x") (.int 2))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.var "p")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "c", "d", "e", "f", "m", "p"]
  conditions := [.gt (.int (-1)) (.var "p"),
    .gt (.var "m") (.int 0),
    .ne (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .gt (.var "m") (.int 1)]
  priority := 9314
  description := "rubi_1_2_2_4_r62 with NeQ[Add[Multiply[c, Power[d, 2]], Multiply[a, Power[e, 2]]], 0]; GtQ[m, 1]"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:62" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p.m#62"


/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem toInt?_neg_one (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem toInt?_two (I : Interp 𝕜) : I.toInt? (2 : 𝕜) = some 2 :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem toInt?_four (I : Interp 𝕜) : I.toInt? (4 : 𝕜) = some 4 :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem zpow_succ_of (A : 𝕜) (k : ℤ) (h : A ≠ 0 ∨ 0 ≤ k) : A ^ (k + 1) = A ^ k * A := by
  rcases h with h | h
  · exact zpow_add_one₀ h k
  · lift k to ℕ using h
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
      pow_succ]

theorem rubi1224r59Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi1224r59Nondeg.conditions rubi1224r59Nondeg.body rubi1224r59Nondeg.result rubi1224r59Nondeg.integrals := by
  intro env hc t hF
  have ord : ∀ (x y : ℤ), I.lt (x : 𝕜) (y : 𝕜) → x < y := by
    intro x y h
    have h' : I.lt ((x : ℚ) : 𝕜) ((y : ℚ) : 𝕜) := by rw [Rat.cast_intCast, Rat.cast_intCast]; exact h
    exact_mod_cast (hlt _ _).1 h'
  have gp := hc (.gt (.int (-1)) (.var "p")) (by simp [rubi1224r59Nondeg])
  have gm := hc (.gt (.var "m") (.int 3)) (by simp [rubi1224r59Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi1224r59Nondeg, Defined, eval, hk_m] at h
  rcases hk_p : I.toInt? (env "p") with _ | q
  · exfalso; have h := hF.self_of_nhds; simp [rubi1224r59Nondeg, Defined, eval, hk_m, hk_p] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have h_p : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have hq : q < -1 := by
    simp only [Cond.Holds, Defined, eval, true_and] at gp; rw [h_p] at gp; exact ord _ _ (by push_cast; simpa using gp)
  have hk : 3 < k := by
    simp only [Cond.Holds, Defined, eval, true_and] at gm; rw [h_m] at gm; exact ord _ _ (by push_cast; simpa using gm)
  have hA := hc (.ne (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1224r59Nondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hA
  have hD : env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2 ≠ 0 := by
    intro h0; apply hA; linear_combination h0
  have em : I.toInt? (env "m" + -1 * 4) = some (k - 4) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em' : I.toInt? (env "m" + -4) = some (k - 4) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em'' : I.toInt? (env "m" - 4) = some (k - 4) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have ep : I.toInt? (env "p" + 1) = some (q + 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have hk0 : ¬ k < 0 := by omega
  have hks : ¬ k - 4 < 0 := by omega
  have hq0 : q < 0 := by omega
  have hq1 : q + 1 < 0 := by omega
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi1224r59Nondeg.body →
      (env "a" + env "b" * w ^ 2 + env "c" * w ^ 4) ≠ 0 ∧ (env "d" + env "e" * w ^ 2) ≠ 0 := by
    intro w h
    simp [rubi1224r59Nondeg, Defined, eval, hk_m, hk_p, toInt?_two, toInt?_four, hk0, hq0, toInt?_neg_one] at h
    first | exact ⟨h.1, h.2⟩ | exact ⟨h.1.1 hq0, h.2⟩ | exact ⟨h.1 hq0, h.2⟩ | exact ⟨h.2.1, h.2.2⟩ | (trace_state; sorry)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1224r59Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    · obtain ⟨h1, h2⟩ := hBody w hw
      simp [Defined, eval, hk_m, hk_p, em, em', em'', ep, hks, hq0, hq1, toInt?_two, toInt?_four, toInt?_neg_one, h1, h2]
  · exact Eventually.of_forall fun w => by
      simp [rubi1224r59Nondeg, Defined, eval, recEnv, toInt?_neg_one, toInt?_two, toInt?_four, hA]
  · simp only [rubi1224r59Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    obtain ⟨hP0, hE0⟩ := hBody t hF.self_of_nhds
    have hΦ1' : HasDerivAt (Φ "I1") ((env "f" * t) ^ (k - 4) * (env "a" * env "d" + (env "b" * env "d" + -1 * env "a" * env "e") * t ^ 2) * (env "a" + env "b" * t ^ 2 + env "c" * t ^ 4) ^ q) t := by
      convert hΦ1 using 1
      simp [eval, hk_m, hk_p, em, em', em'', toInt?_two, toInt?_four, toInt?_neg_one]
      try ring
    have hΦ2' : HasDerivAt (Φ "I2") ((env "f" * t) ^ (k - 4) * (env "a" + env "b" * t ^ 2 + env "c" * t ^ 4) ^ (q + 1) * (env "d" + env "e" * t ^ 2)⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, hk_m, hk_p, em, em', em'', ep, toInt?_two, toInt?_four, toInt?_neg_one]
      try ring
    have hEF : eval I (Function.update env "x" t) rubi1224r59Nondeg.body = (env "f" * t) ^ k * (env "a" + env "b" * t ^ 2 + env "c" * t ^ 4) ^ q * (env "d" + env "e" * t ^ 2)⁻¹ := by
      simp [rubi1224r59Nondeg, eval, hk_m, hk_p, toInt?_two, toInt?_four, toInt?_neg_one]
    have hfun : (fun w => eval I (recEnv env (rubi1224r59Nondeg.integrals.map (·.1)) Φ "x" w) rubi1224r59Nondeg.result) =
        fun w => -1 * env "f" ^ 4 * (env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2)⁻¹ * Φ "I1" w + env "d" ^ 2 * env "f" ^ 4 * (env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2)⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi1224r59Nondeg, eval, recEnv, toInt?_neg_one, toInt?_two, toInt?_four, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have hsplit : (env "f" * t) ^ k = (env "f" * t) ^ (k - 4) * (env "f" * t) ^ (4 : ℕ) := by
      rw [← zpow_natCast, ← zpow_add' (a := env "f" * t) (m := k - 4) (n := ((4 : ℕ) : ℤ)) (Or.inr (Or.inl (by omega)))]; congr 1; push_cast; ring
    rw [hsplit, zpow_succ_of _ (q) (Or.inl hP0)]
    generalize (env "f" * t) ^ (k - 4) = Ek
    generalize (env "a" + env "b" * t ^ 2 + env "c" * t ^ 4) ^ q = Qp
    generalize hDe : (env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2) = Dd at hD ⊢
    field_simp
    subst hDe
    ring

theorem rubi1224r60Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi1224r60Nondeg.conditions rubi1224r60Nondeg.body rubi1224r60Nondeg.result rubi1224r60Nondeg.integrals := by
  intro env hc t hF
  have ord : ∀ (x y : ℤ), I.lt (x : 𝕜) (y : 𝕜) → x < y := by
    intro x y h
    have h' : I.lt ((x : ℚ) : 𝕜) ((y : ℚ) : 𝕜) := by rw [Rat.cast_intCast, Rat.cast_intCast]; exact h
    exact_mod_cast (hlt _ _).1 h'
  have gp := hc (.gt (.int (-1)) (.var "p")) (by simp [rubi1224r60Nondeg])
  have gm := hc (.gt (.var "m") (.int 3)) (by simp [rubi1224r60Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi1224r60Nondeg, Defined, eval, hk_m] at h
  rcases hk_p : I.toInt? (env "p") with _ | q
  · exfalso; have h := hF.self_of_nhds; simp [rubi1224r60Nondeg, Defined, eval, hk_m, hk_p] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have h_p : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have hq : q < -1 := by
    simp only [Cond.Holds, Defined, eval, true_and] at gp; rw [h_p] at gp; exact ord _ _ (by push_cast; simpa using gp)
  have hk : 3 < k := by
    simp only [Cond.Holds, Defined, eval, true_and] at gm; rw [h_m] at gm; exact ord _ _ (by push_cast; simpa using gm)
  have hA := hc (.ne (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1224r60Nondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hA
  have hD : env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2 ≠ 0 := by
    intro h0; apply hA; linear_combination h0
  have em : I.toInt? (env "m" + -1 * 4) = some (k - 4) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em' : I.toInt? (env "m" + -4) = some (k - 4) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em'' : I.toInt? (env "m" - 4) = some (k - 4) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have ep : I.toInt? (env "p" + 1) = some (q + 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have hk0 : ¬ k < 0 := by omega
  have hks : ¬ k - 4 < 0 := by omega
  have hq0 : q < 0 := by omega
  have hq1 : q + 1 < 0 := by omega
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi1224r60Nondeg.body →
      (env "a" + env "c" * w ^ 4) ≠ 0 ∧ (env "d" + env "e" * w ^ 2) ≠ 0 := by
    intro w h
    simp [rubi1224r60Nondeg, Defined, eval, hk_m, hk_p, toInt?_two, toInt?_four, hk0, hq0, toInt?_neg_one] at h
    first | exact ⟨h.1, h.2⟩ | exact ⟨h.1.1 hq0, h.2⟩ | exact ⟨h.1 hq0, h.2⟩ | exact ⟨h.2.1, h.2.2⟩ | (trace_state; sorry)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1224r60Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    · obtain ⟨h1, h2⟩ := hBody w hw
      simp [Defined, eval, hk_m, hk_p, em, em', em'', ep, hks, hq0, hq1, toInt?_two, toInt?_four, toInt?_neg_one, h1, h2]
  · exact Eventually.of_forall fun w => by
      simp [rubi1224r60Nondeg, Defined, eval, recEnv, toInt?_neg_one, toInt?_two, toInt?_four, hA]
  · simp only [rubi1224r60Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    obtain ⟨hP0, hE0⟩ := hBody t hF.self_of_nhds
    have hΦ1' : HasDerivAt (Φ "I1") ((env "f" * t) ^ (k - 4) * (env "d" + -1 * env "e" * t ^ 2) * (env "a" + env "c" * t ^ 4) ^ q) t := by
      convert hΦ1 using 1
      simp [eval, hk_m, hk_p, em, em', em'', toInt?_two, toInt?_four, toInt?_neg_one]
      try ring
    have hΦ2' : HasDerivAt (Φ "I2") ((env "f" * t) ^ (k - 4) * (env "a" + env "c" * t ^ 4) ^ (q + 1) * (env "d" + env "e" * t ^ 2)⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, hk_m, hk_p, em, em', em'', ep, toInt?_two, toInt?_four, toInt?_neg_one]
      try ring
    have hEF : eval I (Function.update env "x" t) rubi1224r60Nondeg.body = (env "f" * t) ^ k * (env "a" + env "c" * t ^ 4) ^ q * (env "d" + env "e" * t ^ 2)⁻¹ := by
      simp [rubi1224r60Nondeg, eval, hk_m, hk_p, toInt?_two, toInt?_four, toInt?_neg_one]
    have hfun : (fun w => eval I (recEnv env (rubi1224r60Nondeg.integrals.map (·.1)) Φ "x" w) rubi1224r60Nondeg.result) =
        fun w => -1 * env "a" * env "f" ^ 4 * (env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2)⁻¹ * Φ "I1" w + env "d" ^ 2 * env "f" ^ 4 * (env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2)⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi1224r60Nondeg, eval, recEnv, toInt?_neg_one, toInt?_two, toInt?_four, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have hsplit : (env "f" * t) ^ k = (env "f" * t) ^ (k - 4) * (env "f" * t) ^ (4 : ℕ) := by
      rw [← zpow_natCast, ← zpow_add' (a := env "f" * t) (m := k - 4) (n := ((4 : ℕ) : ℤ)) (Or.inr (Or.inl (by omega)))]; congr 1; push_cast; ring
    rw [hsplit, zpow_succ_of _ (q) (Or.inl hP0)]
    generalize (env "f" * t) ^ (k - 4) = Ek
    generalize (env "a" + env "c" * t ^ 4) ^ q = Qp
    generalize hDe : (env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2) = Dd at hD ⊢
    field_simp
    subst hDe
    ring

theorem rubi1224r61Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi1224r61Nondeg.conditions rubi1224r61Nondeg.body rubi1224r61Nondeg.result rubi1224r61Nondeg.integrals := by
  intro env hc t hF
  have ord : ∀ (x y : ℤ), I.lt (x : 𝕜) (y : 𝕜) → x < y := by
    intro x y h
    have h' : I.lt ((x : ℚ) : 𝕜) ((y : ℚ) : 𝕜) := by rw [Rat.cast_intCast, Rat.cast_intCast]; exact h
    exact_mod_cast (hlt _ _).1 h'
  have gp := hc (.gt (.int (-1)) (.var "p")) (by simp [rubi1224r61Nondeg])
  have gm := hc (.gt (.var "m") (.int 1)) (by simp [rubi1224r61Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi1224r61Nondeg, Defined, eval, hk_m] at h
  rcases hk_p : I.toInt? (env "p") with _ | q
  · exfalso; have h := hF.self_of_nhds; simp [rubi1224r61Nondeg, Defined, eval, hk_m, hk_p] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have h_p : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have hq : q < -1 := by
    simp only [Cond.Holds, Defined, eval, true_and] at gp; rw [h_p] at gp; exact ord _ _ (by push_cast; simpa using gp)
  have hk : 1 < k := by
    simp only [Cond.Holds, Defined, eval, true_and] at gm; rw [h_m] at gm; exact ord _ _ (by push_cast; simpa using gm)
  have hA := hc (.ne (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1224r61Nondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hA
  have hD : env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2 ≠ 0 := by
    intro h0; apply hA; linear_combination h0
  have em : I.toInt? (env "m" + -1 * 2) = some (k - 2) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em' : I.toInt? (env "m" + -2) = some (k - 2) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em'' : I.toInt? (env "m" - 2) = some (k - 2) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have ep : I.toInt? (env "p" + 1) = some (q + 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have hk0 : ¬ k < 0 := by omega
  have hks : ¬ k - 2 < 0 := by omega
  have hq0 : q < 0 := by omega
  have hq1 : q + 1 < 0 := by omega
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi1224r61Nondeg.body →
      (env "a" + env "b" * w ^ 2 + env "c" * w ^ 4) ≠ 0 ∧ (env "d" + env "e" * w ^ 2) ≠ 0 := by
    intro w h
    simp [rubi1224r61Nondeg, Defined, eval, hk_m, hk_p, toInt?_two, toInt?_four, hk0, hq0, toInt?_neg_one] at h
    first | exact ⟨h.1, h.2⟩ | exact ⟨h.1.1 hq0, h.2⟩ | exact ⟨h.1 hq0, h.2⟩ | exact ⟨h.2.1, h.2.2⟩ | (trace_state; sorry)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1224r61Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    · obtain ⟨h1, h2⟩ := hBody w hw
      simp [Defined, eval, hk_m, hk_p, em, em', em'', ep, hks, hq0, hq1, toInt?_two, toInt?_four, toInt?_neg_one, h1, h2]
  · exact Eventually.of_forall fun w => by
      simp [rubi1224r61Nondeg, Defined, eval, recEnv, toInt?_neg_one, toInt?_two, toInt?_four, hA]
  · simp only [rubi1224r61Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    obtain ⟨hP0, hE0⟩ := hBody t hF.self_of_nhds
    have hΦ1' : HasDerivAt (Φ "I1") ((env "f" * t) ^ (k - 2) * (env "a" * env "e" + env "c" * env "d" * t ^ 2) * (env "a" + env "b" * t ^ 2 + env "c" * t ^ 4) ^ q) t := by
      convert hΦ1 using 1
      simp [eval, hk_m, hk_p, em, em', em'', toInt?_two, toInt?_four, toInt?_neg_one]
      try ring
    have hΦ2' : HasDerivAt (Φ "I2") ((env "f" * t) ^ (k - 2) * (env "a" + env "b" * t ^ 2 + env "c" * t ^ 4) ^ (q + 1) * (env "d" + env "e" * t ^ 2)⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, hk_m, hk_p, em, em', em'', ep, toInt?_two, toInt?_four, toInt?_neg_one]
      try ring
    have hEF : eval I (Function.update env "x" t) rubi1224r61Nondeg.body = (env "f" * t) ^ k * (env "a" + env "b" * t ^ 2 + env "c" * t ^ 4) ^ q * (env "d" + env "e" * t ^ 2)⁻¹ := by
      simp [rubi1224r61Nondeg, eval, hk_m, hk_p, toInt?_two, toInt?_four, toInt?_neg_one]
    have hfun : (fun w => eval I (recEnv env (rubi1224r61Nondeg.integrals.map (·.1)) Φ "x" w) rubi1224r61Nondeg.result) =
        fun w => env "f" ^ 2 * (env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2)⁻¹ * Φ "I1" w + -1 * env "d" * env "e" * env "f" ^ 2 * (env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2)⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi1224r61Nondeg, eval, recEnv, toInt?_neg_one, toInt?_two, toInt?_four, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have hsplit : (env "f" * t) ^ k = (env "f" * t) ^ (k - 2) * (env "f" * t) ^ (2 : ℕ) := by
      rw [← zpow_natCast, ← zpow_add' (a := env "f" * t) (m := k - 2) (n := ((2 : ℕ) : ℤ)) (Or.inr (Or.inl (by omega)))]; congr 1; push_cast; ring
    rw [hsplit, zpow_succ_of _ (q) (Or.inl hP0)]
    generalize (env "f" * t) ^ (k - 2) = Ek
    generalize (env "a" + env "b" * t ^ 2 + env "c" * t ^ 4) ^ q = Qp
    generalize hDe : (env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2) = Dd at hD ⊢
    field_simp
    subst hDe
    ring

theorem rubi1224r62Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi1224r62Nondeg.conditions rubi1224r62Nondeg.body rubi1224r62Nondeg.result rubi1224r62Nondeg.integrals := by
  intro env hc t hF
  have ord : ∀ (x y : ℤ), I.lt (x : 𝕜) (y : 𝕜) → x < y := by
    intro x y h
    have h' : I.lt ((x : ℚ) : 𝕜) ((y : ℚ) : 𝕜) := by rw [Rat.cast_intCast, Rat.cast_intCast]; exact h
    exact_mod_cast (hlt _ _).1 h'
  have gp := hc (.gt (.int (-1)) (.var "p")) (by simp [rubi1224r62Nondeg])
  have gm := hc (.gt (.var "m") (.int 1)) (by simp [rubi1224r62Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi1224r62Nondeg, Defined, eval, hk_m] at h
  rcases hk_p : I.toInt? (env "p") with _ | q
  · exfalso; have h := hF.self_of_nhds; simp [rubi1224r62Nondeg, Defined, eval, hk_m, hk_p] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have h_p : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have hq : q < -1 := by
    simp only [Cond.Holds, Defined, eval, true_and] at gp; rw [h_p] at gp; exact ord _ _ (by push_cast; simpa using gp)
  have hk : 1 < k := by
    simp only [Cond.Holds, Defined, eval, true_and] at gm; rw [h_m] at gm; exact ord _ _ (by push_cast; simpa using gm)
  have hA := hc (.ne (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1224r62Nondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hA
  have hD : env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2 ≠ 0 := by
    intro h0; apply hA; linear_combination h0
  have em : I.toInt? (env "m" + -1 * 2) = some (k - 2) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em' : I.toInt? (env "m" + -2) = some (k - 2) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em'' : I.toInt? (env "m" - 2) = some (k - 2) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have ep : I.toInt? (env "p" + 1) = some (q + 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have hk0 : ¬ k < 0 := by omega
  have hks : ¬ k - 2 < 0 := by omega
  have hq0 : q < 0 := by omega
  have hq1 : q + 1 < 0 := by omega
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi1224r62Nondeg.body →
      (env "a" + env "c" * w ^ 4) ≠ 0 ∧ (env "d" + env "e" * w ^ 2) ≠ 0 := by
    intro w h
    simp [rubi1224r62Nondeg, Defined, eval, hk_m, hk_p, toInt?_two, toInt?_four, hk0, hq0, toInt?_neg_one] at h
    first | exact ⟨h.1, h.2⟩ | exact ⟨h.1.1 hq0, h.2⟩ | exact ⟨h.1 hq0, h.2⟩ | exact ⟨h.2.1, h.2.2⟩ | (trace_state; sorry)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1224r62Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    · obtain ⟨h1, h2⟩ := hBody w hw
      simp [Defined, eval, hk_m, hk_p, em, em', em'', ep, hks, hq0, hq1, toInt?_two, toInt?_four, toInt?_neg_one, h1, h2]
  · exact Eventually.of_forall fun w => by
      simp [rubi1224r62Nondeg, Defined, eval, recEnv, toInt?_neg_one, toInt?_two, toInt?_four, hA]
  · simp only [rubi1224r62Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    obtain ⟨hP0, hE0⟩ := hBody t hF.self_of_nhds
    have hΦ1' : HasDerivAt (Φ "I1") ((env "f" * t) ^ (k - 2) * (env "a" * env "e" + env "c" * env "d" * t ^ 2) * (env "a" + env "c" * t ^ 4) ^ q) t := by
      convert hΦ1 using 1
      simp [eval, hk_m, hk_p, em, em', em'', toInt?_two, toInt?_four, toInt?_neg_one]
      try ring
    have hΦ2' : HasDerivAt (Φ "I2") ((env "f" * t) ^ (k - 2) * (env "a" + env "c" * t ^ 4) ^ (q + 1) * (env "d" + env "e" * t ^ 2)⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, hk_m, hk_p, em, em', em'', ep, toInt?_two, toInt?_four, toInt?_neg_one]
      try ring
    have hEF : eval I (Function.update env "x" t) rubi1224r62Nondeg.body = (env "f" * t) ^ k * (env "a" + env "c" * t ^ 4) ^ q * (env "d" + env "e" * t ^ 2)⁻¹ := by
      simp [rubi1224r62Nondeg, eval, hk_m, hk_p, toInt?_two, toInt?_four, toInt?_neg_one]
    have hfun : (fun w => eval I (recEnv env (rubi1224r62Nondeg.integrals.map (·.1)) Φ "x" w) rubi1224r62Nondeg.result) =
        fun w => env "f" ^ 2 * (env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2)⁻¹ * Φ "I1" w + -1 * env "d" * env "e" * env "f" ^ 2 * (env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2)⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi1224r62Nondeg, eval, recEnv, toInt?_neg_one, toInt?_two, toInt?_four, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have hsplit : (env "f" * t) ^ k = (env "f" * t) ^ (k - 2) * (env "f" * t) ^ (2 : ℕ) := by
      rw [← zpow_natCast, ← zpow_add' (a := env "f" * t) (m := k - 2) (n := ((2 : ℕ) : ℤ)) (Or.inr (Or.inl (by omega)))]; congr 1; push_cast; ring
    rw [hsplit, zpow_succ_of _ (q) (Or.inl hP0)]
    generalize (env "f" * t) ^ (k - 2) = Ek
    generalize (env "a" + env "c" * t ^ 4) ^ q = Qp
    generalize hDe : (env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2) = Dd at hD ⊢
    field_simp
    subst hDe
    ring

theorem rubi1224r59Nondeg_real : rubi1224r59Nondeg.Holds .real := rubi1224r59Nondeg_holds Interp.real Interp.real_lt_rat
theorem rubi1224r59Nondeg_complex : rubi1224r59Nondeg.Holds .complex := rubi1224r59Nondeg_holds Interp.complex Interp.complex_lt_rat
theorem rubi1224r60Nondeg_real : rubi1224r60Nondeg.Holds .real := rubi1224r60Nondeg_holds Interp.real Interp.real_lt_rat
theorem rubi1224r60Nondeg_complex : rubi1224r60Nondeg.Holds .complex := rubi1224r60Nondeg_holds Interp.complex Interp.complex_lt_rat
theorem rubi1224r61Nondeg_real : rubi1224r61Nondeg.Holds .real := rubi1224r61Nondeg_holds Interp.real Interp.real_lt_rat
theorem rubi1224r61Nondeg_complex : rubi1224r61Nondeg.Holds .complex := rubi1224r61Nondeg_holds Interp.complex Interp.complex_lt_rat
theorem rubi1224r62Nondeg_real : rubi1224r62Nondeg.Holds .real := rubi1224r62Nondeg_holds Interp.real Interp.real_lt_rat
theorem rubi1224r62Nondeg_complex : rubi1224r62Nondeg.Holds .complex := rubi1224r62Nondeg_holds Interp.complex Interp.complex_lt_rat

end Proofs

end OSR.IntegrationRec113
