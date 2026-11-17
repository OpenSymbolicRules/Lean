import OSR.IntegrationRec91

/-!
# Integration (RUBI): strengthened variants of refuted named rules, sixth batch

RUBI 1.2.1.2 #5 and 1.2.3.3 #50 are refuted as stated (at `d = 0` or `e = 0`);
with `d ≠ 0` and `e ≠ 0` the condition `c d² - b d e + a e² = 0` factors the
trinomial as `(d + e y) (a/d + c y/e)`.  Proved over ℝ and ℂ; their candidates
were first sampled with the equality conditions solved.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec99

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- rubi_1_2_1_2_r5 with NeQ[d, 0]; NeQ[e, 0] -/
def rubi1212r5Nondeg : CRule where
  id := "integration.rubi_1_2_1_2_r5_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:5"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.var "I1")
  integrals := [("I1", .app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "p") (.int 1))) (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "e") (.int (-1)))) (.var "x"))) (.var "p")))]
  independent := ["a", "b", "c", "d", "e", "p"]
  conditions := [.ne (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0), .int (.var "p"), .gt (.var "p") (.int 0), .eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .ne (.var "d") (.int 0),
    .ne (.var "e") (.int 0)]
  priority := 9171
  description := "rubi_1_2_1_2_r5 with NeQ[d, 0]; NeQ[e, 0]"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:5" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#5"

/-- rubi_1_2_3_3_r50 with NeQ[d, 0]; NeQ[e, 0] -/
def rubi1233r50Nondeg : CRule where
  id := "integration.rubi_1_2_3_3_r50_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:50"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "q")) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.var "n")))) (.var "r"))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p")))
  result := (.var "I1")
  integrals := [("I1", .app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.var "q"))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.var "n")))) (.var "r"))) (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "e") (.int (-1)))) (.pow (.var "x") (.var "n")))) (.var "p")))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "n", "q", "r", "n2", "p"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")), .ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0), .eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0), .int (.var "p"),
    .ne (.var "d") (.int 0),
    .ne (.var "e") (.int 0)]
  priority := 9172
  description := "rubi_1_2_3_3_r50 with NeQ[d, 0]; NeQ[e, 0]"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:50" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#50"


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

theorem rubi1212r5Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi1212r5Nondeg.conditions rubi1212r5Nondeg.body rubi1212r5Nondeg.result rubi1212r5Nondeg.integrals := by
  intro env hc t hF
  have heq : env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1212r5Nondeg])
    simp [Cond.Holds, Defined, eval, toInt?_two] at h
    linear_combination h
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi1212r5Nondeg]); simpa [Cond.Holds, Defined, eval] using h
  have he : env "e" ≠ 0 := by
    have h := hc (.ne (.var "e") (.int 0)) (by simp [rubi1212r5Nondeg]); simpa [Cond.Holds, Defined, eval] using h
  have hg := hc (.gt (.var "p") (.int 0)) (by simp [rubi1212r5Nondeg])
  rcases hk_p : I.toInt? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1212r5Nondeg, Defined, eval, hk_p] at h
  have h_p : env "p" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have hk : 0 < k := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg
    rw [h_p] at hg
    have h' : I.lt ((((0 : ℤ)) : ℚ) : 𝕜) ((k : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg
    exact_mod_cast (hlt _ _).1 h'
  have e1 : I.toInt? (env "p" + 1) = some (k + 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have hk0 : ¬ k < 0 := by omega
  have hk1 : ¬ k + 1 < 0 := by omega
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1212r5Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    exact Eventually.of_forall fun w => by
      simp [Defined, eval, hk_p, e1, toInt?_neg_one, hd, he, hk0, hk1]
  · exact Eventually.of_forall fun w => by simp [rubi1212r5Nondeg, Defined]
  · simp only [rubi1212r5Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (rubi1212r5Nondeg.integrals.map (·.1)) Φ "x" w) rubi1212r5Nondeg.result) = Φ "I1" := by
      funext w; simp [rubi1212r5Nondeg, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    have hQ : (env "a" + env "b" * t + env "c" * t ^ 2) = (env "d" + env "e" * t) * (env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * t) := by
      field_simp
      first | linear_combination (-t) * heq | linear_combination t * heq | linear_combination (-t * env "d" * env "e") * heq | linear_combination (t * env "d" * env "e") * heq
    have key : (env "d" + env "e" * t) ^ (k + 1) * (env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * t) ^ k = (env "d" + env "e" * t) * (env "a" + env "b" * t + env "c" * t ^ 2) ^ k := by
      rw [hQ, mul_zpow, zpow_succ_of _ _ (Or.inr (by omega))]
      ring
    simpa [rubi1212r5Nondeg, eval, hk_p, e1, toInt?_neg_one, toInt?_two] using key

theorem rubi1233r50Nondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi1233r50Nondeg.conditions rubi1233r50Nondeg.body rubi1233r50Nondeg.result rubi1233r50Nondeg.integrals := by
  intro env hc t hF
  have heq : env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1233r50Nondeg])
    simp [Cond.Holds, Defined, eval, toInt?_two] at h
    linear_combination h
  have hn2 : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi1233r50Nondeg]); simpa [Cond.Holds, Defined, eval] using h
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi1233r50Nondeg]); simpa [Cond.Holds, Defined, eval] using h
  have he : env "e" ≠ 0 := by
    have h := hc (.ne (.var "e") (.int 0)) (by simp [rubi1233r50Nondeg]); simpa [Cond.Holds, Defined, eval] using h
  rcases hk_q : I.toInt? (env "q") with _ | kq
  · exfalso; have h := hF.self_of_nhds; simp [rubi1233r50Nondeg, Defined, eval, hk_q] at h
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso; have h := hF.self_of_nhds; simp [rubi1233r50Nondeg, Defined, eval, hk_q, hk_n] at h
  rcases hk_r : I.toInt? (env "r") with _ | kr
  · exfalso; have h := hF.self_of_nhds; simp [rubi1233r50Nondeg, Defined, eval, hk_q, hk_n, hk_r] at h
  rcases hk_p : I.toInt? (env "p") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi1233r50Nondeg, Defined, eval, hk_q, hk_n, hk_r, hk_p] at h
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have h_p : env "p" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have h_q : env "q" = (kq : 𝕜) := (I.toInt?_eq _ _).1 hk_q
  have e2 : I.toInt? (env "n2") = some (2 * j) := (I.toInt?_eq _ _).2 (by rw [hn2, h_n]; push_cast; ring)
  have epq : I.toInt? (env "p" + env "q") = some (k + kq) := (I.toInt?_eq _ _).2 (by rw [h_p, h_q]; push_cast; ring)
  have hQ : ∀ w : 𝕜, (env "a" + env "b" * w ^ j + env "c" * (w ^ j) ^ 2) = (env "d" + env "e" * w ^ j) * (env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * w ^ j) := by
    intro w
    field_simp
    first | linear_combination (-(w ^ j)) * heq | linear_combination (w ^ j) * heq | linear_combination (-(w ^ j) * env "d" * env "e") * heq | linear_combination (w ^ j * env "d" * env "e") * heq
  have hsq : ∀ w : 𝕜, w ^ (2 * j) = (w ^ j) ^ 2 := by
    intro w; rw [mul_comm, zpow_mul]; norm_cast
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi1233r50Nondeg.body →
      (j < 0 → w ≠ 0) ∧ (kq < 0 → (env "d" + env "e" * w ^ j) ≠ 0) ∧ (kr < 0 → (env "f" + env "g" * w ^ j) ≠ 0) ∧ (k < 0 → (env "a" + env "b" * w ^ j + env "c" * (w ^ j) ^ 2) ≠ 0) := by
    intro w h
    simp [rubi1233r50Nondeg, Defined, eval, hk_q, hk_n, hk_r, hk_p, e2, hsq] at h
    exact ⟨h.1.1.1, h.1.1.2, h.1.2.2, h.2.2⟩
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1233r50Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2, h3, h4⟩ := hBody w hw
    have hD : k + kq < 0 → (env "d" + env "e" * w ^ j) ≠ 0 := by
      intro h
      by_cases hq : kq < 0
      · exact h2 hq
      · have := h4 (by omega); rw [hQ w] at this; exact left_ne_zero_of_mul this
    have hE : k < 0 → (env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * w ^ j) ≠ 0 := by
      intro h; have := h4 h; rw [hQ w] at this; exact right_ne_zero_of_mul this
    simp [Defined, eval, hk_n, hk_r, hk_p, epq, toInt?_neg_one, hd, he]
    exact ⟨⟨⟨h1, hD⟩, h1, h3⟩, h1, hE⟩
  · exact Eventually.of_forall fun w => by simp [rubi1233r50Nondeg, Defined]
  · simp only [rubi1233r50Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (rubi1233r50Nondeg.integrals.map (·.1)) Φ "x" w) rubi1233r50Nondeg.result) = Φ "I1" := by
      funext w; simp [rubi1233r50Nondeg, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    obtain ⟨h1, h2, h3, h4⟩ := hBody t hF.self_of_nhds
    have hadd : (env "d" + env "e" * t ^ j) ^ (k + kq) = (env "d" + env "e" * t ^ j) ^ k * (env "d" + env "e" * t ^ j) ^ kq := by
      by_cases hD0 : (env "d" + env "e" * t ^ j) = 0
      · have hkq : 0 ≤ kq := by by_contra h; exact h2 (by omega) hD0
        have hk' : 0 ≤ k := by
          by_contra h
          have := h4 (by omega); rw [hQ t, hD0, zero_mul] at this; exact this rfl
        rcases em (k + kq = 0) with h0 | h0
        · have : k = 0 := by omega
          have : kq = 0 := by omega
          subst_vars; simp
        · exact zpow_add' (Or.inr (Or.inl h0))
      · exact zpow_add₀ hD0 _ _
    have key : (env "d" + env "e" * t ^ j) ^ (k + kq) * (env "f" + env "g" * t ^ j) ^ kr * (env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * t ^ j) ^ k = (env "d" + env "e" * t ^ j) ^ kq * (env "f" + env "g" * t ^ j) ^ kr * (env "a" + env "b" * t ^ j + env "c" * (t ^ j) ^ 2) ^ k := by
      rw [hQ t, mul_zpow, hadd]
      ring
    simpa [rubi1233r50Nondeg, eval, hk_q, hk_n, hk_r, hk_p, e2, epq, hsq, toInt?_neg_one] using key

theorem rubi1212r5Nondeg_real : rubi1212r5Nondeg.Holds .real :=
  rubi1212r5Nondeg_holds Interp.real Interp.real_lt_rat
theorem rubi1212r5Nondeg_complex : rubi1212r5Nondeg.Holds .complex :=
  rubi1212r5Nondeg_holds Interp.complex Interp.complex_lt_rat
theorem rubi1233r50Nondeg_real : rubi1233r50Nondeg.Holds .real := rubi1233r50Nondeg_holds Interp.real
theorem rubi1233r50Nondeg_complex : rubi1233r50Nondeg.Holds .complex := rubi1233r50Nondeg_holds Interp.complex

end Proofs

end OSR.IntegrationRec99
