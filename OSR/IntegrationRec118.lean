import OSR.IntegrationRec91

/-!
# Integration (RUBI): 1.2.3.3 #41, #42, #47 and 1.2.3.4 #92, #93, #100

These rules rewrite `(a + b x^(-n) + c x^(-2n))^p` (and its variants) as
`x^(-2np) (c + b xⁿ + a x^(2n))^p` inside a residual integral.  For an integer
`p` the identity holds wherever the integrand is defined, since `x ≠ 0` there
unless `n = 0`.  Proved over ℝ and ℂ, as RUBI states them.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec118

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 1.2.3.3 #41 -/
def rubi1233r41 : CRule where
  id := "integration.rubi_1_2_3_3_r41"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:41"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "q")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "mn")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "mn2")))) (.var "p")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .mul (.app2 .mul (.int (-2)) (.var "n")) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "q"))) (.pow (.app2 .add (.app2 .add (.var "c") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "a") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "n", "q", "mn", "mn2", "p"]
  conditions := [.eq (.var "mn") (.app2 .mul (.int (-1)) (.var "n")),
    .eq (.var "mn2") (.app2 .mul (.int 2) (.var "mn")),
    .int (.var "p")]
  priority := 9404
  description := "RUBI 1.2.3.3 #41"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:41" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#41"

/-- RUBI 1.2.3.3 #42 -/
def rubi1233r42 : CRule where
  id := "integration.rubi_1_2_3_3_r42"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:42"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "q")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.var "mn2")))) (.var "p")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .mul (.app2 .mul (.int (-2)) (.var "n")) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "q"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "a") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.var "p"))))]
  independent := ["a", "c", "d", "e", "n", "q", "mn2", "p"]
  conditions := [.eq (.var "mn2") (.app2 .mul (.int (-2)) (.var "n")),
    .int (.var "p")]
  priority := 9405
  description := "RUBI 1.2.3.3 #42"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:42" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#42"

/-- RUBI 1.2.3.3 #47 -/
def rubi1233r47 : CRule where
  id := "integration.rubi_1_2_3_3_r47"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:47"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "q")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "mn")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "p")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .mul (.app2 .mul (.int (-1)) (.var "n")) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "q"))) (.pow (.app2 .add (.app2 .add (.var "b") (.app2 .mul (.var "a") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "n", "q", "mn", "p"]
  conditions := [.eq (.var "mn") (.app2 .mul (.int (-1)) (.var "n")),
    .int (.var "p")]
  priority := 9406
  description := "RUBI 1.2.3.3 #47"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:47" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#47"

/-- RUBI 1.2.3.4 #92 -/
def rubi1234r92 : CRule where
  id := "integration.rubi_1_2_3_4_r92"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:92"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "q"))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "mn")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "mn2")))) (.var "p")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n")) (.var "p")))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "q"))) (.pow (.app2 .add (.app2 .add (.var "c") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "a") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "m", "n", "q", "mn", "mn2", "p"]
  conditions := [.eq (.var "mn") (.app2 .mul (.int (-1)) (.var "n")),
    .eq (.var "mn2") (.app2 .mul (.int 2) (.var "mn")),
    .int (.var "p")]
  priority := 9407
  description := "RUBI 1.2.3.4 #92"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:92" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#92"

/-- RUBI 1.2.3.4 #93 -/
def rubi1234r93 : CRule where
  id := "integration.rubi_1_2_3_4_r93"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:93"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.var "mn2")))) (.var "p")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n")) (.var "p")))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "q"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "a") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.var "p"))))]
  independent := ["a", "c", "d", "e", "m", "n", "q", "mn2", "p"]
  conditions := [.eq (.var "mn2") (.app2 .mul (.int (-2)) (.var "n")),
    .int (.var "p")]
  priority := 9408
  description := "RUBI 1.2.3.4 #93"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:93" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#93"

/-- RUBI 1.2.3.4 #100 -/
def rubi1234r100 : CRule where
  id := "integration.rubi_1_2_3_4_r100"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:100"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "q"))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "mn")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "p")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.var "n")) (.var "p")))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "q"))) (.pow (.app2 .add (.app2 .add (.var "b") (.app2 .mul (.var "a") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "m", "n", "q", "mn", "p"]
  conditions := [.eq (.var "mn") (.app2 .mul (.int (-1)) (.var "n")),
    .int (.var "p")]
  priority := 9409
  description := "RUBI 1.2.3.4 #100"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:100" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#100"

/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem toInt?_two (I : Interp 𝕜) : I.toInt? (2 : 𝕜) = some 2 :=
  (I.toInt?_eq _ _).2 (by simp)

theorem rubi1233r41_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi1233r41.conditions rubi1233r41.body rubi1233r41.result rubi1233r41.integrals := by
  intro env hc t hF
  have hmn : env "mn" = -1 * env "n" := by
    have h := hc (.eq (.var "mn") (.app2 .mul (.int (-1)) (.var "n"))) (by simp [rubi1233r41]); simpa [Cond.Holds, Defined, eval] using h
  have hmn2 : env "mn2" = 2 * env "mn" := by
    have h := hc (.eq (.var "mn2") (.app2 .mul (.int 2) (.var "mn"))) (by simp [rubi1233r41]); simpa [Cond.Holds, Defined, eval] using h
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso; have h := hF.self_of_nhds; simp [rubi1233r41, Defined, eval, hk_n] at h
  rcases hk_p : I.toInt? (env "p") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi1233r41, Defined, eval, hk_n, hk_p] at h
  rcases hk_q : I.toInt? (env "q") with _ | l
  · exfalso; have h := hF.self_of_nhds; simp [rubi1233r41, Defined, eval, hk_n, hk_p, hk_q] at h
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have h_p : env "p" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have emn : I.toInt? (env "mn") = some (-j) := (I.toInt?_eq _ _).2 (by rw [hmn, h_n]; push_cast; ring)
  have emn2 : I.toInt? (env "mn2") = some (-(2 * j)) := (I.toInt?_eq _ _).2 (by rw [hmn2, hmn, h_n]; push_cast; ring)
  have e2n : I.toInt? (2 * env "n") = some (2 * j) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have esn0 : I.toInt? (-2 * env "n" * env "p") = some (-(2 * j * k)) := (I.toInt?_eq _ _).2 (by rw [h_n, h_p]; push_cast; ring)
  have esn1 : I.toInt? (-(2 * env "n" * env "p")) = some (-(2 * j * k)) := (I.toInt?_eq _ _).2 (by rw [h_n, h_p]; push_cast; ring)
  have esn2 : I.toInt? (-(env "n" * env "p" * 2)) = some (-(2 * j * k)) := (I.toInt?_eq _ _).2 (by rw [h_n, h_p]; push_cast; ring)
  have esn3 : I.toInt? (-(2 * (env "n" * env "p"))) = some (-(2 * j * k)) := (I.toInt?_eq _ _).2 (by rw [h_n, h_p]; push_cast; ring)
  have esn4 : I.toInt? (-(env "n" * (env "p" * 2))) = some (-(2 * j * k)) := (I.toInt?_eq _ _).2 (by rw [h_n, h_p]; push_cast; ring)
  have e0 : I.toInt? (0 : 𝕜) = some 0 := (I.toInt?_eq _ _).2 (by simp)
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi1233r41.body →
      (j ≠ 0 → w ≠ 0) ∧ (l < 0 → env "d" + env "e" * w ^ j ≠ 0) ∧ (k < 0 → env "a" + env "b" * (w ^ j)⁻¹ + env "c" * (w ^ (2 * j))⁻¹ ≠ 0) := by
    intro w h
    simp [rubi1233r41, Defined, eval, hk_n, hk_p, hk_q, emn, emn2, e2n, esn0, esn1, esn2, esn3, esn4, e0, toInt?_two] at h
    refine ⟨fun hj => ?_, ?_, ?_⟩
    · rcases lt_or_gt_of_ne hj with hj' | hj' <;> simp_all
    all_goals simp_all
  have hPQ : ∀ w : 𝕜, (j ≠ 0 → w ≠ 0) → env "a" + env "b" * (w ^ j)⁻¹ + env "c" * (w ^ (2 * j))⁻¹ = (w ^ (2 * j))⁻¹ * (env "c" + env "b" * w ^ j + env "a" * w ^ (2 * j)) := by
    intro w hw
    rcases eq_or_ne j 0 with hj | hj
    · subst hj; simp; ring
    · have hw0 := hw hj
      have hy : w ^ j ≠ 0 := zpow_ne_zero _ hw0
      rw [show w ^ (2 * j) = (w ^ j) ^ 2 by rw [mul_comm, zpow_mul]; norm_cast]
      generalize w ^ j = y at hy ⊢
      field_simp
      ring
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1233r41, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2, h3⟩ := hBody w hw
    have hQ : k < 0 → env "c" + env "b" * w ^ j + env "a" * w ^ (2 * j) ≠ 0 := by
      intro hk h0; apply h3 hk; rw [hPQ w h1, h0, mul_zero]
    rcases eq_or_ne j 0 with hj | hj
    · subst hj; simp [Defined, eval, hk_n, hk_p, hk_q, emn, emn2, e2n, esn0, esn1, esn2, esn3, esn4, e0, toInt?_two, h_n, h_p, Interp.toInt?_cast] at hQ h2 ⊢
      first | done | simp (config := {contextual := true}) [hQ, h2] | (trace_state; sorry)
    · have hw0 := h1 hj
      simp (config := {contextual := true}) [Defined, eval, hk_n, hk_p, hk_q, emn, emn2, e2n, esn0, esn1, esn2, esn3, esn4, e0, toInt?_two, hw0, hQ, h2]
      first | done | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi1233r41, Defined, eval, recEnv]
  · simp only [rubi1233r41, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨h1, -, -⟩ := hBody t hF.self_of_nhds
    have hfun : (fun w => eval I (recEnv env (rubi1233r41.integrals.map (·.1)) Φ "x" w) rubi1233r41.result) = Φ "I1" := by
      funext w; simp [rubi1233r41, eval, recEnv]
    have heq : eval I (Function.update env "x" t) rubi1233r41.body =
        eval I (Function.update env "x" t) (rubi1233r41.integrals.head!).2 := by
      simp [rubi1233r41, eval, hk_n, hk_p, hk_q, emn, emn2, e2n, esn0, esn1, esn2, esn3, esn4, e0, toInt?_two]
      rw [hPQ t h1, mul_zpow, inv_zpow, ← zpow_mul]
      rcases eq_or_ne j 0 with hj | hj
      · subst hj; simp [h_n, h_p, e0]
      · have ht0 := h1 hj
        first | ring1 | (rw [zpow_add₀ ht0, zpow_neg]; ring1) | (rw [zpow_sub₀ ht0]; ring1) | (simp [zpow_sub₀ ht0]; ring1) | (trace_state; sorry)
    rw [hfun, heq]
    simpa [rubi1233r41] using hΦ

theorem rubi1233r42_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi1233r42.conditions rubi1233r42.body rubi1233r42.result rubi1233r42.integrals := by
  intro env hc t hF
  have hmn2 : env "mn2" = -2 * env "n" := by
    have h := hc (.eq (.var "mn2") (.app2 .mul (.int (-2)) (.var "n"))) (by simp [rubi1233r42]); simpa [Cond.Holds, Defined, eval] using h
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso; have h := hF.self_of_nhds; simp [rubi1233r42, Defined, eval, hk_n] at h
  rcases hk_p : I.toInt? (env "p") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi1233r42, Defined, eval, hk_n, hk_p] at h
  rcases hk_q : I.toInt? (env "q") with _ | l
  · exfalso; have h := hF.self_of_nhds; simp [rubi1233r42, Defined, eval, hk_n, hk_p, hk_q] at h
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have h_p : env "p" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have emn2 : I.toInt? (env "mn2") = some (-(2 * j)) := (I.toInt?_eq _ _).2 (by rw [hmn2, h_n]; push_cast; ring)
  have e2n : I.toInt? (2 * env "n") = some (2 * j) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have esn0 : I.toInt? (-2 * env "n" * env "p") = some (-(2 * j * k)) := (I.toInt?_eq _ _).2 (by rw [h_n, h_p]; push_cast; ring)
  have esn1 : I.toInt? (-(2 * env "n" * env "p")) = some (-(2 * j * k)) := (I.toInt?_eq _ _).2 (by rw [h_n, h_p]; push_cast; ring)
  have esn2 : I.toInt? (-(env "n" * env "p" * 2)) = some (-(2 * j * k)) := (I.toInt?_eq _ _).2 (by rw [h_n, h_p]; push_cast; ring)
  have esn3 : I.toInt? (-(2 * (env "n" * env "p"))) = some (-(2 * j * k)) := (I.toInt?_eq _ _).2 (by rw [h_n, h_p]; push_cast; ring)
  have esn4 : I.toInt? (-(env "n" * (env "p" * 2))) = some (-(2 * j * k)) := (I.toInt?_eq _ _).2 (by rw [h_n, h_p]; push_cast; ring)
  have e0 : I.toInt? (0 : 𝕜) = some 0 := (I.toInt?_eq _ _).2 (by simp)
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi1233r42.body →
      (j ≠ 0 → w ≠ 0) ∧ (l < 0 → env "d" + env "e" * w ^ j ≠ 0) ∧ (k < 0 → env "a" + env "c" * (w ^ (2 * j))⁻¹ ≠ 0) := by
    intro w h
    simp [rubi1233r42, Defined, eval, hk_n, hk_p, hk_q, emn2, e2n, esn0, esn1, esn2, esn3, esn4, e0, toInt?_two] at h
    refine ⟨fun hj => ?_, ?_, ?_⟩
    · rcases lt_or_gt_of_ne hj with hj' | hj' <;> simp_all
    all_goals simp_all
  have hPQ : ∀ w : 𝕜, (j ≠ 0 → w ≠ 0) → env "a" + env "c" * (w ^ (2 * j))⁻¹ = (w ^ (2 * j))⁻¹ * (env "c" + env "a" * w ^ (2 * j)) := by
    intro w hw
    rcases eq_or_ne j 0 with hj | hj
    · subst hj; simp; ring
    · have hw0 := hw hj
      have hy : w ^ j ≠ 0 := zpow_ne_zero _ hw0
      rw [show w ^ (2 * j) = (w ^ j) ^ 2 by rw [mul_comm, zpow_mul]; norm_cast]
      generalize w ^ j = y at hy ⊢
      field_simp
      ring
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1233r42, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2, h3⟩ := hBody w hw
    have hQ : k < 0 → env "c" + env "a" * w ^ (2 * j) ≠ 0 := by
      intro hk h0; apply h3 hk; rw [hPQ w h1, h0, mul_zero]
    rcases eq_or_ne j 0 with hj | hj
    · subst hj; simp [Defined, eval, hk_n, hk_p, hk_q, emn2, e2n, esn0, esn1, esn2, esn3, esn4, e0, toInt?_two, h_n, h_p, Interp.toInt?_cast] at hQ h2 ⊢
      first | done | simp (config := {contextual := true}) [hQ, h2] | (trace_state; sorry)
    · have hw0 := h1 hj
      simp (config := {contextual := true}) [Defined, eval, hk_n, hk_p, hk_q, emn2, e2n, esn0, esn1, esn2, esn3, esn4, e0, toInt?_two, hw0, hQ, h2]
      first | done | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi1233r42, Defined, eval, recEnv]
  · simp only [rubi1233r42, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨h1, -, -⟩ := hBody t hF.self_of_nhds
    have hfun : (fun w => eval I (recEnv env (rubi1233r42.integrals.map (·.1)) Φ "x" w) rubi1233r42.result) = Φ "I1" := by
      funext w; simp [rubi1233r42, eval, recEnv]
    have heq : eval I (Function.update env "x" t) rubi1233r42.body =
        eval I (Function.update env "x" t) (rubi1233r42.integrals.head!).2 := by
      simp [rubi1233r42, eval, hk_n, hk_p, hk_q, emn2, e2n, esn0, esn1, esn2, esn3, esn4, e0, toInt?_two]
      rw [hPQ t h1, mul_zpow, inv_zpow, ← zpow_mul]
      rcases eq_or_ne j 0 with hj | hj
      · subst hj; simp [h_n, h_p, e0]
      · have ht0 := h1 hj
        first | ring1 | (rw [zpow_add₀ ht0, zpow_neg]; ring1) | (rw [zpow_sub₀ ht0]; ring1) | (simp [zpow_sub₀ ht0]; ring1) | (trace_state; sorry)
    rw [hfun, heq]
    simpa [rubi1233r42] using hΦ

theorem rubi1233r47_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi1233r47.conditions rubi1233r47.body rubi1233r47.result rubi1233r47.integrals := by
  intro env hc t hF
  have hmn : env "mn" = -1 * env "n" := by
    have h := hc (.eq (.var "mn") (.app2 .mul (.int (-1)) (.var "n"))) (by simp [rubi1233r47]); simpa [Cond.Holds, Defined, eval] using h
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso; have h := hF.self_of_nhds; simp [rubi1233r47, Defined, eval, hk_n] at h
  rcases hk_p : I.toInt? (env "p") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi1233r47, Defined, eval, hk_n, hk_p] at h
  rcases hk_q : I.toInt? (env "q") with _ | l
  · exfalso; have h := hF.self_of_nhds; simp [rubi1233r47, Defined, eval, hk_n, hk_p, hk_q] at h
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have h_p : env "p" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have emn : I.toInt? (env "mn") = some (-j) := (I.toInt?_eq _ _).2 (by rw [hmn, h_n]; push_cast; ring)
  have e2n : I.toInt? (2 * env "n") = some (2 * j) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have esn0 : I.toInt? (-1 * env "n" * env "p") = some (-(1 * j * k)) := (I.toInt?_eq _ _).2 (by rw [h_n, h_p]; push_cast; ring)
  have esn1 : I.toInt? (-(env "n" * env "p")) = some (-(1 * j * k)) := (I.toInt?_eq _ _).2 (by rw [h_n, h_p]; push_cast; ring)
  have e0 : I.toInt? (0 : 𝕜) = some 0 := (I.toInt?_eq _ _).2 (by simp)
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi1233r47.body →
      (j ≠ 0 → w ≠ 0) ∧ (l < 0 → env "d" + env "e" * w ^ j ≠ 0) ∧ (k < 0 → env "a" + env "b" * (w ^ j)⁻¹ + env "c" * w ^ j ≠ 0) := by
    intro w h
    simp [rubi1233r47, Defined, eval, hk_n, hk_p, hk_q, emn, e2n, esn0, esn1, e0, toInt?_two] at h
    refine ⟨fun hj => ?_, ?_, ?_⟩
    · rcases lt_or_gt_of_ne hj with hj' | hj' <;> simp_all
    all_goals simp_all
  have hPQ : ∀ w : 𝕜, (j ≠ 0 → w ≠ 0) → env "a" + env "b" * (w ^ j)⁻¹ + env "c" * w ^ j = (w ^ j)⁻¹ * (env "b" + env "a" * w ^ j + env "c" * w ^ (2 * j)) := by
    intro w hw
    rcases eq_or_ne j 0 with hj | hj
    · subst hj; simp; ring
    · have hw0 := hw hj
      have hy : w ^ j ≠ 0 := zpow_ne_zero _ hw0
      rw [show w ^ (2 * j) = (w ^ j) ^ 2 by rw [mul_comm, zpow_mul]; norm_cast]
      generalize w ^ j = y at hy ⊢
      field_simp
      ring
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1233r47, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2, h3⟩ := hBody w hw
    have hQ : k < 0 → env "b" + env "a" * w ^ j + env "c" * w ^ (2 * j) ≠ 0 := by
      intro hk h0; apply h3 hk; rw [hPQ w h1, h0, mul_zero]
    rcases eq_or_ne j 0 with hj | hj
    · subst hj; simp [Defined, eval, hk_n, hk_p, hk_q, emn, e2n, esn0, esn1, e0, toInt?_two, h_n, h_p, Interp.toInt?_cast] at hQ h2 ⊢
      first | done | simp (config := {contextual := true}) [hQ, h2] | (trace_state; sorry)
    · have hw0 := h1 hj
      simp (config := {contextual := true}) [Defined, eval, hk_n, hk_p, hk_q, emn, e2n, esn0, esn1, e0, toInt?_two, hw0, hQ, h2]
      first | done | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi1233r47, Defined, eval, recEnv]
  · simp only [rubi1233r47, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨h1, -, -⟩ := hBody t hF.self_of_nhds
    have hfun : (fun w => eval I (recEnv env (rubi1233r47.integrals.map (·.1)) Φ "x" w) rubi1233r47.result) = Φ "I1" := by
      funext w; simp [rubi1233r47, eval, recEnv]
    have heq : eval I (Function.update env "x" t) rubi1233r47.body =
        eval I (Function.update env "x" t) (rubi1233r47.integrals.head!).2 := by
      simp [rubi1233r47, eval, hk_n, hk_p, hk_q, emn, e2n, esn0, esn1, e0, toInt?_two]
      rw [hPQ t h1, mul_zpow, inv_zpow, ← zpow_mul]
      rcases eq_or_ne j 0 with hj | hj
      · subst hj; simp [h_n, h_p, e0]
      · have ht0 := h1 hj
        first | ring1 | (rw [zpow_add₀ ht0, zpow_neg]; ring1) | (rw [zpow_sub₀ ht0]; ring1) | (simp [zpow_sub₀ ht0]; ring1) | (trace_state; sorry)
    rw [hfun, heq]
    simpa [rubi1233r47] using hΦ

theorem rubi1234r92_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi1234r92.conditions rubi1234r92.body rubi1234r92.result rubi1234r92.integrals := by
  intro env hc t hF
  have hmn : env "mn" = -1 * env "n" := by
    have h := hc (.eq (.var "mn") (.app2 .mul (.int (-1)) (.var "n"))) (by simp [rubi1234r92]); simpa [Cond.Holds, Defined, eval] using h
  have hmn2 : env "mn2" = 2 * env "mn" := by
    have h := hc (.eq (.var "mn2") (.app2 .mul (.int 2) (.var "mn"))) (by simp [rubi1234r92]); simpa [Cond.Holds, Defined, eval] using h
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso; have h := hF.self_of_nhds; simp [rubi1234r92, Defined, eval, hk_n] at h
  rcases hk_p : I.toInt? (env "p") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi1234r92, Defined, eval, hk_n, hk_p] at h
  rcases hk_q : I.toInt? (env "q") with _ | l
  · exfalso; have h := hF.self_of_nhds; simp [rubi1234r92, Defined, eval, hk_n, hk_p, hk_q] at h
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have h_p : env "p" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have emn : I.toInt? (env "mn") = some (-j) := (I.toInt?_eq _ _).2 (by rw [hmn, h_n]; push_cast; ring)
  have emn2 : I.toInt? (env "mn2") = some (-(2 * j)) := (I.toInt?_eq _ _).2 (by rw [hmn2, hmn, h_n]; push_cast; ring)
  have e2n : I.toInt? (2 * env "n") = some (2 * j) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have esn0 : I.toInt? (-2 * env "n" * env "p") = some (-(2 * j * k)) := (I.toInt?_eq _ _).2 (by rw [h_n, h_p]; push_cast; ring)
  have esn1 : I.toInt? (-(2 * env "n" * env "p")) = some (-(2 * j * k)) := (I.toInt?_eq _ _).2 (by rw [h_n, h_p]; push_cast; ring)
  have esn2 : I.toInt? (-(env "n" * env "p" * 2)) = some (-(2 * j * k)) := (I.toInt?_eq _ _).2 (by rw [h_n, h_p]; push_cast; ring)
  have esn3 : I.toInt? (-(2 * (env "n" * env "p"))) = some (-(2 * j * k)) := (I.toInt?_eq _ _).2 (by rw [h_n, h_p]; push_cast; ring)
  have esn4 : I.toInt? (-(env "n" * (env "p" * 2))) = some (-(2 * j * k)) := (I.toInt?_eq _ _).2 (by rw [h_n, h_p]; push_cast; ring)
  have e0 : I.toInt? (0 : 𝕜) = some 0 := (I.toInt?_eq _ _).2 (by simp)
  rcases hk_m : I.toInt? (env "m") with _ | mm
  · exfalso; have h := hF.self_of_nhds; simp [rubi1234r92, Defined, eval, hk_n, hk_p, hk_q, hk_m] at h
  have h_m : env "m" = (mm : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have emk0 : I.toInt? (env "m" + -2 * env "n" * env "p") = some (mm - 2 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have emk1 : I.toInt? (env "m" + -(2 * env "n" * env "p")) = some (mm - 2 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have emk2 : I.toInt? (env "m" + -(env "n" * env "p" * 2)) = some (mm - 2 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have emk3 : I.toInt? (env "m" + -(2 * (env "n" * env "p"))) = some (mm - 2 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have emk4 : I.toInt? (env "m" + -(env "n" * (env "p" * 2))) = some (mm - 2 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have emk5 : I.toInt? (env "m" - 2 * env "n" * env "p") = some (mm - 2 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have emk6 : I.toInt? (env "m" - env "n" * env "p" * 2) = some (mm - 2 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have emk7 : I.toInt? (env "m" - 2 * (env "n" * env "p")) = some (mm - 2 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have emk8 : I.toInt? (env "m" - env "n" * (env "p" * 2)) = some (mm - 2 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have emk0 : I.toInt? (env "m" + -2 * env "n" * env "p") = some (mm - 2 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have emk1 : I.toInt? (env "m" + -(2 * env "n" * env "p")) = some (mm - 2 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have emk2 : I.toInt? (env "m" + -(env "n" * env "p" * 2)) = some (mm - 2 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have emk3 : I.toInt? (env "m" + -(2 * (env "n" * env "p"))) = some (mm - 2 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have emk4 : I.toInt? (env "m" + -(env "n" * (env "p" * 2))) = some (mm - 2 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have emk5 : I.toInt? (env "m" - 2 * env "n" * env "p") = some (mm - 2 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have emk6 : I.toInt? (env "m" - env "n" * env "p" * 2) = some (mm - 2 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have emk7 : I.toInt? (env "m" - 2 * (env "n" * env "p")) = some (mm - 2 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have emk8 : I.toInt? (env "m" - env "n" * (env "p" * 2)) = some (mm - 2 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi1234r92.body →
      (j ≠ 0 → w ≠ 0) ∧ (l < 0 → env "d" + env "e" * w ^ j ≠ 0) ∧ (k < 0 → env "a" + env "b" * (w ^ j)⁻¹ + env "c" * (w ^ (2 * j))⁻¹ ≠ 0) ∧ (mm < 0 → w ≠ 0) := by
    intro w h
    simp [rubi1234r92, Defined, eval, hk_n, hk_p, hk_q, hk_m, emn, emn2, e2n, esn0, esn1, esn2, esn3, esn4, emk0, emk1, emk2, emk3, emk4, emk5, emk6, emk7, emk8, e0, toInt?_two] at h
    refine ⟨fun hj => ?_, ?_, ?_, ?_⟩
    · rcases lt_or_gt_of_ne hj with hj' | hj' <;> simp_all
    all_goals simp_all
  have hPQ : ∀ w : 𝕜, (j ≠ 0 → w ≠ 0) → env "a" + env "b" * (w ^ j)⁻¹ + env "c" * (w ^ (2 * j))⁻¹ = (w ^ (2 * j))⁻¹ * (env "c" + env "b" * w ^ j + env "a" * w ^ (2 * j)) := by
    intro w hw
    rcases eq_or_ne j 0 with hj | hj
    · subst hj; simp; ring
    · have hw0 := hw hj
      have hy : w ^ j ≠ 0 := zpow_ne_zero _ hw0
      rw [show w ^ (2 * j) = (w ^ j) ^ 2 by rw [mul_comm, zpow_mul]; norm_cast]
      generalize w ^ j = y at hy ⊢
      field_simp
      ring
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1234r92, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2, h3, h4⟩ := hBody w hw
    have hQ : k < 0 → env "c" + env "b" * w ^ j + env "a" * w ^ (2 * j) ≠ 0 := by
      intro hk h0; apply h3 hk; rw [hPQ w h1, h0, mul_zero]
    rcases eq_or_ne j 0 with hj | hj
    · subst hj; simp [Defined, eval, hk_n, hk_p, hk_q, hk_m, emn, emn2, e2n, esn0, esn1, esn2, esn3, esn4, emk0, emk1, emk2, emk3, emk4, emk5, emk6, emk7, emk8, e0, toInt?_two, h_n, h_p, Interp.toInt?_cast] at hQ h2 ⊢
      first | done | simp (config := {contextual := true}) [hQ, h2, h4] | (trace_state; sorry)
    · have hw0 := h1 hj
      simp (config := {contextual := true}) [Defined, eval, hk_n, hk_p, hk_q, hk_m, emn, emn2, e2n, esn0, esn1, esn2, esn3, esn4, emk0, emk1, emk2, emk3, emk4, emk5, emk6, emk7, emk8, e0, toInt?_two, hw0, hQ, h2]
      first | done | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi1234r92, Defined, eval, recEnv]
  · simp only [rubi1234r92, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨h1, -, -, -⟩ := hBody t hF.self_of_nhds
    have hfun : (fun w => eval I (recEnv env (rubi1234r92.integrals.map (·.1)) Φ "x" w) rubi1234r92.result) = Φ "I1" := by
      funext w; simp [rubi1234r92, eval, recEnv]
    have heq : eval I (Function.update env "x" t) rubi1234r92.body =
        eval I (Function.update env "x" t) (rubi1234r92.integrals.head!).2 := by
      simp [rubi1234r92, eval, hk_n, hk_p, hk_q, hk_m, emn, emn2, e2n, esn0, esn1, esn2, esn3, esn4, emk0, emk1, emk2, emk3, emk4, emk5, emk6, emk7, emk8, e0, toInt?_two]
      rw [hPQ t h1, mul_zpow, inv_zpow, ← zpow_mul]
      rcases eq_or_ne j 0 with hj | hj
      · subst hj; simp [h_n, h_p, e0]
      · have ht0 := h1 hj
        first | ring1 | (rw [zpow_add₀ ht0, zpow_neg]; ring1) | (rw [zpow_sub₀ ht0]; ring1) | (simp [zpow_sub₀ ht0]; ring1) | (trace_state; sorry)
    rw [hfun, heq]
    simpa [rubi1234r92] using hΦ

theorem rubi1234r93_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi1234r93.conditions rubi1234r93.body rubi1234r93.result rubi1234r93.integrals := by
  intro env hc t hF
  have hmn2 : env "mn2" = -2 * env "n" := by
    have h := hc (.eq (.var "mn2") (.app2 .mul (.int (-2)) (.var "n"))) (by simp [rubi1234r93]); simpa [Cond.Holds, Defined, eval] using h
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso; have h := hF.self_of_nhds; simp [rubi1234r93, Defined, eval, hk_n] at h
  rcases hk_p : I.toInt? (env "p") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi1234r93, Defined, eval, hk_n, hk_p] at h
  rcases hk_q : I.toInt? (env "q") with _ | l
  · exfalso; have h := hF.self_of_nhds; simp [rubi1234r93, Defined, eval, hk_n, hk_p, hk_q] at h
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have h_p : env "p" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have emn2 : I.toInt? (env "mn2") = some (-(2 * j)) := (I.toInt?_eq _ _).2 (by rw [hmn2, h_n]; push_cast; ring)
  have e2n : I.toInt? (2 * env "n") = some (2 * j) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have esn0 : I.toInt? (-2 * env "n" * env "p") = some (-(2 * j * k)) := (I.toInt?_eq _ _).2 (by rw [h_n, h_p]; push_cast; ring)
  have esn1 : I.toInt? (-(2 * env "n" * env "p")) = some (-(2 * j * k)) := (I.toInt?_eq _ _).2 (by rw [h_n, h_p]; push_cast; ring)
  have esn2 : I.toInt? (-(env "n" * env "p" * 2)) = some (-(2 * j * k)) := (I.toInt?_eq _ _).2 (by rw [h_n, h_p]; push_cast; ring)
  have esn3 : I.toInt? (-(2 * (env "n" * env "p"))) = some (-(2 * j * k)) := (I.toInt?_eq _ _).2 (by rw [h_n, h_p]; push_cast; ring)
  have esn4 : I.toInt? (-(env "n" * (env "p" * 2))) = some (-(2 * j * k)) := (I.toInt?_eq _ _).2 (by rw [h_n, h_p]; push_cast; ring)
  have e0 : I.toInt? (0 : 𝕜) = some 0 := (I.toInt?_eq _ _).2 (by simp)
  rcases hk_m : I.toInt? (env "m") with _ | mm
  · exfalso; have h := hF.self_of_nhds; simp [rubi1234r93, Defined, eval, hk_n, hk_p, hk_q, hk_m] at h
  have h_m : env "m" = (mm : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have emk0 : I.toInt? (env "m" + -2 * env "n" * env "p") = some (mm - 2 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have emk1 : I.toInt? (env "m" + -(2 * env "n" * env "p")) = some (mm - 2 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have emk2 : I.toInt? (env "m" + -(env "n" * env "p" * 2)) = some (mm - 2 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have emk3 : I.toInt? (env "m" + -(2 * (env "n" * env "p"))) = some (mm - 2 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have emk4 : I.toInt? (env "m" + -(env "n" * (env "p" * 2))) = some (mm - 2 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have emk5 : I.toInt? (env "m" - 2 * env "n" * env "p") = some (mm - 2 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have emk6 : I.toInt? (env "m" - env "n" * env "p" * 2) = some (mm - 2 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have emk7 : I.toInt? (env "m" - 2 * (env "n" * env "p")) = some (mm - 2 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have emk8 : I.toInt? (env "m" - env "n" * (env "p" * 2)) = some (mm - 2 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have emk0 : I.toInt? (env "m" + -2 * env "n" * env "p") = some (mm - 2 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have emk1 : I.toInt? (env "m" + -(2 * env "n" * env "p")) = some (mm - 2 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have emk2 : I.toInt? (env "m" + -(env "n" * env "p" * 2)) = some (mm - 2 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have emk3 : I.toInt? (env "m" + -(2 * (env "n" * env "p"))) = some (mm - 2 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have emk4 : I.toInt? (env "m" + -(env "n" * (env "p" * 2))) = some (mm - 2 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have emk5 : I.toInt? (env "m" - 2 * env "n" * env "p") = some (mm - 2 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have emk6 : I.toInt? (env "m" - env "n" * env "p" * 2) = some (mm - 2 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have emk7 : I.toInt? (env "m" - 2 * (env "n" * env "p")) = some (mm - 2 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have emk8 : I.toInt? (env "m" - env "n" * (env "p" * 2)) = some (mm - 2 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi1234r93.body →
      (j ≠ 0 → w ≠ 0) ∧ (l < 0 → env "d" + env "e" * w ^ j ≠ 0) ∧ (k < 0 → env "a" + env "c" * (w ^ (2 * j))⁻¹ ≠ 0) ∧ (mm < 0 → w ≠ 0) := by
    intro w h
    simp [rubi1234r93, Defined, eval, hk_n, hk_p, hk_q, hk_m, emn2, e2n, esn0, esn1, esn2, esn3, esn4, emk0, emk1, emk2, emk3, emk4, emk5, emk6, emk7, emk8, e0, toInt?_two] at h
    refine ⟨fun hj => ?_, ?_, ?_, ?_⟩
    · rcases lt_or_gt_of_ne hj with hj' | hj' <;> simp_all
    all_goals simp_all
  have hPQ : ∀ w : 𝕜, (j ≠ 0 → w ≠ 0) → env "a" + env "c" * (w ^ (2 * j))⁻¹ = (w ^ (2 * j))⁻¹ * (env "c" + env "a" * w ^ (2 * j)) := by
    intro w hw
    rcases eq_or_ne j 0 with hj | hj
    · subst hj; simp; ring
    · have hw0 := hw hj
      have hy : w ^ j ≠ 0 := zpow_ne_zero _ hw0
      rw [show w ^ (2 * j) = (w ^ j) ^ 2 by rw [mul_comm, zpow_mul]; norm_cast]
      generalize w ^ j = y at hy ⊢
      field_simp
      ring
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1234r93, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2, h3, h4⟩ := hBody w hw
    have hQ : k < 0 → env "c" + env "a" * w ^ (2 * j) ≠ 0 := by
      intro hk h0; apply h3 hk; rw [hPQ w h1, h0, mul_zero]
    rcases eq_or_ne j 0 with hj | hj
    · subst hj; simp [Defined, eval, hk_n, hk_p, hk_q, hk_m, emn2, e2n, esn0, esn1, esn2, esn3, esn4, emk0, emk1, emk2, emk3, emk4, emk5, emk6, emk7, emk8, e0, toInt?_two, h_n, h_p, Interp.toInt?_cast] at hQ h2 ⊢
      first | done | simp (config := {contextual := true}) [hQ, h2, h4] | (trace_state; sorry)
    · have hw0 := h1 hj
      simp (config := {contextual := true}) [Defined, eval, hk_n, hk_p, hk_q, hk_m, emn2, e2n, esn0, esn1, esn2, esn3, esn4, emk0, emk1, emk2, emk3, emk4, emk5, emk6, emk7, emk8, e0, toInt?_two, hw0, hQ, h2]
      first | done | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi1234r93, Defined, eval, recEnv]
  · simp only [rubi1234r93, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨h1, -, -, -⟩ := hBody t hF.self_of_nhds
    have hfun : (fun w => eval I (recEnv env (rubi1234r93.integrals.map (·.1)) Φ "x" w) rubi1234r93.result) = Φ "I1" := by
      funext w; simp [rubi1234r93, eval, recEnv]
    have heq : eval I (Function.update env "x" t) rubi1234r93.body =
        eval I (Function.update env "x" t) (rubi1234r93.integrals.head!).2 := by
      simp [rubi1234r93, eval, hk_n, hk_p, hk_q, hk_m, emn2, e2n, esn0, esn1, esn2, esn3, esn4, emk0, emk1, emk2, emk3, emk4, emk5, emk6, emk7, emk8, e0, toInt?_two]
      rw [hPQ t h1, mul_zpow, inv_zpow, ← zpow_mul]
      rcases eq_or_ne j 0 with hj | hj
      · subst hj; simp [h_n, h_p, e0]
      · have ht0 := h1 hj
        first | ring1 | (rw [zpow_add₀ ht0, zpow_neg]; ring1) | (rw [zpow_sub₀ ht0]; ring1) | (simp [zpow_sub₀ ht0]; ring1) | (trace_state; sorry)
    rw [hfun, heq]
    simpa [rubi1234r93] using hΦ

theorem rubi1234r100_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi1234r100.conditions rubi1234r100.body rubi1234r100.result rubi1234r100.integrals := by
  intro env hc t hF
  have hmn : env "mn" = -1 * env "n" := by
    have h := hc (.eq (.var "mn") (.app2 .mul (.int (-1)) (.var "n"))) (by simp [rubi1234r100]); simpa [Cond.Holds, Defined, eval] using h
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso; have h := hF.self_of_nhds; simp [rubi1234r100, Defined, eval, hk_n] at h
  rcases hk_p : I.toInt? (env "p") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi1234r100, Defined, eval, hk_n, hk_p] at h
  rcases hk_q : I.toInt? (env "q") with _ | l
  · exfalso; have h := hF.self_of_nhds; simp [rubi1234r100, Defined, eval, hk_n, hk_p, hk_q] at h
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have h_p : env "p" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have emn : I.toInt? (env "mn") = some (-j) := (I.toInt?_eq _ _).2 (by rw [hmn, h_n]; push_cast; ring)
  have e2n : I.toInt? (2 * env "n") = some (2 * j) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have esn0 : I.toInt? (-1 * env "n" * env "p") = some (-(1 * j * k)) := (I.toInt?_eq _ _).2 (by rw [h_n, h_p]; push_cast; ring)
  have esn1 : I.toInt? (-(env "n" * env "p")) = some (-(1 * j * k)) := (I.toInt?_eq _ _).2 (by rw [h_n, h_p]; push_cast; ring)
  have e0 : I.toInt? (0 : 𝕜) = some 0 := (I.toInt?_eq _ _).2 (by simp)
  rcases hk_m : I.toInt? (env "m") with _ | mm
  · exfalso; have h := hF.self_of_nhds; simp [rubi1234r100, Defined, eval, hk_n, hk_p, hk_q, hk_m] at h
  have h_m : env "m" = (mm : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have emk0 : I.toInt? (env "m" + -1 * env "n" * env "p") = some (mm - 1 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have emk1 : I.toInt? (env "m" + -(env "n" * env "p")) = some (mm - 1 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have emk2 : I.toInt? (env "m" - env "n" * env "p") = some (mm - 1 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have emk0 : I.toInt? (env "m" + -1 * env "n" * env "p") = some (mm - 1 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have emk1 : I.toInt? (env "m" + -(env "n" * env "p")) = some (mm - 1 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have emk2 : I.toInt? (env "m" - env "n" * env "p") = some (mm - 1 * j * k) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n, h_p]; push_cast; ring)
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi1234r100.body →
      (j ≠ 0 → w ≠ 0) ∧ (l < 0 → env "d" + env "e" * w ^ j ≠ 0) ∧ (k < 0 → env "a" + env "b" * (w ^ j)⁻¹ + env "c" * w ^ j ≠ 0) ∧ (mm < 0 → w ≠ 0) := by
    intro w h
    simp [rubi1234r100, Defined, eval, hk_n, hk_p, hk_q, hk_m, emn, e2n, esn0, esn1, emk0, emk1, emk2, e0, toInt?_two] at h
    refine ⟨fun hj => ?_, ?_, ?_, ?_⟩
    · rcases lt_or_gt_of_ne hj with hj' | hj' <;> simp_all
    all_goals simp_all
  have hPQ : ∀ w : 𝕜, (j ≠ 0 → w ≠ 0) → env "a" + env "b" * (w ^ j)⁻¹ + env "c" * w ^ j = (w ^ j)⁻¹ * (env "b" + env "a" * w ^ j + env "c" * w ^ (2 * j)) := by
    intro w hw
    rcases eq_or_ne j 0 with hj | hj
    · subst hj; simp; ring
    · have hw0 := hw hj
      have hy : w ^ j ≠ 0 := zpow_ne_zero _ hw0
      rw [show w ^ (2 * j) = (w ^ j) ^ 2 by rw [mul_comm, zpow_mul]; norm_cast]
      generalize w ^ j = y at hy ⊢
      field_simp
      ring
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1234r100, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2, h3, h4⟩ := hBody w hw
    have hQ : k < 0 → env "b" + env "a" * w ^ j + env "c" * w ^ (2 * j) ≠ 0 := by
      intro hk h0; apply h3 hk; rw [hPQ w h1, h0, mul_zero]
    rcases eq_or_ne j 0 with hj | hj
    · subst hj; simp [Defined, eval, hk_n, hk_p, hk_q, hk_m, emn, e2n, esn0, esn1, emk0, emk1, emk2, e0, toInt?_two, h_n, h_p, Interp.toInt?_cast] at hQ h2 ⊢
      first | done | simp (config := {contextual := true}) [hQ, h2, h4] | (trace_state; sorry)
    · have hw0 := h1 hj
      simp (config := {contextual := true}) [Defined, eval, hk_n, hk_p, hk_q, hk_m, emn, e2n, esn0, esn1, emk0, emk1, emk2, e0, toInt?_two, hw0, hQ, h2]
      first | done | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi1234r100, Defined, eval, recEnv]
  · simp only [rubi1234r100, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨h1, -, -, -⟩ := hBody t hF.self_of_nhds
    have hfun : (fun w => eval I (recEnv env (rubi1234r100.integrals.map (·.1)) Φ "x" w) rubi1234r100.result) = Φ "I1" := by
      funext w; simp [rubi1234r100, eval, recEnv]
    have heq : eval I (Function.update env "x" t) rubi1234r100.body =
        eval I (Function.update env "x" t) (rubi1234r100.integrals.head!).2 := by
      simp [rubi1234r100, eval, hk_n, hk_p, hk_q, hk_m, emn, e2n, esn0, esn1, emk0, emk1, emk2, e0, toInt?_two]
      rw [hPQ t h1, mul_zpow, inv_zpow, ← zpow_mul]
      rcases eq_or_ne j 0 with hj | hj
      · subst hj; simp [h_n, h_p, e0]
      · have ht0 := h1 hj
        first | ring1 | (rw [zpow_add₀ ht0, zpow_neg]; ring1) | (rw [zpow_sub₀ ht0]; ring1) | (simp [zpow_sub₀ ht0]; ring1) | (trace_state; sorry)
    rw [hfun, heq]
    simpa [rubi1234r100] using hΦ

theorem rubi1233r41_real : rubi1233r41.Holds .real := rubi1233r41_holds Interp.real
theorem rubi1233r41_complex : rubi1233r41.Holds .complex := rubi1233r41_holds Interp.complex
theorem rubi1233r42_real : rubi1233r42.Holds .real := rubi1233r42_holds Interp.real
theorem rubi1233r42_complex : rubi1233r42.Holds .complex := rubi1233r42_holds Interp.complex
theorem rubi1233r47_real : rubi1233r47.Holds .real := rubi1233r47_holds Interp.real
theorem rubi1233r47_complex : rubi1233r47.Holds .complex := rubi1233r47_holds Interp.complex
theorem rubi1234r92_real : rubi1234r92.Holds .real := rubi1234r92_holds Interp.real
theorem rubi1234r92_complex : rubi1234r92.Holds .complex := rubi1234r92_holds Interp.complex
theorem rubi1234r93_real : rubi1234r93.Holds .real := rubi1234r93_holds Interp.real
theorem rubi1234r93_complex : rubi1234r93.Holds .complex := rubi1234r93_holds Interp.complex
theorem rubi1234r100_real : rubi1234r100.Holds .real := rubi1234r100_holds Interp.real
theorem rubi1234r100_complex : rubi1234r100.Holds .complex := rubi1234r100_holds Interp.complex

end Proofs

end OSR.IntegrationRec118
