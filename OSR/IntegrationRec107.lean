import OSR.IntegrationRec98
import OSR.IntegrationRec7

/-!
# Integration (RUBI): strengthened variant of 3.2.3 #8

RUBI 3.2.3 #8 is refuted as stated, and its first strengthened variant (with
`k n t (m + 1) ≠ 0`) fails the pole probe when `p` or `q` vanishes.  With
`p, q, r ≠ 0` as well it is proved over ℝ, with the real logarithm: the
condition `h j = g k` makes `1/(j + k x) = h/(k (g + h x))`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec107

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- rubi_3_2_3_r8 with NeQ[Multiply[k, n, t, Add[m, 1]], 0]; NeQ[p, 0]; NeQ[q, 0]; NeQ[r, 0] -/
def rubi323r8Nondeg : CRule where
  id := "integration.rubi_3_2_3_r8_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s:8"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "s") (.app2 .mul (.var "t") (.app1 .ln (.app2 .mul (.var "i") (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "n")))))) (.var "m")) (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "q"))) (.var "r"))))) (.pow (.app2 .add (.var "j") (.app2 .mul (.var "k") (.var "x"))) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "s") (.app2 .mul (.var "t") (.app1 .ln (.app2 .mul (.var "i") (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "n")))))) (.app2 .add (.var "m") (.int 1))) (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "q"))) (.var "r"))))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "k") (.var "n")) (.var "t")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "p")) (.var "r")) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "k") (.var "n")) (.var "t")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "q")) (.var "r")) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "k") (.var "n")) (.var "t")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", .app2 .mul (.pow (.app2 .add (.var "s") (.app2 .mul (.var "t") (.app1 .ln (.app2 .mul (.var "i") (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "n")))))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.int (-1)))), ("I2", .app2 .mul (.pow (.app2 .add (.var "s") (.app2 .mul (.var "t") (.app1 .ln (.app2 .mul (.var "i") (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "n")))))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "s", "t", "m", "n", "p", "q", "r"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0), .eq (.app2 .add (.app2 .mul (.var "h") (.var "j")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "g")) (.var "k"))) (.int 0), .int (.var "m"), .gt (.var "m") (.int 0),
    .ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "k") (.var "n")) (.var "t")) (.app2 .add (.var "m") (.int 1))) (.int 0),
    .ne (.var "p") (.int 0),
    .ne (.var "q") (.int 0),
    .ne (.var "r") (.int 0)]
  priority := 9251
  description := "rubi_3_2_3_r8 with NeQ[Multiply[k, n, t, Add[m, 1]], 0]; NeQ[p, 0]; NeQ[q, 0]; NeQ[r, 0]"
  provenance := migrated "rubi:3 Logarithms/3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s:8" "3 Logarithms/3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s.m#8"


/-! ## Proofs -/

section Proofs

private theorem zpow_succ_of (A : ℝ) (k : ℤ) (h : A ≠ 0 ∨ 0 ≤ k) : A ^ (k + 1) = A ^ k * A := by
  rcases h with h | h
  · exact zpow_add_one₀ h k
  · lift k to ℕ using h
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
      pow_succ]

theorem rubi323r8Nondeg_real : rubi323r8Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi323r8Nondeg.conditions rubi323r8Nondeg.body rubi323r8Nondeg.result rubi323r8Nondeg.integrals
  intro env hc x0 hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have ord : ∀ (x y : ℤ), Interp.real.lt (x : ℝ) (y : ℝ) → x < y := by
    intro x y h
    have h' : Interp.real.lt ((x : ℚ) : ℝ) ((y : ℚ) : ℝ) := by rw [Rat.cast_intCast, Rat.cast_intCast]; exact h
    exact_mod_cast (Interp.real_lt_rat _ _).1 h'
  have heq := hc (.eq (.app2 .add (.app2 .mul (.var "h") (.var "j")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "g")) (.var "k"))) (.int 0)) (by simp [rubi323r8Nondeg])
  simp [Cond.Holds, Defined, eval] at heq
  have hA0 := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "k") (.var "n")) (.var "t")) (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi323r8Nondeg])
  simp [Cond.Holds, Defined, eval] at hA0
  have hp0 : env "p" ≠ 0 := by have h := hc (.ne (.var "p") (.int 0)) (by simp [rubi323r8Nondeg]); simpa [Cond.Holds, Defined, eval] using h
  have hq0 : env "q" ≠ 0 := by have h := hc (.ne (.var "q") (.int 0)) (by simp [rubi323r8Nondeg]); simpa [Cond.Holds, Defined, eval] using h
  have hr0 : env "r" ≠ 0 := by have h := hc (.ne (.var "r") (.int 0)) (by simp [rubi323r8Nondeg]); simpa [Cond.Holds, Defined, eval] using h
  have hk0 : env "k" ≠ 0 := by intro h; simp [h] at hA0
  have hn0 : env "n" ≠ 0 := by intro h; simp [h] at hA0
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi323r8Nondeg, Defined, eval, Interp.real, hm1, hk_m, -Real.log_eq_zero] at h
  have h_m : env "m" = (km : ℝ) := (intValue?_eq _ _).1 hk_m
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi323r8Nondeg, Defined, eval, Interp.real, hm1, hk_m, hk_n, -Real.log_eq_zero] at h
  have h_n : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi323r8Nondeg, Defined, eval, Interp.real, hm1, hk_m, hk_n, hk_p, -Real.log_eq_zero] at h
  have h_p : env "p" = (kp : ℝ) := (intValue?_eq _ _).1 hk_p
  rcases hk_q : intValue? (env "q") with _ | kq
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi323r8Nondeg, Defined, eval, Interp.real, hm1, hk_m, hk_n, hk_p, hk_q, -Real.log_eq_zero] at h
  have h_q : env "q" = (kq : ℝ) := (intValue?_eq _ _).1 hk_q
  rcases hk_r : intValue? (env "r") with _ | kr
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi323r8Nondeg, Defined, eval, Interp.real, hm1, hk_m, hk_n, hk_p, hk_q, hk_r, -Real.log_eq_zero] at h
  have h_r : env "r" = (kr : ℝ) := (intValue?_eq _ _).1 hk_r
  have g_m := hc (.gt (.var "m") (.int 0)) (by simp [rubi323r8Nondeg])
  have hkm : 0 < km := by
    simp only [Cond.Holds, Defined, eval, true_and] at g_m; simp only [h_m] at g_m
    exact ord _ _ (by simpa using g_m)
  have hkn0 : kn ≠ 0 := by intro h; apply hn0; rw [h_n, h]; simp
  have hkp0 : kp ≠ 0 := by intro h; apply hp0; rw [h_p, h]; simp
  have hkq0 : kq ≠ 0 := by intro h; apply hq0; rw [h_q, h]; simp
  have hkr0 : kr ≠ 0 := by intro h; apply hr0; rw [h_r, h]; simp
  have em1 : intValue? (env "m" + 1) = some (km + 1) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have hm0 : ¬ km < 0 := by omega
  have hm1' : ¬ km + 1 < 0 := by omega
  have hGne : ∀ w : ℝ, 0 < env "i" * (env "g" + env "h" * w) ^ kn → (env "g" + env "h" * w) ≠ 0 := by
    intro w h h0; rw [h0, zero_zpow kn hkn0, mul_zero] at h; exact lt_irrefl 0 h
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi323r8Nondeg.body →
      0 < env "i" * (env "g" + env "h" * w) ^ kn ∧ 0 < (env "e" * (env "f" * (env "a" + env "b" * w) ^ kp * (env "c" + env "d" * w) ^ kq) ^ kr) ∧ (env "j" + env "k" * w) ≠ 0 := by
    intro w h
    simp [rubi323r8Nondeg, Defined, eval, Interp.real, hk_m, hk_n, hk_p, hk_q, hk_r, em1, hm1, -Real.log_eq_zero, hm0] at h
    first | exact ⟨h.1.1.2, h.1.2.2, h.2⟩ | exact ⟨h.1.1.1.2, h.1.2.2, h.2⟩ | tauto
  have hfac : ∀ w, 0 < (env "e" * (env "f" * (env "a" + env "b" * w) ^ kp * (env "c" + env "d" * w) ^ kq) ^ kr) → (env "a" + env "b" * w) ≠ 0 ∧ (env "c" + env "d" * w) ≠ 0 ∧ env "f" ≠ 0 := by
    intro w h
    obtain ⟨h1, h2, -⟩ := OSR.IntegrationRec98.hasDerivAt_log_prod (env "e") (env "f") (env "a") (env "b") (env "c") (env "d") kp kq kr w hkp0 hkq0 hkr0 h
    refine ⟨h1, h2, ?_⟩
    rintro h0
    rw [h0, zero_mul, zero_mul, zero_zpow kr hkr0, mul_zero] at h
    exact lt_irrefl 0 h
  refine ⟨fun i' hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi323r8Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    · obtain ⟨h1, h2, h3⟩ := hBody w hw
      obtain ⟨hA, hC, hf⟩ := hfac w h2
      simp [Defined, eval, Interp.real, hk_m, hk_n, hk_p, hk_q, hk_r, em1, hm1, -Real.log_eq_zero, hm1', h1, hA, hC, hGne w h1]
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h2, h3⟩ := hBody w hw
    obtain ⟨hA, hC, hf⟩ := hfac w h2
    simp [rubi323r8Nondeg, Defined, eval, Interp.real, recEnv, hk_m, hk_n, hk_p, hk_q, hk_r, em1, hm1, -Real.log_eq_zero, hm1', h1, h2, hA, hC, hf, hA0, zpow_ne_zero kp hA, zpow_ne_zero kq hC, hGne w h1]
  · simp only [rubi323r8Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    obtain ⟨hpos1, hpos2, hJ0⟩ := hBody x0 hF.self_of_nhds
    have hG0 := hGne x0 hpos1
    obtain ⟨hA0', hC0', hL2⟩ := OSR.IntegrationRec98.hasDerivAt_log_prod (env "e") (env "f") (env "a") (env "b") (env "c") (env "d") kp kq kr x0 hkp0 hkq0 hkr0 hpos2
    have hh0 : env "h" ≠ 0 := by
      intro h0
      rw [h0, zero_mul, add_zero] at hG0
      apply hG0
      have : env "g" * env "k" = 0 := by rw [h0] at heq; linear_combination -heq
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd h hk0
    have hJe : (env "j" + env "k" * x0) = env "k" * (env "g" + env "h" * x0) * (env "h")⁻¹ := by
      field_simp
      first | linear_combination heq | linear_combination -heq | linear_combination (-1) * heq
    have hJinv : (env "j" + env "k" * x0)⁻¹ = env "h" * (env "k" * (env "g" + env "h" * x0))⁻¹ := by
      rw [hJe, mul_inv, inv_inv]; ring
    have hΦ1' : HasDerivAt (Φ "I1") ((env "s" + env "t" * Real.log (env "i" * (env "g" + env "h" * x0) ^ kn)) ^ (km + 1) * (env "a" + env "b" * x0)⁻¹) x0 := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hk_m, hk_n, hk_p, hk_q, hk_r, em1, hm1, -Real.log_eq_zero]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "s" + env "t" * Real.log (env "i" * (env "g" + env "h" * x0) ^ kn)) ^ (km + 1) * (env "c" + env "d" * x0)⁻¹) x0 := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hk_m, hk_n, hk_p, hk_q, hk_r, em1, hm1, -Real.log_eq_zero]
    have hEF : eval Interp.real (Function.update env "x" x0) rubi323r8Nondeg.body = (env "s" + env "t" * Real.log (env "i" * (env "g" + env "h" * x0) ^ kn)) ^ km * Real.log (env "e" * (env "f" * (env "a" + env "b" * x0) ^ kp * (env "c" + env "d" * x0) ^ kq) ^ kr) * (env "j" + env "k" * x0)⁻¹ := by
      simp [rubi323r8Nondeg, eval, Interp.real, hk_m, hk_n, hk_p, hk_q, hk_r, em1, hm1, -Real.log_eq_zero]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi323r8Nondeg.integrals.map (·.1)) Φ "x" w) rubi323r8Nondeg.result) =
        fun w => (env "s" + env "t" * Real.log (env "i" * (env "g" + env "h" * w) ^ kn)) ^ (km + 1) * Real.log (env "e" * (env "f" * (env "a" + env "b" * w) ^ kp * (env "c" + env "d" * w) ^ kq) ^ kr) * (env "k" * env "n" * env "t" * (env "m" + 1))⁻¹ +
          -1 * env "b" * env "p" * env "r" * (env "k" * env "n" * env "t" * (env "m" + 1))⁻¹ * Φ "I1" w +
          -1 * env "d" * env "q" * env "r" * (env "k" * env "n" * env "t" * (env "m" + 1))⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi323r8Nondeg, eval, Interp.real, recEnv, hk_m, hk_n, hk_p, hk_q, hk_r, em1, hm1, -Real.log_eq_zero, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF, hJinv]
    have hGd : HasDerivAt (fun w => (env "g" + env "h" * w)) (env "h") x0 := by
      simpa using ((hasDerivAt_id' x0).const_mul (env "h")).const_add (env "g")
    have hL1 := (OSR.IntegrationRec7.hasDerivAt_log_monomial (env "i") (env "g" + env "h" * x0) kn hpos1).comp x0 hGd
    have hM := (hL1.const_mul (env "t")).const_add (env "s")
    have hMp := HasDerivAt.comp x0 (hasDerivAt_zpow (km + 1) _ (Or.inr (by omega))) hM
    refine ((((hMp.mul hL2).mul_const _).add (hΦ1'.const_mul _)).add (hΦ2'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    rw [zpow_succ_of _ _ (Or.inr (by omega)), div_eq_mul_inv]
    generalize (env "s" + env "t" * Real.log (env "i" * (env "g" + env "h" * x0) ^ kn)) ^ km = Mk
    generalize (env "s" + env "t" * Real.log (env "i" * (env "g" + env "h" * x0) ^ kn)) = Mv
    generalize Real.log (env "e" * (env "f" * (env "a" + env "b" * x0) ^ kp * (env "c" + env "d" * x0) ^ kq) ^ kr) = L
    generalize hAe : env "a" + env "b" * x0 = A at hA0' ⊢
    generalize hCe : env "c" + env "d" * x0 = C at hC0' ⊢
    generalize hGe : (env "g" + env "h" * x0) = Gv at hG0 ⊢
    simp only [h_m, h_n, h_p, h_q, h_r] at *
    casesm* _ ∧ _
    field_simp
    push_cast
    ring

end Proofs

end OSR.IntegrationRec107
