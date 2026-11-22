import OSR.IntegrationNum1

/-!
# Integration (RUBI): algebra for the strengthened rule 1.1.1.3 #19

The polynomial identity below relates the differentiated boundary term and
the residual integrand. The full rule also requires definedness and
differentiability of the integer powers and of the residual antiderivative.
-/

namespace OSR.IntegrationRec201

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

/-- Polynomial identity used by the integration-by-parts rule. -/
theorem rubi1113r19_coefficient {K : Type} [CommRing K]
    (a b c d e f n p x : K) :
    b * (b * (c + d * x) * (e + f * x) +
      (a + b * x) * d * (n + 1) * (e + f * x) +
      (a + b * x) * f * (p + 1) * (c + d * x)) +
      (a ^ 2 * d * f * (n + p + 3) -
        b * (b * c * e + a * (d * e * (n + 1) + c * f * (p + 1))) +
        b * (a * d * f * (n + p + 4) -
          b * (d * e * (n + 2) + c * f * (p + 2))) * x) =
      d * f * (n + p + 3) * (a + b * x) ^ 2 := by
  ring

section
variable {K : Type} [NontriviallyNormedField K]

private theorem int_neg_one (I : Interp K) : I.toInt? (-1 : K) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem int_two (I : Interp K) : I.toInt? (2 : K) = some 2 :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem zsucc (a : K) (k : ℤ) (h : a ≠ 0 ∨ 0 ≤ k) : a ^ (k + 1) = a ^ k * a := by
  rcases h with h | h
  · exact zpow_add_one₀ h k
  · lift k to ℕ using h
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast, zpow_natCast, pow_succ]

/-- RUBI 1.1.1.3 #19 with the denominator required to be nonzero. -/
theorem rubi1113r19Nondeg_holds (I : Interp K) :
    AntiderivRecHolds I "x" rubi1113r19Nondeg.conditions rubi1113r19Nondeg.body
      rubi1113r19Nondeg.result rubi1113r19Nondeg.integrals := by
  intro env hc t hF
  have hd : env "d" * env "f" * (env "n" + env "p" + 3) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "d") (.var "f"))
      (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 3))) (.int 0))
      (by simp [rubi1113r19Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkn : I.toInt? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1113r19Nondeg, Defined, eval, hkn, int_two] at h
  rcases hkp : I.toInt? (env "p") with _ | p
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1113r19Nondeg, Defined, eval, hkp, int_two] at h
  have hn : env "n" = (n : K) := (I.toInt?_eq _ _).1 hkn
  have hp : env "p" = (p : K) := (I.toInt?_eq _ _).1 hkp
  have hkn1 : I.toInt? (env "n" + 1) = some (n + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hn]; push_cast; ring)
  have hkp1 : I.toInt? (env "p" + 1) = some (p + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1113r19Nondeg.body →
      (n < 0 → env "c" + env "d" * w ≠ 0) ∧
      (p < 0 → env "e" + env "f" * w ≠ 0) := by
    intro w h
    simp [rubi1113r19Nondeg, Defined, eval, hkn, hkp, int_two] at h
    exact h
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1113r19Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, hkn, hkp, int_two]
    exact h
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1113r19Nondeg, Defined, eval, recEnv, hkn1, hkp1, int_neg_one, hd]
    exact ⟨fun h' => h.1 (by omega), fun h' => h.2 (by omega)⟩
  · simp only [rubi1113r19Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hE : ∀ w, eval I (recEnv env (rubi1113r19Nondeg.integrals.map (·.1)) Φ "x" w)
        rubi1113r19Nondeg.result =
      (env "b" * (env "a" + env "b" * w) * (env "c" + env "d" * w) ^ (n + 1) *
        (env "e" + env "f" * w) ^ (p + 1) + Φ "I1" w) *
        (env "d" * env "f" * (env "n" + env "p" + 3))⁻¹ := by
      intro w
      simp [rubi1113r19Nondeg, eval, recEnv, hkn1, hkp1, int_neg_one]
      ring
    have hEF : eval I (Function.update env "x" t) rubi1113r19Nondeg.body =
      (env "a" + env "b" * t) ^ 2 * (env "c" + env "d" * t) ^ n *
        (env "e" + env "f" * t) ^ p := by
      simp [rubi1113r19Nondeg, eval, hkn, hkp, int_two]
    rw [hEF, show (fun w => eval I (recEnv env (rubi1113r19Nondeg.integrals.map (·.1)) Φ "x" w)
      rubi1113r19Nondeg.result) = fun w =>
      (env "b" * (env "a" + env "b" * w) * (env "c" + env "d" * w) ^ (n + 1) *
        (env "e" + env "f" * w) ^ (p + 1) + Φ "I1" w) *
        (env "d" * env "f" * (env "n" + env "p" + 3))⁻¹ from funext hE]
    have hu : env "c" + env "d" * t ≠ 0 ∨ 0 ≤ n := by
      by_cases h : n < 0
      · exact Or.inl (ht.1 h)
      · exact Or.inr (by omega)
    have hv : env "e" + env "f" * t ≠ 0 ∨ 0 ≤ p := by
      by_cases h : p < 0
      · exact Or.inl (ht.2 h)
      · exact Or.inr (by omega)
    have hu1 : env "c" + env "d" * t ≠ 0 ∨ 0 ≤ n + 1 := hu.imp_right (by omega)
    have hv1 : env "e" + env "f" * t ≠ 0 ∨ 0 ≤ p + 1 := hv.imp_right (by omega)
    have hI : HasDerivAt (Φ "I1")
      ((env "c" + env "d" * t) ^ n * (env "e" + env "f" * t) ^ p *
        (env "a" ^ 2 * env "d" * env "f" * (env "n" + env "p" + 3) -
          env "b" * (env "b" * env "c" * env "e" + env "a" *
            (env "d" * env "e" * (env "n" + 1) + env "c" * env "f" * (env "p" + 1))) +
          env "b" * (env "a" * env "d" * env "f" * (env "n" + env "p" + 4) -
            env "b" * (env "d" * env "e" * (env "n" + 2) + env "c" * env "f" * (env "p" + 2))) * t)) t := by
      simpa [rubi1113r19Nondeg, eval, hkn, hkp, int_two, sub_eq_add_neg] using hΦ
    refine ((((((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).const_mul (env "b")).mul
      (HasDerivAt.comp t (hasDerivAt_zpow (n + 1) _ hu1)
        (((hasDerivAt_id' t).const_mul (env "d")).const_add (env "c")))).mul
      (HasDerivAt.comp t (hasDerivAt_zpow (p + 1) _ hv1)
        (((hasDerivAt_id' t).const_mul (env "f")).const_add (env "e")))).add hI |>.mul_const _ |>.congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, add_sub_cancel_right]
    rw [zsucc _ _ hu, zsucc _ _ hv]
    rw [hn, hp] at hd ⊢
    push_cast at hd ⊢
    rw [mul_inv_eq_iff_eq_mul₀ hd]
    linear_combination (env "c" + env "d" * t) ^ n * (env "e" + env "f" * t) ^ p *
      rubi1113r19_coefficient (env "a") (env "b") (env "c") (env "d") (env "e") (env "f") (n : K) (p : K) t

theorem rubi1113r19Nondeg_real : rubi1113r19Nondeg.Holds .real :=
  rubi1113r19Nondeg_holds Interp.real

theorem rubi1113r19Nondeg_complex : rubi1113r19Nondeg.Holds .complex :=
  rubi1113r19Nondeg_holds Interp.complex

end

end OSR.IntegrationRec201
