import OSR.IntegrationNum1

/-!
# Integration (RUBI): strengthened recursive rule 1.1.3.4 #29

The proof covers the boundary term and every residual antiderivative.
-/

namespace OSR.IntegrationRec206

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

/-- The residual polynomial and differentiated boundary term recombine. -/
theorem rubi1134r29_coefficient {K : Type} [CommRing K]
    (a b c d m n p x : K) :
    d ^ 2 * x * ((m + n + 1) * (a + b * x) + b * n * (p + 1) * x) +
      (b * c ^ 2 * (m + n * (p + 2) + 1) +
        d * ((2 * b * c - a * d) * (m + n + 1) + 2 * b * c * n * (p + 1)) * x) =
      b * (m + n * (p + 2) + 1) * (c + d * x) ^ 2 := by
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

/-- RUBI 1.1.3.4 #29 with nonzero denominator. -/
theorem rubi1134r29Nondeg_holds (I : Interp K)
    (hlt : ∀ j : ℤ, I.lt 0 (j : K) → 0 < j) :
    AntiderivRecHolds I "x" rubi1134r29Nondeg.conditions rubi1134r29Nondeg.body
      rubi1134r29Nondeg.result rubi1134r29Nondeg.integrals := by
  intro env hc t hF
  have hpos : I.lt 0 (env "n") := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi1134r29Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : I.toInt? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1134r29Nondeg, Defined, eval, hkm, int_two] at h
  rcases hkn : I.toInt? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1134r29Nondeg, Defined, eval, hkn, int_two] at h
  rcases hkp : I.toInt? (env "p") with _ | p
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1134r29Nondeg, Defined, eval, hkp, int_two] at h
  have hm : env "m" = (m : K) := (I.toInt?_eq _ _).1 hkm
  have hn : env "n" = (n : K) := (I.toInt?_eq _ _).1 hkn
  have hp : env "p" = (p : K) := (I.toInt?_eq _ _).1 hkp
  have hnpos : 0 < n := hlt n (by simpa [hn] using hpos)
  have hkn1 : I.toInt? (env "n" + 1) = some (n + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hn]; push_cast; ring)
  have hkmn : I.toInt? (env "m" + env "n") = some (m + n) :=
    (I.toInt?_eq _ _).2 (by rw [hm, hn]; push_cast; ring)
  have hkmn1 : I.toInt? (env "m" + env "n" + 1) = some (m + n + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hm, hn]; push_cast; ring)
  have hkp1 : I.toInt? (env "p" + 1) = some (p + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hd : env "b" * env "e" ^ (n + 1) *
      (env "m" + env "n" * (env "p" + 2) + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.pow (.var "e")
      (.app2 .add (.var "n") (.int 1)))) (.app2 .add (.app2 .add (.var "m")
      (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 2)))) (.int 1))) (.int 0))
      (by simp [rubi1134r29Nondeg])
    have h' : (n + 1 < 0 → env "e" ≠ 0) ∧
        env "b" * env "e" ^ (n + 1) * (env "m" + env "n" * (env "p" + 2) + 1) ≠ 0 := by
      simpa [Cond.Holds, Defined, eval, hkn1] using h
    exact h'.2
  have he : env "e" ≠ 0 := by
    intro h
    apply hd
    rw [h, zero_zpow (n + 1) (by omega)]
    ring
  have hd2 : env "b" * (env "m" + env "n" * (env "p" + 2) + 1) ≠ 0 := by
    intro h
    apply hd
    linear_combination env "e" ^ (n + 1) * h
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1134r29Nondeg.body →
      (m < 0 → w ≠ 0) ∧ (n < 0 → w ≠ 0) ∧
      (p < 0 → env "a" + env "b" * w ^ n ≠ 0) := by
    intro w h
    simp [rubi1134r29Nondeg, Defined, eval, hkm, hkn, hkp, int_two] at h
    tauto
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1134r29Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hm0, hn0, hp0⟩ := hD w hw
    simp [Defined, eval, hkm, hkn, hkp, he, int_two]
    exact ⟨⟨hm0, hn0, hp0⟩, hn0⟩
  · filter_upwards [hF] with w hw
    obtain ⟨hm0, hn0, hp0⟩ := hD w hw
    simp [rubi1134r29Nondeg, Defined, eval, recEnv, hkmn1, hkn1, hkn, hkp1,
      int_neg_one, int_two, hd, he, hd2]
    exact ⟨fun h => hm0 (by omega), hn0, fun h => hp0 (by omega)⟩
  · simp only [rubi1134r29Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hE : ∀ w, eval I (recEnv env (rubi1134r29Nondeg.integrals.map (·.1)) Φ "x" w)
        rubi1134r29Nondeg.result =
      env "d" ^ 2 * (env "e" * w) ^ (m + n + 1) *
        (env "a" + env "b" * w ^ n) ^ (p + 1) *
        (env "b" * env "e" ^ (n + 1) * (env "m" + env "n" * (env "p" + 2) + 1))⁻¹ +
        (env "b" * (env "m" + env "n" * (env "p" + 2) + 1))⁻¹ * Φ "I1" w := by
      intro w
      simp [rubi1134r29Nondeg, eval, recEnv, hkmn1, hkn1, hkn, hkp1, int_neg_one, int_two]
    have hEF : eval I (Function.update env "x" t) rubi1134r29Nondeg.body =
      (env "e" * t) ^ m * (env "a" + env "b" * t ^ n) ^ p *
        (env "c" + env "d" * t ^ n) ^ 2 := by
      simp [rubi1134r29Nondeg, eval, hkm, hkn, hkp, int_two]
    rw [hEF, show (fun w => eval I (recEnv env (rubi1134r29Nondeg.integrals.map (·.1)) Φ "x" w)
      rubi1134r29Nondeg.result) = fun w =>
      env "d" ^ 2 * (env "e" * w) ^ (m + n + 1) *
        (env "a" + env "b" * w ^ n) ^ (p + 1) *
        (env "b" * env "e" ^ (n + 1) * (env "m" + env "n" * (env "p" + 2) + 1))⁻¹ +
        (env "b" * (env "m" + env "n" * (env "p" + 2) + 1))⁻¹ * Φ "I1" w from funext hE]
    have hI : HasDerivAt (Φ "I1")
      ((env "e" * t) ^ m * (env "a" + env "b" * t ^ n) ^ p *
        (env "b" * env "c" ^ 2 * (env "m" + env "n" * (env "p" + 2) + 1) +
          env "d" * ((2 * env "b" * env "c" - env "a" * env "d") * (env "m" + env "n" + 1) +
            2 * env "b" * env "c" * env "n" * (env "p" + 1)) * t ^ n)) t := by
      simpa [rubi1134r29Nondeg, eval, hkm, hkn, hkp, int_two, sub_eq_add_neg] using hΦ
    have he0 : env "e" * t ≠ 0 ∨ 0 ≤ m := by
      by_cases h : m < 0
      · exact Or.inl (mul_ne_zero he (ht.1 h))
      · exact Or.inr (by omega)
    have hx : t ≠ 0 ∨ 0 ≤ n := by
      by_cases h : n < 0
      · exact Or.inl (ht.2.1 h)
      · exact Or.inr (by omega)
    have hu : env "a" + env "b" * t ^ n ≠ 0 ∨ 0 ≤ p := by
      by_cases h : p < 0
      · exact Or.inl (ht.2.2 h)
      · exact Or.inr (by omega)
    have heMN : env "e" * t ≠ 0 ∨ 0 ≤ m + n := he0.imp_right (by omega)
    have he1 : env "e" * t ≠ 0 ∨ 0 ≤ m + n + 1 := heMN.imp_right (by omega)
    have hu1 : env "a" + env "b" * t ^ n ≠ 0 ∨ 0 ≤ p + 1 := hu.imp_right (by omega)
    have hkey : (n : K) * t ^ (n - 1) * t = (n : K) * t ^ n := by
      rcases em (n = 0) with hn0 | hn0
      · subst hn0; simp
      · have h' : t ≠ 0 ∨ 0 ≤ n - 1 := by
          by_cases hn' : n < 0
          · exact Or.inl (ht.2.1 hn')
          · exact Or.inr (by omega)
        rw [show t ^ n = t ^ (n - 1) * t by rw [← zsucc _ _ h', sub_add_cancel]]
        ring
    have hscale : (env "e" * t) ^ (m + n) = (env "e" * t) ^ m * env "e" ^ n * t ^ n := by
      by_cases ht0 : t = 0
      · have hm0 : 0 ≤ m := by by_contra h; exact ht.1 (by omega) ht0
        lift m to ℕ using hm0
        lift n to ℕ using (show 0 ≤ n by omega)
        rw [← Int.natCast_add, zpow_natCast, zpow_natCast, zpow_natCast, pow_add, mul_pow]
        simp only [zpow_natCast]
        ring
      · rw [zpow_add₀ (mul_ne_zero he ht0), mul_zpow]
        simp only [mul_zpow]
        ring
    have hU := ((hasDerivAt_zpow n t hx).const_mul (env "b")).const_add (env "a")
    refine (((((HasDerivAt.comp t (hasDerivAt_zpow (m + n + 1) _ he1)
      ((hasDerivAt_id' t).const_mul (env "e"))).const_mul (env "d" ^ 2)).mul
      (HasDerivAt.comp t (hasDerivAt_zpow (p + 1) _ hu1) hU)).mul_const _).add
      (hI.const_mul (env "b" * (env "m" + env "n" * (env "p" + 2) + 1))⁻¹)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    rw [zsucc _ _ heMN, zsucc _ _ hu]
    rw [hscale]
    generalize (env "e" * t) ^ m = E
    generalize (env "a" + env "b" * t ^ n) ^ p = U
    generalize t ^ (n - 1) = R at hkey ⊢
    generalize t ^ n = T at hkey ⊢
    rw [hm, hn, hp] at hd hd2 ⊢
    push_cast at hd hd2 ⊢
    have hi : (env "b" * env "e" ^ (n + 1) * ((m : K) + (n : K) * ((p : K) + 2) + 1))⁻¹ =
        (env "b" * ((m : K) + (n : K) * ((p : K) + 2) + 1))⁻¹ *
          (env "e" ^ n)⁻¹ * (env "e")⁻¹ := by
      rw [zsucc _ _ (Or.inl he)]
      rw [← mul_inv]
      rw [← mul_inv]
      congr 1
      ring
    rw [hi]
    have hb : env "b" ≠ 0 := left_ne_zero_of_mul hd2
    have hL : (m : K) + (n : K) * ((p : K) + 2) + 1 ≠ 0 := right_ne_zero_of_mul hd2
    have hen : env "e" ^ n ≠ 0 := zpow_ne_zero _ he
    field_simp [hb, hL, he, hen]
    linear_combination
      (env "d" ^ 2 * E * U * T * env "b" * (p + 1)) * hkey

theorem rubi1134r29Nondeg_real : rubi1134r29Nondeg.Holds .real :=
  rubi1134r29Nondeg_holds Interp.real (by intro j h; change (0 : ℝ) < (j : ℝ) at h; exact_mod_cast h)

theorem rubi1134r29Nondeg_complex : rubi1134r29Nondeg.Holds .complex :=
  rubi1134r29Nondeg_holds Interp.complex (by intro j h; have h' := h.2.2; exact_mod_cast h')

end

end OSR.IntegrationRec206
