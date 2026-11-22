import OSR.IntegrationNum1

/-!
# Integration (RUBI): strengthened recursive rule 1.1.3.4 #28

The proof covers the boundary term and every residual antiderivative.
-/

namespace OSR.IntegrationRec205

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

/-- The residual polynomial and the differentiated boundary term recombine. -/
theorem rubi1134r28_coefficient {K : Type} [CommRing K]
    (a b c d m n p x : K) :
    (a + b * x) * ((b * c - a * d) ^ 2 * (m + 1) +
      b ^ 2 * c ^ 2 * n * (p + 1) + a * b * d ^ 2 * n * (p + 1) * x) -
      (b * c - a * d) ^ 2 * ((m + 1) * (a + b * x) + b * n * (p + 1) * x) =
      a * b ^ 2 * n * (p + 1) * (c + d * x) ^ 2 := by
  ring

section
variable {K : Type} [NontriviallyNormedField K]

/-- The denominator condition shared by the RUBI variant and its order-free generalization. -/
def rubi1134r28Denominator : Cond :=
  .ne (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "a")
    (.pow (.var "b") (.int 2))) (.var "e")) (.var "n"))
    (.app2 .add (.var "p") (.int 1))) (.int 0)

/-- A derived rule with the same expressions and only the necessary denominator condition. -/
def rubi1134r28OrderFree : CRule :=
  { rubi1134r28Nondeg with
    id := "integration.rubi_1_1_3_4_r28_order_free"
    conditions := [rubi1134r28Denominator]
    description := "Order-free generalization of RUBI 1.1.3.4 #28" }

/-- Every assignment satisfying the original variant also satisfies the generalized conditions. -/
theorem rubi1134r28OriginalConditions_imply_OrderFree (I : Interp K) (env : String → K)
    (h : ∀ c ∈ rubi1134r28Nondeg.conditions, c.Holds I env) :
    ∀ c ∈ rubi1134r28OrderFree.conditions, c.Holds I env := by
  intro c hc
  have hmem : c = rubi1134r28Denominator := by
    simpa [rubi1134r28OrderFree] using hc
  subst c
  exact h rubi1134r28Denominator (by simp [rubi1134r28Nondeg, rubi1134r28Denominator])

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

/-- The proof needs only the denominator condition; no ordering assumption is used. -/
theorem rubi1134r28_holds_of_denominator (I : Interp K) (cs : List Cond)
    (hmem : rubi1134r28Denominator ∈ cs) :
    AntiderivRecHolds I "x" cs rubi1134r28Nondeg.body
      rubi1134r28Nondeg.result rubi1134r28Nondeg.integrals := by
  intro env hc t hF
  have hd : env "a" * (env "b" ^ 2) * env "e" * env "n" * (env "p" + 1) ≠ 0 := by
    have h := hc rubi1134r28Denominator hmem
    simpa [rubi1134r28Denominator, Cond.Holds, Defined, eval, int_two] using h
  have he : env "e" ≠ 0 := by
    intro h
    apply hd
    rw [h]
    ring
  rcases hkm : I.toInt? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1134r28Nondeg, Defined, eval, hkm, int_two] at h
  rcases hkn : I.toInt? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1134r28Nondeg, Defined, eval, hkn, int_two] at h
  rcases hkp : I.toInt? (env "p") with _ | p
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1134r28Nondeg, Defined, eval, hkp, int_two] at h
  have hm : env "m" = (m : K) := (I.toInt?_eq _ _).1 hkm
  have hn : env "n" = (n : K) := (I.toInt?_eq _ _).1 hkn
  have hp : env "p" = (p : K) := (I.toInt?_eq _ _).1 hkp
  have hkm1 : I.toInt? (env "m" + 1) = some (m + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hkmn : I.toInt? (env "m" + env "n") = some (m + n) :=
    (I.toInt?_eq _ _).2 (by rw [hm, hn]; push_cast; ring)
  have hkp1 : I.toInt? (env "p" + 1) = some (p + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hd2 : env "a" * env "b" ^ 2 * env "n" * (env "p" + 1) ≠ 0 := by
    intro h
    apply hd
    linear_combination env "e" * h
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1134r28Nondeg.body →
      (m < 0 → w ≠ 0) ∧ (n < 0 → w ≠ 0) ∧
      (p < 0 → env "a" + env "b" * w ^ n ≠ 0) := by
    intro w h
    simp [rubi1134r28Nondeg, Defined, eval, hkm, hkn, hkp, int_two] at h
    tauto
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1134r28Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hm0, hn0, hp0⟩ := hD w hw
    simp [Defined, eval, hkm, hkn, hkp1, he, int_two]
    exact ⟨⟨hm0, hn0, fun h => hp0 (by omega)⟩, hn0⟩
  · filter_upwards [hF] with w hw
    obtain ⟨hm0, hn0, hp0⟩ := hD w hw
    simp [rubi1134r28Nondeg, Defined, eval, recEnv, hkm1, hkn, hkp1, int_neg_one, int_two, hd, he, hd2]
    exact ⟨fun h => hm0 (by omega), hn0, fun h => hp0 (by omega)⟩
  · simp only [rubi1134r28Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hE : ∀ w, eval I (recEnv env (rubi1134r28Nondeg.integrals.map (·.1)) Φ "x" w)
        rubi1134r28Nondeg.result =
      -(env "b" * env "c" - env "a" * env "d") ^ 2 * (env "e" * w) ^ (m + 1) *
        (env "a" + env "b" * w ^ n) ^ (p + 1) *
        (env "a" * env "b" ^ 2 * env "e" * env "n" * (env "p" + 1))⁻¹ +
        (env "a" * env "b" ^ 2 * env "n" * (env "p" + 1))⁻¹ * Φ "I1" w := by
      intro w
      simp [rubi1134r28Nondeg, eval, recEnv, hkm1, hkn, hkp1, int_neg_one, int_two, sub_eq_add_neg]
    have hEF : eval I (Function.update env "x" t) rubi1134r28Nondeg.body =
      (env "e" * t) ^ m * (env "a" + env "b" * t ^ n) ^ p *
        (env "c" + env "d" * t ^ n) ^ 2 := by
      simp [rubi1134r28Nondeg, eval, hkm, hkn, hkp, int_two]
    rw [hEF, show (fun w => eval I (recEnv env (rubi1134r28Nondeg.integrals.map (·.1)) Φ "x" w)
      rubi1134r28Nondeg.result) = fun w =>
      -(env "b" * env "c" - env "a" * env "d") ^ 2 * (env "e" * w) ^ (m + 1) *
        (env "a" + env "b" * w ^ n) ^ (p + 1) *
        (env "a" * env "b" ^ 2 * env "e" * env "n" * (env "p" + 1))⁻¹ +
        (env "a" * env "b" ^ 2 * env "n" * (env "p" + 1))⁻¹ * Φ "I1" w from funext hE]
    have hI : HasDerivAt (Φ "I1")
      ((env "e" * t) ^ m * (env "a" + env "b" * t ^ n) ^ (p + 1) *
        ((env "b" * env "c" - env "a" * env "d") ^ 2 * (env "m" + 1) +
          env "b" ^ 2 * env "c" ^ 2 * env "n" * (env "p" + 1) +
          env "a" * env "b" * env "d" ^ 2 * env "n" * (env "p" + 1) * t ^ n)) t := by
      simpa [rubi1134r28Nondeg, eval, hkm, hkn, hkp1, int_two, sub_eq_add_neg] using hΦ
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
    have he1 : env "e" * t ≠ 0 ∨ 0 ≤ m + 1 := he0.imp_right (by omega)
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
    have hU := ((hasDerivAt_zpow n t hx).const_mul (env "b")).const_add (env "a")
    refine (((((HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ he1)
      ((hasDerivAt_id' t).const_mul (env "e"))).const_mul (-(env "b" * env "c" - env "a" * env "d") ^ 2)).mul
      (HasDerivAt.comp t (hasDerivAt_zpow (p + 1) _ hu1) hU)).mul_const _).add
      (hI.const_mul (env "a" * env "b" ^ 2 * env "n" * (env "p" + 1))⁻¹)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    rw [zsucc _ _ he0, zsucc _ _ hu]
    generalize (env "e" * t) ^ m = E
    generalize (env "a" + env "b" * t ^ n) ^ p = U
    generalize t ^ (n - 1) = R at hkey ⊢
    generalize t ^ n = T at hkey ⊢
    rw [hn, hp] at hd hd2 ⊢
    rw [hm]
    push_cast at hd hd2 ⊢
    have hi : (env "a" * env "b" ^ 2 * env "e" * (n : K) * ((p : K) + 1))⁻¹ =
        (env "a" * env "b" ^ 2 * (n : K) * ((p : K) + 1))⁻¹ * (env "e")⁻¹ := by
      rw [← mul_inv]
      congr 1
      ring
    rw [hi]
    have ha : env "a" ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hd2))
    have hb : env "b" ≠ 0 := by
      have h := right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hd2))
      exact fun hb => h (by rw [hb]; simp)
    have hn0 : (n : K) ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hd2)
    have hp0 : (p : K) + 1 ≠ 0 := right_ne_zero_of_mul hd2
    field_simp [ha, hb, hn0, hp0, he]
    linear_combination
      (-(env "b" * env "c" - env "a" * env "d") ^ 2 * E * U * env "b" * (p + 1)) * hkey

theorem rubi1134r28Nondeg_holds (I : Interp K) :
    AntiderivRecHolds I "x" rubi1134r28Nondeg.conditions rubi1134r28Nondeg.body
      rubi1134r28Nondeg.result rubi1134r28Nondeg.integrals :=
  rubi1134r28_holds_of_denominator I _ (by simp [rubi1134r28Nondeg, rubi1134r28Denominator])

theorem rubi1134r28OrderFree_real : rubi1134r28OrderFree.Holds .real :=
  rubi1134r28_holds_of_denominator Interp.real _ (by simp [rubi1134r28OrderFree])

theorem rubi1134r28OrderFree_complex : rubi1134r28OrderFree.Holds .complex :=
  rubi1134r28_holds_of_denominator Interp.complex _ (by simp [rubi1134r28OrderFree])

theorem rubi1134r28Nondeg_real : rubi1134r28Nondeg.Holds .real :=
  rubi1134r28Nondeg_holds Interp.real

theorem rubi1134r28Nondeg_complex : rubi1134r28Nondeg.Holds .complex :=
  rubi1134r28Nondeg_holds Interp.complex

end

end OSR.IntegrationRec205
