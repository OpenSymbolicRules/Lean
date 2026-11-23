import OSR.IntegrationNum1

/-!
# Integration (RUBI): strengthened rule 1.1.3.4 #27

The polynomial identity relates the differentiated boundary term to the
residual integrand and establishes the rule over both supported domains.
-/

namespace OSR.IntegrationRec204

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

/-- The polynomial identity underlying RUBI 1.1.3.4 #27. -/
theorem rubi1134r27_coefficient {K : Type} [CommRing K]
    (a b c d m n p x : K) :
    c ^ 2 * ((m + 1) * (a + b * x) + b * n * (p + 1) * x) -
      x * (b * c ^ 2 * n * (p + 1) + c * (b * c - 2 * a * d) * (m + 1) -
        a * (m + 1) * d ^ 2 * x) = a * (m + 1) * (c + d * x) ^ 2 := by
  ring

section
variable {K : Type} [NontriviallyNormedField K]

/-- The denominator condition shared by the strengthened and derived rules. -/
def rubi1134r27Denominator : Cond :=
  .ne (.app2 .mul (.app2 .mul (.var "a") (.var "e"))
    (.app2 .add (.var "m") (.int 1))) (.int 0)

/-- A derived rule with the same expressions and matching constraints. -/
def rubi1134r27OrderFree : CRule :=
  { rubi1134r27Nondeg with
    id := "integration.rubi_1_1_3_4_r27_order_free"
    conditions := [rubi1134r27Denominator]
    description := "Order-free generalization of RUBI 1.1.3.4 #27" }

/-- The strengthened rule's conditions imply the generalized conditions. -/
theorem rubi1134r27OriginalConditions_imply_OrderFree (I : Interp K) (env : String → K)
    (h : ∀ c ∈ rubi1134r27Nondeg.conditions, c.Holds I env) :
    ∀ c ∈ rubi1134r27OrderFree.conditions, c.Holds I env := by
  intro c hc
  have hmem : c = rubi1134r27Denominator := by
    simpa [rubi1134r27OrderFree] using hc
  subst c
  exact h rubi1134r27Denominator (by simp [rubi1134r27Nondeg, rubi1134r27Denominator])

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

/-- RUBI 1.1.3.4 #27 with nonzero denominator. -/
theorem rubi1134r27_holds_of_denominator (I : Interp K) (cs : List Cond)
    (hmem : rubi1134r27Denominator ∈ cs) :
    AntiderivRecHolds I "x" cs rubi1134r27Nondeg.body
      rubi1134r27Nondeg.result rubi1134r27Nondeg.integrals := by
  intro env hc t hF
  have hd : env "a" * env "e" * (env "m" + 1) ≠ 0 := by
    have h := hc rubi1134r27Denominator hmem
    simpa [rubi1134r27Denominator, Cond.Holds, Defined, eval] using h
  have he : env "e" ≠ 0 := by
    intro h
    apply hd
    rw [h]
    ring
  rcases hkm : I.toInt? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1134r27Nondeg, Defined, eval, hkm, int_two] at h
  rcases hkn : I.toInt? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1134r27Nondeg, Defined, eval, hkn, int_two] at h
  rcases hkp : I.toInt? (env "p") with _ | p
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1134r27Nondeg, Defined, eval, hkp, int_two] at h
  have hm : env "m" = (m : K) := (I.toInt?_eq _ _).1 hkm
  have hn : env "n" = (n : K) := (I.toInt?_eq _ _).1 hkn
  have hp : env "p" = (p : K) := (I.toInt?_eq _ _).1 hkp
  have hkm1 : I.toInt? (env "m" + 1) = some (m + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hkmn : I.toInt? (env "m" + env "n") = some (m + n) :=
    (I.toInt?_eq _ _).2 (by rw [hm, hn]; push_cast; ring)
  have hkp1 : I.toInt? (env "p" + 1) = some (p + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hen : env "e" ^ n ≠ 0 := zpow_ne_zero _ he
  have ha : env "a" ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hd)
  have hmne : env "m" + 1 ≠ 0 := right_ne_zero_of_mul hd
  have hd2 : env "a" * env "e" ^ n * (env "m" + 1) ≠ 0 := mul_ne_zero (mul_ne_zero ha hen) hmne
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1134r27Nondeg.body →
      (m < 0 → w ≠ 0) ∧ (n < 0 → w ≠ 0) ∧
      (p < 0 → env "a" + env "b" * w ^ n ≠ 0) := by
    intro w h
    simp [rubi1134r27Nondeg, Defined, eval, hkm, hkn, hkp, int_two] at h
    tauto
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1134r27Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hm0, hn0, hp0⟩ := hD w hw
    simp [Defined, eval, hkmn, hkn, hkp, he, int_two]
    exact ⟨⟨fun h => by by_cases hn : n < 0 <;> first | exact hn0 hn | exact hm0 (by omega),
      hn0, hp0⟩, hn0⟩
  · filter_upwards [hF] with w hw
    obtain ⟨hm0, hn0, hp0⟩ := hD w hw
    simp [rubi1134r27Nondeg, Defined, eval, recEnv, hkm1, hkn, hkp1, int_neg_one, int_two, hd, he, hd2]
    exact ⟨fun h => hm0 (by omega), hn0, fun h => hp0 (by omega)⟩
  · simp only [rubi1134r27Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hE : ∀ w, eval I (recEnv env (rubi1134r27Nondeg.integrals.map (·.1)) Φ "x" w)
        rubi1134r27Nondeg.result =
      env "c" ^ 2 * (env "e" * w) ^ (m + 1) * (env "a" + env "b" * w ^ n) ^ (p + 1) *
        (env "a" * env "e" * (env "m" + 1))⁻¹ -
        (env "a" * env "e" ^ n * (env "m" + 1))⁻¹ * Φ "I1" w := by
      intro w
      simp [rubi1134r27Nondeg, eval, recEnv, hkm1, hkn, hkp1, int_neg_one, int_two, sub_eq_add_neg]
    have hEF : eval I (Function.update env "x" t) rubi1134r27Nondeg.body =
      (env "e" * t) ^ m * (env "a" + env "b" * t ^ n) ^ p *
        (env "c" + env "d" * t ^ n) ^ 2 := by
      simp [rubi1134r27Nondeg, eval, hkm, hkn, hkp, int_two]
    rw [hEF, show (fun w => eval I (recEnv env (rubi1134r27Nondeg.integrals.map (·.1)) Φ "x" w)
      rubi1134r27Nondeg.result) = fun w =>
      env "c" ^ 2 * (env "e" * w) ^ (m + 1) * (env "a" + env "b" * w ^ n) ^ (p + 1) *
        (env "a" * env "e" * (env "m" + 1))⁻¹ -
        (env "a" * env "e" ^ n * (env "m" + 1))⁻¹ * Φ "I1" w from funext hE]
    have hI : HasDerivAt (Φ "I1")
      ((env "e" * t) ^ (m + n) * (env "a" + env "b" * t ^ n) ^ p *
        (env "b" * env "c" ^ 2 * env "n" * (env "p" + 1) +
          env "c" * (env "b" * env "c" - 2 * env "a" * env "d") * (env "m" + 1) -
          env "a" * (env "m" + 1) * env "d" ^ 2 * t ^ n)) t := by
      simpa [rubi1134r27Nondeg, eval, hkmn, hkn, hkp, int_two, sub_eq_add_neg] using hΦ
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
    have hscale : (env "e" * t) ^ (m + n) * (env "e" ^ n)⁻¹ =
        (env "e" * t) ^ m * t ^ n := by
      rw [mul_zpow, mul_zpow, zpow_add₀ he]
      by_cases ht0 : t = 0
      · have hm0 : 0 ≤ m := by by_contra h; exact ht.1 (by omega) ht0
        have hn0 : 0 ≤ n := by by_contra h; exact ht.2.1 (by omega) ht0
        lift m to ℕ using hm0
        lift n to ℕ using hn0
        rw [← Int.natCast_add, zpow_natCast, zpow_natCast, zpow_natCast, pow_add]
        field_simp
        simp only [zpow_natCast]
      · rw [zpow_add₀ ht0]
        field_simp
    have hI' : HasDerivAt (fun w => (env "a" * env "e" ^ n * (env "m" + 1))⁻¹ * Φ "I1" w)
        (((env "a" * (env "m" + 1))⁻¹) * ((env "e" * t) ^ m * t ^ n) *
          (env "a" + env "b" * t ^ n) ^ p *
          (env "b" * env "c" ^ 2 * env "n" * (env "p" + 1) +
            env "c" * (env "b" * env "c" - 2 * env "a" * env "d") * (env "m" + 1) -
            env "a" * (env "m" + 1) * env "d" ^ 2 * t ^ n)) t := by
      convert hI.const_mul (env "a" * env "e" ^ n * (env "m" + 1))⁻¹ using 1
      rw [← hscale]
      rw [mul_inv, mul_inv, mul_inv]
      ring
    have hU := ((hasDerivAt_zpow n t hx).const_mul (env "b")).const_add (env "a")
    refine (((((HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ he1)
      ((hasDerivAt_id' t).const_mul (env "e"))).const_mul (env "c" ^ 2)).mul
      (HasDerivAt.comp t (hasDerivAt_zpow (p + 1) _ hu1) hU)).mul_const _).sub
      hI').congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    rw [zsucc _ _ he0, zsucc _ _ hu]
    generalize (env "e" * t) ^ m = E
    generalize (env "a" + env "b" * t ^ n) ^ p = U
    generalize t ^ (n - 1) = R at hkey ⊢
    generalize t ^ n = T at hkey ⊢
    rw [hm] at hd hmne ⊢
    rw [hn, hp]
    push_cast at hd ⊢
    field_simp [ha, he, hmne]
    linear_combination
      (env "c" ^ 2 * E * U * env "b" * (p + 1)) * hkey

theorem rubi1134r27Nondeg_holds (I : Interp K) :
    AntiderivRecHolds I "x" rubi1134r27Nondeg.conditions rubi1134r27Nondeg.body
      rubi1134r27Nondeg.result rubi1134r27Nondeg.integrals :=
  rubi1134r27_holds_of_denominator I _ (by simp [rubi1134r27Nondeg, rubi1134r27Denominator])

theorem rubi1134r27OrderFree_real : rubi1134r27OrderFree.Holds .real :=
  rubi1134r27_holds_of_denominator Interp.real _ (by simp [rubi1134r27OrderFree])

theorem rubi1134r27OrderFree_complex : rubi1134r27OrderFree.Holds .complex :=
  rubi1134r27_holds_of_denominator Interp.complex _ (by simp [rubi1134r27OrderFree])

theorem rubi1134r27Nondeg_real : rubi1134r27Nondeg.Holds .real :=
  rubi1134r27Nondeg_holds Interp.real

theorem rubi1134r27Nondeg_complex : rubi1134r27Nondeg.Holds .complex :=
  rubi1134r27Nondeg_holds Interp.complex

end

end OSR.IntegrationRec204
