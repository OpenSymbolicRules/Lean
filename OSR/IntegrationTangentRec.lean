import OSR.IntegrationNum1

open OSR OSR.Calculus Filter Topology
namespace OSR.IntegrationTangentRec

section
variable {𝕜 : Type} [NontriviallyNormedField 𝕜]
private theorem htwo (I : Interp 𝕜) : I.toInt? (2 : 𝕜) = some 2 :=
  (I.toInt?_eq _ _).2 (by simp)
private theorem hneg (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

theorem tanSquare_holds (I : Interp 𝕜)
    (htan : ∀ u, I.tanDefined u → HasDerivAt I.tan (1 + I.tan u ^ 2) u) :
    AntiderivRecHolds I "x" IntegrationNum1.rubi4311r5Nondeg.conditions
      IntegrationNum1.rubi4311r5Nondeg.body IntegrationNum1.rubi4311r5Nondeg.result IntegrationNum1.rubi4311r5Nondeg.integrals := by
  intro env hcond t hF
  have hd : env "d" ≠ 0 := by
    have h := hcond (.ne (.var "d") (.int 0)) (by simp [IntegrationNum1.rubi4311r5Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have htanDef : ∀ᶠ w in 𝓝 t, I.tanDefined (env "c" + env "d"*w) := by
    filter_upwards [hF] with w hw
    simpa [IntegrationNum1.rubi4311r5Nondeg, Defined, eval, Function.update, htwo] using hw
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [IntegrationNum1.rubi4311r5Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    filter_upwards [htanDef] with w hw
    simpa [Defined, eval, Function.update] using hw
  · intro Φ hΦ
    simp only [IntegrationNum1.rubi4311r5Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards [htanDef] with w hw
      simp [IntegrationNum1.rubi4311r5Nondeg, Defined, eval, recEnv, htwo, hneg, hd, hw]
    · have hU : HasDerivAt (fun w : 𝕜 => env "c" + env "d"*w) (env "d") t := by
        simpa using (((hasDerivAt_id' t).const_mul (env "d")).const_add (env "c"))
      have hT := (htan _ htanDef.self_of_nhds).comp t hU
      have hfun : (fun w => eval I (recEnv env (IntegrationNum1.rubi4311r5Nondeg.integrals.map (·.1)) Φ "x" w) IntegrationNum1.rubi4311r5Nondeg.result) =
        (fun w : 𝕜 => (env "a"^2-env "b"^2)*w + env "b"^2 * I.tan (env "c"+env "d"*w) * (env "d")⁻¹ +
          (2*env "a"*env "b")*Φ "I1" w) := by
        funext w
        simp [IntegrationNum1.rubi4311r5Nondeg, eval, recEnv, htwo, hneg, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
        ring
      rw [hfun]
      simp [eval, Function.update] at hΦ
      refine (((hasDerivAt_id' t).const_mul _).add ((hT.const_mul _).mul_const _)).add (hΦ.const_mul _) |>.congr_deriv ?_
      simp [IntegrationNum1.rubi4311r5Nondeg, eval, htwo, Function.update]
      generalize I.tan (env "c"+env "d"*t) = T
      field_simp [hd]
      ring

private theorem zpow_succ_nonneg (A : 𝕜) (k : ℤ) (h : 0 ≤ k) : A ^ (k + 1) = A ^ k * A := by
  lift k to ℕ using h
  rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast, pow_succ]

variable [CharZero 𝕜]

theorem tanPower_holds (I : Interp 𝕜)
    (htan : ∀ u, I.tanDefined u → HasDerivAt I.tan (1 + I.tan u ^ 2) u)
    (horder : ∀ k : ℤ, I.lt 1 (k : 𝕜) → 1 < k) :
    AntiderivRecHolds I "x" IntegrationNum1.rubi4311r1Nondeg.conditions
      IntegrationNum1.rubi4311r1Nondeg.body IntegrationNum1.rubi4311r1Nondeg.result IntegrationNum1.rubi4311r1Nondeg.integrals := by
  intro env hcond t hF
  have hN : env "d" * (env "n" + -1 * 1) ≠ 0 := by
    have h := hcond (.ne (.app2 .mul (.var "d") (.app2 .add (.var "n")
      (.app2 .mul (.int (-1)) (.int 1)))) (.int 0)) (by simp [IntegrationNum1.rubi4311r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hd : env "d" ≠ 0 := (mul_ne_zero_iff.mp hN).1
  have hn1 : env "n" + -1 * 1 ≠ 0 := (mul_ne_zero_iff.mp hN).2
  have hn1' : env "n" + -1 ≠ 0 := by simpa using hn1
  have hord : I.lt 1 (env "n") := by
    have h := hcond (.gt (.var "n") (.int 1)) (by simp [IntegrationNum1.rubi4311r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hk : I.toInt? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [IntegrationNum1.rubi4311r1Nondeg, Defined, eval, Function.update, hk] at h
  have hn : env "n" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk
  have hk2 : 2 ≤ k := by
    rw [hn] at hord
    have h := horder k hord
    omega
  have hk1 : I.toInt? (env "n" + -1 * 1) = some (k - 1) :=
    (I.toInt?_eq _ _).2 (by rw [hn]; push_cast; ring)
  have hkm2 : I.toInt? (env "n" + -1 * 2) = some (k - 2) :=
    (I.toInt?_eq _ _).2 (by rw [hn]; push_cast; ring)
  have hk1'' : I.toInt? (env "n" + -1) = some (k - 1) := by simpa using hk1
  have hk1' : I.toInt? (-1 + env "n") = some (k - 1) := by simpa [add_comm] using hk1
  have hkm2' : I.toInt? (env "n" + -2) = some (k - 2) := by simpa using hkm2
  have htanDef : ∀ᶠ w in 𝓝 t, I.tanDefined (env "c" + env "d"*w) := by
    filter_upwards [hF] with w hw
    simp [IntegrationNum1.rubi4311r1Nondeg, Defined, eval, Function.update, hk] at hw
    exact hw.1
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [IntegrationNum1.rubi4311r1Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    filter_upwards [htanDef] with w hw
    simp [Defined, eval, Function.update, hkm2', hw]
    omega
  · intro Φ hΦ
    simp only [IntegrationNum1.rubi4311r1Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards [htanDef] with w hw
      simp [IntegrationNum1.rubi4311r1Nondeg, Defined, eval, recEnv, hneg, hw]
      simp [hk1'', htwo, hd, hn1', show ¬ k - 1 < 0 by omega]
    · have hU : HasDerivAt (fun w : 𝕜 => env "c" + env "d"*w) (env "d") t := by
        simpa using (((hasDerivAt_id' t).const_mul (env "d")).const_add (env "c"))
      have hT := (htan _ htanDef.self_of_nhds).comp t hU
      have hY := hT.const_mul (env "b")
      have hP := (hasDerivAt_zpow (k-1) (env "b" * I.tan (env "c"+env "d"*t)) (Or.inr (by omega))).comp t hY
      have hfun : (fun w => eval I (recEnv env (IntegrationNum1.rubi4311r1Nondeg.integrals.map (·.1)) Φ "x" w) IntegrationNum1.rubi4311r1Nondeg.result) =
        (fun w : 𝕜 => env "b" * (env "b"*I.tan (env "c"+env "d"*w))^(k-1) *
          (env "d"*(env "n"-1))⁻¹ - env "b"^2 * Φ "I1" w) := by
        funext w
        simp [IntegrationNum1.rubi4311r1Nondeg, eval, recEnv, hneg, htwo, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
        simp only [hk1'']
        ring
      rw [hfun]
      simp [eval, Function.update, hkm2'] at hΦ
      refine (((hP.const_mul _).mul_const _).sub (hΦ.const_mul _)).congr_deriv ?_
      simp [IntegrationNum1.rubi4311r1Nondeg, eval, Function.update, hk]
      have hpow1 := zpow_succ_nonneg (env "b"*I.tan (env "c"+env "d"*t)) (k-1) (by omega)
      have hpow2 := zpow_succ_nonneg (env "b"*I.tan (env "c"+env "d"*t)) (k-2) (by omega)
      rw [show k - 1 + 1 = k by omega] at hpow1
      rw [show k - 2 + 1 = k - 1 by omega] at hpow2
      simp_rw [hpow1, hpow2]
      simp only [sub_sub]
      rw [hn]
      have hkne : (k : 𝕜) - 1 ≠ 0 := by simpa [hn, sub_eq_add_neg] using hn1
      generalize I.tan (env "c"+env "d"*t) = T
      generalize (env "b"*T)^(-2+k) = P
      field_simp [hd, hkne]
      ring

theorem tanAffinePower_holds (I : Interp 𝕜)
    (htan : ∀ u, I.tanDefined u → HasDerivAt I.tan (1 + I.tan u ^ 2) u)
    (horder : ∀ k : ℤ, I.lt 1 (k : 𝕜) → 1 < k) :
    AntiderivRecHolds I "x" IntegrationNum1.rubi4311r10Nondeg.conditions
      IntegrationNum1.rubi4311r10Nondeg.body IntegrationNum1.rubi4311r10Nondeg.result IntegrationNum1.rubi4311r10Nondeg.integrals := by
  intro env hcond t hF
  have hN : env "d" * (env "n" + -1 * 1) ≠ 0 := by
    have h := hcond (.ne (.app2 .mul (.var "d") (.app2 .add (.var "n")
      (.app2 .mul (.int (-1)) (.int 1)))) (.int 0)) (by simp [IntegrationNum1.rubi4311r10Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hd : env "d" ≠ 0 := (mul_ne_zero_iff.mp hN).1
  have hn1 : env "n" + -1 * 1 ≠ 0 := (mul_ne_zero_iff.mp hN).2
  have hn1' : env "n" + -1 ≠ 0 := by simpa using hn1
  have hord : I.lt 1 (env "n") := by
    have h := hcond (.gt (.var "n") (.int 1)) (by simp [IntegrationNum1.rubi4311r10Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hk : I.toInt? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [IntegrationNum1.rubi4311r10Nondeg, Defined, eval, Function.update, hk] at h
  have hn : env "n" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk
  have hk2 : 2 ≤ k := by
    rw [hn] at hord
    have h := horder k hord
    omega
  have hk1 : I.toInt? (env "n" + -1 * 1) = some (k - 1) :=
    (I.toInt?_eq _ _).2 (by rw [hn]; push_cast; ring)
  have hkm2 : I.toInt? (env "n" + -1 * 2) = some (k - 2) :=
    (I.toInt?_eq _ _).2 (by rw [hn]; push_cast; ring)
  have hk1'' : I.toInt? (env "n" + -1) = some (k - 1) := by simpa using hk1
  have hk1' : I.toInt? (-1 + env "n") = some (k - 1) := by simpa [add_comm] using hk1
  have hkm2' : I.toInt? (env "n" + -2) = some (k - 2) := by simpa using hkm2
  have htanDef : ∀ᶠ w in 𝓝 t, I.tanDefined (env "c" + env "d"*w) := by
    filter_upwards [hF] with w hw
    simp [IntegrationNum1.rubi4311r10Nondeg, Defined, eval, Function.update, hk] at hw
    exact hw.1
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [IntegrationNum1.rubi4311r10Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    filter_upwards [htanDef] with w hw
    simp [Defined, eval, Function.update, hkm2', htwo, hw]
    omega
  · intro Φ hΦ
    simp only [IntegrationNum1.rubi4311r10Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards [htanDef] with w hw
      simp [IntegrationNum1.rubi4311r10Nondeg, Defined, eval, recEnv, hneg, hw]
      simp [hk1'', hd, hn1', show ¬ k - 1 < 0 by omega]
    · have hU : HasDerivAt (fun w : 𝕜 => env "c" + env "d"*w) (env "d") t := by
        simpa using (((hasDerivAt_id' t).const_mul (env "d")).const_add (env "c"))
      have hT := (htan _ htanDef.self_of_nhds).comp t hU
      have hY := (hT.const_mul (env "b")).const_add (env "a")
      have hP := (hasDerivAt_zpow (k-1) (env "a" + env "b" * I.tan (env "c"+env "d"*t)) (Or.inr (by omega))).comp t hY
      have hfun : (fun w => eval I (recEnv env (IntegrationNum1.rubi4311r10Nondeg.integrals.map (·.1)) Φ "x" w) IntegrationNum1.rubi4311r10Nondeg.result) =
        (fun w : 𝕜 => env "b" * (env "a"+env "b"*I.tan (env "c"+env "d"*w))^(k-1) *
          (env "d"*(env "n"-1))⁻¹ + Φ "I1" w) := by
        funext w
        simp [IntegrationNum1.rubi4311r10Nondeg, eval, recEnv, hneg, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
        simp only [hk1'']
        ring
      rw [hfun]
      simp [eval, Function.update, hkm2', htwo] at hΦ
      refine (((hP.const_mul _).mul_const _).add hΦ).congr_deriv ?_
      simp [IntegrationNum1.rubi4311r10Nondeg, eval, Function.update, hk]
      have hpow1 := zpow_succ_nonneg (env "a"+env "b"*I.tan (env "c"+env "d"*t)) (k-1) (by omega)
      have hpow2 := zpow_succ_nonneg (env "a"+env "b"*I.tan (env "c"+env "d"*t)) (k-2) (by omega)
      rw [show k - 1 + 1 = k by omega] at hpow1
      rw [show k - 2 + 1 = k - 1 by omega] at hpow2
      simp_rw [hpow1, hpow2]
      simp only [sub_sub]
      rw [hn]
      have hkne : (k : 𝕜) - 1 ≠ 0 := by simpa [hn, sub_eq_add_neg] using hn1
      generalize I.tan (env "c"+env "d"*t) = T
      generalize (env "a"+env "b"*T)^(-2+k) = P
      field_simp [hd, hkne]
      ring

theorem tanDegeneratePower_holds (I : Interp 𝕜)
    (htan : ∀ u, I.tanDefined u → HasDerivAt I.tan (1 + I.tan u ^ 2) u)
    (horder : ∀ k : ℤ, I.lt 1 (k : 𝕜) → 1 < k) :
    AntiderivRecHolds I "x" IntegrationNum1.rubi4311r6Nondeg.conditions
      IntegrationNum1.rubi4311r6Nondeg.body IntegrationNum1.rubi4311r6Nondeg.result IntegrationNum1.rubi4311r6Nondeg.integrals := by
  intro env hcond t hF
  have hab : env "a" ^ 2 + env "b" ^ 2 = 0 := by
    have h := hcond (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0)) (by simp [IntegrationNum1.rubi4311r6Nondeg])
    simpa [Cond.Holds, Defined, eval, htwo] using h
  have hN : env "d" * (env "n" + -1 * 1) ≠ 0 := by
    have h := hcond (.ne (.app2 .mul (.var "d") (.app2 .add (.var "n")
      (.app2 .mul (.int (-1)) (.int 1)))) (.int 0)) (by simp [IntegrationNum1.rubi4311r6Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hd : env "d" ≠ 0 := (mul_ne_zero_iff.mp hN).1
  have hn1 : env "n" + -1 * 1 ≠ 0 := (mul_ne_zero_iff.mp hN).2
  have hn1' : env "n" + -1 ≠ 0 := by simpa using hn1
  have hord : I.lt 1 (env "n") := by
    have h := hcond (.gt (.var "n") (.int 1)) (by simp [IntegrationNum1.rubi4311r6Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hk : I.toInt? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [IntegrationNum1.rubi4311r6Nondeg, Defined, eval, Function.update, hk] at h
  have hn : env "n" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk
  have hk2 : 2 ≤ k := by
    rw [hn] at hord
    have h := horder k hord
    omega
  have hk1 : I.toInt? (env "n" + -1 * 1) = some (k - 1) :=
    (I.toInt?_eq _ _).2 (by rw [hn]; push_cast; ring)
  have hkm2 : I.toInt? (env "n" + -1 * 2) = some (k - 2) :=
    (I.toInt?_eq _ _).2 (by rw [hn]; push_cast; ring)
  have hk1'' : I.toInt? (env "n" + -1) = some (k - 1) := by simpa using hk1
  have hk1' : I.toInt? (-1 + env "n") = some (k - 1) := by simpa [add_comm] using hk1
  have hkm2' : I.toInt? (env "n" + -2) = some (k - 2) := by simpa using hkm2
  have htanDef : ∀ᶠ w in 𝓝 t, I.tanDefined (env "c" + env "d"*w) := by
    filter_upwards [hF] with w hw
    simp [IntegrationNum1.rubi4311r6Nondeg, Defined, eval, Function.update, hk] at hw
    exact hw.1
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [IntegrationNum1.rubi4311r6Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    filter_upwards [htanDef] with w hw
    simp [Defined, eval, Function.update, hk1'', hw]
    omega
  · intro Φ hΦ
    simp only [IntegrationNum1.rubi4311r6Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards [htanDef] with w hw
      simp [IntegrationNum1.rubi4311r6Nondeg, Defined, eval, recEnv, hneg, hw]
      simp [hk1'', hd, hn1', show ¬ k - 1 < 0 by omega]
    · have hU : HasDerivAt (fun w : 𝕜 => env "c" + env "d"*w) (env "d") t := by
        simpa using (((hasDerivAt_id' t).const_mul (env "d")).const_add (env "c"))
      have hT := (htan _ htanDef.self_of_nhds).comp t hU
      have hY := (hT.const_mul (env "b")).const_add (env "a")
      have hP := (hasDerivAt_zpow (k-1) (env "a" + env "b" * I.tan (env "c"+env "d"*t)) (Or.inr (by omega))).comp t hY
      have hfun : (fun w => eval I (recEnv env (IntegrationNum1.rubi4311r6Nondeg.integrals.map (·.1)) Φ "x" w) IntegrationNum1.rubi4311r6Nondeg.result) =
        (fun w : 𝕜 => env "b" * (env "a"+env "b"*I.tan (env "c"+env "d"*w))^(k-1) *
          (env "d"*(env "n"-1))⁻¹ + (2*env "a") * Φ "I1" w) := by
        funext w
        simp [IntegrationNum1.rubi4311r6Nondeg, eval, recEnv, hneg, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
        simp only [hk1'']
        ring
      rw [hfun]
      simp [eval, Function.update, hk1''] at hΦ
      refine (((hP.const_mul _).mul_const _).add (hΦ.const_mul _)).congr_deriv ?_
      simp [IntegrationNum1.rubi4311r6Nondeg, eval, Function.update, hk]
      have hpow1 := zpow_succ_nonneg (env "a"+env "b"*I.tan (env "c"+env "d"*t)) (k-1) (by omega)
      have hpow2 := zpow_succ_nonneg (env "a"+env "b"*I.tan (env "c"+env "d"*t)) (k-2) (by omega)
      rw [show k - 1 + 1 = k by omega] at hpow1
      rw [show k - 2 + 1 = k - 1 by omega] at hpow2
      simp_rw [hpow1, hpow2]
      simp only [sub_sub]
      rw [hn]
      have hkne : (k : 𝕜) - 1 ≠ 0 := by simpa [hn, sub_eq_add_neg] using hn1
      generalize I.tan (env "c"+env "d"*t) = T
      simp only [show k - (1 + 1) = k - 2 by omega]
      generalize (env "a"+env "b"*T)^(k-2) = P
      field_simp [hd, hkne]
      linear_combination P * hab

omit [CharZero 𝕜] in
theorem tanNegative_holds (I : Interp 𝕜)
    (htan : ∀ u, I.tanDefined u → HasDerivAt I.tan (1 + I.tan u ^ 2) u)
    (horder : ∀ k : ℤ, I.lt (k : 𝕜) (-1) → k < -1) :
    AntiderivRecHolds I "x" IntegrationNum1.rubi4311r11Nondeg.conditions
      IntegrationNum1.rubi4311r11Nondeg.body IntegrationNum1.rubi4311r11Nondeg.result IntegrationNum1.rubi4311r11Nondeg.integrals := by
  intro env hcond t hF
  have hN : env "d" * (env "n" + 1) * (env "a"^2 + env "b"^2) ≠ 0 := by
    have h := hcond (.ne (.app2 .mul (.app2 .mul (.var "d") (.app2 .add (.var "n") (.int 1)))
      (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [IntegrationNum1.rubi4311r11Nondeg])
    simpa [Cond.Holds, Defined, eval, htwo] using h
  have hd : env "d" ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hN).1).1
  have hn1 : env "n" + 1 ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hN).1).2
  have hab : env "a"^2 + env "b"^2 ≠ 0 := (mul_ne_zero_iff.mp hN).2
  have hord : I.lt (env "n") (-1) := by
    have h := hcond (.gt (.int (-1)) (.var "n")) (by simp [IntegrationNum1.rubi4311r11Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hk : I.toInt? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [IntegrationNum1.rubi4311r11Nondeg, Defined, eval, Function.update, hk] at h
  have hn : env "n" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk
  have hkneg : k < 0 := by rw [hn] at hord; have h := horder k hord; omega
  have hk1 : I.toInt? (env "n" + 1) = some (k + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hn]; push_cast; ring)
  have hbase : ∀ᶠ w in 𝓝 t, I.tanDefined (env "c" + env "d"*w) ∧
      env "a" + env "b" * I.tan (env "c"+env "d"*w) ≠ 0 := by
    filter_upwards [hF] with w hw
    simp [IntegrationNum1.rubi4311r11Nondeg, Defined, eval, Function.update, hk] at hw
    exact ⟨hw.1, hw.2 hkneg⟩
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [IntegrationNum1.rubi4311r11Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    filter_upwards [hbase] with w hw
    simp [Defined, eval, Function.update, hk1, hw.1, hw.2]
  · intro Φ hΦ
    simp only [IntegrationNum1.rubi4311r11Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards [hbase] with w hw
      simp [IntegrationNum1.rubi4311r11Nondeg, Defined, eval, recEnv, hneg, htwo, hk1, hN, hab, hw.1, hw.2]
    · have hz := hbase.self_of_nhds.2
      have hU : HasDerivAt (fun w : 𝕜 => env "c" + env "d"*w) (env "d") t := by
        simpa using (((hasDerivAt_id' t).const_mul (env "d")).const_add (env "c"))
      have hT := (htan _ hbase.self_of_nhds.1).comp t hU
      have hY := (hT.const_mul (env "b")).const_add (env "a")
      have hP := (hasDerivAt_zpow (k+1) (env "a" + env "b" * I.tan (env "c"+env "d"*t)) (Or.inl hz)).comp t hY
      have hfun : (fun w => eval I (recEnv env (IntegrationNum1.rubi4311r11Nondeg.integrals.map (·.1)) Φ "x" w) IntegrationNum1.rubi4311r11Nondeg.result) =
        (fun w : 𝕜 => env "b" * (env "a"+env "b"*I.tan (env "c"+env "d"*w))^(k+1) *
          (env "d"*(env "n"+1)*(env "a"^2+env "b"^2))⁻¹ + (env "a"^2+env "b"^2)⁻¹ * Φ "I1" w) := by
        funext w
        simp [IntegrationNum1.rubi4311r11Nondeg, eval, recEnv, hneg, htwo, hk1, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      rw [hfun]
      simp [eval, Function.update, hk1] at hΦ
      refine (((hP.const_mul _).mul_const _).add (hΦ.const_mul _)).congr_deriv ?_
      simp [IntegrationNum1.rubi4311r11Nondeg, eval, Function.update, hk]
      have hpow := zpow_add_one₀ hz k
      simp_rw [hpow]
      rw [hn]
      have hkne : (k : 𝕜) + 1 ≠ 0 := by simpa [hn] using hn1
      generalize I.tan (env "c"+env "d"*t) = T
      generalize (env "a"+env "b"*T)^k = P
      field_simp [hd, hkne, hab]
      ring

omit [CharZero 𝕜] in
theorem tanProduct_holds (I : Interp 𝕜)
    (htan : ∀ u, I.tanDefined u → HasDerivAt I.tan (1 + I.tan u ^ 2) u) :
    AntiderivHoldsUnder I "x" IntegrationNum1.rubi4321r3Nondeg.conditions
      IntegrationNum1.rubi4321r3Nondeg.body IntegrationNum1.rubi4321r3Nondeg.result := by
  intro env hcond t hF
  have hf : env "f" ≠ 0 := by
    have h := hcond (.ne (.var "f") (.int 0)) (by simp [IntegrationNum1.rubi4321r3Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have heq : env "b"*env "c" + env "a"*env "d" = 0 := by
    have h := hcond (.eq (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a") (.var "d"))) (.int 0)) (by simp [IntegrationNum1.rubi4321r3Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have htanDef : ∀ᶠ w in 𝓝 t, I.tanDefined (env "e" + env "f"*w) := by
    filter_upwards [hF] with w hw
    simpa [IntegrationNum1.rubi4321r3Nondeg, Defined, eval, Function.update] using hw
  constructor
  · filter_upwards [htanDef] with w hw
    simp [IntegrationNum1.rubi4321r3Nondeg, Defined, eval, Function.update, hneg, hf, hw]
  · have hU : HasDerivAt (fun w : 𝕜 => env "e" + env "f"*w) (env "f") t := by
      simpa using (((hasDerivAt_id' t).const_mul (env "f")).const_add (env "e"))
    have hT := (htan _ htanDef.self_of_nhds).comp t hU
    have hfun : (fun w => eval I (Function.update env "x" w) IntegrationNum1.rubi4321r3Nondeg.result) =
      (fun w : 𝕜 => (env "a"*env "c"-env "b"*env "d")*w + env "b"*env "d"*I.tan (env "e"+env "f"*w)*(env "f")⁻¹) := by
      funext w
      simp [IntegrationNum1.rubi4321r3Nondeg, eval, Function.update, hneg, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      ring
    rw [hfun]
    refine (((hasDerivAt_id' t).const_mul _).add ((hT.const_mul _).mul_const _)).congr_deriv ?_
    simp [IntegrationNum1.rubi4321r3Nondeg, eval, Function.update]
    generalize I.tan (env "e"+env "f"*t) = T
    field_simp [hf]
    linear_combination -T * heq

omit [CharZero 𝕜] in
theorem tanProductRec_holds (I : Interp 𝕜)
    (htan : ∀ u, I.tanDefined u → HasDerivAt I.tan (1 + I.tan u ^ 2) u) :
    AntiderivRecHolds I "x" IntegrationNum1.rubi4321r4Nondeg.conditions
      IntegrationNum1.rubi4321r4Nondeg.body IntegrationNum1.rubi4321r4Nondeg.result IntegrationNum1.rubi4321r4Nondeg.integrals := by
  intro env hcond t hF
  have hf : env "f" ≠ 0 := by
    have h := hcond (.ne (.var "f") (.int 0)) (by simp [IntegrationNum1.rubi4321r4Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have htanDef : ∀ᶠ w in 𝓝 t, I.tanDefined (env "e" + env "f"*w) := by
    filter_upwards [hF] with w hw
    simpa [IntegrationNum1.rubi4321r4Nondeg, Defined, eval, Function.update] using hw
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [IntegrationNum1.rubi4321r4Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    filter_upwards [htanDef] with w hw
    simpa [Defined, eval, Function.update] using hw
  · intro Φ hΦ
    simp only [IntegrationNum1.rubi4321r4Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards [htanDef] with w hw
      simp [IntegrationNum1.rubi4321r4Nondeg, Defined, eval, recEnv, hneg, hf, hw]
    · have hU : HasDerivAt (fun w : 𝕜 => env "e" + env "f"*w) (env "f") t := by
        simpa using (((hasDerivAt_id' t).const_mul (env "f")).const_add (env "e"))
      have hT := (htan _ htanDef.self_of_nhds).comp t hU
      have hfun : (fun w => eval I (recEnv env (IntegrationNum1.rubi4321r4Nondeg.integrals.map (·.1)) Φ "x" w) IntegrationNum1.rubi4321r4Nondeg.result) =
        (fun w : 𝕜 => (env "a"*env "c"-env "b"*env "d")*w + env "b"*env "d"*I.tan (env "e"+env "f"*w)*(env "f")⁻¹ +
          (env "b"*env "c"+env "a"*env "d")*Φ "I1" w) := by
        funext w
        simp [IntegrationNum1.rubi4321r4Nondeg, eval, recEnv, hneg, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
        ring
      rw [hfun]
      simp [eval, Function.update] at hΦ
      refine (((hasDerivAt_id' t).const_mul _).add ((hT.const_mul _).mul_const _)).add (hΦ.const_mul _) |>.congr_deriv ?_
      simp [IntegrationNum1.rubi4321r4Nondeg, eval, Function.update]
      generalize I.tan (env "e"+env "f"*t) = T
      field_simp [hf]
      ring

end

private theorem real_tan_deriv (u : ℝ) (h : Real.cos u ≠ 0) :
    HasDerivAt Real.tan (1 + Real.tan u ^ 2) u := by
  convert Real.hasDerivAt_tan h using 1
  rw [Real.tan_eq_sin_div_cos]
  have hp := Real.sin_sq_add_cos_sq u
  field_simp
  nlinarith [hp]

private theorem complex_tan_deriv (u : ℂ) (h : Complex.cos u ≠ 0) :
    HasDerivAt Complex.tan (1 + Complex.tan u ^ 2) u := by
  convert Complex.hasDerivAt_tan h using 1
  rw [Complex.tan_eq_sin_div_cos]
  have hp := Complex.sin_sq_add_cos_sq u
  field_simp
  linear_combination hp

theorem tanSquare_real : IntegrationNum1.rubi4311r5Nondeg.Holds .real :=
  tanSquare_holds Interp.real real_tan_deriv

theorem tanSquare_complex : IntegrationNum1.rubi4311r5Nondeg.Holds .complex :=
  tanSquare_holds Interp.complex complex_tan_deriv

theorem tanPower_real : IntegrationNum1.rubi4311r1Nondeg.Holds .real :=
  tanPower_holds Interp.real real_tan_deriv (by intro k h; have hr : (1 : ℝ) < (k : ℝ) := h; exact_mod_cast hr)

theorem tanPower_complex : IntegrationNum1.rubi4311r1Nondeg.Holds .complex :=
  tanPower_holds Interp.complex complex_tan_deriv (by
    intro k h
    have hr : (1 : ℝ) < (k : ℝ) := by simpa [Interp.complex] using h
    exact_mod_cast hr)

theorem tanAffinePower_real : IntegrationNum1.rubi4311r10Nondeg.Holds .real :=
  tanAffinePower_holds Interp.real real_tan_deriv (by intro k h; have hr : (1 : ℝ) < (k : ℝ) := h; exact_mod_cast hr)

theorem tanAffinePower_complex : IntegrationNum1.rubi4311r10Nondeg.Holds .complex :=
  tanAffinePower_holds Interp.complex complex_tan_deriv (by
    intro k h
    have hr : (1 : ℝ) < (k : ℝ) := by simpa [Interp.complex] using h
    exact_mod_cast hr)

theorem tanDegeneratePower_real : IntegrationNum1.rubi4311r6Nondeg.Holds .real :=
  tanDegeneratePower_holds Interp.real real_tan_deriv (by intro k h; have hr : (1 : ℝ) < (k : ℝ) := h; exact_mod_cast hr)

theorem tanDegeneratePower_complex : IntegrationNum1.rubi4311r6Nondeg.Holds .complex :=
  tanDegeneratePower_holds Interp.complex complex_tan_deriv (by
    intro k h
    have hr : (1 : ℝ) < (k : ℝ) := by simpa [Interp.complex] using h
    exact_mod_cast hr)

theorem tanNegative_real : IntegrationNum1.rubi4311r11Nondeg.Holds .real :=
  tanNegative_holds Interp.real real_tan_deriv (by intro k h; have hr : (k : ℝ) < -1 := h; exact_mod_cast hr)

theorem tanNegative_complex : IntegrationNum1.rubi4311r11Nondeg.Holds .complex :=
  tanNegative_holds Interp.complex complex_tan_deriv (by
    intro k h
    have hr : (k : ℝ) < -1 := by simpa [Interp.complex] using h
    exact_mod_cast hr)

theorem tanProduct_real : IntegrationNum1.rubi4321r3Nondeg.Holds .real :=
  tanProduct_holds Interp.real real_tan_deriv

theorem tanProduct_complex : IntegrationNum1.rubi4321r3Nondeg.Holds .complex :=
  tanProduct_holds Interp.complex complex_tan_deriv

theorem tanProductRec_real : IntegrationNum1.rubi4321r4Nondeg.Holds .real :=
  tanProductRec_holds Interp.real real_tan_deriv

theorem tanProductRec_complex : IntegrationNum1.rubi4321r4Nondeg.Holds .complex :=
  tanProductRec_holds Interp.complex complex_tan_deriv

end OSR.IntegrationTangentRec
