import OSR.IntegrationNum1
import OSR.SymDeriv

/-! # Substitution variants proved by the chain rule

Instances of `SymDeriv.antiderivSubst_chain`: the substitution `u = g(x)` has a nonzero
derivative wherever the integrand is defined, so `g` is a local homeomorphism there. -/

namespace OSR.IntegrationRec303
open OSR OSR.Calculus OSR.IntegrationNum1 OSR.SymDeriv Filter Topology

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

/-- RUBI rubi4112r10Nondeg: `u = g(x)`. -/
theorem rubi4112r10Nondeg_holds (I : Interp 𝕜) (C : Calc I) :
    AntiderivSubstHolds I "x" rubi4112r10Nondeg.conditions rubi4112r10Nondeg.body rubi4112r10Nondeg.result rubi4112r10Nondeg.integrals
      rubi4112r10Nondeg.substs := by
  have hm1 : I.toInt? (-1 : 𝕜) = some (-1) := by simpa using Interp.toInt?_cast I (-1)
  have hm2 : I.toInt? (-2 : 𝕜) = some (-2) := by simpa using Interp.toInt?_cast I (-2)
  have h2 : I.toInt? (2 : 𝕜) = some 2 := by simpa using Interp.toInt?_cast I 2
  have hm11 : I.toInt? (-1 + -1 : 𝕜) = some (-2) := by
    rw [show (-1 + -1 : 𝕜) = -2 by norm_num]; exact hm2
  refine antiderivSubst_chain C _ (rubi4112r10Nondeg.integrals.head!.2) (rubi4112r10Nondeg.substs.head!.2) (.app2 .mul (.int (-1)) (.pow (.var "f") (.int (-1))))
    (by decide) (by decide) ?_
  intro env hcs t hF
  have hc4 := hcs (.eq (.var "n") (.int (-2))) (by simp [rubi4112r10Nondeg])
  simp [Cond.Holds, Defined, eval] at hc4
  have hc5 := hcs (.ne (.var "f") (.int 0)) (by simp [rubi4112r10Nondeg])
  simp [Cond.Holds, Defined, eval] at hc5
  rcases hkp : I.toInt? (env "p") with _ | kp
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi4112r10Nondeg, Defined, eval, hkp] at h0
  have hkpp1 : I.toInt? (env "p" + 1) = some (kp + 1) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpp2 : I.toInt? (env "p" + 2) = some (kp + 2) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm1 : I.toInt? (env "p" + -1) = some (kp + -1) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm2 : I.toInt? (env "p" + -2) = some (kp + -2) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have h0 := hF.self_of_nhds
  simp [rubi4112r10Nondeg, Defined, eval, hm2, hc4, hkp] at h0
  casesm* _ ∧ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc5]
  · simp [rubi4112r10Nondeg, eval, Ok, Expr.varList, hm1]
    try tauto
  · simp [rubi4112r10Nondeg, eval, d, hm1, hm11, hc5]
    try tauto
  · filter_upwards [hF] with v hv
    simp [rubi4112r10Nondeg, Defined, eval, hm1, hm2, h2, hc4, hkp] at hv ⊢
    try tauto
  · simp [rubi4112r10Nondeg, eval, d, hm1, hm2, h2, hm11, hc4, hkp]
    try field_simp

theorem rubi4112r10Nondeg_real : rubi4112r10Nondeg.Holds .real := rubi4112r10Nondeg_holds Interp.real Calc.real
theorem rubi4112r10Nondeg_complex : rubi4112r10Nondeg.Holds .complex := rubi4112r10Nondeg_holds Interp.complex Calc.complex

/-- RUBI rubi4112r9Nondeg: `u = g(x)`. -/
theorem rubi4112r9Nondeg_holds (I : Interp 𝕜) (C : Calc I) :
    AntiderivSubstHolds I "x" rubi4112r9Nondeg.conditions rubi4112r9Nondeg.body rubi4112r9Nondeg.result rubi4112r9Nondeg.integrals
      rubi4112r9Nondeg.substs := by
  have hm1 : I.toInt? (-1 : 𝕜) = some (-1) := by simpa using Interp.toInt?_cast I (-1)
  have hm2 : I.toInt? (-2 : 𝕜) = some (-2) := by simpa using Interp.toInt?_cast I (-2)
  have h2 : I.toInt? (2 : 𝕜) = some 2 := by simpa using Interp.toInt?_cast I 2
  have hm11 : I.toInt? (-1 + -1 : 𝕜) = some (-2) := by
    rw [show (-1 + -1 : 𝕜) = -2 by norm_num]; exact hm2
  refine antiderivSubst_chain C _ (rubi4112r9Nondeg.integrals.head!.2) (rubi4112r9Nondeg.substs.head!.2) (.app2 .mul (.int (-1)) (.pow (.var "f") (.int (-1))))
    (by decide) (by decide) ?_
  intro env hcs t hF
  have hc4 := hcs (.eq (.var "n") (.int (-2))) (by simp [rubi4112r9Nondeg])
  simp [Cond.Holds, Defined, eval] at hc4
  have hc5 := hcs (.ne (.var "f") (.int 0)) (by simp [rubi4112r9Nondeg])
  simp [Cond.Holds, Defined, eval] at hc5
  rcases hkp : I.toInt? (env "p") with _ | kp
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi4112r9Nondeg, Defined, eval, hkp] at h0
  have hkpp1 : I.toInt? (env "p" + 1) = some (kp + 1) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpp2 : I.toInt? (env "p" + 2) = some (kp + 2) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm1 : I.toInt? (env "p" + -1) = some (kp + -1) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm2 : I.toInt? (env "p" + -2) = some (kp + -2) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have h0 := hF.self_of_nhds
  simp [rubi4112r9Nondeg, Defined, eval, hm2, hc4, hkp] at h0
  casesm* _ ∧ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc5]
  · simp [rubi4112r9Nondeg, eval, Ok, Expr.varList, hm1]
    try tauto
  · simp [rubi4112r9Nondeg, eval, d, hm1, hm11, hc5]
    try tauto
  · filter_upwards [hF] with v hv
    simp [rubi4112r9Nondeg, Defined, eval, hm1, hm2, h2, hc4, hkp] at hv ⊢
    try tauto
  · simp [rubi4112r9Nondeg, eval, d, hm1, hm2, h2, hm11, hc4, hkp]
    try field_simp

theorem rubi4112r9Nondeg_real : rubi4112r9Nondeg.Holds .real := rubi4112r9Nondeg_holds Interp.real Calc.real
theorem rubi4112r9Nondeg_complex : rubi4112r9Nondeg.Holds .complex := rubi4112r9Nondeg_holds Interp.complex Calc.complex

/-- RUBI rubi679r49Nondeg: `u = g(x)`. -/
theorem rubi679r49Nondeg_holds (I : Interp 𝕜) (C : Calc I) :
    AntiderivSubstHolds I "x" rubi679r49Nondeg.conditions rubi679r49Nondeg.body rubi679r49Nondeg.result rubi679r49Nondeg.integrals
      rubi679r49Nondeg.substs := by
  have hm1 : I.toInt? (-1 : 𝕜) = some (-1) := by simpa using Interp.toInt?_cast I (-1)
  have hm2 : I.toInt? (-2 : 𝕜) = some (-2) := by simpa using Interp.toInt?_cast I (-2)
  have h2 : I.toInt? (2 : 𝕜) = some 2 := by simpa using Interp.toInt?_cast I 2
  have hm11 : I.toInt? (-1 + -1 : 𝕜) = some (-2) := by
    rw [show (-1 + -1 : 𝕜) = -2 by norm_num]; exact hm2
  refine antiderivSubst_chain C _ (rubi679r49Nondeg.integrals.head!.2) (rubi679r49Nondeg.substs.head!.2) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int (-1))))
    (by decide) (by decide) ?_
  intro env hcs t hF
  have hc2 := hcs (.ne (.var "d") (.int 0)) (by simp [rubi679r49Nondeg])
  simp [Cond.Holds, Defined, eval] at hc2
  rcases hkn : I.toInt? (env "n") with _ | kn
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi679r49Nondeg, Defined, eval, hkn, hm1] at h0
  have hknp1 : I.toInt? (env "n" + 1) = some (kn + 1) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknp2 : I.toInt? (env "n" + 2) = some (kn + 2) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm1 : I.toInt? (env "n" + -1) = some (kn + -1) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm2 : I.toInt? (env "n" + -2) = some (kn + -2) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have h0 := hF.self_of_nhds
  simp [rubi679r49Nondeg, Defined, eval, hm1, hkn] at h0
  casesm* _ ∧ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc2]
  · simp [rubi679r49Nondeg, eval, Ok, Expr.varList, hm1]
    try tauto
  · simp [rubi679r49Nondeg, eval, d, hm1, hm11, hc2]
    try tauto
  · filter_upwards [hF] with v hv
    simp [rubi679r49Nondeg, Defined, eval, hm1, h2, hkn] at hv ⊢
    try tauto
  · simp [rubi679r49Nondeg, eval, d, hm1, h2, hm11, hkn]
    try field_simp

theorem rubi679r49Nondeg_real : rubi679r49Nondeg.Holds .real := rubi679r49Nondeg_holds Interp.real Calc.real
theorem rubi679r49Nondeg_complex : rubi679r49Nondeg.Holds .complex := rubi679r49Nondeg_holds Interp.complex Calc.complex

/-- RUBI rubi679r50Nondeg: `u = g(x)`. -/
theorem rubi679r50Nondeg_holds (I : Interp 𝕜) (C : Calc I) :
    AntiderivSubstHolds I "x" rubi679r50Nondeg.conditions rubi679r50Nondeg.body rubi679r50Nondeg.result rubi679r50Nondeg.integrals
      rubi679r50Nondeg.substs := by
  have hm1 : I.toInt? (-1 : 𝕜) = some (-1) := by simpa using Interp.toInt?_cast I (-1)
  have hm2 : I.toInt? (-2 : 𝕜) = some (-2) := by simpa using Interp.toInt?_cast I (-2)
  have h2 : I.toInt? (2 : 𝕜) = some 2 := by simpa using Interp.toInt?_cast I 2
  have hm11 : I.toInt? (-1 + -1 : 𝕜) = some (-2) := by
    rw [show (-1 + -1 : 𝕜) = -2 by norm_num]; exact hm2
  refine antiderivSubst_chain C _ (rubi679r50Nondeg.integrals.head!.2) (rubi679r50Nondeg.substs.head!.2) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int (-1))))
    (by decide) (by decide) ?_
  intro env hcs t hF
  have hc2 := hcs (.ne (.var "d") (.int 0)) (by simp [rubi679r50Nondeg])
  simp [Cond.Holds, Defined, eval] at hc2
  rcases hkn : I.toInt? (env "n") with _ | kn
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi679r50Nondeg, Defined, eval, hkn, hm1] at h0
  have hknp1 : I.toInt? (env "n" + 1) = some (kn + 1) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknp2 : I.toInt? (env "n" + 2) = some (kn + 2) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm1 : I.toInt? (env "n" + -1) = some (kn + -1) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm2 : I.toInt? (env "n" + -2) = some (kn + -2) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have h0 := hF.self_of_nhds
  simp [rubi679r50Nondeg, Defined, eval, hm1, hkn] at h0
  casesm* _ ∧ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc2]
  · simp [rubi679r50Nondeg, eval, Ok, Expr.varList, hm1]
    try tauto
  · simp [rubi679r50Nondeg, eval, d, hm1, hm11, hc2]
    try tauto
  · filter_upwards [hF] with v hv
    simp [rubi679r50Nondeg, Defined, eval, hm1, h2, hkn] at hv ⊢
    try tauto
  · simp [rubi679r50Nondeg, eval, d, hm1, h2, hm11, hkn]
    try field_simp

theorem rubi679r50Nondeg_real : rubi679r50Nondeg.Holds .real := rubi679r50Nondeg_holds Interp.real Calc.real
theorem rubi679r50Nondeg_complex : rubi679r50Nondeg.Holds .complex := rubi679r50Nondeg_holds Interp.complex Calc.complex

end OSR.IntegrationRec303
