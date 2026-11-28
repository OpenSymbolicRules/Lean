import OSR.IntegrationNum1
import OSR.SymDeriv

/-! # Substitution variants proved by the chain rule

Instances of `SymDeriv.antiderivSubst_chain_open`: pointwise obligations at `t` and `g(t)`,
definedness being open where `SymDeriv.Ok` holds. -/

namespace OSR.IntegrationRec304
open OSR OSR.Calculus OSR.IntegrationNum1 OSR.SymDeriv Filter Topology

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [CharZero 𝕜]

omit [CharZero 𝕜] in
set_option maxHeartbeats 1000000 in
/-- RUBI rubi1132r83Nondeg: `u = g(x)`. -/
theorem rubi1132r83Nondeg_holds (I : Interp 𝕜) (C : Calc I) :
    AntiderivSubstHolds I "x" rubi1132r83Nondeg.conditions rubi1132r83Nondeg.body rubi1132r83Nondeg.result rubi1132r83Nondeg.integrals
      rubi1132r83Nondeg.substs := by
  have hm1 : I.toInt? (-1 : 𝕜) = some (-1) := by simpa using Interp.toInt?_cast I (-1)
  have hm2 : I.toInt? (-2 : 𝕜) = some (-2) := by simpa using Interp.toInt?_cast I (-2)
  have h2 : I.toInt? (2 : 𝕜) = some 2 := by simpa using Interp.toInt?_cast I 2
  have hm11 : I.toInt? (-1 + -1 : 𝕜) = some (-2) := by
    rw [show (-1 + -1 : 𝕜) = -2 by norm_num]; exact hm2
  refine antiderivSubst_chain_open C _ (rubi1132r83Nondeg.integrals.head!.2) (rubi1132r83Nondeg.substs.head!.2) (.app2 .mul (.int 1) (.pow (.var "c") (.int (-1))))
    (by decide) (by decide) ?_
  intro env hcs t hF
  have hc0 := hcs (.ne (.var "c") (.int 0)) (by simp [rubi1132r83Nondeg])
  simp [Cond.Holds, Defined, eval] at hc0
  rcases hkm : I.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1132r83Nondeg, Defined, eval, hkm] at h0
  have hem : env "m" = (km : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hom1 : I.toInt? ((-1 : 𝕜) + (km : 𝕜)) = some (-1 + km) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm1 : I.toInt? ((km : 𝕜) + (-1 : 𝕜)) = some (km + -1) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hom2 : I.toInt? ((1 : 𝕜) + (km : 𝕜)) = some (1 + km) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm2 : I.toInt? ((km : 𝕜) + (1 : 𝕜)) = some (km + 1) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hom3 : I.toInt? ((-2 : 𝕜) + (km : 𝕜)) = some (-2 + km) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm3 : I.toInt? ((km : 𝕜) + (-2 : 𝕜)) = some (km + -2) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hom4 : I.toInt? ((2 : 𝕜) + (km : 𝕜)) = some (2 + km) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm4 : I.toInt? ((km : 𝕜) + (2 : 𝕜)) = some (km + 2) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm1 : I.toInt? ((km : 𝕜) - 1) = some (km - 1) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm2 : I.toInt? ((km : 𝕜) - 2) = some (km - 2) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hkmp1 : I.toInt? (env "m" + 1) = some (km + 1) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmp2 : I.toInt? (env "m" + 2) = some (km + 2) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm1 : I.toInt? (env "m" + -1) = some (km + -1) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm2 : I.toInt? (env "m" + -2) = some (km + -2) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkm]; push_cast; ring)
  rcases hkn : I.toInt? (env "n") with _ | kn
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1132r83Nondeg, Defined, eval, hkn] at h0
  have hen : env "n" = (kn : 𝕜) := (I.toInt?_eq _ _).1 hkn
  have hon1 : I.toInt? ((-1 : 𝕜) + (kn : 𝕜)) = some (-1 + kn) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn1 : I.toInt? ((kn : 𝕜) + (-1 : 𝕜)) = some (kn + -1) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hon2 : I.toInt? ((1 : 𝕜) + (kn : 𝕜)) = some (1 + kn) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn2 : I.toInt? ((kn : 𝕜) + (1 : 𝕜)) = some (kn + 1) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hon3 : I.toInt? ((-2 : 𝕜) + (kn : 𝕜)) = some (-2 + kn) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn3 : I.toInt? ((kn : 𝕜) + (-2 : 𝕜)) = some (kn + -2) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hon4 : I.toInt? ((2 : 𝕜) + (kn : 𝕜)) = some (2 + kn) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn4 : I.toInt? ((kn : 𝕜) + (2 : 𝕜)) = some (kn + 2) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn1 : I.toInt? ((kn : 𝕜) - 1) = some (kn - 1) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn2 : I.toInt? ((kn : 𝕜) - 2) = some (kn - 2) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hknp1 : I.toInt? (env "n" + 1) = some (kn + 1) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknp2 : I.toInt? (env "n" + 2) = some (kn + 2) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm1 : I.toInt? (env "n" + -1) = some (kn + -1) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm2 : I.toInt? (env "n" + -2) = some (kn + -2) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkn]; push_cast; ring)
  rcases hkp : I.toInt? (env "p") with _ | kp
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1132r83Nondeg, Defined, eval, hkp] at h0
  have hep : env "p" = (kp : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hop1 : I.toInt? ((-1 : 𝕜) + (kp : 𝕜)) = some (-1 + kp) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp1 : I.toInt? ((kp : 𝕜) + (-1 : 𝕜)) = some (kp + -1) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hop2 : I.toInt? ((1 : 𝕜) + (kp : 𝕜)) = some (1 + kp) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp2 : I.toInt? ((kp : 𝕜) + (1 : 𝕜)) = some (kp + 1) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hop3 : I.toInt? ((-2 : 𝕜) + (kp : 𝕜)) = some (-2 + kp) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp3 : I.toInt? ((kp : 𝕜) + (-2 : 𝕜)) = some (kp + -2) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hop4 : I.toInt? ((2 : 𝕜) + (kp : 𝕜)) = some (2 + kp) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp4 : I.toInt? ((kp : 𝕜) + (2 : 𝕜)) = some (kp + 2) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hsp1 : I.toInt? ((kp : 𝕜) - 1) = some (kp - 1) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hsp2 : I.toInt? ((kp : 𝕜) - 2) = some (kp - 2) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hkpp1 : I.toInt? (env "p" + 1) = some (kp + 1) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpp2 : I.toInt? (env "p" + 2) = some (kp + 2) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm1 : I.toInt? (env "p" + -1) = some (kp + -1) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm2 : I.toInt? (env "p" + -2) = some (kp + -2) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have h0 := hF.self_of_nhds
  simp [rubi1132r83Nondeg, Defined, eval, hc0, hem, hen, hep, Interp.toInt?_cast] at h0
  casesm* _ ∧ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc0]
  · simp [rubi1132r83Nondeg, Ok]
  · simp [rubi1132r83Nondeg, Defined]
  · simp [rubi1132r83Nondeg, eval, Ok, Expr.varList, hm1, hc0, hem, hen, hep, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> simp_all
  · simp [rubi1132r83Nondeg, Defined, eval, hm1, hc0, hem, hen, hep, Interp.toInt?_cast]
    simp_all
  · simp [rubi1132r83Nondeg, eval, d, hm1, hem, hen, hep, Interp.toInt?_cast]
    try field_simp

theorem rubi1132r83Nondeg_real : rubi1132r83Nondeg.Holds .real := rubi1132r83Nondeg_holds Interp.real Calc.real
theorem rubi1132r83Nondeg_complex : rubi1132r83Nondeg.Holds .complex := rubi1132r83Nondeg_holds Interp.complex Calc.complex

set_option maxHeartbeats 1000000 in
/-- RUBI rubi1134r9Nondeg: `u = g(x)`. -/
theorem rubi1134r9Nondeg_holds (I : Interp 𝕜) (C : Calc I) :
    AntiderivSubstHolds I "x" rubi1134r9Nondeg.conditions rubi1134r9Nondeg.body rubi1134r9Nondeg.result rubi1134r9Nondeg.integrals
      rubi1134r9Nondeg.substs := by
  have hm1 : I.toInt? (-1 : 𝕜) = some (-1) := by simpa using Interp.toInt?_cast I (-1)
  have hm2 : I.toInt? (-2 : 𝕜) = some (-2) := by simpa using Interp.toInt?_cast I (-2)
  have h2 : I.toInt? (2 : 𝕜) = some 2 := by simpa using Interp.toInt?_cast I 2
  have hm11 : I.toInt? (-1 + -1 : 𝕜) = some (-2) := by
    rw [show (-1 + -1 : 𝕜) = -2 by norm_num]; exact hm2
  refine antiderivSubst_chain_open C _ (rubi1134r9Nondeg.integrals.head!.2) (rubi1134r9Nondeg.substs.head!.2) (.app2 .mul (.int 1) (.pow (.var "n") (.int (-1))))
    (by decide) (by decide) ?_
  intro env hcs t hF
  have hc0 := hcs (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi1134r9Nondeg])
  simp [Cond.Holds, Defined, eval] at hc0
  have hc1 := hcs (.eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)) (.int 0)) (by simp [rubi1134r9Nondeg])
  simp [Cond.Holds, Defined, eval] at hc1
  have hc2 := hcs (.ne (.var "n") (.int 0)) (by simp [rubi1134r9Nondeg])
  simp [Cond.Holds, Defined, eval] at hc2
  rcases hkm : I.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1134r9Nondeg, Defined, eval, hkm] at h0
  have hem : env "m" = (km : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hom1 : I.toInt? ((-1 : 𝕜) + (km : 𝕜)) = some (-1 + km) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm1 : I.toInt? ((km : 𝕜) + (-1 : 𝕜)) = some (km + -1) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hom2 : I.toInt? ((1 : 𝕜) + (km : 𝕜)) = some (1 + km) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm2 : I.toInt? ((km : 𝕜) + (1 : 𝕜)) = some (km + 1) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hom3 : I.toInt? ((-2 : 𝕜) + (km : 𝕜)) = some (-2 + km) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm3 : I.toInt? ((km : 𝕜) + (-2 : 𝕜)) = some (km + -2) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hom4 : I.toInt? ((2 : 𝕜) + (km : 𝕜)) = some (2 + km) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm4 : I.toInt? ((km : 𝕜) + (2 : 𝕜)) = some (km + 2) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm1 : I.toInt? ((km : 𝕜) - 1) = some (km - 1) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm2 : I.toInt? ((km : 𝕜) - 2) = some (km - 2) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hkmp1 : I.toInt? (env "m" + 1) = some (km + 1) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmp2 : I.toInt? (env "m" + 2) = some (km + 2) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm1 : I.toInt? (env "m" + -1) = some (km + -1) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm2 : I.toInt? (env "m" + -2) = some (km + -2) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkm]; push_cast; ring)
  rcases hkn : I.toInt? (env "n") with _ | kn
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1134r9Nondeg, Defined, eval, hkn] at h0
  have hen : env "n" = (kn : 𝕜) := (I.toInt?_eq _ _).1 hkn
  have hon1 : I.toInt? ((-1 : 𝕜) + (kn : 𝕜)) = some (-1 + kn) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn1 : I.toInt? ((kn : 𝕜) + (-1 : 𝕜)) = some (kn + -1) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hon2 : I.toInt? ((1 : 𝕜) + (kn : 𝕜)) = some (1 + kn) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn2 : I.toInt? ((kn : 𝕜) + (1 : 𝕜)) = some (kn + 1) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hon3 : I.toInt? ((-2 : 𝕜) + (kn : 𝕜)) = some (-2 + kn) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn3 : I.toInt? ((kn : 𝕜) + (-2 : 𝕜)) = some (kn + -2) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hon4 : I.toInt? ((2 : 𝕜) + (kn : 𝕜)) = some (2 + kn) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn4 : I.toInt? ((kn : 𝕜) + (2 : 𝕜)) = some (kn + 2) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn1 : I.toInt? ((kn : 𝕜) - 1) = some (kn - 1) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn2 : I.toInt? ((kn : 𝕜) - 2) = some (kn - 2) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hknp1 : I.toInt? (env "n" + 1) = some (kn + 1) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknp2 : I.toInt? (env "n" + 2) = some (kn + 2) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm1 : I.toInt? (env "n" + -1) = some (kn + -1) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm2 : I.toInt? (env "n" + -2) = some (kn + -2) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkn]; push_cast; ring)
  rcases hkp : I.toInt? (env "p") with _ | kp
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1134r9Nondeg, Defined, eval, hkp] at h0
  have hep : env "p" = (kp : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hop1 : I.toInt? ((-1 : 𝕜) + (kp : 𝕜)) = some (-1 + kp) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp1 : I.toInt? ((kp : 𝕜) + (-1 : 𝕜)) = some (kp + -1) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hop2 : I.toInt? ((1 : 𝕜) + (kp : 𝕜)) = some (1 + kp) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp2 : I.toInt? ((kp : 𝕜) + (1 : 𝕜)) = some (kp + 1) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hop3 : I.toInt? ((-2 : 𝕜) + (kp : 𝕜)) = some (-2 + kp) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp3 : I.toInt? ((kp : 𝕜) + (-2 : 𝕜)) = some (kp + -2) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hop4 : I.toInt? ((2 : 𝕜) + (kp : 𝕜)) = some (2 + kp) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp4 : I.toInt? ((kp : 𝕜) + (2 : 𝕜)) = some (kp + 2) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hsp1 : I.toInt? ((kp : 𝕜) - 1) = some (kp - 1) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hsp2 : I.toInt? ((kp : 𝕜) - 2) = some (kp - 2) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hkpp1 : I.toInt? (env "p" + 1) = some (kp + 1) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpp2 : I.toInt? (env "p" + 2) = some (kp + 2) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm1 : I.toInt? (env "p" + -1) = some (kp + -1) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm2 : I.toInt? (env "p" + -2) = some (kp + -2) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkp]; push_cast; ring)
  rcases hkq : I.toInt? (env "q") with _ | kq
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1134r9Nondeg, Defined, eval, hkq] at h0
  have heq : env "q" = (kq : 𝕜) := (I.toInt?_eq _ _).1 hkq
  have hoq1 : I.toInt? ((-1 : 𝕜) + (kq : 𝕜)) = some (-1 + kq) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqq1 : I.toInt? ((kq : 𝕜) + (-1 : 𝕜)) = some (kq + -1) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hoq2 : I.toInt? ((1 : 𝕜) + (kq : 𝕜)) = some (1 + kq) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqq2 : I.toInt? ((kq : 𝕜) + (1 : 𝕜)) = some (kq + 1) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hoq3 : I.toInt? ((-2 : 𝕜) + (kq : 𝕜)) = some (-2 + kq) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqq3 : I.toInt? ((kq : 𝕜) + (-2 : 𝕜)) = some (kq + -2) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hoq4 : I.toInt? ((2 : 𝕜) + (kq : 𝕜)) = some (2 + kq) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqq4 : I.toInt? ((kq : 𝕜) + (2 : 𝕜)) = some (kq + 2) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hsq1 : I.toInt? ((kq : 𝕜) - 1) = some (kq - 1) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hsq2 : I.toInt? ((kq : 𝕜) - 2) = some (kq - 2) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hkqp1 : I.toInt? (env "q" + 1) = some (kq + 1) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkq]; push_cast; ring)
  have hkqp2 : I.toInt? (env "q" + 2) = some (kq + 2) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkq]; push_cast; ring)
  have hkqm1 : I.toInt? (env "q" + -1) = some (kq + -1) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkq]; push_cast; ring)
  have hkqm2 : I.toInt? (env "q" + -2) = some (kq + -2) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkq]; push_cast; ring)
  have hzm : (km : 𝕜) = (kn : 𝕜) - 1 := by
    have h := hcs (.eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)) (.int 0)) (by simp [rubi1134r9Nondeg])
    simp [Cond.Holds, Defined, eval, (I.toInt?_eq _ _).1 hkm, (I.toInt?_eq _ _).1 hkn] at h
    linear_combination h
  have hzim : km = kn - 1 := by exact_mod_cast hzm
  subst hzim
  try simp only [hem, hen, Int.cast_eq_zero] at hc0 hc1 hc2
  have h0 := hF.self_of_nhds
  simp [rubi1134r9Nondeg, Defined, eval, hem, hen, hep, heq, Interp.toInt?_cast] at h0
  casesm* _ ∧ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc2, hen]
  · simp [rubi1134r9Nondeg, eval, Ok, Expr.varList, hen, Interp.toInt?_cast]
    rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> rcases lt_or_ge kq 0 with hsq | hsq <;> simp_all
  · simp [rubi1134r9Nondeg, Defined, eval, hen, Interp.toInt?_cast]
    assumption
  · simp [rubi1134r9Nondeg, eval, Ok, Expr.varList, hen, hep, heq, Interp.toInt?_cast]
    rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> rcases lt_or_ge kq 0 with hsq | hsq <;> simp_all
  · simp [rubi1134r9Nondeg, Defined, eval, hen, hep, heq, Interp.toInt?_cast]
    simp_all
  · simp [rubi1134r9Nondeg, eval, d, hm1, hem, hen, hsn1, hqn1, hep, heq, Interp.toInt?_cast]
    try field_simp
    try ring

theorem rubi1134r9Nondeg_real : rubi1134r9Nondeg.Holds .real := rubi1134r9Nondeg_holds Interp.real Calc.real
theorem rubi1134r9Nondeg_complex : rubi1134r9Nondeg.Holds .complex := rubi1134r9Nondeg_holds Interp.complex Calc.complex

set_option maxHeartbeats 1000000 in
/-- RUBI rubi1136r5Nondeg: `u = g(x)`. -/
theorem rubi1136r5Nondeg_holds (I : Interp 𝕜) (C : Calc I) :
    AntiderivSubstHolds I "x" rubi1136r5Nondeg.conditions rubi1136r5Nondeg.body rubi1136r5Nondeg.result rubi1136r5Nondeg.integrals
      rubi1136r5Nondeg.substs := by
  have hm1 : I.toInt? (-1 : 𝕜) = some (-1) := by simpa using Interp.toInt?_cast I (-1)
  have hm2 : I.toInt? (-2 : 𝕜) = some (-2) := by simpa using Interp.toInt?_cast I (-2)
  have h2 : I.toInt? (2 : 𝕜) = some 2 := by simpa using Interp.toInt?_cast I 2
  have hm11 : I.toInt? (-1 + -1 : 𝕜) = some (-2) := by
    rw [show (-1 + -1 : 𝕜) = -2 by norm_num]; exact hm2
  refine antiderivSubst_chain_open C _ (rubi1136r5Nondeg.integrals.head!.2) (rubi1136r5Nondeg.substs.head!.2) (.app2 .mul (.int 1) (.pow (.var "n") (.int (-1))))
    (by decide) (by decide) ?_
  intro env hcs t hF
  have hc0 := hcs (.eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)) (.int 0)) (by simp [rubi1136r5Nondeg])
  simp [Cond.Holds, Defined, eval] at hc0
  have hc1 := hcs (.ne (.var "n") (.int 0)) (by simp [rubi1136r5Nondeg])
  simp [Cond.Holds, Defined, eval] at hc1
  rcases hkm : I.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1136r5Nondeg, Defined, eval, hkm] at h0
  have hem : env "m" = (km : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hom1 : I.toInt? ((-1 : 𝕜) + (km : 𝕜)) = some (-1 + km) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm1 : I.toInt? ((km : 𝕜) + (-1 : 𝕜)) = some (km + -1) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hom2 : I.toInt? ((1 : 𝕜) + (km : 𝕜)) = some (1 + km) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm2 : I.toInt? ((km : 𝕜) + (1 : 𝕜)) = some (km + 1) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hom3 : I.toInt? ((-2 : 𝕜) + (km : 𝕜)) = some (-2 + km) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm3 : I.toInt? ((km : 𝕜) + (-2 : 𝕜)) = some (km + -2) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hom4 : I.toInt? ((2 : 𝕜) + (km : 𝕜)) = some (2 + km) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm4 : I.toInt? ((km : 𝕜) + (2 : 𝕜)) = some (km + 2) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm1 : I.toInt? ((km : 𝕜) - 1) = some (km - 1) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm2 : I.toInt? ((km : 𝕜) - 2) = some (km - 2) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hkmp1 : I.toInt? (env "m" + 1) = some (km + 1) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmp2 : I.toInt? (env "m" + 2) = some (km + 2) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm1 : I.toInt? (env "m" + -1) = some (km + -1) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm2 : I.toInt? (env "m" + -2) = some (km + -2) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkm]; push_cast; ring)
  rcases hkn : I.toInt? (env "n") with _ | kn
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1136r5Nondeg, Defined, eval, hkn] at h0
  have hen : env "n" = (kn : 𝕜) := (I.toInt?_eq _ _).1 hkn
  have hon1 : I.toInt? ((-1 : 𝕜) + (kn : 𝕜)) = some (-1 + kn) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn1 : I.toInt? ((kn : 𝕜) + (-1 : 𝕜)) = some (kn + -1) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hon2 : I.toInt? ((1 : 𝕜) + (kn : 𝕜)) = some (1 + kn) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn2 : I.toInt? ((kn : 𝕜) + (1 : 𝕜)) = some (kn + 1) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hon3 : I.toInt? ((-2 : 𝕜) + (kn : 𝕜)) = some (-2 + kn) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn3 : I.toInt? ((kn : 𝕜) + (-2 : 𝕜)) = some (kn + -2) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hon4 : I.toInt? ((2 : 𝕜) + (kn : 𝕜)) = some (2 + kn) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn4 : I.toInt? ((kn : 𝕜) + (2 : 𝕜)) = some (kn + 2) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn1 : I.toInt? ((kn : 𝕜) - 1) = some (kn - 1) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn2 : I.toInt? ((kn : 𝕜) - 2) = some (kn - 2) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hknp1 : I.toInt? (env "n" + 1) = some (kn + 1) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknp2 : I.toInt? (env "n" + 2) = some (kn + 2) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm1 : I.toInt? (env "n" + -1) = some (kn + -1) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm2 : I.toInt? (env "n" + -2) = some (kn + -2) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkn]; push_cast; ring)
  rcases hkp : I.toInt? (env "p") with _ | kp
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1136r5Nondeg, Defined, eval, hkp] at h0
  have hep : env "p" = (kp : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hop1 : I.toInt? ((-1 : 𝕜) + (kp : 𝕜)) = some (-1 + kp) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp1 : I.toInt? ((kp : 𝕜) + (-1 : 𝕜)) = some (kp + -1) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hop2 : I.toInt? ((1 : 𝕜) + (kp : 𝕜)) = some (1 + kp) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp2 : I.toInt? ((kp : 𝕜) + (1 : 𝕜)) = some (kp + 1) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hop3 : I.toInt? ((-2 : 𝕜) + (kp : 𝕜)) = some (-2 + kp) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp3 : I.toInt? ((kp : 𝕜) + (-2 : 𝕜)) = some (kp + -2) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hop4 : I.toInt? ((2 : 𝕜) + (kp : 𝕜)) = some (2 + kp) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp4 : I.toInt? ((kp : 𝕜) + (2 : 𝕜)) = some (kp + 2) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hsp1 : I.toInt? ((kp : 𝕜) - 1) = some (kp - 1) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hsp2 : I.toInt? ((kp : 𝕜) - 2) = some (kp - 2) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hkpp1 : I.toInt? (env "p" + 1) = some (kp + 1) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpp2 : I.toInt? (env "p" + 2) = some (kp + 2) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm1 : I.toInt? (env "p" + -1) = some (kp + -1) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm2 : I.toInt? (env "p" + -2) = some (kp + -2) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkp]; push_cast; ring)
  rcases hkq : I.toInt? (env "q") with _ | kq
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1136r5Nondeg, Defined, eval, hkq] at h0
  have heq : env "q" = (kq : 𝕜) := (I.toInt?_eq _ _).1 hkq
  have hoq1 : I.toInt? ((-1 : 𝕜) + (kq : 𝕜)) = some (-1 + kq) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqq1 : I.toInt? ((kq : 𝕜) + (-1 : 𝕜)) = some (kq + -1) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hoq2 : I.toInt? ((1 : 𝕜) + (kq : 𝕜)) = some (1 + kq) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqq2 : I.toInt? ((kq : 𝕜) + (1 : 𝕜)) = some (kq + 1) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hoq3 : I.toInt? ((-2 : 𝕜) + (kq : 𝕜)) = some (-2 + kq) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqq3 : I.toInt? ((kq : 𝕜) + (-2 : 𝕜)) = some (kq + -2) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hoq4 : I.toInt? ((2 : 𝕜) + (kq : 𝕜)) = some (2 + kq) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqq4 : I.toInt? ((kq : 𝕜) + (2 : 𝕜)) = some (kq + 2) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hsq1 : I.toInt? ((kq : 𝕜) - 1) = some (kq - 1) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hsq2 : I.toInt? ((kq : 𝕜) - 2) = some (kq - 2) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hkqp1 : I.toInt? (env "q" + 1) = some (kq + 1) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkq]; push_cast; ring)
  have hkqp2 : I.toInt? (env "q" + 2) = some (kq + 2) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkq]; push_cast; ring)
  have hkqm1 : I.toInt? (env "q" + -1) = some (kq + -1) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkq]; push_cast; ring)
  have hkqm2 : I.toInt? (env "q" + -2) = some (kq + -2) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkq]; push_cast; ring)
  rcases hkr : I.toInt? (env "r") with _ | kr
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1136r5Nondeg, Defined, eval, hkr] at h0
  have her : env "r" = (kr : 𝕜) := (I.toInt?_eq _ _).1 hkr
  have hor1 : I.toInt? ((-1 : 𝕜) + (kr : 𝕜)) = some (-1 + kr) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqr1 : I.toInt? ((kr : 𝕜) + (-1 : 𝕜)) = some (kr + -1) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hor2 : I.toInt? ((1 : 𝕜) + (kr : 𝕜)) = some (1 + kr) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqr2 : I.toInt? ((kr : 𝕜) + (1 : 𝕜)) = some (kr + 1) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hor3 : I.toInt? ((-2 : 𝕜) + (kr : 𝕜)) = some (-2 + kr) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqr3 : I.toInt? ((kr : 𝕜) + (-2 : 𝕜)) = some (kr + -2) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hor4 : I.toInt? ((2 : 𝕜) + (kr : 𝕜)) = some (2 + kr) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hqr4 : I.toInt? ((kr : 𝕜) + (2 : 𝕜)) = some (kr + 2) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hsr1 : I.toInt? ((kr : 𝕜) - 1) = some (kr - 1) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hsr2 : I.toInt? ((kr : 𝕜) - 2) = some (kr - 2) :=
    (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hkrp1 : I.toInt? (env "r" + 1) = some (kr + 1) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkr]; push_cast; ring)
  have hkrp2 : I.toInt? (env "r" + 2) = some (kr + 2) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkr]; push_cast; ring)
  have hkrm1 : I.toInt? (env "r" + -1) = some (kr + -1) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkr]; push_cast; ring)
  have hkrm2 : I.toInt? (env "r" + -2) = some (kr + -2) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkr]; push_cast; ring)
  have hzm : (km : 𝕜) = (kn : 𝕜) - 1 := by
    have h := hcs (.eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)) (.int 0)) (by simp [rubi1136r5Nondeg])
    simp [Cond.Holds, Defined, eval, (I.toInt?_eq _ _).1 hkm, (I.toInt?_eq _ _).1 hkn] at h
    linear_combination h
  have hzim : km = kn - 1 := by exact_mod_cast hzm
  subst hzim
  try simp only [hem, hen, Int.cast_eq_zero] at hc0 hc1
  have h0 := hF.self_of_nhds
  simp [rubi1136r5Nondeg, Defined, eval, hem, hen, hep, heq, her, Interp.toInt?_cast] at h0
  casesm* _ ∧ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc1, hen]
  · simp [rubi1136r5Nondeg, eval, Ok, Expr.varList, hen, Interp.toInt?_cast]
    rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> rcases lt_or_ge kq 0 with hsq | hsq <;> rcases lt_or_ge kr 0 with hsr | hsr <;> simp_all
  · simp [rubi1136r5Nondeg, Defined, eval, hen, Interp.toInt?_cast]
    assumption
  · simp [rubi1136r5Nondeg, eval, Ok, Expr.varList, hen, hep, heq, her, Interp.toInt?_cast]
    rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> rcases lt_or_ge kq 0 with hsq | hsq <;> rcases lt_or_ge kr 0 with hsr | hsr <;> simp_all
  · simp [rubi1136r5Nondeg, Defined, eval, hen, hep, heq, her, Interp.toInt?_cast]
    simp_all
  · simp [rubi1136r5Nondeg, eval, d, hm1, hem, hen, hsn1, hqn1, hep, heq, her, Interp.toInt?_cast]
    try field_simp
    try ring

theorem rubi1136r5Nondeg_real : rubi1136r5Nondeg.Holds .real := rubi1136r5Nondeg_holds Interp.real Calc.real
theorem rubi1136r5Nondeg_complex : rubi1136r5Nondeg.Holds .complex := rubi1136r5Nondeg_holds Interp.complex Calc.complex

end OSR.IntegrationRec304
