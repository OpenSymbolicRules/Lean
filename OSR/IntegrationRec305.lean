import OSR.IntegrationNum1
import OSR.SymDeriv

/-! # Explicit terms by the symbolic derivative

Instances of `SymDeriv.antiderivRec_open`, `antiderivRec_open1`, `antiderivRec_open2`,
`antiderivRec_lin1`, `antiderivRec_lin2` and `antideriv_open` with the concrete interpretation:
pointwise obligations at `t`, the derivative of the explicit term being `SymDeriv.d`. Powers
`B ^ (k + c)` with a symbolic integer exponent are split as `B ^ (k + c₀) * B ^ (c - c₀)`
(`zsplit`) so that the value identity is a rational-function identity, closed by `field_simp` and
`ring1`, or by `linear_combination` with a coefficient computed offline when an equality
condition of the rule is needed. -/

namespace OSR.IntegrationRec305
open OSR OSR.Calculus OSR.IntegrationNum1 OSR.SymDeriv Filter Topology

private theorem zsplit {K : Type} [DivisionRing K] (X : K) (j : ℤ) (n : ℕ) (h : X ≠ 0 ∨ 0 ≤ j) :
    X ^ (j + n) = X ^ j * X ^ n := by
  rcases h with h | h
  · rw [zpow_add₀ h, zpow_natCast]
  · lift j to ℕ using h
    rw [show ((j : ℤ) + n) = ((j + n : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
      pow_add]

set_option maxHeartbeats 1000000 in
/-- RUBI rubi1113r24Nondeg: explicit term by the symbolic derivative. -/
theorem rubi1113r24Nondeg_real : rubi1113r24Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1113r24Nondeg.conditions rubi1113r24Nondeg.body rubi1113r24Nondeg.result rubi1113r24Nondeg.integrals
  have hm1 : Interp.real.toInt? (-1 : ℝ) = some (-1) := by simpa using Interp.toInt?_cast Interp.real (-1)
  have hm2 : Interp.real.toInt? (-2 : ℝ) = some (-2) := by simpa using Interp.toInt?_cast Interp.real (-2)
  have h2 : Interp.real.toInt? (2 : ℝ) = some 2 := by simpa using Interp.toInt?_cast Interp.real 2
  have hm11 : Interp.real.toInt? (-1 + -1 : ℝ) = some (-2) := by
    rw [show (-1 + -1 : ℝ) = -2 by norm_num]; exact hm2
  have dln : ∀ z : ℝ, Interp.real.lnDefined z ↔ 0 < z := fun _ => Iff.rfl
  have dtan : ∀ z : ℝ, Interp.real.tanDefined z ↔ Real.cos z ≠ 0 := fun _ => Iff.rfl
  have dasin : ∀ z : ℝ, Interp.real.fnDefined .arcsin z ↔ -1 ≤ z ∧ z ≤ 1 := fun _ => Iff.rfl
  have dacos : ∀ z : ℝ, Interp.real.fnDefined .arccos z ↔ -1 ≤ z ∧ z ≤ 1 := fun _ => Iff.rfl
  refine antiderivRec_open Calc.real _ (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n"))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "p"))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (rubi1113r24Nondeg.integrals.head!.2) (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.real.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1113r24Nondeg, Defined, eval, hkm] at h0
  have hem : env "m" = (km : ℝ) := (Interp.real.toInt?_eq _ _).1 hkm
  have hom1 : Interp.real.toInt? ((-1 : ℝ) + (km : ℝ)) = some (-1 + km) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm1 : Interp.real.toInt? ((km : ℝ) + (-1 : ℝ)) = some (km + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hom2 : Interp.real.toInt? ((1 : ℝ) + (km : ℝ)) = some (1 + km) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm2 : Interp.real.toInt? ((km : ℝ) + (1 : ℝ)) = some (km + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hom3 : Interp.real.toInt? ((-2 : ℝ) + (km : ℝ)) = some (-2 + km) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm3 : Interp.real.toInt? ((km : ℝ) + (-2 : ℝ)) = some (km + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hom4 : Interp.real.toInt? ((2 : ℝ) + (km : ℝ)) = some (2 + km) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm4 : Interp.real.toInt? ((km : ℝ) + (2 : ℝ)) = some (km + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm1 : Interp.real.toInt? ((km : ℝ) - 1) = some (km - 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm2 : Interp.real.toInt? ((km : ℝ) - 2) = some (km - 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hkmp1 : Interp.real.toInt? (env "m" + 1) = some (km + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmp2 : Interp.real.toInt? (env "m" + 2) = some (km + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm1 : Interp.real.toInt? (env "m" + -1) = some (km + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm2 : Interp.real.toInt? (env "m" + -2) = some (km + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkm]; push_cast; ring)
  rcases hkn : Interp.real.toInt? (env "n") with _ | kn
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1113r24Nondeg, Defined, eval, hkn] at h0
  have hen : env "n" = (kn : ℝ) := (Interp.real.toInt?_eq _ _).1 hkn
  have hon1 : Interp.real.toInt? ((-1 : ℝ) + (kn : ℝ)) = some (-1 + kn) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn1 : Interp.real.toInt? ((kn : ℝ) + (-1 : ℝ)) = some (kn + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hon2 : Interp.real.toInt? ((1 : ℝ) + (kn : ℝ)) = some (1 + kn) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn2 : Interp.real.toInt? ((kn : ℝ) + (1 : ℝ)) = some (kn + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hon3 : Interp.real.toInt? ((-2 : ℝ) + (kn : ℝ)) = some (-2 + kn) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn3 : Interp.real.toInt? ((kn : ℝ) + (-2 : ℝ)) = some (kn + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hon4 : Interp.real.toInt? ((2 : ℝ) + (kn : ℝ)) = some (2 + kn) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn4 : Interp.real.toInt? ((kn : ℝ) + (2 : ℝ)) = some (kn + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn1 : Interp.real.toInt? ((kn : ℝ) - 1) = some (kn - 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn2 : Interp.real.toInt? ((kn : ℝ) - 2) = some (kn - 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hknp1 : Interp.real.toInt? (env "n" + 1) = some (kn + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknp2 : Interp.real.toInt? (env "n" + 2) = some (kn + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm1 : Interp.real.toInt? (env "n" + -1) = some (kn + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm2 : Interp.real.toInt? (env "n" + -2) = some (kn + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkn]; push_cast; ring)
  rcases hkp : Interp.real.toInt? (env "p") with _ | kp
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1113r24Nondeg, Defined, eval, hkp] at h0
  have hep : env "p" = (kp : ℝ) := (Interp.real.toInt?_eq _ _).1 hkp
  have hop1 : Interp.real.toInt? ((-1 : ℝ) + (kp : ℝ)) = some (-1 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp1 : Interp.real.toInt? ((kp : ℝ) + (-1 : ℝ)) = some (kp + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hop2 : Interp.real.toInt? ((1 : ℝ) + (kp : ℝ)) = some (1 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp2 : Interp.real.toInt? ((kp : ℝ) + (1 : ℝ)) = some (kp + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hop3 : Interp.real.toInt? ((-2 : ℝ) + (kp : ℝ)) = some (-2 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp3 : Interp.real.toInt? ((kp : ℝ) + (-2 : ℝ)) = some (kp + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hop4 : Interp.real.toInt? ((2 : ℝ) + (kp : ℝ)) = some (2 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp4 : Interp.real.toInt? ((kp : ℝ) + (2 : ℝ)) = some (kp + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsp1 : Interp.real.toInt? ((kp : ℝ) - 1) = some (kp - 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsp2 : Interp.real.toInt? ((kp : ℝ) - 2) = some (kp - 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hkpp1 : Interp.real.toInt? (env "p" + 1) = some (kp + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpp2 : Interp.real.toInt? (env "p" + 2) = some (kp + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm1 : Interp.real.toInt? (env "p" + -1) = some (kp + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm2 : Interp.real.toInt? (env "p" + -2) = some (kp + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hbm1gt : km < -1 := by
    have h := hcs (.gt (.int (-1)) (.var "m")) (by simp [rubi1113r24Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hem] at h
    exact_mod_cast h
  have hbn0gt : 0 < kn := by
    have h := hcs (.gt (.var "n") (.int 0)) (by simp [rubi1113r24Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hen] at h
    exact_mod_cast h
  have hbp0gt : 0 < kp := by
    have h := hcs (.gt (.var "p") (.int 0)) (by simp [rubi1113r24Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hep] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi1113r24Nondeg, Defined, eval, hem, hen, hep, Interp.toInt?_cast] at h0
  casesm* _ ∧ _
  have hc15 := hcs (.ne (.app2 .mul (.var "b") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi1113r24Nondeg])
  simp [Cond.Holds, Defined, eval] at hc15
  try simp only [hem] at hc15
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc15, hem]
  · simp [eval, Ok, Expr.varList, hm1, hc15, hem, hqm2, hen, hep, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [Defined, eval, hm1, hc15, hem, hqm2, hen, hep, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [Calc.real, rubi1113r24Nondeg, eval, Ok, Expr.varList, hem, hqm2, hen, hqn1, hep, hqp1]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [rubi1113r24Nondeg, Defined, eval, hem, hqm2, hen, hqn1, hep, hqp1]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [rubi1113r24Nondeg, eval, d, hm1, hm11, hem, hqm2, hen, hqn1, hep, hqp1, Interp.toInt?_cast]
    try have hqmm30 : (km : ℝ) - 3 ≠ 0 := by exact_mod_cast (show km - 3 ≠ 0 by omega)
    try have hqmm20 : (km : ℝ) - 2 ≠ 0 := by exact_mod_cast (show km - 2 ≠ 0 by omega)
    try have hqmm10 : (km : ℝ) - 1 ≠ 0 := by exact_mod_cast (show km - 1 ≠ 0 by omega)
    try have hqmp00 : (km : ℝ) ≠ 0 := by exact_mod_cast (show km ≠ 0 by omega)
    try have hqmp10 : (km : ℝ) + 1 ≠ 0 := by exact_mod_cast (show km + 1 ≠ 0 by omega)
    try have hqnp00 : (kn : ℝ) ≠ 0 := by exact_mod_cast (show kn ≠ 0 by omega)
    try have hqnp10 : (kn : ℝ) + 1 ≠ 0 := by exact_mod_cast (show kn + 1 ≠ 0 by omega)
    try have hqnp20 : (kn : ℝ) + 2 ≠ 0 := by exact_mod_cast (show kn + 2 ≠ 0 by omega)
    try have hqnp30 : (kn : ℝ) + 3 ≠ 0 := by exact_mod_cast (show kn + 3 ≠ 0 by omega)
    try have hqpp00 : (kp : ℝ) ≠ 0 := by exact_mod_cast (show kp ≠ 0 by omega)
    try have hqpp10 : (kp : ℝ) + 1 ≠ 0 := by exact_mod_cast (show kp + 1 ≠ 0 by omega)
    try have hqpp20 : (kp : ℝ) + 2 ≠ 0 := by exact_mod_cast (show kp + 2 ≠ 0 by omega)
    try have hqpp30 : (kp : ℝ) + 3 ≠ 0 := by exact_mod_cast (show kp + 3 ≠ 0 by omega)
    have hz0 : (env "a" + (env "b" * t)) ≠ 0 ∨ 0 ≤ km := by
      rcases lt_or_ge (km) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show (env "a" + (env "b" * t)) ^ (km + 1) = (env "a" + (env "b" * t)) ^ (km) * (env "a" + (env "b" * t)) ^ 1 from by
      have := zsplit ((env "a" + (env "b" * t))) (km) 1 hz0
      rwa [show km + ((1 : ℕ) : ℤ) = km + 1 by push_cast; ring] at this]
    try generalize (env "a" + (env "b" * t)) ^ (km) = P0
    have hz1 : (env "c" + (env "d" * t)) ≠ 0 ∨ 0 ≤ kn + -1 := by
      exact Or.inr (by omega)
    try rw [show (env "c" + (env "d" * t)) ^ (kn) = (env "c" + (env "d" * t)) ^ (kn + -1) * (env "c" + (env "d" * t)) ^ 1 from by
      have := zsplit ((env "c" + (env "d" * t))) (kn + -1) 1 hz1
      rwa [show kn + -1 + ((1 : ℕ) : ℤ) = kn by push_cast; ring] at this]
    try generalize (env "c" + (env "d" * t)) ^ (kn + -1) = P1
    have hz2 : (env "e" + (env "f" * t)) ≠ 0 ∨ 0 ≤ kp + -1 := by
      exact Or.inr (by omega)
    try rw [show (env "e" + (env "f" * t)) ^ (kp) = (env "e" + (env "f" * t)) ^ (kp + -1) * (env "e" + (env "f" * t)) ^ 1 from by
      have := zsplit ((env "e" + (env "f" * t))) (kp + -1) 1 hz2
      rwa [show kp + -1 + ((1 : ℕ) : ℤ) = kp by push_cast; ring] at this]
    try generalize (env "e" + (env "f" * t)) ^ (kp + -1) = P2
    try casesm* _ ∧ _
    try field_simp
    try ring

set_option maxHeartbeats 1000000 in
/-- RUBI rubi1113r24Nondeg: explicit term by the symbolic derivative. -/
theorem rubi1113r24Nondeg_complex : rubi1113r24Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1113r24Nondeg.conditions rubi1113r24Nondeg.body rubi1113r24Nondeg.result rubi1113r24Nondeg.integrals
  have hm1 : Interp.complex.toInt? (-1 : ℂ) = some (-1) := by simpa using Interp.toInt?_cast Interp.complex (-1)
  have hm2 : Interp.complex.toInt? (-2 : ℂ) = some (-2) := by simpa using Interp.toInt?_cast Interp.complex (-2)
  have h2 : Interp.complex.toInt? (2 : ℂ) = some 2 := by simpa using Interp.toInt?_cast Interp.complex 2
  have hm11 : Interp.complex.toInt? (-1 + -1 : ℂ) = some (-2) := by
    rw [show (-1 + -1 : ℂ) = -2 by norm_num]; exact hm2
  have dln : ∀ z : ℂ, Interp.complex.lnDefined z ↔ z ≠ 0 := fun _ => Iff.rfl
  have dtan : ∀ z : ℂ, Interp.complex.tanDefined z ↔ Complex.cos z ≠ 0 := fun _ => Iff.rfl
  refine antiderivRec_open Calc.complex _ (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n"))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "p"))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (rubi1113r24Nondeg.integrals.head!.2) (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.complex.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1113r24Nondeg, Defined, eval, hkm] at h0
  have hem : env "m" = (km : ℂ) := (Interp.complex.toInt?_eq _ _).1 hkm
  have hom1 : Interp.complex.toInt? ((-1 : ℂ) + (km : ℂ)) = some (-1 + km) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm1 : Interp.complex.toInt? ((km : ℂ) + (-1 : ℂ)) = some (km + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hom2 : Interp.complex.toInt? ((1 : ℂ) + (km : ℂ)) = some (1 + km) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm2 : Interp.complex.toInt? ((km : ℂ) + (1 : ℂ)) = some (km + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hom3 : Interp.complex.toInt? ((-2 : ℂ) + (km : ℂ)) = some (-2 + km) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm3 : Interp.complex.toInt? ((km : ℂ) + (-2 : ℂ)) = some (km + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hom4 : Interp.complex.toInt? ((2 : ℂ) + (km : ℂ)) = some (2 + km) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm4 : Interp.complex.toInt? ((km : ℂ) + (2 : ℂ)) = some (km + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm1 : Interp.complex.toInt? ((km : ℂ) - 1) = some (km - 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm2 : Interp.complex.toInt? ((km : ℂ) - 2) = some (km - 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hkmp1 : Interp.complex.toInt? (env "m" + 1) = some (km + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmp2 : Interp.complex.toInt? (env "m" + 2) = some (km + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm1 : Interp.complex.toInt? (env "m" + -1) = some (km + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm2 : Interp.complex.toInt? (env "m" + -2) = some (km + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkm]; push_cast; ring)
  rcases hkn : Interp.complex.toInt? (env "n") with _ | kn
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1113r24Nondeg, Defined, eval, hkn] at h0
  have hen : env "n" = (kn : ℂ) := (Interp.complex.toInt?_eq _ _).1 hkn
  have hon1 : Interp.complex.toInt? ((-1 : ℂ) + (kn : ℂ)) = some (-1 + kn) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn1 : Interp.complex.toInt? ((kn : ℂ) + (-1 : ℂ)) = some (kn + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hon2 : Interp.complex.toInt? ((1 : ℂ) + (kn : ℂ)) = some (1 + kn) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn2 : Interp.complex.toInt? ((kn : ℂ) + (1 : ℂ)) = some (kn + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hon3 : Interp.complex.toInt? ((-2 : ℂ) + (kn : ℂ)) = some (-2 + kn) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn3 : Interp.complex.toInt? ((kn : ℂ) + (-2 : ℂ)) = some (kn + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hon4 : Interp.complex.toInt? ((2 : ℂ) + (kn : ℂ)) = some (2 + kn) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn4 : Interp.complex.toInt? ((kn : ℂ) + (2 : ℂ)) = some (kn + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn1 : Interp.complex.toInt? ((kn : ℂ) - 1) = some (kn - 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn2 : Interp.complex.toInt? ((kn : ℂ) - 2) = some (kn - 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hknp1 : Interp.complex.toInt? (env "n" + 1) = some (kn + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknp2 : Interp.complex.toInt? (env "n" + 2) = some (kn + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm1 : Interp.complex.toInt? (env "n" + -1) = some (kn + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm2 : Interp.complex.toInt? (env "n" + -2) = some (kn + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkn]; push_cast; ring)
  rcases hkp : Interp.complex.toInt? (env "p") with _ | kp
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1113r24Nondeg, Defined, eval, hkp] at h0
  have hep : env "p" = (kp : ℂ) := (Interp.complex.toInt?_eq _ _).1 hkp
  have hop1 : Interp.complex.toInt? ((-1 : ℂ) + (kp : ℂ)) = some (-1 + kp) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp1 : Interp.complex.toInt? ((kp : ℂ) + (-1 : ℂ)) = some (kp + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hop2 : Interp.complex.toInt? ((1 : ℂ) + (kp : ℂ)) = some (1 + kp) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp2 : Interp.complex.toInt? ((kp : ℂ) + (1 : ℂ)) = some (kp + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hop3 : Interp.complex.toInt? ((-2 : ℂ) + (kp : ℂ)) = some (-2 + kp) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp3 : Interp.complex.toInt? ((kp : ℂ) + (-2 : ℂ)) = some (kp + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hop4 : Interp.complex.toInt? ((2 : ℂ) + (kp : ℂ)) = some (2 + kp) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp4 : Interp.complex.toInt? ((kp : ℂ) + (2 : ℂ)) = some (kp + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsp1 : Interp.complex.toInt? ((kp : ℂ) - 1) = some (kp - 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsp2 : Interp.complex.toInt? ((kp : ℂ) - 2) = some (kp - 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hkpp1 : Interp.complex.toInt? (env "p" + 1) = some (kp + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpp2 : Interp.complex.toInt? (env "p" + 2) = some (kp + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm1 : Interp.complex.toInt? (env "p" + -1) = some (kp + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm2 : Interp.complex.toInt? (env "p" + -2) = some (kp + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hbm1gt : km < -1 := by
    have h := hcs (.gt (.int (-1)) (.var "m")) (by simp [rubi1113r24Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, hem, Complex.ext_iff] at h
    exact_mod_cast h
  have hbn0gt : 0 < kn := by
    have h := hcs (.gt (.var "n") (.int 0)) (by simp [rubi1113r24Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, hen, Complex.ext_iff] at h
    exact_mod_cast h
  have hbp0gt : 0 < kp := by
    have h := hcs (.gt (.var "p") (.int 0)) (by simp [rubi1113r24Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, hep, Complex.ext_iff] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi1113r24Nondeg, Defined, eval, hem, hen, hep, Interp.toInt?_cast] at h0
  casesm* _ ∧ _
  have hc15 := hcs (.ne (.app2 .mul (.var "b") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi1113r24Nondeg])
  simp [Cond.Holds, Defined, eval] at hc15
  try simp only [hem] at hc15
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc15, hem]
  · simp [eval, Ok, Expr.varList, hm1, hc15, hem, hqm2, hen, hep, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [Defined, eval, hm1, hc15, hem, hqm2, hen, hep, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [Calc.complex, rubi1113r24Nondeg, eval, Ok, Expr.varList, hem, hqm2, hen, hqn1, hep, hqp1]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [rubi1113r24Nondeg, Defined, eval, hem, hqm2, hen, hqn1, hep, hqp1]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [rubi1113r24Nondeg, eval, d, hm1, hm11, hem, hqm2, hen, hqn1, hep, hqp1, Interp.toInt?_cast]
    try have hqmm30 : (km : ℂ) - 3 ≠ 0 := by exact_mod_cast (show km - 3 ≠ 0 by omega)
    try have hqmm20 : (km : ℂ) - 2 ≠ 0 := by exact_mod_cast (show km - 2 ≠ 0 by omega)
    try have hqmm10 : (km : ℂ) - 1 ≠ 0 := by exact_mod_cast (show km - 1 ≠ 0 by omega)
    try have hqmp00 : (km : ℂ) ≠ 0 := by exact_mod_cast (show km ≠ 0 by omega)
    try have hqmp10 : (km : ℂ) + 1 ≠ 0 := by exact_mod_cast (show km + 1 ≠ 0 by omega)
    try have hqnp00 : (kn : ℂ) ≠ 0 := by exact_mod_cast (show kn ≠ 0 by omega)
    try have hqnp10 : (kn : ℂ) + 1 ≠ 0 := by exact_mod_cast (show kn + 1 ≠ 0 by omega)
    try have hqnp20 : (kn : ℂ) + 2 ≠ 0 := by exact_mod_cast (show kn + 2 ≠ 0 by omega)
    try have hqnp30 : (kn : ℂ) + 3 ≠ 0 := by exact_mod_cast (show kn + 3 ≠ 0 by omega)
    try have hqpp00 : (kp : ℂ) ≠ 0 := by exact_mod_cast (show kp ≠ 0 by omega)
    try have hqpp10 : (kp : ℂ) + 1 ≠ 0 := by exact_mod_cast (show kp + 1 ≠ 0 by omega)
    try have hqpp20 : (kp : ℂ) + 2 ≠ 0 := by exact_mod_cast (show kp + 2 ≠ 0 by omega)
    try have hqpp30 : (kp : ℂ) + 3 ≠ 0 := by exact_mod_cast (show kp + 3 ≠ 0 by omega)
    have hz0 : (env "a" + (env "b" * t)) ≠ 0 ∨ 0 ≤ km := by
      rcases lt_or_ge (km) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show (env "a" + (env "b" * t)) ^ (km + 1) = (env "a" + (env "b" * t)) ^ (km) * (env "a" + (env "b" * t)) ^ 1 from by
      have := zsplit ((env "a" + (env "b" * t))) (km) 1 hz0
      rwa [show km + ((1 : ℕ) : ℤ) = km + 1 by push_cast; ring] at this]
    try generalize (env "a" + (env "b" * t)) ^ (km) = P0
    have hz1 : (env "c" + (env "d" * t)) ≠ 0 ∨ 0 ≤ kn + -1 := by
      exact Or.inr (by omega)
    try rw [show (env "c" + (env "d" * t)) ^ (kn) = (env "c" + (env "d" * t)) ^ (kn + -1) * (env "c" + (env "d" * t)) ^ 1 from by
      have := zsplit ((env "c" + (env "d" * t))) (kn + -1) 1 hz1
      rwa [show kn + -1 + ((1 : ℕ) : ℤ) = kn by push_cast; ring] at this]
    try generalize (env "c" + (env "d" * t)) ^ (kn + -1) = P1
    have hz2 : (env "e" + (env "f" * t)) ≠ 0 ∨ 0 ≤ kp + -1 := by
      exact Or.inr (by omega)
    try rw [show (env "e" + (env "f" * t)) ^ (kp) = (env "e" + (env "f" * t)) ^ (kp + -1) * (env "e" + (env "f" * t)) ^ 1 from by
      have := zsplit ((env "e" + (env "f" * t))) (kp + -1) 1 hz2
      rwa [show kp + -1 + ((1 : ℕ) : ℤ) = kp by push_cast; ring] at this]
    try generalize (env "e" + (env "f" * t)) ^ (kp + -1) = P2
    try casesm* _ ∧ _
    try field_simp
    try ring

set_option maxHeartbeats 1000000 in
/-- RUBI rubi1113r26Nondeg: explicit term by the symbolic derivative. -/
theorem rubi1113r26Nondeg_real : rubi1113r26Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1113r26Nondeg.conditions rubi1113r26Nondeg.body rubi1113r26Nondeg.result rubi1113r26Nondeg.integrals
  have hm1 : Interp.real.toInt? (-1 : ℝ) = some (-1) := by simpa using Interp.toInt?_cast Interp.real (-1)
  have hm2 : Interp.real.toInt? (-2 : ℝ) = some (-2) := by simpa using Interp.toInt?_cast Interp.real (-2)
  have h2 : Interp.real.toInt? (2 : ℝ) = some 2 := by simpa using Interp.toInt?_cast Interp.real 2
  have hm11 : Interp.real.toInt? (-1 + -1 : ℝ) = some (-2) := by
    rw [show (-1 + -1 : ℝ) = -2 by norm_num]; exact hm2
  have dln : ∀ z : ℝ, Interp.real.lnDefined z ↔ 0 < z := fun _ => Iff.rfl
  have dtan : ∀ z : ℝ, Interp.real.tanDefined z ↔ Real.cos z ≠ 0 := fun _ => Iff.rfl
  have dasin : ∀ z : ℝ, Interp.real.fnDefined .arcsin z ↔ -1 ≤ z ∧ z ≤ 1 := fun _ => Iff.rfl
  have dacos : ∀ z : ℝ, Interp.real.fnDefined .arccos z ↔ -1 ≤ z ∧ z ≤ 1 := fun _ => Iff.rfl
  refine antiderivRec_open Calc.real _ (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n"))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.int (-1)))) (rubi1113r26Nondeg.integrals.head!.2) (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.int (-1)))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.real.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1113r26Nondeg, Defined, eval, hkm] at h0
  have hem : env "m" = (km : ℝ) := (Interp.real.toInt?_eq _ _).1 hkm
  have hom1 : Interp.real.toInt? ((-1 : ℝ) + (km : ℝ)) = some (-1 + km) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm1 : Interp.real.toInt? ((km : ℝ) + (-1 : ℝ)) = some (km + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hom2 : Interp.real.toInt? ((1 : ℝ) + (km : ℝ)) = some (1 + km) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm2 : Interp.real.toInt? ((km : ℝ) + (1 : ℝ)) = some (km + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hom3 : Interp.real.toInt? ((-2 : ℝ) + (km : ℝ)) = some (-2 + km) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm3 : Interp.real.toInt? ((km : ℝ) + (-2 : ℝ)) = some (km + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hom4 : Interp.real.toInt? ((2 : ℝ) + (km : ℝ)) = some (2 + km) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm4 : Interp.real.toInt? ((km : ℝ) + (2 : ℝ)) = some (km + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm1 : Interp.real.toInt? ((km : ℝ) - 1) = some (km - 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm2 : Interp.real.toInt? ((km : ℝ) - 2) = some (km - 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hkmp1 : Interp.real.toInt? (env "m" + 1) = some (km + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmp2 : Interp.real.toInt? (env "m" + 2) = some (km + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm1 : Interp.real.toInt? (env "m" + -1) = some (km + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm2 : Interp.real.toInt? (env "m" + -2) = some (km + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkm]; push_cast; ring)
  rcases hkn : Interp.real.toInt? (env "n") with _ | kn
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1113r26Nondeg, Defined, eval, hkn] at h0
  have hen : env "n" = (kn : ℝ) := (Interp.real.toInt?_eq _ _).1 hkn
  have hon1 : Interp.real.toInt? ((-1 : ℝ) + (kn : ℝ)) = some (-1 + kn) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn1 : Interp.real.toInt? ((kn : ℝ) + (-1 : ℝ)) = some (kn + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hon2 : Interp.real.toInt? ((1 : ℝ) + (kn : ℝ)) = some (1 + kn) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn2 : Interp.real.toInt? ((kn : ℝ) + (1 : ℝ)) = some (kn + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hon3 : Interp.real.toInt? ((-2 : ℝ) + (kn : ℝ)) = some (-2 + kn) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn3 : Interp.real.toInt? ((kn : ℝ) + (-2 : ℝ)) = some (kn + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hon4 : Interp.real.toInt? ((2 : ℝ) + (kn : ℝ)) = some (2 + kn) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn4 : Interp.real.toInt? ((kn : ℝ) + (2 : ℝ)) = some (kn + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn1 : Interp.real.toInt? ((kn : ℝ) - 1) = some (kn - 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn2 : Interp.real.toInt? ((kn : ℝ) - 2) = some (kn - 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hknp1 : Interp.real.toInt? (env "n" + 1) = some (kn + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknp2 : Interp.real.toInt? (env "n" + 2) = some (kn + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm1 : Interp.real.toInt? (env "n" + -1) = some (kn + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm2 : Interp.real.toInt? (env "n" + -2) = some (kn + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkn]; push_cast; ring)
  rcases hkp : Interp.real.toInt? (env "p") with _ | kp
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1113r26Nondeg, Defined, eval, hkp] at h0
  have hep : env "p" = (kp : ℝ) := (Interp.real.toInt?_eq _ _).1 hkp
  have hop1 : Interp.real.toInt? ((-1 : ℝ) + (kp : ℝ)) = some (-1 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp1 : Interp.real.toInt? ((kp : ℝ) + (-1 : ℝ)) = some (kp + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hop2 : Interp.real.toInt? ((1 : ℝ) + (kp : ℝ)) = some (1 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp2 : Interp.real.toInt? ((kp : ℝ) + (1 : ℝ)) = some (kp + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hop3 : Interp.real.toInt? ((-2 : ℝ) + (kp : ℝ)) = some (-2 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp3 : Interp.real.toInt? ((kp : ℝ) + (-2 : ℝ)) = some (kp + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hop4 : Interp.real.toInt? ((2 : ℝ) + (kp : ℝ)) = some (2 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp4 : Interp.real.toInt? ((kp : ℝ) + (2 : ℝ)) = some (kp + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsp1 : Interp.real.toInt? ((kp : ℝ) - 1) = some (kp - 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsp2 : Interp.real.toInt? ((kp : ℝ) - 2) = some (kp - 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hkpp1 : Interp.real.toInt? (env "p" + 1) = some (kp + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpp2 : Interp.real.toInt? (env "p" + 2) = some (kp + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm1 : Interp.real.toInt? (env "p" + -1) = some (kp + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm2 : Interp.real.toInt? (env "p" + -2) = some (kp + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hbm1gt : km < -1 := by
    have h := hcs (.gt (.int (-1)) (.var "m")) (by simp [rubi1113r26Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hem] at h
    exact_mod_cast h
  have hbn0gt : 0 < kn := by
    have h := hcs (.gt (.var "n") (.int 0)) (by simp [rubi1113r26Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hen] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi1113r26Nondeg, Defined, eval, hem, hen, hep, Interp.toInt?_cast] at h0
  casesm* _ ∧ _
  have hc14 := hcs (.ne (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.int 0)) (by simp [rubi1113r26Nondeg])
  simp [Cond.Holds, Defined, eval] at hc14
  try simp only [hem] at hc14
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc14, hem]
  · simp [eval, Ok, Expr.varList, hm1, hc14, hem, hqm2, hen, hep, hqp2, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [Defined, eval, hm1, hc14, hem, hqm2, hen, hep, hqp2, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [Calc.real, rubi1113r26Nondeg, eval, Ok, Expr.varList, hem, hqm2, hen, hqn1, hep, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [rubi1113r26Nondeg, Defined, eval, hem, hqm2, hen, hqn1, hep, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [rubi1113r26Nondeg, eval, d, hm1, hm11, hem, hqm2, hen, hqn1, hep, hqp2, Interp.toInt?_cast]
    try have hqmm30 : (km : ℝ) - 3 ≠ 0 := by exact_mod_cast (show km - 3 ≠ 0 by omega)
    try have hqmm20 : (km : ℝ) - 2 ≠ 0 := by exact_mod_cast (show km - 2 ≠ 0 by omega)
    try have hqmm10 : (km : ℝ) - 1 ≠ 0 := by exact_mod_cast (show km - 1 ≠ 0 by omega)
    try have hqmp00 : (km : ℝ) ≠ 0 := by exact_mod_cast (show km ≠ 0 by omega)
    try have hqmp10 : (km : ℝ) + 1 ≠ 0 := by exact_mod_cast (show km + 1 ≠ 0 by omega)
    try have hqnp00 : (kn : ℝ) ≠ 0 := by exact_mod_cast (show kn ≠ 0 by omega)
    try have hqnp10 : (kn : ℝ) + 1 ≠ 0 := by exact_mod_cast (show kn + 1 ≠ 0 by omega)
    try have hqnp20 : (kn : ℝ) + 2 ≠ 0 := by exact_mod_cast (show kn + 2 ≠ 0 by omega)
    try have hqnp30 : (kn : ℝ) + 3 ≠ 0 := by exact_mod_cast (show kn + 3 ≠ 0 by omega)
    have hz0 : (env "a" + (env "b" * t)) ≠ 0 ∨ 0 ≤ km := by
      rcases lt_or_ge (km) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show (env "a" + (env "b" * t)) ^ (km + 1) = (env "a" + (env "b" * t)) ^ (km) * (env "a" + (env "b" * t)) ^ 1 from by
      have := zsplit ((env "a" + (env "b" * t))) (km) 1 hz0
      rwa [show km + ((1 : ℕ) : ℤ) = km + 1 by push_cast; ring] at this]
    try generalize (env "a" + (env "b" * t)) ^ (km) = P0
    have hz1 : (env "c" + (env "d" * t)) ≠ 0 ∨ 0 ≤ kn + -1 := by
      exact Or.inr (by omega)
    try rw [show (env "c" + (env "d" * t)) ^ (kn) = (env "c" + (env "d" * t)) ^ (kn + -1) * (env "c" + (env "d" * t)) ^ 1 from by
      have := zsplit ((env "c" + (env "d" * t))) (kn + -1) 1 hz1
      rwa [show kn + -1 + ((1 : ℕ) : ℤ) = kn by push_cast; ring] at this]
    try generalize (env "c" + (env "d" * t)) ^ (kn + -1) = P1
    have hz2 : (env "e" + (env "f" * t)) ≠ 0 ∨ 0 ≤ kp := by
      rcases lt_or_ge (kp) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show (env "e" + (env "f" * t)) ^ (kp + 1) = (env "e" + (env "f" * t)) ^ (kp) * (env "e" + (env "f" * t)) ^ 1 from by
      have := zsplit ((env "e" + (env "f" * t))) (kp) 1 hz2
      rwa [show kp + ((1 : ℕ) : ℤ) = kp + 1 by push_cast; ring] at this]
    try generalize (env "e" + (env "f" * t)) ^ (kp) = P2
    try casesm* _ ∧ _
    try field_simp
    try ring

set_option maxHeartbeats 1000000 in
/-- RUBI rubi1113r26Nondeg: explicit term by the symbolic derivative. -/
theorem rubi1113r26Nondeg_complex : rubi1113r26Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1113r26Nondeg.conditions rubi1113r26Nondeg.body rubi1113r26Nondeg.result rubi1113r26Nondeg.integrals
  have hm1 : Interp.complex.toInt? (-1 : ℂ) = some (-1) := by simpa using Interp.toInt?_cast Interp.complex (-1)
  have hm2 : Interp.complex.toInt? (-2 : ℂ) = some (-2) := by simpa using Interp.toInt?_cast Interp.complex (-2)
  have h2 : Interp.complex.toInt? (2 : ℂ) = some 2 := by simpa using Interp.toInt?_cast Interp.complex 2
  have hm11 : Interp.complex.toInt? (-1 + -1 : ℂ) = some (-2) := by
    rw [show (-1 + -1 : ℂ) = -2 by norm_num]; exact hm2
  have dln : ∀ z : ℂ, Interp.complex.lnDefined z ↔ z ≠ 0 := fun _ => Iff.rfl
  have dtan : ∀ z : ℂ, Interp.complex.tanDefined z ↔ Complex.cos z ≠ 0 := fun _ => Iff.rfl
  refine antiderivRec_open Calc.complex _ (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n"))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.int (-1)))) (rubi1113r26Nondeg.integrals.head!.2) (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.int (-1)))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.complex.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1113r26Nondeg, Defined, eval, hkm] at h0
  have hem : env "m" = (km : ℂ) := (Interp.complex.toInt?_eq _ _).1 hkm
  have hom1 : Interp.complex.toInt? ((-1 : ℂ) + (km : ℂ)) = some (-1 + km) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm1 : Interp.complex.toInt? ((km : ℂ) + (-1 : ℂ)) = some (km + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hom2 : Interp.complex.toInt? ((1 : ℂ) + (km : ℂ)) = some (1 + km) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm2 : Interp.complex.toInt? ((km : ℂ) + (1 : ℂ)) = some (km + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hom3 : Interp.complex.toInt? ((-2 : ℂ) + (km : ℂ)) = some (-2 + km) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm3 : Interp.complex.toInt? ((km : ℂ) + (-2 : ℂ)) = some (km + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hom4 : Interp.complex.toInt? ((2 : ℂ) + (km : ℂ)) = some (2 + km) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm4 : Interp.complex.toInt? ((km : ℂ) + (2 : ℂ)) = some (km + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm1 : Interp.complex.toInt? ((km : ℂ) - 1) = some (km - 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm2 : Interp.complex.toInt? ((km : ℂ) - 2) = some (km - 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hkmp1 : Interp.complex.toInt? (env "m" + 1) = some (km + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmp2 : Interp.complex.toInt? (env "m" + 2) = some (km + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm1 : Interp.complex.toInt? (env "m" + -1) = some (km + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm2 : Interp.complex.toInt? (env "m" + -2) = some (km + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkm]; push_cast; ring)
  rcases hkn : Interp.complex.toInt? (env "n") with _ | kn
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1113r26Nondeg, Defined, eval, hkn] at h0
  have hen : env "n" = (kn : ℂ) := (Interp.complex.toInt?_eq _ _).1 hkn
  have hon1 : Interp.complex.toInt? ((-1 : ℂ) + (kn : ℂ)) = some (-1 + kn) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn1 : Interp.complex.toInt? ((kn : ℂ) + (-1 : ℂ)) = some (kn + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hon2 : Interp.complex.toInt? ((1 : ℂ) + (kn : ℂ)) = some (1 + kn) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn2 : Interp.complex.toInt? ((kn : ℂ) + (1 : ℂ)) = some (kn + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hon3 : Interp.complex.toInt? ((-2 : ℂ) + (kn : ℂ)) = some (-2 + kn) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn3 : Interp.complex.toInt? ((kn : ℂ) + (-2 : ℂ)) = some (kn + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hon4 : Interp.complex.toInt? ((2 : ℂ) + (kn : ℂ)) = some (2 + kn) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn4 : Interp.complex.toInt? ((kn : ℂ) + (2 : ℂ)) = some (kn + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn1 : Interp.complex.toInt? ((kn : ℂ) - 1) = some (kn - 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn2 : Interp.complex.toInt? ((kn : ℂ) - 2) = some (kn - 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hknp1 : Interp.complex.toInt? (env "n" + 1) = some (kn + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknp2 : Interp.complex.toInt? (env "n" + 2) = some (kn + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm1 : Interp.complex.toInt? (env "n" + -1) = some (kn + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm2 : Interp.complex.toInt? (env "n" + -2) = some (kn + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkn]; push_cast; ring)
  rcases hkp : Interp.complex.toInt? (env "p") with _ | kp
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1113r26Nondeg, Defined, eval, hkp] at h0
  have hep : env "p" = (kp : ℂ) := (Interp.complex.toInt?_eq _ _).1 hkp
  have hop1 : Interp.complex.toInt? ((-1 : ℂ) + (kp : ℂ)) = some (-1 + kp) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp1 : Interp.complex.toInt? ((kp : ℂ) + (-1 : ℂ)) = some (kp + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hop2 : Interp.complex.toInt? ((1 : ℂ) + (kp : ℂ)) = some (1 + kp) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp2 : Interp.complex.toInt? ((kp : ℂ) + (1 : ℂ)) = some (kp + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hop3 : Interp.complex.toInt? ((-2 : ℂ) + (kp : ℂ)) = some (-2 + kp) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp3 : Interp.complex.toInt? ((kp : ℂ) + (-2 : ℂ)) = some (kp + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hop4 : Interp.complex.toInt? ((2 : ℂ) + (kp : ℂ)) = some (2 + kp) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp4 : Interp.complex.toInt? ((kp : ℂ) + (2 : ℂ)) = some (kp + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsp1 : Interp.complex.toInt? ((kp : ℂ) - 1) = some (kp - 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsp2 : Interp.complex.toInt? ((kp : ℂ) - 2) = some (kp - 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hkpp1 : Interp.complex.toInt? (env "p" + 1) = some (kp + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpp2 : Interp.complex.toInt? (env "p" + 2) = some (kp + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm1 : Interp.complex.toInt? (env "p" + -1) = some (kp + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm2 : Interp.complex.toInt? (env "p" + -2) = some (kp + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hbm1gt : km < -1 := by
    have h := hcs (.gt (.int (-1)) (.var "m")) (by simp [rubi1113r26Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, hem, Complex.ext_iff] at h
    exact_mod_cast h
  have hbn0gt : 0 < kn := by
    have h := hcs (.gt (.var "n") (.int 0)) (by simp [rubi1113r26Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, hen, Complex.ext_iff] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi1113r26Nondeg, Defined, eval, hem, hen, hep, Interp.toInt?_cast] at h0
  casesm* _ ∧ _
  have hc14 := hcs (.ne (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.int 0)) (by simp [rubi1113r26Nondeg])
  simp [Cond.Holds, Defined, eval] at hc14
  try simp only [hem] at hc14
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc14, hem]
  · simp [eval, Ok, Expr.varList, hm1, hc14, hem, hqm2, hen, hep, hqp2, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [Defined, eval, hm1, hc14, hem, hqm2, hen, hep, hqp2, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [Calc.complex, rubi1113r26Nondeg, eval, Ok, Expr.varList, hem, hqm2, hen, hqn1, hep, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [rubi1113r26Nondeg, Defined, eval, hem, hqm2, hen, hqn1, hep, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [rubi1113r26Nondeg, eval, d, hm1, hm11, hem, hqm2, hen, hqn1, hep, hqp2, Interp.toInt?_cast]
    try have hqmm30 : (km : ℂ) - 3 ≠ 0 := by exact_mod_cast (show km - 3 ≠ 0 by omega)
    try have hqmm20 : (km : ℂ) - 2 ≠ 0 := by exact_mod_cast (show km - 2 ≠ 0 by omega)
    try have hqmm10 : (km : ℂ) - 1 ≠ 0 := by exact_mod_cast (show km - 1 ≠ 0 by omega)
    try have hqmp00 : (km : ℂ) ≠ 0 := by exact_mod_cast (show km ≠ 0 by omega)
    try have hqmp10 : (km : ℂ) + 1 ≠ 0 := by exact_mod_cast (show km + 1 ≠ 0 by omega)
    try have hqnp00 : (kn : ℂ) ≠ 0 := by exact_mod_cast (show kn ≠ 0 by omega)
    try have hqnp10 : (kn : ℂ) + 1 ≠ 0 := by exact_mod_cast (show kn + 1 ≠ 0 by omega)
    try have hqnp20 : (kn : ℂ) + 2 ≠ 0 := by exact_mod_cast (show kn + 2 ≠ 0 by omega)
    try have hqnp30 : (kn : ℂ) + 3 ≠ 0 := by exact_mod_cast (show kn + 3 ≠ 0 by omega)
    have hz0 : (env "a" + (env "b" * t)) ≠ 0 ∨ 0 ≤ km := by
      rcases lt_or_ge (km) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show (env "a" + (env "b" * t)) ^ (km + 1) = (env "a" + (env "b" * t)) ^ (km) * (env "a" + (env "b" * t)) ^ 1 from by
      have := zsplit ((env "a" + (env "b" * t))) (km) 1 hz0
      rwa [show km + ((1 : ℕ) : ℤ) = km + 1 by push_cast; ring] at this]
    try generalize (env "a" + (env "b" * t)) ^ (km) = P0
    have hz1 : (env "c" + (env "d" * t)) ≠ 0 ∨ 0 ≤ kn + -1 := by
      exact Or.inr (by omega)
    try rw [show (env "c" + (env "d" * t)) ^ (kn) = (env "c" + (env "d" * t)) ^ (kn + -1) * (env "c" + (env "d" * t)) ^ 1 from by
      have := zsplit ((env "c" + (env "d" * t))) (kn + -1) 1 hz1
      rwa [show kn + -1 + ((1 : ℕ) : ℤ) = kn by push_cast; ring] at this]
    try generalize (env "c" + (env "d" * t)) ^ (kn + -1) = P1
    have hz2 : (env "e" + (env "f" * t)) ≠ 0 ∨ 0 ≤ kp := by
      rcases lt_or_ge (kp) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show (env "e" + (env "f" * t)) ^ (kp + 1) = (env "e" + (env "f" * t)) ^ (kp) * (env "e" + (env "f" * t)) ^ 1 from by
      have := zsplit ((env "e" + (env "f" * t))) (kp) 1 hz2
      rwa [show kp + ((1 : ℕ) : ℤ) = kp + 1 by push_cast; ring] at this]
    try generalize (env "e" + (env "f" * t)) ^ (kp) = P2
    try casesm* _ ∧ _
    try field_simp
    try ring

set_option maxHeartbeats 1000000 in
/-- RUBI rubi1113r28Nondeg: explicit term by the symbolic derivative. -/
theorem rubi1113r28Nondeg_real : rubi1113r28Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1113r28Nondeg.conditions rubi1113r28Nondeg.body rubi1113r28Nondeg.result rubi1113r28Nondeg.integrals
  have hm1 : Interp.real.toInt? (-1 : ℝ) = some (-1) := by simpa using Interp.toInt?_cast Interp.real (-1)
  have hm2 : Interp.real.toInt? (-2 : ℝ) = some (-2) := by simpa using Interp.toInt?_cast Interp.real (-2)
  have h2 : Interp.real.toInt? (2 : ℝ) = some 2 := by simpa using Interp.toInt?_cast Interp.real 2
  have hm11 : Interp.real.toInt? (-1 + -1 : ℝ) = some (-2) := by
    rw [show (-1 + -1 : ℝ) = -2 by norm_num]; exact hm2
  have dln : ∀ z : ℝ, Interp.real.lnDefined z ↔ 0 < z := fun _ => Iff.rfl
  have dtan : ∀ z : ℝ, Interp.real.tanDefined z ↔ Real.cos z ≠ 0 := fun _ => Iff.rfl
  have dasin : ∀ z : ℝ, Interp.real.fnDefined .arcsin z ↔ -1 ≤ z ∧ z ≤ 1 := fun _ => Iff.rfl
  have dacos : ∀ z : ℝ, Interp.real.fnDefined .arccos z ↔ -1 ≤ z ∧ z ≤ 1 := fun _ => Iff.rfl
  refine antiderivRec_open Calc.real _ (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n"))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.var "f") (.app2 .add (.app2 .add (.app2 .add (.var "m") (.var "n")) (.var "p")) (.int 1))) (.int (-1)))) (rubi1113r28Nondeg.integrals.head!.2) (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.app2 .mul (.var "f") (.app2 .add (.app2 .add (.app2 .add (.var "m") (.var "n")) (.var "p")) (.int 1))) (.int (-1)))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.real.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1113r28Nondeg, Defined, eval, hkm] at h0
  have hem : env "m" = (km : ℝ) := (Interp.real.toInt?_eq _ _).1 hkm
  have hom1 : Interp.real.toInt? ((-1 : ℝ) + (km : ℝ)) = some (-1 + km) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm1 : Interp.real.toInt? ((km : ℝ) + (-1 : ℝ)) = some (km + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hom2 : Interp.real.toInt? ((1 : ℝ) + (km : ℝ)) = some (1 + km) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm2 : Interp.real.toInt? ((km : ℝ) + (1 : ℝ)) = some (km + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hom3 : Interp.real.toInt? ((-2 : ℝ) + (km : ℝ)) = some (-2 + km) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm3 : Interp.real.toInt? ((km : ℝ) + (-2 : ℝ)) = some (km + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hom4 : Interp.real.toInt? ((2 : ℝ) + (km : ℝ)) = some (2 + km) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm4 : Interp.real.toInt? ((km : ℝ) + (2 : ℝ)) = some (km + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm1 : Interp.real.toInt? ((km : ℝ) - 1) = some (km - 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm2 : Interp.real.toInt? ((km : ℝ) - 2) = some (km - 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hkmp1 : Interp.real.toInt? (env "m" + 1) = some (km + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmp2 : Interp.real.toInt? (env "m" + 2) = some (km + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm1 : Interp.real.toInt? (env "m" + -1) = some (km + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm2 : Interp.real.toInt? (env "m" + -2) = some (km + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkm]; push_cast; ring)
  rcases hkn : Interp.real.toInt? (env "n") with _ | kn
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1113r28Nondeg, Defined, eval, hkn] at h0
  have hen : env "n" = (kn : ℝ) := (Interp.real.toInt?_eq _ _).1 hkn
  have hon1 : Interp.real.toInt? ((-1 : ℝ) + (kn : ℝ)) = some (-1 + kn) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn1 : Interp.real.toInt? ((kn : ℝ) + (-1 : ℝ)) = some (kn + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hon2 : Interp.real.toInt? ((1 : ℝ) + (kn : ℝ)) = some (1 + kn) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn2 : Interp.real.toInt? ((kn : ℝ) + (1 : ℝ)) = some (kn + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hon3 : Interp.real.toInt? ((-2 : ℝ) + (kn : ℝ)) = some (-2 + kn) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn3 : Interp.real.toInt? ((kn : ℝ) + (-2 : ℝ)) = some (kn + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hon4 : Interp.real.toInt? ((2 : ℝ) + (kn : ℝ)) = some (2 + kn) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn4 : Interp.real.toInt? ((kn : ℝ) + (2 : ℝ)) = some (kn + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn1 : Interp.real.toInt? ((kn : ℝ) - 1) = some (kn - 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn2 : Interp.real.toInt? ((kn : ℝ) - 2) = some (kn - 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hknp1 : Interp.real.toInt? (env "n" + 1) = some (kn + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknp2 : Interp.real.toInt? (env "n" + 2) = some (kn + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm1 : Interp.real.toInt? (env "n" + -1) = some (kn + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm2 : Interp.real.toInt? (env "n" + -2) = some (kn + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkn]; push_cast; ring)
  rcases hkp : Interp.real.toInt? (env "p") with _ | kp
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1113r28Nondeg, Defined, eval, hkp] at h0
  have hep : env "p" = (kp : ℝ) := (Interp.real.toInt?_eq _ _).1 hkp
  have hop1 : Interp.real.toInt? ((-1 : ℝ) + (kp : ℝ)) = some (-1 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp1 : Interp.real.toInt? ((kp : ℝ) + (-1 : ℝ)) = some (kp + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hop2 : Interp.real.toInt? ((1 : ℝ) + (kp : ℝ)) = some (1 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp2 : Interp.real.toInt? ((kp : ℝ) + (1 : ℝ)) = some (kp + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hop3 : Interp.real.toInt? ((-2 : ℝ) + (kp : ℝ)) = some (-2 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp3 : Interp.real.toInt? ((kp : ℝ) + (-2 : ℝ)) = some (kp + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hop4 : Interp.real.toInt? ((2 : ℝ) + (kp : ℝ)) = some (2 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp4 : Interp.real.toInt? ((kp : ℝ) + (2 : ℝ)) = some (kp + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsp1 : Interp.real.toInt? ((kp : ℝ) - 1) = some (kp - 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsp2 : Interp.real.toInt? ((kp : ℝ) - 2) = some (kp - 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hkpp1 : Interp.real.toInt? (env "p" + 1) = some (kp + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpp2 : Interp.real.toInt? (env "p" + 2) = some (kp + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm1 : Interp.real.toInt? (env "p" + -1) = some (kp + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm2 : Interp.real.toInt? (env "p" + -2) = some (kp + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hbm0gt : 0 < km := by
    have h := hcs (.gt (.var "m") (.int 0)) (by simp [rubi1113r28Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hem] at h
    exact_mod_cast h
  have hbn0gt : 0 < kn := by
    have h := hcs (.gt (.var "n") (.int 0)) (by simp [rubi1113r28Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hen] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi1113r28Nondeg, Defined, eval, hem, hen, hep, Interp.toInt?_cast] at h0
  casesm* _ ∧ _
  have hc2 := hcs (.ne (.app2 .add (.app2 .add (.app2 .add (.var "m") (.var "n")) (.var "p")) (.int 1)) (.int 0)) (by simp [rubi1113r28Nondeg])
  simp [Cond.Holds, Defined, eval] at hc2
  have hc15 := hcs (.ne (.app2 .mul (.var "f") (.app2 .add (.app2 .add (.app2 .add (.var "m") (.var "n")) (.var "p")) (.int 1))) (.int 0)) (by simp [rubi1113r28Nondeg])
  simp [Cond.Holds, Defined, eval] at hc15
  try simp only [hem, hen, hep] at hc2 hc15
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc2, hc15, hem, hen, hep]
  · simp [eval, Ok, Expr.varList, hm1, hc2, hc15, hem, hen, hep, hqp2, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [Defined, eval, hm1, hc2, hc15, hem, hen, hep, hqp2, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [Calc.real, rubi1113r28Nondeg, eval, Ok, Expr.varList, hem, hqm1, hen, hqn1, hep, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [rubi1113r28Nondeg, Defined, eval, hem, hqm1, hen, hqn1, hep, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [rubi1113r28Nondeg, eval, d, hm1, hm11, hem, hqm1, hen, hqn1, hep, hqp2, Interp.toInt?_cast]
    try have hqmp00 : (km : ℝ) ≠ 0 := by exact_mod_cast (show km ≠ 0 by omega)
    try have hqmp10 : (km : ℝ) + 1 ≠ 0 := by exact_mod_cast (show km + 1 ≠ 0 by omega)
    try have hqmp20 : (km : ℝ) + 2 ≠ 0 := by exact_mod_cast (show km + 2 ≠ 0 by omega)
    try have hqmp30 : (km : ℝ) + 3 ≠ 0 := by exact_mod_cast (show km + 3 ≠ 0 by omega)
    try have hqnp00 : (kn : ℝ) ≠ 0 := by exact_mod_cast (show kn ≠ 0 by omega)
    try have hqnp10 : (kn : ℝ) + 1 ≠ 0 := by exact_mod_cast (show kn + 1 ≠ 0 by omega)
    try have hqnp20 : (kn : ℝ) + 2 ≠ 0 := by exact_mod_cast (show kn + 2 ≠ 0 by omega)
    try have hqnp30 : (kn : ℝ) + 3 ≠ 0 := by exact_mod_cast (show kn + 3 ≠ 0 by omega)
    have hz0 : (env "a" + (env "b" * t)) ≠ 0 ∨ 0 ≤ km + -1 := by
      exact Or.inr (by omega)
    try rw [show (env "a" + (env "b" * t)) ^ (km) = (env "a" + (env "b" * t)) ^ (km + -1) * (env "a" + (env "b" * t)) ^ 1 from by
      have := zsplit ((env "a" + (env "b" * t))) (km + -1) 1 hz0
      rwa [show km + -1 + ((1 : ℕ) : ℤ) = km by push_cast; ring] at this]
    try generalize (env "a" + (env "b" * t)) ^ (km + -1) = P0
    have hz1 : (env "c" + (env "d" * t)) ≠ 0 ∨ 0 ≤ kn + -1 := by
      exact Or.inr (by omega)
    try rw [show (env "c" + (env "d" * t)) ^ (kn) = (env "c" + (env "d" * t)) ^ (kn + -1) * (env "c" + (env "d" * t)) ^ 1 from by
      have := zsplit ((env "c" + (env "d" * t))) (kn + -1) 1 hz1
      rwa [show kn + -1 + ((1 : ℕ) : ℤ) = kn by push_cast; ring] at this]
    try generalize (env "c" + (env "d" * t)) ^ (kn + -1) = P1
    have hz2 : (env "e" + (env "f" * t)) ≠ 0 ∨ 0 ≤ kp := by
      rcases lt_or_ge (kp) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show (env "e" + (env "f" * t)) ^ (kp + 1) = (env "e" + (env "f" * t)) ^ (kp) * (env "e" + (env "f" * t)) ^ 1 from by
      have := zsplit ((env "e" + (env "f" * t))) (kp) 1 hz2
      rwa [show kp + ((1 : ℕ) : ℤ) = kp + 1 by push_cast; ring] at this]
    try generalize (env "e" + (env "f" * t)) ^ (kp) = P2
    try casesm* _ ∧ _
    try field_simp
    try ring

set_option maxHeartbeats 1000000 in
/-- RUBI rubi1113r28Nondeg: explicit term by the symbolic derivative. -/
theorem rubi1113r28Nondeg_complex : rubi1113r28Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1113r28Nondeg.conditions rubi1113r28Nondeg.body rubi1113r28Nondeg.result rubi1113r28Nondeg.integrals
  have hm1 : Interp.complex.toInt? (-1 : ℂ) = some (-1) := by simpa using Interp.toInt?_cast Interp.complex (-1)
  have hm2 : Interp.complex.toInt? (-2 : ℂ) = some (-2) := by simpa using Interp.toInt?_cast Interp.complex (-2)
  have h2 : Interp.complex.toInt? (2 : ℂ) = some 2 := by simpa using Interp.toInt?_cast Interp.complex 2
  have hm11 : Interp.complex.toInt? (-1 + -1 : ℂ) = some (-2) := by
    rw [show (-1 + -1 : ℂ) = -2 by norm_num]; exact hm2
  have dln : ∀ z : ℂ, Interp.complex.lnDefined z ↔ z ≠ 0 := fun _ => Iff.rfl
  have dtan : ∀ z : ℂ, Interp.complex.tanDefined z ↔ Complex.cos z ≠ 0 := fun _ => Iff.rfl
  refine antiderivRec_open Calc.complex _ (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n"))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.var "f") (.app2 .add (.app2 .add (.app2 .add (.var "m") (.var "n")) (.var "p")) (.int 1))) (.int (-1)))) (rubi1113r28Nondeg.integrals.head!.2) (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.app2 .mul (.var "f") (.app2 .add (.app2 .add (.app2 .add (.var "m") (.var "n")) (.var "p")) (.int 1))) (.int (-1)))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.complex.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1113r28Nondeg, Defined, eval, hkm] at h0
  have hem : env "m" = (km : ℂ) := (Interp.complex.toInt?_eq _ _).1 hkm
  have hom1 : Interp.complex.toInt? ((-1 : ℂ) + (km : ℂ)) = some (-1 + km) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm1 : Interp.complex.toInt? ((km : ℂ) + (-1 : ℂ)) = some (km + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hom2 : Interp.complex.toInt? ((1 : ℂ) + (km : ℂ)) = some (1 + km) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm2 : Interp.complex.toInt? ((km : ℂ) + (1 : ℂ)) = some (km + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hom3 : Interp.complex.toInt? ((-2 : ℂ) + (km : ℂ)) = some (-2 + km) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm3 : Interp.complex.toInt? ((km : ℂ) + (-2 : ℂ)) = some (km + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hom4 : Interp.complex.toInt? ((2 : ℂ) + (km : ℂ)) = some (2 + km) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm4 : Interp.complex.toInt? ((km : ℂ) + (2 : ℂ)) = some (km + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm1 : Interp.complex.toInt? ((km : ℂ) - 1) = some (km - 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm2 : Interp.complex.toInt? ((km : ℂ) - 2) = some (km - 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hkmp1 : Interp.complex.toInt? (env "m" + 1) = some (km + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmp2 : Interp.complex.toInt? (env "m" + 2) = some (km + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm1 : Interp.complex.toInt? (env "m" + -1) = some (km + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm2 : Interp.complex.toInt? (env "m" + -2) = some (km + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkm]; push_cast; ring)
  rcases hkn : Interp.complex.toInt? (env "n") with _ | kn
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1113r28Nondeg, Defined, eval, hkn] at h0
  have hen : env "n" = (kn : ℂ) := (Interp.complex.toInt?_eq _ _).1 hkn
  have hon1 : Interp.complex.toInt? ((-1 : ℂ) + (kn : ℂ)) = some (-1 + kn) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn1 : Interp.complex.toInt? ((kn : ℂ) + (-1 : ℂ)) = some (kn + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hon2 : Interp.complex.toInt? ((1 : ℂ) + (kn : ℂ)) = some (1 + kn) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn2 : Interp.complex.toInt? ((kn : ℂ) + (1 : ℂ)) = some (kn + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hon3 : Interp.complex.toInt? ((-2 : ℂ) + (kn : ℂ)) = some (-2 + kn) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn3 : Interp.complex.toInt? ((kn : ℂ) + (-2 : ℂ)) = some (kn + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hon4 : Interp.complex.toInt? ((2 : ℂ) + (kn : ℂ)) = some (2 + kn) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn4 : Interp.complex.toInt? ((kn : ℂ) + (2 : ℂ)) = some (kn + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn1 : Interp.complex.toInt? ((kn : ℂ) - 1) = some (kn - 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn2 : Interp.complex.toInt? ((kn : ℂ) - 2) = some (kn - 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hknp1 : Interp.complex.toInt? (env "n" + 1) = some (kn + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknp2 : Interp.complex.toInt? (env "n" + 2) = some (kn + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm1 : Interp.complex.toInt? (env "n" + -1) = some (kn + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm2 : Interp.complex.toInt? (env "n" + -2) = some (kn + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkn]; push_cast; ring)
  rcases hkp : Interp.complex.toInt? (env "p") with _ | kp
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1113r28Nondeg, Defined, eval, hkp] at h0
  have hep : env "p" = (kp : ℂ) := (Interp.complex.toInt?_eq _ _).1 hkp
  have hop1 : Interp.complex.toInt? ((-1 : ℂ) + (kp : ℂ)) = some (-1 + kp) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp1 : Interp.complex.toInt? ((kp : ℂ) + (-1 : ℂ)) = some (kp + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hop2 : Interp.complex.toInt? ((1 : ℂ) + (kp : ℂ)) = some (1 + kp) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp2 : Interp.complex.toInt? ((kp : ℂ) + (1 : ℂ)) = some (kp + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hop3 : Interp.complex.toInt? ((-2 : ℂ) + (kp : ℂ)) = some (-2 + kp) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp3 : Interp.complex.toInt? ((kp : ℂ) + (-2 : ℂ)) = some (kp + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hop4 : Interp.complex.toInt? ((2 : ℂ) + (kp : ℂ)) = some (2 + kp) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp4 : Interp.complex.toInt? ((kp : ℂ) + (2 : ℂ)) = some (kp + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsp1 : Interp.complex.toInt? ((kp : ℂ) - 1) = some (kp - 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsp2 : Interp.complex.toInt? ((kp : ℂ) - 2) = some (kp - 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hkpp1 : Interp.complex.toInt? (env "p" + 1) = some (kp + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpp2 : Interp.complex.toInt? (env "p" + 2) = some (kp + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm1 : Interp.complex.toInt? (env "p" + -1) = some (kp + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm2 : Interp.complex.toInt? (env "p" + -2) = some (kp + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hbm0gt : 0 < km := by
    have h := hcs (.gt (.var "m") (.int 0)) (by simp [rubi1113r28Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, hem, Complex.ext_iff] at h
    exact_mod_cast h
  have hbn0gt : 0 < kn := by
    have h := hcs (.gt (.var "n") (.int 0)) (by simp [rubi1113r28Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, hen, Complex.ext_iff] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi1113r28Nondeg, Defined, eval, hem, hen, hep, Interp.toInt?_cast] at h0
  casesm* _ ∧ _
  have hc2 := hcs (.ne (.app2 .add (.app2 .add (.app2 .add (.var "m") (.var "n")) (.var "p")) (.int 1)) (.int 0)) (by simp [rubi1113r28Nondeg])
  simp [Cond.Holds, Defined, eval] at hc2
  have hc15 := hcs (.ne (.app2 .mul (.var "f") (.app2 .add (.app2 .add (.app2 .add (.var "m") (.var "n")) (.var "p")) (.int 1))) (.int 0)) (by simp [rubi1113r28Nondeg])
  simp [Cond.Holds, Defined, eval] at hc15
  try simp only [hem, hen, hep] at hc2 hc15
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc2, hc15, hem, hen, hep]
  · simp [eval, Ok, Expr.varList, hm1, hc2, hc15, hem, hen, hep, hqp2, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [Defined, eval, hm1, hc2, hc15, hem, hen, hep, hqp2, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [Calc.complex, rubi1113r28Nondeg, eval, Ok, Expr.varList, hem, hqm1, hen, hqn1, hep, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [rubi1113r28Nondeg, Defined, eval, hem, hqm1, hen, hqn1, hep, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [rubi1113r28Nondeg, eval, d, hm1, hm11, hem, hqm1, hen, hqn1, hep, hqp2, Interp.toInt?_cast]
    try have hqmp00 : (km : ℂ) ≠ 0 := by exact_mod_cast (show km ≠ 0 by omega)
    try have hqmp10 : (km : ℂ) + 1 ≠ 0 := by exact_mod_cast (show km + 1 ≠ 0 by omega)
    try have hqmp20 : (km : ℂ) + 2 ≠ 0 := by exact_mod_cast (show km + 2 ≠ 0 by omega)
    try have hqmp30 : (km : ℂ) + 3 ≠ 0 := by exact_mod_cast (show km + 3 ≠ 0 by omega)
    try have hqnp00 : (kn : ℂ) ≠ 0 := by exact_mod_cast (show kn ≠ 0 by omega)
    try have hqnp10 : (kn : ℂ) + 1 ≠ 0 := by exact_mod_cast (show kn + 1 ≠ 0 by omega)
    try have hqnp20 : (kn : ℂ) + 2 ≠ 0 := by exact_mod_cast (show kn + 2 ≠ 0 by omega)
    try have hqnp30 : (kn : ℂ) + 3 ≠ 0 := by exact_mod_cast (show kn + 3 ≠ 0 by omega)
    have hz0 : (env "a" + (env "b" * t)) ≠ 0 ∨ 0 ≤ km + -1 := by
      exact Or.inr (by omega)
    try rw [show (env "a" + (env "b" * t)) ^ (km) = (env "a" + (env "b" * t)) ^ (km + -1) * (env "a" + (env "b" * t)) ^ 1 from by
      have := zsplit ((env "a" + (env "b" * t))) (km + -1) 1 hz0
      rwa [show km + -1 + ((1 : ℕ) : ℤ) = km by push_cast; ring] at this]
    try generalize (env "a" + (env "b" * t)) ^ (km + -1) = P0
    have hz1 : (env "c" + (env "d" * t)) ≠ 0 ∨ 0 ≤ kn + -1 := by
      exact Or.inr (by omega)
    try rw [show (env "c" + (env "d" * t)) ^ (kn) = (env "c" + (env "d" * t)) ^ (kn + -1) * (env "c" + (env "d" * t)) ^ 1 from by
      have := zsplit ((env "c" + (env "d" * t))) (kn + -1) 1 hz1
      rwa [show kn + -1 + ((1 : ℕ) : ℤ) = kn by push_cast; ring] at this]
    try generalize (env "c" + (env "d" * t)) ^ (kn + -1) = P1
    have hz2 : (env "e" + (env "f" * t)) ≠ 0 ∨ 0 ≤ kp := by
      rcases lt_or_ge (kp) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show (env "e" + (env "f" * t)) ^ (kp + 1) = (env "e" + (env "f" * t)) ^ (kp) * (env "e" + (env "f" * t)) ^ 1 from by
      have := zsplit ((env "e" + (env "f" * t))) (kp) 1 hz2
      rwa [show kp + ((1 : ℕ) : ℤ) = kp + 1 by push_cast; ring] at this]
    try generalize (env "e" + (env "f" * t)) ^ (kp) = P2
    try casesm* _ ∧ _
    try field_simp
    try ring

set_option maxHeartbeats 1000000 in
/-- RUBI rubi1114r10Nondeg: explicit term by the symbolic derivative. -/
theorem rubi1114r10Nondeg_real : rubi1114r10Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1114r10Nondeg.conditions rubi1114r10Nondeg.body rubi1114r10Nondeg.result rubi1114r10Nondeg.integrals
  have hm1 : Interp.real.toInt? (-1 : ℝ) = some (-1) := by simpa using Interp.toInt?_cast Interp.real (-1)
  have hm2 : Interp.real.toInt? (-2 : ℝ) = some (-2) := by simpa using Interp.toInt?_cast Interp.real (-2)
  have h2 : Interp.real.toInt? (2 : ℝ) = some 2 := by simpa using Interp.toInt?_cast Interp.real 2
  have hm11 : Interp.real.toInt? (-1 + -1 : ℝ) = some (-2) := by
    rw [show (-1 + -1 : ℝ) = -2 by norm_num]; exact hm2
  have dln : ∀ z : ℝ, Interp.real.lnDefined z ↔ 0 < z := fun _ => Iff.rfl
  have dtan : ∀ z : ℝ, Interp.real.tanDefined z ↔ Real.cos z ≠ 0 := fun _ => Iff.rfl
  have dasin : ∀ z : ℝ, Interp.real.fnDefined .arcsin z ↔ -1 ≤ z ∧ z ≤ 1 := fun _ => Iff.rfl
  have dacos : ∀ z : ℝ, Interp.real.fnDefined .arccos z ↔ -1 ≤ z ∧ z ≤ 1 := fun _ => Iff.rfl
  refine antiderivRec_open Calc.real _ (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "g")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "h"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.int (-1)))) (rubi1114r10Nondeg.integrals.head!.2) (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.int (-1)))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.real.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1114r10Nondeg, Defined, eval, hkm] at h0
  have hem : env "m" = (km : ℝ) := (Interp.real.toInt?_eq _ _).1 hkm
  have hom1 : Interp.real.toInt? ((-1 : ℝ) + (km : ℝ)) = some (-1 + km) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm1 : Interp.real.toInt? ((km : ℝ) + (-1 : ℝ)) = some (km + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hom2 : Interp.real.toInt? ((1 : ℝ) + (km : ℝ)) = some (1 + km) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm2 : Interp.real.toInt? ((km : ℝ) + (1 : ℝ)) = some (km + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hom3 : Interp.real.toInt? ((-2 : ℝ) + (km : ℝ)) = some (-2 + km) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm3 : Interp.real.toInt? ((km : ℝ) + (-2 : ℝ)) = some (km + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hom4 : Interp.real.toInt? ((2 : ℝ) + (km : ℝ)) = some (2 + km) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm4 : Interp.real.toInt? ((km : ℝ) + (2 : ℝ)) = some (km + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm1 : Interp.real.toInt? ((km : ℝ) - 1) = some (km - 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm2 : Interp.real.toInt? ((km : ℝ) - 2) = some (km - 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hkmp1 : Interp.real.toInt? (env "m" + 1) = some (km + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmp2 : Interp.real.toInt? (env "m" + 2) = some (km + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm1 : Interp.real.toInt? (env "m" + -1) = some (km + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm2 : Interp.real.toInt? (env "m" + -2) = some (km + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkm]; push_cast; ring)
  rcases hkn : Interp.real.toInt? (env "n") with _ | kn
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1114r10Nondeg, Defined, eval, hkn] at h0
  have hen : env "n" = (kn : ℝ) := (Interp.real.toInt?_eq _ _).1 hkn
  have hon1 : Interp.real.toInt? ((-1 : ℝ) + (kn : ℝ)) = some (-1 + kn) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn1 : Interp.real.toInt? ((kn : ℝ) + (-1 : ℝ)) = some (kn + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hon2 : Interp.real.toInt? ((1 : ℝ) + (kn : ℝ)) = some (1 + kn) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn2 : Interp.real.toInt? ((kn : ℝ) + (1 : ℝ)) = some (kn + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hon3 : Interp.real.toInt? ((-2 : ℝ) + (kn : ℝ)) = some (-2 + kn) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn3 : Interp.real.toInt? ((kn : ℝ) + (-2 : ℝ)) = some (kn + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hon4 : Interp.real.toInt? ((2 : ℝ) + (kn : ℝ)) = some (2 + kn) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn4 : Interp.real.toInt? ((kn : ℝ) + (2 : ℝ)) = some (kn + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn1 : Interp.real.toInt? ((kn : ℝ) - 1) = some (kn - 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn2 : Interp.real.toInt? ((kn : ℝ) - 2) = some (kn - 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hknp1 : Interp.real.toInt? (env "n" + 1) = some (kn + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknp2 : Interp.real.toInt? (env "n" + 2) = some (kn + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm1 : Interp.real.toInt? (env "n" + -1) = some (kn + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm2 : Interp.real.toInt? (env "n" + -2) = some (kn + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkn]; push_cast; ring)
  rcases hkp : Interp.real.toInt? (env "p") with _ | kp
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1114r10Nondeg, Defined, eval, hkp] at h0
  have hep : env "p" = (kp : ℝ) := (Interp.real.toInt?_eq _ _).1 hkp
  have hop1 : Interp.real.toInt? ((-1 : ℝ) + (kp : ℝ)) = some (-1 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp1 : Interp.real.toInt? ((kp : ℝ) + (-1 : ℝ)) = some (kp + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hop2 : Interp.real.toInt? ((1 : ℝ) + (kp : ℝ)) = some (1 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp2 : Interp.real.toInt? ((kp : ℝ) + (1 : ℝ)) = some (kp + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hop3 : Interp.real.toInt? ((-2 : ℝ) + (kp : ℝ)) = some (-2 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp3 : Interp.real.toInt? ((kp : ℝ) + (-2 : ℝ)) = some (kp + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hop4 : Interp.real.toInt? ((2 : ℝ) + (kp : ℝ)) = some (2 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp4 : Interp.real.toInt? ((kp : ℝ) + (2 : ℝ)) = some (kp + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsp1 : Interp.real.toInt? ((kp : ℝ) - 1) = some (kp - 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsp2 : Interp.real.toInt? ((kp : ℝ) - 2) = some (kp - 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hkpp1 : Interp.real.toInt? (env "p" + 1) = some (kp + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpp2 : Interp.real.toInt? (env "p" + 2) = some (kp + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm1 : Interp.real.toInt? (env "p" + -1) = some (kp + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm2 : Interp.real.toInt? (env "p" + -2) = some (kp + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hbm1gt : km < -1 := by
    have h := hcs (.gt (.int (-1)) (.var "m")) (by simp [rubi1114r10Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hem] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi1114r10Nondeg, Defined, eval, hem, hen, hep, Interp.toInt?_cast] at h0
  casesm* _ ∧ _
  have hc2 := hcs (.ne (.app2 .mul (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.int 0)) (by simp [rubi1114r10Nondeg])
  simp [Cond.Holds, Defined, eval] at hc2
  try simp only [hem] at hc2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc2, hem]
  · simp [eval, Ok, Expr.varList, hm1, hc2, hem, hqm2, hen, hqn2, hep, hqp2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [Defined, eval, hm1, hc2, hem, hqm2, hen, hqn2, hep, hqp2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [Calc.real, rubi1114r10Nondeg, eval, Ok, Expr.varList, hem, hqm2, hen, hep, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [rubi1114r10Nondeg, Defined, eval, hem, hqm2, hen, hep, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [rubi1114r10Nondeg, eval, d, hm1, hm11, hem, hqm2, hen, hqn2, hep, hqp2, Interp.toInt?_cast]
    try have hqmm30 : (km : ℝ) - 3 ≠ 0 := by exact_mod_cast (show km - 3 ≠ 0 by omega)
    try have hqmm20 : (km : ℝ) - 2 ≠ 0 := by exact_mod_cast (show km - 2 ≠ 0 by omega)
    try have hqmm10 : (km : ℝ) - 1 ≠ 0 := by exact_mod_cast (show km - 1 ≠ 0 by omega)
    try have hqmp00 : (km : ℝ) ≠ 0 := by exact_mod_cast (show km ≠ 0 by omega)
    try have hqmp10 : (km : ℝ) + 1 ≠ 0 := by exact_mod_cast (show km + 1 ≠ 0 by omega)
    have hz0 : (env "a" + (env "b" * t)) ≠ 0 ∨ 0 ≤ km := by
      rcases lt_or_ge (km) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show (env "a" + (env "b" * t)) ^ (km + 1) = (env "a" + (env "b" * t)) ^ (km) * (env "a" + (env "b" * t)) ^ 1 from by
      have := zsplit ((env "a" + (env "b" * t))) (km) 1 hz0
      rwa [show km + ((1 : ℕ) : ℤ) = km + 1 by push_cast; ring] at this]
    try generalize (env "a" + (env "b" * t)) ^ (km) = P0
    have hz1 : (env "c" + (env "d" * t)) ≠ 0 ∨ 0 ≤ kn := by
      rcases lt_or_ge (kn) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show (env "c" + (env "d" * t)) ^ (kn + 1) = (env "c" + (env "d" * t)) ^ (kn) * (env "c" + (env "d" * t)) ^ 1 from by
      have := zsplit ((env "c" + (env "d" * t))) (kn) 1 hz1
      rwa [show kn + ((1 : ℕ) : ℤ) = kn + 1 by push_cast; ring] at this]
    try generalize (env "c" + (env "d" * t)) ^ (kn) = P1
    have hz2 : (env "e" + (env "f" * t)) ≠ 0 ∨ 0 ≤ kp := by
      rcases lt_or_ge (kp) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show (env "e" + (env "f" * t)) ^ (kp + 1) = (env "e" + (env "f" * t)) ^ (kp) * (env "e" + (env "f" * t)) ^ 1 from by
      have := zsplit ((env "e" + (env "f" * t))) (kp) 1 hz2
      rwa [show kp + ((1 : ℕ) : ℤ) = kp + 1 by push_cast; ring] at this]
    try generalize (env "e" + (env "f" * t)) ^ (kp) = P2
    try casesm* _ ∧ _
    try field_simp
    try ring

set_option maxHeartbeats 1000000 in
/-- RUBI rubi1114r10Nondeg: explicit term by the symbolic derivative. -/
theorem rubi1114r10Nondeg_complex : rubi1114r10Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1114r10Nondeg.conditions rubi1114r10Nondeg.body rubi1114r10Nondeg.result rubi1114r10Nondeg.integrals
  have hm1 : Interp.complex.toInt? (-1 : ℂ) = some (-1) := by simpa using Interp.toInt?_cast Interp.complex (-1)
  have hm2 : Interp.complex.toInt? (-2 : ℂ) = some (-2) := by simpa using Interp.toInt?_cast Interp.complex (-2)
  have h2 : Interp.complex.toInt? (2 : ℂ) = some 2 := by simpa using Interp.toInt?_cast Interp.complex 2
  have hm11 : Interp.complex.toInt? (-1 + -1 : ℂ) = some (-2) := by
    rw [show (-1 + -1 : ℂ) = -2 by norm_num]; exact hm2
  have dln : ∀ z : ℂ, Interp.complex.lnDefined z ↔ z ≠ 0 := fun _ => Iff.rfl
  have dtan : ∀ z : ℂ, Interp.complex.tanDefined z ↔ Complex.cos z ≠ 0 := fun _ => Iff.rfl
  refine antiderivRec_open Calc.complex _ (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "g")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "h"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.int (-1)))) (rubi1114r10Nondeg.integrals.head!.2) (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.int (-1)))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.complex.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1114r10Nondeg, Defined, eval, hkm] at h0
  have hem : env "m" = (km : ℂ) := (Interp.complex.toInt?_eq _ _).1 hkm
  have hom1 : Interp.complex.toInt? ((-1 : ℂ) + (km : ℂ)) = some (-1 + km) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm1 : Interp.complex.toInt? ((km : ℂ) + (-1 : ℂ)) = some (km + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hom2 : Interp.complex.toInt? ((1 : ℂ) + (km : ℂ)) = some (1 + km) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm2 : Interp.complex.toInt? ((km : ℂ) + (1 : ℂ)) = some (km + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hom3 : Interp.complex.toInt? ((-2 : ℂ) + (km : ℂ)) = some (-2 + km) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm3 : Interp.complex.toInt? ((km : ℂ) + (-2 : ℂ)) = some (km + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hom4 : Interp.complex.toInt? ((2 : ℂ) + (km : ℂ)) = some (2 + km) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm4 : Interp.complex.toInt? ((km : ℂ) + (2 : ℂ)) = some (km + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm1 : Interp.complex.toInt? ((km : ℂ) - 1) = some (km - 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm2 : Interp.complex.toInt? ((km : ℂ) - 2) = some (km - 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hkmp1 : Interp.complex.toInt? (env "m" + 1) = some (km + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmp2 : Interp.complex.toInt? (env "m" + 2) = some (km + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm1 : Interp.complex.toInt? (env "m" + -1) = some (km + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm2 : Interp.complex.toInt? (env "m" + -2) = some (km + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkm]; push_cast; ring)
  rcases hkn : Interp.complex.toInt? (env "n") with _ | kn
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1114r10Nondeg, Defined, eval, hkn] at h0
  have hen : env "n" = (kn : ℂ) := (Interp.complex.toInt?_eq _ _).1 hkn
  have hon1 : Interp.complex.toInt? ((-1 : ℂ) + (kn : ℂ)) = some (-1 + kn) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn1 : Interp.complex.toInt? ((kn : ℂ) + (-1 : ℂ)) = some (kn + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hon2 : Interp.complex.toInt? ((1 : ℂ) + (kn : ℂ)) = some (1 + kn) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn2 : Interp.complex.toInt? ((kn : ℂ) + (1 : ℂ)) = some (kn + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hon3 : Interp.complex.toInt? ((-2 : ℂ) + (kn : ℂ)) = some (-2 + kn) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn3 : Interp.complex.toInt? ((kn : ℂ) + (-2 : ℂ)) = some (kn + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hon4 : Interp.complex.toInt? ((2 : ℂ) + (kn : ℂ)) = some (2 + kn) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn4 : Interp.complex.toInt? ((kn : ℂ) + (2 : ℂ)) = some (kn + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn1 : Interp.complex.toInt? ((kn : ℂ) - 1) = some (kn - 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn2 : Interp.complex.toInt? ((kn : ℂ) - 2) = some (kn - 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hknp1 : Interp.complex.toInt? (env "n" + 1) = some (kn + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknp2 : Interp.complex.toInt? (env "n" + 2) = some (kn + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm1 : Interp.complex.toInt? (env "n" + -1) = some (kn + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm2 : Interp.complex.toInt? (env "n" + -2) = some (kn + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkn]; push_cast; ring)
  rcases hkp : Interp.complex.toInt? (env "p") with _ | kp
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1114r10Nondeg, Defined, eval, hkp] at h0
  have hep : env "p" = (kp : ℂ) := (Interp.complex.toInt?_eq _ _).1 hkp
  have hop1 : Interp.complex.toInt? ((-1 : ℂ) + (kp : ℂ)) = some (-1 + kp) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp1 : Interp.complex.toInt? ((kp : ℂ) + (-1 : ℂ)) = some (kp + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hop2 : Interp.complex.toInt? ((1 : ℂ) + (kp : ℂ)) = some (1 + kp) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp2 : Interp.complex.toInt? ((kp : ℂ) + (1 : ℂ)) = some (kp + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hop3 : Interp.complex.toInt? ((-2 : ℂ) + (kp : ℂ)) = some (-2 + kp) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp3 : Interp.complex.toInt? ((kp : ℂ) + (-2 : ℂ)) = some (kp + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hop4 : Interp.complex.toInt? ((2 : ℂ) + (kp : ℂ)) = some (2 + kp) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp4 : Interp.complex.toInt? ((kp : ℂ) + (2 : ℂ)) = some (kp + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsp1 : Interp.complex.toInt? ((kp : ℂ) - 1) = some (kp - 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsp2 : Interp.complex.toInt? ((kp : ℂ) - 2) = some (kp - 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hkpp1 : Interp.complex.toInt? (env "p" + 1) = some (kp + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpp2 : Interp.complex.toInt? (env "p" + 2) = some (kp + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm1 : Interp.complex.toInt? (env "p" + -1) = some (kp + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm2 : Interp.complex.toInt? (env "p" + -2) = some (kp + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hbm1gt : km < -1 := by
    have h := hcs (.gt (.int (-1)) (.var "m")) (by simp [rubi1114r10Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, hem, Complex.ext_iff] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi1114r10Nondeg, Defined, eval, hem, hen, hep, Interp.toInt?_cast] at h0
  casesm* _ ∧ _
  have hc2 := hcs (.ne (.app2 .mul (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.int 0)) (by simp [rubi1114r10Nondeg])
  simp [Cond.Holds, Defined, eval] at hc2
  try simp only [hem] at hc2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc2, hem]
  · simp [eval, Ok, Expr.varList, hm1, hc2, hem, hqm2, hen, hqn2, hep, hqp2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [Defined, eval, hm1, hc2, hem, hqm2, hen, hqn2, hep, hqp2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [Calc.complex, rubi1114r10Nondeg, eval, Ok, Expr.varList, hem, hqm2, hen, hep, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [rubi1114r10Nondeg, Defined, eval, hem, hqm2, hen, hep, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [rubi1114r10Nondeg, eval, d, hm1, hm11, hem, hqm2, hen, hqn2, hep, hqp2, Interp.toInt?_cast]
    try have hqmm30 : (km : ℂ) - 3 ≠ 0 := by exact_mod_cast (show km - 3 ≠ 0 by omega)
    try have hqmm20 : (km : ℂ) - 2 ≠ 0 := by exact_mod_cast (show km - 2 ≠ 0 by omega)
    try have hqmm10 : (km : ℂ) - 1 ≠ 0 := by exact_mod_cast (show km - 1 ≠ 0 by omega)
    try have hqmp00 : (km : ℂ) ≠ 0 := by exact_mod_cast (show km ≠ 0 by omega)
    try have hqmp10 : (km : ℂ) + 1 ≠ 0 := by exact_mod_cast (show km + 1 ≠ 0 by omega)
    have hz0 : (env "a" + (env "b" * t)) ≠ 0 ∨ 0 ≤ km := by
      rcases lt_or_ge (km) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show (env "a" + (env "b" * t)) ^ (km + 1) = (env "a" + (env "b" * t)) ^ (km) * (env "a" + (env "b" * t)) ^ 1 from by
      have := zsplit ((env "a" + (env "b" * t))) (km) 1 hz0
      rwa [show km + ((1 : ℕ) : ℤ) = km + 1 by push_cast; ring] at this]
    try generalize (env "a" + (env "b" * t)) ^ (km) = P0
    have hz1 : (env "c" + (env "d" * t)) ≠ 0 ∨ 0 ≤ kn := by
      rcases lt_or_ge (kn) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show (env "c" + (env "d" * t)) ^ (kn + 1) = (env "c" + (env "d" * t)) ^ (kn) * (env "c" + (env "d" * t)) ^ 1 from by
      have := zsplit ((env "c" + (env "d" * t))) (kn) 1 hz1
      rwa [show kn + ((1 : ℕ) : ℤ) = kn + 1 by push_cast; ring] at this]
    try generalize (env "c" + (env "d" * t)) ^ (kn) = P1
    have hz2 : (env "e" + (env "f" * t)) ≠ 0 ∨ 0 ≤ kp := by
      rcases lt_or_ge (kp) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show (env "e" + (env "f" * t)) ^ (kp + 1) = (env "e" + (env "f" * t)) ^ (kp) * (env "e" + (env "f" * t)) ^ 1 from by
      have := zsplit ((env "e" + (env "f" * t))) (kp) 1 hz2
      rwa [show kp + ((1 : ℕ) : ℤ) = kp + 1 by push_cast; ring] at this]
    try generalize (env "e" + (env "f" * t)) ^ (kp) = P2
    try casesm* _ ∧ _
    try field_simp
    try ring

set_option maxHeartbeats 1000000 in
/-- RUBI rubi1114r12Nondeg: explicit term by the symbolic derivative. -/
theorem rubi1114r12Nondeg_real : rubi1114r12Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1114r12Nondeg.conditions rubi1114r12Nondeg.body rubi1114r12Nondeg.result rubi1114r12Nondeg.integrals
  have hm1 : Interp.real.toInt? (-1 : ℝ) = some (-1) := by simpa using Interp.toInt?_cast Interp.real (-1)
  have hm2 : Interp.real.toInt? (-2 : ℝ) = some (-2) := by simpa using Interp.toInt?_cast Interp.real (-2)
  have h2 : Interp.real.toInt? (2 : ℝ) = some 2 := by simpa using Interp.toInt?_cast Interp.real 2
  have hm11 : Interp.real.toInt? (-1 + -1 : ℝ) = some (-2) := by
    rw [show (-1 + -1 : ℝ) = -2 by norm_num]; exact hm2
  have dln : ∀ z : ℝ, Interp.real.lnDefined z ↔ 0 < z := fun _ => Iff.rfl
  have dtan : ∀ z : ℝ, Interp.real.tanDefined z ↔ Real.cos z ≠ 0 := fun _ => Iff.rfl
  have dasin : ∀ z : ℝ, Interp.real.fnDefined .arcsin z ↔ -1 ≤ z ∧ z ≤ 1 := fun _ => Iff.rfl
  have dacos : ∀ z : ℝ, Interp.real.fnDefined .arccos z ↔ -1 ≤ z ∧ z ≤ 1 := fun _ => Iff.rfl
  refine antiderivRec_open Calc.real _ (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "h") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "m"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.app2 .add (.app2 .add (.var "m") (.var "n")) (.var "p")) (.int 2))) (.int (-1)))) (rubi1114r12Nondeg.integrals.head!.2) (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.app2 .add (.app2 .add (.var "m") (.var "n")) (.var "p")) (.int 2))) (.int (-1)))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.real.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1114r12Nondeg, Defined, eval, hkm] at h0
  have hem : env "m" = (km : ℝ) := (Interp.real.toInt?_eq _ _).1 hkm
  have hom1 : Interp.real.toInt? ((-1 : ℝ) + (km : ℝ)) = some (-1 + km) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm1 : Interp.real.toInt? ((km : ℝ) + (-1 : ℝ)) = some (km + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hom2 : Interp.real.toInt? ((1 : ℝ) + (km : ℝ)) = some (1 + km) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm2 : Interp.real.toInt? ((km : ℝ) + (1 : ℝ)) = some (km + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hom3 : Interp.real.toInt? ((-2 : ℝ) + (km : ℝ)) = some (-2 + km) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm3 : Interp.real.toInt? ((km : ℝ) + (-2 : ℝ)) = some (km + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hom4 : Interp.real.toInt? ((2 : ℝ) + (km : ℝ)) = some (2 + km) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm4 : Interp.real.toInt? ((km : ℝ) + (2 : ℝ)) = some (km + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm1 : Interp.real.toInt? ((km : ℝ) - 1) = some (km - 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm2 : Interp.real.toInt? ((km : ℝ) - 2) = some (km - 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hkmp1 : Interp.real.toInt? (env "m" + 1) = some (km + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmp2 : Interp.real.toInt? (env "m" + 2) = some (km + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm1 : Interp.real.toInt? (env "m" + -1) = some (km + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm2 : Interp.real.toInt? (env "m" + -2) = some (km + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkm]; push_cast; ring)
  rcases hkn : Interp.real.toInt? (env "n") with _ | kn
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1114r12Nondeg, Defined, eval, hkn] at h0
  have hen : env "n" = (kn : ℝ) := (Interp.real.toInt?_eq _ _).1 hkn
  have hon1 : Interp.real.toInt? ((-1 : ℝ) + (kn : ℝ)) = some (-1 + kn) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn1 : Interp.real.toInt? ((kn : ℝ) + (-1 : ℝ)) = some (kn + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hon2 : Interp.real.toInt? ((1 : ℝ) + (kn : ℝ)) = some (1 + kn) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn2 : Interp.real.toInt? ((kn : ℝ) + (1 : ℝ)) = some (kn + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hon3 : Interp.real.toInt? ((-2 : ℝ) + (kn : ℝ)) = some (-2 + kn) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn3 : Interp.real.toInt? ((kn : ℝ) + (-2 : ℝ)) = some (kn + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hon4 : Interp.real.toInt? ((2 : ℝ) + (kn : ℝ)) = some (2 + kn) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn4 : Interp.real.toInt? ((kn : ℝ) + (2 : ℝ)) = some (kn + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn1 : Interp.real.toInt? ((kn : ℝ) - 1) = some (kn - 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn2 : Interp.real.toInt? ((kn : ℝ) - 2) = some (kn - 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hknp1 : Interp.real.toInt? (env "n" + 1) = some (kn + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknp2 : Interp.real.toInt? (env "n" + 2) = some (kn + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm1 : Interp.real.toInt? (env "n" + -1) = some (kn + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm2 : Interp.real.toInt? (env "n" + -2) = some (kn + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkn]; push_cast; ring)
  rcases hkp : Interp.real.toInt? (env "p") with _ | kp
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1114r12Nondeg, Defined, eval, hkp] at h0
  have hep : env "p" = (kp : ℝ) := (Interp.real.toInt?_eq _ _).1 hkp
  have hop1 : Interp.real.toInt? ((-1 : ℝ) + (kp : ℝ)) = some (-1 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp1 : Interp.real.toInt? ((kp : ℝ) + (-1 : ℝ)) = some (kp + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hop2 : Interp.real.toInt? ((1 : ℝ) + (kp : ℝ)) = some (1 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp2 : Interp.real.toInt? ((kp : ℝ) + (1 : ℝ)) = some (kp + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hop3 : Interp.real.toInt? ((-2 : ℝ) + (kp : ℝ)) = some (-2 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp3 : Interp.real.toInt? ((kp : ℝ) + (-2 : ℝ)) = some (kp + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hop4 : Interp.real.toInt? ((2 : ℝ) + (kp : ℝ)) = some (2 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp4 : Interp.real.toInt? ((kp : ℝ) + (2 : ℝ)) = some (kp + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsp1 : Interp.real.toInt? ((kp : ℝ) - 1) = some (kp - 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsp2 : Interp.real.toInt? ((kp : ℝ) - 2) = some (kp - 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hkpp1 : Interp.real.toInt? (env "p" + 1) = some (kp + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpp2 : Interp.real.toInt? (env "p" + 2) = some (kp + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm1 : Interp.real.toInt? (env "p" + -1) = some (kp + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm2 : Interp.real.toInt? (env "p" + -2) = some (kp + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hbm0gt : 0 < km := by
    have h := hcs (.gt (.var "m") (.int 0)) (by simp [rubi1114r12Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hem] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi1114r12Nondeg, Defined, eval, hem, hen, hep, Interp.toInt?_cast] at h0
  casesm* _ ∧ _
  have hc1 := hcs (.ne (.app2 .add (.app2 .add (.app2 .add (.var "m") (.var "n")) (.var "p")) (.int 2)) (.int 0)) (by simp [rubi1114r12Nondeg])
  simp [Cond.Holds, Defined, eval] at hc1
  have hc3 := hcs (.ne (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.app2 .add (.app2 .add (.var "m") (.var "n")) (.var "p")) (.int 2))) (.int 0)) (by simp [rubi1114r12Nondeg])
  simp [Cond.Holds, Defined, eval] at hc3
  try simp only [hem, hen, hep] at hc1 hc3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc1, hc3, hem, hen, hep]
  · simp [eval, Ok, Expr.varList, hm1, hc1, hc3, hem, hen, hqn2, hep, hqp2, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [Defined, eval, hm1, hc1, hc3, hem, hen, hqn2, hep, hqp2, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [Calc.real, rubi1114r12Nondeg, eval, Ok, Expr.varList, hem, hqm1, hen, hep, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [rubi1114r12Nondeg, Defined, eval, hem, hqm1, hen, hep, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [rubi1114r12Nondeg, eval, d, hm1, hm11, hem, hqm1, hen, hqn2, hep, hqp2, Interp.toInt?_cast]
    try have hqmp00 : (km : ℝ) ≠ 0 := by exact_mod_cast (show km ≠ 0 by omega)
    try have hqmp10 : (km : ℝ) + 1 ≠ 0 := by exact_mod_cast (show km + 1 ≠ 0 by omega)
    try have hqmp20 : (km : ℝ) + 2 ≠ 0 := by exact_mod_cast (show km + 2 ≠ 0 by omega)
    try have hqmp30 : (km : ℝ) + 3 ≠ 0 := by exact_mod_cast (show km + 3 ≠ 0 by omega)
    have hz0 : (env "a" + (env "b" * t)) ≠ 0 ∨ 0 ≤ km + -1 := by
      exact Or.inr (by omega)
    try rw [show (env "a" + (env "b" * t)) ^ (km) = (env "a" + (env "b" * t)) ^ (km + -1) * (env "a" + (env "b" * t)) ^ 1 from by
      have := zsplit ((env "a" + (env "b" * t))) (km + -1) 1 hz0
      rwa [show km + -1 + ((1 : ℕ) : ℤ) = km by push_cast; ring] at this]
    try generalize (env "a" + (env "b" * t)) ^ (km + -1) = P0
    have hz1 : (env "c" + (env "d" * t)) ≠ 0 ∨ 0 ≤ kn := by
      rcases lt_or_ge (kn) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show (env "c" + (env "d" * t)) ^ (kn + 1) = (env "c" + (env "d" * t)) ^ (kn) * (env "c" + (env "d" * t)) ^ 1 from by
      have := zsplit ((env "c" + (env "d" * t))) (kn) 1 hz1
      rwa [show kn + ((1 : ℕ) : ℤ) = kn + 1 by push_cast; ring] at this]
    try generalize (env "c" + (env "d" * t)) ^ (kn) = P1
    have hz2 : (env "e" + (env "f" * t)) ≠ 0 ∨ 0 ≤ kp := by
      rcases lt_or_ge (kp) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show (env "e" + (env "f" * t)) ^ (kp + 1) = (env "e" + (env "f" * t)) ^ (kp) * (env "e" + (env "f" * t)) ^ 1 from by
      have := zsplit ((env "e" + (env "f" * t))) (kp) 1 hz2
      rwa [show kp + ((1 : ℕ) : ℤ) = kp + 1 by push_cast; ring] at this]
    try generalize (env "e" + (env "f" * t)) ^ (kp) = P2
    try casesm* _ ∧ _
    try field_simp
    try ring

set_option maxHeartbeats 1000000 in
/-- RUBI rubi1114r12Nondeg: explicit term by the symbolic derivative. -/
theorem rubi1114r12Nondeg_complex : rubi1114r12Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1114r12Nondeg.conditions rubi1114r12Nondeg.body rubi1114r12Nondeg.result rubi1114r12Nondeg.integrals
  have hm1 : Interp.complex.toInt? (-1 : ℂ) = some (-1) := by simpa using Interp.toInt?_cast Interp.complex (-1)
  have hm2 : Interp.complex.toInt? (-2 : ℂ) = some (-2) := by simpa using Interp.toInt?_cast Interp.complex (-2)
  have h2 : Interp.complex.toInt? (2 : ℂ) = some 2 := by simpa using Interp.toInt?_cast Interp.complex 2
  have hm11 : Interp.complex.toInt? (-1 + -1 : ℂ) = some (-2) := by
    rw [show (-1 + -1 : ℂ) = -2 by norm_num]; exact hm2
  have dln : ∀ z : ℂ, Interp.complex.lnDefined z ↔ z ≠ 0 := fun _ => Iff.rfl
  have dtan : ∀ z : ℂ, Interp.complex.tanDefined z ↔ Complex.cos z ≠ 0 := fun _ => Iff.rfl
  refine antiderivRec_open Calc.complex _ (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "h") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "m"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.app2 .add (.app2 .add (.var "m") (.var "n")) (.var "p")) (.int 2))) (.int (-1)))) (rubi1114r12Nondeg.integrals.head!.2) (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.app2 .add (.app2 .add (.var "m") (.var "n")) (.var "p")) (.int 2))) (.int (-1)))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.complex.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1114r12Nondeg, Defined, eval, hkm] at h0
  have hem : env "m" = (km : ℂ) := (Interp.complex.toInt?_eq _ _).1 hkm
  have hom1 : Interp.complex.toInt? ((-1 : ℂ) + (km : ℂ)) = some (-1 + km) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm1 : Interp.complex.toInt? ((km : ℂ) + (-1 : ℂ)) = some (km + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hom2 : Interp.complex.toInt? ((1 : ℂ) + (km : ℂ)) = some (1 + km) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm2 : Interp.complex.toInt? ((km : ℂ) + (1 : ℂ)) = some (km + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hom3 : Interp.complex.toInt? ((-2 : ℂ) + (km : ℂ)) = some (-2 + km) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm3 : Interp.complex.toInt? ((km : ℂ) + (-2 : ℂ)) = some (km + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hom4 : Interp.complex.toInt? ((2 : ℂ) + (km : ℂ)) = some (2 + km) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm4 : Interp.complex.toInt? ((km : ℂ) + (2 : ℂ)) = some (km + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm1 : Interp.complex.toInt? ((km : ℂ) - 1) = some (km - 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm2 : Interp.complex.toInt? ((km : ℂ) - 2) = some (km - 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hkmp1 : Interp.complex.toInt? (env "m" + 1) = some (km + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmp2 : Interp.complex.toInt? (env "m" + 2) = some (km + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm1 : Interp.complex.toInt? (env "m" + -1) = some (km + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm2 : Interp.complex.toInt? (env "m" + -2) = some (km + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkm]; push_cast; ring)
  rcases hkn : Interp.complex.toInt? (env "n") with _ | kn
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1114r12Nondeg, Defined, eval, hkn] at h0
  have hen : env "n" = (kn : ℂ) := (Interp.complex.toInt?_eq _ _).1 hkn
  have hon1 : Interp.complex.toInt? ((-1 : ℂ) + (kn : ℂ)) = some (-1 + kn) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn1 : Interp.complex.toInt? ((kn : ℂ) + (-1 : ℂ)) = some (kn + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hon2 : Interp.complex.toInt? ((1 : ℂ) + (kn : ℂ)) = some (1 + kn) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn2 : Interp.complex.toInt? ((kn : ℂ) + (1 : ℂ)) = some (kn + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hon3 : Interp.complex.toInt? ((-2 : ℂ) + (kn : ℂ)) = some (-2 + kn) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn3 : Interp.complex.toInt? ((kn : ℂ) + (-2 : ℂ)) = some (kn + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hon4 : Interp.complex.toInt? ((2 : ℂ) + (kn : ℂ)) = some (2 + kn) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn4 : Interp.complex.toInt? ((kn : ℂ) + (2 : ℂ)) = some (kn + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn1 : Interp.complex.toInt? ((kn : ℂ) - 1) = some (kn - 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn2 : Interp.complex.toInt? ((kn : ℂ) - 2) = some (kn - 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hknp1 : Interp.complex.toInt? (env "n" + 1) = some (kn + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknp2 : Interp.complex.toInt? (env "n" + 2) = some (kn + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm1 : Interp.complex.toInt? (env "n" + -1) = some (kn + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm2 : Interp.complex.toInt? (env "n" + -2) = some (kn + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkn]; push_cast; ring)
  rcases hkp : Interp.complex.toInt? (env "p") with _ | kp
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1114r12Nondeg, Defined, eval, hkp] at h0
  have hep : env "p" = (kp : ℂ) := (Interp.complex.toInt?_eq _ _).1 hkp
  have hop1 : Interp.complex.toInt? ((-1 : ℂ) + (kp : ℂ)) = some (-1 + kp) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp1 : Interp.complex.toInt? ((kp : ℂ) + (-1 : ℂ)) = some (kp + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hop2 : Interp.complex.toInt? ((1 : ℂ) + (kp : ℂ)) = some (1 + kp) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp2 : Interp.complex.toInt? ((kp : ℂ) + (1 : ℂ)) = some (kp + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hop3 : Interp.complex.toInt? ((-2 : ℂ) + (kp : ℂ)) = some (-2 + kp) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp3 : Interp.complex.toInt? ((kp : ℂ) + (-2 : ℂ)) = some (kp + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hop4 : Interp.complex.toInt? ((2 : ℂ) + (kp : ℂ)) = some (2 + kp) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp4 : Interp.complex.toInt? ((kp : ℂ) + (2 : ℂ)) = some (kp + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsp1 : Interp.complex.toInt? ((kp : ℂ) - 1) = some (kp - 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsp2 : Interp.complex.toInt? ((kp : ℂ) - 2) = some (kp - 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hkpp1 : Interp.complex.toInt? (env "p" + 1) = some (kp + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpp2 : Interp.complex.toInt? (env "p" + 2) = some (kp + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm1 : Interp.complex.toInt? (env "p" + -1) = some (kp + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm2 : Interp.complex.toInt? (env "p" + -2) = some (kp + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hbm0gt : 0 < km := by
    have h := hcs (.gt (.var "m") (.int 0)) (by simp [rubi1114r12Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, hem, Complex.ext_iff] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi1114r12Nondeg, Defined, eval, hem, hen, hep, Interp.toInt?_cast] at h0
  casesm* _ ∧ _
  have hc1 := hcs (.ne (.app2 .add (.app2 .add (.app2 .add (.var "m") (.var "n")) (.var "p")) (.int 2)) (.int 0)) (by simp [rubi1114r12Nondeg])
  simp [Cond.Holds, Defined, eval] at hc1
  have hc3 := hcs (.ne (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.app2 .add (.app2 .add (.var "m") (.var "n")) (.var "p")) (.int 2))) (.int 0)) (by simp [rubi1114r12Nondeg])
  simp [Cond.Holds, Defined, eval] at hc3
  try simp only [hem, hen, hep] at hc1 hc3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc1, hc3, hem, hen, hep]
  · simp [eval, Ok, Expr.varList, hm1, hc1, hc3, hem, hen, hqn2, hep, hqp2, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [Defined, eval, hm1, hc1, hc3, hem, hen, hqn2, hep, hqp2, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [Calc.complex, rubi1114r12Nondeg, eval, Ok, Expr.varList, hem, hqm1, hen, hep, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [rubi1114r12Nondeg, Defined, eval, hem, hqm1, hen, hep, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [rubi1114r12Nondeg, eval, d, hm1, hm11, hem, hqm1, hen, hqn2, hep, hqp2, Interp.toInt?_cast]
    try have hqmp00 : (km : ℂ) ≠ 0 := by exact_mod_cast (show km ≠ 0 by omega)
    try have hqmp10 : (km : ℂ) + 1 ≠ 0 := by exact_mod_cast (show km + 1 ≠ 0 by omega)
    try have hqmp20 : (km : ℂ) + 2 ≠ 0 := by exact_mod_cast (show km + 2 ≠ 0 by omega)
    try have hqmp30 : (km : ℂ) + 3 ≠ 0 := by exact_mod_cast (show km + 3 ≠ 0 by omega)
    have hz0 : (env "a" + (env "b" * t)) ≠ 0 ∨ 0 ≤ km + -1 := by
      exact Or.inr (by omega)
    try rw [show (env "a" + (env "b" * t)) ^ (km) = (env "a" + (env "b" * t)) ^ (km + -1) * (env "a" + (env "b" * t)) ^ 1 from by
      have := zsplit ((env "a" + (env "b" * t))) (km + -1) 1 hz0
      rwa [show km + -1 + ((1 : ℕ) : ℤ) = km by push_cast; ring] at this]
    try generalize (env "a" + (env "b" * t)) ^ (km + -1) = P0
    have hz1 : (env "c" + (env "d" * t)) ≠ 0 ∨ 0 ≤ kn := by
      rcases lt_or_ge (kn) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show (env "c" + (env "d" * t)) ^ (kn + 1) = (env "c" + (env "d" * t)) ^ (kn) * (env "c" + (env "d" * t)) ^ 1 from by
      have := zsplit ((env "c" + (env "d" * t))) (kn) 1 hz1
      rwa [show kn + ((1 : ℕ) : ℤ) = kn + 1 by push_cast; ring] at this]
    try generalize (env "c" + (env "d" * t)) ^ (kn) = P1
    have hz2 : (env "e" + (env "f" * t)) ≠ 0 ∨ 0 ≤ kp := by
      rcases lt_or_ge (kp) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show (env "e" + (env "f" * t)) ^ (kp + 1) = (env "e" + (env "f" * t)) ^ (kp) * (env "e" + (env "f" * t)) ^ 1 from by
      have := zsplit ((env "e" + (env "f" * t))) (kp) 1 hz2
      rwa [show kp + ((1 : ℕ) : ℤ) = kp + 1 by push_cast; ring] at this]
    try generalize (env "e" + (env "f" * t)) ^ (kp) = P2
    try casesm* _ ∧ _
    try field_simp
    try ring

set_option maxHeartbeats 1000000 in
/-- RUBI rubi1114r8Nondeg: explicit term by the symbolic derivative. -/
theorem rubi1114r8Nondeg_real : rubi1114r8Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1114r8Nondeg.conditions rubi1114r8Nondeg.body rubi1114r8Nondeg.result rubi1114r8Nondeg.integrals
  have hm1 : Interp.real.toInt? (-1 : ℝ) = some (-1) := by simpa using Interp.toInt?_cast Interp.real (-1)
  have hm2 : Interp.real.toInt? (-2 : ℝ) = some (-2) := by simpa using Interp.toInt?_cast Interp.real (-2)
  have h2 : Interp.real.toInt? (2 : ℝ) = some 2 := by simpa using Interp.toInt?_cast Interp.real 2
  have hm11 : Interp.real.toInt? (-1 + -1 : ℝ) = some (-2) := by
    rw [show (-1 + -1 : ℝ) = -2 by norm_num]; exact hm2
  have dln : ∀ z : ℝ, Interp.real.lnDefined z ↔ 0 < z := fun _ => Iff.rfl
  have dtan : ∀ z : ℝ, Interp.real.tanDefined z ↔ Real.cos z ≠ 0 := fun _ => Iff.rfl
  have dasin : ∀ z : ℝ, Interp.real.fnDefined .arcsin z ↔ -1 ≤ z ∧ z ≤ 1 := fun _ => Iff.rfl
  have dacos : ∀ z : ℝ, Interp.real.fnDefined .arccos z ↔ -1 ≤ z ∧ z ≤ 1 := fun _ => Iff.rfl
  refine antiderivRec_open Calc.real _ (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "g")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "h"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n"))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (rubi1114r8Nondeg.integrals.head!.2) (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.real.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1114r8Nondeg, Defined, eval, hkm] at h0
  have hem : env "m" = (km : ℝ) := (Interp.real.toInt?_eq _ _).1 hkm
  have hom1 : Interp.real.toInt? ((-1 : ℝ) + (km : ℝ)) = some (-1 + km) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm1 : Interp.real.toInt? ((km : ℝ) + (-1 : ℝ)) = some (km + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hom2 : Interp.real.toInt? ((1 : ℝ) + (km : ℝ)) = some (1 + km) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm2 : Interp.real.toInt? ((km : ℝ) + (1 : ℝ)) = some (km + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hom3 : Interp.real.toInt? ((-2 : ℝ) + (km : ℝ)) = some (-2 + km) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm3 : Interp.real.toInt? ((km : ℝ) + (-2 : ℝ)) = some (km + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hom4 : Interp.real.toInt? ((2 : ℝ) + (km : ℝ)) = some (2 + km) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm4 : Interp.real.toInt? ((km : ℝ) + (2 : ℝ)) = some (km + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm1 : Interp.real.toInt? ((km : ℝ) - 1) = some (km - 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm2 : Interp.real.toInt? ((km : ℝ) - 2) = some (km - 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hkmp1 : Interp.real.toInt? (env "m" + 1) = some (km + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmp2 : Interp.real.toInt? (env "m" + 2) = some (km + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm1 : Interp.real.toInt? (env "m" + -1) = some (km + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm2 : Interp.real.toInt? (env "m" + -2) = some (km + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkm]; push_cast; ring)
  rcases hkn : Interp.real.toInt? (env "n") with _ | kn
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1114r8Nondeg, Defined, eval, hkn] at h0
  have hen : env "n" = (kn : ℝ) := (Interp.real.toInt?_eq _ _).1 hkn
  have hon1 : Interp.real.toInt? ((-1 : ℝ) + (kn : ℝ)) = some (-1 + kn) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn1 : Interp.real.toInt? ((kn : ℝ) + (-1 : ℝ)) = some (kn + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hon2 : Interp.real.toInt? ((1 : ℝ) + (kn : ℝ)) = some (1 + kn) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn2 : Interp.real.toInt? ((kn : ℝ) + (1 : ℝ)) = some (kn + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hon3 : Interp.real.toInt? ((-2 : ℝ) + (kn : ℝ)) = some (-2 + kn) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn3 : Interp.real.toInt? ((kn : ℝ) + (-2 : ℝ)) = some (kn + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hon4 : Interp.real.toInt? ((2 : ℝ) + (kn : ℝ)) = some (2 + kn) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn4 : Interp.real.toInt? ((kn : ℝ) + (2 : ℝ)) = some (kn + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn1 : Interp.real.toInt? ((kn : ℝ) - 1) = some (kn - 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn2 : Interp.real.toInt? ((kn : ℝ) - 2) = some (kn - 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hknp1 : Interp.real.toInt? (env "n" + 1) = some (kn + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknp2 : Interp.real.toInt? (env "n" + 2) = some (kn + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm1 : Interp.real.toInt? (env "n" + -1) = some (kn + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm2 : Interp.real.toInt? (env "n" + -2) = some (kn + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkn]; push_cast; ring)
  rcases hkp : Interp.real.toInt? (env "p") with _ | kp
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1114r8Nondeg, Defined, eval, hkp] at h0
  have hep : env "p" = (kp : ℝ) := (Interp.real.toInt?_eq _ _).1 hkp
  have hop1 : Interp.real.toInt? ((-1 : ℝ) + (kp : ℝ)) = some (-1 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp1 : Interp.real.toInt? ((kp : ℝ) + (-1 : ℝ)) = some (kp + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hop2 : Interp.real.toInt? ((1 : ℝ) + (kp : ℝ)) = some (1 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp2 : Interp.real.toInt? ((kp : ℝ) + (1 : ℝ)) = some (kp + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hop3 : Interp.real.toInt? ((-2 : ℝ) + (kp : ℝ)) = some (-2 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp3 : Interp.real.toInt? ((kp : ℝ) + (-2 : ℝ)) = some (kp + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hop4 : Interp.real.toInt? ((2 : ℝ) + (kp : ℝ)) = some (2 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp4 : Interp.real.toInt? ((kp : ℝ) + (2 : ℝ)) = some (kp + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsp1 : Interp.real.toInt? ((kp : ℝ) - 1) = some (kp - 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsp2 : Interp.real.toInt? ((kp : ℝ) - 2) = some (kp - 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hkpp1 : Interp.real.toInt? (env "p" + 1) = some (kp + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpp2 : Interp.real.toInt? (env "p" + 2) = some (kp + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm1 : Interp.real.toInt? (env "p" + -1) = some (kp + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm2 : Interp.real.toInt? (env "p" + -2) = some (kp + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hbm1gt : km < -1 := by
    have h := hcs (.gt (.int (-1)) (.var "m")) (by simp [rubi1114r8Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hem] at h
    exact_mod_cast h
  have hbn0gt : 0 < kn := by
    have h := hcs (.gt (.var "n") (.int 0)) (by simp [rubi1114r8Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hen] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi1114r8Nondeg, Defined, eval, hem, hen, hep, Interp.toInt?_cast] at h0
  casesm* _ ∧ _
  have hc3 := hcs (.ne (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi1114r8Nondeg])
  simp [Cond.Holds, Defined, eval] at hc3
  try simp only [hem] at hc3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc3, hem]
  · simp [eval, Ok, Expr.varList, hm1, hc3, hem, hqm2, hen, hep, hqp2, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [Defined, eval, hm1, hc3, hem, hqm2, hen, hep, hqp2, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [Calc.real, rubi1114r8Nondeg, eval, Ok, Expr.varList, hem, hqm2, hen, hqn1, hep, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [rubi1114r8Nondeg, Defined, eval, hem, hqm2, hen, hqn1, hep, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [rubi1114r8Nondeg, eval, d, hm1, hm11, hem, hqm2, hen, hqn1, hep, hqp2, Interp.toInt?_cast]
    try have hqmm30 : (km : ℝ) - 3 ≠ 0 := by exact_mod_cast (show km - 3 ≠ 0 by omega)
    try have hqmm20 : (km : ℝ) - 2 ≠ 0 := by exact_mod_cast (show km - 2 ≠ 0 by omega)
    try have hqmm10 : (km : ℝ) - 1 ≠ 0 := by exact_mod_cast (show km - 1 ≠ 0 by omega)
    try have hqmp00 : (km : ℝ) ≠ 0 := by exact_mod_cast (show km ≠ 0 by omega)
    try have hqmp10 : (km : ℝ) + 1 ≠ 0 := by exact_mod_cast (show km + 1 ≠ 0 by omega)
    try have hqnp00 : (kn : ℝ) ≠ 0 := by exact_mod_cast (show kn ≠ 0 by omega)
    try have hqnp10 : (kn : ℝ) + 1 ≠ 0 := by exact_mod_cast (show kn + 1 ≠ 0 by omega)
    try have hqnp20 : (kn : ℝ) + 2 ≠ 0 := by exact_mod_cast (show kn + 2 ≠ 0 by omega)
    try have hqnp30 : (kn : ℝ) + 3 ≠ 0 := by exact_mod_cast (show kn + 3 ≠ 0 by omega)
    have hz0 : (env "a" + (env "b" * t)) ≠ 0 ∨ 0 ≤ km := by
      rcases lt_or_ge (km) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show (env "a" + (env "b" * t)) ^ (km + 1) = (env "a" + (env "b" * t)) ^ (km) * (env "a" + (env "b" * t)) ^ 1 from by
      have := zsplit ((env "a" + (env "b" * t))) (km) 1 hz0
      rwa [show km + ((1 : ℕ) : ℤ) = km + 1 by push_cast; ring] at this]
    try generalize (env "a" + (env "b" * t)) ^ (km) = P0
    have hz1 : (env "c" + (env "d" * t)) ≠ 0 ∨ 0 ≤ kn + -1 := by
      exact Or.inr (by omega)
    try rw [show (env "c" + (env "d" * t)) ^ (kn) = (env "c" + (env "d" * t)) ^ (kn + -1) * (env "c" + (env "d" * t)) ^ 1 from by
      have := zsplit ((env "c" + (env "d" * t))) (kn + -1) 1 hz1
      rwa [show kn + -1 + ((1 : ℕ) : ℤ) = kn by push_cast; ring] at this]
    try generalize (env "c" + (env "d" * t)) ^ (kn + -1) = P1
    have hz2 : (env "e" + (env "f" * t)) ≠ 0 ∨ 0 ≤ kp := by
      rcases lt_or_ge (kp) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show (env "e" + (env "f" * t)) ^ (kp + 1) = (env "e" + (env "f" * t)) ^ (kp) * (env "e" + (env "f" * t)) ^ 1 from by
      have := zsplit ((env "e" + (env "f" * t))) (kp) 1 hz2
      rwa [show kp + ((1 : ℕ) : ℤ) = kp + 1 by push_cast; ring] at this]
    try generalize (env "e" + (env "f" * t)) ^ (kp) = P2
    try casesm* _ ∧ _
    try field_simp
    try ring

set_option maxHeartbeats 1000000 in
/-- RUBI rubi1114r8Nondeg: explicit term by the symbolic derivative. -/
theorem rubi1114r8Nondeg_complex : rubi1114r8Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1114r8Nondeg.conditions rubi1114r8Nondeg.body rubi1114r8Nondeg.result rubi1114r8Nondeg.integrals
  have hm1 : Interp.complex.toInt? (-1 : ℂ) = some (-1) := by simpa using Interp.toInt?_cast Interp.complex (-1)
  have hm2 : Interp.complex.toInt? (-2 : ℂ) = some (-2) := by simpa using Interp.toInt?_cast Interp.complex (-2)
  have h2 : Interp.complex.toInt? (2 : ℂ) = some 2 := by simpa using Interp.toInt?_cast Interp.complex 2
  have hm11 : Interp.complex.toInt? (-1 + -1 : ℂ) = some (-2) := by
    rw [show (-1 + -1 : ℂ) = -2 by norm_num]; exact hm2
  have dln : ∀ z : ℂ, Interp.complex.lnDefined z ↔ z ≠ 0 := fun _ => Iff.rfl
  have dtan : ∀ z : ℂ, Interp.complex.tanDefined z ↔ Complex.cos z ≠ 0 := fun _ => Iff.rfl
  refine antiderivRec_open Calc.complex _ (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "g")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "h"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n"))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (rubi1114r8Nondeg.integrals.head!.2) (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.complex.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1114r8Nondeg, Defined, eval, hkm] at h0
  have hem : env "m" = (km : ℂ) := (Interp.complex.toInt?_eq _ _).1 hkm
  have hom1 : Interp.complex.toInt? ((-1 : ℂ) + (km : ℂ)) = some (-1 + km) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm1 : Interp.complex.toInt? ((km : ℂ) + (-1 : ℂ)) = some (km + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hom2 : Interp.complex.toInt? ((1 : ℂ) + (km : ℂ)) = some (1 + km) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm2 : Interp.complex.toInt? ((km : ℂ) + (1 : ℂ)) = some (km + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hom3 : Interp.complex.toInt? ((-2 : ℂ) + (km : ℂ)) = some (-2 + km) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm3 : Interp.complex.toInt? ((km : ℂ) + (-2 : ℂ)) = some (km + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hom4 : Interp.complex.toInt? ((2 : ℂ) + (km : ℂ)) = some (2 + km) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm4 : Interp.complex.toInt? ((km : ℂ) + (2 : ℂ)) = some (km + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm1 : Interp.complex.toInt? ((km : ℂ) - 1) = some (km - 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm2 : Interp.complex.toInt? ((km : ℂ) - 2) = some (km - 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hkmp1 : Interp.complex.toInt? (env "m" + 1) = some (km + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmp2 : Interp.complex.toInt? (env "m" + 2) = some (km + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm1 : Interp.complex.toInt? (env "m" + -1) = some (km + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm2 : Interp.complex.toInt? (env "m" + -2) = some (km + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkm]; push_cast; ring)
  rcases hkn : Interp.complex.toInt? (env "n") with _ | kn
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1114r8Nondeg, Defined, eval, hkn] at h0
  have hen : env "n" = (kn : ℂ) := (Interp.complex.toInt?_eq _ _).1 hkn
  have hon1 : Interp.complex.toInt? ((-1 : ℂ) + (kn : ℂ)) = some (-1 + kn) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn1 : Interp.complex.toInt? ((kn : ℂ) + (-1 : ℂ)) = some (kn + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hon2 : Interp.complex.toInt? ((1 : ℂ) + (kn : ℂ)) = some (1 + kn) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn2 : Interp.complex.toInt? ((kn : ℂ) + (1 : ℂ)) = some (kn + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hon3 : Interp.complex.toInt? ((-2 : ℂ) + (kn : ℂ)) = some (-2 + kn) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn3 : Interp.complex.toInt? ((kn : ℂ) + (-2 : ℂ)) = some (kn + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hon4 : Interp.complex.toInt? ((2 : ℂ) + (kn : ℂ)) = some (2 + kn) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn4 : Interp.complex.toInt? ((kn : ℂ) + (2 : ℂ)) = some (kn + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn1 : Interp.complex.toInt? ((kn : ℂ) - 1) = some (kn - 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn2 : Interp.complex.toInt? ((kn : ℂ) - 2) = some (kn - 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hknp1 : Interp.complex.toInt? (env "n" + 1) = some (kn + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknp2 : Interp.complex.toInt? (env "n" + 2) = some (kn + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm1 : Interp.complex.toInt? (env "n" + -1) = some (kn + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm2 : Interp.complex.toInt? (env "n" + -2) = some (kn + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkn]; push_cast; ring)
  rcases hkp : Interp.complex.toInt? (env "p") with _ | kp
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1114r8Nondeg, Defined, eval, hkp] at h0
  have hep : env "p" = (kp : ℂ) := (Interp.complex.toInt?_eq _ _).1 hkp
  have hop1 : Interp.complex.toInt? ((-1 : ℂ) + (kp : ℂ)) = some (-1 + kp) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp1 : Interp.complex.toInt? ((kp : ℂ) + (-1 : ℂ)) = some (kp + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hop2 : Interp.complex.toInt? ((1 : ℂ) + (kp : ℂ)) = some (1 + kp) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp2 : Interp.complex.toInt? ((kp : ℂ) + (1 : ℂ)) = some (kp + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hop3 : Interp.complex.toInt? ((-2 : ℂ) + (kp : ℂ)) = some (-2 + kp) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp3 : Interp.complex.toInt? ((kp : ℂ) + (-2 : ℂ)) = some (kp + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hop4 : Interp.complex.toInt? ((2 : ℂ) + (kp : ℂ)) = some (2 + kp) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp4 : Interp.complex.toInt? ((kp : ℂ) + (2 : ℂ)) = some (kp + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsp1 : Interp.complex.toInt? ((kp : ℂ) - 1) = some (kp - 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsp2 : Interp.complex.toInt? ((kp : ℂ) - 2) = some (kp - 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hkpp1 : Interp.complex.toInt? (env "p" + 1) = some (kp + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpp2 : Interp.complex.toInt? (env "p" + 2) = some (kp + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm1 : Interp.complex.toInt? (env "p" + -1) = some (kp + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm2 : Interp.complex.toInt? (env "p" + -2) = some (kp + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hbm1gt : km < -1 := by
    have h := hcs (.gt (.int (-1)) (.var "m")) (by simp [rubi1114r8Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, hem, Complex.ext_iff] at h
    exact_mod_cast h
  have hbn0gt : 0 < kn := by
    have h := hcs (.gt (.var "n") (.int 0)) (by simp [rubi1114r8Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, hen, Complex.ext_iff] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi1114r8Nondeg, Defined, eval, hem, hen, hep, Interp.toInt?_cast] at h0
  casesm* _ ∧ _
  have hc3 := hcs (.ne (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi1114r8Nondeg])
  simp [Cond.Holds, Defined, eval] at hc3
  try simp only [hem] at hc3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc3, hem]
  · simp [eval, Ok, Expr.varList, hm1, hc3, hem, hqm2, hen, hep, hqp2, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [Defined, eval, hm1, hc3, hem, hqm2, hen, hep, hqp2, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [Calc.complex, rubi1114r8Nondeg, eval, Ok, Expr.varList, hem, hqm2, hen, hqn1, hep, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [rubi1114r8Nondeg, Defined, eval, hem, hqm2, hen, hqn1, hep, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega)) <;> simp_all
  · simp [rubi1114r8Nondeg, eval, d, hm1, hm11, hem, hqm2, hen, hqn1, hep, hqp2, Interp.toInt?_cast]
    try have hqmm30 : (km : ℂ) - 3 ≠ 0 := by exact_mod_cast (show km - 3 ≠ 0 by omega)
    try have hqmm20 : (km : ℂ) - 2 ≠ 0 := by exact_mod_cast (show km - 2 ≠ 0 by omega)
    try have hqmm10 : (km : ℂ) - 1 ≠ 0 := by exact_mod_cast (show km - 1 ≠ 0 by omega)
    try have hqmp00 : (km : ℂ) ≠ 0 := by exact_mod_cast (show km ≠ 0 by omega)
    try have hqmp10 : (km : ℂ) + 1 ≠ 0 := by exact_mod_cast (show km + 1 ≠ 0 by omega)
    try have hqnp00 : (kn : ℂ) ≠ 0 := by exact_mod_cast (show kn ≠ 0 by omega)
    try have hqnp10 : (kn : ℂ) + 1 ≠ 0 := by exact_mod_cast (show kn + 1 ≠ 0 by omega)
    try have hqnp20 : (kn : ℂ) + 2 ≠ 0 := by exact_mod_cast (show kn + 2 ≠ 0 by omega)
    try have hqnp30 : (kn : ℂ) + 3 ≠ 0 := by exact_mod_cast (show kn + 3 ≠ 0 by omega)
    have hz0 : (env "a" + (env "b" * t)) ≠ 0 ∨ 0 ≤ km := by
      rcases lt_or_ge (km) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show (env "a" + (env "b" * t)) ^ (km + 1) = (env "a" + (env "b" * t)) ^ (km) * (env "a" + (env "b" * t)) ^ 1 from by
      have := zsplit ((env "a" + (env "b" * t))) (km) 1 hz0
      rwa [show km + ((1 : ℕ) : ℤ) = km + 1 by push_cast; ring] at this]
    try generalize (env "a" + (env "b" * t)) ^ (km) = P0
    have hz1 : (env "c" + (env "d" * t)) ≠ 0 ∨ 0 ≤ kn + -1 := by
      exact Or.inr (by omega)
    try rw [show (env "c" + (env "d" * t)) ^ (kn) = (env "c" + (env "d" * t)) ^ (kn + -1) * (env "c" + (env "d" * t)) ^ 1 from by
      have := zsplit ((env "c" + (env "d" * t))) (kn + -1) 1 hz1
      rwa [show kn + -1 + ((1 : ℕ) : ℤ) = kn by push_cast; ring] at this]
    try generalize (env "c" + (env "d" * t)) ^ (kn + -1) = P1
    have hz2 : (env "e" + (env "f" * t)) ≠ 0 ∨ 0 ≤ kp := by
      rcases lt_or_ge (kp) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show (env "e" + (env "f" * t)) ^ (kp + 1) = (env "e" + (env "f" * t)) ^ (kp) * (env "e" + (env "f" * t)) ^ 1 from by
      have := zsplit ((env "e" + (env "f" * t))) (kp) 1 hz2
      rwa [show kp + ((1 : ℕ) : ℤ) = kp + 1 by push_cast; ring] at this]
    try generalize (env "e" + (env "f" * t)) ^ (kp) = P2
    try casesm* _ ∧ _
    try field_simp
    try ring

set_option maxHeartbeats 1000000 in
/-- RUBI rubi534r23Nondeg: explicit term by the symbolic derivative. -/
theorem rubi534r23Nondeg_real : rubi534r23Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi534r23Nondeg.conditions rubi534r23Nondeg.body rubi534r23Nondeg.result rubi534r23Nondeg.integrals
  have hm1 : Interp.real.toInt? (-1 : ℝ) = some (-1) := by simpa using Interp.toInt?_cast Interp.real (-1)
  have hm2 : Interp.real.toInt? (-2 : ℝ) = some (-2) := by simpa using Interp.toInt?_cast Interp.real (-2)
  have h2 : Interp.real.toInt? (2 : ℝ) = some 2 := by simpa using Interp.toInt?_cast Interp.real 2
  have hm11 : Interp.real.toInt? (-1 + -1 : ℝ) = some (-2) := by
    rw [show (-1 + -1 : ℝ) = -2 by norm_num]; exact hm2
  have hn1 : Interp.real.toInt? (1 : ℝ) = some 1 := by simpa using Interp.toInt?_cast Interp.real 1
  have hn3 : Interp.real.toInt? (3 : ℝ) = some 3 := by simpa using Interp.toInt?_cast Interp.real 3
  have hn21 : Interp.real.toInt? (2 + -1 : ℝ) = some 1 := by rw [show (2 + -1 : ℝ) = 1 by norm_num]; exact hn1
  have hn31 : Interp.real.toInt? (3 + -1 : ℝ) = some 2 := by rw [show (3 + -1 : ℝ) = 2 by norm_num]; exact h2
  have hn32 : Interp.real.toInt? (3 + -2 : ℝ) = some 1 := by rw [show (3 + -2 : ℝ) = 1 by norm_num]; exact hn1
  have hn10 : Interp.real.toInt? (1 + -1 : ℝ) = some 0 := by simpa using Interp.toInt?_cast Interp.real 0
  have dln : ∀ z : ℝ, Interp.real.lnDefined z ↔ 0 < z := fun _ => Iff.rfl
  have dtan : ∀ z : ℝ, Interp.real.tanDefined z ↔ Real.cos z ≠ 0 := fun _ => Iff.rfl
  have dasin : ∀ z : ℝ, Interp.real.fnDefined .arcsin z ↔ -1 ≤ z ∧ z ≤ 1 := fun _ => Iff.rfl
  have dacos : ∀ z : ℝ, Interp.real.fnDefined .arccos z ↔ -1 ≤ z ∧ z ≤ 1 := fun _ => Iff.rfl
  refine antiderivRec_open Calc.real _ (.app2 .add (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2))))) (.int (-1)))) (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 1))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "c")) (.pow (.var "d") (.int 2))) (.app2 .add (.var "p") (.int 1))) (.int (-1))))) (rubi534r23Nondeg.integrals.head!.2) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.var "p")) (.pow (.int 2) (.int (-1)))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkp : Interp.real.toInt? (env "p") with _ | kp
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi534r23Nondeg, Defined, eval, hkp, hm1, h2] at h0
  have hep : env "p" = (kp : ℝ) := (Interp.real.toInt?_eq _ _).1 hkp
  have hop1 : Interp.real.toInt? ((-1 : ℝ) + (kp : ℝ)) = some (-1 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp1 : Interp.real.toInt? ((kp : ℝ) + (-1 : ℝ)) = some (kp + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hop2 : Interp.real.toInt? ((1 : ℝ) + (kp : ℝ)) = some (1 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp2 : Interp.real.toInt? ((kp : ℝ) + (1 : ℝ)) = some (kp + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hop3 : Interp.real.toInt? ((-2 : ℝ) + (kp : ℝ)) = some (-2 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp3 : Interp.real.toInt? ((kp : ℝ) + (-2 : ℝ)) = some (kp + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hop4 : Interp.real.toInt? ((2 : ℝ) + (kp : ℝ)) = some (2 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp4 : Interp.real.toInt? ((kp : ℝ) + (2 : ℝ)) = some (kp + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsp1 : Interp.real.toInt? ((kp : ℝ) - 1) = some (kp - 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsp2 : Interp.real.toInt? ((kp : ℝ) - 2) = some (kp - 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp00 : Interp.real.toInt? ((kp : ℝ) + -2 + -2) = some (kp + -2 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp01 : Interp.real.toInt? ((kp : ℝ) + -2 + -1) = some (kp + -2 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp02 : Interp.real.toInt? ((kp : ℝ) + -2 + 1) = some (kp + -2 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp03 : Interp.real.toInt? ((kp : ℝ) + -2 + 2) = some (kp + -2 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp10 : Interp.real.toInt? ((kp : ℝ) + -1 + -2) = some (kp + -1 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp11 : Interp.real.toInt? ((kp : ℝ) + -1 + -1) = some (kp + -1 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp12 : Interp.real.toInt? ((kp : ℝ) + -1 + 1) = some (kp + -1 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp13 : Interp.real.toInt? ((kp : ℝ) + -1 + 2) = some (kp + -1 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp20 : Interp.real.toInt? ((kp : ℝ) + 1 + -2) = some (kp + 1 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp21 : Interp.real.toInt? ((kp : ℝ) + 1 + -1) = some (kp + 1 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp22 : Interp.real.toInt? ((kp : ℝ) + 1 + 1) = some (kp + 1 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp23 : Interp.real.toInt? ((kp : ℝ) + 1 + 2) = some (kp + 1 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp30 : Interp.real.toInt? ((kp : ℝ) + 2 + -2) = some (kp + 2 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp31 : Interp.real.toInt? ((kp : ℝ) + 2 + -1) = some (kp + 2 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp32 : Interp.real.toInt? ((kp : ℝ) + 2 + 1) = some (kp + 2 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp33 : Interp.real.toInt? ((kp : ℝ) + 2 + 2) = some (kp + 2 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hkpp1 : Interp.real.toInt? (env "p" + 1) = some (kp + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpp2 : Interp.real.toInt? (env "p" + 2) = some (kp + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm1 : Interp.real.toInt? (env "p" + -1) = some (kp + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm2 : Interp.real.toInt? (env "p" + -2) = some (kp + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hbp0gt : 0 < kp := by
    have h := hcs (.gt (.var "p") (.int 0)) (by simp [rubi534r23Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hep] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi534r23Nondeg, Defined, eval, hm1, h2, hep, Interp.toInt?_cast] at h0
  try casesm* _ ∧ _
  have hc0 := hcs (.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d"))) (by simp [rubi534r23Nondeg])
  simp [Cond.Holds, Defined, eval, h2] at hc0
  have hc2 := hcs (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "c")) (.pow (.var "d") (.int 2))) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi534r23Nondeg])
  simp [Cond.Holds, Defined, eval, h2] at hc2
  try simp only [hep] at hc0 hc2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1]
  · simp [Calc.real, eval, Ok, Expr.varList, hm1, h2, hc0, hc2, hep, hqp2, Interp.toInt?_cast]
    rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [Defined, eval, hm1, h2, hc0, hc2, hep, hqp2, Interp.toInt?_cast]
    rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [Calc.real, rubi534r23Nondeg, eval, Ok, Expr.varList, hm1, h2, hc0, hep, hqp1]
    rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi534r23Nondeg, Defined, eval, hm1, h2, hc0, hep, hqp1]
    rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi534r23Nondeg, eval, d, hm1, h2, hm11, hn21, hc0, hep, hqp1, hqp2, Interp.toInt?_cast]
    try have hqpp00 : (kp : ℝ) ≠ 0 := by exact_mod_cast (show kp ≠ 0 by omega)
    try have hqpp10 : (kp : ℝ) + 1 ≠ 0 := by exact_mod_cast (show kp + 1 ≠ 0 by omega)
    try have hqpp20 : (kp : ℝ) + 2 ≠ 0 := by exact_mod_cast (show kp + 2 ≠ 0 by omega)
    try have hqpp30 : (kp : ℝ) + 3 ≠ 0 := by exact_mod_cast (show kp + 3 ≠ 0 by omega)
    try casesm* _ ∧ _
    field_simp
    ring1

set_option maxHeartbeats 1000000 in
/-- RUBI rubi534r24Nondeg: explicit term by the symbolic derivative. -/
theorem rubi534r24Nondeg_real : rubi534r24Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi534r24Nondeg.conditions rubi534r24Nondeg.body rubi534r24Nondeg.result rubi534r24Nondeg.integrals
  have hm1 : Interp.real.toInt? (-1 : ℝ) = some (-1) := by simpa using Interp.toInt?_cast Interp.real (-1)
  have hm2 : Interp.real.toInt? (-2 : ℝ) = some (-2) := by simpa using Interp.toInt?_cast Interp.real (-2)
  have h2 : Interp.real.toInt? (2 : ℝ) = some 2 := by simpa using Interp.toInt?_cast Interp.real 2
  have hm11 : Interp.real.toInt? (-1 + -1 : ℝ) = some (-2) := by
    rw [show (-1 + -1 : ℝ) = -2 by norm_num]; exact hm2
  have hn1 : Interp.real.toInt? (1 : ℝ) = some 1 := by simpa using Interp.toInt?_cast Interp.real 1
  have hn3 : Interp.real.toInt? (3 : ℝ) = some 3 := by simpa using Interp.toInt?_cast Interp.real 3
  have hn21 : Interp.real.toInt? (2 + -1 : ℝ) = some 1 := by rw [show (2 + -1 : ℝ) = 1 by norm_num]; exact hn1
  have hn31 : Interp.real.toInt? (3 + -1 : ℝ) = some 2 := by rw [show (3 + -1 : ℝ) = 2 by norm_num]; exact h2
  have hn32 : Interp.real.toInt? (3 + -2 : ℝ) = some 1 := by rw [show (3 + -2 : ℝ) = 1 by norm_num]; exact hn1
  have hn10 : Interp.real.toInt? (1 + -1 : ℝ) = some 0 := by simpa using Interp.toInt?_cast Interp.real 0
  have dln : ∀ z : ℝ, Interp.real.lnDefined z ↔ 0 < z := fun _ => Iff.rfl
  have dtan : ∀ z : ℝ, Interp.real.tanDefined z ↔ Real.cos z ≠ 0 := fun _ => Iff.rfl
  have dasin : ∀ z : ℝ, Interp.real.fnDefined .arcsin z ↔ -1 ≤ z ∧ z ≤ 1 := fun _ => Iff.rfl
  have dacos : ∀ z : ℝ, Interp.real.fnDefined .arccos z ↔ -1 ≤ z ∧ z ≤ 1 := fun _ => Iff.rfl
  refine antiderivRec_open Calc.real _ (.app2 .add (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.pow (.app2 .mul (.var "c") (.var "x")) (.int (-1)))))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.pow (.app2 .mul (.var "c") (.var "x")) (.int (-1)))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "c")) (.pow (.var "d") (.int 2))) (.app2 .add (.var "p") (.int 1))) (.int (-1))))) (rubi534r24Nondeg.integrals.head!.2) (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "p")) (.pow (.int 2) (.int (-1)))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkp : Interp.real.toInt? (env "p") with _ | kp
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi534r24Nondeg, Defined, eval, hkp, hm1, h2] at h0
  have hep : env "p" = (kp : ℝ) := (Interp.real.toInt?_eq _ _).1 hkp
  have hop1 : Interp.real.toInt? ((-1 : ℝ) + (kp : ℝ)) = some (-1 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp1 : Interp.real.toInt? ((kp : ℝ) + (-1 : ℝ)) = some (kp + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hop2 : Interp.real.toInt? ((1 : ℝ) + (kp : ℝ)) = some (1 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp2 : Interp.real.toInt? ((kp : ℝ) + (1 : ℝ)) = some (kp + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hop3 : Interp.real.toInt? ((-2 : ℝ) + (kp : ℝ)) = some (-2 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp3 : Interp.real.toInt? ((kp : ℝ) + (-2 : ℝ)) = some (kp + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hop4 : Interp.real.toInt? ((2 : ℝ) + (kp : ℝ)) = some (2 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp4 : Interp.real.toInt? ((kp : ℝ) + (2 : ℝ)) = some (kp + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsp1 : Interp.real.toInt? ((kp : ℝ) - 1) = some (kp - 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsp2 : Interp.real.toInt? ((kp : ℝ) - 2) = some (kp - 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp00 : Interp.real.toInt? ((kp : ℝ) + -2 + -2) = some (kp + -2 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp01 : Interp.real.toInt? ((kp : ℝ) + -2 + -1) = some (kp + -2 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp02 : Interp.real.toInt? ((kp : ℝ) + -2 + 1) = some (kp + -2 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp03 : Interp.real.toInt? ((kp : ℝ) + -2 + 2) = some (kp + -2 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp10 : Interp.real.toInt? ((kp : ℝ) + -1 + -2) = some (kp + -1 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp11 : Interp.real.toInt? ((kp : ℝ) + -1 + -1) = some (kp + -1 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp12 : Interp.real.toInt? ((kp : ℝ) + -1 + 1) = some (kp + -1 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp13 : Interp.real.toInt? ((kp : ℝ) + -1 + 2) = some (kp + -1 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp20 : Interp.real.toInt? ((kp : ℝ) + 1 + -2) = some (kp + 1 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp21 : Interp.real.toInt? ((kp : ℝ) + 1 + -1) = some (kp + 1 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp22 : Interp.real.toInt? ((kp : ℝ) + 1 + 1) = some (kp + 1 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp23 : Interp.real.toInt? ((kp : ℝ) + 1 + 2) = some (kp + 1 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp30 : Interp.real.toInt? ((kp : ℝ) + 2 + -2) = some (kp + 2 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp31 : Interp.real.toInt? ((kp : ℝ) + 2 + -1) = some (kp + 2 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp32 : Interp.real.toInt? ((kp : ℝ) + 2 + 1) = some (kp + 2 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp33 : Interp.real.toInt? ((kp : ℝ) + 2 + 2) = some (kp + 2 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hkpp1 : Interp.real.toInt? (env "p" + 1) = some (kp + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpp2 : Interp.real.toInt? (env "p" + 2) = some (kp + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm1 : Interp.real.toInt? (env "p" + -1) = some (kp + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm2 : Interp.real.toInt? (env "p" + -2) = some (kp + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hbp0gt : 0 < kp := by
    have h := hcs (.gt (.var "p") (.int 0)) (by simp [rubi534r24Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hep] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi534r24Nondeg, Defined, eval, hm1, h2, hep, Interp.toInt?_cast] at h0
  try casesm* _ ∧ _
  have hc0 := hcs (.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d"))) (by simp [rubi534r24Nondeg])
  simp [Cond.Holds, Defined, eval, h2] at hc0
  have hc2 := hcs (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "c")) (.pow (.var "d") (.int 2))) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi534r24Nondeg])
  simp [Cond.Holds, Defined, eval, h2] at hc2
  try simp only [hep] at hc0 hc2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1]
  · simp [Calc.real, eval, Ok, Expr.varList, hm1, h2, hc0, hc2, hep, hqp2, Interp.toInt?_cast]
    rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [Defined, eval, hm1, h2, hc0, hc2, hep, hqp2, Interp.toInt?_cast]
    rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [Calc.real, rubi534r24Nondeg, eval, Ok, Expr.varList, hm1, h2, hc0, hc2, hep, hqp1]
    rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi534r24Nondeg, Defined, eval, hm1, h2, hc0, hc2, hep, hqp1]
    rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi534r24Nondeg, eval, d, hm1, h2, hm11, hn21, hc0, hep, hqp1, hqp2, Interp.toInt?_cast]
    try have hqpp00 : (kp : ℝ) ≠ 0 := by exact_mod_cast (show kp ≠ 0 by omega)
    try have hqpp10 : (kp : ℝ) + 1 ≠ 0 := by exact_mod_cast (show kp + 1 ≠ 0 by omega)
    try have hqpp20 : (kp : ℝ) + 2 ≠ 0 := by exact_mod_cast (show kp + 2 ≠ 0 by omega)
    try have hqpp30 : (kp : ℝ) + 3 ≠ 0 := by exact_mod_cast (show kp + 3 ≠ 0 by omega)
    try casesm* _ ∧ _
    field_simp
    ring1

set_option maxHeartbeats 1000000 in
/-- RUBI rubi534r65Nondeg: explicit term by the symbolic derivative. -/
theorem rubi534r65Nondeg_real : rubi534r65Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi534r65Nondeg.conditions rubi534r65Nondeg.body rubi534r65Nondeg.result rubi534r65Nondeg.integrals
  have hm1 : Interp.real.toInt? (-1 : ℝ) = some (-1) := by simpa using Interp.toInt?_cast Interp.real (-1)
  have hm2 : Interp.real.toInt? (-2 : ℝ) = some (-2) := by simpa using Interp.toInt?_cast Interp.real (-2)
  have h2 : Interp.real.toInt? (2 : ℝ) = some 2 := by simpa using Interp.toInt?_cast Interp.real 2
  have hm11 : Interp.real.toInt? (-1 + -1 : ℝ) = some (-2) := by
    rw [show (-1 + -1 : ℝ) = -2 by norm_num]; exact hm2
  have hn1 : Interp.real.toInt? (1 : ℝ) = some 1 := by simpa using Interp.toInt?_cast Interp.real 1
  have hn3 : Interp.real.toInt? (3 : ℝ) = some 3 := by simpa using Interp.toInt?_cast Interp.real 3
  have hn21 : Interp.real.toInt? (2 + -1 : ℝ) = some 1 := by rw [show (2 + -1 : ℝ) = 1 by norm_num]; exact hn1
  have hn31 : Interp.real.toInt? (3 + -1 : ℝ) = some 2 := by rw [show (3 + -1 : ℝ) = 2 by norm_num]; exact h2
  have hn32 : Interp.real.toInt? (3 + -2 : ℝ) = some 1 := by rw [show (3 + -2 : ℝ) = 1 by norm_num]; exact hn1
  have hn10 : Interp.real.toInt? (1 + -1 : ℝ) = some 0 := by simpa using Interp.toInt?_cast Interp.real 0
  have dln : ∀ z : ℝ, Interp.real.lnDefined z ↔ 0 < z := fun _ => Iff.rfl
  have dtan : ∀ z : ℝ, Interp.real.tanDefined z ↔ Real.cos z ≠ 0 := fun _ => Iff.rfl
  have dasin : ∀ z : ℝ, Interp.real.fnDefined .arcsin z ↔ -1 ≤ z ∧ z ≤ 1 := fun _ => Iff.rfl
  have dacos : ∀ z : ℝ, Interp.real.fnDefined .arccos z ↔ -1 ≤ z ∧ z ≤ 1 := fun _ => Iff.rfl
  refine antiderivRec_open Calc.real _ (.app2 .add (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 1))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.pow (.var "c") (.int 3))) (.pow (.var "d") (.int 2))) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "x")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.pow (.var "c") (.int 2))) (.var "d")) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2))))) (.int (-1))))) (rubi534r65Nondeg.integrals.head!.2) (.app2 .mul (.app2 .mul (.var "b") (.var "p")) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkp : Interp.real.toInt? (env "p") with _ | kp
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi534r65Nondeg, Defined, eval, hkp, hm1, h2] at h0
  have hep : env "p" = (kp : ℝ) := (Interp.real.toInt?_eq _ _).1 hkp
  have hop1 : Interp.real.toInt? ((-1 : ℝ) + (kp : ℝ)) = some (-1 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp1 : Interp.real.toInt? ((kp : ℝ) + (-1 : ℝ)) = some (kp + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hop2 : Interp.real.toInt? ((1 : ℝ) + (kp : ℝ)) = some (1 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp2 : Interp.real.toInt? ((kp : ℝ) + (1 : ℝ)) = some (kp + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hop3 : Interp.real.toInt? ((-2 : ℝ) + (kp : ℝ)) = some (-2 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp3 : Interp.real.toInt? ((kp : ℝ) + (-2 : ℝ)) = some (kp + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hop4 : Interp.real.toInt? ((2 : ℝ) + (kp : ℝ)) = some (2 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp4 : Interp.real.toInt? ((kp : ℝ) + (2 : ℝ)) = some (kp + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsp1 : Interp.real.toInt? ((kp : ℝ) - 1) = some (kp - 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsp2 : Interp.real.toInt? ((kp : ℝ) - 2) = some (kp - 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp00 : Interp.real.toInt? ((kp : ℝ) + -2 + -2) = some (kp + -2 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp01 : Interp.real.toInt? ((kp : ℝ) + -2 + -1) = some (kp + -2 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp02 : Interp.real.toInt? ((kp : ℝ) + -2 + 1) = some (kp + -2 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp03 : Interp.real.toInt? ((kp : ℝ) + -2 + 2) = some (kp + -2 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp10 : Interp.real.toInt? ((kp : ℝ) + -1 + -2) = some (kp + -1 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp11 : Interp.real.toInt? ((kp : ℝ) + -1 + -1) = some (kp + -1 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp12 : Interp.real.toInt? ((kp : ℝ) + -1 + 1) = some (kp + -1 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp13 : Interp.real.toInt? ((kp : ℝ) + -1 + 2) = some (kp + -1 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp20 : Interp.real.toInt? ((kp : ℝ) + 1 + -2) = some (kp + 1 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp21 : Interp.real.toInt? ((kp : ℝ) + 1 + -1) = some (kp + 1 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp22 : Interp.real.toInt? ((kp : ℝ) + 1 + 1) = some (kp + 1 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp23 : Interp.real.toInt? ((kp : ℝ) + 1 + 2) = some (kp + 1 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp30 : Interp.real.toInt? ((kp : ℝ) + 2 + -2) = some (kp + 2 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp31 : Interp.real.toInt? ((kp : ℝ) + 2 + -1) = some (kp + 2 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp32 : Interp.real.toInt? ((kp : ℝ) + 2 + 1) = some (kp + 2 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp33 : Interp.real.toInt? ((kp : ℝ) + 2 + 2) = some (kp + 2 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hkpp1 : Interp.real.toInt? (env "p" + 1) = some (kp + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpp2 : Interp.real.toInt? (env "p" + 2) = some (kp + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm1 : Interp.real.toInt? (env "p" + -1) = some (kp + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm2 : Interp.real.toInt? (env "p" + -2) = some (kp + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hbp0gt : 0 < kp := by
    have h := hcs (.gt (.var "p") (.int 0)) (by simp [rubi534r65Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hep] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi534r65Nondeg, Defined, eval, hm1, h2, hep, Interp.toInt?_cast] at h0
  try casesm* _ ∧ _
  have hc0 := hcs (.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d"))) (by simp [rubi534r65Nondeg])
  simp [Cond.Holds, Defined, eval, h2] at hc0
  have hc2 := hcs (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.pow (.var "c") (.int 3))) (.pow (.var "d") (.int 2))) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi534r65Nondeg])
  simp [Cond.Holds, Defined, eval, h2, hn3] at hc2
  try simp only [hep] at hc0 hc2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc2]
  · simp [Calc.real, eval, Ok, Expr.varList, hm1, h2, hc0, hc2, hep, hqp2, Interp.toInt?_cast]
    rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [Defined, eval, hm1, h2, hc0, hc2, hep, hqp2, Interp.toInt?_cast]
    rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [Calc.real, rubi534r65Nondeg, eval, Ok, Expr.varList, hm1, h2, hc0, hep, hqp1]
    rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi534r65Nondeg, Defined, eval, hm1, h2, hc0, hep, hqp1]
    rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi534r65Nondeg, eval, d, hm1, h2, hm11, hn3, hn21, hn31, hc0, hep, hqp1, hqp2, Interp.toInt?_cast]
    try have hqpp00 : (kp : ℝ) ≠ 0 := by exact_mod_cast (show kp ≠ 0 by omega)
    try have hqpp10 : (kp : ℝ) + 1 ≠ 0 := by exact_mod_cast (show kp + 1 ≠ 0 by omega)
    try have hqpp20 : (kp : ℝ) + 2 ≠ 0 := by exact_mod_cast (show kp + 2 ≠ 0 by omega)
    try have hqpp30 : (kp : ℝ) + 3 ≠ 0 := by exact_mod_cast (show kp + 3 ≠ 0 by omega)
    try casesm* _ ∧ _
    field_simp
    ring1

set_option maxHeartbeats 1000000 in
/-- RUBI rubi534r66Nondeg: explicit term by the symbolic derivative. -/
theorem rubi534r66Nondeg_real : rubi534r66Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi534r66Nondeg.conditions rubi534r66Nondeg.body rubi534r66Nondeg.result rubi534r66Nondeg.integrals
  have hm1 : Interp.real.toInt? (-1 : ℝ) = some (-1) := by simpa using Interp.toInt?_cast Interp.real (-1)
  have hm2 : Interp.real.toInt? (-2 : ℝ) = some (-2) := by simpa using Interp.toInt?_cast Interp.real (-2)
  have h2 : Interp.real.toInt? (2 : ℝ) = some 2 := by simpa using Interp.toInt?_cast Interp.real 2
  have hm11 : Interp.real.toInt? (-1 + -1 : ℝ) = some (-2) := by
    rw [show (-1 + -1 : ℝ) = -2 by norm_num]; exact hm2
  have hn1 : Interp.real.toInt? (1 : ℝ) = some 1 := by simpa using Interp.toInt?_cast Interp.real 1
  have hn3 : Interp.real.toInt? (3 : ℝ) = some 3 := by simpa using Interp.toInt?_cast Interp.real 3
  have hn21 : Interp.real.toInt? (2 + -1 : ℝ) = some 1 := by rw [show (2 + -1 : ℝ) = 1 by norm_num]; exact hn1
  have hn31 : Interp.real.toInt? (3 + -1 : ℝ) = some 2 := by rw [show (3 + -1 : ℝ) = 2 by norm_num]; exact h2
  have hn32 : Interp.real.toInt? (3 + -2 : ℝ) = some 1 := by rw [show (3 + -2 : ℝ) = 1 by norm_num]; exact hn1
  have hn10 : Interp.real.toInt? (1 + -1 : ℝ) = some 0 := by simpa using Interp.toInt?_cast Interp.real 0
  have dln : ∀ z : ℝ, Interp.real.lnDefined z ↔ 0 < z := fun _ => Iff.rfl
  have dtan : ∀ z : ℝ, Interp.real.tanDefined z ↔ Real.cos z ≠ 0 := fun _ => Iff.rfl
  have dasin : ∀ z : ℝ, Interp.real.fnDefined .arcsin z ↔ -1 ≤ z ∧ z ≤ 1 := fun _ => Iff.rfl
  have dacos : ∀ z : ℝ, Interp.real.fnDefined .arccos z ↔ -1 ≤ z ∧ z ≤ 1 := fun _ => Iff.rfl
  refine antiderivRec_open Calc.real _ (.app2 .add (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.pow (.app2 .mul (.var "c") (.var "x")) (.int (-1)))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.pow (.var "c") (.int 3))) (.pow (.var "d") (.int 2))) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "x")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.pow (.app2 .mul (.var "c") (.var "x")) (.int (-1)))))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.pow (.var "c") (.int 2))) (.var "d")) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2))))) (.int (-1))))) (rubi534r66Nondeg.integrals.head!.2) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "p")) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkp : Interp.real.toInt? (env "p") with _ | kp
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi534r66Nondeg, Defined, eval, hkp, hm1, h2] at h0
  have hep : env "p" = (kp : ℝ) := (Interp.real.toInt?_eq _ _).1 hkp
  have hop1 : Interp.real.toInt? ((-1 : ℝ) + (kp : ℝ)) = some (-1 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp1 : Interp.real.toInt? ((kp : ℝ) + (-1 : ℝ)) = some (kp + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hop2 : Interp.real.toInt? ((1 : ℝ) + (kp : ℝ)) = some (1 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp2 : Interp.real.toInt? ((kp : ℝ) + (1 : ℝ)) = some (kp + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hop3 : Interp.real.toInt? ((-2 : ℝ) + (kp : ℝ)) = some (-2 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp3 : Interp.real.toInt? ((kp : ℝ) + (-2 : ℝ)) = some (kp + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hop4 : Interp.real.toInt? ((2 : ℝ) + (kp : ℝ)) = some (2 + kp) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqp4 : Interp.real.toInt? ((kp : ℝ) + (2 : ℝ)) = some (kp + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsp1 : Interp.real.toInt? ((kp : ℝ) - 1) = some (kp - 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsp2 : Interp.real.toInt? ((kp : ℝ) - 2) = some (kp - 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp00 : Interp.real.toInt? ((kp : ℝ) + -2 + -2) = some (kp + -2 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp01 : Interp.real.toInt? ((kp : ℝ) + -2 + -1) = some (kp + -2 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp02 : Interp.real.toInt? ((kp : ℝ) + -2 + 1) = some (kp + -2 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp03 : Interp.real.toInt? ((kp : ℝ) + -2 + 2) = some (kp + -2 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp10 : Interp.real.toInt? ((kp : ℝ) + -1 + -2) = some (kp + -1 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp11 : Interp.real.toInt? ((kp : ℝ) + -1 + -1) = some (kp + -1 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp12 : Interp.real.toInt? ((kp : ℝ) + -1 + 1) = some (kp + -1 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp13 : Interp.real.toInt? ((kp : ℝ) + -1 + 2) = some (kp + -1 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp20 : Interp.real.toInt? ((kp : ℝ) + 1 + -2) = some (kp + 1 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp21 : Interp.real.toInt? ((kp : ℝ) + 1 + -1) = some (kp + 1 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp22 : Interp.real.toInt? ((kp : ℝ) + 1 + 1) = some (kp + 1 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp23 : Interp.real.toInt? ((kp : ℝ) + 1 + 2) = some (kp + 1 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp30 : Interp.real.toInt? ((kp : ℝ) + 2 + -2) = some (kp + 2 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp31 : Interp.real.toInt? ((kp : ℝ) + 2 + -1) = some (kp + 2 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp32 : Interp.real.toInt? ((kp : ℝ) + 2 + 1) = some (kp + 2 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp33 : Interp.real.toInt? ((kp : ℝ) + 2 + 2) = some (kp + 2 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hkpp1 : Interp.real.toInt? (env "p" + 1) = some (kp + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpp2 : Interp.real.toInt? (env "p" + 2) = some (kp + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm1 : Interp.real.toInt? (env "p" + -1) = some (kp + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm2 : Interp.real.toInt? (env "p" + -2) = some (kp + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hbp0gt : 0 < kp := by
    have h := hcs (.gt (.var "p") (.int 0)) (by simp [rubi534r66Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hep] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi534r66Nondeg, Defined, eval, hm1, h2, hep, Interp.toInt?_cast] at h0
  try casesm* _ ∧ _
  have hc0 := hcs (.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d"))) (by simp [rubi534r66Nondeg])
  simp [Cond.Holds, Defined, eval, h2] at hc0
  have hc2 := hcs (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.pow (.var "c") (.int 3))) (.pow (.var "d") (.int 2))) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi534r66Nondeg])
  simp [Cond.Holds, Defined, eval, h2, hn3] at hc2
  try simp only [hep] at hc0 hc2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc2]
  · simp [Calc.real, eval, Ok, Expr.varList, hm1, h2, hc0, hc2, hep, hqp2, Interp.toInt?_cast]
    rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [Defined, eval, hm1, h2, hc0, hc2, hep, hqp2, Interp.toInt?_cast]
    rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [Calc.real, rubi534r66Nondeg, eval, Ok, Expr.varList, hm1, h2, hc0, hc2, hep, hqp1]
    rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi534r66Nondeg, Defined, eval, hm1, h2, hc0, hc2, hep, hqp1]
    rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi534r66Nondeg, eval, d, hm1, h2, hm11, hn3, hn21, hn31, hc0, hep, hqp1, hqp2, Interp.toInt?_cast]
    try have hqpp00 : (kp : ℝ) ≠ 0 := by exact_mod_cast (show kp ≠ 0 by omega)
    try have hqpp10 : (kp : ℝ) + 1 ≠ 0 := by exact_mod_cast (show kp + 1 ≠ 0 by omega)
    try have hqpp20 : (kp : ℝ) + 2 ≠ 0 := by exact_mod_cast (show kp + 2 ≠ 0 by omega)
    try have hqpp30 : (kp : ℝ) + 3 ≠ 0 := by exact_mod_cast (show kp + 3 ≠ 0 by omega)
    try casesm* _ ∧ _
    field_simp
    ring1

set_option maxHeartbeats 1000000 in
/-- RUBI rubi676r16Nondeg: explicit term by the symbolic derivative. -/
theorem rubi676r16Nondeg_real : rubi676r16Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi676r16Nondeg.conditions rubi676r16Nondeg.body rubi676r16Nondeg.result rubi676r16Nondeg.integrals
  have hm1 : Interp.real.toInt? (-1 : ℝ) = some (-1) := by simpa using Interp.toInt?_cast Interp.real (-1)
  have hm2 : Interp.real.toInt? (-2 : ℝ) = some (-2) := by simpa using Interp.toInt?_cast Interp.real (-2)
  have h2 : Interp.real.toInt? (2 : ℝ) = some 2 := by simpa using Interp.toInt?_cast Interp.real 2
  have hm11 : Interp.real.toInt? (-1 + -1 : ℝ) = some (-2) := by
    rw [show (-1 + -1 : ℝ) = -2 by norm_num]; exact hm2
  have hn1 : Interp.real.toInt? (1 : ℝ) = some 1 := by simpa using Interp.toInt?_cast Interp.real 1
  have hn3 : Interp.real.toInt? (3 : ℝ) = some 3 := by simpa using Interp.toInt?_cast Interp.real 3
  have hn21 : Interp.real.toInt? (2 + -1 : ℝ) = some 1 := by rw [show (2 + -1 : ℝ) = 1 by norm_num]; exact hn1
  have hn31 : Interp.real.toInt? (3 + -1 : ℝ) = some 2 := by rw [show (3 + -1 : ℝ) = 2 by norm_num]; exact h2
  have hn32 : Interp.real.toInt? (3 + -2 : ℝ) = some 1 := by rw [show (3 + -2 : ℝ) = 1 by norm_num]; exact hn1
  have hn10 : Interp.real.toInt? (1 + -1 : ℝ) = some 0 := by simpa using Interp.toInt?_cast Interp.real 0
  have dln : ∀ z : ℝ, Interp.real.lnDefined z ↔ 0 < z := fun _ => Iff.rfl
  have dtan : ∀ z : ℝ, Interp.real.tanDefined z ↔ Real.cos z ≠ 0 := fun _ => Iff.rfl
  have dasin : ∀ z : ℝ, Interp.real.fnDefined .arcsin z ↔ -1 ≤ z ∧ z ≤ 1 := fun _ => Iff.rfl
  have dacos : ∀ z : ℝ, Interp.real.fnDefined .arccos z ↔ -1 ≤ z ∧ z ≤ 1 := fun _ => Iff.rfl
  refine antiderivRec_open Calc.real _ (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (rubi676r16Nondeg.integrals.head!.2) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.var "m")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.real.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi676r16Nondeg, Defined, eval, hkm] at h0
  have hem : env "m" = (km : ℝ) := (Interp.real.toInt?_eq _ _).1 hkm
  have hom1 : Interp.real.toInt? ((-1 : ℝ) + (km : ℝ)) = some (-1 + km) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm1 : Interp.real.toInt? ((km : ℝ) + (-1 : ℝ)) = some (km + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hom2 : Interp.real.toInt? ((1 : ℝ) + (km : ℝ)) = some (1 + km) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm2 : Interp.real.toInt? ((km : ℝ) + (1 : ℝ)) = some (km + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hom3 : Interp.real.toInt? ((-2 : ℝ) + (km : ℝ)) = some (-2 + km) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm3 : Interp.real.toInt? ((km : ℝ) + (-2 : ℝ)) = some (km + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hom4 : Interp.real.toInt? ((2 : ℝ) + (km : ℝ)) = some (2 + km) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm4 : Interp.real.toInt? ((km : ℝ) + (2 : ℝ)) = some (km + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm1 : Interp.real.toInt? ((km : ℝ) - 1) = some (km - 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm2 : Interp.real.toInt? ((km : ℝ) - 2) = some (km - 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm00 : Interp.real.toInt? ((km : ℝ) + -2 + -2) = some (km + -2 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm01 : Interp.real.toInt? ((km : ℝ) + -2 + -1) = some (km + -2 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm02 : Interp.real.toInt? ((km : ℝ) + -2 + 1) = some (km + -2 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm03 : Interp.real.toInt? ((km : ℝ) + -2 + 2) = some (km + -2 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm10 : Interp.real.toInt? ((km : ℝ) + -1 + -2) = some (km + -1 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm11 : Interp.real.toInt? ((km : ℝ) + -1 + -1) = some (km + -1 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm12 : Interp.real.toInt? ((km : ℝ) + -1 + 1) = some (km + -1 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm13 : Interp.real.toInt? ((km : ℝ) + -1 + 2) = some (km + -1 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm20 : Interp.real.toInt? ((km : ℝ) + 1 + -2) = some (km + 1 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm21 : Interp.real.toInt? ((km : ℝ) + 1 + -1) = some (km + 1 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm22 : Interp.real.toInt? ((km : ℝ) + 1 + 1) = some (km + 1 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm23 : Interp.real.toInt? ((km : ℝ) + 1 + 2) = some (km + 1 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm30 : Interp.real.toInt? ((km : ℝ) + 2 + -2) = some (km + 2 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm31 : Interp.real.toInt? ((km : ℝ) + 2 + -1) = some (km + 2 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm32 : Interp.real.toInt? ((km : ℝ) + 2 + 1) = some (km + 2 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm33 : Interp.real.toInt? ((km : ℝ) + 2 + 2) = some (km + 2 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hkmp1 : Interp.real.toInt? (env "m" + 1) = some (km + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmp2 : Interp.real.toInt? (env "m" + 2) = some (km + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm1 : Interp.real.toInt? (env "m" + -1) = some (km + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm2 : Interp.real.toInt? (env "m" + -2) = some (km + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkm]; push_cast; ring)
  rcases hkn : Interp.real.toInt? (env "n") with _ | kn
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi676r16Nondeg, Defined, eval, hkn] at h0
  have hen : env "n" = (kn : ℝ) := (Interp.real.toInt?_eq _ _).1 hkn
  have hon1 : Interp.real.toInt? ((-1 : ℝ) + (kn : ℝ)) = some (-1 + kn) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn1 : Interp.real.toInt? ((kn : ℝ) + (-1 : ℝ)) = some (kn + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hon2 : Interp.real.toInt? ((1 : ℝ) + (kn : ℝ)) = some (1 + kn) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn2 : Interp.real.toInt? ((kn : ℝ) + (1 : ℝ)) = some (kn + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hon3 : Interp.real.toInt? ((-2 : ℝ) + (kn : ℝ)) = some (-2 + kn) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn3 : Interp.real.toInt? ((kn : ℝ) + (-2 : ℝ)) = some (kn + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hon4 : Interp.real.toInt? ((2 : ℝ) + (kn : ℝ)) = some (2 + kn) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn4 : Interp.real.toInt? ((kn : ℝ) + (2 : ℝ)) = some (kn + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn1 : Interp.real.toInt? ((kn : ℝ) - 1) = some (kn - 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn2 : Interp.real.toInt? ((kn : ℝ) - 2) = some (kn - 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn00 : Interp.real.toInt? ((kn : ℝ) + -2 + -2) = some (kn + -2 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn01 : Interp.real.toInt? ((kn : ℝ) + -2 + -1) = some (kn + -2 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn02 : Interp.real.toInt? ((kn : ℝ) + -2 + 1) = some (kn + -2 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn03 : Interp.real.toInt? ((kn : ℝ) + -2 + 2) = some (kn + -2 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn10 : Interp.real.toInt? ((kn : ℝ) + -1 + -2) = some (kn + -1 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn11 : Interp.real.toInt? ((kn : ℝ) + -1 + -1) = some (kn + -1 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn12 : Interp.real.toInt? ((kn : ℝ) + -1 + 1) = some (kn + -1 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn13 : Interp.real.toInt? ((kn : ℝ) + -1 + 2) = some (kn + -1 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn20 : Interp.real.toInt? ((kn : ℝ) + 1 + -2) = some (kn + 1 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn21 : Interp.real.toInt? ((kn : ℝ) + 1 + -1) = some (kn + 1 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn22 : Interp.real.toInt? ((kn : ℝ) + 1 + 1) = some (kn + 1 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn23 : Interp.real.toInt? ((kn : ℝ) + 1 + 2) = some (kn + 1 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn30 : Interp.real.toInt? ((kn : ℝ) + 2 + -2) = some (kn + 2 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn31 : Interp.real.toInt? ((kn : ℝ) + 2 + -1) = some (kn + 2 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn32 : Interp.real.toInt? ((kn : ℝ) + 2 + 1) = some (kn + 2 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn33 : Interp.real.toInt? ((kn : ℝ) + 2 + 2) = some (kn + 2 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hknp1 : Interp.real.toInt? (env "n" + 1) = some (kn + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknp2 : Interp.real.toInt? (env "n" + 2) = some (kn + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm1 : Interp.real.toInt? (env "n" + -1) = some (kn + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm2 : Interp.real.toInt? (env "n" + -2) = some (kn + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hbm0gt : 0 < km := by
    have h := hcs (.gt (.var "m") (.int 0)) (by simp [rubi676r16Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hem] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi676r16Nondeg, Defined, eval, hem, hen, Interp.toInt?_cast] at h0
  try casesm* _ ∧ _
  have hc2 := hcs (.ne (.var "n") (.int (-1))) (by simp [rubi676r16Nondeg])
  simp [Cond.Holds, Defined, eval] at hc2
  have hc3 := hcs (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.int 0)) (by simp [rubi676r16Nondeg])
  simp [Cond.Holds, Defined, eval] at hc3
  try simp only [hen] at hc2 hc3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc3, hen]
  · simp [eval, Ok, Expr.varList, hm1, hc3, hem, hen, hqn2, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : ¬ kn < -2 := by omega); (try have : ¬ kn + -2 < 0 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : ¬ kn < -1 := by omega); (try have : ¬ kn + -1 < 0 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [Defined, eval, hm1, hc3, hem, hen, hqn2, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : ¬ kn < -2 := by omega); (try have : ¬ kn + -2 < 0 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : ¬ kn < -1 := by omega); (try have : ¬ kn + -1 < 0 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [Calc.real, rubi676r16Nondeg, eval, Ok, Expr.varList, hem, hqm1, hen, hqn2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : ¬ kn < -2 := by omega); (try have : ¬ kn + -2 < 0 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : ¬ kn < -1 := by omega); (try have : ¬ kn + -1 < 0 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi676r16Nondeg, Defined, eval, hem, hqm1, hen, hqn2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : ¬ kn < -2 := by omega); (try have : ¬ kn + -2 < 0 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : ¬ kn < -1 := by omega); (try have : ¬ kn + -1 < 0 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi676r16Nondeg, eval, d, hm1, hm11, hem, hqm1, hen, hqn2, Interp.toInt?_cast]
    try have hqmp00 : (km : ℝ) ≠ 0 := by exact_mod_cast (show km ≠ 0 by omega)
    try have hqmp10 : (km : ℝ) + 1 ≠ 0 := by exact_mod_cast (show km + 1 ≠ 0 by omega)
    try have hqmp20 : (km : ℝ) + 2 ≠ 0 := by exact_mod_cast (show km + 2 ≠ 0 by omega)
    try have hqmp30 : (km : ℝ) + 3 ≠ 0 := by exact_mod_cast (show km + 3 ≠ 0 by omega)
    have hz1 : (env "e" + (env "f" * t)) ≠ 0 ∨ 0 ≤ km + -1 := by
      exact Or.inr (by omega)
    try rw [show (env "e" + (env "f" * t)) ^ (km) = (env "e" + (env "f" * t)) ^ (km + -1) * (env "e" + (env "f" * t)) ^ 1 from by
      have := zsplit ((env "e" + (env "f" * t))) (km + -1) 1 hz1
      rwa [show km + -1 + ((1 : ℕ) : ℤ) = km by push_cast; ring] at this]
    try generalize (env "e" + (env "f" * t)) ^ (km + -1) = P1
    try casesm* _ ∧ _
    field_simp
    ring1

set_option maxHeartbeats 1000000 in
/-- RUBI rubi676r16Nondeg: explicit term by the symbolic derivative. -/
theorem rubi676r16Nondeg_complex : rubi676r16Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi676r16Nondeg.conditions rubi676r16Nondeg.body rubi676r16Nondeg.result rubi676r16Nondeg.integrals
  have hm1 : Interp.complex.toInt? (-1 : ℂ) = some (-1) := by simpa using Interp.toInt?_cast Interp.complex (-1)
  have hm2 : Interp.complex.toInt? (-2 : ℂ) = some (-2) := by simpa using Interp.toInt?_cast Interp.complex (-2)
  have h2 : Interp.complex.toInt? (2 : ℂ) = some 2 := by simpa using Interp.toInt?_cast Interp.complex 2
  have hm11 : Interp.complex.toInt? (-1 + -1 : ℂ) = some (-2) := by
    rw [show (-1 + -1 : ℂ) = -2 by norm_num]; exact hm2
  have hn1 : Interp.complex.toInt? (1 : ℂ) = some 1 := by simpa using Interp.toInt?_cast Interp.complex 1
  have hn3 : Interp.complex.toInt? (3 : ℂ) = some 3 := by simpa using Interp.toInt?_cast Interp.complex 3
  have hn21 : Interp.complex.toInt? (2 + -1 : ℂ) = some 1 := by rw [show (2 + -1 : ℂ) = 1 by norm_num]; exact hn1
  have hn31 : Interp.complex.toInt? (3 + -1 : ℂ) = some 2 := by rw [show (3 + -1 : ℂ) = 2 by norm_num]; exact h2
  have hn32 : Interp.complex.toInt? (3 + -2 : ℂ) = some 1 := by rw [show (3 + -2 : ℂ) = 1 by norm_num]; exact hn1
  have hn10 : Interp.complex.toInt? (1 + -1 : ℂ) = some 0 := by simpa using Interp.toInt?_cast Interp.complex 0
  have dln : ∀ z : ℂ, Interp.complex.lnDefined z ↔ z ≠ 0 := fun _ => Iff.rfl
  have dtan : ∀ z : ℂ, Interp.complex.tanDefined z ↔ Complex.cos z ≠ 0 := fun _ => Iff.rfl
  refine antiderivRec_open Calc.complex _ (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (rubi676r16Nondeg.integrals.head!.2) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.var "m")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.complex.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi676r16Nondeg, Defined, eval, hkm] at h0
  have hem : env "m" = (km : ℂ) := (Interp.complex.toInt?_eq _ _).1 hkm
  have hom1 : Interp.complex.toInt? ((-1 : ℂ) + (km : ℂ)) = some (-1 + km) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm1 : Interp.complex.toInt? ((km : ℂ) + (-1 : ℂ)) = some (km + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hom2 : Interp.complex.toInt? ((1 : ℂ) + (km : ℂ)) = some (1 + km) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm2 : Interp.complex.toInt? ((km : ℂ) + (1 : ℂ)) = some (km + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hom3 : Interp.complex.toInt? ((-2 : ℂ) + (km : ℂ)) = some (-2 + km) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm3 : Interp.complex.toInt? ((km : ℂ) + (-2 : ℂ)) = some (km + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hom4 : Interp.complex.toInt? ((2 : ℂ) + (km : ℂ)) = some (2 + km) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm4 : Interp.complex.toInt? ((km : ℂ) + (2 : ℂ)) = some (km + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm1 : Interp.complex.toInt? ((km : ℂ) - 1) = some (km - 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm2 : Interp.complex.toInt? ((km : ℂ) - 2) = some (km - 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm00 : Interp.complex.toInt? ((km : ℂ) + -2 + -2) = some (km + -2 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm01 : Interp.complex.toInt? ((km : ℂ) + -2 + -1) = some (km + -2 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm02 : Interp.complex.toInt? ((km : ℂ) + -2 + 1) = some (km + -2 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm03 : Interp.complex.toInt? ((km : ℂ) + -2 + 2) = some (km + -2 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm10 : Interp.complex.toInt? ((km : ℂ) + -1 + -2) = some (km + -1 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm11 : Interp.complex.toInt? ((km : ℂ) + -1 + -1) = some (km + -1 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm12 : Interp.complex.toInt? ((km : ℂ) + -1 + 1) = some (km + -1 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm13 : Interp.complex.toInt? ((km : ℂ) + -1 + 2) = some (km + -1 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm20 : Interp.complex.toInt? ((km : ℂ) + 1 + -2) = some (km + 1 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm21 : Interp.complex.toInt? ((km : ℂ) + 1 + -1) = some (km + 1 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm22 : Interp.complex.toInt? ((km : ℂ) + 1 + 1) = some (km + 1 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm23 : Interp.complex.toInt? ((km : ℂ) + 1 + 2) = some (km + 1 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm30 : Interp.complex.toInt? ((km : ℂ) + 2 + -2) = some (km + 2 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm31 : Interp.complex.toInt? ((km : ℂ) + 2 + -1) = some (km + 2 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm32 : Interp.complex.toInt? ((km : ℂ) + 2 + 1) = some (km + 2 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm33 : Interp.complex.toInt? ((km : ℂ) + 2 + 2) = some (km + 2 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hkmp1 : Interp.complex.toInt? (env "m" + 1) = some (km + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmp2 : Interp.complex.toInt? (env "m" + 2) = some (km + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm1 : Interp.complex.toInt? (env "m" + -1) = some (km + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm2 : Interp.complex.toInt? (env "m" + -2) = some (km + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkm]; push_cast; ring)
  rcases hkn : Interp.complex.toInt? (env "n") with _ | kn
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi676r16Nondeg, Defined, eval, hkn] at h0
  have hen : env "n" = (kn : ℂ) := (Interp.complex.toInt?_eq _ _).1 hkn
  have hon1 : Interp.complex.toInt? ((-1 : ℂ) + (kn : ℂ)) = some (-1 + kn) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn1 : Interp.complex.toInt? ((kn : ℂ) + (-1 : ℂ)) = some (kn + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hon2 : Interp.complex.toInt? ((1 : ℂ) + (kn : ℂ)) = some (1 + kn) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn2 : Interp.complex.toInt? ((kn : ℂ) + (1 : ℂ)) = some (kn + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hon3 : Interp.complex.toInt? ((-2 : ℂ) + (kn : ℂ)) = some (-2 + kn) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn3 : Interp.complex.toInt? ((kn : ℂ) + (-2 : ℂ)) = some (kn + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hon4 : Interp.complex.toInt? ((2 : ℂ) + (kn : ℂ)) = some (2 + kn) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn4 : Interp.complex.toInt? ((kn : ℂ) + (2 : ℂ)) = some (kn + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn1 : Interp.complex.toInt? ((kn : ℂ) - 1) = some (kn - 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn2 : Interp.complex.toInt? ((kn : ℂ) - 2) = some (kn - 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn00 : Interp.complex.toInt? ((kn : ℂ) + -2 + -2) = some (kn + -2 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn01 : Interp.complex.toInt? ((kn : ℂ) + -2 + -1) = some (kn + -2 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn02 : Interp.complex.toInt? ((kn : ℂ) + -2 + 1) = some (kn + -2 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn03 : Interp.complex.toInt? ((kn : ℂ) + -2 + 2) = some (kn + -2 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn10 : Interp.complex.toInt? ((kn : ℂ) + -1 + -2) = some (kn + -1 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn11 : Interp.complex.toInt? ((kn : ℂ) + -1 + -1) = some (kn + -1 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn12 : Interp.complex.toInt? ((kn : ℂ) + -1 + 1) = some (kn + -1 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn13 : Interp.complex.toInt? ((kn : ℂ) + -1 + 2) = some (kn + -1 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn20 : Interp.complex.toInt? ((kn : ℂ) + 1 + -2) = some (kn + 1 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn21 : Interp.complex.toInt? ((kn : ℂ) + 1 + -1) = some (kn + 1 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn22 : Interp.complex.toInt? ((kn : ℂ) + 1 + 1) = some (kn + 1 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn23 : Interp.complex.toInt? ((kn : ℂ) + 1 + 2) = some (kn + 1 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn30 : Interp.complex.toInt? ((kn : ℂ) + 2 + -2) = some (kn + 2 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn31 : Interp.complex.toInt? ((kn : ℂ) + 2 + -1) = some (kn + 2 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn32 : Interp.complex.toInt? ((kn : ℂ) + 2 + 1) = some (kn + 2 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn33 : Interp.complex.toInt? ((kn : ℂ) + 2 + 2) = some (kn + 2 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hknp1 : Interp.complex.toInt? (env "n" + 1) = some (kn + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknp2 : Interp.complex.toInt? (env "n" + 2) = some (kn + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm1 : Interp.complex.toInt? (env "n" + -1) = some (kn + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm2 : Interp.complex.toInt? (env "n" + -2) = some (kn + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hbm0gt : 0 < km := by
    have h := hcs (.gt (.var "m") (.int 0)) (by simp [rubi676r16Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, hem, Complex.ext_iff] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi676r16Nondeg, Defined, eval, hem, hen, Interp.toInt?_cast] at h0
  try casesm* _ ∧ _
  have hc2 := hcs (.ne (.var "n") (.int (-1))) (by simp [rubi676r16Nondeg])
  simp [Cond.Holds, Defined, eval] at hc2
  have hc3 := hcs (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.int 0)) (by simp [rubi676r16Nondeg])
  simp [Cond.Holds, Defined, eval] at hc3
  try simp only [hen] at hc2 hc3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc3, hen]
  · simp [eval, Ok, Expr.varList, hm1, hc3, hem, hen, hqn2, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : ¬ kn < -2 := by omega); (try have : ¬ kn + -2 < 0 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : ¬ kn < -1 := by omega); (try have : ¬ kn + -1 < 0 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [Defined, eval, hm1, hc3, hem, hen, hqn2, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : ¬ kn < -2 := by omega); (try have : ¬ kn + -2 < 0 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : ¬ kn < -1 := by omega); (try have : ¬ kn + -1 < 0 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [Calc.complex, rubi676r16Nondeg, eval, Ok, Expr.varList, hem, hqm1, hen, hqn2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : ¬ kn < -2 := by omega); (try have : ¬ kn + -2 < 0 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : ¬ kn < -1 := by omega); (try have : ¬ kn + -1 < 0 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi676r16Nondeg, Defined, eval, hem, hqm1, hen, hqn2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : ¬ kn < -2 := by omega); (try have : ¬ kn + -2 < 0 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : ¬ kn < -1 := by omega); (try have : ¬ kn + -1 < 0 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi676r16Nondeg, eval, d, hm1, hm11, hem, hqm1, hen, hqn2, Interp.toInt?_cast]
    try have hqmp00 : (km : ℂ) ≠ 0 := by exact_mod_cast (show km ≠ 0 by omega)
    try have hqmp10 : (km : ℂ) + 1 ≠ 0 := by exact_mod_cast (show km + 1 ≠ 0 by omega)
    try have hqmp20 : (km : ℂ) + 2 ≠ 0 := by exact_mod_cast (show km + 2 ≠ 0 by omega)
    try have hqmp30 : (km : ℂ) + 3 ≠ 0 := by exact_mod_cast (show km + 3 ≠ 0 by omega)
    have hz1 : (env "e" + (env "f" * t)) ≠ 0 ∨ 0 ≤ km + -1 := by
      exact Or.inr (by omega)
    try rw [show (env "e" + (env "f" * t)) ^ (km) = (env "e" + (env "f" * t)) ^ (km + -1) * (env "e" + (env "f" * t)) ^ 1 from by
      have := zsplit ((env "e" + (env "f" * t))) (km + -1) 1 hz1
      rwa [show km + -1 + ((1 : ℕ) : ℤ) = km by push_cast; ring] at this]
    try generalize (env "e" + (env "f" * t)) ^ (km + -1) = P1
    try casesm* _ ∧ _
    field_simp
    ring1

set_option maxHeartbeats 1000000 in
/-- RUBI rubi676r17Nondeg: explicit term by the symbolic derivative. -/
theorem rubi676r17Nondeg_real : rubi676r17Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi676r17Nondeg.conditions rubi676r17Nondeg.body rubi676r17Nondeg.result rubi676r17Nondeg.integrals
  have hm1 : Interp.real.toInt? (-1 : ℝ) = some (-1) := by simpa using Interp.toInt?_cast Interp.real (-1)
  have hm2 : Interp.real.toInt? (-2 : ℝ) = some (-2) := by simpa using Interp.toInt?_cast Interp.real (-2)
  have h2 : Interp.real.toInt? (2 : ℝ) = some 2 := by simpa using Interp.toInt?_cast Interp.real 2
  have hm11 : Interp.real.toInt? (-1 + -1 : ℝ) = some (-2) := by
    rw [show (-1 + -1 : ℝ) = -2 by norm_num]; exact hm2
  have hn1 : Interp.real.toInt? (1 : ℝ) = some 1 := by simpa using Interp.toInt?_cast Interp.real 1
  have hn3 : Interp.real.toInt? (3 : ℝ) = some 3 := by simpa using Interp.toInt?_cast Interp.real 3
  have hn21 : Interp.real.toInt? (2 + -1 : ℝ) = some 1 := by rw [show (2 + -1 : ℝ) = 1 by norm_num]; exact hn1
  have hn31 : Interp.real.toInt? (3 + -1 : ℝ) = some 2 := by rw [show (3 + -1 : ℝ) = 2 by norm_num]; exact h2
  have hn32 : Interp.real.toInt? (3 + -2 : ℝ) = some 1 := by rw [show (3 + -2 : ℝ) = 1 by norm_num]; exact hn1
  have hn10 : Interp.real.toInt? (1 + -1 : ℝ) = some 0 := by simpa using Interp.toInt?_cast Interp.real 0
  have dln : ∀ z : ℝ, Interp.real.lnDefined z ↔ 0 < z := fun _ => Iff.rfl
  have dtan : ∀ z : ℝ, Interp.real.tanDefined z ↔ Real.cos z ≠ 0 := fun _ => Iff.rfl
  have dasin : ∀ z : ℝ, Interp.real.fnDefined .arcsin z ↔ -1 ≤ z ∧ z ≤ 1 := fun _ => Iff.rfl
  have dacos : ∀ z : ℝ, Interp.real.fnDefined .arccos z ↔ -1 ≤ z ∧ z ≤ 1 := fun _ => Iff.rfl
  refine antiderivRec_open Calc.real _ (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (rubi676r17Nondeg.integrals.head!.2) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.var "m")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.real.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi676r17Nondeg, Defined, eval, hkm] at h0
  have hem : env "m" = (km : ℝ) := (Interp.real.toInt?_eq _ _).1 hkm
  have hom1 : Interp.real.toInt? ((-1 : ℝ) + (km : ℝ)) = some (-1 + km) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm1 : Interp.real.toInt? ((km : ℝ) + (-1 : ℝ)) = some (km + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hom2 : Interp.real.toInt? ((1 : ℝ) + (km : ℝ)) = some (1 + km) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm2 : Interp.real.toInt? ((km : ℝ) + (1 : ℝ)) = some (km + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hom3 : Interp.real.toInt? ((-2 : ℝ) + (km : ℝ)) = some (-2 + km) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm3 : Interp.real.toInt? ((km : ℝ) + (-2 : ℝ)) = some (km + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hom4 : Interp.real.toInt? ((2 : ℝ) + (km : ℝ)) = some (2 + km) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm4 : Interp.real.toInt? ((km : ℝ) + (2 : ℝ)) = some (km + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm1 : Interp.real.toInt? ((km : ℝ) - 1) = some (km - 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm2 : Interp.real.toInt? ((km : ℝ) - 2) = some (km - 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm00 : Interp.real.toInt? ((km : ℝ) + -2 + -2) = some (km + -2 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm01 : Interp.real.toInt? ((km : ℝ) + -2 + -1) = some (km + -2 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm02 : Interp.real.toInt? ((km : ℝ) + -2 + 1) = some (km + -2 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm03 : Interp.real.toInt? ((km : ℝ) + -2 + 2) = some (km + -2 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm10 : Interp.real.toInt? ((km : ℝ) + -1 + -2) = some (km + -1 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm11 : Interp.real.toInt? ((km : ℝ) + -1 + -1) = some (km + -1 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm12 : Interp.real.toInt? ((km : ℝ) + -1 + 1) = some (km + -1 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm13 : Interp.real.toInt? ((km : ℝ) + -1 + 2) = some (km + -1 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm20 : Interp.real.toInt? ((km : ℝ) + 1 + -2) = some (km + 1 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm21 : Interp.real.toInt? ((km : ℝ) + 1 + -1) = some (km + 1 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm22 : Interp.real.toInt? ((km : ℝ) + 1 + 1) = some (km + 1 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm23 : Interp.real.toInt? ((km : ℝ) + 1 + 2) = some (km + 1 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm30 : Interp.real.toInt? ((km : ℝ) + 2 + -2) = some (km + 2 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm31 : Interp.real.toInt? ((km : ℝ) + 2 + -1) = some (km + 2 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm32 : Interp.real.toInt? ((km : ℝ) + 2 + 1) = some (km + 2 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm33 : Interp.real.toInt? ((km : ℝ) + 2 + 2) = some (km + 2 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hkmp1 : Interp.real.toInt? (env "m" + 1) = some (km + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmp2 : Interp.real.toInt? (env "m" + 2) = some (km + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm1 : Interp.real.toInt? (env "m" + -1) = some (km + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm2 : Interp.real.toInt? (env "m" + -2) = some (km + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkm]; push_cast; ring)
  rcases hkn : Interp.real.toInt? (env "n") with _ | kn
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi676r17Nondeg, Defined, eval, hkn] at h0
  have hen : env "n" = (kn : ℝ) := (Interp.real.toInt?_eq _ _).1 hkn
  have hon1 : Interp.real.toInt? ((-1 : ℝ) + (kn : ℝ)) = some (-1 + kn) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn1 : Interp.real.toInt? ((kn : ℝ) + (-1 : ℝ)) = some (kn + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hon2 : Interp.real.toInt? ((1 : ℝ) + (kn : ℝ)) = some (1 + kn) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn2 : Interp.real.toInt? ((kn : ℝ) + (1 : ℝ)) = some (kn + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hon3 : Interp.real.toInt? ((-2 : ℝ) + (kn : ℝ)) = some (-2 + kn) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn3 : Interp.real.toInt? ((kn : ℝ) + (-2 : ℝ)) = some (kn + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hon4 : Interp.real.toInt? ((2 : ℝ) + (kn : ℝ)) = some (2 + kn) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn4 : Interp.real.toInt? ((kn : ℝ) + (2 : ℝ)) = some (kn + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn1 : Interp.real.toInt? ((kn : ℝ) - 1) = some (kn - 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn2 : Interp.real.toInt? ((kn : ℝ) - 2) = some (kn - 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn00 : Interp.real.toInt? ((kn : ℝ) + -2 + -2) = some (kn + -2 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn01 : Interp.real.toInt? ((kn : ℝ) + -2 + -1) = some (kn + -2 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn02 : Interp.real.toInt? ((kn : ℝ) + -2 + 1) = some (kn + -2 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn03 : Interp.real.toInt? ((kn : ℝ) + -2 + 2) = some (kn + -2 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn10 : Interp.real.toInt? ((kn : ℝ) + -1 + -2) = some (kn + -1 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn11 : Interp.real.toInt? ((kn : ℝ) + -1 + -1) = some (kn + -1 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn12 : Interp.real.toInt? ((kn : ℝ) + -1 + 1) = some (kn + -1 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn13 : Interp.real.toInt? ((kn : ℝ) + -1 + 2) = some (kn + -1 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn20 : Interp.real.toInt? ((kn : ℝ) + 1 + -2) = some (kn + 1 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn21 : Interp.real.toInt? ((kn : ℝ) + 1 + -1) = some (kn + 1 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn22 : Interp.real.toInt? ((kn : ℝ) + 1 + 1) = some (kn + 1 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn23 : Interp.real.toInt? ((kn : ℝ) + 1 + 2) = some (kn + 1 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn30 : Interp.real.toInt? ((kn : ℝ) + 2 + -2) = some (kn + 2 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn31 : Interp.real.toInt? ((kn : ℝ) + 2 + -1) = some (kn + 2 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn32 : Interp.real.toInt? ((kn : ℝ) + 2 + 1) = some (kn + 2 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn33 : Interp.real.toInt? ((kn : ℝ) + 2 + 2) = some (kn + 2 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hknp1 : Interp.real.toInt? (env "n" + 1) = some (kn + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknp2 : Interp.real.toInt? (env "n" + 2) = some (kn + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm1 : Interp.real.toInt? (env "n" + -1) = some (kn + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm2 : Interp.real.toInt? (env "n" + -2) = some (kn + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hbm0gt : 0 < km := by
    have h := hcs (.gt (.var "m") (.int 0)) (by simp [rubi676r17Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hem] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi676r17Nondeg, Defined, eval, hem, hen, Interp.toInt?_cast] at h0
  try casesm* _ ∧ _
  have hc2 := hcs (.ne (.var "n") (.int (-1))) (by simp [rubi676r17Nondeg])
  simp [Cond.Holds, Defined, eval] at hc2
  have hc3 := hcs (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.int 0)) (by simp [rubi676r17Nondeg])
  simp [Cond.Holds, Defined, eval] at hc3
  try simp only [hen] at hc2 hc3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc3, hen]
  · simp [eval, Ok, Expr.varList, hm1, hc3, hem, hen, hqn2, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : ¬ kn < -2 := by omega); (try have : ¬ kn + -2 < 0 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : ¬ kn < -1 := by omega); (try have : ¬ kn + -1 < 0 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [Defined, eval, hm1, hc3, hem, hen, hqn2, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : ¬ kn < -2 := by omega); (try have : ¬ kn + -2 < 0 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : ¬ kn < -1 := by omega); (try have : ¬ kn + -1 < 0 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [Calc.real, rubi676r17Nondeg, eval, Ok, Expr.varList, hem, hqm1, hen, hqn2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : ¬ kn < -2 := by omega); (try have : ¬ kn + -2 < 0 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : ¬ kn < -1 := by omega); (try have : ¬ kn + -1 < 0 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi676r17Nondeg, Defined, eval, hem, hqm1, hen, hqn2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : ¬ kn < -2 := by omega); (try have : ¬ kn + -2 < 0 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : ¬ kn < -1 := by omega); (try have : ¬ kn + -1 < 0 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi676r17Nondeg, eval, d, hm1, hm11, hem, hqm1, hen, hqn2, Interp.toInt?_cast]
    try have hqmp00 : (km : ℝ) ≠ 0 := by exact_mod_cast (show km ≠ 0 by omega)
    try have hqmp10 : (km : ℝ) + 1 ≠ 0 := by exact_mod_cast (show km + 1 ≠ 0 by omega)
    try have hqmp20 : (km : ℝ) + 2 ≠ 0 := by exact_mod_cast (show km + 2 ≠ 0 by omega)
    try have hqmp30 : (km : ℝ) + 3 ≠ 0 := by exact_mod_cast (show km + 3 ≠ 0 by omega)
    have hz1 : (env "e" + (env "f" * t)) ≠ 0 ∨ 0 ≤ km + -1 := by
      exact Or.inr (by omega)
    try rw [show (env "e" + (env "f" * t)) ^ (km) = (env "e" + (env "f" * t)) ^ (km + -1) * (env "e" + (env "f" * t)) ^ 1 from by
      have := zsplit ((env "e" + (env "f" * t))) (km + -1) 1 hz1
      rwa [show km + -1 + ((1 : ℕ) : ℤ) = km by push_cast; ring] at this]
    try generalize (env "e" + (env "f" * t)) ^ (km + -1) = P1
    try casesm* _ ∧ _
    field_simp
    ring1

set_option maxHeartbeats 1000000 in
/-- RUBI rubi676r17Nondeg: explicit term by the symbolic derivative. -/
theorem rubi676r17Nondeg_complex : rubi676r17Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi676r17Nondeg.conditions rubi676r17Nondeg.body rubi676r17Nondeg.result rubi676r17Nondeg.integrals
  have hm1 : Interp.complex.toInt? (-1 : ℂ) = some (-1) := by simpa using Interp.toInt?_cast Interp.complex (-1)
  have hm2 : Interp.complex.toInt? (-2 : ℂ) = some (-2) := by simpa using Interp.toInt?_cast Interp.complex (-2)
  have h2 : Interp.complex.toInt? (2 : ℂ) = some 2 := by simpa using Interp.toInt?_cast Interp.complex 2
  have hm11 : Interp.complex.toInt? (-1 + -1 : ℂ) = some (-2) := by
    rw [show (-1 + -1 : ℂ) = -2 by norm_num]; exact hm2
  have hn1 : Interp.complex.toInt? (1 : ℂ) = some 1 := by simpa using Interp.toInt?_cast Interp.complex 1
  have hn3 : Interp.complex.toInt? (3 : ℂ) = some 3 := by simpa using Interp.toInt?_cast Interp.complex 3
  have hn21 : Interp.complex.toInt? (2 + -1 : ℂ) = some 1 := by rw [show (2 + -1 : ℂ) = 1 by norm_num]; exact hn1
  have hn31 : Interp.complex.toInt? (3 + -1 : ℂ) = some 2 := by rw [show (3 + -1 : ℂ) = 2 by norm_num]; exact h2
  have hn32 : Interp.complex.toInt? (3 + -2 : ℂ) = some 1 := by rw [show (3 + -2 : ℂ) = 1 by norm_num]; exact hn1
  have hn10 : Interp.complex.toInt? (1 + -1 : ℂ) = some 0 := by simpa using Interp.toInt?_cast Interp.complex 0
  have dln : ∀ z : ℂ, Interp.complex.lnDefined z ↔ z ≠ 0 := fun _ => Iff.rfl
  have dtan : ∀ z : ℂ, Interp.complex.tanDefined z ↔ Complex.cos z ≠ 0 := fun _ => Iff.rfl
  refine antiderivRec_open Calc.complex _ (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (rubi676r17Nondeg.integrals.head!.2) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.var "m")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.complex.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi676r17Nondeg, Defined, eval, hkm] at h0
  have hem : env "m" = (km : ℂ) := (Interp.complex.toInt?_eq _ _).1 hkm
  have hom1 : Interp.complex.toInt? ((-1 : ℂ) + (km : ℂ)) = some (-1 + km) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm1 : Interp.complex.toInt? ((km : ℂ) + (-1 : ℂ)) = some (km + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hom2 : Interp.complex.toInt? ((1 : ℂ) + (km : ℂ)) = some (1 + km) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm2 : Interp.complex.toInt? ((km : ℂ) + (1 : ℂ)) = some (km + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hom3 : Interp.complex.toInt? ((-2 : ℂ) + (km : ℂ)) = some (-2 + km) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm3 : Interp.complex.toInt? ((km : ℂ) + (-2 : ℂ)) = some (km + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hom4 : Interp.complex.toInt? ((2 : ℂ) + (km : ℂ)) = some (2 + km) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm4 : Interp.complex.toInt? ((km : ℂ) + (2 : ℂ)) = some (km + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm1 : Interp.complex.toInt? ((km : ℂ) - 1) = some (km - 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm2 : Interp.complex.toInt? ((km : ℂ) - 2) = some (km - 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm00 : Interp.complex.toInt? ((km : ℂ) + -2 + -2) = some (km + -2 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm01 : Interp.complex.toInt? ((km : ℂ) + -2 + -1) = some (km + -2 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm02 : Interp.complex.toInt? ((km : ℂ) + -2 + 1) = some (km + -2 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm03 : Interp.complex.toInt? ((km : ℂ) + -2 + 2) = some (km + -2 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm10 : Interp.complex.toInt? ((km : ℂ) + -1 + -2) = some (km + -1 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm11 : Interp.complex.toInt? ((km : ℂ) + -1 + -1) = some (km + -1 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm12 : Interp.complex.toInt? ((km : ℂ) + -1 + 1) = some (km + -1 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm13 : Interp.complex.toInt? ((km : ℂ) + -1 + 2) = some (km + -1 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm20 : Interp.complex.toInt? ((km : ℂ) + 1 + -2) = some (km + 1 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm21 : Interp.complex.toInt? ((km : ℂ) + 1 + -1) = some (km + 1 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm22 : Interp.complex.toInt? ((km : ℂ) + 1 + 1) = some (km + 1 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm23 : Interp.complex.toInt? ((km : ℂ) + 1 + 2) = some (km + 1 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm30 : Interp.complex.toInt? ((km : ℂ) + 2 + -2) = some (km + 2 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm31 : Interp.complex.toInt? ((km : ℂ) + 2 + -1) = some (km + 2 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm32 : Interp.complex.toInt? ((km : ℂ) + 2 + 1) = some (km + 2 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm33 : Interp.complex.toInt? ((km : ℂ) + 2 + 2) = some (km + 2 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hkmp1 : Interp.complex.toInt? (env "m" + 1) = some (km + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmp2 : Interp.complex.toInt? (env "m" + 2) = some (km + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm1 : Interp.complex.toInt? (env "m" + -1) = some (km + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm2 : Interp.complex.toInt? (env "m" + -2) = some (km + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkm]; push_cast; ring)
  rcases hkn : Interp.complex.toInt? (env "n") with _ | kn
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi676r17Nondeg, Defined, eval, hkn] at h0
  have hen : env "n" = (kn : ℂ) := (Interp.complex.toInt?_eq _ _).1 hkn
  have hon1 : Interp.complex.toInt? ((-1 : ℂ) + (kn : ℂ)) = some (-1 + kn) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn1 : Interp.complex.toInt? ((kn : ℂ) + (-1 : ℂ)) = some (kn + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hon2 : Interp.complex.toInt? ((1 : ℂ) + (kn : ℂ)) = some (1 + kn) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn2 : Interp.complex.toInt? ((kn : ℂ) + (1 : ℂ)) = some (kn + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hon3 : Interp.complex.toInt? ((-2 : ℂ) + (kn : ℂ)) = some (-2 + kn) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn3 : Interp.complex.toInt? ((kn : ℂ) + (-2 : ℂ)) = some (kn + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hon4 : Interp.complex.toInt? ((2 : ℂ) + (kn : ℂ)) = some (2 + kn) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn4 : Interp.complex.toInt? ((kn : ℂ) + (2 : ℂ)) = some (kn + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn1 : Interp.complex.toInt? ((kn : ℂ) - 1) = some (kn - 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn2 : Interp.complex.toInt? ((kn : ℂ) - 2) = some (kn - 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn00 : Interp.complex.toInt? ((kn : ℂ) + -2 + -2) = some (kn + -2 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn01 : Interp.complex.toInt? ((kn : ℂ) + -2 + -1) = some (kn + -2 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn02 : Interp.complex.toInt? ((kn : ℂ) + -2 + 1) = some (kn + -2 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn03 : Interp.complex.toInt? ((kn : ℂ) + -2 + 2) = some (kn + -2 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn10 : Interp.complex.toInt? ((kn : ℂ) + -1 + -2) = some (kn + -1 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn11 : Interp.complex.toInt? ((kn : ℂ) + -1 + -1) = some (kn + -1 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn12 : Interp.complex.toInt? ((kn : ℂ) + -1 + 1) = some (kn + -1 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn13 : Interp.complex.toInt? ((kn : ℂ) + -1 + 2) = some (kn + -1 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn20 : Interp.complex.toInt? ((kn : ℂ) + 1 + -2) = some (kn + 1 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn21 : Interp.complex.toInt? ((kn : ℂ) + 1 + -1) = some (kn + 1 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn22 : Interp.complex.toInt? ((kn : ℂ) + 1 + 1) = some (kn + 1 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn23 : Interp.complex.toInt? ((kn : ℂ) + 1 + 2) = some (kn + 1 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn30 : Interp.complex.toInt? ((kn : ℂ) + 2 + -2) = some (kn + 2 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn31 : Interp.complex.toInt? ((kn : ℂ) + 2 + -1) = some (kn + 2 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn32 : Interp.complex.toInt? ((kn : ℂ) + 2 + 1) = some (kn + 2 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn33 : Interp.complex.toInt? ((kn : ℂ) + 2 + 2) = some (kn + 2 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hknp1 : Interp.complex.toInt? (env "n" + 1) = some (kn + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknp2 : Interp.complex.toInt? (env "n" + 2) = some (kn + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm1 : Interp.complex.toInt? (env "n" + -1) = some (kn + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm2 : Interp.complex.toInt? (env "n" + -2) = some (kn + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hbm0gt : 0 < km := by
    have h := hcs (.gt (.var "m") (.int 0)) (by simp [rubi676r17Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, hem, Complex.ext_iff] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi676r17Nondeg, Defined, eval, hem, hen, Interp.toInt?_cast] at h0
  try casesm* _ ∧ _
  have hc2 := hcs (.ne (.var "n") (.int (-1))) (by simp [rubi676r17Nondeg])
  simp [Cond.Holds, Defined, eval] at hc2
  have hc3 := hcs (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.int 0)) (by simp [rubi676r17Nondeg])
  simp [Cond.Holds, Defined, eval] at hc3
  try simp only [hen] at hc2 hc3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc3, hen]
  · simp [eval, Ok, Expr.varList, hm1, hc3, hem, hen, hqn2, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : ¬ kn < -2 := by omega); (try have : ¬ kn + -2 < 0 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : ¬ kn < -1 := by omega); (try have : ¬ kn + -1 < 0 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [Defined, eval, hm1, hc3, hem, hen, hqn2, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : ¬ kn < -2 := by omega); (try have : ¬ kn + -2 < 0 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : ¬ kn < -1 := by omega); (try have : ¬ kn + -1 < 0 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [Calc.complex, rubi676r17Nondeg, eval, Ok, Expr.varList, hem, hqm1, hen, hqn2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : ¬ kn < -2 := by omega); (try have : ¬ kn + -2 < 0 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : ¬ kn < -1 := by omega); (try have : ¬ kn + -1 < 0 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi676r17Nondeg, Defined, eval, hem, hqm1, hen, hqn2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : ¬ kn < -2 := by omega); (try have : ¬ kn + -2 < 0 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : ¬ kn < -1 := by omega); (try have : ¬ kn + -1 < 0 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi676r17Nondeg, eval, d, hm1, hm11, hem, hqm1, hen, hqn2, Interp.toInt?_cast]
    try have hqmp00 : (km : ℂ) ≠ 0 := by exact_mod_cast (show km ≠ 0 by omega)
    try have hqmp10 : (km : ℂ) + 1 ≠ 0 := by exact_mod_cast (show km + 1 ≠ 0 by omega)
    try have hqmp20 : (km : ℂ) + 2 ≠ 0 := by exact_mod_cast (show km + 2 ≠ 0 by omega)
    try have hqmp30 : (km : ℂ) + 3 ≠ 0 := by exact_mod_cast (show km + 3 ≠ 0 by omega)
    have hz1 : (env "e" + (env "f" * t)) ≠ 0 ∨ 0 ≤ km + -1 := by
      exact Or.inr (by omega)
    try rw [show (env "e" + (env "f" * t)) ^ (km) = (env "e" + (env "f" * t)) ^ (km + -1) * (env "e" + (env "f" * t)) ^ 1 from by
      have := zsplit ((env "e" + (env "f" * t))) (km + -1) 1 hz1
      rwa [show km + -1 + ((1 : ℕ) : ℤ) = km by push_cast; ring] at this]
    try generalize (env "e" + (env "f" * t)) ^ (km + -1) = P1
    try casesm* _ ∧ _
    field_simp
    ring1

set_option maxHeartbeats 1000000 in
/-- RUBI rubi676r1Nondeg: explicit term by the symbolic derivative. -/
theorem rubi676r1Nondeg_real : rubi676r1Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi676r1Nondeg.conditions rubi676r1Nondeg.body rubi676r1Nondeg.result rubi676r1Nondeg.integrals
  have hm1 : Interp.real.toInt? (-1 : ℝ) = some (-1) := by simpa using Interp.toInt?_cast Interp.real (-1)
  have hm2 : Interp.real.toInt? (-2 : ℝ) = some (-2) := by simpa using Interp.toInt?_cast Interp.real (-2)
  have h2 : Interp.real.toInt? (2 : ℝ) = some 2 := by simpa using Interp.toInt?_cast Interp.real 2
  have hm11 : Interp.real.toInt? (-1 + -1 : ℝ) = some (-2) := by
    rw [show (-1 + -1 : ℝ) = -2 by norm_num]; exact hm2
  have hn1 : Interp.real.toInt? (1 : ℝ) = some 1 := by simpa using Interp.toInt?_cast Interp.real 1
  have hn3 : Interp.real.toInt? (3 : ℝ) = some 3 := by simpa using Interp.toInt?_cast Interp.real 3
  have hn21 : Interp.real.toInt? (2 + -1 : ℝ) = some 1 := by rw [show (2 + -1 : ℝ) = 1 by norm_num]; exact hn1
  have hn31 : Interp.real.toInt? (3 + -1 : ℝ) = some 2 := by rw [show (3 + -1 : ℝ) = 2 by norm_num]; exact h2
  have hn32 : Interp.real.toInt? (3 + -2 : ℝ) = some 1 := by rw [show (3 + -2 : ℝ) = 1 by norm_num]; exact hn1
  have hn10 : Interp.real.toInt? (1 + -1 : ℝ) = some 0 := by simpa using Interp.toInt?_cast Interp.real 0
  have dln : ∀ z : ℝ, Interp.real.lnDefined z ↔ 0 < z := fun _ => Iff.rfl
  have dtan : ∀ z : ℝ, Interp.real.tanDefined z ↔ Real.cos z ≠ 0 := fun _ => Iff.rfl
  have dasin : ∀ z : ℝ, Interp.real.fnDefined .arcsin z ↔ -1 ≤ z ∧ z ≤ 1 := fun _ => Iff.rfl
  have dacos : ∀ z : ℝ, Interp.real.fnDefined .arccos z ↔ -1 ≤ z ∧ z ≤ 1 := fun _ => Iff.rfl
  refine antiderivRec_open Calc.real _ (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (rubi676r1Nondeg.integrals.head!.2) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "m")) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.real.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi676r1Nondeg, Defined, eval, hkm] at h0
  have hem : env "m" = (km : ℝ) := (Interp.real.toInt?_eq _ _).1 hkm
  have hom1 : Interp.real.toInt? ((-1 : ℝ) + (km : ℝ)) = some (-1 + km) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm1 : Interp.real.toInt? ((km : ℝ) + (-1 : ℝ)) = some (km + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hom2 : Interp.real.toInt? ((1 : ℝ) + (km : ℝ)) = some (1 + km) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm2 : Interp.real.toInt? ((km : ℝ) + (1 : ℝ)) = some (km + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hom3 : Interp.real.toInt? ((-2 : ℝ) + (km : ℝ)) = some (-2 + km) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm3 : Interp.real.toInt? ((km : ℝ) + (-2 : ℝ)) = some (km + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hom4 : Interp.real.toInt? ((2 : ℝ) + (km : ℝ)) = some (2 + km) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm4 : Interp.real.toInt? ((km : ℝ) + (2 : ℝ)) = some (km + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm1 : Interp.real.toInt? ((km : ℝ) - 1) = some (km - 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm2 : Interp.real.toInt? ((km : ℝ) - 2) = some (km - 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm00 : Interp.real.toInt? ((km : ℝ) + -2 + -2) = some (km + -2 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm01 : Interp.real.toInt? ((km : ℝ) + -2 + -1) = some (km + -2 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm02 : Interp.real.toInt? ((km : ℝ) + -2 + 1) = some (km + -2 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm03 : Interp.real.toInt? ((km : ℝ) + -2 + 2) = some (km + -2 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm10 : Interp.real.toInt? ((km : ℝ) + -1 + -2) = some (km + -1 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm11 : Interp.real.toInt? ((km : ℝ) + -1 + -1) = some (km + -1 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm12 : Interp.real.toInt? ((km : ℝ) + -1 + 1) = some (km + -1 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm13 : Interp.real.toInt? ((km : ℝ) + -1 + 2) = some (km + -1 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm20 : Interp.real.toInt? ((km : ℝ) + 1 + -2) = some (km + 1 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm21 : Interp.real.toInt? ((km : ℝ) + 1 + -1) = some (km + 1 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm22 : Interp.real.toInt? ((km : ℝ) + 1 + 1) = some (km + 1 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm23 : Interp.real.toInt? ((km : ℝ) + 1 + 2) = some (km + 1 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm30 : Interp.real.toInt? ((km : ℝ) + 2 + -2) = some (km + 2 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm31 : Interp.real.toInt? ((km : ℝ) + 2 + -1) = some (km + 2 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm32 : Interp.real.toInt? ((km : ℝ) + 2 + 1) = some (km + 2 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm33 : Interp.real.toInt? ((km : ℝ) + 2 + 2) = some (km + 2 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hkmp1 : Interp.real.toInt? (env "m" + 1) = some (km + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmp2 : Interp.real.toInt? (env "m" + 2) = some (km + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm1 : Interp.real.toInt? (env "m" + -1) = some (km + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm2 : Interp.real.toInt? (env "m" + -2) = some (km + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkm]; push_cast; ring)
  rcases hkn : Interp.real.toInt? (env "n") with _ | kn
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi676r1Nondeg, Defined, eval, hkn] at h0
  have hen : env "n" = (kn : ℝ) := (Interp.real.toInt?_eq _ _).1 hkn
  have hon1 : Interp.real.toInt? ((-1 : ℝ) + (kn : ℝ)) = some (-1 + kn) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn1 : Interp.real.toInt? ((kn : ℝ) + (-1 : ℝ)) = some (kn + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hon2 : Interp.real.toInt? ((1 : ℝ) + (kn : ℝ)) = some (1 + kn) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn2 : Interp.real.toInt? ((kn : ℝ) + (1 : ℝ)) = some (kn + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hon3 : Interp.real.toInt? ((-2 : ℝ) + (kn : ℝ)) = some (-2 + kn) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn3 : Interp.real.toInt? ((kn : ℝ) + (-2 : ℝ)) = some (kn + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hon4 : Interp.real.toInt? ((2 : ℝ) + (kn : ℝ)) = some (2 + kn) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn4 : Interp.real.toInt? ((kn : ℝ) + (2 : ℝ)) = some (kn + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn1 : Interp.real.toInt? ((kn : ℝ) - 1) = some (kn - 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn2 : Interp.real.toInt? ((kn : ℝ) - 2) = some (kn - 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn00 : Interp.real.toInt? ((kn : ℝ) + -2 + -2) = some (kn + -2 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn01 : Interp.real.toInt? ((kn : ℝ) + -2 + -1) = some (kn + -2 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn02 : Interp.real.toInt? ((kn : ℝ) + -2 + 1) = some (kn + -2 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn03 : Interp.real.toInt? ((kn : ℝ) + -2 + 2) = some (kn + -2 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn10 : Interp.real.toInt? ((kn : ℝ) + -1 + -2) = some (kn + -1 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn11 : Interp.real.toInt? ((kn : ℝ) + -1 + -1) = some (kn + -1 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn12 : Interp.real.toInt? ((kn : ℝ) + -1 + 1) = some (kn + -1 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn13 : Interp.real.toInt? ((kn : ℝ) + -1 + 2) = some (kn + -1 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn20 : Interp.real.toInt? ((kn : ℝ) + 1 + -2) = some (kn + 1 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn21 : Interp.real.toInt? ((kn : ℝ) + 1 + -1) = some (kn + 1 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn22 : Interp.real.toInt? ((kn : ℝ) + 1 + 1) = some (kn + 1 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn23 : Interp.real.toInt? ((kn : ℝ) + 1 + 2) = some (kn + 1 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn30 : Interp.real.toInt? ((kn : ℝ) + 2 + -2) = some (kn + 2 + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn31 : Interp.real.toInt? ((kn : ℝ) + 2 + -1) = some (kn + 2 + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn32 : Interp.real.toInt? ((kn : ℝ) + 2 + 1) = some (kn + 2 + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn33 : Interp.real.toInt? ((kn : ℝ) + 2 + 2) = some (kn + 2 + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by push_cast; ring)
  have hknp1 : Interp.real.toInt? (env "n" + 1) = some (kn + 1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknp2 : Interp.real.toInt? (env "n" + 2) = some (kn + 2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm1 : Interp.real.toInt? (env "n" + -1) = some (kn + -1) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm2 : Interp.real.toInt? (env "n" + -2) = some (kn + -2) :=
    (Interp.real.toInt?_eq _ _).2 (by rw [(Interp.real.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hbm0gt : 0 < km := by
    have h := hcs (.gt (.var "m") (.int 0)) (by simp [rubi676r1Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hem] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi676r1Nondeg, Defined, eval, hem, hen, Interp.toInt?_cast] at h0
  try casesm* _ ∧ _
  have hc2 := hcs (.ne (.var "n") (.int (-1))) (by simp [rubi676r1Nondeg])
  simp [Cond.Holds, Defined, eval] at hc2
  have hc3 := hcs (.ne (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int 0)) (by simp [rubi676r1Nondeg])
  simp [Cond.Holds, Defined, eval] at hc3
  try simp only [hen] at hc2 hc3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc3, hen]
  · simp [eval, Ok, Expr.varList, hm1, hc3, hem, hen, hqn2, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : ¬ kn < -2 := by omega); (try have : ¬ kn + -2 < 0 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : ¬ kn < -1 := by omega); (try have : ¬ kn + -1 < 0 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [Defined, eval, hm1, hc3, hem, hen, hqn2, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : ¬ kn < -2 := by omega); (try have : ¬ kn + -2 < 0 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : ¬ kn < -1 := by omega); (try have : ¬ kn + -1 < 0 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [Calc.real, rubi676r1Nondeg, eval, Ok, Expr.varList, hem, hqm1, hen, hqn2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : ¬ kn < -2 := by omega); (try have : ¬ kn + -2 < 0 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : ¬ kn < -1 := by omega); (try have : ¬ kn + -1 < 0 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi676r1Nondeg, Defined, eval, hem, hqm1, hen, hqn2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : ¬ kn < -2 := by omega); (try have : ¬ kn + -2 < 0 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : ¬ kn < -1 := by omega); (try have : ¬ kn + -1 < 0 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi676r1Nondeg, eval, d, hm1, hm11, hem, hqm1, hen, hqn2, Interp.toInt?_cast]
    try have hqmp00 : (km : ℝ) ≠ 0 := by exact_mod_cast (show km ≠ 0 by omega)
    try have hqmp10 : (km : ℝ) + 1 ≠ 0 := by exact_mod_cast (show km + 1 ≠ 0 by omega)
    try have hqmp20 : (km : ℝ) + 2 ≠ 0 := by exact_mod_cast (show km + 2 ≠ 0 by omega)
    try have hqmp30 : (km : ℝ) + 3 ≠ 0 := by exact_mod_cast (show km + 3 ≠ 0 by omega)
    have hz1 : (env "c" + (env "d" * t)) ≠ 0 ∨ 0 ≤ km + -1 := by
      exact Or.inr (by omega)
    try rw [show (env "c" + (env "d" * t)) ^ (km) = (env "c" + (env "d" * t)) ^ (km + -1) * (env "c" + (env "d" * t)) ^ 1 from by
      have := zsplit ((env "c" + (env "d" * t))) (km + -1) 1 hz1
      rwa [show km + -1 + ((1 : ℕ) : ℤ) = km by push_cast; ring] at this]
    try generalize (env "c" + (env "d" * t)) ^ (km + -1) = P1
    try casesm* _ ∧ _
    field_simp
    ring1

set_option maxHeartbeats 1000000 in
/-- RUBI rubi676r1Nondeg: explicit term by the symbolic derivative. -/
theorem rubi676r1Nondeg_complex : rubi676r1Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi676r1Nondeg.conditions rubi676r1Nondeg.body rubi676r1Nondeg.result rubi676r1Nondeg.integrals
  have hm1 : Interp.complex.toInt? (-1 : ℂ) = some (-1) := by simpa using Interp.toInt?_cast Interp.complex (-1)
  have hm2 : Interp.complex.toInt? (-2 : ℂ) = some (-2) := by simpa using Interp.toInt?_cast Interp.complex (-2)
  have h2 : Interp.complex.toInt? (2 : ℂ) = some 2 := by simpa using Interp.toInt?_cast Interp.complex 2
  have hm11 : Interp.complex.toInt? (-1 + -1 : ℂ) = some (-2) := by
    rw [show (-1 + -1 : ℂ) = -2 by norm_num]; exact hm2
  have hn1 : Interp.complex.toInt? (1 : ℂ) = some 1 := by simpa using Interp.toInt?_cast Interp.complex 1
  have hn3 : Interp.complex.toInt? (3 : ℂ) = some 3 := by simpa using Interp.toInt?_cast Interp.complex 3
  have hn21 : Interp.complex.toInt? (2 + -1 : ℂ) = some 1 := by rw [show (2 + -1 : ℂ) = 1 by norm_num]; exact hn1
  have hn31 : Interp.complex.toInt? (3 + -1 : ℂ) = some 2 := by rw [show (3 + -1 : ℂ) = 2 by norm_num]; exact h2
  have hn32 : Interp.complex.toInt? (3 + -2 : ℂ) = some 1 := by rw [show (3 + -2 : ℂ) = 1 by norm_num]; exact hn1
  have hn10 : Interp.complex.toInt? (1 + -1 : ℂ) = some 0 := by simpa using Interp.toInt?_cast Interp.complex 0
  have dln : ∀ z : ℂ, Interp.complex.lnDefined z ↔ z ≠ 0 := fun _ => Iff.rfl
  have dtan : ∀ z : ℂ, Interp.complex.tanDefined z ↔ Complex.cos z ≠ 0 := fun _ => Iff.rfl
  refine antiderivRec_open Calc.complex _ (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (rubi676r1Nondeg.integrals.head!.2) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "m")) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.complex.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi676r1Nondeg, Defined, eval, hkm] at h0
  have hem : env "m" = (km : ℂ) := (Interp.complex.toInt?_eq _ _).1 hkm
  have hom1 : Interp.complex.toInt? ((-1 : ℂ) + (km : ℂ)) = some (-1 + km) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm1 : Interp.complex.toInt? ((km : ℂ) + (-1 : ℂ)) = some (km + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hom2 : Interp.complex.toInt? ((1 : ℂ) + (km : ℂ)) = some (1 + km) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm2 : Interp.complex.toInt? ((km : ℂ) + (1 : ℂ)) = some (km + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hom3 : Interp.complex.toInt? ((-2 : ℂ) + (km : ℂ)) = some (-2 + km) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm3 : Interp.complex.toInt? ((km : ℂ) + (-2 : ℂ)) = some (km + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hom4 : Interp.complex.toInt? ((2 : ℂ) + (km : ℂ)) = some (2 + km) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqm4 : Interp.complex.toInt? ((km : ℂ) + (2 : ℂ)) = some (km + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm1 : Interp.complex.toInt? ((km : ℂ) - 1) = some (km - 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsm2 : Interp.complex.toInt? ((km : ℂ) - 2) = some (km - 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm00 : Interp.complex.toInt? ((km : ℂ) + -2 + -2) = some (km + -2 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm01 : Interp.complex.toInt? ((km : ℂ) + -2 + -1) = some (km + -2 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm02 : Interp.complex.toInt? ((km : ℂ) + -2 + 1) = some (km + -2 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm03 : Interp.complex.toInt? ((km : ℂ) + -2 + 2) = some (km + -2 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm10 : Interp.complex.toInt? ((km : ℂ) + -1 + -2) = some (km + -1 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm11 : Interp.complex.toInt? ((km : ℂ) + -1 + -1) = some (km + -1 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm12 : Interp.complex.toInt? ((km : ℂ) + -1 + 1) = some (km + -1 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm13 : Interp.complex.toInt? ((km : ℂ) + -1 + 2) = some (km + -1 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm20 : Interp.complex.toInt? ((km : ℂ) + 1 + -2) = some (km + 1 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm21 : Interp.complex.toInt? ((km : ℂ) + 1 + -1) = some (km + 1 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm22 : Interp.complex.toInt? ((km : ℂ) + 1 + 1) = some (km + 1 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm23 : Interp.complex.toInt? ((km : ℂ) + 1 + 2) = some (km + 1 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm30 : Interp.complex.toInt? ((km : ℂ) + 2 + -2) = some (km + 2 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm31 : Interp.complex.toInt? ((km : ℂ) + 2 + -1) = some (km + 2 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm32 : Interp.complex.toInt? ((km : ℂ) + 2 + 1) = some (km + 2 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwm33 : Interp.complex.toInt? ((km : ℂ) + 2 + 2) = some (km + 2 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hkmp1 : Interp.complex.toInt? (env "m" + 1) = some (km + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmp2 : Interp.complex.toInt? (env "m" + 2) = some (km + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm1 : Interp.complex.toInt? (env "m" + -1) = some (km + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkm]; push_cast; ring)
  have hkmm2 : Interp.complex.toInt? (env "m" + -2) = some (km + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkm]; push_cast; ring)
  rcases hkn : Interp.complex.toInt? (env "n") with _ | kn
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi676r1Nondeg, Defined, eval, hkn] at h0
  have hen : env "n" = (kn : ℂ) := (Interp.complex.toInt?_eq _ _).1 hkn
  have hon1 : Interp.complex.toInt? ((-1 : ℂ) + (kn : ℂ)) = some (-1 + kn) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn1 : Interp.complex.toInt? ((kn : ℂ) + (-1 : ℂ)) = some (kn + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hon2 : Interp.complex.toInt? ((1 : ℂ) + (kn : ℂ)) = some (1 + kn) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn2 : Interp.complex.toInt? ((kn : ℂ) + (1 : ℂ)) = some (kn + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hon3 : Interp.complex.toInt? ((-2 : ℂ) + (kn : ℂ)) = some (-2 + kn) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn3 : Interp.complex.toInt? ((kn : ℂ) + (-2 : ℂ)) = some (kn + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hon4 : Interp.complex.toInt? ((2 : ℂ) + (kn : ℂ)) = some (2 + kn) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hqn4 : Interp.complex.toInt? ((kn : ℂ) + (2 : ℂ)) = some (kn + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn1 : Interp.complex.toInt? ((kn : ℂ) - 1) = some (kn - 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hsn2 : Interp.complex.toInt? ((kn : ℂ) - 2) = some (kn - 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn00 : Interp.complex.toInt? ((kn : ℂ) + -2 + -2) = some (kn + -2 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn01 : Interp.complex.toInt? ((kn : ℂ) + -2 + -1) = some (kn + -2 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn02 : Interp.complex.toInt? ((kn : ℂ) + -2 + 1) = some (kn + -2 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn03 : Interp.complex.toInt? ((kn : ℂ) + -2 + 2) = some (kn + -2 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn10 : Interp.complex.toInt? ((kn : ℂ) + -1 + -2) = some (kn + -1 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn11 : Interp.complex.toInt? ((kn : ℂ) + -1 + -1) = some (kn + -1 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn12 : Interp.complex.toInt? ((kn : ℂ) + -1 + 1) = some (kn + -1 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn13 : Interp.complex.toInt? ((kn : ℂ) + -1 + 2) = some (kn + -1 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn20 : Interp.complex.toInt? ((kn : ℂ) + 1 + -2) = some (kn + 1 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn21 : Interp.complex.toInt? ((kn : ℂ) + 1 + -1) = some (kn + 1 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn22 : Interp.complex.toInt? ((kn : ℂ) + 1 + 1) = some (kn + 1 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn23 : Interp.complex.toInt? ((kn : ℂ) + 1 + 2) = some (kn + 1 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn30 : Interp.complex.toInt? ((kn : ℂ) + 2 + -2) = some (kn + 2 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn31 : Interp.complex.toInt? ((kn : ℂ) + 2 + -1) = some (kn + 2 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn32 : Interp.complex.toInt? ((kn : ℂ) + 2 + 1) = some (kn + 2 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwn33 : Interp.complex.toInt? ((kn : ℂ) + 2 + 2) = some (kn + 2 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hknp1 : Interp.complex.toInt? (env "n" + 1) = some (kn + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknp2 : Interp.complex.toInt? (env "n" + 2) = some (kn + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm1 : Interp.complex.toInt? (env "n" + -1) = some (kn + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hknm2 : Interp.complex.toInt? (env "n" + -2) = some (kn + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkn]; push_cast; ring)
  have hbm0gt : 0 < km := by
    have h := hcs (.gt (.var "m") (.int 0)) (by simp [rubi676r1Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, hem, Complex.ext_iff] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi676r1Nondeg, Defined, eval, hem, hen, Interp.toInt?_cast] at h0
  try casesm* _ ∧ _
  have hc2 := hcs (.ne (.var "n") (.int (-1))) (by simp [rubi676r1Nondeg])
  simp [Cond.Holds, Defined, eval] at hc2
  have hc3 := hcs (.ne (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int 0)) (by simp [rubi676r1Nondeg])
  simp [Cond.Holds, Defined, eval] at hc3
  try simp only [hen] at hc2 hc3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc3, hen]
  · simp [eval, Ok, Expr.varList, hm1, hc3, hem, hen, hqn2, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : ¬ kn < -2 := by omega); (try have : ¬ kn + -2 < 0 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : ¬ kn < -1 := by omega); (try have : ¬ kn + -1 < 0 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [Defined, eval, hm1, hc3, hem, hen, hqn2, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : ¬ kn < -2 := by omega); (try have : ¬ kn + -2 < 0 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : ¬ kn < -1 := by omega); (try have : ¬ kn + -1 < 0 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [Calc.complex, rubi676r1Nondeg, eval, Ok, Expr.varList, hem, hqm1, hen, hqn2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : ¬ kn < -2 := by omega); (try have : ¬ kn + -2 < 0 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : ¬ kn < -1 := by omega); (try have : ¬ kn + -1 < 0 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi676r1Nondeg, Defined, eval, hem, hqm1, hen, hqn2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : ¬ kn < -2 := by omega); (try have : ¬ kn + -2 < 0 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : ¬ kn < -1 := by omega); (try have : ¬ kn + -1 < 0 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi676r1Nondeg, eval, d, hm1, hm11, hem, hqm1, hen, hqn2, Interp.toInt?_cast]
    try have hqmp00 : (km : ℂ) ≠ 0 := by exact_mod_cast (show km ≠ 0 by omega)
    try have hqmp10 : (km : ℂ) + 1 ≠ 0 := by exact_mod_cast (show km + 1 ≠ 0 by omega)
    try have hqmp20 : (km : ℂ) + 2 ≠ 0 := by exact_mod_cast (show km + 2 ≠ 0 by omega)
    try have hqmp30 : (km : ℂ) + 3 ≠ 0 := by exact_mod_cast (show km + 3 ≠ 0 by omega)
    have hz1 : (env "c" + (env "d" * t)) ≠ 0 ∨ 0 ≤ km + -1 := by
      exact Or.inr (by omega)
    try rw [show (env "c" + (env "d" * t)) ^ (km) = (env "c" + (env "d" * t)) ^ (km + -1) * (env "c" + (env "d" * t)) ^ 1 from by
      have := zsplit ((env "c" + (env "d" * t))) (km + -1) 1 hz1
      rwa [show km + -1 + ((1 : ℕ) : ℤ) = km by push_cast; ring] at this]
    try generalize (env "c" + (env "d" * t)) ^ (km + -1) = P1
    try casesm* _ ∧ _
    field_simp
    ring1

end OSR.IntegrationRec305
