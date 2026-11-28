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

namespace OSR.IntegrationRec306
open OSR OSR.Calculus OSR.IntegrationNum1 OSR.SymDeriv Filter Topology

private theorem zsplit {K : Type} [DivisionRing K] (X : K) (j : ℤ) (n : ℕ) (h : X ≠ 0 ∨ 0 ≤ j) :
    X ^ (j + n) = X ^ j * X ^ n := by
  rcases h with h | h
  · rw [zpow_add₀ h, zpow_natCast]
  · lift j to ℕ using h
    rw [show ((j : ℤ) + n) = ((j + n : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
      pow_add]

set_option maxHeartbeats 1000000 in
/-- RUBI rubi676r2Nondeg: explicit term by the symbolic derivative. -/
theorem rubi676r2Nondeg_real : rubi676r2Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi676r2Nondeg.conditions rubi676r2Nondeg.body rubi676r2Nondeg.result rubi676r2Nondeg.integrals
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
  refine antiderivRec_open Calc.real _ (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (rubi676r2Nondeg.integrals.head!.2) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "m")) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.real.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi676r2Nondeg, Defined, eval, hkm] at h0
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
    simp [rubi676r2Nondeg, Defined, eval, hkn] at h0
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
    have h := hcs (.gt (.var "m") (.int 0)) (by simp [rubi676r2Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hem] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi676r2Nondeg, Defined, eval, hem, hen, Interp.toInt?_cast] at h0
  try casesm* _ ∧ _
  have hc2 := hcs (.ne (.var "n") (.int (-1))) (by simp [rubi676r2Nondeg])
  simp [Cond.Holds, Defined, eval] at hc2
  have hc3 := hcs (.ne (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int 0)) (by simp [rubi676r2Nondeg])
  simp [Cond.Holds, Defined, eval] at hc3
  try simp only [hen] at hc2 hc3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc3, hen]
  · simp [eval, Ok, Expr.varList, hm1, hc3, hem, hen, hqn2, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : ¬ kn < -2 := by omega); (try have : ¬ kn + -2 < 0 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : ¬ kn < -1 := by omega); (try have : ¬ kn + -1 < 0 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [Defined, eval, hm1, hc3, hem, hen, hqn2, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : ¬ kn < -2 := by omega); (try have : ¬ kn + -2 < 0 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : ¬ kn < -1 := by omega); (try have : ¬ kn + -1 < 0 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [Calc.real, rubi676r2Nondeg, eval, Ok, Expr.varList, hem, hqm1, hen, hqn2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : ¬ kn < -2 := by omega); (try have : ¬ kn + -2 < 0 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : ¬ kn < -1 := by omega); (try have : ¬ kn + -1 < 0 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi676r2Nondeg, Defined, eval, hem, hqm1, hen, hqn2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : ¬ kn < -2 := by omega); (try have : ¬ kn + -2 < 0 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : ¬ kn < -1 := by omega); (try have : ¬ kn + -1 < 0 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi676r2Nondeg, eval, d, hm1, hm11, hem, hqm1, hen, hqn2, Interp.toInt?_cast]
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
/-- RUBI rubi676r2Nondeg: explicit term by the symbolic derivative. -/
theorem rubi676r2Nondeg_complex : rubi676r2Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi676r2Nondeg.conditions rubi676r2Nondeg.body rubi676r2Nondeg.result rubi676r2Nondeg.integrals
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
  refine antiderivRec_open Calc.complex _ (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (rubi676r2Nondeg.integrals.head!.2) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "m")) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.complex.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi676r2Nondeg, Defined, eval, hkm] at h0
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
    simp [rubi676r2Nondeg, Defined, eval, hkn] at h0
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
    have h := hcs (.gt (.var "m") (.int 0)) (by simp [rubi676r2Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, hem, Complex.ext_iff] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi676r2Nondeg, Defined, eval, hem, hen, Interp.toInt?_cast] at h0
  try casesm* _ ∧ _
  have hc2 := hcs (.ne (.var "n") (.int (-1))) (by simp [rubi676r2Nondeg])
  simp [Cond.Holds, Defined, eval] at hc2
  have hc3 := hcs (.ne (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int 0)) (by simp [rubi676r2Nondeg])
  simp [Cond.Holds, Defined, eval] at hc3
  try simp only [hen] at hc2 hc3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc3, hen]
  · simp [eval, Ok, Expr.varList, hm1, hc3, hem, hen, hqn2, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : ¬ kn < -2 := by omega); (try have : ¬ kn + -2 < 0 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : ¬ kn < -1 := by omega); (try have : ¬ kn + -1 < 0 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [Defined, eval, hm1, hc3, hem, hen, hqn2, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : ¬ kn < -2 := by omega); (try have : ¬ kn + -2 < 0 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : ¬ kn < -1 := by omega); (try have : ¬ kn + -1 < 0 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [Calc.complex, rubi676r2Nondeg, eval, Ok, Expr.varList, hem, hqm1, hen, hqn2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : ¬ kn < -2 := by omega); (try have : ¬ kn + -2 < 0 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : ¬ kn < -1 := by omega); (try have : ¬ kn + -1 < 0 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi676r2Nondeg, Defined, eval, hem, hqm1, hen, hqn2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : 0 ≤ kn + -2 := by omega); (try have : -2 ≤ kn := by omega); (try have : kn < -2 := by omega); (try have : ¬ kn < -2 := by omega); (try have : ¬ kn + -2 < 0 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : kn < -1 := by omega); (try have : ¬ kn < -1 := by omega); (try have : ¬ kn + -1 < 0 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : kn + 2 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : 2 ≤ kn := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi676r2Nondeg, eval, d, hm1, hm11, hem, hqm1, hen, hqn2, Interp.toInt?_cast]
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

set_option maxHeartbeats 1000000 in
/-- RUBI rubi678r49Nondeg: explicit term by the symbolic derivative. -/
theorem rubi678r49Nondeg_real : rubi678r49Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi678r49Nondeg.conditions rubi678r49Nondeg.body rubi678r49Nondeg.result rubi678r49Nondeg.integrals
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
  refine antiderivRec_open Calc.real _ (.app2 .mul (.app1 .cosh (.app2 .mul (.app2 .mul (.var "a") (.pow (.var "x") (.var "n"))) (.app1 .ln (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app2 .mul (.var "a") (.var "n")) (.int (-1)))) (rubi678r49Nondeg.integrals.head!.2) (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.var "n") (.int (-1)))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.real.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [dln, rubi678r49Nondeg, Defined, eval, hkm] at h0
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
    simp [dln, rubi678r49Nondeg, Defined, eval, hkn] at h0
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
  have hzm : (km : ℝ) = (kn : ℝ) - 1 := by
    have h := hcs (.eq (.var "m") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (by simp [rubi678r49Nondeg])
    simp [Cond.Holds, Defined, eval, (Interp.real.toInt?_eq _ _).1 hkm, (Interp.real.toInt?_eq _
        _).1 hkn] at h
    linear_combination h
  have hzim : km = kn - 1 := by exact_mod_cast hzm
  subst hzim
  have h0 := hF.self_of_nhds
  simp [dln, rubi678r49Nondeg, Defined, eval, hem, hen, Interp.toInt?_cast] at h0
  try casesm* _ ∧ _
  have hc0 := hcs (.eq (.var "m") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (by simp [rubi678r49Nondeg])
  simp [Cond.Holds, Defined, eval] at hc0
  have hc1 := hcs (.ne (.app2 .mul (.var "a") (.var "n")) (.int 0)) (by simp [rubi678r49Nondeg])
  simp [Cond.Holds, Defined, eval] at hc1
  try simp only [hem, hen, Int.cast_eq_zero] at hc0 hc1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc1, hen]
  · simp [Calc.real, eval, Ok, Expr.varList, hm1, hc1, hen, Interp.toInt?_cast]
    rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : kn + -2 < 0 := by omega); (try have : -2 ≤ kn := by omega); (try have : ¬ kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : ¬ kn < -1 := by omega); (try have : ¬ kn + -1 < 0 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [dln, Defined, eval, hm1, hc1, hen, Interp.toInt?_cast]
    rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : kn + -2 < 0 := by omega); (try have : -2 ≤ kn := by omega); (try have : ¬ kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : ¬ kn < -1 := by omega); (try have : ¬ kn + -1 < 0 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> tauto
  · simp [Calc.real, rubi678r49Nondeg, eval, Ok, Expr.varList, hc0, hem, hen, hqn1, Interp.toInt?_cast]
    rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : kn + -2 < 0 := by omega); (try have : -2 ≤ kn := by omega); (try have : ¬ kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : ¬ kn < -1 := by omega); (try have : ¬ kn + -1 < 0 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [dln, rubi678r49Nondeg, Defined, eval, hc0, hem, hen, hqn1, Interp.toInt?_cast]
    simp_all
  · simp [rubi678r49Nondeg, eval, d, hm1, hm11, hc0, hem, hen, hqn1, Interp.toInt?_cast]
    try have hqnp00 : (kn : ℝ) ≠ 0 := by exact_mod_cast (show kn ≠ 0 by omega)
    have hz0 : t ≠ 0 ∨ 0 ≤ kn + -1 := by
      rcases lt_or_ge (kn + -1) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show t ^ (kn) = t ^ (kn + -1) * t ^ 1 from by
      have := zsplit (t) (kn + -1) 1 hz0
      rwa [show kn + -1 + ((1 : ℕ) : ℤ) = kn by push_cast; ring] at this]
    try generalize t ^ (kn + -1) = P0
    try casesm* _ ∧ _
    field_simp
    grind

set_option maxHeartbeats 1000000 in
/-- RUBI rubi678r50Nondeg: explicit term by the symbolic derivative. -/
theorem rubi678r50Nondeg_real : rubi678r50Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi678r50Nondeg.conditions rubi678r50Nondeg.body rubi678r50Nondeg.result rubi678r50Nondeg.integrals
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
  refine antiderivRec_open Calc.real _ (.app2 .mul (.app1 .sinh (.app2 .mul (.app2 .mul (.var "a") (.pow (.var "x") (.var "n"))) (.app1 .ln (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app2 .mul (.var "a") (.var "n")) (.int (-1)))) (rubi678r50Nondeg.integrals.head!.2) (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.var "n") (.int (-1)))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.real.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [dln, rubi678r50Nondeg, Defined, eval, hkm] at h0
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
    simp [dln, rubi678r50Nondeg, Defined, eval, hkn] at h0
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
  have hzm : (km : ℝ) = (kn : ℝ) - 1 := by
    have h := hcs (.eq (.var "m") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (by simp [rubi678r50Nondeg])
    simp [Cond.Holds, Defined, eval, (Interp.real.toInt?_eq _ _).1 hkm, (Interp.real.toInt?_eq _
        _).1 hkn] at h
    linear_combination h
  have hzim : km = kn - 1 := by exact_mod_cast hzm
  subst hzim
  have h0 := hF.self_of_nhds
  simp [dln, rubi678r50Nondeg, Defined, eval, hem, hen, Interp.toInt?_cast] at h0
  try casesm* _ ∧ _
  have hc0 := hcs (.eq (.var "m") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (by simp [rubi678r50Nondeg])
  simp [Cond.Holds, Defined, eval] at hc0
  have hc1 := hcs (.ne (.app2 .mul (.var "a") (.var "n")) (.int 0)) (by simp [rubi678r50Nondeg])
  simp [Cond.Holds, Defined, eval] at hc1
  try simp only [hem, hen, Int.cast_eq_zero] at hc0 hc1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc1, hen]
  · simp [Calc.real, eval, Ok, Expr.varList, hm1, hc1, hen, Interp.toInt?_cast]
    rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : kn + -2 < 0 := by omega); (try have : -2 ≤ kn := by omega); (try have : ¬ kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : ¬ kn < -1 := by omega); (try have : ¬ kn + -1 < 0 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [dln, Defined, eval, hm1, hc1, hen, Interp.toInt?_cast]
    rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : kn + -2 < 0 := by omega); (try have : -2 ≤ kn := by omega); (try have : ¬ kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : ¬ kn < -1 := by omega); (try have : ¬ kn + -1 < 0 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> tauto
  · simp [Calc.real, rubi678r50Nondeg, eval, Ok, Expr.varList, hc0, hem, hen, hqn1, Interp.toInt?_cast]
    rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : kn + -2 < 0 := by omega); (try have : -2 ≤ kn := by omega); (try have : ¬ kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : 0 ≤ kn + -1 := by omega); (try have : -1 ≤ kn := by omega); (try have : ¬ kn < -1 := by omega); (try have : ¬ kn + -1 < 0 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : 1 ≤ kn := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [dln, rubi678r50Nondeg, Defined, eval, hc0, hem, hen, hqn1, Interp.toInt?_cast]
    simp_all
  · simp [rubi678r50Nondeg, eval, d, hm1, hm11, hc0, hem, hen, hqn1, Interp.toInt?_cast]
    try have hqnp00 : (kn : ℝ) ≠ 0 := by exact_mod_cast (show kn ≠ 0 by omega)
    have hz0 : t ≠ 0 ∨ 0 ≤ kn + -1 := by
      rcases lt_or_ge (kn + -1) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show t ^ (kn) = t ^ (kn + -1) * t ^ 1 from by
      have := zsplit (t) (kn + -1) 1 hz0
      rwa [show kn + -1 + ((1 : ℕ) : ℤ) = kn by push_cast; ring] at this]
    try generalize t ^ (kn + -1) = P0
    try casesm* _ ∧ _
    field_simp
    grind

set_option maxHeartbeats 1000000 in
/-- RUBI rubi1114r4Nondeg: explicit term by the symbolic derivative. -/
theorem rubi1114r4Nondeg_real : rubi1114r4Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1114r4Nondeg.conditions rubi1114r4Nondeg.body rubi1114r4Nondeg.result rubi1114r4Nondeg.integrals
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
  refine antiderivRec_open Calc.real _ (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 3)) (.var "c")) (.var "e")) (.var "g")) (.app2 .add (.var "m") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "a") (.int 3))) (.var "d")) (.var "f")) (.var "h")) (.app2 .add (.var "n") (.int 2)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "a") (.int 2))) (.var "b")) (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.var "f")) (.var "h")) (.var "m")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.app2 .add (.app2 .mul (.var "f") (.var "g")) (.app2 .mul (.var "e") (.var "h")))) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 3)))))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.var "b") (.int 2))) (.app2 .add (.app2 .mul (.var "c") (.app2 .add (.app2 .mul (.var "f") (.var "g")) (.app2 .mul (.var "e") (.var "h")))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.var "g")) (.app2 .add (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.var "n")) (.int 4)))))) (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.var "d")) (.var "f")) (.var "h")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n")))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "f")) (.var "h")) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.app2 .add (.app2 .mul (.var "f") (.var "g")) (.app2 .mul (.var "e") (.var "h")))) (.app2 .add (.var "n") (.int 1)))))) (.app2 .mul (.pow (.var "b") (.int 2)) (.app2 .add (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.app2 .mul (.var "f") (.var "g")) (.app2 .mul (.var "e") (.var "h")))) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "e")) (.var "g")) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 2))))))) (.var "x"))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 2))) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.var "m") (.int 2))) (.int (-1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "n") (.int 1)))) (rubi1114r4Nondeg.integrals.head!.2) (.app2 .add (.app2 .mul (.app2 .mul (.var "f") (.var "h")) (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 3))) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.var "d")) (.var "f")) (.var "h")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n")))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "f")) (.var "h")) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.app2 .add (.app2 .mul (.var "f") (.var "g")) (.app2 .mul (.var "e") (.var "h")))) (.app2 .add (.var "n") (.int 1)))))) (.app2 .mul (.pow (.var "b") (.int 2)) (.app2 .add (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.app2 .mul (.var "f") (.var "g")) (.app2 .mul (.var "e") (.var "h")))) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "e")) (.var "g")) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 2))))))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 2))) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.var "m") (.int 2))) (.int (-1))))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.real.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1114r4Nondeg, Defined, eval, hkm] at h0
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
    simp [rubi1114r4Nondeg, Defined, eval, hkn] at h0
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
  have h0 := hF.self_of_nhds
  simp [rubi1114r4Nondeg, Defined, eval, hem, hen, Interp.toInt?_cast] at h0
  try casesm* _ ∧ _
  have hc2 := hcs (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 2))) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.var "m") (.int 2))) (.int 0)) (by simp [rubi1114r4Nondeg])
  simp [Cond.Holds, Defined, eval, h2] at hc2
  try simp only [hem] at hc2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, h2, hc2, hem]
  · simp [eval, Ok, Expr.varList, hm1, h2, hc2, hem, hqm2, hen, hqn2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : -2 ≤ km := by omega); (try have : ¬ km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : -1 ≤ km := by omega); (try have : ¬ km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : -2 ≤ kn := by omega); (try have : ¬ kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : -1 ≤ kn := by omega); (try have : ¬ kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [Defined, eval, hm1, h2, hc2, hem, hqm2, hen, hqn2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : -2 ≤ km := by omega); (try have : ¬ km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : -1 ≤ km := by omega); (try have : ¬ km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : -2 ≤ kn := by omega); (try have : ¬ kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : -1 ≤ kn := by omega); (try have : ¬ kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [Calc.real, rubi1114r4Nondeg, eval, Ok, Expr.varList, hem, hqm4, hen, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : -2 ≤ km := by omega); (try have : ¬ km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : -1 ≤ km := by omega); (try have : ¬ km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : -2 ≤ kn := by omega); (try have : ¬ kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : -1 ≤ kn := by omega); (try have : ¬ kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi1114r4Nondeg, Defined, eval, hem, hqm4, hen, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : -2 ≤ km := by omega); (try have : ¬ km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : -1 ≤ km := by omega); (try have : ¬ km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : -2 ≤ kn := by omega); (try have : ¬ kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : -1 ≤ kn := by omega); (try have : ¬ kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi1114r4Nondeg, eval, d, hm1, h2, hm11, hn3, hn21, hn31, hem, hqm2, hqm4, hen, hqn2, Interp.toInt?_cast]
    have hz0 : (env "a" + (env "b" * t)) ≠ 0 ∨ 0 ≤ km := by
      rcases lt_or_ge (km) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show (env "a" + (env "b" * t)) ^ (km + 1) = (env "a" + (env "b" * t)) ^ (km) * (env "a" + (env "b" * t)) ^ 1 from by
      have := zsplit ((env "a" + (env "b" * t))) (km) 1 hz0
      rwa [show km + ((1 : ℕ) : ℤ) = km + 1 by push_cast; ring] at this]
    try rw [show (env "a" + (env "b" * t)) ^ (km + 2) = (env "a" + (env "b" * t)) ^ (km) * (env "a" + (env "b" * t)) ^ 2 from by
      have := zsplit ((env "a" + (env "b" * t))) (km) 2 hz0
      rwa [show km + ((2 : ℕ) : ℤ) = km + 2 by push_cast; ring] at this]
    try generalize (env "a" + (env "b" * t)) ^ (km) = P0
    have hz1 : (env "c" + (env "d" * t)) ≠ 0 ∨ 0 ≤ kn := by
      rcases lt_or_ge (kn) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show (env "c" + (env "d" * t)) ^ (kn + 1) = (env "c" + (env "d" * t)) ^ (kn) * (env "c" + (env "d" * t)) ^ 1 from by
      have := zsplit ((env "c" + (env "d" * t))) (kn) 1 hz1
      rwa [show kn + ((1 : ℕ) : ℤ) = kn + 1 by push_cast; ring] at this]
    try generalize (env "c" + (env "d" * t)) ^ (kn) = P1
    try casesm* _ ∧ _
    field_simp
    ring1

set_option maxHeartbeats 1000000 in
/-- RUBI rubi1114r4Nondeg: explicit term by the symbolic derivative. -/
theorem rubi1114r4Nondeg_complex : rubi1114r4Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1114r4Nondeg.conditions rubi1114r4Nondeg.body rubi1114r4Nondeg.result rubi1114r4Nondeg.integrals
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
  refine antiderivRec_open Calc.complex _ (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 3)) (.var "c")) (.var "e")) (.var "g")) (.app2 .add (.var "m") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "a") (.int 3))) (.var "d")) (.var "f")) (.var "h")) (.app2 .add (.var "n") (.int 2)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "a") (.int 2))) (.var "b")) (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.var "f")) (.var "h")) (.var "m")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.app2 .add (.app2 .mul (.var "f") (.var "g")) (.app2 .mul (.var "e") (.var "h")))) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 3)))))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.var "b") (.int 2))) (.app2 .add (.app2 .mul (.var "c") (.app2 .add (.app2 .mul (.var "f") (.var "g")) (.app2 .mul (.var "e") (.var "h")))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.var "g")) (.app2 .add (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.var "n")) (.int 4)))))) (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.var "d")) (.var "f")) (.var "h")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n")))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "f")) (.var "h")) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.app2 .add (.app2 .mul (.var "f") (.var "g")) (.app2 .mul (.var "e") (.var "h")))) (.app2 .add (.var "n") (.int 1)))))) (.app2 .mul (.pow (.var "b") (.int 2)) (.app2 .add (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.app2 .mul (.var "f") (.var "g")) (.app2 .mul (.var "e") (.var "h")))) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "e")) (.var "g")) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 2))))))) (.var "x"))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 2))) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.var "m") (.int 2))) (.int (-1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "n") (.int 1)))) (rubi1114r4Nondeg.integrals.head!.2) (.app2 .add (.app2 .mul (.app2 .mul (.var "f") (.var "h")) (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 3))) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.var "d")) (.var "f")) (.var "h")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n")))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "f")) (.var "h")) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.app2 .add (.app2 .mul (.var "f") (.var "g")) (.app2 .mul (.var "e") (.var "h")))) (.app2 .add (.var "n") (.int 1)))))) (.app2 .mul (.pow (.var "b") (.int 2)) (.app2 .add (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.app2 .mul (.var "f") (.var "g")) (.app2 .mul (.var "e") (.var "h")))) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "e")) (.var "g")) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 2))))))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 2))) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.var "m") (.int 2))) (.int (-1))))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.complex.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1114r4Nondeg, Defined, eval, hkm] at h0
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
    simp [rubi1114r4Nondeg, Defined, eval, hkn] at h0
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
  have h0 := hF.self_of_nhds
  simp [rubi1114r4Nondeg, Defined, eval, hem, hen, Interp.toInt?_cast] at h0
  try casesm* _ ∧ _
  have hc2 := hcs (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 2))) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.var "m") (.int 2))) (.int 0)) (by simp [rubi1114r4Nondeg])
  simp [Cond.Holds, Defined, eval, h2] at hc2
  try simp only [hem] at hc2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, h2, hc2, hem]
  · simp [eval, Ok, Expr.varList, hm1, h2, hc2, hem, hqm2, hen, hqn2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : -2 ≤ km := by omega); (try have : ¬ km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : -1 ≤ km := by omega); (try have : ¬ km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : -2 ≤ kn := by omega); (try have : ¬ kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : -1 ≤ kn := by omega); (try have : ¬ kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [Defined, eval, hm1, h2, hc2, hem, hqm2, hen, hqn2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : -2 ≤ km := by omega); (try have : ¬ km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : -1 ≤ km := by omega); (try have : ¬ km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : -2 ≤ kn := by omega); (try have : ¬ kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : -1 ≤ kn := by omega); (try have : ¬ kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [Calc.complex, rubi1114r4Nondeg, eval, Ok, Expr.varList, hem, hqm4, hen, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : -2 ≤ km := by omega); (try have : ¬ km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : -1 ≤ km := by omega); (try have : ¬ km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : -2 ≤ kn := by omega); (try have : ¬ kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : -1 ≤ kn := by omega); (try have : ¬ kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi1114r4Nondeg, Defined, eval, hem, hqm4, hen, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kn 0 with hsn | hsn <;> ((try have : km + -2 < 0 := by omega); (try have : -2 ≤ km := by omega); (try have : ¬ km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : -1 ≤ km := by omega); (try have : ¬ km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kn + -2 < 0 := by omega); (try have : -2 ≤ kn := by omega); (try have : ¬ kn < -2 := by omega); (try have : kn + -1 < 0 := by omega); (try have : -1 ≤ kn := by omega); (try have : ¬ kn < -1 := by omega); (try have : kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 0 := by omega); (try have : 0 ≤ kn := by omega); (try have : kn < 0 := by omega); (try have : ¬ kn < 0 := by omega); (try have : ¬ kn + 0 < 0 := by omega); (try have : 0 ≤ kn + 1 := by omega); (try have : kn < 1 := by omega); (try have : ¬ kn + 1 < 0 := by omega); (try have : 0 ≤ kn + 2 := by omega); (try have : kn < 2 := by omega); (try have : ¬ kn + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi1114r4Nondeg, eval, d, hm1, h2, hm11, hn3, hn21, hn31, hem, hqm2, hqm4, hen, hqn2, Interp.toInt?_cast]
    have hz0 : (env "a" + (env "b" * t)) ≠ 0 ∨ 0 ≤ km := by
      rcases lt_or_ge (km) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show (env "a" + (env "b" * t)) ^ (km + 1) = (env "a" + (env "b" * t)) ^ (km) * (env "a" + (env "b" * t)) ^ 1 from by
      have := zsplit ((env "a" + (env "b" * t))) (km) 1 hz0
      rwa [show km + ((1 : ℕ) : ℤ) = km + 1 by push_cast; ring] at this]
    try rw [show (env "a" + (env "b" * t)) ^ (km + 2) = (env "a" + (env "b" * t)) ^ (km) * (env "a" + (env "b" * t)) ^ 2 from by
      have := zsplit ((env "a" + (env "b" * t))) (km) 2 hz0
      rwa [show km + ((2 : ℕ) : ℤ) = km + 2 by push_cast; ring] at this]
    try generalize (env "a" + (env "b" * t)) ^ (km) = P0
    have hz1 : (env "c" + (env "d" * t)) ≠ 0 ∨ 0 ≤ kn := by
      rcases lt_or_ge (kn) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show (env "c" + (env "d" * t)) ^ (kn + 1) = (env "c" + (env "d" * t)) ^ (kn) * (env "c" + (env "d" * t)) ^ 1 from by
      have := zsplit ((env "c" + (env "d" * t))) (kn) 1 hz1
      rwa [show kn + ((1 : ℕ) : ℤ) = kn + 1 by push_cast; ring] at this]
    try generalize (env "c" + (env "d" * t)) ^ (kn) = P1
    try casesm* _ ∧ _
    field_simp
    ring1

set_option maxHeartbeats 1000000 in
/-- RUBI rubi1212r41Nondeg: explicit term by the symbolic derivative. -/
theorem rubi1212r41Nondeg_real : rubi1212r41Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1212r41Nondeg.conditions rubi1212r41Nondeg.body rubi1212r41Nondeg.result rubi1212r41Nondeg.integrals
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
  refine antiderivRec_open Calc.real _ (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.var "c") (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (rubi1212r41Nondeg.integrals.head!.2) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "e") (.int 2))) (.app2 .add (.var "m") (.var "p"))) (.pow (.app2 .mul (.var "c") (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.real.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1212r41Nondeg, Defined, eval, hkm, h2] at h0
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
  rcases hkp : Interp.real.toInt? (env "p") with _ | kp
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1212r41Nondeg, Defined, eval, hkp, h2] at h0
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
  have hbp1gt : kp < -1 := by
    have h := hcs (.gt (.int (-1)) (.var "p")) (by simp [rubi1212r41Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hep] at h
    exact_mod_cast h
  have hbm1gt : 1 < km := by
    have h := hcs (.gt (.var "m") (.int 1)) (by simp [rubi1212r41Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hem] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi1212r41Nondeg, Defined, eval, h2, hem, hep, Interp.toInt?_cast] at h0
  try casesm* _ ∧ _
  have hc0 := hcs (.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)) (by simp [rubi1212r41Nondeg])
  simp [Cond.Holds, Defined, eval, h2] at hc0
  have hc1 := hcs (.eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1212r41Nondeg])
  simp [Cond.Holds, Defined, eval, h2] at hc1
  have hc5 := hcs (.ne (.app2 .mul (.var "c") (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi1212r41Nondeg])
  simp [Cond.Holds, Defined, eval] at hc5
  try simp only [hep] at hc0 hc1 hc5
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, h2, hc5, hep]
  · simp [eval, Ok, Expr.varList, hm1, h2, hc5, hem, hqm1, hep, hqp2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [Defined, eval, hm1, h2, hc5, hem, hqm1, hep, hqp2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [Calc.real, rubi1212r41Nondeg, eval, Ok, Expr.varList, h2, hem, hqm3, hep, hqp2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi1212r41Nondeg, Defined, eval, h2, hem, hqm3, hep, hqp2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi1212r41Nondeg, eval, d, hm1, h2, hm11, hn21, hem, hwm11, hqm1, hqm3, hep, hqp2, Interp.toInt?_cast]
    try have hqmm10 : (km : ℝ) - 1 ≠ 0 := by exact_mod_cast (show km - 1 ≠ 0 by omega)
    try have hqmp00 : (km : ℝ) ≠ 0 := by exact_mod_cast (show km ≠ 0 by omega)
    try have hqmp10 : (km : ℝ) + 1 ≠ 0 := by exact_mod_cast (show km + 1 ≠ 0 by omega)
    try have hqmp20 : (km : ℝ) + 2 ≠ 0 := by exact_mod_cast (show km + 2 ≠ 0 by omega)
    try have hqmp30 : (km : ℝ) + 3 ≠ 0 := by exact_mod_cast (show km + 3 ≠ 0 by omega)
    try have hqpm30 : (kp : ℝ) - 3 ≠ 0 := by exact_mod_cast (show kp - 3 ≠ 0 by omega)
    try have hqpm20 : (kp : ℝ) - 2 ≠ 0 := by exact_mod_cast (show kp - 2 ≠ 0 by omega)
    try have hqpm10 : (kp : ℝ) - 1 ≠ 0 := by exact_mod_cast (show kp - 1 ≠ 0 by omega)
    try have hqpp00 : (kp : ℝ) ≠ 0 := by exact_mod_cast (show kp ≠ 0 by omega)
    try have hqpp10 : (kp : ℝ) + 1 ≠ 0 := by exact_mod_cast (show kp + 1 ≠ 0 by omega)
    try rw [show (km + -1 + -1 : ℤ) = km + -2 by ring]
    have hz0 : ((env "a" + (env "b" * t)) + (env "c" * (t ^ 2))) ≠ 0 ∨ 0 ≤ kp := by
      rcases lt_or_ge (kp) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show ((env "a" + (env "b" * t)) + (env "c" * (t ^ 2))) ^ (kp + 1) = ((env "a" + (env "b" * t)) + (env "c" * (t ^ 2))) ^ (kp) * ((env "a" + (env "b" * t)) + (env "c" * (t ^ 2))) ^ 1 from by
      have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t ^ 2)))) (kp) 1 hz0
      rwa [show kp + ((1 : ℕ) : ℤ) = kp + 1 by push_cast; ring] at this]
    try generalize ((env "a" + (env "b" * t)) + (env "c" * (t ^ 2))) ^ (kp) = P0
    have hz1 : (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ km + -2 := by
      exact Or.inr (by omega)
    try rw [show (env "d" + (env "e" * t)) ^ (km + -1) = (env "d" + (env "e" * t)) ^ (km + -2) * (env "d" + (env "e" * t)) ^ 1 from by
      have := zsplit ((env "d" + (env "e" * t))) (km + -2) 1 hz1
      rwa [show km + -2 + ((1 : ℕ) : ℤ) = km + -1 by push_cast; ring] at this]
    try rw [show (env "d" + (env "e" * t)) ^ (km) = (env "d" + (env "e" * t)) ^ (km + -2) * (env "d" + (env "e" * t)) ^ 2 from by
      have := zsplit ((env "d" + (env "e" * t))) (km + -2) 2 hz1
      rwa [show km + -2 + ((2 : ℕ) : ℤ) = km by push_cast; ring] at this]
    try generalize (env "d" + (env "e" * t)) ^ (km + -2) = P1
    try casesm* _ ∧ _
    linear_combination (norm := skip) ((P0 * P1) / env "c") * hc1; field_simp; ring1

set_option maxHeartbeats 1000000 in
/-- RUBI rubi1212r41Nondeg: explicit term by the symbolic derivative. -/
theorem rubi1212r41Nondeg_complex : rubi1212r41Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1212r41Nondeg.conditions rubi1212r41Nondeg.body rubi1212r41Nondeg.result rubi1212r41Nondeg.integrals
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
  refine antiderivRec_open Calc.complex _ (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.var "c") (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (rubi1212r41Nondeg.integrals.head!.2) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "e") (.int 2))) (.app2 .add (.var "m") (.var "p"))) (.pow (.app2 .mul (.var "c") (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.complex.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1212r41Nondeg, Defined, eval, hkm, h2] at h0
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
  rcases hkp : Interp.complex.toInt? (env "p") with _ | kp
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1212r41Nondeg, Defined, eval, hkp, h2] at h0
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
  have hwp00 : Interp.complex.toInt? ((kp : ℂ) + -2 + -2) = some (kp + -2 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp01 : Interp.complex.toInt? ((kp : ℂ) + -2 + -1) = some (kp + -2 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp02 : Interp.complex.toInt? ((kp : ℂ) + -2 + 1) = some (kp + -2 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp03 : Interp.complex.toInt? ((kp : ℂ) + -2 + 2) = some (kp + -2 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp10 : Interp.complex.toInt? ((kp : ℂ) + -1 + -2) = some (kp + -1 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp11 : Interp.complex.toInt? ((kp : ℂ) + -1 + -1) = some (kp + -1 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp12 : Interp.complex.toInt? ((kp : ℂ) + -1 + 1) = some (kp + -1 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp13 : Interp.complex.toInt? ((kp : ℂ) + -1 + 2) = some (kp + -1 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp20 : Interp.complex.toInt? ((kp : ℂ) + 1 + -2) = some (kp + 1 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp21 : Interp.complex.toInt? ((kp : ℂ) + 1 + -1) = some (kp + 1 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp22 : Interp.complex.toInt? ((kp : ℂ) + 1 + 1) = some (kp + 1 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp23 : Interp.complex.toInt? ((kp : ℂ) + 1 + 2) = some (kp + 1 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp30 : Interp.complex.toInt? ((kp : ℂ) + 2 + -2) = some (kp + 2 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp31 : Interp.complex.toInt? ((kp : ℂ) + 2 + -1) = some (kp + 2 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp32 : Interp.complex.toInt? ((kp : ℂ) + 2 + 1) = some (kp + 2 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp33 : Interp.complex.toInt? ((kp : ℂ) + 2 + 2) = some (kp + 2 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hkpp1 : Interp.complex.toInt? (env "p" + 1) = some (kp + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpp2 : Interp.complex.toInt? (env "p" + 2) = some (kp + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm1 : Interp.complex.toInt? (env "p" + -1) = some (kp + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm2 : Interp.complex.toInt? (env "p" + -2) = some (kp + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hbp1gt : kp < -1 := by
    have h := hcs (.gt (.int (-1)) (.var "p")) (by simp [rubi1212r41Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, hep, Complex.ext_iff] at h
    exact_mod_cast h
  have hbm1gt : 1 < km := by
    have h := hcs (.gt (.var "m") (.int 1)) (by simp [rubi1212r41Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, hem, Complex.ext_iff] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi1212r41Nondeg, Defined, eval, h2, hem, hep, Interp.toInt?_cast] at h0
  try casesm* _ ∧ _
  have hc0 := hcs (.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)) (by simp [rubi1212r41Nondeg])
  simp [Cond.Holds, Defined, eval, h2] at hc0
  have hc1 := hcs (.eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1212r41Nondeg])
  simp [Cond.Holds, Defined, eval, h2] at hc1
  have hc5 := hcs (.ne (.app2 .mul (.var "c") (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi1212r41Nondeg])
  simp [Cond.Holds, Defined, eval] at hc5
  try simp only [hep] at hc0 hc1 hc5
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, h2, hc5, hep]
  · simp [eval, Ok, Expr.varList, hm1, h2, hc5, hem, hqm1, hep, hqp2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [Defined, eval, hm1, h2, hc5, hem, hqm1, hep, hqp2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [Calc.complex, rubi1212r41Nondeg, eval, Ok, Expr.varList, h2, hem, hqm3, hep, hqp2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi1212r41Nondeg, Defined, eval, h2, hem, hqm3, hep, hqp2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi1212r41Nondeg, eval, d, hm1, h2, hm11, hn21, hem, hwm11, hqm1, hqm3, hep, hqp2, Interp.toInt?_cast]
    try have hqmm10 : (km : ℂ) - 1 ≠ 0 := by exact_mod_cast (show km - 1 ≠ 0 by omega)
    try have hqmp00 : (km : ℂ) ≠ 0 := by exact_mod_cast (show km ≠ 0 by omega)
    try have hqmp10 : (km : ℂ) + 1 ≠ 0 := by exact_mod_cast (show km + 1 ≠ 0 by omega)
    try have hqmp20 : (km : ℂ) + 2 ≠ 0 := by exact_mod_cast (show km + 2 ≠ 0 by omega)
    try have hqmp30 : (km : ℂ) + 3 ≠ 0 := by exact_mod_cast (show km + 3 ≠ 0 by omega)
    try have hqpm30 : (kp : ℂ) - 3 ≠ 0 := by exact_mod_cast (show kp - 3 ≠ 0 by omega)
    try have hqpm20 : (kp : ℂ) - 2 ≠ 0 := by exact_mod_cast (show kp - 2 ≠ 0 by omega)
    try have hqpm10 : (kp : ℂ) - 1 ≠ 0 := by exact_mod_cast (show kp - 1 ≠ 0 by omega)
    try have hqpp00 : (kp : ℂ) ≠ 0 := by exact_mod_cast (show kp ≠ 0 by omega)
    try have hqpp10 : (kp : ℂ) + 1 ≠ 0 := by exact_mod_cast (show kp + 1 ≠ 0 by omega)
    try rw [show (km + -1 + -1 : ℤ) = km + -2 by ring]
    have hz0 : ((env "a" + (env "b" * t)) + (env "c" * (t ^ 2))) ≠ 0 ∨ 0 ≤ kp := by
      rcases lt_or_ge (kp) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show ((env "a" + (env "b" * t)) + (env "c" * (t ^ 2))) ^ (kp + 1) = ((env "a" + (env "b" * t)) + (env "c" * (t ^ 2))) ^ (kp) * ((env "a" + (env "b" * t)) + (env "c" * (t ^ 2))) ^ 1 from by
      have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t ^ 2)))) (kp) 1 hz0
      rwa [show kp + ((1 : ℕ) : ℤ) = kp + 1 by push_cast; ring] at this]
    try generalize ((env "a" + (env "b" * t)) + (env "c" * (t ^ 2))) ^ (kp) = P0
    have hz1 : (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ km + -2 := by
      exact Or.inr (by omega)
    try rw [show (env "d" + (env "e" * t)) ^ (km + -1) = (env "d" + (env "e" * t)) ^ (km + -2) * (env "d" + (env "e" * t)) ^ 1 from by
      have := zsplit ((env "d" + (env "e" * t))) (km + -2) 1 hz1
      rwa [show km + -2 + ((1 : ℕ) : ℤ) = km + -1 by push_cast; ring] at this]
    try rw [show (env "d" + (env "e" * t)) ^ (km) = (env "d" + (env "e" * t)) ^ (km + -2) * (env "d" + (env "e" * t)) ^ 2 from by
      have := zsplit ((env "d" + (env "e" * t))) (km + -2) 2 hz1
      rwa [show km + -2 + ((2 : ℕ) : ℤ) = km by push_cast; ring] at this]
    try generalize (env "d" + (env "e" * t)) ^ (km + -2) = P1
    try casesm* _ ∧ _
    linear_combination (norm := skip) ((P0 * P1) / env "c") * hc1; field_simp; ring1

set_option maxHeartbeats 1000000 in
/-- RUBI rubi1212r42Nondeg: explicit term by the symbolic derivative. -/
theorem rubi1212r42Nondeg_real : rubi1212r42Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1212r42Nondeg.conditions rubi1212r42Nondeg.body rubi1212r42Nondeg.result rubi1212r42Nondeg.integrals
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
  refine antiderivRec_open Calc.real _ (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.var "c") (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (rubi1212r42Nondeg.integrals.head!.2) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "e") (.int 2))) (.app2 .add (.var "m") (.var "p"))) (.pow (.app2 .mul (.var "c") (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.real.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1212r42Nondeg, Defined, eval, hkm, h2] at h0
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
  rcases hkp : Interp.real.toInt? (env "p") with _ | kp
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1212r42Nondeg, Defined, eval, hkp, h2] at h0
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
  have hbp1gt : kp < -1 := by
    have h := hcs (.gt (.int (-1)) (.var "p")) (by simp [rubi1212r42Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hep] at h
    exact_mod_cast h
  have hbm1gt : 1 < km := by
    have h := hcs (.gt (.var "m") (.int 1)) (by simp [rubi1212r42Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hem] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi1212r42Nondeg, Defined, eval, h2, hem, hep, Interp.toInt?_cast] at h0
  try casesm* _ ∧ _
  have hc0 := hcs (.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1212r42Nondeg])
  simp [Cond.Holds, Defined, eval, h2] at hc0
  have hc4 := hcs (.ne (.app2 .mul (.var "c") (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi1212r42Nondeg])
  simp [Cond.Holds, Defined, eval] at hc4
  try simp only [hep] at hc0 hc4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, h2, hc4, hep]
  · simp [eval, Ok, Expr.varList, hm1, h2, hc4, hem, hqm1, hep, hqp2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [Defined, eval, hm1, h2, hc4, hem, hqm1, hep, hqp2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [Calc.real, rubi1212r42Nondeg, eval, Ok, Expr.varList, h2, hem, hqm3, hep, hqp2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi1212r42Nondeg, Defined, eval, h2, hem, hqm3, hep, hqp2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi1212r42Nondeg, eval, d, hm1, h2, hm11, hn21, hem, hwm11, hqm1, hqm3, hep, hqp2, Interp.toInt?_cast]
    try have hqmm10 : (km : ℝ) - 1 ≠ 0 := by exact_mod_cast (show km - 1 ≠ 0 by omega)
    try have hqmp00 : (km : ℝ) ≠ 0 := by exact_mod_cast (show km ≠ 0 by omega)
    try have hqmp10 : (km : ℝ) + 1 ≠ 0 := by exact_mod_cast (show km + 1 ≠ 0 by omega)
    try have hqmp20 : (km : ℝ) + 2 ≠ 0 := by exact_mod_cast (show km + 2 ≠ 0 by omega)
    try have hqmp30 : (km : ℝ) + 3 ≠ 0 := by exact_mod_cast (show km + 3 ≠ 0 by omega)
    try have hqpm30 : (kp : ℝ) - 3 ≠ 0 := by exact_mod_cast (show kp - 3 ≠ 0 by omega)
    try have hqpm20 : (kp : ℝ) - 2 ≠ 0 := by exact_mod_cast (show kp - 2 ≠ 0 by omega)
    try have hqpm10 : (kp : ℝ) - 1 ≠ 0 := by exact_mod_cast (show kp - 1 ≠ 0 by omega)
    try have hqpp00 : (kp : ℝ) ≠ 0 := by exact_mod_cast (show kp ≠ 0 by omega)
    try have hqpp10 : (kp : ℝ) + 1 ≠ 0 := by exact_mod_cast (show kp + 1 ≠ 0 by omega)
    try rw [show (km + -1 + -1 : ℤ) = km + -2 by ring]
    have hz0 : (env "a" + (env "c" * (t ^ 2))) ≠ 0 ∨ 0 ≤ kp := by
      rcases lt_or_ge (kp) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show (env "a" + (env "c" * (t ^ 2))) ^ (kp + 1) = (env "a" + (env "c" * (t ^ 2))) ^ (kp) * (env "a" + (env "c" * (t ^ 2))) ^ 1 from by
      have := zsplit ((env "a" + (env "c" * (t ^ 2)))) (kp) 1 hz0
      rwa [show kp + ((1 : ℕ) : ℤ) = kp + 1 by push_cast; ring] at this]
    try generalize (env "a" + (env "c" * (t ^ 2))) ^ (kp) = P0
    have hz1 : (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ km + -2 := by
      exact Or.inr (by omega)
    try rw [show (env "d" + (env "e" * t)) ^ (km + -1) = (env "d" + (env "e" * t)) ^ (km + -2) * (env "d" + (env "e" * t)) ^ 1 from by
      have := zsplit ((env "d" + (env "e" * t))) (km + -2) 1 hz1
      rwa [show km + -2 + ((1 : ℕ) : ℤ) = km + -1 by push_cast; ring] at this]
    try rw [show (env "d" + (env "e" * t)) ^ (km) = (env "d" + (env "e" * t)) ^ (km + -2) * (env "d" + (env "e" * t)) ^ 2 from by
      have := zsplit ((env "d" + (env "e" * t))) (km + -2) 2 hz1
      rwa [show km + -2 + ((2 : ℕ) : ℤ) = km by push_cast; ring] at this]
    try generalize (env "d" + (env "e" * t)) ^ (km + -2) = P1
    try casesm* _ ∧ _
    linear_combination (norm := skip) ((P0 * P1) / env "c") * hc0; field_simp; ring1

set_option maxHeartbeats 1000000 in
/-- RUBI rubi1212r42Nondeg: explicit term by the symbolic derivative. -/
theorem rubi1212r42Nondeg_complex : rubi1212r42Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1212r42Nondeg.conditions rubi1212r42Nondeg.body rubi1212r42Nondeg.result rubi1212r42Nondeg.integrals
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
  refine antiderivRec_open Calc.complex _ (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.var "c") (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (rubi1212r42Nondeg.integrals.head!.2) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "e") (.int 2))) (.app2 .add (.var "m") (.var "p"))) (.pow (.app2 .mul (.var "c") (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.complex.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1212r42Nondeg, Defined, eval, hkm, h2] at h0
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
  rcases hkp : Interp.complex.toInt? (env "p") with _ | kp
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1212r42Nondeg, Defined, eval, hkp, h2] at h0
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
  have hwp00 : Interp.complex.toInt? ((kp : ℂ) + -2 + -2) = some (kp + -2 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp01 : Interp.complex.toInt? ((kp : ℂ) + -2 + -1) = some (kp + -2 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp02 : Interp.complex.toInt? ((kp : ℂ) + -2 + 1) = some (kp + -2 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp03 : Interp.complex.toInt? ((kp : ℂ) + -2 + 2) = some (kp + -2 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp10 : Interp.complex.toInt? ((kp : ℂ) + -1 + -2) = some (kp + -1 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp11 : Interp.complex.toInt? ((kp : ℂ) + -1 + -1) = some (kp + -1 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp12 : Interp.complex.toInt? ((kp : ℂ) + -1 + 1) = some (kp + -1 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp13 : Interp.complex.toInt? ((kp : ℂ) + -1 + 2) = some (kp + -1 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp20 : Interp.complex.toInt? ((kp : ℂ) + 1 + -2) = some (kp + 1 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp21 : Interp.complex.toInt? ((kp : ℂ) + 1 + -1) = some (kp + 1 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp22 : Interp.complex.toInt? ((kp : ℂ) + 1 + 1) = some (kp + 1 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp23 : Interp.complex.toInt? ((kp : ℂ) + 1 + 2) = some (kp + 1 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp30 : Interp.complex.toInt? ((kp : ℂ) + 2 + -2) = some (kp + 2 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp31 : Interp.complex.toInt? ((kp : ℂ) + 2 + -1) = some (kp + 2 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp32 : Interp.complex.toInt? ((kp : ℂ) + 2 + 1) = some (kp + 2 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp33 : Interp.complex.toInt? ((kp : ℂ) + 2 + 2) = some (kp + 2 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hkpp1 : Interp.complex.toInt? (env "p" + 1) = some (kp + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpp2 : Interp.complex.toInt? (env "p" + 2) = some (kp + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm1 : Interp.complex.toInt? (env "p" + -1) = some (kp + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm2 : Interp.complex.toInt? (env "p" + -2) = some (kp + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hbp1gt : kp < -1 := by
    have h := hcs (.gt (.int (-1)) (.var "p")) (by simp [rubi1212r42Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, hep, Complex.ext_iff] at h
    exact_mod_cast h
  have hbm1gt : 1 < km := by
    have h := hcs (.gt (.var "m") (.int 1)) (by simp [rubi1212r42Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, hem, Complex.ext_iff] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi1212r42Nondeg, Defined, eval, h2, hem, hep, Interp.toInt?_cast] at h0
  try casesm* _ ∧ _
  have hc0 := hcs (.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1212r42Nondeg])
  simp [Cond.Holds, Defined, eval, h2] at hc0
  have hc4 := hcs (.ne (.app2 .mul (.var "c") (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi1212r42Nondeg])
  simp [Cond.Holds, Defined, eval] at hc4
  try simp only [hep] at hc0 hc4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, h2, hc4, hep]
  · simp [eval, Ok, Expr.varList, hm1, h2, hc4, hem, hqm1, hep, hqp2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [Defined, eval, hm1, h2, hc4, hem, hqm1, hep, hqp2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [Calc.complex, rubi1212r42Nondeg, eval, Ok, Expr.varList, h2, hem, hqm3, hep, hqp2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi1212r42Nondeg, Defined, eval, h2, hem, hqm3, hep, hqp2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi1212r42Nondeg, eval, d, hm1, h2, hm11, hn21, hem, hwm11, hqm1, hqm3, hep, hqp2, Interp.toInt?_cast]
    try have hqmm10 : (km : ℂ) - 1 ≠ 0 := by exact_mod_cast (show km - 1 ≠ 0 by omega)
    try have hqmp00 : (km : ℂ) ≠ 0 := by exact_mod_cast (show km ≠ 0 by omega)
    try have hqmp10 : (km : ℂ) + 1 ≠ 0 := by exact_mod_cast (show km + 1 ≠ 0 by omega)
    try have hqmp20 : (km : ℂ) + 2 ≠ 0 := by exact_mod_cast (show km + 2 ≠ 0 by omega)
    try have hqmp30 : (km : ℂ) + 3 ≠ 0 := by exact_mod_cast (show km + 3 ≠ 0 by omega)
    try have hqpm30 : (kp : ℂ) - 3 ≠ 0 := by exact_mod_cast (show kp - 3 ≠ 0 by omega)
    try have hqpm20 : (kp : ℂ) - 2 ≠ 0 := by exact_mod_cast (show kp - 2 ≠ 0 by omega)
    try have hqpm10 : (kp : ℂ) - 1 ≠ 0 := by exact_mod_cast (show kp - 1 ≠ 0 by omega)
    try have hqpp00 : (kp : ℂ) ≠ 0 := by exact_mod_cast (show kp ≠ 0 by omega)
    try have hqpp10 : (kp : ℂ) + 1 ≠ 0 := by exact_mod_cast (show kp + 1 ≠ 0 by omega)
    try rw [show (km + -1 + -1 : ℤ) = km + -2 by ring]
    have hz0 : (env "a" + (env "c" * (t ^ 2))) ≠ 0 ∨ 0 ≤ kp := by
      rcases lt_or_ge (kp) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show (env "a" + (env "c" * (t ^ 2))) ^ (kp + 1) = (env "a" + (env "c" * (t ^ 2))) ^ (kp) * (env "a" + (env "c" * (t ^ 2))) ^ 1 from by
      have := zsplit ((env "a" + (env "c" * (t ^ 2)))) (kp) 1 hz0
      rwa [show kp + ((1 : ℕ) : ℤ) = kp + 1 by push_cast; ring] at this]
    try generalize (env "a" + (env "c" * (t ^ 2))) ^ (kp) = P0
    have hz1 : (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ km + -2 := by
      exact Or.inr (by omega)
    try rw [show (env "d" + (env "e" * t)) ^ (km + -1) = (env "d" + (env "e" * t)) ^ (km + -2) * (env "d" + (env "e" * t)) ^ 1 from by
      have := zsplit ((env "d" + (env "e" * t))) (km + -2) 1 hz1
      rwa [show km + -2 + ((1 : ℕ) : ℤ) = km + -1 by push_cast; ring] at this]
    try rw [show (env "d" + (env "e" * t)) ^ (km) = (env "d" + (env "e" * t)) ^ (km + -2) * (env "d" + (env "e" * t)) ^ 2 from by
      have := zsplit ((env "d" + (env "e" * t))) (km + -2) 2 hz1
      rwa [show km + -2 + ((2 : ℕ) : ℤ) = km by push_cast; ring] at this]
    try generalize (env "d" + (env "e" * t)) ^ (km + -2) = P1
    try casesm* _ ∧ _
    linear_combination (norm := skip) ((P0 * P1) / env "c") * hc0; field_simp; ring1

set_option maxHeartbeats 1000000 in
/-- RUBI rubi1212r59Nondeg: explicit term by the symbolic derivative. -/
theorem rubi1212r59Nondeg_real : rubi1212r59Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1212r59Nondeg.conditions rubi1212r59Nondeg.body rubi1212r59Nondeg.result rubi1212r59Nondeg.integrals
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
  refine antiderivRec_open Calc.real _ (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (rubi1212r59Nondeg.integrals.head!.2) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "e")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.real.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1212r59Nondeg, Defined, eval, hkm, h2] at h0
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
  rcases hkp : Interp.real.toInt? (env "p") with _ | kp
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1212r59Nondeg, Defined, eval, hkp, h2] at h0
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
  have hbp1gt : kp < -1 := by
    have h := hcs (.gt (.int (-1)) (.var "p")) (by simp [rubi1212r59Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hep] at h
    exact_mod_cast h
  have hbm1gt : 1 < km := by
    have h := hcs (.gt (.var "m") (.int 1)) (by simp [rubi1212r59Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hem] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi1212r59Nondeg, Defined, eval, h2, hem, hep, Interp.toInt?_cast] at h0
  try casesm* _ ∧ _
  have hc0 := hcs (.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)) (by simp [rubi1212r59Nondeg])
  simp [Cond.Holds, Defined, eval, h2] at hc0
  have hc1 := hcs (.eq (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0)) (by simp [rubi1212r59Nondeg])
  simp [Cond.Holds, Defined, eval] at hc1
  have hc2 := hcs (.ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3)) (.int 0)) (by simp [rubi1212r59Nondeg])
  simp [Cond.Holds, Defined, eval] at hc2
  have hc6 := hcs (.ne (.app2 .mul (.var "b") (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi1212r59Nondeg])
  simp [Cond.Holds, Defined, eval] at hc6
  try simp only [hem, hep] at hc0 hc1 hc2 hc6
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc6, hep]
  · simp [eval, Ok, Expr.varList, hm1, h2, hc6, hem, hqm1, hep, hqp2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [Defined, eval, hm1, h2, hc6, hem, hqm1, hep, hqp2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [Calc.real, rubi1212r59Nondeg, eval, Ok, Expr.varList, h2, hem, hqm3, hep, hqp2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi1212r59Nondeg, Defined, eval, h2, hem, hqm3, hep, hqp2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi1212r59Nondeg, eval, d, hm1, h2, hm11, hn21, hem, hwm11, hqm1, hqm3, hep, hqp2, Interp.toInt?_cast]
    try have hqmm10 : (km : ℝ) - 1 ≠ 0 := by exact_mod_cast (show km - 1 ≠ 0 by omega)
    try have hqmp00 : (km : ℝ) ≠ 0 := by exact_mod_cast (show km ≠ 0 by omega)
    try have hqmp10 : (km : ℝ) + 1 ≠ 0 := by exact_mod_cast (show km + 1 ≠ 0 by omega)
    try have hqmp20 : (km : ℝ) + 2 ≠ 0 := by exact_mod_cast (show km + 2 ≠ 0 by omega)
    try have hqmp30 : (km : ℝ) + 3 ≠ 0 := by exact_mod_cast (show km + 3 ≠ 0 by omega)
    try have hqpm30 : (kp : ℝ) - 3 ≠ 0 := by exact_mod_cast (show kp - 3 ≠ 0 by omega)
    try have hqpm20 : (kp : ℝ) - 2 ≠ 0 := by exact_mod_cast (show kp - 2 ≠ 0 by omega)
    try have hqpm10 : (kp : ℝ) - 1 ≠ 0 := by exact_mod_cast (show kp - 1 ≠ 0 by omega)
    try have hqpp00 : (kp : ℝ) ≠ 0 := by exact_mod_cast (show kp ≠ 0 by omega)
    try have hqpp10 : (kp : ℝ) + 1 ≠ 0 := by exact_mod_cast (show kp + 1 ≠ 0 by omega)
    try rw [show (km + -1 + -1 : ℤ) = km + -2 by ring]
    have hz0 : ((env "a" + (env "b" * t)) + (env "c" * (t ^ 2))) ≠ 0 ∨ 0 ≤ kp := by
      rcases lt_or_ge (kp) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show ((env "a" + (env "b" * t)) + (env "c" * (t ^ 2))) ^ (kp + 1) = ((env "a" + (env "b" * t)) + (env "c" * (t ^ 2))) ^ (kp) * ((env "a" + (env "b" * t)) + (env "c" * (t ^ 2))) ^ 1 from by
      have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t ^ 2)))) (kp) 1 hz0
      rwa [show kp + ((1 : ℕ) : ℤ) = kp + 1 by push_cast; ring] at this]
    try generalize ((env "a" + (env "b" * t)) + (env "c" * (t ^ 2))) ^ (kp) = P0
    have hz1 : (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ km + -2 := by
      exact Or.inr (by omega)
    try rw [show (env "d" + (env "e" * t)) ^ (km + -1) = (env "d" + (env "e" * t)) ^ (km + -2) * (env "d" + (env "e" * t)) ^ 1 from by
      have := zsplit ((env "d" + (env "e" * t))) (km + -2) 1 hz1
      rwa [show km + -2 + ((1 : ℕ) : ℤ) = km + -1 by push_cast; ring] at this]
    try rw [show (env "d" + (env "e" * t)) ^ (km) = (env "d" + (env "e" * t)) ^ (km + -2) * (env "d" + (env "e" * t)) ^ 2 from by
      have := zsplit ((env "d" + (env "e" * t))) (km + -2) 2 hz1
      rwa [show km + -2 + ((2 : ℕ) : ℤ) = km by push_cast; ring] at this]
    try generalize (env "d" + (env "e" * t)) ^ (km + -2) = P1
    try casesm* _ ∧ _
    linear_combination (norm := skip) ((((-1) * env "d" * t * P0 * P1) + ((-1) * env "e" * P0 * P1 * (t ^ 2))) / env "b") * hc1; field_simp; ring1

set_option maxHeartbeats 1000000 in
/-- RUBI rubi1212r59Nondeg: explicit term by the symbolic derivative. -/
theorem rubi1212r59Nondeg_complex : rubi1212r59Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1212r59Nondeg.conditions rubi1212r59Nondeg.body rubi1212r59Nondeg.result rubi1212r59Nondeg.integrals
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
  refine antiderivRec_open Calc.complex _ (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (rubi1212r59Nondeg.integrals.head!.2) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "e")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.complex.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1212r59Nondeg, Defined, eval, hkm, h2] at h0
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
  rcases hkp : Interp.complex.toInt? (env "p") with _ | kp
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1212r59Nondeg, Defined, eval, hkp, h2] at h0
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
  have hwp00 : Interp.complex.toInt? ((kp : ℂ) + -2 + -2) = some (kp + -2 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp01 : Interp.complex.toInt? ((kp : ℂ) + -2 + -1) = some (kp + -2 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp02 : Interp.complex.toInt? ((kp : ℂ) + -2 + 1) = some (kp + -2 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp03 : Interp.complex.toInt? ((kp : ℂ) + -2 + 2) = some (kp + -2 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp10 : Interp.complex.toInt? ((kp : ℂ) + -1 + -2) = some (kp + -1 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp11 : Interp.complex.toInt? ((kp : ℂ) + -1 + -1) = some (kp + -1 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp12 : Interp.complex.toInt? ((kp : ℂ) + -1 + 1) = some (kp + -1 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp13 : Interp.complex.toInt? ((kp : ℂ) + -1 + 2) = some (kp + -1 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp20 : Interp.complex.toInt? ((kp : ℂ) + 1 + -2) = some (kp + 1 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp21 : Interp.complex.toInt? ((kp : ℂ) + 1 + -1) = some (kp + 1 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp22 : Interp.complex.toInt? ((kp : ℂ) + 1 + 1) = some (kp + 1 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp23 : Interp.complex.toInt? ((kp : ℂ) + 1 + 2) = some (kp + 1 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp30 : Interp.complex.toInt? ((kp : ℂ) + 2 + -2) = some (kp + 2 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp31 : Interp.complex.toInt? ((kp : ℂ) + 2 + -1) = some (kp + 2 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp32 : Interp.complex.toInt? ((kp : ℂ) + 2 + 1) = some (kp + 2 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp33 : Interp.complex.toInt? ((kp : ℂ) + 2 + 2) = some (kp + 2 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hkpp1 : Interp.complex.toInt? (env "p" + 1) = some (kp + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpp2 : Interp.complex.toInt? (env "p" + 2) = some (kp + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm1 : Interp.complex.toInt? (env "p" + -1) = some (kp + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm2 : Interp.complex.toInt? (env "p" + -2) = some (kp + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hbp1gt : kp < -1 := by
    have h := hcs (.gt (.int (-1)) (.var "p")) (by simp [rubi1212r59Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, hep, Complex.ext_iff] at h
    exact_mod_cast h
  have hbm1gt : 1 < km := by
    have h := hcs (.gt (.var "m") (.int 1)) (by simp [rubi1212r59Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, hem, Complex.ext_iff] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi1212r59Nondeg, Defined, eval, h2, hem, hep, Interp.toInt?_cast] at h0
  try casesm* _ ∧ _
  have hc0 := hcs (.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)) (by simp [rubi1212r59Nondeg])
  simp [Cond.Holds, Defined, eval, h2] at hc0
  have hc1 := hcs (.eq (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0)) (by simp [rubi1212r59Nondeg])
  simp [Cond.Holds, Defined, eval] at hc1
  have hc2 := hcs (.ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3)) (.int 0)) (by simp [rubi1212r59Nondeg])
  simp [Cond.Holds, Defined, eval] at hc2
  have hc6 := hcs (.ne (.app2 .mul (.var "b") (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi1212r59Nondeg])
  simp [Cond.Holds, Defined, eval] at hc6
  try simp only [hem, hep] at hc0 hc1 hc2 hc6
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc6, hep]
  · simp [eval, Ok, Expr.varList, hm1, h2, hc6, hem, hqm1, hep, hqp2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [Defined, eval, hm1, h2, hc6, hem, hqm1, hep, hqp2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [Calc.complex, rubi1212r59Nondeg, eval, Ok, Expr.varList, h2, hem, hqm3, hep, hqp2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi1212r59Nondeg, Defined, eval, h2, hem, hqm3, hep, hqp2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi1212r59Nondeg, eval, d, hm1, h2, hm11, hn21, hem, hwm11, hqm1, hqm3, hep, hqp2, Interp.toInt?_cast]
    try have hqmm10 : (km : ℂ) - 1 ≠ 0 := by exact_mod_cast (show km - 1 ≠ 0 by omega)
    try have hqmp00 : (km : ℂ) ≠ 0 := by exact_mod_cast (show km ≠ 0 by omega)
    try have hqmp10 : (km : ℂ) + 1 ≠ 0 := by exact_mod_cast (show km + 1 ≠ 0 by omega)
    try have hqmp20 : (km : ℂ) + 2 ≠ 0 := by exact_mod_cast (show km + 2 ≠ 0 by omega)
    try have hqmp30 : (km : ℂ) + 3 ≠ 0 := by exact_mod_cast (show km + 3 ≠ 0 by omega)
    try have hqpm30 : (kp : ℂ) - 3 ≠ 0 := by exact_mod_cast (show kp - 3 ≠ 0 by omega)
    try have hqpm20 : (kp : ℂ) - 2 ≠ 0 := by exact_mod_cast (show kp - 2 ≠ 0 by omega)
    try have hqpm10 : (kp : ℂ) - 1 ≠ 0 := by exact_mod_cast (show kp - 1 ≠ 0 by omega)
    try have hqpp00 : (kp : ℂ) ≠ 0 := by exact_mod_cast (show kp ≠ 0 by omega)
    try have hqpp10 : (kp : ℂ) + 1 ≠ 0 := by exact_mod_cast (show kp + 1 ≠ 0 by omega)
    try rw [show (km + -1 + -1 : ℤ) = km + -2 by ring]
    have hz0 : ((env "a" + (env "b" * t)) + (env "c" * (t ^ 2))) ≠ 0 ∨ 0 ≤ kp := by
      rcases lt_or_ge (kp) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show ((env "a" + (env "b" * t)) + (env "c" * (t ^ 2))) ^ (kp + 1) = ((env "a" + (env "b" * t)) + (env "c" * (t ^ 2))) ^ (kp) * ((env "a" + (env "b" * t)) + (env "c" * (t ^ 2))) ^ 1 from by
      have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t ^ 2)))) (kp) 1 hz0
      rwa [show kp + ((1 : ℕ) : ℤ) = kp + 1 by push_cast; ring] at this]
    try generalize ((env "a" + (env "b" * t)) + (env "c" * (t ^ 2))) ^ (kp) = P0
    have hz1 : (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ km + -2 := by
      exact Or.inr (by omega)
    try rw [show (env "d" + (env "e" * t)) ^ (km + -1) = (env "d" + (env "e" * t)) ^ (km + -2) * (env "d" + (env "e" * t)) ^ 1 from by
      have := zsplit ((env "d" + (env "e" * t))) (km + -2) 1 hz1
      rwa [show km + -2 + ((1 : ℕ) : ℤ) = km + -1 by push_cast; ring] at this]
    try rw [show (env "d" + (env "e" * t)) ^ (km) = (env "d" + (env "e" * t)) ^ (km + -2) * (env "d" + (env "e" * t)) ^ 2 from by
      have := zsplit ((env "d" + (env "e" * t))) (km + -2) 2 hz1
      rwa [show km + -2 + ((2 : ℕ) : ℤ) = km by push_cast; ring] at this]
    try generalize (env "d" + (env "e" * t)) ^ (km + -2) = P1
    try casesm* _ ∧ _
    linear_combination (norm := skip) ((((-1) * env "d" * t * P0 * P1) + ((-1) * env "e" * P0 * P1 * (t ^ 2))) / env "b") * hc1; field_simp; ring1

set_option maxHeartbeats 1000000 in
/-- RUBI rubi1212r69Nondeg: explicit term by the symbolic derivative. -/
theorem rubi1212r69Nondeg_real : rubi1212r69Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1212r69Nondeg.conditions rubi1212r69Nondeg.body rubi1212r69Nondeg.result rubi1212r69Nondeg.integrals
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
  refine antiderivRec_open1 Calc.real _ (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.var "m")) (.pow (.var "d") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (rubi1212r69Nondeg.integrals.head!.2) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.real.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1212r69Nondeg, Defined, eval, hkm, h2] at h0
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
  rcases hkp : Interp.real.toInt? (env "p") with _ | kp
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1212r69Nondeg, Defined, eval, hkp, h2] at h0
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
  have hbp1gt : 1 < kp := by
    have h := hcs (.gt (.var "p") (.int 1)) (by simp [rubi1212r69Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hep] at h
    exact_mod_cast h
  have hbm0gt : 0 < km := by
    have h := hcs (.gt (.var "m") (.int 0)) (by simp [rubi1212r69Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hem] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi1212r69Nondeg, Defined, eval, h2, hem, hep, Interp.toInt?_cast] at h0
  try casesm* _ ∧ _
  have hc0 := hcs (.ne (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1212r69Nondeg])
  simp [Cond.Holds, Defined, eval, h2] at hc0
  have hc6 := hcs (.ne (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi1212r69Nondeg])
  simp [Cond.Holds, Defined, eval] at hc6
  try simp only [hep] at hc0 hc6
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [eval, Ok, Expr.varList, hm1, h2, hc6, hem, hqm1, hep, hqp2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [Defined, eval, hm1, h2, hc6, hem, hqm1, hep, hqp2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [Calc.real, rubi1212r69Nondeg, eval, Ok, Expr.varList, h2, hem, hqm1, hep, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi1212r69Nondeg, Defined, eval, h2, hem, hqm1, hep, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi1212r69Nondeg, eval, d, hm1, h2, hm11, hn21, hem, hwm11, hqm1, hep, hqp2, Interp.toInt?_cast]
    try have hqmp00 : (km : ℝ) ≠ 0 := by exact_mod_cast (show km ≠ 0 by omega)
    try have hqmp10 : (km : ℝ) + 1 ≠ 0 := by exact_mod_cast (show km + 1 ≠ 0 by omega)
    try have hqmp20 : (km : ℝ) + 2 ≠ 0 := by exact_mod_cast (show km + 2 ≠ 0 by omega)
    try have hqmp30 : (km : ℝ) + 3 ≠ 0 := by exact_mod_cast (show km + 3 ≠ 0 by omega)
    try have hqpm10 : (kp : ℝ) - 1 ≠ 0 := by exact_mod_cast (show kp - 1 ≠ 0 by omega)
    try have hqpp00 : (kp : ℝ) ≠ 0 := by exact_mod_cast (show kp ≠ 0 by omega)
    try have hqpp10 : (kp : ℝ) + 1 ≠ 0 := by exact_mod_cast (show kp + 1 ≠ 0 by omega)
    try have hqpp20 : (kp : ℝ) + 2 ≠ 0 := by exact_mod_cast (show kp + 2 ≠ 0 by omega)
    try have hqpp30 : (kp : ℝ) + 3 ≠ 0 := by exact_mod_cast (show kp + 3 ≠ 0 by omega)
    have hz0 : (env "a" + (env "c" * (t ^ 2))) ≠ 0 ∨ 0 ≤ kp := by
      exact Or.inr (by omega)
    try generalize (env "a" + (env "c" * (t ^ 2))) ^ (kp) = P0
    try casesm* _ ∧ _
    field_simp
    ring1

set_option maxHeartbeats 1000000 in
/-- RUBI rubi1212r69Nondeg: explicit term by the symbolic derivative. -/
theorem rubi1212r69Nondeg_complex : rubi1212r69Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1212r69Nondeg.conditions rubi1212r69Nondeg.body rubi1212r69Nondeg.result rubi1212r69Nondeg.integrals
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
  refine antiderivRec_open1 Calc.complex _ (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.var "m")) (.pow (.var "d") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (rubi1212r69Nondeg.integrals.head!.2) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.complex.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1212r69Nondeg, Defined, eval, hkm, h2] at h0
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
  rcases hkp : Interp.complex.toInt? (env "p") with _ | kp
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1212r69Nondeg, Defined, eval, hkp, h2] at h0
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
  have hwp00 : Interp.complex.toInt? ((kp : ℂ) + -2 + -2) = some (kp + -2 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp01 : Interp.complex.toInt? ((kp : ℂ) + -2 + -1) = some (kp + -2 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp02 : Interp.complex.toInt? ((kp : ℂ) + -2 + 1) = some (kp + -2 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp03 : Interp.complex.toInt? ((kp : ℂ) + -2 + 2) = some (kp + -2 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp10 : Interp.complex.toInt? ((kp : ℂ) + -1 + -2) = some (kp + -1 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp11 : Interp.complex.toInt? ((kp : ℂ) + -1 + -1) = some (kp + -1 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp12 : Interp.complex.toInt? ((kp : ℂ) + -1 + 1) = some (kp + -1 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp13 : Interp.complex.toInt? ((kp : ℂ) + -1 + 2) = some (kp + -1 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp20 : Interp.complex.toInt? ((kp : ℂ) + 1 + -2) = some (kp + 1 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp21 : Interp.complex.toInt? ((kp : ℂ) + 1 + -1) = some (kp + 1 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp22 : Interp.complex.toInt? ((kp : ℂ) + 1 + 1) = some (kp + 1 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp23 : Interp.complex.toInt? ((kp : ℂ) + 1 + 2) = some (kp + 1 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp30 : Interp.complex.toInt? ((kp : ℂ) + 2 + -2) = some (kp + 2 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp31 : Interp.complex.toInt? ((kp : ℂ) + 2 + -1) = some (kp + 2 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp32 : Interp.complex.toInt? ((kp : ℂ) + 2 + 1) = some (kp + 2 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp33 : Interp.complex.toInt? ((kp : ℂ) + 2 + 2) = some (kp + 2 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hkpp1 : Interp.complex.toInt? (env "p" + 1) = some (kp + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpp2 : Interp.complex.toInt? (env "p" + 2) = some (kp + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm1 : Interp.complex.toInt? (env "p" + -1) = some (kp + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm2 : Interp.complex.toInt? (env "p" + -2) = some (kp + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hbp1gt : 1 < kp := by
    have h := hcs (.gt (.var "p") (.int 1)) (by simp [rubi1212r69Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, hep, Complex.ext_iff] at h
    exact_mod_cast h
  have hbm0gt : 0 < km := by
    have h := hcs (.gt (.var "m") (.int 0)) (by simp [rubi1212r69Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, hem, Complex.ext_iff] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi1212r69Nondeg, Defined, eval, h2, hem, hep, Interp.toInt?_cast] at h0
  try casesm* _ ∧ _
  have hc0 := hcs (.ne (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1212r69Nondeg])
  simp [Cond.Holds, Defined, eval, h2] at hc0
  have hc6 := hcs (.ne (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi1212r69Nondeg])
  simp [Cond.Holds, Defined, eval] at hc6
  try simp only [hep] at hc0 hc6
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [eval, Ok, Expr.varList, hm1, h2, hc6, hem, hqm1, hep, hqp2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [Defined, eval, hm1, h2, hc6, hem, hqm1, hep, hqp2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [Calc.complex, rubi1212r69Nondeg, eval, Ok, Expr.varList, h2, hem, hqm1, hep, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi1212r69Nondeg, Defined, eval, h2, hem, hqm1, hep, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi1212r69Nondeg, eval, d, hm1, h2, hm11, hn21, hem, hwm11, hqm1, hep, hqp2, Interp.toInt?_cast]
    try have hqmp00 : (km : ℂ) ≠ 0 := by exact_mod_cast (show km ≠ 0 by omega)
    try have hqmp10 : (km : ℂ) + 1 ≠ 0 := by exact_mod_cast (show km + 1 ≠ 0 by omega)
    try have hqmp20 : (km : ℂ) + 2 ≠ 0 := by exact_mod_cast (show km + 2 ≠ 0 by omega)
    try have hqmp30 : (km : ℂ) + 3 ≠ 0 := by exact_mod_cast (show km + 3 ≠ 0 by omega)
    try have hqpm10 : (kp : ℂ) - 1 ≠ 0 := by exact_mod_cast (show kp - 1 ≠ 0 by omega)
    try have hqpp00 : (kp : ℂ) ≠ 0 := by exact_mod_cast (show kp ≠ 0 by omega)
    try have hqpp10 : (kp : ℂ) + 1 ≠ 0 := by exact_mod_cast (show kp + 1 ≠ 0 by omega)
    try have hqpp20 : (kp : ℂ) + 2 ≠ 0 := by exact_mod_cast (show kp + 2 ≠ 0 by omega)
    try have hqpp30 : (kp : ℂ) + 3 ≠ 0 := by exact_mod_cast (show kp + 3 ≠ 0 by omega)
    have hz0 : (env "a" + (env "c" * (t ^ 2))) ≠ 0 ∨ 0 ≤ kp := by
      exact Or.inr (by omega)
    try generalize (env "a" + (env "c" * (t ^ 2))) ^ (kp) = P0
    try casesm* _ ∧ _
    field_simp
    ring1

set_option maxHeartbeats 1000000 in
/-- RUBI rubi1212r76Nondeg: explicit term by the symbolic derivative. -/
theorem rubi1212r76Nondeg_real : rubi1212r76Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1212r76Nondeg.conditions rubi1212r76Nondeg.body rubi1212r76Nondeg.result rubi1212r76Nondeg.integrals
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
  refine antiderivRec_open Calc.real _ (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.var "c") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.int (-1)))) (rubi1212r76Nondeg.integrals.head!.2) (.app2 .mul (.int 1) (.pow (.var "c") (.int (-1)))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.real.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1212r76Nondeg, Defined, eval, hkm, hm1, h2] at h0
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
  have hbm1gt : 1 < km := by
    have h := hcs (.gt (.var "m") (.int 1)) (by simp [rubi1212r76Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hem] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi1212r76Nondeg, Defined, eval, hm1, h2, hem, Interp.toInt?_cast] at h0
  try casesm* _ ∧ _
  have hc0 := hcs (.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)) (by simp [rubi1212r76Nondeg])
  simp [Cond.Holds, Defined, eval, h2] at hc0
  have hc1 := hcs (.ne (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1212r76Nondeg])
  simp [Cond.Holds, Defined, eval, h2] at hc1
  have hc2 := hcs (.ne (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0)) (by simp [rubi1212r76Nondeg])
  simp [Cond.Holds, Defined, eval] at hc2
  have hc4 := hcs (.ne (.app2 .mul (.var "c") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.int 0)) (by simp [rubi1212r76Nondeg])
  simp [Cond.Holds, Defined, eval] at hc4
  try simp only [hem] at hc0 hc1 hc2 hc4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc4]
  · simp [eval, Ok, Expr.varList, hm1, hc4, hem, hqm1]
    rcases lt_or_ge km 0 with hsm | hsm <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega)) <;> simp_all
  · simp [Defined, eval, hm1, hc4, hem, hqm1]
    rcases lt_or_ge km 0 with hsm | hsm <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega)) <;> simp_all
  · simp [Calc.real, rubi1212r76Nondeg, eval, Ok, Expr.varList, hm1, h2, hem, hqm3]
    rcases lt_or_ge km 0 with hsm | hsm <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi1212r76Nondeg, Defined, eval, hm1, h2, hem, hqm3]
    simp_all
  · simp [rubi1212r76Nondeg, eval, d, hm1, h2, hm11, hem, hwm11, hqm1, hqm3, Interp.toInt?_cast]
    try have hqmm10 : (km : ℝ) - 1 ≠ 0 := by exact_mod_cast (show km - 1 ≠ 0 by omega)
    try have hqmp00 : (km : ℝ) ≠ 0 := by exact_mod_cast (show km ≠ 0 by omega)
    try have hqmp10 : (km : ℝ) + 1 ≠ 0 := by exact_mod_cast (show km + 1 ≠ 0 by omega)
    try have hqmp20 : (km : ℝ) + 2 ≠ 0 := by exact_mod_cast (show km + 2 ≠ 0 by omega)
    try have hqmp30 : (km : ℝ) + 3 ≠ 0 := by exact_mod_cast (show km + 3 ≠ 0 by omega)
    try rw [show (km + -1 + -1 : ℤ) = km + -2 by ring]
    have hz0 : (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ km + -2 := by
      exact Or.inr (by omega)
    try rw [show (env "d" + (env "e" * t)) ^ (km) = (env "d" + (env "e" * t)) ^ (km + -2) * (env "d" + (env "e" * t)) ^ 2 from by
      have := zsplit ((env "d" + (env "e" * t))) (km + -2) 2 hz0
      rwa [show km + -2 + ((2 : ℕ) : ℤ) = km by push_cast; ring] at this]
    try generalize (env "d" + (env "e" * t)) ^ (km + -2) = P0
    try casesm* _ ∧ _
    field_simp
    grind

set_option maxHeartbeats 1000000 in
/-- RUBI rubi1212r77Nondeg: explicit term by the symbolic derivative. -/
theorem rubi1212r77Nondeg_real : rubi1212r77Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1212r77Nondeg.conditions rubi1212r77Nondeg.body rubi1212r77Nondeg.result rubi1212r77Nondeg.integrals
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
  refine antiderivRec_open Calc.real _ (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.var "c") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.int (-1)))) (rubi1212r77Nondeg.integrals.head!.2) (.app2 .mul (.int 1) (.pow (.var "c") (.int (-1)))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.real.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1212r77Nondeg, Defined, eval, hkm, hm1, h2] at h0
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
  have hbm1gt : 1 < km := by
    have h := hcs (.gt (.var "m") (.int 1)) (by simp [rubi1212r77Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hem] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi1212r77Nondeg, Defined, eval, hm1, h2, hem, Interp.toInt?_cast] at h0
  try casesm* _ ∧ _
  have hc0 := hcs (.ne (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1212r77Nondeg])
  simp [Cond.Holds, Defined, eval, h2] at hc0
  have hc2 := hcs (.ne (.app2 .mul (.var "c") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.int 0)) (by simp [rubi1212r77Nondeg])
  simp [Cond.Holds, Defined, eval] at hc2
  try simp only [hem] at hc0 hc2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc2]
  · simp [eval, Ok, Expr.varList, hm1, hc2, hem, hqm1]
    rcases lt_or_ge km 0 with hsm | hsm <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega)) <;> simp_all
  · simp [Defined, eval, hm1, hc2, hem, hqm1]
    rcases lt_or_ge km 0 with hsm | hsm <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega)) <;> simp_all
  · simp [Calc.real, rubi1212r77Nondeg, eval, Ok, Expr.varList, hm1, h2, hem, hqm3]
    rcases lt_or_ge km 0 with hsm | hsm <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi1212r77Nondeg, Defined, eval, hm1, h2, hem, hqm3]
    simp_all
  · simp [rubi1212r77Nondeg, eval, d, hm1, h2, hm11, hem, hwm11, hqm1, hqm3, Interp.toInt?_cast]
    try have hqmm10 : (km : ℝ) - 1 ≠ 0 := by exact_mod_cast (show km - 1 ≠ 0 by omega)
    try have hqmp00 : (km : ℝ) ≠ 0 := by exact_mod_cast (show km ≠ 0 by omega)
    try have hqmp10 : (km : ℝ) + 1 ≠ 0 := by exact_mod_cast (show km + 1 ≠ 0 by omega)
    try have hqmp20 : (km : ℝ) + 2 ≠ 0 := by exact_mod_cast (show km + 2 ≠ 0 by omega)
    try have hqmp30 : (km : ℝ) + 3 ≠ 0 := by exact_mod_cast (show km + 3 ≠ 0 by omega)
    try rw [show (km + -1 + -1 : ℤ) = km + -2 by ring]
    have hz0 : (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ km + -2 := by
      exact Or.inr (by omega)
    try rw [show (env "d" + (env "e" * t)) ^ (km) = (env "d" + (env "e" * t)) ^ (km + -2) * (env "d" + (env "e" * t)) ^ 2 from by
      have := zsplit ((env "d" + (env "e" * t))) (km + -2) 2 hz0
      rwa [show km + -2 + ((2 : ℕ) : ℤ) = km by push_cast; ring] at this]
    try generalize (env "d" + (env "e" * t)) ^ (km + -2) = P0
    try casesm* _ ∧ _
    field_simp
    grind

set_option maxHeartbeats 1000000 in
/-- RUBI rubi1212r77Nondeg: explicit term by the symbolic derivative. -/
theorem rubi1212r77Nondeg_complex : rubi1212r77Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1212r77Nondeg.conditions rubi1212r77Nondeg.body rubi1212r77Nondeg.result rubi1212r77Nondeg.integrals
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
  refine antiderivRec_open Calc.complex _ (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.var "c") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.int (-1)))) (rubi1212r77Nondeg.integrals.head!.2) (.app2 .mul (.int 1) (.pow (.var "c") (.int (-1)))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.complex.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1212r77Nondeg, Defined, eval, hkm, hm1, h2] at h0
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
  have hbm1gt : 1 < km := by
    have h := hcs (.gt (.var "m") (.int 1)) (by simp [rubi1212r77Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, hem, Complex.ext_iff] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi1212r77Nondeg, Defined, eval, hm1, h2, hem, Interp.toInt?_cast] at h0
  try casesm* _ ∧ _
  have hc0 := hcs (.ne (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1212r77Nondeg])
  simp [Cond.Holds, Defined, eval, h2] at hc0
  have hc2 := hcs (.ne (.app2 .mul (.var "c") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.int 0)) (by simp [rubi1212r77Nondeg])
  simp [Cond.Holds, Defined, eval] at hc2
  try simp only [hem] at hc0 hc2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc2]
  · simp [eval, Ok, Expr.varList, hm1, hc2, hem, hqm1]
    rcases lt_or_ge km 0 with hsm | hsm <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega)) <;> simp_all
  · simp [Defined, eval, hm1, hc2, hem, hqm1]
    rcases lt_or_ge km 0 with hsm | hsm <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega)) <;> simp_all
  · simp [Calc.complex, rubi1212r77Nondeg, eval, Ok, Expr.varList, hm1, h2, hem, hqm3]
    rcases lt_or_ge km 0 with hsm | hsm <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi1212r77Nondeg, Defined, eval, hm1, h2, hem, hqm3]
    simp_all
  · simp [rubi1212r77Nondeg, eval, d, hm1, h2, hm11, hem, hwm11, hqm1, hqm3, Interp.toInt?_cast]
    try have hqmm10 : (km : ℂ) - 1 ≠ 0 := by exact_mod_cast (show km - 1 ≠ 0 by omega)
    try have hqmp00 : (km : ℂ) ≠ 0 := by exact_mod_cast (show km ≠ 0 by omega)
    try have hqmp10 : (km : ℂ) + 1 ≠ 0 := by exact_mod_cast (show km + 1 ≠ 0 by omega)
    try have hqmp20 : (km : ℂ) + 2 ≠ 0 := by exact_mod_cast (show km + 2 ≠ 0 by omega)
    try have hqmp30 : (km : ℂ) + 3 ≠ 0 := by exact_mod_cast (show km + 3 ≠ 0 by omega)
    try rw [show (km + -1 + -1 : ℤ) = km + -2 by ring]
    have hz0 : (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ km + -2 := by
      exact Or.inr (by omega)
    try rw [show (env "d" + (env "e" * t)) ^ (km) = (env "d" + (env "e" * t)) ^ (km + -2) * (env "d" + (env "e" * t)) ^ 2 from by
      have := zsplit ((env "d" + (env "e" * t))) (km + -2) 2 hz0
      rwa [show km + -2 + ((2 : ℕ) : ℤ) = km by push_cast; ring] at this]
    try generalize (env "d" + (env "e" * t)) ^ (km + -2) = P0
    try casesm* _ ∧ _
    field_simp
    grind

set_option maxHeartbeats 1000000 in
/-- RUBI rubi1213r61Nondeg: explicit term by the symbolic derivative. -/
theorem rubi1213r61Nondeg_real : rubi1213r61Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1213r61Nondeg.conditions rubi1213r61Nondeg.body rubi1213r61Nondeg.result rubi1213r61Nondeg.integrals
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
  refine antiderivRec_open Calc.real _ (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1)))) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.var "a")) (.var "c")) (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "g")) (.var "c")) (.var "d"))) (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.app2 .mul (.app2 .mul (.var "c") (.var "d")) (.var "f")) (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.var "g")))) (.var "x")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))))) (.int (-1)))) (rubi1213r61Nondeg.integrals.head!.2) (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))))) (.int (-1)))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.real.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1213r61Nondeg, Defined, eval, hkm, h2] at h0
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
  rcases hkp : Interp.real.toInt? (env "p") with _ | kp
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1213r61Nondeg, Defined, eval, hkp, h2] at h0
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
  have hbp1gt : kp < -1 := by
    have h := hcs (.gt (.int (-1)) (.var "p")) (by simp [rubi1213r61Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hep] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi1213r61Nondeg, Defined, eval, h2, hem, hep, Interp.toInt?_cast] at h0
  try casesm* _ ∧ _
  have hc0 := hcs (.ne (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1213r61Nondeg])
  simp [Cond.Holds, Defined, eval, h2] at hc0
  have hc4 := hcs (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))))) (.int 0)) (by simp [rubi1213r61Nondeg])
  simp [Cond.Holds, Defined, eval, h2] at hc4
  try simp only [hep] at hc0 hc4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, h2, hc0, hc4, hep]
  · simp [eval, Ok, Expr.varList, hm1, h2, hc0, hc4, hem, hqm2, hep, hqp2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [Defined, eval, hm1, h2, hc0, hc4, hem, hqm2, hep, hqp2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [Calc.real, rubi1213r61Nondeg, eval, Ok, Expr.varList, h2, hc4, hem, hep, hqp2, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi1213r61Nondeg, Defined, eval, h2, hc4, hem, hep, hqp2, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi1213r61Nondeg, eval, d, hm1, h2, hm11, hn21, hem, hqm2, hep, hqp2, Interp.toInt?_cast]
    try have hqpm30 : (kp : ℝ) - 3 ≠ 0 := by exact_mod_cast (show kp - 3 ≠ 0 by omega)
    try have hqpm20 : (kp : ℝ) - 2 ≠ 0 := by exact_mod_cast (show kp - 2 ≠ 0 by omega)
    try have hqpm10 : (kp : ℝ) - 1 ≠ 0 := by exact_mod_cast (show kp - 1 ≠ 0 by omega)
    try have hqpp00 : (kp : ℝ) ≠ 0 := by exact_mod_cast (show kp ≠ 0 by omega)
    try have hqpp10 : (kp : ℝ) + 1 ≠ 0 := by exact_mod_cast (show kp + 1 ≠ 0 by omega)
    have hz0 : (env "a" + (env "c" * (t ^ 2))) ≠ 0 ∨ 0 ≤ kp := by
      rcases lt_or_ge (kp) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show (env "a" + (env "c" * (t ^ 2))) ^ (kp + 1) = (env "a" + (env "c" * (t ^ 2))) ^ (kp) * (env "a" + (env "c" * (t ^ 2))) ^ 1 from by
      have := zsplit ((env "a" + (env "c" * (t ^ 2)))) (kp) 1 hz0
      rwa [show kp + ((1 : ℕ) : ℤ) = kp + 1 by push_cast; ring] at this]
    try generalize (env "a" + (env "c" * (t ^ 2))) ^ (kp) = P0
    have hz1 : (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ km := by
      rcases lt_or_ge (km) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show (env "d" + (env "e" * t)) ^ (km + 1) = (env "d" + (env "e" * t)) ^ (km) * (env "d" + (env "e" * t)) ^ 1 from by
      have := zsplit ((env "d" + (env "e" * t))) (km) 1 hz1
      rwa [show km + ((1 : ℕ) : ℤ) = km + 1 by push_cast; ring] at this]
    try generalize (env "d" + (env "e" * t)) ^ (km) = P1
    try casesm* _ ∧ _
    field_simp
    grind

set_option maxHeartbeats 1000000 in
/-- RUBI rubi1213r61Nondeg: explicit term by the symbolic derivative. -/
theorem rubi1213r61Nondeg_complex : rubi1213r61Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1213r61Nondeg.conditions rubi1213r61Nondeg.body rubi1213r61Nondeg.result rubi1213r61Nondeg.integrals
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
  refine antiderivRec_open Calc.complex _ (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1)))) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.var "a")) (.var "c")) (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "g")) (.var "c")) (.var "d"))) (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.app2 .mul (.app2 .mul (.var "c") (.var "d")) (.var "f")) (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.var "g")))) (.var "x")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))))) (.int (-1)))) (rubi1213r61Nondeg.integrals.head!.2) (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))))) (.int (-1)))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.complex.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1213r61Nondeg, Defined, eval, hkm, h2] at h0
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
  rcases hkp : Interp.complex.toInt? (env "p") with _ | kp
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi1213r61Nondeg, Defined, eval, hkp, h2] at h0
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
  have hwp00 : Interp.complex.toInt? ((kp : ℂ) + -2 + -2) = some (kp + -2 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp01 : Interp.complex.toInt? ((kp : ℂ) + -2 + -1) = some (kp + -2 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp02 : Interp.complex.toInt? ((kp : ℂ) + -2 + 1) = some (kp + -2 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp03 : Interp.complex.toInt? ((kp : ℂ) + -2 + 2) = some (kp + -2 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp10 : Interp.complex.toInt? ((kp : ℂ) + -1 + -2) = some (kp + -1 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp11 : Interp.complex.toInt? ((kp : ℂ) + -1 + -1) = some (kp + -1 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp12 : Interp.complex.toInt? ((kp : ℂ) + -1 + 1) = some (kp + -1 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp13 : Interp.complex.toInt? ((kp : ℂ) + -1 + 2) = some (kp + -1 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp20 : Interp.complex.toInt? ((kp : ℂ) + 1 + -2) = some (kp + 1 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp21 : Interp.complex.toInt? ((kp : ℂ) + 1 + -1) = some (kp + 1 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp22 : Interp.complex.toInt? ((kp : ℂ) + 1 + 1) = some (kp + 1 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp23 : Interp.complex.toInt? ((kp : ℂ) + 1 + 2) = some (kp + 1 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp30 : Interp.complex.toInt? ((kp : ℂ) + 2 + -2) = some (kp + 2 + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp31 : Interp.complex.toInt? ((kp : ℂ) + 2 + -1) = some (kp + 2 + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp32 : Interp.complex.toInt? ((kp : ℂ) + 2 + 1) = some (kp + 2 + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hwp33 : Interp.complex.toInt? ((kp : ℂ) + 2 + 2) = some (kp + 2 + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by push_cast; ring)
  have hkpp1 : Interp.complex.toInt? (env "p" + 1) = some (kp + 1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpp2 : Interp.complex.toInt? (env "p" + 2) = some (kp + 2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm1 : Interp.complex.toInt? (env "p" + -1) = some (kp + -1) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hkpm2 : Interp.complex.toInt? (env "p" + -2) = some (kp + -2) :=
    (Interp.complex.toInt?_eq _ _).2 (by rw [(Interp.complex.toInt?_eq _ _).1 hkp]; push_cast; ring)
  have hbp1gt : kp < -1 := by
    have h := hcs (.gt (.int (-1)) (.var "p")) (by simp [rubi1213r61Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, hep, Complex.ext_iff] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi1213r61Nondeg, Defined, eval, h2, hem, hep, Interp.toInt?_cast] at h0
  try casesm* _ ∧ _
  have hc0 := hcs (.ne (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1213r61Nondeg])
  simp [Cond.Holds, Defined, eval, h2] at hc0
  have hc4 := hcs (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))))) (.int 0)) (by simp [rubi1213r61Nondeg])
  simp [Cond.Holds, Defined, eval, h2] at hc4
  try simp only [hep] at hc0 hc4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, h2, hc0, hc4, hep]
  · simp [eval, Ok, Expr.varList, hm1, h2, hc0, hc4, hem, hqm2, hep, hqp2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [Defined, eval, hm1, h2, hc0, hc4, hem, hqm2, hep, hqp2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [Calc.complex, rubi1213r61Nondeg, eval, Ok, Expr.varList, h2, hc4, hem, hep, hqp2, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi1213r61Nondeg, Defined, eval, h2, hc4, hem, hep, hqp2, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi1213r61Nondeg, eval, d, hm1, h2, hm11, hn21, hem, hqm2, hep, hqp2, Interp.toInt?_cast]
    try have hqpm30 : (kp : ℂ) - 3 ≠ 0 := by exact_mod_cast (show kp - 3 ≠ 0 by omega)
    try have hqpm20 : (kp : ℂ) - 2 ≠ 0 := by exact_mod_cast (show kp - 2 ≠ 0 by omega)
    try have hqpm10 : (kp : ℂ) - 1 ≠ 0 := by exact_mod_cast (show kp - 1 ≠ 0 by omega)
    try have hqpp00 : (kp : ℂ) ≠ 0 := by exact_mod_cast (show kp ≠ 0 by omega)
    try have hqpp10 : (kp : ℂ) + 1 ≠ 0 := by exact_mod_cast (show kp + 1 ≠ 0 by omega)
    have hz0 : (env "a" + (env "c" * (t ^ 2))) ≠ 0 ∨ 0 ≤ kp := by
      rcases lt_or_ge (kp) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show (env "a" + (env "c" * (t ^ 2))) ^ (kp + 1) = (env "a" + (env "c" * (t ^ 2))) ^ (kp) * (env "a" + (env "c" * (t ^ 2))) ^ 1 from by
      have := zsplit ((env "a" + (env "c" * (t ^ 2)))) (kp) 1 hz0
      rwa [show kp + ((1 : ℕ) : ℤ) = kp + 1 by push_cast; ring] at this]
    try generalize (env "a" + (env "c" * (t ^ 2))) ^ (kp) = P0
    have hz1 : (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ km := by
      rcases lt_or_ge (km) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show (env "d" + (env "e" * t)) ^ (km + 1) = (env "d" + (env "e" * t)) ^ (km) * (env "d" + (env "e" * t)) ^ 1 from by
      have := zsplit ((env "d" + (env "e" * t))) (km) 1 hz1
      rwa [show km + ((1 : ℕ) : ℤ) = km + 1 by push_cast; ring] at this]
    try generalize (env "d" + (env "e" * t)) ^ (km) = P1
    try casesm* _ ∧ _
    field_simp
    grind

set_option maxHeartbeats 1000000 in
/-- RUBI rubi534r45Nondeg: explicit term by the symbolic derivative. -/
theorem rubi534r45Nondeg_real : rubi534r45Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi534r45Nondeg.conditions rubi534r45Nondeg.body rubi534r45Nondeg.result rubi534r45Nondeg.integrals
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
  refine antiderivRec_lin2 Calc.real _ ((rubi534r45Nondeg.integrals[0]!).2) ((rubi534r45Nondeg.integrals[1]!).2) (.app2 .mul (.pow (.var "f") (.int 2)) (.pow (.var "e") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.pow (.var "f") (.int 2))) (.pow (.var "e") (.int (-1)))) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.real.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi534r45Nondeg, Defined, eval, hkm, hm1, h2] at h0
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
  rcases hkp : Interp.real.toInt? (env "p") with _ | kp
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi534r45Nondeg, Defined, eval, hkp, hm1, h2] at h0
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
    have h := hcs (.gt (.var "p") (.int 0)) (by simp [rubi534r45Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hep] at h
    exact_mod_cast h
  have hbm1gt : 1 < km := by
    have h := hcs (.gt (.var "m") (.int 1)) (by simp [rubi534r45Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hem] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi534r45Nondeg, Defined, eval, hm1, h2, hem, hep, Interp.toInt?_cast] at h0
  try casesm* _ ∧ _
  have hc2 := hcs (.ne (.var "e") (.int 0)) (by simp [rubi534r45Nondeg])
  simp [Cond.Holds, Defined, eval] at hc2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, h2, hc2]
  · simp [Defined, eval, hm1, h2, hc2]
  · simp [Calc.real, rubi534r45Nondeg, eval, Ok, Expr.varList, hem, hqm3, hep, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi534r45Nondeg, Defined, eval, hem, hqm3, hep, Interp.toInt?_cast]
    simp_all
  · simp [Calc.real, rubi534r45Nondeg, eval, Ok, Expr.varList, hm1, h2, hem, hqm3, hep, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi534r45Nondeg, Defined, eval, hm1, h2, hem, hqm3, hep, Interp.toInt?_cast]
    simp_all
  · simp [rubi534r45Nondeg, eval, hm1, h2, hem, hqm3, hep, Interp.toInt?_cast]
    try have hqmm10 : (km : ℝ) - 1 ≠ 0 := by exact_mod_cast (show km - 1 ≠ 0 by omega)
    try have hqmp00 : (km : ℝ) ≠ 0 := by exact_mod_cast (show km ≠ 0 by omega)
    try have hqmp10 : (km : ℝ) + 1 ≠ 0 := by exact_mod_cast (show km + 1 ≠ 0 by omega)
    try have hqmp20 : (km : ℝ) + 2 ≠ 0 := by exact_mod_cast (show km + 2 ≠ 0 by omega)
    try have hqmp30 : (km : ℝ) + 3 ≠ 0 := by exact_mod_cast (show km + 3 ≠ 0 by omega)
    try have hqpp00 : (kp : ℝ) ≠ 0 := by exact_mod_cast (show kp ≠ 0 by omega)
    try have hqpp10 : (kp : ℝ) + 1 ≠ 0 := by exact_mod_cast (show kp + 1 ≠ 0 by omega)
    try have hqpp20 : (kp : ℝ) + 2 ≠ 0 := by exact_mod_cast (show kp + 2 ≠ 0 by omega)
    try have hqpp30 : (kp : ℝ) + 3 ≠ 0 := by exact_mod_cast (show kp + 3 ≠ 0 by omega)
    have hz1 : (env "f" * t) ≠ 0 ∨ 0 ≤ km + -2 := by
      exact Or.inr (by omega)
    try rw [show (env "f" * t) ^ (km) = (env "f" * t) ^ (km + -2) * (env "f" * t) ^ 2 from by
      have := zsplit ((env "f" * t)) (km + -2) 2 hz1
      rwa [show km + -2 + ((2 : ℕ) : ℤ) = km by push_cast; ring] at this]
    try generalize (env "f" * t) ^ (km + -2) = P1
    field_simp
    grind

set_option maxHeartbeats 1000000 in
/-- RUBI rubi534r46Nondeg: explicit term by the symbolic derivative. -/
theorem rubi534r46Nondeg_real : rubi534r46Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi534r46Nondeg.conditions rubi534r46Nondeg.body rubi534r46Nondeg.result rubi534r46Nondeg.integrals
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
  refine antiderivRec_lin2 Calc.real _ ((rubi534r46Nondeg.integrals[0]!).2) ((rubi534r46Nondeg.integrals[1]!).2) (.app2 .mul (.pow (.var "f") (.int 2)) (.pow (.var "e") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.pow (.var "f") (.int 2))) (.pow (.var "e") (.int (-1)))) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.real.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi534r46Nondeg, Defined, eval, hkm, hm1, h2] at h0
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
  rcases hkp : Interp.real.toInt? (env "p") with _ | kp
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi534r46Nondeg, Defined, eval, hkp, hm1, h2] at h0
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
    have h := hcs (.gt (.var "p") (.int 0)) (by simp [rubi534r46Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hep] at h
    exact_mod_cast h
  have hbm1gt : 1 < km := by
    have h := hcs (.gt (.var "m") (.int 1)) (by simp [rubi534r46Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hem] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi534r46Nondeg, Defined, eval, hm1, h2, hem, hep, Interp.toInt?_cast] at h0
  try casesm* _ ∧ _
  have hc2 := hcs (.ne (.var "e") (.int 0)) (by simp [rubi534r46Nondeg])
  simp [Cond.Holds, Defined, eval] at hc2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, h2, hc2]
  · simp [Defined, eval, hm1, h2, hc2]
  · simp [Calc.real, rubi534r46Nondeg, eval, Ok, Expr.varList, hm1, hem, hqm3, hep, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi534r46Nondeg, Defined, eval, hm1, hem, hqm3, hep, Interp.toInt?_cast]
    simp_all
  · simp [Calc.real, rubi534r46Nondeg, eval, Ok, Expr.varList, hm1, h2, hem, hqm3, hep, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi534r46Nondeg, Defined, eval, hm1, h2, hem, hqm3, hep, Interp.toInt?_cast]
    simp_all
  · simp [rubi534r46Nondeg, eval, hm1, h2, hem, hqm3, hep, Interp.toInt?_cast]
    try have hqmm10 : (km : ℝ) - 1 ≠ 0 := by exact_mod_cast (show km - 1 ≠ 0 by omega)
    try have hqmp00 : (km : ℝ) ≠ 0 := by exact_mod_cast (show km ≠ 0 by omega)
    try have hqmp10 : (km : ℝ) + 1 ≠ 0 := by exact_mod_cast (show km + 1 ≠ 0 by omega)
    try have hqmp20 : (km : ℝ) + 2 ≠ 0 := by exact_mod_cast (show km + 2 ≠ 0 by omega)
    try have hqmp30 : (km : ℝ) + 3 ≠ 0 := by exact_mod_cast (show km + 3 ≠ 0 by omega)
    try have hqpp00 : (kp : ℝ) ≠ 0 := by exact_mod_cast (show kp ≠ 0 by omega)
    try have hqpp10 : (kp : ℝ) + 1 ≠ 0 := by exact_mod_cast (show kp + 1 ≠ 0 by omega)
    try have hqpp20 : (kp : ℝ) + 2 ≠ 0 := by exact_mod_cast (show kp + 2 ≠ 0 by omega)
    try have hqpp30 : (kp : ℝ) + 3 ≠ 0 := by exact_mod_cast (show kp + 3 ≠ 0 by omega)
    have hz1 : (env "f" * t) ≠ 0 ∨ 0 ≤ km + -2 := by
      exact Or.inr (by omega)
    try rw [show (env "f" * t) ^ (km) = (env "f" * t) ^ (km + -2) * (env "f" * t) ^ 2 from by
      have := zsplit ((env "f" * t)) (km + -2) 2 hz1
      rwa [show km + -2 + ((2 : ℕ) : ℤ) = km by push_cast; ring] at this]
    try generalize (env "f" * t) ^ (km + -2) = P1
    field_simp
    grind

set_option maxHeartbeats 1000000 in
/-- RUBI rubi534r47Nondeg: explicit term by the symbolic derivative. -/
theorem rubi534r47Nondeg_real : rubi534r47Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi534r47Nondeg.conditions rubi534r47Nondeg.body rubi534r47Nondeg.result rubi534r47Nondeg.integrals
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
  refine antiderivRec_lin2 Calc.real _ ((rubi534r47Nondeg.integrals[0]!).2) ((rubi534r47Nondeg.integrals[1]!).2) (.app2 .mul (.int 1) (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.app2 .mul (.var "d") (.pow (.var "f") (.int 2))) (.int (-1)))) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.real.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi534r47Nondeg, Defined, eval, hkm, hm1, h2] at h0
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
  rcases hkp : Interp.real.toInt? (env "p") with _ | kp
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi534r47Nondeg, Defined, eval, hkp, hm1, h2] at h0
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
    have h := hcs (.gt (.var "p") (.int 0)) (by simp [rubi534r47Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hep] at h
    exact_mod_cast h
  have hbm1gt : km < -1 := by
    have h := hcs (.gt (.int (-1)) (.var "m")) (by simp [rubi534r47Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hem] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi534r47Nondeg, Defined, eval, hm1, h2, hem, hep, Interp.toInt?_cast] at h0
  try casesm* _ ∧ _
  have hc2 := hcs (.ne (.var "d") (.int 0)) (by simp [rubi534r47Nondeg])
  simp [Cond.Holds, Defined, eval] at hc2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc2]
  · simp [Defined, eval, hm1, h2, hc2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [Calc.real, rubi534r47Nondeg, eval, Ok, Expr.varList, hem, hep, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi534r47Nondeg, Defined, eval, hem, hep, Interp.toInt?_cast]
    simp_all
  · simp [Calc.real, rubi534r47Nondeg, eval, Ok, Expr.varList, hm1, h2, hem, hqm4, hep, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi534r47Nondeg, Defined, eval, hm1, h2, hem, hqm4, hep, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi534r47Nondeg, eval, hm1, h2, hem, hqm4, hep, Interp.toInt?_cast]
    try have hqmm30 : (km : ℝ) - 3 ≠ 0 := by exact_mod_cast (show km - 3 ≠ 0 by omega)
    try have hqmm20 : (km : ℝ) - 2 ≠ 0 := by exact_mod_cast (show km - 2 ≠ 0 by omega)
    try have hqmm10 : (km : ℝ) - 1 ≠ 0 := by exact_mod_cast (show km - 1 ≠ 0 by omega)
    try have hqmp00 : (km : ℝ) ≠ 0 := by exact_mod_cast (show km ≠ 0 by omega)
    try have hqmp10 : (km : ℝ) + 1 ≠ 0 := by exact_mod_cast (show km + 1 ≠ 0 by omega)
    try have hqpp00 : (kp : ℝ) ≠ 0 := by exact_mod_cast (show kp ≠ 0 by omega)
    try have hqpp10 : (kp : ℝ) + 1 ≠ 0 := by exact_mod_cast (show kp + 1 ≠ 0 by omega)
    try have hqpp20 : (kp : ℝ) + 2 ≠ 0 := by exact_mod_cast (show kp + 2 ≠ 0 by omega)
    try have hqpp30 : (kp : ℝ) + 3 ≠ 0 := by exact_mod_cast (show kp + 3 ≠ 0 by omega)
    have hz1 : (env "f" * t) ≠ 0 ∨ 0 ≤ km := by
      rcases lt_or_ge (km) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show (env "f" * t) ^ (km + 2) = (env "f" * t) ^ (km) * (env "f" * t) ^ 2 from by
      have := zsplit ((env "f" * t)) (km) 2 hz1
      rwa [show km + ((2 : ℕ) : ℤ) = km + 2 by push_cast; ring] at this]
    try generalize (env "f" * t) ^ (km) = P1
    field_simp
    grind

set_option maxHeartbeats 1000000 in
/-- RUBI rubi534r48Nondeg: explicit term by the symbolic derivative. -/
theorem rubi534r48Nondeg_real : rubi534r48Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi534r48Nondeg.conditions rubi534r48Nondeg.body rubi534r48Nondeg.result rubi534r48Nondeg.integrals
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
  refine antiderivRec_lin2 Calc.real _ ((rubi534r48Nondeg.integrals[0]!).2) ((rubi534r48Nondeg.integrals[1]!).2) (.app2 .mul (.int 1) (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.app2 .mul (.var "d") (.pow (.var "f") (.int 2))) (.int (-1)))) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.real.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi534r48Nondeg, Defined, eval, hkm, hm1, h2] at h0
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
  rcases hkp : Interp.real.toInt? (env "p") with _ | kp
  · exfalso
    have h0 := hF.self_of_nhds
    simp [rubi534r48Nondeg, Defined, eval, hkp, hm1, h2] at h0
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
    have h := hcs (.gt (.var "p") (.int 0)) (by simp [rubi534r48Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hep] at h
    exact_mod_cast h
  have hbm1gt : km < -1 := by
    have h := hcs (.gt (.int (-1)) (.var "m")) (by simp [rubi534r48Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hem] at h
    exact_mod_cast h
  have h0 := hF.self_of_nhds
  simp [rubi534r48Nondeg, Defined, eval, hm1, h2, hem, hep, Interp.toInt?_cast] at h0
  try casesm* _ ∧ _
  have hc2 := hcs (.ne (.var "d") (.int 0)) (by simp [rubi534r48Nondeg])
  simp [Cond.Holds, Defined, eval] at hc2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc2]
  · simp [Defined, eval, hm1, h2, hc2]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [Calc.real, rubi534r48Nondeg, eval, Ok, Expr.varList, hm1, hem, hep, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi534r48Nondeg, Defined, eval, hm1, hem, hep, Interp.toInt?_cast]
    simp_all
  · simp [Calc.real, rubi534r48Nondeg, eval, Ok, Expr.varList, hm1, h2, hem, hqm4, hep, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi534r48Nondeg, Defined, eval, hm1, h2, hem, hqm4, hep, Interp.toInt?_cast]
    rcases lt_or_ge km 0 with hsm | hsm <;> rcases lt_or_ge kp 0 with hsp | hsp <;> ((try have : km + -2 < 0 := by omega); (try have : 0 ≤ km + -2 := by omega); (try have : -2 ≤ km := by omega); (try have : km < -2 := by omega); (try have : ¬ km < -2 := by omega); (try have : ¬ km + -2 < 0 := by omega); (try have : km + -1 < 0 := by omega); (try have : 0 ≤ km + -1 := by omega); (try have : -1 ≤ km := by omega); (try have : km < -1 := by omega); (try have : ¬ km < -1 := by omega); (try have : ¬ km + -1 < 0 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : km + 1 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : 1 ≤ km := by omega); (try have : km < 1 := by omega); (try have : ¬ km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : km + 2 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : 2 ≤ km := by omega); (try have : km < 2 := by omega); (try have : ¬ km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega); (try have : kp + -2 < 0 := by omega); (try have : 0 ≤ kp + -2 := by omega); (try have : -2 ≤ kp := by omega); (try have : kp < -2 := by omega); (try have : ¬ kp < -2 := by omega); (try have : ¬ kp + -2 < 0 := by omega); (try have : kp + -1 < 0 := by omega); (try have : 0 ≤ kp + -1 := by omega); (try have : -1 ≤ kp := by omega); (try have : kp < -1 := by omega); (try have : ¬ kp < -1 := by omega); (try have : ¬ kp + -1 < 0 := by omega); (try have : kp + 0 < 0 := by omega); (try have : 0 ≤ kp + 0 := by omega); (try have : 0 ≤ kp := by omega); (try have : kp < 0 := by omega); (try have : ¬ kp < 0 := by omega); (try have : ¬ kp + 0 < 0 := by omega); (try have : kp + 1 < 0 := by omega); (try have : 0 ≤ kp + 1 := by omega); (try have : 1 ≤ kp := by omega); (try have : kp < 1 := by omega); (try have : ¬ kp < 1 := by omega); (try have : ¬ kp + 1 < 0 := by omega); (try have : kp + 2 < 0 := by omega); (try have : 0 ≤ kp + 2 := by omega); (try have : 2 ≤ kp := by omega); (try have : kp < 2 := by omega); (try have : ¬ kp < 2 := by omega); (try have : ¬ kp + 2 < 0 := by omega)) <;> simp_all
  · simp [rubi534r48Nondeg, eval, hm1, h2, hem, hqm4, hep, Interp.toInt?_cast]
    try have hqmm30 : (km : ℝ) - 3 ≠ 0 := by exact_mod_cast (show km - 3 ≠ 0 by omega)
    try have hqmm20 : (km : ℝ) - 2 ≠ 0 := by exact_mod_cast (show km - 2 ≠ 0 by omega)
    try have hqmm10 : (km : ℝ) - 1 ≠ 0 := by exact_mod_cast (show km - 1 ≠ 0 by omega)
    try have hqmp00 : (km : ℝ) ≠ 0 := by exact_mod_cast (show km ≠ 0 by omega)
    try have hqmp10 : (km : ℝ) + 1 ≠ 0 := by exact_mod_cast (show km + 1 ≠ 0 by omega)
    try have hqpp00 : (kp : ℝ) ≠ 0 := by exact_mod_cast (show kp ≠ 0 by omega)
    try have hqpp10 : (kp : ℝ) + 1 ≠ 0 := by exact_mod_cast (show kp + 1 ≠ 0 by omega)
    try have hqpp20 : (kp : ℝ) + 2 ≠ 0 := by exact_mod_cast (show kp + 2 ≠ 0 by omega)
    try have hqpp30 : (kp : ℝ) + 3 ≠ 0 := by exact_mod_cast (show kp + 3 ≠ 0 by omega)
    have hz1 : (env "f" * t) ≠ 0 ∨ 0 ≤ km := by
      rcases lt_or_ge (km) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show (env "f" * t) ^ (km + 2) = (env "f" * t) ^ (km) * (env "f" * t) ^ 2 from by
      have := zsplit ((env "f" * t)) (km) 2 hz1
      rwa [show km + ((2 : ℕ) : ℤ) = km + 2 by push_cast; ring] at this]
    try generalize (env "f" * t) ^ (km) = P1
    field_simp
    grind

end OSR.IntegrationRec306
