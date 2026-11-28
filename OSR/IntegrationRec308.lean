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

namespace OSR.IntegrationRec308
open OSR OSR.Calculus OSR.IntegrationNum1 OSR.SymDeriv Filter Topology

private theorem zsplit {K : Type} [DivisionRing K] (X : K) (j : ℤ) (n : ℕ) (h : X ≠ 0 ∨ 0 ≤ j) :
    X ^ (j + n) = X ^ j * X ^ n := by
  rcases h with h | h
  · rw [zpow_add₀ h, zpow_natCast]
  · lift j to ℕ using h
    rw [show ((j : ℤ) + n) = ((j + n : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
      pow_add]

set_option maxHeartbeats 1000000 in
/-- RUBI rubi537r17Nondeg: explicit term by the symbolic derivative. -/
theorem rubi537r17Nondeg_real : rubi537r17Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi537r17Nondeg.conditions rubi537r17Nondeg.body rubi537r17Nondeg.result rubi537r17Nondeg.integrals
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
  have droot : ∀ z n : ℝ, Interp.real.root z n = Real.sqrt z := fun _ _ => rfl
  refine antiderivRec_open Calc.real _ (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.app1 .arctan (.app2 .mul (.app2 .mul (.var "c") (.var "x")) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (rubi537r17Nondeg.integrals.head!.2) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.real.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [droot, Real.sqrt_eq_zero', rubi537r17Nondeg, Defined, eval, hkm, hm1, h2] at h0
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
  have h0 := hF.self_of_nhds
  simp [droot, Real.sqrt_eq_zero', rubi537r17Nondeg, Defined, eval, hm1, h2, hem,
      Interp.toInt?_cast] at h0
  try casesm* _ ∧ _
  have hc0 := hcs (.eq (.app2 .add (.var "b") (.pow (.var "c") (.int 2))) (.int 0)) (by simp [rubi537r17Nondeg])
  simp [Cond.Holds, Defined, eval, h2] at hc0
  have hc1 := hcs (.ne (.var "m") (.int (-1))) (by simp [rubi537r17Nondeg])
  simp [Cond.Holds, Defined, eval] at hc1
  have hc2 := hcs (.ne (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi537r17Nondeg])
  simp [Cond.Holds, Defined, eval] at hc2
  try simp only [hem] at hc0 hc1 hc2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc2, hem]
  · simp [Calc.real, droot, Real.sqrt_eq_zero', eval, Ok, Expr.varList, hm1, h2, hc2, hem, hqm2]
    rcases lt_or_ge km 0 with hsm | hsm <;> ((try have : km + -2 < 0 := by omega); (try have : -2 ≤ km := by omega); (try have : ¬ km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : -1 ≤ km := by omega); (try have : ¬ km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega)) <;> simp_all
  · simp [droot, Real.sqrt_eq_zero', Defined, eval, hm1, h2, hc2, hem, hqm2]
    rcases lt_or_ge km 0 with hsm | hsm <;> ((try have : km + -2 < 0 := by omega); (try have : -2 ≤ km := by omega); (try have : ¬ km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : -1 ≤ km := by omega); (try have : ¬ km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega)) <;> simp_all
  · simp [Calc.real, droot, Real.sqrt_eq_zero', rubi537r17Nondeg, eval, Ok, Expr.varList, hm1, h2, hc2, hem, hqm2]
    rcases lt_or_ge km 0 with hsm | hsm <;> ((try have : km + -2 < 0 := by omega); (try have : -2 ≤ km := by omega); (try have : ¬ km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : -1 ≤ km := by omega); (try have : ¬ km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega)) <;> simp_all
  · simp [droot, Real.sqrt_eq_zero', rubi537r17Nondeg, Defined, eval, hm1, h2, hc2, hem, hqm2]
    rcases lt_or_ge km 0 with hsm | hsm <;> ((try have : km + -2 < 0 := by omega); (try have : -2 ≤ km := by omega); (try have : ¬ km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : -1 ≤ km := by omega); (try have : ¬ km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega)) <;> simp_all
  · simp [droot, rubi537r17Nondeg, eval, d, hm1, h2, hm11, hn21, hem, hqm2, Interp.toInt?_cast]
    have hz0 : (env "d" * t) ≠ 0 ∨ 0 ≤ km := by
      rcases lt_or_ge (km) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show (env "d" * t) ^ (km + 1) = (env "d" * t) ^ (km) * (env "d" * t) ^ 1 from by
      have := zsplit ((env "d" * t)) (km) 1 hz0
      rwa [show km + ((1 : ℕ) : ℤ) = km + 1 by push_cast; ring] at this]
    try generalize (env "d" * t) ^ (km) = P0
    try casesm* _ ∧ _
    field_simp
    grind

set_option maxHeartbeats 1000000 in
/-- RUBI rubi537r18Nondeg: explicit term by the symbolic derivative. -/
theorem rubi537r18Nondeg_real : rubi537r18Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi537r18Nondeg.conditions rubi537r18Nondeg.body rubi537r18Nondeg.result rubi537r18Nondeg.integrals
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
  have droot : ∀ z n : ℝ, Interp.real.root z n = Real.sqrt z := fun _ _ => rfl
  refine antiderivRec_open Calc.real _ (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.app1 .arctan (.pow (.app2 .mul (.app2 .mul (.var "c") (.var "x")) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))) (.int (-1))))) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (rubi537r18Nondeg.integrals.head!.2) (.app2 .mul (.var "c") (.pow (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (by decide) (by decide) (by decide) ?_
  intro env hcs t hF
  rcases hkm : Interp.real.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [droot, Real.sqrt_eq_zero', rubi537r18Nondeg, Defined, eval, hkm, hm1, h2] at h0
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
  have h0 := hF.self_of_nhds
  simp [droot, Real.sqrt_eq_zero', rubi537r18Nondeg, Defined, eval, hm1, h2, hem,
      Interp.toInt?_cast] at h0
  try casesm* _ ∧ _
  have hc0 := hcs (.eq (.app2 .add (.var "b") (.pow (.var "c") (.int 2))) (.int 0)) (by simp [rubi537r18Nondeg])
  simp [Cond.Holds, Defined, eval, h2] at hc0
  have hc1 := hcs (.ne (.var "m") (.int (-1))) (by simp [rubi537r18Nondeg])
  simp [Cond.Holds, Defined, eval] at hc1
  have hc2 := hcs (.ne (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi537r18Nondeg])
  simp [Cond.Holds, Defined, eval] at hc2
  try simp only [hem] at hc0 hc1 hc2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc2, hem]
  · simp [Calc.real, droot, Real.sqrt_eq_zero', eval, Ok, Expr.varList, hm1, h2, hc2, hem, hqm2]
    simp_all
  · simp [droot, Real.sqrt_eq_zero', Defined, eval, hm1, h2, hc2, hem, hqm2]
    simp_all
  · simp [Calc.real, droot, Real.sqrt_eq_zero', rubi537r18Nondeg, eval, Ok, Expr.varList, hm1, h2, hc2, hem, hqm2]
    simp_all
  · simp [droot, Real.sqrt_eq_zero', rubi537r18Nondeg, Defined, eval, hm1, h2, hc2, hem, hqm2]
    simp_all
  · simp [droot, rubi537r18Nondeg, eval, d, hm1, h2, hm11, hn21, hem, hqm2, Interp.toInt?_cast]
    have hz0 : (env "d" * t) ≠ 0 ∨ 0 ≤ km := by
      rcases lt_or_ge (km) 0 with hzz | hzz
      · left; simp_all
      · exact Or.inr hzz
    try rw [show (env "d" * t) ^ (km + 1) = (env "d" * t) ^ (km) * (env "d" * t) ^ 1 from by
      have := zsplit ((env "d" * t)) (km) 1 hz0
      rwa [show km + ((1 : ℕ) : ℤ) = km + 1 by push_cast; ring] at this]
    try generalize (env "d" * t) ^ (km) = P0
    try casesm* _ ∧ _
    field_simp
    grind

set_option maxHeartbeats 1000000 in
/-- RUBI rubi537r21Nondeg: explicit term by the symbolic derivative. -/
theorem rubi537r21Nondeg_real : rubi537r21Nondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" rubi537r21Nondeg.conditions rubi537r21Nondeg.body rubi537r21Nondeg.result
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
  have droot : ∀ z n : ℝ, Interp.real.root z n = Real.sqrt z := fun _ _ => rfl
  refine antideriv_open Calc.real _ (.app2 .mul (.pow (.app1 .arctan (.app2 .mul (.app2 .mul (.var "c") (.var "x")) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .mul (.var "c") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) ?_
  intro env hcs t hF
  rcases hkm : Interp.real.toInt? (env "m") with _ | km
  · exfalso
    have h0 := hF.self_of_nhds
    simp [droot, Real.sqrt_eq_zero', rubi537r21Nondeg, Defined, eval, hkm, hm1, h2] at h0
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
  have h0 := hF.self_of_nhds
  simp [droot, Real.sqrt_eq_zero', rubi537r21Nondeg, Defined, eval, hm1, h2, hem,
      Interp.toInt?_cast] at h0
  try casesm* _ ∧ _
  have hc0 := hcs (.eq (.app2 .add (.var "b") (.pow (.var "c") (.int 2))) (.int 0)) (by simp [rubi537r21Nondeg])
  simp [Cond.Holds, Defined, eval, h2] at hc0
  have hc1 := hcs (.ne (.var "m") (.int (-1))) (by simp [rubi537r21Nondeg])
  simp [Cond.Holds, Defined, eval] at hc1
  have hc2 := hcs (.ne (.app2 .mul (.var "c") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi537r21Nondeg])
  simp [Cond.Holds, Defined, eval] at hc2
  try simp only [hem] at hc0 hc1 hc2
  refine ⟨?_, ?_, ?_⟩
  · simp [Calc.real, droot, Real.sqrt_eq_zero', eval, Ok, Expr.varList, hm1, h2, hc2, hem, hqm2]
    rcases lt_or_ge km 0 with hsm | hsm <;> ((try have : km + -2 < 0 := by omega); (try have : -2 ≤ km := by omega); (try have : ¬ km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : -1 ≤ km := by omega); (try have : ¬ km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega)) <;> simp_all
  · simp [droot, Real.sqrt_eq_zero', Defined, eval, hm1, h2, hc2, hem, hqm2]
    rcases lt_or_ge km 0 with hsm | hsm <;> ((try have : km + -2 < 0 := by omega); (try have : -2 ≤ km := by omega); (try have : ¬ km < -2 := by omega); (try have : km + -1 < 0 := by omega); (try have : -1 ≤ km := by omega); (try have : ¬ km < -1 := by omega); (try have : km + 0 < 0 := by omega); (try have : 0 ≤ km + 0 := by omega); (try have : 0 ≤ km := by omega); (try have : km < 0 := by omega); (try have : ¬ km < 0 := by omega); (try have : ¬ km + 0 < 0 := by omega); (try have : 0 ≤ km + 1 := by omega); (try have : km < 1 := by omega); (try have : ¬ km + 1 < 0 := by omega); (try have : 0 ≤ km + 2 := by omega); (try have : km < 2 := by omega); (try have : ¬ km + 2 < 0 := by omega)) <;> simp_all
  · simp [droot, rubi537r21Nondeg, eval, d, hm1, h2, hm11, hn21, hem, hqm2, Interp.toInt?_cast]
    try casesm* _ ∧ _
    field_simp
    grind

end OSR.IntegrationRec308
