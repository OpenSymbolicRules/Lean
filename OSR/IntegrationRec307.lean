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

namespace OSR.IntegrationRec307
open OSR OSR.Calculus OSR.IntegrationNum1 OSR.SymDeriv Filter Topology

private theorem zsplit {K : Type} [DivisionRing K] (X : K) (j : ℤ) (n : ℕ) (h : X ≠ 0 ∨ 0 ≤ j) :
    X ^ (j + n) = X ^ j * X ^ n := by
  rcases h with h | h
  · rw [zpow_add₀ h, zpow_natCast]
  · lift j to ℕ using h
    rw [show ((j : ℤ) + n) = ((j + n : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
      pow_add]

set_option maxHeartbeats 1000000 in
/-- RUBI rubi1117r12Nondeg: explicit term by the symbolic derivative. -/
theorem rubi1117r12Nondeg_real : rubi1117r12Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1117r12Nondeg.conditions rubi1117r12Nondeg.body rubi1117r12Nondeg.result rubi1117r12Nondeg.integrals
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
  refine antiderivRec_lin2 Calc.real _ ((rubi1117r12Nondeg.integrals[0]!).2) ((rubi1117r12Nondeg.integrals[1]!).2) (.app2 .mul (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "B"))) (.pow (.var "b") (.int (-1)))) (.app2 .mul (.var "B") (.pow (.var "b") (.int (-1)))) (by decide) (by decide) ?_
  intro env hcs t hF
  have h0 := hF.self_of_nhds
  simp [droot, Real.sqrt_eq_zero', rubi1117r12Nondeg, Defined, eval, hm1] at h0
  try casesm* _ ∧ _
  have hc0 := hcs (.ne (.var "b") (.int 0)) (by simp [rubi1117r12Nondeg])
  simp [Cond.Holds, Defined, eval] at hc0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc0]
  · simp [Defined, eval, hm1, hc0]
  · simp [Calc.real, droot, Real.sqrt_eq_zero', rubi1117r12Nondeg, eval, Ok, Expr.varList, hm1, h2]
    simp_all
  · simp [droot, Real.sqrt_eq_zero', rubi1117r12Nondeg, Defined, eval, hm1]
    simp_all
  · simp [Calc.real, droot, Real.sqrt_eq_zero', rubi1117r12Nondeg, eval, Ok, Expr.varList, hm1, h2]
    simp_all
  · simp [droot, Real.sqrt_eq_zero', rubi1117r12Nondeg, Defined, eval, hm1]
    simp_all
  · simp [droot, rubi1117r12Nondeg, eval, hm1]
    field_simp
    grind

set_option maxHeartbeats 1000000 in
/-- RUBI rubi1135r13Nondeg: explicit term by the symbolic derivative. -/
theorem rubi1135r13Nondeg_real : rubi1135r13Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1135r13Nondeg.conditions rubi1135r13Nondeg.body rubi1135r13Nondeg.result rubi1135r13Nondeg.integrals
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
  refine antiderivRec_lin2 Calc.real _ ((rubi1135r13Nondeg.integrals[0]!).2) ((rubi1135r13Nondeg.integrals[1]!).2) (.app2 .mul (.int 1) (.pow (.var "c") (.int (-1)))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.pow (.var "c") (.int (-1)))) (by decide) (by decide) ?_
  intro env hcs t hF
  have h0 := hF.self_of_nhds
  simp [droot, Real.sqrt_eq_zero', rubi1135r13Nondeg, Defined, eval, hm1, h2] at h0
  try casesm* _ ∧ _
  have hc0 := hcs (.ne (.app2 .add (.app2 .mul (.var "d") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f"))) (.int 0)) (by simp [rubi1135r13Nondeg])
  simp [Cond.Holds, Defined, eval] at hc0
  have hc1 := hcs (.ne (.var "c") (.int 0)) (by simp [rubi1135r13Nondeg])
  simp [Cond.Holds, Defined, eval] at hc1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc1]
  · simp [Defined, eval, hm1, hc1]
  · simp [Calc.real, droot, Real.sqrt_eq_zero', rubi1135r13Nondeg, eval, Ok, Expr.varList, hm1, h2]
    simp_all
  · simp [droot, Real.sqrt_eq_zero', rubi1135r13Nondeg, Defined, eval, hm1, h2]
    simp_all
  · simp [Calc.real, droot, Real.sqrt_eq_zero', rubi1135r13Nondeg, eval, Ok, Expr.varList, hm1, h2]
    simp_all
  · simp [droot, Real.sqrt_eq_zero', rubi1135r13Nondeg, Defined, eval, hm1, h2]
    simp_all
  · simp [droot, rubi1135r13Nondeg, eval, hm1, h2]
    field_simp
    grind

set_option maxHeartbeats 1000000 in
/-- RUBI rubi1216r26Nondeg: explicit term by the symbolic derivative. -/
theorem rubi1216r26Nondeg_real : rubi1216r26Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1216r26Nondeg.conditions rubi1216r26Nondeg.body rubi1216r26Nondeg.result rubi1216r26Nondeg.integrals
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
  refine antiderivRec_lin2 Calc.real _ ((rubi1216r26Nondeg.integrals[0]!).2) ((rubi1216r26Nondeg.integrals[1]!).2) (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "h") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "g")) (.var "f")))) (.pow (.app2 .mul (.int 2) (.var "f")) (.int (-1)))) (.app2 .mul (.var "h") (.pow (.app2 .mul (.int 2) (.var "f")) (.int (-1)))) (by decide) (by decide) ?_
  intro env hcs t hF
  have h0 := hF.self_of_nhds
  simp [droot, Real.sqrt_eq_zero', rubi1216r26Nondeg, Defined, eval, hm1, h2] at h0
  try casesm* _ ∧ _
  have hc0 := hcs (.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)) (by simp [rubi1216r26Nondeg])
  simp [Cond.Holds, Defined, eval, h2] at hc0
  have hc1 := hcs (.ne (.app2 .add (.pow (.var "e") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "d")) (.var "f"))) (.int 0)) (by simp [rubi1216r26Nondeg])
  simp [Cond.Holds, Defined, eval, h2] at hc1
  have hc2 := hcs (.eq (.app2 .add (.app2 .mul (.var "c") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "f"))) (.int 0)) (by simp [rubi1216r26Nondeg])
  simp [Cond.Holds, Defined, eval] at hc2
  have hc3 := hcs (.ne (.app2 .add (.app2 .mul (.var "h") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "g")) (.var "f"))) (.int 0)) (by simp [rubi1216r26Nondeg])
  simp [Cond.Holds, Defined, eval] at hc3
  have hc4 := hcs (.ne (.app2 .mul (.int 2) (.var "f")) (.int 0)) (by simp [rubi1216r26Nondeg])
  simp [Cond.Holds, Defined, eval] at hc4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc4]
  · simp [Defined, eval, hm1, hc4]
  · simp [Calc.real, droot, Real.sqrt_eq_zero', rubi1216r26Nondeg, eval, Ok, Expr.varList, hm1, h2]
    simp_all
  · simp [droot, Real.sqrt_eq_zero', rubi1216r26Nondeg, Defined, eval, hm1, h2]
    simp_all
  · simp [Calc.real, droot, Real.sqrt_eq_zero', rubi1216r26Nondeg, eval, Ok, Expr.varList, hm1, h2]
    simp_all
  · simp [droot, Real.sqrt_eq_zero', rubi1216r26Nondeg, Defined, eval, hm1, h2]
    simp_all
  · simp [droot, rubi1216r26Nondeg, eval, hm1, h2]
    field_simp
    ring1

set_option maxHeartbeats 1000000 in
/-- RUBI rubi1216r29Nondeg: explicit term by the symbolic derivative. -/
theorem rubi1216r29Nondeg_real : rubi1216r29Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1216r29Nondeg.conditions rubi1216r29Nondeg.body rubi1216r29Nondeg.result rubi1216r29Nondeg.integrals
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
  refine antiderivRec_lin2 Calc.real _ ((rubi1216r29Nondeg.integrals[0]!).2) ((rubi1216r29Nondeg.integrals[1]!).2) (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "h")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "g")) (.var "e")))) (.pow (.var "e") (.int (-1)))) (.app2 .mul (.var "h") (.pow (.var "e") (.int (-1)))) (by decide) (by decide) ?_
  intro env hcs t hF
  have h0 := hF.self_of_nhds
  simp [droot, Real.sqrt_eq_zero', rubi1216r29Nondeg, Defined, eval, hm1, h2] at h0
  try casesm* _ ∧ _
  have hc0 := hcs (.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)) (by simp [rubi1216r29Nondeg])
  simp [Cond.Holds, Defined, eval, h2] at hc0
  have hc1 := hcs (.ne (.app2 .add (.pow (.var "e") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "d")) (.var "f"))) (.int 0)) (by simp [rubi1216r29Nondeg])
  simp [Cond.Holds, Defined, eval, h2] at hc1
  have hc2 := hcs (.eq (.app2 .add (.app2 .mul (.var "b") (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "e"))) (.int 0)) (by simp [rubi1216r29Nondeg])
  simp [Cond.Holds, Defined, eval] at hc2
  have hc3 := hcs (.ne (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "h")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "g")) (.var "e"))) (.int 0)) (by simp [rubi1216r29Nondeg])
  simp [Cond.Holds, Defined, eval] at hc3
  have hc4 := hcs (.ne (.var "e") (.int 0)) (by simp [rubi1216r29Nondeg])
  simp [Cond.Holds, Defined, eval] at hc4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc4]
  · simp [Defined, eval, hm1, hc4]
  · simp [Calc.real, droot, Real.sqrt_eq_zero', rubi1216r29Nondeg, eval, Ok, Expr.varList, hm1, h2]
    simp_all
  · simp [droot, Real.sqrt_eq_zero', rubi1216r29Nondeg, Defined, eval, hm1, h2]
    simp_all
  · simp [Calc.real, droot, Real.sqrt_eq_zero', rubi1216r29Nondeg, eval, Ok, Expr.varList, hm1, h2]
    simp_all
  · simp [droot, Real.sqrt_eq_zero', rubi1216r29Nondeg, Defined, eval, hm1, h2]
    simp_all
  · simp [droot, rubi1216r29Nondeg, eval, hm1, h2]
    field_simp
    ring1

set_option maxHeartbeats 1000000 in
/-- RUBI rubi133r27Nondeg: explicit term by the symbolic derivative. -/
theorem rubi133r27Nondeg_real : rubi133r27Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi133r27Nondeg.conditions rubi133r27Nondeg.body rubi133r27Nondeg.result rubi133r27Nondeg.integrals
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
  refine antiderivRec_lin2 Calc.real _ ((rubi133r27Nondeg.integrals[0]!).2) ((rubi133r27Nondeg.integrals[1]!).2) (.app2 .mul (.int 2) (.pow (.app2 .mul (.int 3) (.var "c")) (.int (-1)))) (.app2 .mul (.int 1) (.pow (.app2 .mul (.int 3) (.var "c")) (.int (-1)))) (by decide) (by decide) ?_
  intro env hcs t hF
  have h0 := hF.self_of_nhds
  simp [droot, Real.sqrt_eq_zero', rubi133r27Nondeg, Defined, eval, hm1] at h0
  try casesm* _ ∧ _
  have hc0 := hcs (.eq (.app2 .add (.app2 .mul (.var "b") (.pow (.var "c") (.int 3))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.pow (.var "d") (.int 3)))) (.int 0)) (by simp [rubi133r27Nondeg])
  simp [Cond.Holds, Defined, eval, hn3] at hc0
  have hc1 := hcs (.ne (.app2 .mul (.int 3) (.var "c")) (.int 0)) (by simp [rubi133r27Nondeg])
  simp [Cond.Holds, Defined, eval] at hc1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc1]
  · simp [Defined, eval, hm1, hc1]
  · simp [Calc.real, droot, Real.sqrt_eq_zero', rubi133r27Nondeg, eval, Ok, Expr.varList, hm1, h2]
    simp_all
  · simp [droot, Real.sqrt_eq_zero', rubi133r27Nondeg, Defined, eval, hm1]
    simp_all
  · simp [Calc.real, droot, Real.sqrt_eq_zero', rubi133r27Nondeg, eval, Ok, Expr.varList, hm1, h2]
    simp_all
  · simp [droot, Real.sqrt_eq_zero', rubi133r27Nondeg, Defined, eval, hm1]
    simp_all
  · simp [droot, rubi133r27Nondeg, eval, hm1, hn3]
    field_simp
    grind

set_option maxHeartbeats 1000000 in
/-- RUBI rubi4121r19Nondeg: explicit term by the symbolic derivative. -/
theorem rubi4121r19Nondeg_real : rubi4121r19Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4121r19Nondeg.conditions rubi4121r19Nondeg.body rubi4121r19Nondeg.result rubi4121r19Nondeg.integrals
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
  refine antiderivRec_lin2 Calc.real _ ((rubi4121r19Nondeg.integrals[0]!).2) ((rubi4121r19Nondeg.integrals[1]!).2) (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.pow (.var "b") (.int (-1)))) (.app2 .mul (.var "d") (.pow (.var "b") (.int (-1)))) (by decide) (by decide) ?_
  intro env hcs t hF
  have h0 := hF.self_of_nhds
  simp [droot, Real.sqrt_eq_zero', rubi4121r19Nondeg, Defined, eval, hm1] at h0
  try casesm* _ ∧ _
  have hc0 := hcs (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4121r19Nondeg])
  simp [Cond.Holds, Defined, eval] at hc0
  have hc1 := hcs (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4121r19Nondeg])
  simp [Cond.Holds, Defined, eval, h2] at hc1
  have hc2 := hcs (.ne (.var "b") (.int 0)) (by simp [rubi4121r19Nondeg])
  simp [Cond.Holds, Defined, eval] at hc2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc2]
  · simp [Defined, eval, hm1, hc2]
  · simp [Calc.real, droot, Real.sqrt_eq_zero', rubi4121r19Nondeg, eval, Ok, Expr.varList, hm1, h2]
    assumption
  · simp [droot, Real.sqrt_eq_zero', rubi4121r19Nondeg, Defined, eval, hm1]
    simp_all
  · simp [Calc.real, rubi4121r19Nondeg, eval, Ok, Expr.varList, h2]
    assumption
  · simp [rubi4121r19Nondeg, Defined, eval]
    assumption
  · simp [droot, rubi4121r19Nondeg, eval, hm1]
    field_simp
    grind

set_option maxHeartbeats 1000000 in
/-- RUBI rubi4123r14Nondeg: explicit term by the symbolic derivative. -/
theorem rubi4123r14Nondeg_real : rubi4123r14Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4123r14Nondeg.conditions rubi4123r14Nondeg.body rubi4123r14Nondeg.result rubi4123r14Nondeg.integrals
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
  refine antiderivRec_lin2 Calc.real _ ((rubi4123r14Nondeg.integrals[0]!).2) ((rubi4123r14Nondeg.integrals[1]!).2) (.app2 .mul (.int 1) (.pow (.var "c") (.int (-1)))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.pow (.var "c") (.int (-1)))) (by decide) (by decide) ?_
  intro env hcs t hF
  have h0 := hF.self_of_nhds
  simp [droot, Real.sqrt_eq_zero', rubi4123r14Nondeg, Defined, eval, hm1] at h0
  try casesm* _ ∧ _
  have hc0 := hcs (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4123r14Nondeg])
  simp [Cond.Holds, Defined, eval] at hc0
  have hc1 := hcs (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4123r14Nondeg])
  simp [Cond.Holds, Defined, eval, h2] at hc1
  have hc2 := hcs (.ne (.var "c") (.int 0)) (by simp [rubi4123r14Nondeg])
  simp [Cond.Holds, Defined, eval] at hc2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc2]
  · simp [Defined, eval, hm1, hc2]
  · simp [Calc.real, droot, Real.sqrt_eq_zero', rubi4123r14Nondeg, eval, Ok, Expr.varList, hm1, h2]
    simp_all
  · simp [droot, Real.sqrt_eq_zero', rubi4123r14Nondeg, Defined, eval, hm1]
    simp_all
  · simp [Calc.real, droot, Real.sqrt_eq_zero', rubi4123r14Nondeg, eval, Ok, Expr.varList, hm1, h2]
    simp_all
  · simp [droot, Real.sqrt_eq_zero', rubi4123r14Nondeg, Defined, eval, hm1]
    simp_all
  · simp [droot, rubi4123r14Nondeg, eval, hm1]
    field_simp
    ring1

set_option maxHeartbeats 1000000 in
/-- RUBI rubi416r34Nondeg: explicit term by the symbolic derivative. -/
theorem rubi416r34Nondeg_real : rubi416r34Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi416r34Nondeg.conditions rubi416r34Nondeg.body rubi416r34Nondeg.result rubi416r34Nondeg.integrals
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
  refine antiderivRec_lin2 Calc.real _ ((rubi416r34Nondeg.integrals[0]!).2) ((rubi416r34Nondeg.integrals[1]!).2) (.app2 .mul (.var "B") (.pow (.var "b") (.int (-1)))) (.app2 .mul (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "B"))) (.pow (.var "b") (.int (-1)))) (by decide) (by decide) ?_
  intro env hcs t hF
  have h0 := hF.self_of_nhds
  simp [droot, Real.sqrt_eq_zero', rubi416r34Nondeg, Defined, eval, hm1] at h0
  try casesm* _ ∧ _
  have hc0 := hcs (.eq (.app2 .add (.app2 .mul (.var "B") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "C"))) (.int 0)) (by simp [rubi416r34Nondeg])
  simp [Cond.Holds, Defined, eval] at hc0
  have hc1 := hcs (.ne (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "B"))) (.int 0)) (by simp [rubi416r34Nondeg])
  simp [Cond.Holds, Defined, eval] at hc1
  have hc2 := hcs (.ne (.var "b") (.int 0)) (by simp [rubi416r34Nondeg])
  simp [Cond.Holds, Defined, eval] at hc2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Defined, eval, hm1, hc2]
  · simp [Defined, eval, hm1, hc2]
  · simp [Calc.real, rubi416r34Nondeg, eval, Ok, Expr.varList, h2]
    assumption
  · simp [rubi416r34Nondeg, Defined, eval]
    assumption
  · simp [Calc.real, droot, Real.sqrt_eq_zero', rubi416r34Nondeg, eval, Ok, Expr.varList, hm1, h2]
    assumption
  · simp [droot, Real.sqrt_eq_zero', rubi416r34Nondeg, Defined, eval, hm1]
    simp_all
  · simp [droot, rubi416r34Nondeg, eval, hm1]
    field_simp
    grind

end OSR.IntegrationRec307
