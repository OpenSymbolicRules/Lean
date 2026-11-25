module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Real.Sqrt

/-! The pinned RUBI 4.5.2.1 source line 51 (OSR ID 47) uses cosines in the
residual integral. Specialize a=b=c=d=f=m=1, e=0, p=2 and n=1/2 over ℝ.
A candidate primitive of that residual, multiplied by the source prefactor,
cannot have the required derivative at π/2. -/

public section

namespace OSRTest.RubiCosecant

open Filter Topology

noncomputable def prefactor (x : ℝ) : ℝ :=
  Real.sqrt ((Real.sin x)⁻¹ ^ 2) / (Real.sin x)⁻¹

theorem wrong_residual (F : ℝ → ℝ)
    (hF : HasDerivAt F ((1 + Real.cos (Real.pi / 2)) * Real.cos (Real.pi / 2)) (Real.pi / 2)) :
    ¬ HasDerivAt (fun x => prefactor x * F x)
      ((1 + (Real.sin (Real.pi / 2))⁻¹) * Real.sqrt ((Real.sin (Real.pi / 2))⁻¹ ^ 2))
      (Real.pi / 2) := by
  have hsin : ∀ᶠ x : ℝ in 𝓝 (Real.pi / 2), 0 < Real.sin x :=
    (isOpen_lt continuous_const Real.continuous_sin).mem_nhds
      (show 0 < Real.sin (Real.pi / 2) by simp)
  have heq : (fun x => prefactor x * F x) =ᶠ[𝓝 (Real.pi / 2)] F := by
    filter_upwards [hsin] with x hx
    have hp : 0 < (Real.sin x)⁻¹ := inv_pos.mpr hx
    simp only [prefactor, Real.sqrt_sq_eq_abs, abs_of_pos hp, div_self hp.ne', one_mul]
  intro h
  have he := (h.congr_of_eventuallyEq heq.symm).unique hF
  norm_num [Real.sin_pi_div_two, Real.cos_pi_div_two] at he

end OSRTest.RubiCosecant
