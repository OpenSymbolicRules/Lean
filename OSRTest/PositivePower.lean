import OSR.Calculus

/-! Exploratory checks for a positive-base real-power interpretation. -/

namespace OSRTest.PositivePower

open OSR

/-- The positive-base value agrees with the OpenMath exp/log characterization. -/
theorem positive_power_exp_log (x p : ℝ) (hx : 0 < x) :
    Real.rpow x p = Real.exp (p * Real.log x) := by
  simpa [mul_comm] using (Real.rpow_def_of_pos hx p)

/-- Mathlib's real power agrees in value with the existing integer fragment. -/
theorem integer_fragment_value (env : String → ℝ) (base exponent : Expr) (n : ℤ)
    (hn : intValue? (eval Interp.real env exponent) = some n) :
    eval Interp.real env (.pow base exponent) =
      Real.rpow (eval Interp.real env base) (eval Interp.real env exponent) := by
  have hv := (intValue?_eq _ _).1 hn
  change (match intValue? (eval Interp.real env exponent) with
    | some k => eval Interp.real env base ^ k
    | none => 0) = Real.rpow (eval Interp.real env base) (eval Interp.real env exponent)
  rw [hn]
  change eval Interp.real env base ^ n = Real.rpow (eval Interp.real env base) (eval Interp.real env exponent)
  rw [hv]
  exact (Real.rpow_intCast _ _).symm

/-- Positive bases preserve the current integer fragment's definedness. -/
theorem integer_fragment_defined (env : String → ℝ) (base exponent : Expr) (n : ℤ)
    (hb : Defined Interp.real env base) (he : Defined Interp.real env exponent)
    (hn : intValue? (eval Interp.real env exponent) = some n)
    (hpos : 0 < eval Interp.real env base) :
    Defined Interp.real env (.pow base exponent) := by
  exact ⟨hb, he, n, hn, fun _ => ne_of_gt hpos⟩

/-- A local primitive for real powers on the strictly positive half-line. -/
theorem positive_power_primitive (p t : ℝ) (ht : 0 < t) (hp : p ≠ -1) :
    HasDerivAt (fun x : ℝ => Real.rpow x (p + 1) / (p + 1)) (Real.rpow t p) t := by
  have hne : p + 1 ≠ 0 := by
    intro h
    apply hp
    linarith
  have h := (Real.hasDerivAt_rpow_const (x := t) (p := p + 1) (Or.inl ht.ne')).div_const (p + 1)
  convert h using 1
  have hp' : p + 1 - 1 = p := by ring
  rw [hp']
  field_simp
  rfl

-- Mathlib's total value at a pole must not become an OSR definedness claim.
example : Real.rpow 0 (-1) = 0 := by
  exact Real.zero_rpow (by norm_num)

example : ¬ Defined Interp.real (fun _ => 0) (.pow (.int 0) (.int (-1))) := by
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  simp [Defined, eval, Interp.real, hm1]

-- The present fragment excludes even positive-base non-integer powers.
example : ¬ Defined Interp.real (fun _ => 0)
    (.pow (.int 2) (.app2 .div (.int 1) (.int 2))) := by
  intro h
  obtain ⟨_, _, n, hn, _⟩ := h
  have hv : (1 / 2 : ℝ) = n := by
    have hvalue := (intValue?_eq _ _).1 hn
    simpa [eval] using hvalue
  have heven : (2 : ℤ) * n = 1 := by
    exact_mod_cast (show (2 : ℝ) * (n : ℝ) = 1 by linarith)
  omega

example : 0 < Real.rpow 2 (1 / 2) := by
  exact Real.rpow_pos_of_pos (by norm_num) _

-- Dropping p ≠ -1 would certify a false statement via totalized division.
example : ¬ HasDerivAt
    (fun x : ℝ => Real.rpow x ((-1 : ℝ) + 1) / ((-1 : ℝ) + 1))
    (Real.rpow 1 (-1)) 1 := by
  intro h
  have hz : HasDerivAt
      (fun x : ℝ => Real.rpow x ((-1 : ℝ) + 1) / ((-1 : ℝ) + 1)) 0 1 := by
    simpa using (hasDerivAt_const (1 : ℝ) (0 : ℝ))
  have heq := h.unique hz
  norm_num at heq

end OSRTest.PositivePower
