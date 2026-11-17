import OSR.IntegrationRec91
import OSR.IntegrationRec7

/-!
# Integration (RUBI): strengthened variants refuted by the pole probe, corrected (two bases)

RUBI 3.2.1 #2 and 3.2.3 #2, #4 and #7 are refuted as stated, and their first
strengthened variants were refuted by the pole probe at a vanishing exponent
(`n = 0`, or `p`, `q` or `r = 0`), where the logarithm's argument no longer
vanishes at the pole of a residual integrand.  With these exponents nonzero
they are proved over ℝ, with the real logarithm; the complex domain stays
unproved.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec98

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- rubi_3_2_1_r2 with NeQ[b, 0]; NeQ[n, 0] -/
def rubi321r2Nondeg : CRule where
  id := "integration.rubi_3_2_1_r2_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p:2"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .ln (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "n"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "mn")))))) (.var "p"))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.pow (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .ln (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "n"))) (.pow (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n")) (.int (-1))))))) (.var "p"))) (.pow (.var "b") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "B")) (.var "n")) (.var "p")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.pow (.var "b") (.int (-1)))) (.var "I1")))
  integrals := [("I1", .app2 .mul (.pow (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .ln (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "n"))) (.pow (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n")) (.int (-1))))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1))))]
  independent := ["a", "b", "c", "d", "e", "A", "B", "n", "mn", "p"]
  conditions := [.eq (.app2 .add (.var "n") (.var "mn")) (.int 0), .ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0), .int (.var "p"), .gt (.var "p") (.int 0),
    .ne (.var "b") (.int 0),
    .ne (.var "n") (.int 0)]
  priority := 9161
  description := "rubi_3_2_1_r2 with NeQ[b, 0]; NeQ[n, 0]"
  provenance := migrated "rubi:3 Logarithms/3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p:2" "3 Logarithms/3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p.m#2"

/-- ∫ log(e (f (a + b x)^p (c + d x)^q)^r)^s, when b ≠ 0 and p, q, r ≠ 0 -/
def logProductPowNondeg : CRule where
  id := "integration.log_product_power_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s:2"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "q"))) (.var "r")))) (.var "s"))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.pow (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "q"))) (.var "r")))) (.var "s"))) (.pow (.var "b") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "r")) (.var "s")) (.app2 .add (.var "p") (.var "q"))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "q") (.var "r")) (.var "s")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", .pow (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "q"))) (.var "r")))) (.app2 .add (.var "s") (.app2 .mul (.int (-1)) (.int 1)))), ("I2", .app2 .mul (.pow (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "q"))) (.var "r")))) (.app2 .add (.var "s") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1))))]
  independent := ["a", "b", "c", "d", "e", "f", "p", "q", "r", "s"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0), .ne (.app2 .add (.var "p") (.var "q")) (.int 0), .int (.var "s"), .gt (.var "s") (.int 0), .gt (.int 4) (.var "s"),
    .ne (.var "b") (.int 0),
    .ne (.var "p") (.int 0),
    .ne (.var "q") (.int 0),
    .ne (.var "r") (.int 0)]
  priority := 9162
  description := "∫ log(e (f (a + b x)^p (c + d x)^q)^r)^s, when b ≠ 0 and p, q, r ≠ 0"
  provenance := migrated "rubi:3 Logarithms/3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s:2" "3 Logarithms/3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s.m#2"

/-- ∫ (g + h x)^m log(e (f (a + b x)^p (c + d x)^q)^r), when h (m + 1) ≠ 0 and p, q, r ≠ 0 -/
def powLogProductNondeg : CRule where
  id := "integration.power_log_product_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s:4"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "m")) (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "q"))) (.var "r")))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "q"))) (.var "r"))))) (.pow (.app2 .mul (.var "h") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "p")) (.var "r")) (.pow (.app2 .mul (.var "h") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "q")) (.var "r")) (.pow (.app2 .mul (.var "h") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", .app2 .mul (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.int (-1)))), ("I2", .app2 .mul (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h", "m", "p", "q", "r"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0), .ne (.var "m") (.int (-1)),
    .ne (.app2 .mul (.var "h") (.app2 .add (.var "m") (.int 1))) (.int 0),
    .ne (.var "p") (.int 0),
    .ne (.var "q") (.int 0),
    .ne (.var "r") (.int 0)]
  priority := 9163
  description := "∫ (g + h x)^m log(e (f (a + b x)^p (c + d x)^q)^r), when h (m + 1) ≠ 0 and p, q, r ≠ 0"
  provenance := migrated "rubi:3 Logarithms/3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s:4" "3 Logarithms/3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s.m#4"

/-- ∫ (g + h x)^m log(e (f (a + b x)^p (c + d x)^q)^r)^s, when h (m + 1) ≠ 0 and p, q, r ≠ 0 -/
def powLogProductPowNondeg : CRule where
  id := "integration.power_log_product_power_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s:7"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "m")) (.pow (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "q"))) (.var "r")))) (.var "s")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "q"))) (.var "r")))) (.var "s"))) (.pow (.app2 .mul (.var "h") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "p")) (.var "r")) (.var "s")) (.pow (.app2 .mul (.var "h") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "q")) (.var "r")) (.var "s")) (.pow (.app2 .mul (.var "h") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", .app2 .mul (.app2 .mul (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "q"))) (.var "r")))) (.app2 .add (.var "s") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.int (-1)))), ("I2", .app2 .mul (.app2 .mul (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "q"))) (.var "r")))) (.app2 .add (.var "s") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h", "m", "p", "q", "r", "s"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0), .int (.var "s"), .gt (.var "s") (.int 0), .ne (.var "m") (.int (-1)),
    .ne (.app2 .mul (.var "h") (.app2 .add (.var "m") (.int 1))) (.int 0),
    .ne (.var "p") (.int 0),
    .ne (.var "q") (.int 0),
    .ne (.var "r") (.int 0)]
  priority := 9164
  description := "∫ (g + h x)^m log(e (f (a + b x)^p (c + d x)^q)^r)^s, when h (m + 1) ≠ 0 and p, q, r ≠ 0"
  provenance := migrated "rubi:3 Logarithms/3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s:7" "3 Logarithms/3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s.m#7"


/-! ## Proofs -/

section Proofs

private theorem zpow_succ_of (A : ℝ) (k : ℤ) (h : A ≠ 0 ∨ 0 ≤ k) : A ^ (k + 1) = A ^ k * A := by
  rcases h with h | h
  · exact zpow_add_one₀ h k
  · lift k to ℕ using h
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
      pow_succ]

/-- `d/dw log (e (f Aᵖ C^q)^r) = r (p b/A + q d/C)` for linear `A`, `C`, where the
argument is positive and `p, q, r ≠ 0`. -/
theorem hasDerivAt_log_prod (e f a b c d : ℝ) (p q r : ℤ) (t : ℝ) (hp : p ≠ 0) (hq : q ≠ 0)
    (hr : r ≠ 0) (h : 0 < e * (f * (a + b * t) ^ p * (c + d * t) ^ q) ^ r) :
    a + b * t ≠ 0 ∧ c + d * t ≠ 0 ∧
    HasDerivAt (fun w => Real.log (e * (f * (a + b * w) ^ p * (c + d * w) ^ q) ^ r))
      ((r : ℝ) * ((p : ℝ) * b * (a + b * t)⁻¹ + (q : ℝ) * d * (c + d * t)⁻¹)) t := by
  have hA : a + b * t ≠ 0 := by
    intro h0
    rw [h0, zero_zpow p hp, mul_zero, zero_mul, zero_zpow r hr, mul_zero] at h
    exact lt_irrefl 0 h
  have hC : c + d * t ≠ 0 := by
    intro h0
    rw [h0, zero_zpow q hq, mul_zero, zero_zpow r hr, mul_zero] at h
    exact lt_irrefl 0 h
  have hP : f * (a + b * t) ^ p * (c + d * t) ^ q ≠ 0 := by
    intro h0
    rw [h0, zero_zpow r hr, mul_zero] at h
    exact lt_irrefl 0 h
  have he : e ≠ 0 := by rintro rfl; simp at h
  have hf : f ≠ 0 := by rintro rfl; simp at hP
  refine ⟨hA, hC, ?_⟩
  have hAd : HasDerivAt (fun w => a + b * w) b t := by
    simpa using ((hasDerivAt_id' t).const_mul b).const_add a
  have hCd : HasDerivAt (fun w => c + d * w) d t := by
    simpa using ((hasDerivAt_id' t).const_mul d).const_add c
  have hAp := (hasDerivAt_zpow p _ (Or.inl hA)).comp t hAd
  have hCp := (hasDerivAt_zpow q _ (Or.inl hC)).comp t hCd
  have hPd := (hAp.const_mul f).mul hCp
  have hPr := (hasDerivAt_zpow r _ (Or.inl hP)).comp t hPd
  have hg := (hPr.const_mul e).log h.ne'
  convert hg using 1
  all_goals first
    | (funext w; simp [Function.comp_def]; done)
    | (simp only [Function.comp_def, Pi.mul_apply]
       rw [zpow_sub_one₀ hA, zpow_sub_one₀ hC, zpow_sub_one₀ hP]
       have hAp0 := zpow_ne_zero p hA
       have hCq0 := zpow_ne_zero q hC
       have hPr0 := zpow_ne_zero r hP
       generalize a + b * t = A at *
       generalize c + d * t = C at *
       field_simp
       try ring)

/-- `d/dw log (e Aⁿ C^m) = n b/A + m d/C` for linear `A`, `C`, where the argument is
positive and `n, m ≠ 0`. -/
theorem hasDerivAt_log_two (e a b c d : ℝ) (n m : ℤ) (t : ℝ) (hn : n ≠ 0) (hm : m ≠ 0)
    (h : 0 < e * (a + b * t) ^ n * (c + d * t) ^ m) :
    a + b * t ≠ 0 ∧ c + d * t ≠ 0 ∧
    HasDerivAt (fun w => Real.log (e * (a + b * w) ^ n * (c + d * w) ^ m))
      ((n : ℝ) * b * (a + b * t)⁻¹ + (m : ℝ) * d * (c + d * t)⁻¹) t := by
  have hA : a + b * t ≠ 0 := by
    intro h0
    rw [h0, zero_zpow n hn, mul_zero, zero_mul] at h
    exact lt_irrefl 0 h
  have hC : c + d * t ≠ 0 := by
    intro h0
    rw [h0, zero_zpow m hm, mul_zero] at h
    exact lt_irrefl 0 h
  have he : e ≠ 0 := by rintro rfl; simp at h
  refine ⟨hA, hC, ?_⟩
  have hAd : HasDerivAt (fun w => a + b * w) b t := by
    simpa using ((hasDerivAt_id' t).const_mul b).const_add a
  have hCd : HasDerivAt (fun w => c + d * w) d t := by
    simpa using ((hasDerivAt_id' t).const_mul d).const_add c
  have hAp := (hasDerivAt_zpow n _ (Or.inl hA)).comp t hAd
  have hCp := (hasDerivAt_zpow m _ (Or.inl hC)).comp t hCd
  have hg := ((hAp.const_mul e).mul hCp).log h.ne'
  convert hg using 1
  all_goals first
    | (funext w; simp [Function.comp_def]; done)
    | (simp only [Function.comp_def, Pi.mul_apply]
       rw [zpow_sub_one₀ hA, zpow_sub_one₀ hC]
       have hAp0 := zpow_ne_zero n hA
       have hCq0 := zpow_ne_zero m hC
       generalize a + b * t = A at *
       generalize c + d * t = C at *
       field_simp
       try ring)

theorem rubi321r2Nondeg_real : rubi321r2Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi321r2Nondeg.conditions rubi321r2Nondeg.body rubi321r2Nondeg.result rubi321r2Nondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi321r2Nondeg]); simpa [Cond.Holds, Defined, eval] using h
  have hN_n : env "n" ≠ 0 := by
    have h := hc (.ne (.var "n") (.int 0)) (by simp [rubi321r2Nondeg]); simpa [Cond.Holds, Defined, eval] using h
  have hnm := hc (.eq (.app2 .add (.var "n") (.var "mn")) (.int 0)) (by simp [rubi321r2Nondeg])
  simp [Cond.Holds, Defined, eval] at hnm
  rcases hk_n : intValue? (env "n") with _ | i
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi321r2Nondeg, Defined, eval, Interp.real, hm1, hk_n] at h
  have h_n : env "n" = (i : ℝ) := (intValue?_eq _ _).1 hk_n
  rcases hk_mn : intValue? (env "mn") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi321r2Nondeg, Defined, eval, Interp.real, hm1, hk_n, hk_mn] at h
  have h_mn : env "mn" = (j : ℝ) := (intValue?_eq _ _).1 hk_mn
  rcases hk_p : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi321r2Nondeg, Defined, eval, Interp.real, hm1, hk_n, hk_mn, hk_p] at h
  have h_p : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hk_p
  have hg_p := hc (.gt (.var "p") (.int 0)) (by simp [rubi321r2Nondeg])
  have hkpos : 0 < k := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg_p
    rw [h_p] at hg_p
    have h' : Interp.real.lt ((((0 : ℤ)) : ℚ) : ℝ) ((k : ℚ) : ℝ) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg_p
    exact_mod_cast (Interp.real_lt_rat _ _).1 h'
  have hi0 : i ≠ 0 := by intro h; apply hN_n; rw [h_n, h]; simp
  have hji : j = -i := by
    have : (j : ℝ) = -(i : ℝ) := by rw [← h_mn, ← h_n]; linear_combination hnm
    exact_mod_cast this
  subst hji
  have e1 : intValue? (env "p" + -1 * 1) = some (k - 1) := (intValue?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have e1' : intValue? (env "p" + -1) = some (k - 1) := (intValue?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have hk0 : ¬ k < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi321r2Nondeg.body →
      0 < (env "e" * (env "a" + env "b" * w) ^ i * ((env "c" + env "d" * w) ^ i)⁻¹) := by
    intro w h
    simp [rubi321r2Nondeg, Defined, eval, Interp.real, hm1, hk_n, hk_mn, hk_p, hk0, -Real.log_eq_zero] at h
    first | exact h.2 | exact h.1.2 | (trace_state; sorry)
  have hAC : ∀ w, 0 < (env "e" * (env "a" + env "b" * w) ^ i * ((env "c" + env "d" * w) ^ i)⁻¹) → (env "a" + env "b" * w) ≠ 0 ∧ (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    have h' : 0 < env "e" * (env "a" + env "b" * w) ^ i * (env "c" + env "d" * w) ^ (-i) := by rwa [zpow_neg]
    obtain ⟨h1, h2, -⟩ := hasDerivAt_log_two (env "e") (env "a") (env "b") (env "c") (env "d") i (-i) w hi0 (by omega) h'
    exact ⟨h1, h2⟩
  refine ⟨fun i' hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi321r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hpw := hD w hw
    obtain ⟨hA, hC⟩ := hAC w hpw
    simp [Defined, eval, Interp.real, hm1, hk_n, e1, e1', hk1, hA, hC, hpw, zpow_ne_zero i hA, zpow_ne_zero i hC, -Real.log_eq_zero]
  · filter_upwards [hF] with w hw
    have hpw := hD w hw
    obtain ⟨hA, hC⟩ := hAC w hpw
    simp [rubi321r2Nondeg, Defined, eval, Interp.real, recEnv, hm1, hk_n, hk_p, hk0, hA, hC, hpw, hb, zpow_ne_zero i hA, zpow_ne_zero i hC, -Real.log_eq_zero]
  · simp only [rubi321r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hpt := hD t hF.self_of_nhds
    obtain ⟨hA, hC⟩ := hAC t hpt
    have hpt' : 0 < env "e" * (env "a" + env "b" * t) ^ i * (env "c" + env "d" * t) ^ (-i) := by rwa [zpow_neg]
    obtain ⟨-, -, hL⟩ := hasDerivAt_log_two (env "e") (env "a") (env "b") (env "c") (env "d") i (-i) t hi0 (by omega) hpt'
    have hfe : (fun w => Real.log (env "e" * (env "a" + env "b" * w) ^ i * (env "c" + env "d" * w) ^ (-i))) = fun w => Real.log (env "e" * (env "a" + env "b" * w) ^ i * ((env "c" + env "d" * w) ^ i)⁻¹) := by
      funext w; rw [zpow_neg]
    rw [hfe] at hL
    have hΦ' : HasDerivAt (Φ "I1") ((env "A" + env "B" * Real.log (env "e" * (env "a" + env "b" * t) ^ i * ((env "c" + env "d" * t) ^ i)⁻¹)) ^ (k - 1) * (env "c" + env "d" * t)⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hm1, hk_n, e1, e1', -Real.log_eq_zero]
    have hEF : eval Interp.real (Function.update env "x" t) rubi321r2Nondeg.body = (env "A" + env "B" * Real.log (env "e" * (env "a" + env "b" * t) ^ i * ((env "c" + env "d" * t) ^ i)⁻¹)) ^ k := by
      simp [rubi321r2Nondeg, eval, Interp.real, hm1, hk_n, hk_mn, hk_p, -Real.log_eq_zero]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi321r2Nondeg.integrals.map (·.1)) Φ "x" w) rubi321r2Nondeg.result) =
        fun w => (env "a" + env "b" * w) * (env "A" + env "B" * Real.log (env "e" * (env "a" + env "b" * w) ^ i * ((env "c" + env "d" * w) ^ i)⁻¹)) ^ k * (env "b")⁻¹ +
          -1 * env "B" * env "n" * env "p" * (env "b" * env "c" + -1 * env "a" * env "d") * (env "b")⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi321r2Nondeg, eval, Interp.real, recEnv, hm1, hk_n, hk_p, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hAd : HasDerivAt (fun w => (env "a" + env "b" * w)) (env "b") t := by
      simpa using ((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")
    have hΛ := (hL.const_mul (env "B")).const_add (env "A")
    have hΛk := HasDerivAt.comp t (hasDerivAt_zpow k _ (Or.inr (by omega))) hΛ
    refine (((hAd.mul hΛk).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def]
    have hk' : (env "A" + env "B" * Real.log (env "e" * (env "a" + env "b" * t) ^ i * ((env "c" + env "d" * t) ^ i)⁻¹)) ^ k = (env "A" + env "B" * Real.log (env "e" * (env "a" + env "b" * t) ^ i * ((env "c" + env "d" * t) ^ i)⁻¹)) ^ (k - 1) * (env "A" + env "B" * Real.log (env "e" * (env "a" + env "b" * t) ^ i * ((env "c" + env "d" * t) ^ i)⁻¹)) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    rw [hk']
    simp only [h_n, h_p] at *
    generalize (env "A" + env "B" * Real.log (env "e" * (env "a" + env "b" * t) ^ i * ((env "c" + env "d" * t) ^ i)⁻¹)) ^ (k - 1) = Lk
    generalize (env "A" + env "B" * Real.log (env "e" * (env "a" + env "b" * t) ^ i * ((env "c" + env "d" * t) ^ i)⁻¹)) = Lm
    generalize hAe : (env "a" + env "b" * t) = A at hA ⊢
    generalize hCe : (env "c" + env "d" * t) = C at hC ⊢
    field_simp
    subst hAe hCe
    push_cast
    ring

theorem logProductPowNondeg_real : logProductPowNondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" logProductPowNondeg.conditions logProductPowNondeg.body logProductPowNondeg.result logProductPowNondeg.integrals
  intro env hc t hF
  have hN_b : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [logProductPowNondeg]); simpa [Cond.Holds, Defined, eval] using h
  have hN_p : env "p" ≠ 0 := by
    have h := hc (.ne (.var "p") (.int 0)) (by simp [logProductPowNondeg]); simpa [Cond.Holds, Defined, eval] using h
  have hN_q : env "q" ≠ 0 := by
    have h := hc (.ne (.var "q") (.int 0)) (by simp [logProductPowNondeg]); simpa [Cond.Holds, Defined, eval] using h
  have hN_r : env "r" ≠ 0 := by
    have h := hc (.ne (.var "r") (.int 0)) (by simp [logProductPowNondeg]); simpa [Cond.Holds, Defined, eval] using h
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso
    have h := hF.self_of_nhds
    simp [logProductPowNondeg, Defined, eval, Interp.real, hm1, hk_p] at h
  have h_p : env "p" = (kp : ℝ) := (intValue?_eq _ _).1 hk_p
  rcases hk_q : intValue? (env "q") with _ | kq
  · exfalso
    have h := hF.self_of_nhds
    simp [logProductPowNondeg, Defined, eval, Interp.real, hm1, hk_p, hk_q] at h
  have h_q : env "q" = (kq : ℝ) := (intValue?_eq _ _).1 hk_q
  rcases hk_r : intValue? (env "r") with _ | kr
  · exfalso
    have h := hF.self_of_nhds
    simp [logProductPowNondeg, Defined, eval, Interp.real, hm1, hk_p, hk_q, hk_r] at h
  have h_r : env "r" = (kr : ℝ) := (intValue?_eq _ _).1 hk_r
  rcases hk_s : intValue? (env "s") with _ | ks
  · exfalso
    have h := hF.self_of_nhds
    simp [logProductPowNondeg, Defined, eval, Interp.real, hm1, hk_p, hk_q, hk_r, hk_s] at h
  have h_s : env "s" = (ks : ℝ) := (intValue?_eq _ _).1 hk_s
  have hkp0 : kp ≠ 0 := by intro h; apply hN_p; rw [h_p, h]; simp
  have hkq0 : kq ≠ 0 := by intro h; apply hN_q; rw [h_q, h]; simp
  have hkr0 : kr ≠ 0 := by intro h; apply hN_r; rw [h_r, h]; simp
  have hpos : ∀ w, Defined Interp.real (Function.update env "x" w) logProductPowNondeg.body → 0 < (env "e" * (env "f" * (env "a" + env "b" * w) ^ kp * (env "c" + env "d" * w) ^ kq) ^ kr) := by
    intro w h
    simp [logProductPowNondeg, Defined, eval, Interp.real, hm1, hk_p, hk_q, hk_r, hk_s, -Real.log_eq_zero] at h
    first | exact h.1.2 | exact h.2 | exact h.2.2 | exact h.2.1.2 | exact h.2.1 | (trace_state; sorry)
  have hfac : ∀ w, 0 < (env "e" * (env "f" * (env "a" + env "b" * w) ^ kp * (env "c" + env "d" * w) ^ kq) ^ kr) → (env "a" + env "b" * w) ≠ 0 ∧ (env "c" + env "d" * w) ≠ 0 ∧ env "f" ≠ 0 := by
    intro w h
    obtain ⟨h1, h2, -⟩ := hasDerivAt_log_prod (env "e") (env "f") (env "a") (env "b") (env "c") (env "d") kp kq kr w hkp0 hkq0 hkr0 h
    refine ⟨h1, h2, ?_⟩
    rintro h0
    rw [h0, zero_mul, zero_mul, zero_zpow kr hkr0, mul_zero] at h
    exact lt_irrefl 0 h
  have hg_s := hc (.gt (.var "s") (.int 0)) (by simp [logProductPowNondeg])
  have hkspos : 0 < ks := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg_s
    rw [h_s] at hg_s
    have h' : Interp.real.lt ((((0 : ℤ)) : ℚ) : ℝ) ((ks : ℚ) : ℝ) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg_s
    exact_mod_cast (Interp.real_lt_rat _ _).1 h'
  have e1 : intValue? (env "s" + -1 * 1) = some (ks - 1) := (intValue?_eq _ _).2 (by rw [h_s]; push_cast; ring)
  have e1' : intValue? (env "s" + -1) = some (ks - 1) := (intValue?_eq _ _).2 (by rw [h_s]; push_cast; ring)
  have hks0 : ¬ ks < 0 := by omega
  have hks1 : ¬ ks - 1 < 0 := by omega
  refine ⟨fun i' hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [logProductPowNondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    · have hpw := hpos w hw
      obtain ⟨hA, hC, hf⟩ := hfac w hpw
      simp [Defined, eval, Interp.real, hm1, hk_p, hk_q, hk_r, hk_s, e1, e1', hks1, hA, hC, hf, hpw, zpow_ne_zero kp hA, zpow_ne_zero kq hC, -Real.log_eq_zero]
  · filter_upwards [hF] with w hw
    have hpw := hpos w hw
    obtain ⟨hA, hC, hf⟩ := hfac w hpw
    simp [logProductPowNondeg, Defined, eval, Interp.real, recEnv, hm1, hk_p, hk_q, hk_r, hk_s, hks0, hA, hC, hf, hpw, hN_b, zpow_ne_zero kp hA, zpow_ne_zero kq hC, -Real.log_eq_zero]
  · simp only [logProductPowNondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hpt := hpos t hF.self_of_nhds
    obtain ⟨hA, hC, hL⟩ := hasDerivAt_log_prod (env "e") (env "f") (env "a") (env "b") (env "c") (env "d") kp kq kr t hkp0 hkq0 hkr0 hpt
    have hΦ1' : HasDerivAt (Φ "I1") ((Real.log (env "e" * (env "f" * (env "a" + env "b" * t) ^ kp * (env "c" + env "d" * t) ^ kq) ^ kr)) ^ (ks - 1)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hm1, hk_p, hk_q, hk_r, hk_s, e1, e1', -Real.log_eq_zero]
    have hΦ2' : HasDerivAt (Φ "I2") ((Real.log (env "e" * (env "f" * (env "a" + env "b" * t) ^ kp * (env "c" + env "d" * t) ^ kq) ^ kr)) ^ (ks - 1) * (env "c" + env "d" * t)⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hm1, hk_p, hk_q, hk_r, hk_s, e1, e1', -Real.log_eq_zero]
    have hEF : eval Interp.real (Function.update env "x" t) logProductPowNondeg.body = (Real.log (env "e" * (env "f" * (env "a" + env "b" * t) ^ kp * (env "c" + env "d" * t) ^ kq) ^ kr)) ^ ks := by
      simp [logProductPowNondeg, eval, Interp.real, hm1, hk_p, hk_q, hk_r, hk_s, -Real.log_eq_zero]
    have hfun : (fun w => eval Interp.real (recEnv env (logProductPowNondeg.integrals.map (·.1)) Φ "x" w) logProductPowNondeg.result) =
        fun w => (((((env "a" + (env "b" * w)) * Real.log (env "e" * ((env "f" * (env "a" + (env "b" * w)) ^ kp) * (env "c" + (env "d" * w)) ^ kq) ^ kr) ^ ks) * (env "b")⁻¹) + (((((-1) * env "r") * env "s") * (env "p" + env "q")) * Φ "I1" w)) + (((((env "q" * env "r") * env "s") * ((env "b" * env "c") + (((-1) * env "a") * env "d"))) * (env "b")⁻¹) * Φ "I2" w)) := by
      funext w
      simp [logProductPowNondeg, eval, Interp.real, recEnv, hm1, hk_p, hk_q, hk_r, hk_s, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff, -Real.log_eq_zero]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hAd : HasDerivAt (fun w => env "a" + env "b" * w) (env "b") t := by
      simpa using ((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")
    have hLs := HasDerivAt.comp t (hasDerivAt_zpow ks _ (Or.inr (by omega))) hL
    refine ((((hAd.mul hLs).mul_const _).add (hΦ1'.const_mul _)).add (hΦ2'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def]
    have hk' : (Real.log (env "e" * (env "f" * (env "a" + env "b" * t) ^ kp * (env "c" + env "d" * t) ^ kq) ^ kr)) ^ ks = (Real.log (env "e" * (env "f" * (env "a" + env "b" * t) ^ kp * (env "c" + env "d" * t) ^ kq) ^ kr)) ^ (ks - 1) * (Real.log (env "e" * (env "f" * (env "a" + env "b" * t) ^ kp * (env "c" + env "d" * t) ^ kq) ^ kr)) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    rw [hk']
    simp only [h_p, h_q, h_r, h_s] at *
    generalize (Real.log (env "e" * (env "f" * (env "a" + env "b" * t) ^ kp * (env "c" + env "d" * t) ^ kq) ^ kr)) ^ (ks - 1) = Lk
    generalize Real.log (env "e" * (env "f" * (env "a" + env "b" * t) ^ kp * (env "c" + env "d" * t) ^ kq) ^ kr) = Lm
    generalize hAe : env "a" + env "b" * t = A at hA ⊢
    generalize hCe : env "c" + env "d" * t = C at hC ⊢
    field_simp
    subst hAe hCe
    push_cast
    ring

theorem powLogProductNondeg_real : powLogProductNondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" powLogProductNondeg.conditions powLogProductNondeg.body powLogProductNondeg.result powLogProductNondeg.integrals
  intro env hc t hF
  have hN_p : env "p" ≠ 0 := by
    have h := hc (.ne (.var "p") (.int 0)) (by simp [powLogProductNondeg]); simpa [Cond.Holds, Defined, eval] using h
  have hN_q : env "q" ≠ 0 := by
    have h := hc (.ne (.var "q") (.int 0)) (by simp [powLogProductNondeg]); simpa [Cond.Holds, Defined, eval] using h
  have hN_r : env "r" ≠ 0 := by
    have h := hc (.ne (.var "r") (.int 0)) (by simp [powLogProductNondeg]); simpa [Cond.Holds, Defined, eval] using h
  have hN_W := hc (.ne (.app2 .mul (.var "h") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [powLogProductNondeg])
  simp [Cond.Holds, Defined, eval] at hN_W
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso
    have h := hF.self_of_nhds
    simp [powLogProductNondeg, Defined, eval, Interp.real, hm1, hk_p] at h
  have h_p : env "p" = (kp : ℝ) := (intValue?_eq _ _).1 hk_p
  rcases hk_q : intValue? (env "q") with _ | kq
  · exfalso
    have h := hF.self_of_nhds
    simp [powLogProductNondeg, Defined, eval, Interp.real, hm1, hk_p, hk_q] at h
  have h_q : env "q" = (kq : ℝ) := (intValue?_eq _ _).1 hk_q
  rcases hk_r : intValue? (env "r") with _ | kr
  · exfalso
    have h := hF.self_of_nhds
    simp [powLogProductNondeg, Defined, eval, Interp.real, hm1, hk_p, hk_q, hk_r] at h
  have h_r : env "r" = (kr : ℝ) := (intValue?_eq _ _).1 hk_r
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso
    have h := hF.self_of_nhds
    simp [powLogProductNondeg, Defined, eval, Interp.real, hm1, hk_p, hk_q, hk_r, hk_m] at h
  have h_m : env "m" = (km : ℝ) := (intValue?_eq _ _).1 hk_m
  have hkp0 : kp ≠ 0 := by intro h; apply hN_p; rw [h_p, h]; simp
  have hkq0 : kq ≠ 0 := by intro h; apply hN_q; rw [h_q, h]; simp
  have hkr0 : kr ≠ 0 := by intro h; apply hN_r; rw [h_r, h]; simp
  have hpos : ∀ w, Defined Interp.real (Function.update env "x" w) powLogProductNondeg.body → 0 < (env "e" * (env "f" * (env "a" + env "b" * w) ^ kp * (env "c" + env "d" * w) ^ kq) ^ kr) := by
    intro w h
    simp [powLogProductNondeg, Defined, eval, Interp.real, hm1, hk_p, hk_q, hk_r, hk_m, -Real.log_eq_zero] at h
    first | exact h.1.2 | exact h.2 | exact h.2.2 | exact h.2.1.2 | exact h.2.1 | (trace_state; sorry)
  have hfac : ∀ w, 0 < (env "e" * (env "f" * (env "a" + env "b" * w) ^ kp * (env "c" + env "d" * w) ^ kq) ^ kr) → (env "a" + env "b" * w) ≠ 0 ∧ (env "c" + env "d" * w) ≠ 0 ∧ env "f" ≠ 0 := by
    intro w h
    obtain ⟨h1, h2, -⟩ := hasDerivAt_log_prod (env "e") (env "f") (env "a") (env "b") (env "c") (env "d") kp kq kr w hkp0 hkq0 hkr0 h
    refine ⟨h1, h2, ?_⟩
    rintro h0
    rw [h0, zero_mul, zero_mul, zero_zpow kr hkr0, mul_zero] at h
    exact lt_irrefl 0 h

  have e2 : intValue? (env "m" + 1) = some (km + 1) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have hGb : ∀ w, Defined Interp.real (Function.update env "x" w) powLogProductNondeg.body → (km < 0 → (env "g" + env "h" * w) ≠ 0) := by
    intro w h
    simp [powLogProductNondeg, Defined, eval, Interp.real, hm1, hk_p, hk_q, hk_r, hk_m, -Real.log_eq_zero] at h
    first | exact h.1 | exact h.1.1 | tauto
  refine ⟨fun i' hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [powLogProductNondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    · have hpw := hpos w hw
      obtain ⟨hA, hC, hf⟩ := hfac w hpw
      have hg := hGb w hw
      have hg' : km + 1 < 0 → (env "g" + env "h" * w) ≠ 0 := fun h => hg (by omega)
      simp [Defined, eval, Interp.real, hm1, hk_p, hk_q, hk_r, hk_m, e2, hA, hC, hf, hpw, zpow_ne_zero kp hA, zpow_ne_zero kq hC, -Real.log_eq_zero]
      first | done | exact hg' | tauto
  · filter_upwards [hF] with w hw
    have hpw := hpos w hw
    obtain ⟨hA, hC, hf⟩ := hfac w hpw
    have hg := hGb w hw
    have hg' : km + 1 < 0 → (env "g" + env "h" * w) ≠ 0 := fun h => hg (by omega)
    simp [powLogProductNondeg, Defined, eval, Interp.real, recEnv, hm1, hk_p, hk_q, hk_r, hk_m, e2, hA, hC, hf, hpw, hN_W, zpow_ne_zero kp hA, zpow_ne_zero kq hC, -Real.log_eq_zero]
    first | done | exact hg' | tauto
  · simp only [powLogProductNondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hpt := hpos t hF.self_of_nhds
    have hG0' := hGb t hF.self_of_nhds
    have hG0 : (env "g" + env "h" * t) ≠ 0 ∨ 0 ≤ km := by
      by_cases h : km < 0
      · exact Or.inl (hG0' h)
      · exact Or.inr (by omega)
    have hG1 : (env "g" + env "h" * t) ≠ 0 ∨ 0 ≤ km + 1 := by
      rcases hG0 with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    obtain ⟨hA, hC, hL⟩ := hasDerivAt_log_prod (env "e") (env "f") (env "a") (env "b") (env "c") (env "d") kp kq kr t hkp0 hkq0 hkr0 hpt
    have hΦ1' : HasDerivAt (Φ "I1") ((env "g" + env "h" * t) ^ (km + 1) * (env "a" + env "b" * t)⁻¹) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hm1, hk_p, hk_q, hk_r, hk_m, e2, -Real.log_eq_zero]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "g" + env "h" * t) ^ (km + 1) * (env "c" + env "d" * t)⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hm1, hk_p, hk_q, hk_r, hk_m, e2, -Real.log_eq_zero]
    have hEF : eval Interp.real (Function.update env "x" t) powLogProductNondeg.body = (env "g" + env "h" * t) ^ km * Real.log (env "e" * (env "f" * (env "a" + env "b" * t) ^ kp * (env "c" + env "d" * t) ^ kq) ^ kr) := by
      simp [powLogProductNondeg, eval, Interp.real, hm1, hk_p, hk_q, hk_r, hk_m, -Real.log_eq_zero]
    have hfun : (fun w => eval Interp.real (recEnv env (powLogProductNondeg.integrals.map (·.1)) Φ "x" w) powLogProductNondeg.result) =
        fun w => (((((env "g" + (env "h" * w)) ^ (km + 1) * Real.log (env "e" * ((env "f" * (env "a" + (env "b" * w)) ^ kp) * (env "c" + (env "d" * w)) ^ kq) ^ kr)) * (env "h" * (env "m" + 1))⁻¹) + ((((((-1) * env "b") * env "p") * env "r") * (env "h" * (env "m" + 1))⁻¹) * Φ "I1" w)) + ((((((-1) * env "d") * env "q") * env "r") * (env "h" * (env "m" + 1))⁻¹) * Φ "I2" w)) := by
      funext w
      simp [powLogProductNondeg, eval, Interp.real, recEnv, hm1, hk_p, hk_q, hk_r, hk_m, e2, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff, -Real.log_eq_zero]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hGd : HasDerivAt (fun w => (env "g" + env "h" * w)) (env "h") t := by
      simpa using ((hasDerivAt_id' t).const_mul (env "h")).const_add (env "g")
    have hGp := HasDerivAt.comp t (hasDerivAt_zpow (km + 1) _ hG1) hGd
    have hLs := hL
    refine ((((hGp.mul hLs).mul_const _).add (hΦ1'.const_mul _)).add (hΦ2'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    rw [zpow_succ_of _ _ hG0]
    simp only [h_p, h_q, h_r, h_m] at *
    try casesm* _ ∧ _
    generalize Real.log (env "e" * (env "f" * (env "a" + env "b" * t) ^ kp * (env "c" + env "d" * t) ^ kq) ^ kr) = Lm
    generalize (env "g" + env "h" * t) ^ km = Gk
    generalize hAe : env "a" + env "b" * t = A at hA ⊢
    generalize hCe : env "c" + env "d" * t = C at hC ⊢
    field_simp
    subst hAe hCe
    push_cast
    ring

theorem powLogProductPowNondeg_real : powLogProductPowNondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" powLogProductPowNondeg.conditions powLogProductPowNondeg.body powLogProductPowNondeg.result powLogProductPowNondeg.integrals
  intro env hc t hF
  have hN_p : env "p" ≠ 0 := by
    have h := hc (.ne (.var "p") (.int 0)) (by simp [powLogProductPowNondeg]); simpa [Cond.Holds, Defined, eval] using h
  have hN_q : env "q" ≠ 0 := by
    have h := hc (.ne (.var "q") (.int 0)) (by simp [powLogProductPowNondeg]); simpa [Cond.Holds, Defined, eval] using h
  have hN_r : env "r" ≠ 0 := by
    have h := hc (.ne (.var "r") (.int 0)) (by simp [powLogProductPowNondeg]); simpa [Cond.Holds, Defined, eval] using h
  have hN_W := hc (.ne (.app2 .mul (.var "h") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [powLogProductPowNondeg])
  simp [Cond.Holds, Defined, eval] at hN_W
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso
    have h := hF.self_of_nhds
    simp [powLogProductPowNondeg, Defined, eval, Interp.real, hm1, hk_p] at h
  have h_p : env "p" = (kp : ℝ) := (intValue?_eq _ _).1 hk_p
  rcases hk_q : intValue? (env "q") with _ | kq
  · exfalso
    have h := hF.self_of_nhds
    simp [powLogProductPowNondeg, Defined, eval, Interp.real, hm1, hk_p, hk_q] at h
  have h_q : env "q" = (kq : ℝ) := (intValue?_eq _ _).1 hk_q
  rcases hk_r : intValue? (env "r") with _ | kr
  · exfalso
    have h := hF.self_of_nhds
    simp [powLogProductPowNondeg, Defined, eval, Interp.real, hm1, hk_p, hk_q, hk_r] at h
  have h_r : env "r" = (kr : ℝ) := (intValue?_eq _ _).1 hk_r
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso
    have h := hF.self_of_nhds
    simp [powLogProductPowNondeg, Defined, eval, Interp.real, hm1, hk_p, hk_q, hk_r, hk_m] at h
  have h_m : env "m" = (km : ℝ) := (intValue?_eq _ _).1 hk_m
  rcases hk_s : intValue? (env "s") with _ | ks
  · exfalso
    have h := hF.self_of_nhds
    simp [powLogProductPowNondeg, Defined, eval, Interp.real, hm1, hk_p, hk_q, hk_r, hk_m, hk_s] at h
  have h_s : env "s" = (ks : ℝ) := (intValue?_eq _ _).1 hk_s
  have hkp0 : kp ≠ 0 := by intro h; apply hN_p; rw [h_p, h]; simp
  have hkq0 : kq ≠ 0 := by intro h; apply hN_q; rw [h_q, h]; simp
  have hkr0 : kr ≠ 0 := by intro h; apply hN_r; rw [h_r, h]; simp
  have hpos : ∀ w, Defined Interp.real (Function.update env "x" w) powLogProductPowNondeg.body → 0 < (env "e" * (env "f" * (env "a" + env "b" * w) ^ kp * (env "c" + env "d" * w) ^ kq) ^ kr) := by
    intro w h
    simp [powLogProductPowNondeg, Defined, eval, Interp.real, hm1, hk_p, hk_q, hk_r, hk_m, hk_s, -Real.log_eq_zero] at h
    first | exact h.1.2 | exact h.2 | exact h.2.2 | exact h.2.1.2 | exact h.2.1 | (trace_state; sorry)
  have hfac : ∀ w, 0 < (env "e" * (env "f" * (env "a" + env "b" * w) ^ kp * (env "c" + env "d" * w) ^ kq) ^ kr) → (env "a" + env "b" * w) ≠ 0 ∧ (env "c" + env "d" * w) ≠ 0 ∧ env "f" ≠ 0 := by
    intro w h
    obtain ⟨h1, h2, -⟩ := hasDerivAt_log_prod (env "e") (env "f") (env "a") (env "b") (env "c") (env "d") kp kq kr w hkp0 hkq0 hkr0 h
    refine ⟨h1, h2, ?_⟩
    rintro h0
    rw [h0, zero_mul, zero_mul, zero_zpow kr hkr0, mul_zero] at h
    exact lt_irrefl 0 h
  have hg_s := hc (.gt (.var "s") (.int 0)) (by simp [powLogProductPowNondeg])
  have hkspos : 0 < ks := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg_s
    rw [h_s] at hg_s
    have h' : Interp.real.lt ((((0 : ℤ)) : ℚ) : ℝ) ((ks : ℚ) : ℝ) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg_s
    exact_mod_cast (Interp.real_lt_rat _ _).1 h'
  have e1 : intValue? (env "s" + -1 * 1) = some (ks - 1) := (intValue?_eq _ _).2 (by rw [h_s]; push_cast; ring)
  have e1' : intValue? (env "s" + -1) = some (ks - 1) := (intValue?_eq _ _).2 (by rw [h_s]; push_cast; ring)
  have hks0 : ¬ ks < 0 := by omega
  have hks1 : ¬ ks - 1 < 0 := by omega
  have e2 : intValue? (env "m" + 1) = some (km + 1) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have hGb : ∀ w, Defined Interp.real (Function.update env "x" w) powLogProductPowNondeg.body → (km < 0 → (env "g" + env "h" * w) ≠ 0) := by
    intro w h
    simp [powLogProductPowNondeg, Defined, eval, Interp.real, hm1, hk_p, hk_q, hk_r, hk_m, hk_s, -Real.log_eq_zero] at h
    first | exact h.1 | exact h.1.1 | tauto
  refine ⟨fun i' hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [powLogProductPowNondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    · have hpw := hpos w hw
      obtain ⟨hA, hC, hf⟩ := hfac w hpw
      have hg := hGb w hw
      have hg' : km + 1 < 0 → (env "g" + env "h" * w) ≠ 0 := fun h => hg (by omega)
      simp [Defined, eval, Interp.real, hm1, hk_p, hk_q, hk_r, hk_m, hk_s, e2, e1, e1', hks0, hks1, hA, hC, hf, hpw, zpow_ne_zero kp hA, zpow_ne_zero kq hC, -Real.log_eq_zero]
      first | done | exact hg' | tauto
  · filter_upwards [hF] with w hw
    have hpw := hpos w hw
    obtain ⟨hA, hC, hf⟩ := hfac w hpw
    have hg := hGb w hw
    have hg' : km + 1 < 0 → (env "g" + env "h" * w) ≠ 0 := fun h => hg (by omega)
    simp [powLogProductPowNondeg, Defined, eval, Interp.real, recEnv, hm1, hk_p, hk_q, hk_r, hk_m, hk_s, e2, e1, e1', hks0, hks1, hA, hC, hf, hpw, hN_W, zpow_ne_zero kp hA, zpow_ne_zero kq hC, -Real.log_eq_zero]
    first | done | exact hg' | tauto
  · simp only [powLogProductPowNondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hpt := hpos t hF.self_of_nhds
    have hG0' := hGb t hF.self_of_nhds
    have hG0 : (env "g" + env "h" * t) ≠ 0 ∨ 0 ≤ km := by
      by_cases h : km < 0
      · exact Or.inl (hG0' h)
      · exact Or.inr (by omega)
    have hG1 : (env "g" + env "h" * t) ≠ 0 ∨ 0 ≤ km + 1 := by
      rcases hG0 with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    obtain ⟨hA, hC, hL⟩ := hasDerivAt_log_prod (env "e") (env "f") (env "a") (env "b") (env "c") (env "d") kp kq kr t hkp0 hkq0 hkr0 hpt
    have hΦ1' : HasDerivAt (Φ "I1") ((env "g" + env "h" * t) ^ (km + 1) * (Real.log (env "e" * (env "f" * (env "a" + env "b" * t) ^ kp * (env "c" + env "d" * t) ^ kq) ^ kr)) ^ (ks - 1) * (env "a" + env "b" * t)⁻¹) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hm1, hk_p, hk_q, hk_r, hk_m, hk_s, e2, e1, e1', hks0, hks1, -Real.log_eq_zero]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "g" + env "h" * t) ^ (km + 1) * (Real.log (env "e" * (env "f" * (env "a" + env "b" * t) ^ kp * (env "c" + env "d" * t) ^ kq) ^ kr)) ^ (ks - 1) * (env "c" + env "d" * t)⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hm1, hk_p, hk_q, hk_r, hk_m, hk_s, e2, e1, e1', hks0, hks1, -Real.log_eq_zero]
    have hEF : eval Interp.real (Function.update env "x" t) powLogProductPowNondeg.body = (env "g" + env "h" * t) ^ km * (Real.log (env "e" * (env "f" * (env "a" + env "b" * t) ^ kp * (env "c" + env "d" * t) ^ kq) ^ kr)) ^ ks := by
      simp [powLogProductPowNondeg, eval, Interp.real, hm1, hk_p, hk_q, hk_r, hk_m, hk_s, -Real.log_eq_zero]
    have hfun : (fun w => eval Interp.real (recEnv env (powLogProductPowNondeg.integrals.map (·.1)) Φ "x" w) powLogProductPowNondeg.result) =
        fun w => (((((env "g" + (env "h" * w)) ^ (km + 1) * Real.log (env "e" * ((env "f" * (env "a" + (env "b" * w)) ^ kp) * (env "c" + (env "d" * w)) ^ kq) ^ kr) ^ ks) * (env "h" * (env "m" + 1))⁻¹) + (((((((-1) * env "b") * env "p") * env "r") * env "s") * (env "h" * (env "m" + 1))⁻¹) * Φ "I1" w)) + (((((((-1) * env "d") * env "q") * env "r") * env "s") * (env "h" * (env "m" + 1))⁻¹) * Φ "I2" w)) := by
      funext w
      simp [powLogProductPowNondeg, eval, Interp.real, recEnv, hm1, hk_p, hk_q, hk_r, hk_m, hk_s, e2, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff, -Real.log_eq_zero]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hGd : HasDerivAt (fun w => (env "g" + env "h" * w)) (env "h") t := by
      simpa using ((hasDerivAt_id' t).const_mul (env "h")).const_add (env "g")
    have hGp := HasDerivAt.comp t (hasDerivAt_zpow (km + 1) _ hG1) hGd
    have hLs := HasDerivAt.comp t (hasDerivAt_zpow ks _ (Or.inr (by omega))) hL
    refine ((((hGp.mul hLs).mul_const _).add (hΦ1'.const_mul _)).add (hΦ2'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have hk' : (Real.log (env "e" * (env "f" * (env "a" + env "b" * t) ^ kp * (env "c" + env "d" * t) ^ kq) ^ kr)) ^ ks = (Real.log (env "e" * (env "f" * (env "a" + env "b" * t) ^ kp * (env "c" + env "d" * t) ^ kq) ^ kr)) ^ (ks - 1) * (Real.log (env "e" * (env "f" * (env "a" + env "b" * t) ^ kp * (env "c" + env "d" * t) ^ kq) ^ kr)) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    rw [hk']
    rw [zpow_succ_of _ _ hG0]
    simp only [h_p, h_q, h_r, h_m, h_s] at *
    try casesm* _ ∧ _
    generalize (Real.log (env "e" * (env "f" * (env "a" + env "b" * t) ^ kp * (env "c" + env "d" * t) ^ kq) ^ kr)) ^ (ks - 1) = Lk
    generalize Real.log (env "e" * (env "f" * (env "a" + env "b" * t) ^ kp * (env "c" + env "d" * t) ^ kq) ^ kr) = Lm
    generalize (env "g" + env "h" * t) ^ km = Gk
    generalize hAe : env "a" + env "b" * t = A at hA ⊢
    generalize hCe : env "c" + env "d" * t = C at hC ⊢
    field_simp
    subst hAe hCe
    push_cast
    ring

end Proofs

end OSR.IntegrationRec98
