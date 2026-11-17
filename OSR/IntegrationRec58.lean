import OSR.IntegrationNum1

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, tenth batch

Proofs of strengthened variants first distributed unproved
(`OSR.IntegrationNum1`, which keeps their definitions): the reductions
1.1.1.3 #13 (`p > 1`) and #14 (`p < -1`) of `(e + f x)^p / ((a + b x) (c + d x))`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec58

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem toInt?_neg_one (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem zpow_succ_of (A : 𝕜) (k : ℤ) (h : A ≠ 0 ∨ 0 ≤ k) : A ^ (k + 1) = A ^ k * A := by
  rcases h with h | h
  · exact zpow_add_one₀ h k
  · lift k to ℕ using h
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
      pow_succ]

private theorem toInt?_two (I : Interp 𝕜) : I.toInt? (2 : 𝕜) = some 2 :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem toInt?_four (I : Interp 𝕜) : I.toInt? (4 : 𝕜) = some 4 :=
  (I.toInt?_eq _ _).2 (by simp)








/-- **1.1.1.3 #13** with `b d (p - 1) ≠ 0` and `p > 1`: `f² (a + b x) (c + d x) + R(x) = b d (e + f x)²`. -/
theorem rubi1113r13Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi1113r13Nondeg.conditions rubi1113r13Nondeg.body rubi1113r13Nondeg.result rubi1113r13Nondeg.integrals := by
  intro env hc t hF
  have hW1 : (env "b" * env "d" * (env "p" + -1)) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.int 0)) (by simp [rubi1113r13Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW2 : (env "b" * env "d") ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "b") (.var "d")) (.int 0)) (by simp [rubi1113r13Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hg := hc (.gt (.var "p") (.int 1)) (by simp [rubi1113r13Nondeg])
  rcases hkp : I.toInt? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1113r13Nondeg, Defined, eval, hkp] at h
  have hp : env "p" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hk : 1 < k := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg
    rw [hp] at hg
    have h' : I.lt ((((1 : ℤ)) : ℚ) : 𝕜) ((k : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg
    exact_mod_cast (hlt _ _).1 h'
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1113r13Nondeg.body →
      (k < 0 → (env "e" + env "f" * w) ≠ 0) ∧ (env "a" + env "b" * w) ≠ 0 ∧ (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi1113r13Nondeg, Defined, eval, hkp, toInt?_neg_one] at h
    refine ⟨?_, ?_, ?_⟩ <;> tauto
  have ht := hD t hF.self_of_nhds
  have e1 : I.toInt? (env "p" + -1 * 1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have e1' : I.toInt? (env "p" + -1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have e2 : I.toInt? (env "p" + -1 * 2) = some (k - 2) := (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have e2' : I.toInt? (env "p" + -2) = some (k - 2) := (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1113r13Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1', h2', h3'⟩ := hD w hw
    simp [Defined, eval, e2, e2', toInt?_neg_one, toInt?_two, h2', h3']
    first | done | omega | (intro h; omega) | tauto
  · exact Eventually.of_forall fun w => by
      have hW1' := hW1
      simp only [ne_eq, mul_eq_zero, not_or] at hW1'
      obtain ⟨⟨hb, hd⟩, hp1⟩ := hW1'
      simp [rubi1113r13Nondeg, Defined, eval, recEnv, e1, e1', toInt?_neg_one, hb, hd, hp1]
      first | done | exact fun h => absurd h (by omega) | (intro h; omega) | tauto
  · simp only [rubi1113r13Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "b" * env "d" * env "e" ^ 2 + -1 * env "a" * env "c" * env "f" ^ 2 + env "f" * (2 * env "b" * env "d" * env "e" + -1 * env "b" * env "c" * env "f" + -1 * env "a" * env "d" * env "f") * t) * (env "e" + env "f" * t) ^ (k - 2) * ((env "a" + env "b" * t) * (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ using 1
      simp [eval, e2, e2', toInt?_neg_one, toInt?_two]
      try ring
    have hEF : eval I (Function.update env "x" t) rubi1113r13Nondeg.body = (env "e" + env "f" * t) ^ k * ((env "a" + env "b" * t) * (env "c" + env "d" * t))⁻¹ := by
      simp [rubi1113r13Nondeg, eval, hkp, toInt?_neg_one]
    set u1 := (env "b" * env "d" * (env "p" + -1))⁻¹ with hu1_def
    set u2 := (env "b" * env "d")⁻¹ with hu2_def
    have hU1 : (env "b" * env "d" * (env "p" + -1)) * u1 = 1 := by rw [hu1_def]; exact mul_inv_cancel₀ hW1
    have hU2 : (env "b" * env "d") * u2 = 1 := by rw [hu2_def]; exact mul_inv_cancel₀ hW2
    have hfun : (fun w => eval I (recEnv env (rubi1113r13Nondeg.integrals.map (·.1)) Φ "x" w) rubi1113r13Nondeg.result) =
        fun w => env "f" * (env "e" + env "f" * w) ^ (k - 1) * u1 + u2 * Φ "I1" w := by
      funext w
      simp [rubi1113r13Nondeg, eval, recEnv, e1, e1', toInt?_neg_one, hu1_def, hu2_def]
      try first | ring1 | simp | tauto
    rw [hfun, hEF]
    have hlin : HasDerivAt (fun w => (env "e" + env "f" * w)) (env "f") t := by
      have := ((hasDerivAt_id' t).const_mul (env "f")).const_add (env "e")
      convert this using 1 <;> first | ring | (funext w; simp only [id])
    refine ((((HasDerivAt.comp t (hasDerivAt_zpow (k - 1) _ (Or.inr (by omega))) hlin).const_mul (env "f")).mul_const u1).add (hΦ'.const_mul _)).congr_deriv ?_
    try simp only [Function.comp_def]
    rw [show k - 1 - 1 = k - 2 by ring]
    have hE2 : (env "e" + env "f" * t) ^ k = (env "e" + env "f" * t) ^ (k - 2) * (env "e" + env "f" * t) ^ 2 := by
      rw [← zpow_natCast, ← zpow_add' (Or.inr (Or.inl (by omega)))]
      congr 1; push_cast; ring
    rw [hE2]
    have hP : ((env "a" + env "b" * t) * (env "c" + env "d" * t)) * ((env "a" + env "b" * t) * (env "c" + env "d" * t))⁻¹ = 1 := mul_inv_cancel₀ (mul_ne_zero ht.2.1 ht.2.2)
    generalize (env "e" + env "f" * t) ^ (k - 2) = Z
    generalize ((env "a" + env "b" * t) * (env "c" + env "d" * t))⁻¹ = Pi at hP ⊢
    clear_value u1 u2
    simp only [hp] at hU1 ⊢
    push_cast
    linear_combination Z * ((-(env "f" ^ 2 * ((k : 𝕜) - 1) * u1)) * hP +
      (Pi * env "f" ^ 2 * ((env "a" + env "b" * t) * (env "c" + env "d" * t)) * u2) * hU1 +
      (Pi * (env "e" + env "f" * t) ^ 2 - Pi * env "f" ^ 2 * ((env "a" + env "b" * t) * (env "c" + env "d" * t)) * ((k : 𝕜) - 1) * u1) * hU2)

theorem rubi1113r13Nondeg_real : rubi1113r13Nondeg.Holds .real :=
  rubi1113r13Nondeg_holds Interp.real Interp.real_lt_rat

theorem rubi1113r13Nondeg_complex : rubi1113r13Nondeg.Holds .complex :=
  rubi1113r13Nondeg_holds Interp.complex Interp.complex_lt_rat

/-- **1.1.1.3 #14** with `(p + 1) (b e - a f) (d e - c f) ≠ 0` and `p < -1`: `f² (a + b x) (c + d x) + R(x) (e + f x) = (b e - a f) (d e - c f)`. -/
theorem rubi1113r14Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi1113r14Nondeg.conditions rubi1113r14Nondeg.body rubi1113r14Nondeg.result rubi1113r14Nondeg.integrals := by
  intro env hc t hF
  have hW1 : ((env "p" + 1) * (env "b" * env "e" + -1 * env "a" * env "f") * (env "d" * env "e" + -1 * env "c" * env "f")) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.app2 .add (.var "p") (.int 1)) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.app2 .add (.app2 .mul (.var "d") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f")))) (.int 0)) (by simp [rubi1113r14Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW2 : ((env "b" * env "e" + -1 * env "a" * env "f") * (env "d" * env "e" + -1 * env "c" * env "f")) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f"))) (.app2 .add (.app2 .mul (.var "d") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f")))) (.int 0)) (by simp [rubi1113r14Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hg := hc (.gt (.int (-1)) (.var "p")) (by simp [rubi1113r14Nondeg])
  rcases hkp : I.toInt? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1113r14Nondeg, Defined, eval, hkp] at h
  have hp : env "p" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hk : k < -1 := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg
    rw [hp] at hg
    have h' : I.lt ((k : ℚ) : 𝕜) ((((-1 : ℤ)) : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg
    exact_mod_cast (hlt _ _).1 h'
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1113r14Nondeg.body →
      (k < 0 → (env "e" + env "f" * w) ≠ 0) ∧ (env "a" + env "b" * w) ≠ 0 ∧ (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi1113r14Nondeg, Defined, eval, hkp, toInt?_neg_one] at h
    refine ⟨?_, ?_, ?_⟩ <;> tauto
  have ht := hD t hF.self_of_nhds
  have e1 : I.toInt? (env "p" + 1) = some (k + 1) := (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1113r14Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1', h2', h3'⟩ := hD w hw
    simp [Defined, eval, e1, toInt?_neg_one, h2', h3']
    first | done | exact fun h => h1' (by omega) | exact ⟨fun h => h1' (by omega), by simpa using hbe, by simpa using hde⟩ | tauto
  · filter_upwards [hF] with w hw
    obtain ⟨h1', h2', h3'⟩ := hD w hw
    have hW1' := hW1
    simp only [ne_eq, mul_eq_zero, not_or] at hW1'
    obtain ⟨⟨hp1, hbe⟩, hde⟩ := hW1'
    simp [rubi1113r14Nondeg, Defined, eval, recEnv, e1, toInt?_neg_one, hp1, hbe, hde]
    first | done | exact fun h => h1' (by omega) | exact ⟨fun h => h1' (by omega), by simpa using hbe, by simpa using hde⟩ | tauto
  · simp only [rubi1113r14Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "b" * env "d" * env "e" + -1 * env "b" * env "c" * env "f" + -1 * env "a" * env "d" * env "f" + -1 * env "b" * env "d" * env "f" * t) * (env "e" + env "f" * t) ^ (k + 1) * ((env "a" + env "b" * t) * (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ using 1
      simp [eval, e1, toInt?_neg_one]
      try ring
    have hEF : eval I (Function.update env "x" t) rubi1113r14Nondeg.body = (env "e" + env "f" * t) ^ k * ((env "a" + env "b" * t) * (env "c" + env "d" * t))⁻¹ := by
      simp [rubi1113r14Nondeg, eval, hkp, toInt?_neg_one]
    set u1 := ((env "p" + 1) * (env "b" * env "e" + -1 * env "a" * env "f") * (env "d" * env "e" + -1 * env "c" * env "f"))⁻¹ with hu1_def
    set u2 := ((env "b" * env "e" + -1 * env "a" * env "f") * (env "d" * env "e" + -1 * env "c" * env "f"))⁻¹ with hu2_def
    have hU1 : ((env "p" + 1) * (env "b" * env "e" + -1 * env "a" * env "f") * (env "d" * env "e" + -1 * env "c" * env "f")) * u1 = 1 := by rw [hu1_def]; exact mul_inv_cancel₀ hW1
    have hU2 : ((env "b" * env "e" + -1 * env "a" * env "f") * (env "d" * env "e" + -1 * env "c" * env "f")) * u2 = 1 := by rw [hu2_def]; exact mul_inv_cancel₀ hW2
    have hfun : (fun w => eval I (recEnv env (rubi1113r14Nondeg.integrals.map (·.1)) Φ "x" w) rubi1113r14Nondeg.result) =
        fun w => env "f" * (env "e" + env "f" * w) ^ (k + 1) * u1 + u2 * Φ "I1" w := by
      funext w
      simp [rubi1113r14Nondeg, eval, recEnv, e1, toInt?_neg_one, hu1_def, hu2_def]
      try first | ring1 | simp | tauto
    rw [hfun, hEF]
    have hlin : HasDerivAt (fun w => (env "e" + env "f" * w)) (env "f") t := by
      have := ((hasDerivAt_id' t).const_mul (env "f")).const_add (env "e")
      convert this using 1 <;> first | ring | (funext w; simp only [id])
    have hE0 : (env "e" + env "f" * t) ≠ 0 := ht.1 (by omega)
    refine ((((HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (Or.inl hE0)) hlin).const_mul (env "f")).mul_const u1).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    rw [zpow_succ_of _ _ (Or.inl hE0)]
    have hP : ((env "a" + env "b" * t) * (env "c" + env "d" * t)) * ((env "a" + env "b" * t) * (env "c" + env "d" * t))⁻¹ = 1 := mul_inv_cancel₀ (mul_ne_zero ht.2.1 ht.2.2)
    generalize (env "e" + env "f" * t) ^ k = Y
    generalize ((env "a" + env "b" * t) * (env "c" + env "d" * t))⁻¹ = Pi at hP ⊢
    clear_value u1 u2
    simp only [hp] at hU1 ⊢
    push_cast
    linear_combination Y * ((-(env "f" ^ 2 * ((k : 𝕜) + 1) * u1)) * hP +
      (Pi * env "f" ^ 2 * ((env "a" + env "b" * t) * (env "c" + env "d" * t)) * u2) * hU1 +
      (Pi - Pi * env "f" ^ 2 * ((env "a" + env "b" * t) * (env "c" + env "d" * t)) * ((k : 𝕜) + 1) * u1) * hU2)

theorem rubi1113r14Nondeg_real : rubi1113r14Nondeg.Holds .real :=
  rubi1113r14Nondeg_holds Interp.real Interp.real_lt_rat

theorem rubi1113r14Nondeg_complex : rubi1113r14Nondeg.Holds .complex :=
  rubi1113r14Nondeg_holds Interp.complex Interp.complex_lt_rat

end Proofs

end OSR.IntegrationRec58
