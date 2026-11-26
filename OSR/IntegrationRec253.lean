import OSR.IntegrationNum1

/-! # Strengthened trigonometric variants: double angles

Proofs over ℝ and ℂ of RUBI 4.7.4 #6, #7 and #31: when `b c = a d` and `d / b = 2`,
`sin(c + d x) = 2 sin(a + b x) cos(a + b x)`, so that `(e cos u)^m (f sin u)^n sin(2 u)^p` is
`2^p / (e^p f^p)` times `(e cos u)^(m + p) (f sin u)^(n + p)` (with the variants without the
cosine or the sine factor). -/

namespace OSR.IntegrationRec253

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem ivm1C : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)

/-! ## RUBI 4.7.4 #6 -/

theorem rubi474r6Nondeg_real : rubi474r6Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi474r6Nondeg.conditions rubi474r6Nondeg.body
    rubi474r6Nondeg.result rubi474r6Nondeg.integrals
  intro env hc t hF
  have hrel : env "b" * env "c" - env "a" * env "d" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul
      (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi474r6Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hdb : env "d" * (env "b")⁻¹ = 2 := by
    have h := hc (.eq (.app2 .mul (.var "d") (.pow (.var "b") (.int (-1)))) (.int 2))
      (by simp [rubi474r6Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, ivm1R] at h
    exact h.2
  have hb : env "b" ≠ 0 := by
    intro h0; rw [h0, inv_zero, mul_zero] at hdb; norm_num at hdb
  have hd : env "d" = 2 * env "b" := by field_simp at hdb; linear_combination hdb
  have hcc : env "c" = 2 * env "a" := by
    have : env "b" * (env "c" - 2 * env "a") = 0 := by rw [hd] at hrel; linear_combination hrel
    linear_combination (mul_eq_zero.mp this).resolve_left hb
  have hZ : ∀ w, Real.sin (env "c" + env "d" * w) = 2 * Real.sin (env "a" + env "b" * w) *
      Real.cos (env "a" + env "b" * w) := by
    intro w
    rw [show env "c" + env "d" * w = 2 * (env "a" + env "b" * w) by rw [hcc, hd]; ring,
        Real.sin_two_mul]
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi474r6Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkp : intValue? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi474r6Nondeg, Defined, eval, Interp.real, hkm, hkp] at h
  have hW0 : (l < 0 → env "e" ≠ 0) ∧ env "e" ^ l ≠ 0 := by
    have h := hc (.ne (.pow (.var "e") (.var "p")) (.int 0)) (by simp [rubi474r6Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hkp] at h
    tauto
  obtain ⟨hle, hel⟩ := hW0
  have emp : intValue? (env "m" + env "p") = some (m + l) :=
    (intValue?_eq _ _).2 (by
      rw [(intValue?_eq _ _).1 hkm, (intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi474r6Nondeg.body →
      (m < 0 → env "e" * Real.cos (env "a" + env "b" * w) ≠ 0) ∧
      (l < 0 → Real.sin (env "c" + env "d" * w) ≠ 0) := by
    intro w h
    simp [rubi474r6Nondeg, Defined, eval, Interp.real, hkm, hkp] at h
    simp only [ne_eq, mul_eq_zero, not_or]
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi474r6Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hCw, hZw⟩ := hD w hw
    have hc0 : l < 0 → Real.cos (env "a" + env "b" * w) ≠ 0 :=
      fun hl h0 => hZw hl (by rw [hZ w, h0]; ring)
    have hs0 : l < 0 → Real.sin (env "a" + env "b" * w) ≠ 0 :=
      fun hl h0 => hZw hl (by rw [hZ w, h0]; ring)
    have goal : (m + l < 0 → env "e" * Real.cos (env "a" + env "b" * w) ≠ 0) ∧
        (l < 0 → Real.sin (env "a" + env "b" * w) ≠ 0) := by
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rcases (show m < 0 ∨ l < 0 by omega) with h1 | h1
        · exact hCw h1
        · exact mul_ne_zero (hle h1) (hc0 h1)
      · exact hs0 h
    simp only [ne_eq, mul_eq_zero, not_or] at goal
    simp [Defined, eval, Interp.real, hkp, emp]
    tauto
  · filter_upwards with w
    simp [rubi474r6Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hkp] at *
    tauto
  · simp only [rubi474r6Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "e" * Real.cos (env "a" + env "b" * t)) ^ (m + l) *
        (Real.sin (env "a" + env "b" * t)) ^ l) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkp, emp]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi474r6Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi474r6Nondeg.result) = fun w => (2 : ℝ) ^ l * (env "e" ^ l)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi474r6Nondeg, eval, recEnv, Interp.real, ivm1R, hkp]
    have hEF : eval Interp.real (Function.update env "x" t) rubi474r6Nondeg.body =
        (env "e" * Real.cos (env "a" + env "b" * t)) ^ m *
        (Real.sin (env "c" + env "d" * t)) ^ l := by
      simp [rubi474r6Nondeg, eval, Interp.real, hkm, hkp]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    obtain ⟨hC0, hZ0⟩ := hD t hF.self_of_nhds
    have hc0t : l < 0 → Real.cos (env "a" + env "b" * t) ≠ 0 :=
        fun hl h0 => hZ0 hl (by rw [hZ t, h0]; ring)
    have hs0t : l < 0 → Real.sin (env "a" + env "b" * t) ≠ 0 :=
        fun hl h0 => hZ0 hl (by rw [hZ t, h0]; ring)
    have eC : (env "e" * Real.cos (env "a" + env "b" * t)) ^ (m + l) =
        (env "e" * Real.cos (env "a" + env "b" * t)) ^ m *
        (env "e" * Real.cos (env "a" + env "b" * t)) ^ l := by
      apply zpow_add'
      by_cases h0 : env "e" * Real.cos (env "a" + env "b" * t) = 0
      · right
        have hm : ¬ m < 0 := fun hm => hC0 hm h0
        have hl : ¬ l < 0 := fun hl => by
          have := hc0t hl
          exact this (by
            rcases mul_eq_zero.mp h0 with h | h
            · exact absurd h (hle hl)
            · exact h)
        omega
      · left; exact h0
    rw [eC, hZ t]
    simp only [mul_zpow]
    field_simp

theorem rubi474r6Nondeg_complex : rubi474r6Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi474r6Nondeg.conditions rubi474r6Nondeg.body
    rubi474r6Nondeg.result rubi474r6Nondeg.integrals
  intro env hc t hF
  have hrel : env "b" * env "c" - env "a" * env "d" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul
      (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi474r6Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hdb : env "d" * (env "b")⁻¹ = 2 := by
    have h := hc (.eq (.app2 .mul (.var "d") (.pow (.var "b") (.int (-1)))) (.int 2))
      (by simp [rubi474r6Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, ivm1C] at h
    exact h.2
  have hb : env "b" ≠ 0 := by
    intro h0; rw [h0, inv_zero, mul_zero] at hdb; norm_num at hdb
  have hd : env "d" = 2 * env "b" := by field_simp at hdb; linear_combination hdb
  have hcc : env "c" = 2 * env "a" := by
    have : env "b" * (env "c" - 2 * env "a") = 0 := by rw [hd] at hrel; linear_combination hrel
    linear_combination (mul_eq_zero.mp this).resolve_left hb
  have hZ : ∀ w, Complex.sin (env "c" + env "d" * w) = 2 * Complex.sin (env "a" + env "b" * w) *
      Complex.cos (env "a" + env "b" * w) := by
    intro w
    rw [show env "c" + env "d" * w = 2 * (env "a" + env "b" * w) by rw [hcc, hd]; ring,
        Complex.sin_two_mul]
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi474r6Nondeg, Defined, eval, Interp.complex, hkm] at h
  rcases hkp : intValue? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi474r6Nondeg, Defined, eval, Interp.complex, hkm, hkp] at h
  have hW0 : (l < 0 → env "e" ≠ 0) ∧ env "e" ^ l ≠ 0 := by
    have h := hc (.ne (.pow (.var "e") (.var "p")) (.int 0)) (by simp [rubi474r6Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, hkp] at h
    tauto
  obtain ⟨hle, hel⟩ := hW0
  have emp : intValue? (env "m" + env "p") = some (m + l) :=
    (intValue?_eq _ _).2 (by
      rw [(intValue?_eq _ _).1 hkm, (intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi474r6Nondeg.body →
      (m < 0 → env "e" * Complex.cos (env "a" + env "b" * w) ≠ 0) ∧
      (l < 0 → Complex.sin (env "c" + env "d" * w) ≠ 0) := by
    intro w h
    simp [rubi474r6Nondeg, Defined, eval, Interp.complex, hkm, hkp] at h
    simp only [ne_eq, mul_eq_zero, not_or]
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi474r6Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hCw, hZw⟩ := hD w hw
    have hc0 : l < 0 → Complex.cos (env "a" + env "b" * w) ≠ 0 :=
      fun hl h0 => hZw hl (by rw [hZ w, h0]; ring)
    have hs0 : l < 0 → Complex.sin (env "a" + env "b" * w) ≠ 0 :=
      fun hl h0 => hZw hl (by rw [hZ w, h0]; ring)
    have goal : (m + l < 0 → env "e" * Complex.cos (env "a" + env "b" * w) ≠ 0) ∧
        (l < 0 → Complex.sin (env "a" + env "b" * w) ≠ 0) := by
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rcases (show m < 0 ∨ l < 0 by omega) with h1 | h1
        · exact hCw h1
        · exact mul_ne_zero (hle h1) (hc0 h1)
      · exact hs0 h
    simp only [ne_eq, mul_eq_zero, not_or] at goal
    simp [Defined, eval, Interp.complex, hkp, emp]
    tauto
  · filter_upwards with w
    simp [rubi474r6Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hkp] at *
    tauto
  · simp only [rubi474r6Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "e" * Complex.cos (env "a" + env "b" * t)) ^ (m + l) *
        (Complex.sin (env "a" + env "b" * t)) ^ l) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkp, emp]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi474r6Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi474r6Nondeg.result) = fun w => (2 : ℂ) ^ l * (env "e" ^ l)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi474r6Nondeg, eval, recEnv, Interp.complex, ivm1C, hkp]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi474r6Nondeg.body =
        (env "e" * Complex.cos (env "a" + env "b" * t)) ^ m *
        (Complex.sin (env "c" + env "d" * t)) ^ l := by
      simp [rubi474r6Nondeg, eval, Interp.complex, hkm, hkp]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    obtain ⟨hC0, hZ0⟩ := hD t hF.self_of_nhds
    have hc0t : l < 0 → Complex.cos (env "a" + env "b" * t) ≠ 0 :=
        fun hl h0 => hZ0 hl (by rw [hZ t, h0]; ring)
    have hs0t : l < 0 → Complex.sin (env "a" + env "b" * t) ≠ 0 :=
        fun hl h0 => hZ0 hl (by rw [hZ t, h0]; ring)
    have eC : (env "e" * Complex.cos (env "a" + env "b" * t)) ^ (m + l) =
        (env "e" * Complex.cos (env "a" + env "b" * t)) ^ m *
        (env "e" * Complex.cos (env "a" + env "b" * t)) ^ l := by
      apply zpow_add'
      by_cases h0 : env "e" * Complex.cos (env "a" + env "b" * t) = 0
      · right
        have hm : ¬ m < 0 := fun hm => hC0 hm h0
        have hl : ¬ l < 0 := fun hl => by
          have := hc0t hl
          exact this (by
            rcases mul_eq_zero.mp h0 with h | h
            · exact absurd h (hle hl)
            · exact h)
        omega
      · left; exact h0
    rw [eC, hZ t]
    simp only [mul_zpow]
    field_simp

/-! ## RUBI 4.7.4 #7 -/

theorem rubi474r7Nondeg_real : rubi474r7Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi474r7Nondeg.conditions rubi474r7Nondeg.body
    rubi474r7Nondeg.result rubi474r7Nondeg.integrals
  intro env hc t hF
  have hrel : env "b" * env "c" - env "a" * env "d" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul
      (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi474r7Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hdb : env "d" * (env "b")⁻¹ = 2 := by
    have h := hc (.eq (.app2 .mul (.var "d") (.pow (.var "b") (.int (-1)))) (.int 2))
      (by simp [rubi474r7Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, ivm1R] at h
    exact h.2
  have hb : env "b" ≠ 0 := by
    intro h0; rw [h0, inv_zero, mul_zero] at hdb; norm_num at hdb
  have hd : env "d" = 2 * env "b" := by field_simp at hdb; linear_combination hdb
  have hcc : env "c" = 2 * env "a" := by
    have : env "b" * (env "c" - 2 * env "a") = 0 := by rw [hd] at hrel; linear_combination hrel
    linear_combination (mul_eq_zero.mp this).resolve_left hb
  have hZ : ∀ w, Real.sin (env "c" + env "d" * w) = 2 * Real.sin (env "a" + env "b" * w) *
      Real.cos (env "a" + env "b" * w) := by
    intro w
    rw [show env "c" + env "d" * w = 2 * (env "a" + env "b" * w) by rw [hcc, hd]; ring,
        Real.sin_two_mul]
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi474r7Nondeg, Defined, eval, Interp.real, hkn] at h
  rcases hkp : intValue? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi474r7Nondeg, Defined, eval, Interp.real, hkn, hkp] at h
  have hW0 : (l < 0 → env "f" ≠ 0) ∧ env "f" ^ l ≠ 0 := by
    have h := hc (.ne (.pow (.var "f") (.var "p")) (.int 0)) (by simp [rubi474r7Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hkp] at h
    tauto
  obtain ⟨hlf, hfl⟩ := hW0
  have enp : intValue? (env "n" + env "p") = some (k + l) :=
    (intValue?_eq _ _).2 (by
      rw [(intValue?_eq _ _).1 hkn, (intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi474r7Nondeg.body →
      (k < 0 → env "f" * Real.sin (env "a" + env "b" * w) ≠ 0) ∧
      (l < 0 → Real.sin (env "c" + env "d" * w) ≠ 0) := by
    intro w h
    simp [rubi474r7Nondeg, Defined, eval, Interp.real, hkn, hkp] at h
    simp only [ne_eq, mul_eq_zero, not_or]
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi474r7Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hSw, hZw⟩ := hD w hw
    have hc0 : l < 0 → Real.cos (env "a" + env "b" * w) ≠ 0 :=
      fun hl h0 => hZw hl (by rw [hZ w, h0]; ring)
    have hs0 : l < 0 → Real.sin (env "a" + env "b" * w) ≠ 0 :=
      fun hl h0 => hZw hl (by rw [hZ w, h0]; ring)
    have goal : (l < 0 → Real.cos (env "a" + env "b" * w) ≠ 0) ∧
        (k + l < 0 → env "f" * Real.sin (env "a" + env "b" * w) ≠ 0) := by
      refine ⟨fun h => ?_, fun h => ?_⟩
      · exact hc0 h
      · rcases (show k < 0 ∨ l < 0 by omega) with h1 | h1
        · exact hSw h1
        · exact mul_ne_zero (hlf h1) (hs0 h1)
    simp only [ne_eq, mul_eq_zero, not_or] at goal
    simp [Defined, eval, Interp.real, hkp, enp]
    tauto
  · filter_upwards with w
    simp [rubi474r7Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hkp] at *
    tauto
  · simp only [rubi474r7Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((Real.cos (env "a" + env "b" * t)) ^ l *
        (env "f" * Real.sin (env "a" + env "b" * t)) ^ (k + l)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkp, enp]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi474r7Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi474r7Nondeg.result) = fun w => (2 : ℝ) ^ l * (env "f" ^ l)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi474r7Nondeg, eval, recEnv, Interp.real, ivm1R, hkp]
    have hEF : eval Interp.real (Function.update env "x" t) rubi474r7Nondeg.body =
        (env "f" * Real.sin (env "a" + env "b" * t)) ^ k *
        (Real.sin (env "c" + env "d" * t)) ^ l := by
      simp [rubi474r7Nondeg, eval, Interp.real, hkn, hkp]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    obtain ⟨hS0, hZ0⟩ := hD t hF.self_of_nhds
    have hc0t : l < 0 → Real.cos (env "a" + env "b" * t) ≠ 0 :=
        fun hl h0 => hZ0 hl (by rw [hZ t, h0]; ring)
    have hs0t : l < 0 → Real.sin (env "a" + env "b" * t) ≠ 0 :=
        fun hl h0 => hZ0 hl (by rw [hZ t, h0]; ring)
    have eS : (env "f" * Real.sin (env "a" + env "b" * t)) ^ (k + l) =
        (env "f" * Real.sin (env "a" + env "b" * t)) ^ k *
        (env "f" * Real.sin (env "a" + env "b" * t)) ^ l := by
      apply zpow_add'
      by_cases h0 : env "f" * Real.sin (env "a" + env "b" * t) = 0
      · right
        have hm : ¬ k < 0 := fun hm => hS0 hm h0
        have hl : ¬ l < 0 := fun hl => by
          have := hs0t hl
          exact this (by
            rcases mul_eq_zero.mp h0 with h | h
            · exact absurd h (hlf hl)
            · exact h)
        omega
      · left; exact h0
    rw [eS, hZ t]
    simp only [mul_zpow]
    field_simp

theorem rubi474r7Nondeg_complex : rubi474r7Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi474r7Nondeg.conditions rubi474r7Nondeg.body
    rubi474r7Nondeg.result rubi474r7Nondeg.integrals
  intro env hc t hF
  have hrel : env "b" * env "c" - env "a" * env "d" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul
      (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi474r7Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hdb : env "d" * (env "b")⁻¹ = 2 := by
    have h := hc (.eq (.app2 .mul (.var "d") (.pow (.var "b") (.int (-1)))) (.int 2))
      (by simp [rubi474r7Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, ivm1C] at h
    exact h.2
  have hb : env "b" ≠ 0 := by
    intro h0; rw [h0, inv_zero, mul_zero] at hdb; norm_num at hdb
  have hd : env "d" = 2 * env "b" := by field_simp at hdb; linear_combination hdb
  have hcc : env "c" = 2 * env "a" := by
    have : env "b" * (env "c" - 2 * env "a") = 0 := by rw [hd] at hrel; linear_combination hrel
    linear_combination (mul_eq_zero.mp this).resolve_left hb
  have hZ : ∀ w, Complex.sin (env "c" + env "d" * w) = 2 * Complex.sin (env "a" + env "b" * w) *
      Complex.cos (env "a" + env "b" * w) := by
    intro w
    rw [show env "c" + env "d" * w = 2 * (env "a" + env "b" * w) by rw [hcc, hd]; ring,
        Complex.sin_two_mul]
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi474r7Nondeg, Defined, eval, Interp.complex, hkn] at h
  rcases hkp : intValue? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi474r7Nondeg, Defined, eval, Interp.complex, hkn, hkp] at h
  have hW0 : (l < 0 → env "f" ≠ 0) ∧ env "f" ^ l ≠ 0 := by
    have h := hc (.ne (.pow (.var "f") (.var "p")) (.int 0)) (by simp [rubi474r7Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, hkp] at h
    tauto
  obtain ⟨hlf, hfl⟩ := hW0
  have enp : intValue? (env "n" + env "p") = some (k + l) :=
    (intValue?_eq _ _).2 (by
      rw [(intValue?_eq _ _).1 hkn, (intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi474r7Nondeg.body →
      (k < 0 → env "f" * Complex.sin (env "a" + env "b" * w) ≠ 0) ∧
      (l < 0 → Complex.sin (env "c" + env "d" * w) ≠ 0) := by
    intro w h
    simp [rubi474r7Nondeg, Defined, eval, Interp.complex, hkn, hkp] at h
    simp only [ne_eq, mul_eq_zero, not_or]
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi474r7Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hSw, hZw⟩ := hD w hw
    have hc0 : l < 0 → Complex.cos (env "a" + env "b" * w) ≠ 0 :=
      fun hl h0 => hZw hl (by rw [hZ w, h0]; ring)
    have hs0 : l < 0 → Complex.sin (env "a" + env "b" * w) ≠ 0 :=
      fun hl h0 => hZw hl (by rw [hZ w, h0]; ring)
    have goal : (l < 0 → Complex.cos (env "a" + env "b" * w) ≠ 0) ∧
        (k + l < 0 → env "f" * Complex.sin (env "a" + env "b" * w) ≠ 0) := by
      refine ⟨fun h => ?_, fun h => ?_⟩
      · exact hc0 h
      · rcases (show k < 0 ∨ l < 0 by omega) with h1 | h1
        · exact hSw h1
        · exact mul_ne_zero (hlf h1) (hs0 h1)
    simp only [ne_eq, mul_eq_zero, not_or] at goal
    simp [Defined, eval, Interp.complex, hkp, enp]
    tauto
  · filter_upwards with w
    simp [rubi474r7Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hkp] at *
    tauto
  · simp only [rubi474r7Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((Complex.cos (env "a" + env "b" * t)) ^ l *
        (env "f" * Complex.sin (env "a" + env "b" * t)) ^ (k + l)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkp, enp]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi474r7Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi474r7Nondeg.result) = fun w => (2 : ℂ) ^ l * (env "f" ^ l)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi474r7Nondeg, eval, recEnv, Interp.complex, ivm1C, hkp]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi474r7Nondeg.body =
        (env "f" * Complex.sin (env "a" + env "b" * t)) ^ k *
        (Complex.sin (env "c" + env "d" * t)) ^ l := by
      simp [rubi474r7Nondeg, eval, Interp.complex, hkn, hkp]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    obtain ⟨hS0, hZ0⟩ := hD t hF.self_of_nhds
    have hc0t : l < 0 → Complex.cos (env "a" + env "b" * t) ≠ 0 :=
        fun hl h0 => hZ0 hl (by rw [hZ t, h0]; ring)
    have hs0t : l < 0 → Complex.sin (env "a" + env "b" * t) ≠ 0 :=
        fun hl h0 => hZ0 hl (by rw [hZ t, h0]; ring)
    have eS : (env "f" * Complex.sin (env "a" + env "b" * t)) ^ (k + l) =
        (env "f" * Complex.sin (env "a" + env "b" * t)) ^ k *
        (env "f" * Complex.sin (env "a" + env "b" * t)) ^ l := by
      apply zpow_add'
      by_cases h0 : env "f" * Complex.sin (env "a" + env "b" * t) = 0
      · right
        have hm : ¬ k < 0 := fun hm => hS0 hm h0
        have hl : ¬ l < 0 := fun hl => by
          have := hs0t hl
          exact this (by
            rcases mul_eq_zero.mp h0 with h | h
            · exact absurd h (hlf hl)
            · exact h)
        omega
      · left; exact h0
    rw [eS, hZ t]
    simp only [mul_zpow]
    field_simp

/-! ## RUBI 4.7.4 #31 -/

theorem rubi474r31Nondeg_real : rubi474r31Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi474r31Nondeg.conditions rubi474r31Nondeg.body
    rubi474r31Nondeg.result rubi474r31Nondeg.integrals
  intro env hc t hF
  have hrel : env "b" * env "c" - env "a" * env "d" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul
      (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi474r31Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hdb : env "d" * (env "b")⁻¹ = 2 := by
    have h := hc (.eq (.app2 .mul (.var "d") (.pow (.var "b") (.int (-1)))) (.int 2))
      (by simp [rubi474r31Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, ivm1R] at h
    exact h.2
  have hb : env "b" ≠ 0 := by
    intro h0; rw [h0, inv_zero, mul_zero] at hdb; norm_num at hdb
  have hd : env "d" = 2 * env "b" := by field_simp at hdb; linear_combination hdb
  have hcc : env "c" = 2 * env "a" := by
    have : env "b" * (env "c" - 2 * env "a") = 0 := by rw [hd] at hrel; linear_combination hrel
    linear_combination (mul_eq_zero.mp this).resolve_left hb
  have hZ : ∀ w, Real.sin (env "c" + env "d" * w) = 2 * Real.sin (env "a" + env "b" * w) *
      Real.cos (env "a" + env "b" * w) := by
    intro w
    rw [show env "c" + env "d" * w = 2 * (env "a" + env "b" * w) by rw [hcc, hd]; ring,
        Real.sin_two_mul]
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi474r31Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi474r31Nondeg, Defined, eval, Interp.real, hkm, hkn] at h
  rcases hkp : intValue? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi474r31Nondeg, Defined, eval, Interp.real, hkm, hkn, hkp] at h
  have hW0 : (l < 0 → env "e" ≠ 0) ∧ (l < 0 → env "f" ≠ 0) ∧ env "e" ^ l ≠ 0 ∧ env "f" ^ l ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.var "e") (.var "p")) (.pow (.var "f") (.var "p")))
      (.int 0)) (by simp [rubi474r31Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, hkp] at h
    tauto
  obtain ⟨hle, hlf, hel, hfl⟩ := hW0
  have emp : intValue? (env "m" + env "p") = some (m + l) :=
    (intValue?_eq _ _).2 (by
      rw [(intValue?_eq _ _).1 hkm, (intValue?_eq _ _).1 hkp]; push_cast; ring)
  have enp : intValue? (env "n" + env "p") = some (k + l) :=
    (intValue?_eq _ _).2 (by
      rw [(intValue?_eq _ _).1 hkn, (intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi474r31Nondeg.body →
      (m < 0 → env "e" * Real.cos (env "a" + env "b" * w) ≠ 0) ∧
      (k < 0 → env "f" * Real.sin (env "a" + env "b" * w) ≠ 0) ∧
      (l < 0 → Real.sin (env "c" + env "d" * w) ≠ 0) := by
    intro w h
    simp [rubi474r31Nondeg, Defined, eval, Interp.real, hkm, hkn, hkp] at h
    simp only [ne_eq, mul_eq_zero, not_or]
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi474r31Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hCw, hSw, hZw⟩ := hD w hw
    have hc0 : l < 0 → Real.cos (env "a" + env "b" * w) ≠ 0 :=
      fun hl h0 => hZw hl (by rw [hZ w, h0]; ring)
    have hs0 : l < 0 → Real.sin (env "a" + env "b" * w) ≠ 0 :=
      fun hl h0 => hZw hl (by rw [hZ w, h0]; ring)
    have goal : (m + l < 0 → env "e" * Real.cos (env "a" + env "b" * w) ≠ 0) ∧
        (k + l < 0 → env "f" * Real.sin (env "a" + env "b" * w) ≠ 0) := by
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rcases (show m < 0 ∨ l < 0 by omega) with h1 | h1
        · exact hCw h1
        · exact mul_ne_zero (hle h1) (hc0 h1)
      · rcases (show k < 0 ∨ l < 0 by omega) with h1 | h1
        · exact hSw h1
        · exact mul_ne_zero (hlf h1) (hs0 h1)
    simp only [ne_eq, mul_eq_zero, not_or] at goal
    simp [Defined, eval, Interp.real, emp, enp]
    tauto
  · filter_upwards with w
    simp [rubi474r31Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hkp] at *
    tauto
  · simp only [rubi474r31Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "e" * Real.cos (env "a" + env "b" * t)) ^ (m + l) *
        (env "f" * Real.sin (env "a" + env "b" * t)) ^ (k + l)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, emp, enp]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi474r31Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi474r31Nondeg.result) = fun w => (2 : ℝ) ^ l * (env "e" ^ l * env "f" ^ l)⁻¹ *
            Φ "I1" w := by
      funext w
      simp [rubi474r31Nondeg, eval, recEnv, Interp.real, ivm1R, hkp]
    have hEF : eval Interp.real (Function.update env "x" t) rubi474r31Nondeg.body =
        (env "e" * Real.cos (env "a" + env "b" * t)) ^ m *
        (env "f" * Real.sin (env "a" + env "b" * t)) ^ k *
        (Real.sin (env "c" + env "d" * t)) ^ l := by
      simp [rubi474r31Nondeg, eval, Interp.real, hkm, hkn, hkp]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    obtain ⟨hC0, hS0, hZ0⟩ := hD t hF.self_of_nhds
    have hc0t : l < 0 → Real.cos (env "a" + env "b" * t) ≠ 0 :=
        fun hl h0 => hZ0 hl (by rw [hZ t, h0]; ring)
    have hs0t : l < 0 → Real.sin (env "a" + env "b" * t) ≠ 0 :=
        fun hl h0 => hZ0 hl (by rw [hZ t, h0]; ring)
    have eC : (env "e" * Real.cos (env "a" + env "b" * t)) ^ (m + l) =
        (env "e" * Real.cos (env "a" + env "b" * t)) ^ m *
        (env "e" * Real.cos (env "a" + env "b" * t)) ^ l := by
      apply zpow_add'
      by_cases h0 : env "e" * Real.cos (env "a" + env "b" * t) = 0
      · right
        have hm : ¬ m < 0 := fun hm => hC0 hm h0
        have hl : ¬ l < 0 := fun hl => by
          have := hc0t hl
          exact this (by
            rcases mul_eq_zero.mp h0 with h | h
            · exact absurd h (hle hl)
            · exact h)
        omega
      · left; exact h0
    have eS : (env "f" * Real.sin (env "a" + env "b" * t)) ^ (k + l) =
        (env "f" * Real.sin (env "a" + env "b" * t)) ^ k *
        (env "f" * Real.sin (env "a" + env "b" * t)) ^ l := by
      apply zpow_add'
      by_cases h0 : env "f" * Real.sin (env "a" + env "b" * t) = 0
      · right
        have hm : ¬ k < 0 := fun hm => hS0 hm h0
        have hl : ¬ l < 0 := fun hl => by
          have := hs0t hl
          exact this (by
            rcases mul_eq_zero.mp h0 with h | h
            · exact absurd h (hlf hl)
            · exact h)
        omega
      · left; exact h0
    rw [eC, eS, hZ t]
    simp only [mul_zpow]
    field_simp

theorem rubi474r31Nondeg_complex : rubi474r31Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi474r31Nondeg.conditions rubi474r31Nondeg.body
    rubi474r31Nondeg.result rubi474r31Nondeg.integrals
  intro env hc t hF
  have hrel : env "b" * env "c" - env "a" * env "d" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul
      (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi474r31Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hdb : env "d" * (env "b")⁻¹ = 2 := by
    have h := hc (.eq (.app2 .mul (.var "d") (.pow (.var "b") (.int (-1)))) (.int 2))
      (by simp [rubi474r31Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, ivm1C] at h
    exact h.2
  have hb : env "b" ≠ 0 := by
    intro h0; rw [h0, inv_zero, mul_zero] at hdb; norm_num at hdb
  have hd : env "d" = 2 * env "b" := by field_simp at hdb; linear_combination hdb
  have hcc : env "c" = 2 * env "a" := by
    have : env "b" * (env "c" - 2 * env "a") = 0 := by rw [hd] at hrel; linear_combination hrel
    linear_combination (mul_eq_zero.mp this).resolve_left hb
  have hZ : ∀ w, Complex.sin (env "c" + env "d" * w) = 2 * Complex.sin (env "a" + env "b" * w) *
      Complex.cos (env "a" + env "b" * w) := by
    intro w
    rw [show env "c" + env "d" * w = 2 * (env "a" + env "b" * w) by rw [hcc, hd]; ring,
        Complex.sin_two_mul]
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi474r31Nondeg, Defined, eval, Interp.complex, hkm] at h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi474r31Nondeg, Defined, eval, Interp.complex, hkm, hkn] at h
  rcases hkp : intValue? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi474r31Nondeg, Defined, eval, Interp.complex, hkm, hkn, hkp] at h
  have hW0 : (l < 0 → env "e" ≠ 0) ∧ (l < 0 → env "f" ≠ 0) ∧ env "e" ^ l ≠ 0 ∧ env "f" ^ l ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.var "e") (.var "p")) (.pow (.var "f") (.var "p")))
      (.int 0)) (by simp [rubi474r31Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, hkp] at h
    tauto
  obtain ⟨hle, hlf, hel, hfl⟩ := hW0
  have emp : intValue? (env "m" + env "p") = some (m + l) :=
    (intValue?_eq _ _).2 (by
      rw [(intValue?_eq _ _).1 hkm, (intValue?_eq _ _).1 hkp]; push_cast; ring)
  have enp : intValue? (env "n" + env "p") = some (k + l) :=
    (intValue?_eq _ _).2 (by
      rw [(intValue?_eq _ _).1 hkn, (intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi474r31Nondeg.body →
      (m < 0 → env "e" * Complex.cos (env "a" + env "b" * w) ≠ 0) ∧
      (k < 0 → env "f" * Complex.sin (env "a" + env "b" * w) ≠ 0) ∧
      (l < 0 → Complex.sin (env "c" + env "d" * w) ≠ 0) := by
    intro w h
    simp [rubi474r31Nondeg, Defined, eval, Interp.complex, hkm, hkn, hkp] at h
    simp only [ne_eq, mul_eq_zero, not_or]
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi474r31Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hCw, hSw, hZw⟩ := hD w hw
    have hc0 : l < 0 → Complex.cos (env "a" + env "b" * w) ≠ 0 :=
      fun hl h0 => hZw hl (by rw [hZ w, h0]; ring)
    have hs0 : l < 0 → Complex.sin (env "a" + env "b" * w) ≠ 0 :=
      fun hl h0 => hZw hl (by rw [hZ w, h0]; ring)
    have goal : (m + l < 0 → env "e" * Complex.cos (env "a" + env "b" * w) ≠ 0) ∧
        (k + l < 0 → env "f" * Complex.sin (env "a" + env "b" * w) ≠ 0) := by
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rcases (show m < 0 ∨ l < 0 by omega) with h1 | h1
        · exact hCw h1
        · exact mul_ne_zero (hle h1) (hc0 h1)
      · rcases (show k < 0 ∨ l < 0 by omega) with h1 | h1
        · exact hSw h1
        · exact mul_ne_zero (hlf h1) (hs0 h1)
    simp only [ne_eq, mul_eq_zero, not_or] at goal
    simp [Defined, eval, Interp.complex, emp, enp]
    tauto
  · filter_upwards with w
    simp [rubi474r31Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hkp] at *
    tauto
  · simp only [rubi474r31Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "e" * Complex.cos (env "a" + env "b" * t)) ^ (m + l) *
        (env "f" * Complex.sin (env "a" + env "b" * t)) ^ (k + l)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, emp, enp]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi474r31Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi474r31Nondeg.result) = fun w => (2 : ℂ) ^ l * (env "e" ^ l * env "f" ^ l)⁻¹ *
            Φ "I1" w := by
      funext w
      simp [rubi474r31Nondeg, eval, recEnv, Interp.complex, ivm1C, hkp]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi474r31Nondeg.body =
        (env "e" * Complex.cos (env "a" + env "b" * t)) ^ m *
        (env "f" * Complex.sin (env "a" + env "b" * t)) ^ k *
        (Complex.sin (env "c" + env "d" * t)) ^ l := by
      simp [rubi474r31Nondeg, eval, Interp.complex, hkm, hkn, hkp]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    obtain ⟨hC0, hS0, hZ0⟩ := hD t hF.self_of_nhds
    have hc0t : l < 0 → Complex.cos (env "a" + env "b" * t) ≠ 0 :=
        fun hl h0 => hZ0 hl (by rw [hZ t, h0]; ring)
    have hs0t : l < 0 → Complex.sin (env "a" + env "b" * t) ≠ 0 :=
        fun hl h0 => hZ0 hl (by rw [hZ t, h0]; ring)
    have eC : (env "e" * Complex.cos (env "a" + env "b" * t)) ^ (m + l) =
        (env "e" * Complex.cos (env "a" + env "b" * t)) ^ m *
        (env "e" * Complex.cos (env "a" + env "b" * t)) ^ l := by
      apply zpow_add'
      by_cases h0 : env "e" * Complex.cos (env "a" + env "b" * t) = 0
      · right
        have hm : ¬ m < 0 := fun hm => hC0 hm h0
        have hl : ¬ l < 0 := fun hl => by
          have := hc0t hl
          exact this (by
            rcases mul_eq_zero.mp h0 with h | h
            · exact absurd h (hle hl)
            · exact h)
        omega
      · left; exact h0
    have eS : (env "f" * Complex.sin (env "a" + env "b" * t)) ^ (k + l) =
        (env "f" * Complex.sin (env "a" + env "b" * t)) ^ k *
        (env "f" * Complex.sin (env "a" + env "b" * t)) ^ l := by
      apply zpow_add'
      by_cases h0 : env "f" * Complex.sin (env "a" + env "b" * t) = 0
      · right
        have hm : ¬ k < 0 := fun hm => hS0 hm h0
        have hl : ¬ l < 0 := fun hl => by
          have := hs0t hl
          exact this (by
            rcases mul_eq_zero.mp h0 with h | h
            · exact absurd h (hlf hl)
            · exact h)
        omega
      · left; exact h0
    rw [eC, eS, hZ t]
    simp only [mul_zpow]
    field_simp

end OSR.IntegrationRec253
