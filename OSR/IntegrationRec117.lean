import OSR.IntegrationRec91

/-!
# Integration (RUBI): strengthened variants of 2.3 (exponentials with a varying exponent)

OSR powers have integer exponents, so `F^(a + b (c + d x)ⁿ)` is defined on a
neighbourhood only where its exponent is a locally constant integer.  Over ℝ
and ℂ an integer-valued function continuous at `t` is constant near `t`, so
its derivative vanishes: this forces `b = 0`, and the rule holds with
`d ≠ 0` and `F > 0` (for `log F`).  Proved over ℝ and ℂ.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec117

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- rubi_2_3_r11 with NeQ[d, 0]; GtQ[F, 0] -/
def rubi23r11Nondeg : CRule where
  id := "integration.rubi_2_3_r11_nondegenerate"; legacyId := some "rubi:2 Exponentials/2.3 Miscellaneous exponentials:11"
  shape := .antiderivRec; x := "x"
  body := (.pow (.var "F") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.pow (.var "F") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n")))))) (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "n")) (.app1 .ln (.var "F"))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n")) (.pow (.var "F") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n")))))))]
  independent := ["F", "a", "b", "c", "d", "n"]
  conditions := [.int (.app2 .mul (.int 2) (.pow (.var "n") (.int (-1)))),
    .int (.var "n"),
    .gt (.int 0) (.var "n"),
    .ne (.var "d") (.int 0),
    .gt (.var "F") (.int 0)]
  priority := 9351
  description := "rubi_2_3_r11 with NeQ[d, 0]; GtQ[F, 0]"
  provenance := migrated "rubi:2 Exponentials/2.3 Miscellaneous exponentials:11" "2 Exponentials/2.3 Miscellaneous exponentials.m#11"

/-- rubi_2_3_r23 with NeQ[Multiply[Add[m, 1], Power[f, 2]], 0]; NeQ[Multiply[Power[f, 2], Add[m, 1]], 0]; GtQ[F, 0] -/
def rubi23r23Nondeg : CRule where
  id := "integration.rubi_2_3_r23_nondegenerate"; legacyId := some "rubi:2 Exponentials/2.3 Miscellaneous exponentials:23"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.var "F") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int 2))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "m") (.int 1)))) (.pow (.var "F") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int 2)))))) (.pow (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.pow (.var "f") (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "d")) (.app2 .add (.app2 .mul (.var "d") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f")))) (.app1 .ln (.var "F"))) (.pow (.app2 .mul (.pow (.var "f") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "b")) (.pow (.var "d") (.int 2))) (.app1 .ln (.var "F"))) (.pow (.app2 .mul (.pow (.var "f") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.var "F") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int 2))))))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "m") (.int 2))) (.pow (.var "F") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int 2)))))))]
  independent := ["F", "a", "b", "c", "d", "e", "f", "m"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "d") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f"))) (.int 0),
    .gt (.int (-1)) (.var "m"),
    .ne (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.pow (.var "f") (.int 2))) (.int 0),
    .ne (.app2 .mul (.pow (.var "f") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.int 0),
    .gt (.var "F") (.int 0)]
  priority := 9352
  description := "rubi_2_3_r23 with NeQ[Multiply[Add[m, 1], Power[f, 2]], 0]; NeQ[Multiply[Power[f, 2], Add[m, 1]], 0]; GtQ[F, 0]"
  provenance := migrated "rubi:2 Exponentials/2.3 Miscellaneous exponentials:23" "2 Exponentials/2.3 Miscellaneous exponentials.m#23"

/-- rubi_2_3_r24 with NeQ[Multiply[f, Add[m, 1]], 0]; GtQ[F, 0] -/
def rubi23r24Nondeg : CRule where
  id := "integration.rubi_2_3_r24_nondegenerate"; legacyId := some "rubi:2 Exponentials/2.3 Miscellaneous exponentials:24"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.var "F") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n"))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.var "F") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n")))))) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "n")) (.app1 .ln (.var "F"))) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.var "F") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n")))))))]
  independent := ["F", "a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "d") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f"))) (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 2),
    .gt (.int (-1)) (.var "m"),
    .ne (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int 0),
    .gt (.var "F") (.int 0)]
  priority := 9353
  description := "rubi_2_3_r24 with NeQ[Multiply[f, Add[m, 1]], 0]; GtQ[F, 0]"
  provenance := migrated "rubi:2 Exponentials/2.3 Miscellaneous exponentials:24" "2 Exponentials/2.3 Miscellaneous exponentials.m#24"

/-- rubi_2_3_r26 with NeQ[Multiply[f, Add[m, 1]], 0]; GtQ[F, 0] -/
def rubi23r26Nondeg : CRule where
  id := "integration.rubi_2_3_r26_nondegenerate"; legacyId := some "rubi:2 Exponentials/2.3 Miscellaneous exponentials:26"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.var "F") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.var "F") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1))))))) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app1 .ln (.var "F"))) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.var "F") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1))))))) (.pow (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int 2)) (.int (-1)))))]
  independent := ["F", "a", "b", "c", "d", "e", "f", "m"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "d") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f"))) (.int 0),
    .int (.var "m"),
    .gt (.int (-1)) (.var "m"),
    .ne (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int 0),
    .gt (.var "F") (.int 0)]
  priority := 9354
  description := "rubi_2_3_r26 with NeQ[Multiply[f, Add[m, 1]], 0]; GtQ[F, 0]"
  provenance := migrated "rubi:2 Exponentials/2.3 Miscellaneous exponentials:26" "2 Exponentials/2.3 Miscellaneous exponentials.m#26"

/-- rubi_2_3_r35 with NeQ[Multiply[h, Add[m, 1]], 0]; GtQ[F, 0] -/
def rubi23r35Nondeg : CRule where
  id := "integration.rubi_2_3_r35_nondegenerate"; legacyId := some "rubi:2 Exponentials/2.3 Miscellaneous exponentials:35"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "m")) (.pow (.var "F") (.app2 .add (.var "e") (.app2 .mul (.app2 .mul (.var "f") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.var "F") (.app2 .add (.var "e") (.app2 .mul (.app2 .mul (.var "f") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1))))))) (.pow (.app2 .mul (.var "h") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app1 .ln (.var "F"))) (.pow (.app2 .mul (.var "h") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.var "F") (.app2 .add (.var "e") (.app2 .mul (.app2 .mul (.var "f") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1))))))) (.pow (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int 2)) (.int (-1)))))]
  independent := ["F", "a", "b", "c", "d", "e", "f", "g", "h", "m"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.app2 .mul (.var "d") (.var "g")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "h"))) (.int 0),
    .int (.var "m"),
    .gt (.int (-1)) (.var "m"),
    .ne (.app2 .mul (.var "h") (.app2 .add (.var "m") (.int 1))) (.int 0),
    .gt (.var "F") (.int 0)]
  priority := 9355
  description := "rubi_2_3_r35 with NeQ[Multiply[h, Add[m, 1]], 0]; GtQ[F, 0]"
  provenance := migrated "rubi:2 Exponentials/2.3 Miscellaneous exponentials:35" "2 Exponentials/2.3 Miscellaneous exponentials.m#35"

/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem toInt?_neg_one (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem toInt?_two (I : Interp 𝕜) : I.toInt? (2 : 𝕜) = some 2 :=
  (I.toInt?_eq _ _).2 (by simp)

/-- An integer-valued function continuous at `t` is constant near `t`, in a field whose
nonzero integers have norm at least one. -/
theorem eventually_eq_of_int (hint : ∀ n : ℤ, n ≠ 0 → 1 ≤ ‖(n : 𝕜)‖) {g : 𝕜 → 𝕜} {t : 𝕜}
    (hg : ContinuousAt g t) (hI : ∀ᶠ w in 𝓝 t, ∃ n : ℤ, g w = n) : ∀ᶠ w in 𝓝 t, g w = g t := by
  obtain ⟨n0, hn0⟩ := hI.self_of_nhds
  have hc : ∀ᶠ w in 𝓝 t, ‖g w - g t‖ < 1 := by
    filter_upwards [hg (Metric.ball_mem_nhds (g t) one_pos)] with w hw
    simpa [dist_eq_norm] using hw
  filter_upwards [hI, hc] with w hw hwc
  obtain ⟨n, hn⟩ := hw
  rw [hn, hn0] at hwc ⊢
  by_contra hne
  have h1 : n - n0 ≠ 0 := sub_ne_zero.2 (fun h => hne (by rw [h]))
  have h2 := hint _ h1
  push_cast at h2
  linarith

/-- A function constant near `t` has derivative zero there. -/
theorem deriv_eq_zero_of_eventually {g : 𝕜 → 𝕜} {g' t : 𝕜} (hd : HasDerivAt g g' t)
    (he : ∀ᶠ w in 𝓝 t, g w = g t) : g' = 0 :=
  hd.unique ((hasDerivAt_const t (g t)).congr_of_eventuallyEq he)

/-- A function with derivatives near `t` that is integer-valued near `t` has zero
derivative near `t`. -/
theorem eventually_deriv_zero (hint : ∀ n : ℤ, n ≠ 0 → 1 ≤ ‖(n : 𝕜)‖) {g g' : 𝕜 → 𝕜} {t : 𝕜}
    (hd : ∀ᶠ w in 𝓝 t, HasDerivAt g (g' w) w) (hI : ∀ᶠ w in 𝓝 t, ∃ n : ℤ, g w = n) :
    ∀ᶠ w in 𝓝 t, g' w = 0 := by
  filter_upwards [hd, hI.eventually_nhds] with w hdw hIw
  exact deriv_eq_zero_of_eventually hdw (eventually_eq_of_int hint hdw.continuousAt hIw)

theorem exists_ne_of_eventually {p : 𝕜 → Prop} {t : 𝕜} (h : ∀ᶠ w in 𝓝 t, p w) :
    ∃ w, w ≠ t ∧ p w := by
  obtain ⟨w, hw, hw'⟩ := ((h.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : {t}ᶜ ∈ 𝓝[≠] t)).exists
  exact ⟨w, hw', hw⟩

theorem rubi23r11Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (hint : ∀ n : ℤ, n ≠ 0 → 1 ≤ ‖(n : 𝕜)‖) (hlnF : ∀ z : 𝕜, I.lt 0 z → I.lnDefined z) :
    AntiderivRecHolds I "x" rubi23r11Nondeg.conditions rubi23r11Nondeg.body rubi23r11Nondeg.result rubi23r11Nondeg.integrals := by
  intro env hc t hF
  have ord : ∀ (x y : ℤ), I.lt (x : 𝕜) (y : 𝕜) → x < y := by
    intro x y h
    have h' : I.lt ((x : ℚ) : 𝕜) ((y : ℚ) : 𝕜) := by rw [Rat.cast_intCast, Rat.cast_intCast]; exact h
    exact_mod_cast (hlt _ _).1 h'
  have hd0 : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi23r11Nondeg]); simpa [Cond.Holds, Defined, eval] using h
  have hFl : I.lnDefined (env "F") := by
    have h := hc (.gt (.var "F") (.int 0)) (by simp [rubi23r11Nondeg])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    exact hlnF _ (by simpa using h)
  have gn := hc (.gt (.int 0) (.var "n")) (by simp [rubi23r11Nondeg])
  rcases hk_n : I.toInt? (env "n") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi23r11Nondeg, Defined, eval, hk_n] at h
  have h_n : env "n" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have hk : k < 0 := by
    simp only [Cond.Holds, Defined, eval, true_and] at gn; rw [h_n] at gn; exact ord _ _ (by simpa using gn)
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi23r11Nondeg.body →
      (env "c" + env "d" * w) ≠ 0 ∧ ∃ N : ℤ, I.toInt? (env "a" + env "b" * (env "c" + env "d" * w) ^ k) = some N ∧ (N < 0 → env "F" ≠ 0) := by
    intro w h
    simp [rubi23r11Nondeg, Defined, eval, hk_n, hk] at h
    first | exact h | exact ⟨h.1, h.2⟩ | tauto | (trace_state; sorry)
  obtain ⟨hc0, N0, hN0, hNF⟩ := hBody t hF.self_of_nhds
  -- the exponent is a locally constant integer
  have hgd : HasDerivAt (fun w => env "a" + env "b" * (env "c" + env "d" * w) ^ k)
      (env "b" * ((k : 𝕜) * (env "c" + env "d" * t) ^ (k - 1) * env "d")) t := by
    have hl : HasDerivAt (fun w => env "c" + env "d" * w) (env "d") t := by
      simpa using ((hasDerivAt_id t).const_mul (env "d")).const_add (env "c")
    exact ((hasDerivAt_zpow k _ (Or.inl hc0)).comp t hl).const_mul _ |>.const_add _
  have hev : ∀ᶠ w in 𝓝 t, ∃ n : ℤ, env "a" + env "b" * (env "c" + env "d" * w) ^ k = n := by
    filter_upwards [hF] with w hw
    obtain ⟨-, N, hN, -⟩ := hBody w hw
    exact ⟨N, (I.toInt?_eq _ _).1 hN⟩
  have hb0 : env "b" = 0 := by
    have h0 := deriv_eq_zero_of_eventually hgd (eventually_eq_of_int hint hgd.continuousAt hev)
    have hk0 : (k : 𝕜) ≠ 0 := by
      intro h; have := hint k (by omega); rw [h, norm_zero] at this; linarith
    have hz : (env "c" + env "d" * t) ^ (k - 1) ≠ 0 := zpow_ne_zero _ hc0
    rcases mul_eq_zero.1 h0 with h | h
    · exact h
    · exfalso; exact mul_ne_zero (mul_ne_zero hk0 hz) hd0 h
  have hNa : I.toInt? (env "a") = some N0 := by simpa [hb0] using hN0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi23r11Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, N, hN, hNF'⟩ := hBody w hw
    simp [Defined, eval, hk_n, hk, h1]
    first | exact ⟨N, hN, hNF'⟩ | exact ⟨fun _ => h1, N, hN, hNF'⟩ | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    obtain ⟨h1, N, hN, hNF'⟩ := hBody w hw
    simp [rubi23r11Nondeg, Defined, eval, recEnv, hk_n, hk, h1, hd0, toInt?_neg_one, hFl]
    first | exact ⟨N, hN, hNF'⟩ | tauto | (trace_state; sorry)
  · simp only [rubi23r11Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (rubi23r11Nondeg.integrals.map (·.1)) Φ "x" w) rubi23r11Nondeg.result) =
        fun w => (env "c" + env "d" * w) * env "F" ^ N0 * (env "d")⁻¹ + 0 * Φ "I1" w := by
      funext w
      simp [rubi23r11Nondeg, eval, recEnv, hk_n, hb0, hNa, toInt?_neg_one, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
    have hEF : eval I (Function.update env "x" t) rubi23r11Nondeg.body = env "F" ^ N0 := by
      simp [rubi23r11Nondeg, eval, hk_n, hb0, hNa]
    rw [hfun, hEF]
    have hl : HasDerivAt (fun w => (env "c" + env "d" * w)) (env "d") t := by
      simpa using ((hasDerivAt_id t).const_mul (env "d")).const_add (env "c")
    refine (((hl.mul_const (env "F" ^ N0)).mul_const (env "d")⁻¹).add ((hΦ.const_mul 0))).congr_deriv ?_
    field_simp
    ring

theorem rubi23r23Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (hint : ∀ n : ℤ, n ≠ 0 → 1 ≤ ‖(n : 𝕜)‖) (hlnF : ∀ z : 𝕜, I.lt 0 z → I.lnDefined z) :
    AntiderivRecHolds I "x" rubi23r23Nondeg.conditions rubi23r23Nondeg.body rubi23r23Nondeg.result rubi23r23Nondeg.integrals := by
  intro env hc t hF
  have ord : ∀ (x y : ℤ), I.lt (x : 𝕜) (y : 𝕜) → x < y := by
    intro x y h
    have h' : I.lt ((x : ℚ) : 𝕜) ((y : ℚ) : 𝕜) := by rw [Rat.cast_intCast, Rat.cast_intCast]; exact h
    exact_mod_cast (hlt _ _).1 h'
  have hFl : I.lnDefined (env "F") := by
    have h := hc (.gt (.var "F") (.int 0)) (by simp [rubi23r23Nondeg])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    exact hlnF _ (by simpa using h)
  have h2 : (2 : 𝕜) ≠ 0 := by
    intro h; have := hint 2 (by norm_num); push_cast at this; rw [h, norm_zero] at this; linarith
  have gm := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi23r23Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi23r23Nondeg, Defined, eval, hk_m] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have hk : k < -1 := by
    simp only [Cond.Holds, Defined, eval, true_and] at gm; rw [h_m] at gm; exact ord _ _ (by simpa using gm)
  have hk0 : k < 0 := by omega
  have hk1 : k + 1 < 0 := by omega
  have em1 : I.toInt? (env "m" + 1) = some (k + 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em2 : I.toInt? (env "m" + 2) = some (k + 2) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have ek1 : I.toInt? ((k : 𝕜) + 1) = some (k + 1) := (I.toInt?_eq _ _).2 (by push_cast; ring)
  have ek2 : I.toInt? ((k : 𝕜) + 2) = some (k + 2) := (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hA := hc (.ne (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.pow (.var "f") (.int 2))) (.int 0)) (by simp [rubi23r23Nondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hA
  have hv0 : env "f" ≠ 0 := by tauto
  have hm1 : (k : 𝕜) + 1 ≠ 0 := by rw [← h_m]; tauto
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi23r23Nondeg.body →
      (env "e" + env "f" * w) ≠ 0 ∧ ∃ N : ℤ, I.toInt? (env "a" + env "b" * (env "c" + env "d" * w) ^ 2) = some N ∧ (N < 0 → env "F" ≠ 0) := by
    intro w h
    simp [rubi23r23Nondeg, Defined, eval, hk_m, hk0, toInt?_two] at h
    first | exact h | tauto | (trace_state; sorry)
  obtain ⟨hu0, N0, hN0, hNF⟩ := hBody t hF.self_of_nhds
  rcases eq_or_ne (env "d") 0 with hd | hd0
  · have hNa : I.toInt? (env "a" + env "b" * env "c" ^ 2) = some N0 := by simpa [hd] using hN0
    refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
    · simp only [rubi23r23Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
      · obtain ⟨h1, N, hN, hNF'⟩ := hBody w hw
        simp [Defined, eval, hk_m, em1, em2, toInt?_two, h1, hN, hNF', hk1]
        first | done | tauto | (trace_state; sorry)
    · filter_upwards [hF] with w hw
      obtain ⟨h1, N, hN, hNF'⟩ := hBody w hw
      simp [rubi23r23Nondeg, Defined, eval, recEnv, hk_m, em1, ek1, toInt?_two, h1, hN, hNF', hk1, hv0, hm1, h_m, toInt?_neg_one, toInt?_two, hFl]
      first | done | tauto | (trace_state; sorry)
    · simp only [rubi23r23Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
      obtain ⟨hΦ1, hΦ2⟩ := hΦ
      have hfun : (fun w => eval I (recEnv env (rubi23r23Nondeg.integrals.map (·.1)) Φ "x" w) rubi23r23Nondeg.result) =
          fun w => (env "e" + env "f" * w) ^ (k + 1) * env "F" ^ N0 * (env "f" * ((k : 𝕜) + 1))⁻¹ + 0 * Φ "I1" w + 0 * Φ "I2" w := by
        funext w
        simp [rubi23r23Nondeg, eval, recEnv, hk_m, em1, em2, toInt?_two, ek1, ek2, hd, hNa, h_m, toInt?_neg_one, toInt?_two, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
        try first | ring1 | (field_simp; done) | (field_simp; ring1)
      have hEF : eval I (Function.update env "x" t) rubi23r23Nondeg.body = (env "e" + env "f" * t) ^ k * env "F" ^ N0 := by
        simp [rubi23r23Nondeg, eval, hk_m, em1, em2, toInt?_two, hd, hNa, toInt?_two, toInt?_neg_one]
      rw [hfun, hEF]
      have hl : HasDerivAt (fun w => (env "e" + env "f" * w)) (env "f") t := by
        simpa using ((hasDerivAt_id t).const_mul (env "f")).const_add (env "e")
      have hP := (hasDerivAt_zpow (k + 1) _ (Or.inl hu0)).comp t hl
      refine ((((hP.mul_const (env "F" ^ N0)).mul_const _).add (hΦ1.const_mul 0)).add (hΦ2.const_mul 0)).congr_deriv ?_
      simp only [Function.comp_def, add_sub_cancel_right]
      push_cast
      field_simp
      ring
  · have hev : ∀ᶠ w in 𝓝 t, ∃ n : ℤ, env "a" + env "b" * (env "c" + env "d" * w) ^ 2 = n := by
      filter_upwards [hF] with w hw
      obtain ⟨-, N, hN, -⟩ := hBody w hw
      exact ⟨N, (I.toInt?_eq _ _).1 hN⟩
    have hdz := eventually_deriv_zero hint (g := fun w => env "a" + env "b" * (env "c" + env "d" * w) ^ 2)
      (g' := fun w => env "b" * ((2 : ℕ) * (env "c" + env "d" * w) ^ (2 - 1) * env "d"))
      (Eventually.of_forall fun w => by
        have hl : HasDerivAt (fun w => env "c" + env "d" * w) (env "d") w := by
          simpa using ((hasDerivAt_id w).const_mul (env "d")).const_add (env "c")
        exact (hl.pow 2).const_mul _ |>.const_add _) hev
    have hb0 : env "b" = 0 := by
      obtain ⟨w, hwt, hw⟩ := exists_ne_of_eventually hdz
      have ht := hdz.self_of_nhds
      by_contra hb
      have key : ∀ z, env "c" + env "d" * z = 0 → env "c" + env "d" * z = 0 := by
        intro z hz
        exact hz
      have e1 := key t (by simpa [hb, hd0, h2] using ht)
      have e2 := key w (by simpa [hb, hd0, h2] using hw)
      apply hwt
      have : env "d" * (w - t) = 0 := by linear_combination e2 - e1
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hd0
      · exact sub_eq_zero.1 h
    have hNa : I.toInt? (env "a") = some N0 := by simpa [hb0] using hN0
    refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
    · simp only [rubi23r23Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
      · obtain ⟨h1, N, hN, hNF'⟩ := hBody w hw
        simp [Defined, eval, hk_m, em1, em2, toInt?_two, h1, hN, hNF', hk1]
        first | done | tauto | (trace_state; sorry)
    · filter_upwards [hF] with w hw
      obtain ⟨h1, N, hN, hNF'⟩ := hBody w hw
      simp [rubi23r23Nondeg, Defined, eval, recEnv, hk_m, em1, ek1, toInt?_two, h1, hN, hNF', hk1, hv0, hm1, h_m, toInt?_neg_one, toInt?_two, hFl]
      first | done | tauto | (trace_state; sorry)
    · simp only [rubi23r23Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
      obtain ⟨hΦ1, hΦ2⟩ := hΦ
      have hfun : (fun w => eval I (recEnv env (rubi23r23Nondeg.integrals.map (·.1)) Φ "x" w) rubi23r23Nondeg.result) =
          fun w => (env "e" + env "f" * w) ^ (k + 1) * env "F" ^ N0 * (env "f" * ((k : 𝕜) + 1))⁻¹ + 0 * Φ "I1" w + 0 * Φ "I2" w := by
        funext w
        simp [rubi23r23Nondeg, eval, recEnv, hk_m, em1, em2, toInt?_two, ek1, ek2, hb0, hNa, h_m, toInt?_neg_one, toInt?_two, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
        try first | ring1 | (field_simp; done) | (field_simp; ring1)
      have hEF : eval I (Function.update env "x" t) rubi23r23Nondeg.body = (env "e" + env "f" * t) ^ k * env "F" ^ N0 := by
        simp [rubi23r23Nondeg, eval, hk_m, em1, em2, toInt?_two, hb0, hNa, toInt?_two, toInt?_neg_one]
      rw [hfun, hEF]
      have hl : HasDerivAt (fun w => (env "e" + env "f" * w)) (env "f") t := by
        simpa using ((hasDerivAt_id t).const_mul (env "f")).const_add (env "e")
      have hP := (hasDerivAt_zpow (k + 1) _ (Or.inl hu0)).comp t hl
      refine ((((hP.mul_const (env "F" ^ N0)).mul_const _).add (hΦ1.const_mul 0)).add (hΦ2.const_mul 0)).congr_deriv ?_
      simp only [Function.comp_def, add_sub_cancel_right]
      push_cast
      field_simp
      ring

theorem rubi23r24Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (hint : ∀ n : ℤ, n ≠ 0 → 1 ≤ ‖(n : 𝕜)‖) (hlnF : ∀ z : 𝕜, I.lt 0 z → I.lnDefined z) :
    AntiderivRecHolds I "x" rubi23r24Nondeg.conditions rubi23r24Nondeg.body rubi23r24Nondeg.result rubi23r24Nondeg.integrals := by
  intro env hc t hF
  have ord : ∀ (x y : ℤ), I.lt (x : 𝕜) (y : 𝕜) → x < y := by
    intro x y h
    have h' : I.lt ((x : ℚ) : 𝕜) ((y : ℚ) : 𝕜) := by rw [Rat.cast_intCast, Rat.cast_intCast]; exact h
    exact_mod_cast (hlt _ _).1 h'
  have hFl : I.lnDefined (env "F") := by
    have h := hc (.gt (.var "F") (.int 0)) (by simp [rubi23r24Nondeg])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    exact hlnF _ (by simpa using h)
  have h2 : (2 : 𝕜) ≠ 0 := by
    intro h; have := hint 2 (by norm_num); push_cast at this; rw [h, norm_zero] at this; linarith
  have gm := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi23r24Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi23r24Nondeg, Defined, eval, hk_m] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have hk : k < -1 := by
    simp only [Cond.Holds, Defined, eval, true_and] at gm; rw [h_m] at gm; exact ord _ _ (by simpa using gm)
  have hk0 : k < 0 := by omega
  have hk1 : k + 1 < 0 := by omega
  have em1 : I.toInt? (env "m" + 1) = some (k + 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em2 : I.toInt? (env "m" + 2) = some (k + 2) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have ek1 : I.toInt? ((k : 𝕜) + 1) = some (k + 1) := (I.toInt?_eq _ _).2 (by push_cast; ring)
  have ek2 : I.toInt? ((k : 𝕜) + 2) = some (k + 2) := (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hA := hc (.ne (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi23r24Nondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hA
  have hv0 : env "f" ≠ 0 := by tauto
  have hm1 : (k : 𝕜) + 1 ≠ 0 := by rw [← h_m]; tauto
  have gn := hc (.gt (.var "n") (.int 2)) (by simp [rubi23r24Nondeg])
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso; have h := hF.self_of_nhds; simp [rubi23r24Nondeg, Defined, eval, hk_m, hk_n] at h
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have hj : 2 < j := by
    simp only [Cond.Holds, Defined, eval, true_and] at gn; rw [h_n] at gn; exact ord _ _ (by simpa using gn)
  have hj0 : ¬ j < 0 := by omega
  have hj1 : ¬ j - 1 < 0 := by omega
  have hjne : j - 1 ≠ 0 := by omega
  have hjk : (j : 𝕜) ≠ 0 := by
    intro h; have := hint j (by omega); rw [h, norm_zero] at this; linarith
  have en1 : I.toInt? (env "n" + -1 * 1) = some (j - 1) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have en1' : I.toInt? (env "n" + -1) = some (j - 1) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi23r24Nondeg.body →
      (env "e" + env "f" * w) ≠ 0 ∧ ∃ N : ℤ, I.toInt? (env "a" + env "b" * (env "c" + env "d" * w) ^ j) = some N ∧ (N < 0 → env "F" ≠ 0) := by
    intro w h
    simp [rubi23r24Nondeg, Defined, eval, hk_m, hk0, hk_n, hj0] at h
    first | exact h | tauto | (trace_state; sorry)
  obtain ⟨hu0, N0, hN0, hNF⟩ := hBody t hF.self_of_nhds
  rcases eq_or_ne (env "d") 0 with hd | hd0
  · have hNa : I.toInt? (env "a" + env "b" * env "c" ^ j) = some N0 := by simpa [hd] using hN0
    refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
    · simp only [rubi23r24Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
      subst hi
      filter_upwards [hF] with w hw
      obtain ⟨h1, N, hN, hNF'⟩ := hBody w hw
      simp [Defined, eval, hk_m, hk_n, em1, en1, en1', hj1, h1, hN, hNF', hk1]
      first | done | tauto | (trace_state; sorry)
    · filter_upwards [hF] with w hw
      obtain ⟨h1, N, hN, hNF'⟩ := hBody w hw
      simp [rubi23r24Nondeg, Defined, eval, recEnv, hk_m, hk_n, em1, ek1, h1, hN, hNF', hk1, hv0, hm1, h_m, toInt?_neg_one, toInt?_two, hFl]
      first | done | tauto | (trace_state; sorry)
    · simp only [rubi23r24Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
      have hΦ1 := hΦ
      have hfun : (fun w => eval I (recEnv env (rubi23r24Nondeg.integrals.map (·.1)) Φ "x" w) rubi23r24Nondeg.result) =
          fun w => (env "e" + env "f" * w) ^ (k + 1) * env "F" ^ N0 * (env "f" * ((k : 𝕜) + 1))⁻¹ + 0 * Φ "I1" w := by
        funext w
        simp [rubi23r24Nondeg, eval, recEnv, hk_m, hk_n, em1, en1, en1', ek1, ek2, hd, hNa, h_m, toInt?_neg_one, toInt?_two, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
        try first | ring1 | (field_simp; done) | (field_simp; ring1)
      have hEF : eval I (Function.update env "x" t) rubi23r24Nondeg.body = (env "e" + env "f" * t) ^ k * env "F" ^ N0 := by
        simp [rubi23r24Nondeg, eval, hk_m, hk_n, em1, en1, en1', hd, hNa, toInt?_two, toInt?_neg_one]
      rw [hfun, hEF]
      have hl : HasDerivAt (fun w => (env "e" + env "f" * w)) (env "f") t := by
        simpa using ((hasDerivAt_id t).const_mul (env "f")).const_add (env "e")
      have hP := (hasDerivAt_zpow (k + 1) _ (Or.inl hu0)).comp t hl
      refine (((hP.mul_const (env "F" ^ N0)).mul_const _).add (hΦ1.const_mul 0)).congr_deriv ?_
      simp only [Function.comp_def, add_sub_cancel_right]
      push_cast
      field_simp
      ring
  · have hev : ∀ᶠ w in 𝓝 t, ∃ n : ℤ, env "a" + env "b" * (env "c" + env "d" * w) ^ j = n := by
      filter_upwards [hF] with w hw
      obtain ⟨-, N, hN, -⟩ := hBody w hw
      exact ⟨N, (I.toInt?_eq _ _).1 hN⟩
    have hdz := eventually_deriv_zero hint (g := fun w => env "a" + env "b" * (env "c" + env "d" * w) ^ j)
      (g' := fun w => env "b" * ((j : 𝕜) * (env "c" + env "d" * w) ^ (j - 1) * env "d"))
      (Eventually.of_forall fun w => by
        have hl : HasDerivAt (fun w => env "c" + env "d" * w) (env "d") w := by
          simpa using ((hasDerivAt_id w).const_mul (env "d")).const_add (env "c")
        exact ((hasDerivAt_zpow j _ (Or.inr (by omega))).comp w hl).const_mul _ |>.const_add _) hev
    have hb0 : env "b" = 0 := by
      obtain ⟨w, hwt, hw⟩ := exists_ne_of_eventually hdz
      have ht := hdz.self_of_nhds
      by_contra hb
      have key : ∀ z, env "c" + env "d" * z = 0 → env "c" + env "d" * z = 0 := by
        intro z hz
        exact hz
      have e1 := key t (by simpa [hb, hd0, hjk, zpow_eq_zero_iff hjne] using ht)
      have e2 := key w (by simpa [hb, hd0, hjk, zpow_eq_zero_iff hjne] using hw)
      apply hwt
      have : env "d" * (w - t) = 0 := by linear_combination e2 - e1
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hd0
      · exact sub_eq_zero.1 h
    have hNa : I.toInt? (env "a") = some N0 := by simpa [hb0] using hN0
    refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
    · simp only [rubi23r24Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
      subst hi
      filter_upwards [hF] with w hw
      obtain ⟨h1, N, hN, hNF'⟩ := hBody w hw
      simp [Defined, eval, hk_m, hk_n, em1, en1, en1', hj1, h1, hN, hNF', hk1]
      first | done | tauto | (trace_state; sorry)
    · filter_upwards [hF] with w hw
      obtain ⟨h1, N, hN, hNF'⟩ := hBody w hw
      simp [rubi23r24Nondeg, Defined, eval, recEnv, hk_m, hk_n, em1, ek1, h1, hN, hNF', hk1, hv0, hm1, h_m, toInt?_neg_one, toInt?_two, hFl]
      first | done | tauto | (trace_state; sorry)
    · simp only [rubi23r24Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
      have hΦ1 := hΦ
      have hfun : (fun w => eval I (recEnv env (rubi23r24Nondeg.integrals.map (·.1)) Φ "x" w) rubi23r24Nondeg.result) =
          fun w => (env "e" + env "f" * w) ^ (k + 1) * env "F" ^ N0 * (env "f" * ((k : 𝕜) + 1))⁻¹ + 0 * Φ "I1" w := by
        funext w
        simp [rubi23r24Nondeg, eval, recEnv, hk_m, hk_n, em1, en1, en1', ek1, ek2, hb0, hNa, h_m, toInt?_neg_one, toInt?_two, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
        try first | ring1 | (field_simp; done) | (field_simp; ring1)
      have hEF : eval I (Function.update env "x" t) rubi23r24Nondeg.body = (env "e" + env "f" * t) ^ k * env "F" ^ N0 := by
        simp [rubi23r24Nondeg, eval, hk_m, hk_n, em1, en1, en1', hb0, hNa, toInt?_two, toInt?_neg_one]
      rw [hfun, hEF]
      have hl : HasDerivAt (fun w => (env "e" + env "f" * w)) (env "f") t := by
        simpa using ((hasDerivAt_id t).const_mul (env "f")).const_add (env "e")
      have hP := (hasDerivAt_zpow (k + 1) _ (Or.inl hu0)).comp t hl
      refine (((hP.mul_const (env "F" ^ N0)).mul_const _).add (hΦ1.const_mul 0)).congr_deriv ?_
      simp only [Function.comp_def, add_sub_cancel_right]
      push_cast
      field_simp
      ring

theorem rubi23r26Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (hint : ∀ n : ℤ, n ≠ 0 → 1 ≤ ‖(n : 𝕜)‖) (hlnF : ∀ z : 𝕜, I.lt 0 z → I.lnDefined z) :
    AntiderivRecHolds I "x" rubi23r26Nondeg.conditions rubi23r26Nondeg.body rubi23r26Nondeg.result rubi23r26Nondeg.integrals := by
  intro env hc t hF
  have ord : ∀ (x y : ℤ), I.lt (x : 𝕜) (y : 𝕜) → x < y := by
    intro x y h
    have h' : I.lt ((x : ℚ) : 𝕜) ((y : ℚ) : 𝕜) := by rw [Rat.cast_intCast, Rat.cast_intCast]; exact h
    exact_mod_cast (hlt _ _).1 h'
  have hFl : I.lnDefined (env "F") := by
    have h := hc (.gt (.var "F") (.int 0)) (by simp [rubi23r26Nondeg])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    exact hlnF _ (by simpa using h)
  have h2 : (2 : 𝕜) ≠ 0 := by
    intro h; have := hint 2 (by norm_num); push_cast at this; rw [h, norm_zero] at this; linarith
  have gm := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi23r26Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi23r26Nondeg, Defined, eval, hk_m] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have hk : k < -1 := by
    simp only [Cond.Holds, Defined, eval, true_and] at gm; rw [h_m] at gm; exact ord _ _ (by simpa using gm)
  have hk0 : k < 0 := by omega
  have hk1 : k + 1 < 0 := by omega
  have em1 : I.toInt? (env "m" + 1) = some (k + 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em2 : I.toInt? (env "m" + 2) = some (k + 2) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have ek1 : I.toInt? ((k : 𝕜) + 1) = some (k + 1) := (I.toInt?_eq _ _).2 (by push_cast; ring)
  have ek2 : I.toInt? ((k : 𝕜) + 2) = some (k + 2) := (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hA := hc (.ne (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi23r26Nondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hA
  have hv0 : env "f" ≠ 0 := by tauto
  have hm1 : (k : 𝕜) + 1 ≠ 0 := by rw [← h_m]; tauto
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi23r26Nondeg.body →
      (env "e" + env "f" * w) ≠ 0 ∧ (env "c" + env "d" * w) ≠ 0 ∧ ∃ N : ℤ, I.toInt? (env "a" + env "b" * (env "c" + env "d" * w)⁻¹) = some N ∧ (N < 0 → env "F" ≠ 0) := by
    intro w h
    simp [rubi23r26Nondeg, Defined, eval, hk_m, hk0, toInt?_neg_one] at h
    first | exact h | tauto | (trace_state; sorry)
  obtain ⟨hu0, hc0, N0, hN0, hNF⟩ := hBody t hF.self_of_nhds
  rcases eq_or_ne (env "d") 0 with hd | hd0
  · have hNa : I.toInt? (env "a" + env "b" * (env "c")⁻¹) = some N0 := by simpa [hd] using hN0
    refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
    · simp only [rubi23r26Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
      subst hi
      filter_upwards [hF] with w hw
      obtain ⟨h1, hc1, N, hN, hNF'⟩ := hBody w hw
      simp [Defined, eval, hk_m, em1, toInt?_neg_one, toInt?_two, h1, hc1, hN, hNF', hk1]
      first | done | tauto | (trace_state; sorry)
    · filter_upwards [hF] with w hw
      obtain ⟨h1, hc1, N, hN, hNF'⟩ := hBody w hw
      simp [rubi23r26Nondeg, Defined, eval, recEnv, hk_m, em1, ek1, h1, hc1, hN, hNF', hk1, hv0, hm1, h_m, toInt?_neg_one, toInt?_two, hFl]
      first | done | tauto | (trace_state; sorry)
    · simp only [rubi23r26Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
      have hΦ1 := hΦ
      have hfun : (fun w => eval I (recEnv env (rubi23r26Nondeg.integrals.map (·.1)) Φ "x" w) rubi23r26Nondeg.result) =
          fun w => (env "e" + env "f" * w) ^ (k + 1) * env "F" ^ N0 * (env "f" * ((k : 𝕜) + 1))⁻¹ + 0 * Φ "I1" w := by
        funext w
        simp [rubi23r26Nondeg, eval, recEnv, hk_m, em1, ek1, ek2, hd, hNa, h_m, toInt?_neg_one, toInt?_two, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
        try first | ring1 | (field_simp; done) | (field_simp; ring1)
      have hEF : eval I (Function.update env "x" t) rubi23r26Nondeg.body = (env "e" + env "f" * t) ^ k * env "F" ^ N0 := by
        simp [rubi23r26Nondeg, eval, hk_m, em1, hd, hNa, toInt?_two, toInt?_neg_one]
      rw [hfun, hEF]
      have hl : HasDerivAt (fun w => (env "e" + env "f" * w)) (env "f") t := by
        simpa using ((hasDerivAt_id t).const_mul (env "f")).const_add (env "e")
      have hP := (hasDerivAt_zpow (k + 1) _ (Or.inl hu0)).comp t hl
      refine (((hP.mul_const (env "F" ^ N0)).mul_const _).add (hΦ1.const_mul 0)).congr_deriv ?_
      simp only [Function.comp_def, add_sub_cancel_right]
      push_cast
      field_simp
      ring
  · have hgd : HasDerivAt (fun w => env "a" + env "b" * (env "c" + env "d" * w)⁻¹)
        (env "b" * (-(env "d") / (env "c" + env "d" * t) ^ 2)) t := by
      have hl : HasDerivAt (fun w => env "c" + env "d" * w) (env "d") t := by
        simpa using ((hasDerivAt_id t).const_mul (env "d")).const_add (env "c")
      exact ((hl.inv hc0).const_mul _).const_add _
    have hev : ∀ᶠ w in 𝓝 t, ∃ n : ℤ, env "a" + env "b" * (env "c" + env "d" * w)⁻¹ = n := by
      filter_upwards [hF] with w hw
      obtain ⟨-, -, N, hN, -⟩ := hBody w hw
      exact ⟨N, (I.toInt?_eq _ _).1 hN⟩
    have hb0 : env "b" = 0 := by
      have h0 := deriv_eq_zero_of_eventually hgd (eventually_eq_of_int hint hgd.continuousAt hev)
      simpa [hd0, hc0] using h0
    have hNa : I.toInt? (env "a") = some N0 := by simpa [hb0] using hN0
    refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
    · simp only [rubi23r26Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
      subst hi
      filter_upwards [hF] with w hw
      obtain ⟨h1, hc1, N, hN, hNF'⟩ := hBody w hw
      simp [Defined, eval, hk_m, em1, toInt?_neg_one, toInt?_two, h1, hc1, hN, hNF', hk1]
      first | done | tauto | (trace_state; sorry)
    · filter_upwards [hF] with w hw
      obtain ⟨h1, hc1, N, hN, hNF'⟩ := hBody w hw
      simp [rubi23r26Nondeg, Defined, eval, recEnv, hk_m, em1, ek1, h1, hc1, hN, hNF', hk1, hv0, hm1, h_m, toInt?_neg_one, toInt?_two, hFl]
      first | done | tauto | (trace_state; sorry)
    · simp only [rubi23r26Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
      have hΦ1 := hΦ
      have hfun : (fun w => eval I (recEnv env (rubi23r26Nondeg.integrals.map (·.1)) Φ "x" w) rubi23r26Nondeg.result) =
          fun w => (env "e" + env "f" * w) ^ (k + 1) * env "F" ^ N0 * (env "f" * ((k : 𝕜) + 1))⁻¹ + 0 * Φ "I1" w := by
        funext w
        simp [rubi23r26Nondeg, eval, recEnv, hk_m, em1, ek1, ek2, hb0, hNa, h_m, toInt?_neg_one, toInt?_two, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
        try first | ring1 | (field_simp; done) | (field_simp; ring1)
      have hEF : eval I (Function.update env "x" t) rubi23r26Nondeg.body = (env "e" + env "f" * t) ^ k * env "F" ^ N0 := by
        simp [rubi23r26Nondeg, eval, hk_m, em1, hb0, hNa, toInt?_two, toInt?_neg_one]
      rw [hfun, hEF]
      have hl : HasDerivAt (fun w => (env "e" + env "f" * w)) (env "f") t := by
        simpa using ((hasDerivAt_id t).const_mul (env "f")).const_add (env "e")
      have hP := (hasDerivAt_zpow (k + 1) _ (Or.inl hu0)).comp t hl
      refine (((hP.mul_const (env "F" ^ N0)).mul_const _).add (hΦ1.const_mul 0)).congr_deriv ?_
      simp only [Function.comp_def, add_sub_cancel_right]
      push_cast
      field_simp
      ring

theorem rubi23r35Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (hint : ∀ n : ℤ, n ≠ 0 → 1 ≤ ‖(n : 𝕜)‖) (hlnF : ∀ z : 𝕜, I.lt 0 z → I.lnDefined z) :
    AntiderivRecHolds I "x" rubi23r35Nondeg.conditions rubi23r35Nondeg.body rubi23r35Nondeg.result rubi23r35Nondeg.integrals := by
  intro env hc t hF
  have ord : ∀ (x y : ℤ), I.lt (x : 𝕜) (y : 𝕜) → x < y := by
    intro x y h
    have h' : I.lt ((x : ℚ) : 𝕜) ((y : ℚ) : 𝕜) := by rw [Rat.cast_intCast, Rat.cast_intCast]; exact h
    exact_mod_cast (hlt _ _).1 h'
  have hFl : I.lnDefined (env "F") := by
    have h := hc (.gt (.var "F") (.int 0)) (by simp [rubi23r35Nondeg])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    exact hlnF _ (by simpa using h)
  have h2 : (2 : 𝕜) ≠ 0 := by
    intro h; have := hint 2 (by norm_num); push_cast at this; rw [h, norm_zero] at this; linarith
  have gm := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi23r35Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi23r35Nondeg, Defined, eval, hk_m] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have hk : k < -1 := by
    simp only [Cond.Holds, Defined, eval, true_and] at gm; rw [h_m] at gm; exact ord _ _ (by simpa using gm)
  have hk0 : k < 0 := by omega
  have hk1 : k + 1 < 0 := by omega
  have em1 : I.toInt? (env "m" + 1) = some (k + 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em2 : I.toInt? (env "m" + 2) = some (k + 2) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have ek1 : I.toInt? ((k : 𝕜) + 1) = some (k + 1) := (I.toInt?_eq _ _).2 (by push_cast; ring)
  have ek2 : I.toInt? ((k : 𝕜) + 2) = some (k + 2) := (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hA := hc (.ne (.app2 .mul (.var "h") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi23r35Nondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hA
  have hv0 : env "h" ≠ 0 := by tauto
  have hm1 : (k : 𝕜) + 1 ≠ 0 := by rw [← h_m]; tauto
  have hbc : env "b" * env "c" - env "a" * env "d" ≠ 0 := by
    have h := hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi23r35Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    intro h0; apply h; linear_combination h0
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi23r35Nondeg.body →
      (env "g" + env "h" * w) ≠ 0 ∧ (env "c" + env "d" * w) ≠ 0 ∧ ∃ N : ℤ, I.toInt? (env "e" + env "f" * (env "a" + env "b" * w) * (env "c" + env "d" * w)⁻¹) = some N ∧ (N < 0 → env "F" ≠ 0) := by
    intro w h
    simp [rubi23r35Nondeg, Defined, eval, hk_m, hk0, toInt?_neg_one] at h
    first | exact h | tauto | (trace_state; sorry)
  obtain ⟨hu0, hc0, N0, hN0, hNF⟩ := hBody t hF.self_of_nhds
  have hgd : HasDerivAt (fun w => env "e" + env "f" * (env "a" + env "b" * w) * (env "c" + env "d" * w)⁻¹)
      (env "f" * (env "b" * env "c" - env "a" * env "d") / (env "c" + env "d" * t) ^ 2) t := by
    have hl : HasDerivAt (fun w => env "c" + env "d" * w) (env "d") t := by
      simpa using ((hasDerivAt_id t).const_mul (env "d")).const_add (env "c")
    have hab : HasDerivAt (fun w => env "a" + env "b" * w) (env "b") t := by
      simpa using ((hasDerivAt_id t).const_mul (env "b")).const_add (env "a")
    refine (((hab.const_mul (env "f")).mul (hl.inv hc0)).const_add (env "e")).congr_deriv ?_
    simp only [Pi.inv_apply]
    field_simp
    ring
  have hev : ∀ᶠ w in 𝓝 t, ∃ n : ℤ, env "e" + env "f" * (env "a" + env "b" * w) * (env "c" + env "d" * w)⁻¹ = n := by
    filter_upwards [hF] with w hw
    obtain ⟨-, -, N, hN, -⟩ := hBody w hw
    exact ⟨N, (I.toInt?_eq _ _).1 hN⟩
  have hf0 : env "f" = 0 := by
    have h0 := deriv_eq_zero_of_eventually hgd (eventually_eq_of_int hint hgd.continuousAt hev)
    simpa [hbc, hc0] using h0
  have hNa : I.toInt? (env "e") = some N0 := by simpa [hf0] using hN0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi23r35Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, hc1, N, hN, hNF'⟩ := hBody w hw
    simp [Defined, eval, hk_m, em1, toInt?_neg_one, toInt?_two, h1, hc1, hN, hNF', hk1]
    first | done | tauto | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    obtain ⟨h1, hc1, N, hN, hNF'⟩ := hBody w hw
    simp [rubi23r35Nondeg, Defined, eval, recEnv, hk_m, em1, ek1, h1, hc1, hN, hNF', hk1, hv0, hm1, h_m, toInt?_neg_one, toInt?_two, hFl]
    first | done | tauto | (trace_state; sorry)
  · simp only [rubi23r35Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1 := hΦ
    have hfun : (fun w => eval I (recEnv env (rubi23r35Nondeg.integrals.map (·.1)) Φ "x" w) rubi23r35Nondeg.result) =
        fun w => (env "g" + env "h" * w) ^ (k + 1) * env "F" ^ N0 * (env "h" * ((k : 𝕜) + 1))⁻¹ + 0 * Φ "I1" w := by
      funext w
      simp [rubi23r35Nondeg, eval, recEnv, hk_m, em1, ek1, ek2, hf0, hNa, h_m, toInt?_neg_one, toInt?_two, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | (field_simp; done) | (field_simp; ring1)
    have hEF : eval I (Function.update env "x" t) rubi23r35Nondeg.body = (env "g" + env "h" * t) ^ k * env "F" ^ N0 := by
      simp [rubi23r35Nondeg, eval, hk_m, em1, hf0, hNa, toInt?_two, toInt?_neg_one]
    rw [hfun, hEF]
    have hl : HasDerivAt (fun w => (env "g" + env "h" * w)) (env "h") t := by
      simpa using ((hasDerivAt_id t).const_mul (env "h")).const_add (env "g")
    have hP := (hasDerivAt_zpow (k + 1) _ (Or.inl hu0)).comp t hl
    refine (((hP.mul_const (env "F" ^ N0)).mul_const _).add (hΦ1.const_mul 0)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    push_cast
    field_simp
    ring

private theorem real_hint : ∀ n : ℤ, n ≠ 0 → 1 ≤ ‖(n : ℝ)‖ := by
  intro n hn; rw [Int.norm_cast_real, Int.norm_eq_abs]; exact_mod_cast Int.one_le_abs hn

private theorem complex_hint : ∀ n : ℤ, n ≠ 0 → 1 ≤ ‖(n : ℂ)‖ := by
  intro n hn
  rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real, Int.norm_cast_real, Int.norm_eq_abs]
  exact_mod_cast Int.one_le_abs hn

theorem rubi23r11Nondeg_real : rubi23r11Nondeg.Holds .real :=
  rubi23r11Nondeg_holds Interp.real Interp.real_lt_rat real_hint (fun _ h => h)
theorem rubi23r11Nondeg_complex : rubi23r11Nondeg.Holds .complex :=
  rubi23r11Nondeg_holds Interp.complex Interp.complex_lt_rat complex_hint (fun _ h => by
    intro hz; rw [hz] at h; exact lt_irrefl _ h.2.2)
theorem rubi23r23Nondeg_real : rubi23r23Nondeg.Holds .real :=
  rubi23r23Nondeg_holds Interp.real Interp.real_lt_rat real_hint (fun _ h => h)
theorem rubi23r23Nondeg_complex : rubi23r23Nondeg.Holds .complex :=
  rubi23r23Nondeg_holds Interp.complex Interp.complex_lt_rat complex_hint (fun _ h => by
    intro hz; rw [hz] at h; exact lt_irrefl _ h.2.2)
theorem rubi23r24Nondeg_real : rubi23r24Nondeg.Holds .real :=
  rubi23r24Nondeg_holds Interp.real Interp.real_lt_rat real_hint (fun _ h => h)
theorem rubi23r24Nondeg_complex : rubi23r24Nondeg.Holds .complex :=
  rubi23r24Nondeg_holds Interp.complex Interp.complex_lt_rat complex_hint (fun _ h => by
    intro hz; rw [hz] at h; exact lt_irrefl _ h.2.2)
theorem rubi23r26Nondeg_real : rubi23r26Nondeg.Holds .real :=
  rubi23r26Nondeg_holds Interp.real Interp.real_lt_rat real_hint (fun _ h => h)
theorem rubi23r26Nondeg_complex : rubi23r26Nondeg.Holds .complex :=
  rubi23r26Nondeg_holds Interp.complex Interp.complex_lt_rat complex_hint (fun _ h => by
    intro hz; rw [hz] at h; exact lt_irrefl _ h.2.2)
theorem rubi23r35Nondeg_real : rubi23r35Nondeg.Holds .real :=
  rubi23r35Nondeg_holds Interp.real Interp.real_lt_rat real_hint (fun _ h => h)
theorem rubi23r35Nondeg_complex : rubi23r35Nondeg.Holds .complex :=
  rubi23r35Nondeg_holds Interp.complex Interp.complex_lt_rat complex_hint (fun _ h => by
    intro hz; rw [hz] at h; exact lt_irrefl _ h.2.2)

end Proofs

end OSR.IntegrationRec117
