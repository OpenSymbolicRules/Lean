import OSR.IntegrationRec301

/-! # Affine-substitution variants up to an algebraic identity

Instances of `antiderivSubst_affine_of`: the integrand differs from the residual integrand with
`x ↦ c + d x` only in affine subterms with the same value (an identity, using the rule's
relations and `d ≠ 0`). -/

namespace OSR.IntegrationRec302
open OSR OSR.Calculus OSR.IntegrationNum1 OSR.IntegrationRec300 OSR.IntegrationRec301

/-- RUBI rubi33r2Nondeg: `x ↦ d + e x`, up to identities on 1 subterm. -/
theorem rubi33r2Nondeg_holds {𝕜 : Type} [NontriviallyNormedField 𝕜] (I : Interp 𝕜) :
    AntiderivSubstHolds I "x" rubi33r2Nondeg.conditions rubi33r2Nondeg.body rubi33r2Nondeg.result rubi33r2Nondeg.integrals
      rubi33r2Nondeg.substs := by
  have hm1 : I.toInt? (-1 : 𝕜) = some (-1) := by simpa using Interp.toInt?_cast I (-1)
  have hd0 : ∀ env : String → 𝕜, (∀ k ∈ rubi33r2Nondeg.conditions, k.Holds I env) → env "e" ≠ 0 :=
    fun env hcs => by simpa [Cond.Holds, Defined, eval] using hcs (.ne (.var "e") (.int 0)) (by simp [rubi33r2Nondeg])
  exact antiderivSubst_affine_of (I := I) rubi33r2Nondeg.body (rubi33r2Nondeg.integrals.head!.2) (c := "d") (d := "e")
    (by decide) (by decide) (by decide) hd0 (fun env hcs w => by
      have hd := hd0 env hcs
      have hzd : env "d" ≠ 0 := by
        simpa [Cond.Holds, Defined, eval] using hcs (.ne (.var "d") (.int 0)) (by simp [rubi33r2Nondeg])
      have hr0 := hcs (.eq (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "g"))) (.int 0)) (by simp [rubi33r2Nondeg])
      simp [Cond.Holds, Defined, eval] at hr0
      have e1 : rubi33r2Nondeg.body = Expr.subst [("y1", (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))))] ((.app2 .mul (.pow (.var "y1") (.var "q")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.var "p")))) := by rfl
      have e2 : Expr.subst [("x", affineSub "d" "e")] (rubi33r2Nondeg.integrals.head!.2) =
          Expr.subst [("y1", (.app2 .mul (.app2 .mul (.var "f") (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.pow (.var "d") (.int (-1)))))] ((.app2 .mul (.pow (.var "y1") (.var "q")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.var "p")))) := by rfl
      rw [e1, e2]
      apply subst_congr
      · refine (List.Forall₂.cons ⟨rfl, ?_⟩ List.Forall₂.nil)
        · simp [eval, Function.update, hm1]
          field_simp
          linear_combination (-w) * hr0
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl
        simp [Defined, eval, hm1, hzd])

theorem rubi33r2Nondeg_real : rubi33r2Nondeg.Holds .real := rubi33r2Nondeg_holds Interp.real
theorem rubi33r2Nondeg_complex : rubi33r2Nondeg.Holds .complex := rubi33r2Nondeg_holds Interp.complex

/-- RUBI rubi33r20Nondeg: `x ↦ d + e x`, up to identities on 2 subterms. -/
theorem rubi33r20Nondeg_holds {𝕜 : Type} [NontriviallyNormedField 𝕜] (I : Interp 𝕜) :
    AntiderivSubstHolds I "x" rubi33r20Nondeg.conditions rubi33r20Nondeg.body rubi33r20Nondeg.result rubi33r20Nondeg.integrals
      rubi33r20Nondeg.substs := by
  have hm1 : I.toInt? (-1 : 𝕜) = some (-1) := by simpa using Interp.toInt?_cast I (-1)
  have hd0 : ∀ env : String → 𝕜, (∀ k ∈ rubi33r20Nondeg.conditions, k.Holds I env) → env "e" ≠ 0 :=
    fun env hcs => by simpa [Cond.Holds, Defined, eval] using hcs (.ne (.var "e") (.int 0)) (by simp [rubi33r20Nondeg])
  exact antiderivSubst_affine_of (I := I) rubi33r20Nondeg.body (rubi33r20Nondeg.integrals.head!.2) (c := "d") (d := "e")
    (by decide) (by decide) (by decide) hd0 (fun env hcs w => by
      have hd := hd0 env hcs
      have hr0 := hcs (.eq (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "g"))) (.int 0)) (by simp [rubi33r20Nondeg])
      simp [Cond.Holds, Defined, eval] at hr0
      have e1 : rubi33r20Nondeg.body = Expr.subst [("y1", (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))), ("y2", (.app2 .add (.var "h") (.app2 .mul (.var "i") (.var "x"))))] ((.app2 .mul (.app2 .mul (.pow (.var "y1") (.var "q")) (.pow (.var "y2") (.var "r"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.var "p")))) := by rfl
      have e2 : Expr.subst [("x", affineSub "d" "e")] (rubi33r20Nondeg.integrals.head!.2) =
          Expr.subst [("y1", (.app2 .mul (.app2 .mul (.var "g") (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.pow (.var "e") (.int (-1))))), ("y2", (.app2 .add (.app2 .mul (.app2 .add (.app2 .mul (.var "e") (.var "h")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "i"))) (.pow (.var "e") (.int (-1)))) (.app2 .mul (.app2 .mul (.var "i") (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.pow (.var "e") (.int (-1))))))] ((.app2 .mul (.app2 .mul (.pow (.var "y1") (.var "q")) (.pow (.var "y2") (.var "r"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.var "p")))) := by rfl
      rw [e1, e2]
      apply subst_congr
      · refine (List.Forall₂.cons ⟨rfl, ?_⟩ (List.Forall₂.cons ⟨rfl, ?_⟩ List.Forall₂.nil))
        · simp [eval, Function.update, hm1]
          field_simp
          linear_combination (1) * hr0
        · simp [eval, Function.update, hm1]
          field_simp
          first
          | ring
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> simp [Defined, eval, hm1, hd])

theorem rubi33r20Nondeg_real : rubi33r20Nondeg.Holds .real := rubi33r20Nondeg_holds Interp.real
theorem rubi33r20Nondeg_complex : rubi33r20Nondeg.Holds .complex := rubi33r20Nondeg_holds Interp.complex

/-- RUBI rubi33r37Nondeg: `x ↦ d + e x`, up to identities on 2 subterms. -/
theorem rubi33r37Nondeg_holds {𝕜 : Type} [NontriviallyNormedField 𝕜] (I : Interp 𝕜) :
    AntiderivSubstHolds I "x" rubi33r37Nondeg.conditions rubi33r37Nondeg.body rubi33r37Nondeg.result rubi33r37Nondeg.integrals
      rubi33r37Nondeg.substs := by
  have hm1 : I.toInt? (-1 : 𝕜) = some (-1) := by simpa using Interp.toInt?_cast I (-1)
  have hd0 : ∀ env : String → 𝕜, (∀ k ∈ rubi33r37Nondeg.conditions, k.Holds I env) → env "e" ≠ 0 :=
    fun env hcs => by simpa [Cond.Holds, Defined, eval] using hcs (.ne (.var "e") (.int 0)) (by simp [rubi33r37Nondeg])
  exact antiderivSubst_affine_of (I := I) rubi33r37Nondeg.body (rubi33r37Nondeg.integrals.head!.2) (c := "d") (d := "e")
    (by decide) (by decide) (by decide) hd0 (fun env hcs w => by
      have hd := hd0 env hcs
      have hzd : env "d" ≠ 0 := by
        simpa [Cond.Holds, Defined, eval] using hcs (.ne (.var "d") (.int 0)) (by simp [rubi33r37Nondeg])
      have hr0 := hcs (.eq (.app2 .add (.app2 .mul (.var "e") (.var "k")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "l"))) (.int 0)) (by simp [rubi33r37Nondeg])
      simp [Cond.Holds, Defined, eval] at hr0
      have e1 : rubi33r37Nondeg.body = Expr.subst [("y1", (.app2 .add (.var "k") (.app2 .mul (.var "l") (.var "x")))), ("y2", (.app2 .add (.var "i") (.app2 .mul (.var "j") (.var "x"))))] ((.app2 .mul (.app2 .mul (.pow (.var "y1") (.var "r")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.var "p"))) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.app1 .ln (.app2 .mul (.var "h") (.pow (.var "y2") (.var "m")))))))) := by rfl
      have e2 : Expr.subst [("x", affineSub "d" "e")] (rubi33r37Nondeg.integrals.head!.2) =
          Expr.subst [("y1", (.app2 .mul (.app2 .mul (.var "k") (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.pow (.var "d") (.int (-1))))), ("y2", (.app2 .add (.app2 .mul (.app2 .add (.app2 .mul (.var "e") (.var "i")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "j"))) (.pow (.var "e") (.int (-1)))) (.app2 .mul (.app2 .mul (.var "j") (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.pow (.var "e") (.int (-1))))))] ((.app2 .mul (.app2 .mul (.pow (.var "y1") (.var "r")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.var "p"))) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.app1 .ln (.app2 .mul (.var "h") (.pow (.var "y2") (.var "m")))))))) := by rfl
      rw [e1, e2]
      apply subst_congr
      · refine (List.Forall₂.cons ⟨rfl, ?_⟩ (List.Forall₂.cons ⟨rfl, ?_⟩ List.Forall₂.nil))
        · simp [eval, Function.update, hm1]
          field_simp
          linear_combination (-w) * hr0
        · simp [eval, Function.update, hm1]
          field_simp
          first
          | ring
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> simp [Defined, eval, hm1, hd, hzd])

theorem rubi33r37Nondeg_real : rubi33r37Nondeg.Holds .real := rubi33r37Nondeg_holds Interp.real
theorem rubi33r37Nondeg_complex : rubi33r37Nondeg.Holds .complex := rubi33r37Nondeg_holds Interp.complex

/-- RUBI rubi33r46Nondeg: `x ↦ k + l x`, up to identities on 2 subterms. -/
theorem rubi33r46Nondeg_holds {𝕜 : Type} [NontriviallyNormedField 𝕜] (I : Interp 𝕜) :
    AntiderivSubstHolds I "x" rubi33r46Nondeg.conditions rubi33r46Nondeg.body rubi33r46Nondeg.result rubi33r46Nondeg.integrals
      rubi33r46Nondeg.substs := by
  have hm1 : I.toInt? (-1 : 𝕜) = some (-1) := by simpa using Interp.toInt?_cast I (-1)
  have hd0 : ∀ env : String → 𝕜, (∀ k ∈ rubi33r46Nondeg.conditions, k.Holds I env) → env "l" ≠ 0 :=
    fun env hcs => by simpa [Cond.Holds, Defined, eval] using hcs (.ne (.var "l") (.int 0)) (by simp [rubi33r46Nondeg])
  exact antiderivSubst_affine_of (I := I) rubi33r46Nondeg.body (rubi33r46Nondeg.integrals.head!.2) (c := "k") (d := "l")
    (by decide) (by decide) (by decide) hd0 (fun env hcs w => by
      have hd := hd0 env hcs
      have e1 : rubi33r46Nondeg.body = Expr.subst [("y1", (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))), ("y2", (.app2 .add (.var "i") (.app2 .mul (.var "j") (.var "x"))))] ((.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "k") (.app2 .mul (.var "l") (.var "x"))) (.var "r")) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "y1") (.var "n"))))))) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.app1 .ln (.app2 .mul (.var "h") (.pow (.var "y2") (.var "m")))))))) := by rfl
      have e2 : Expr.subst [("x", affineSub "k" "l")] (rubi33r46Nondeg.integrals.head!.2) =
          Expr.subst [("y1", (.app2 .add (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "e") (.var "k")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "l")))) (.pow (.var "l") (.int (-1)))) (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.var "k") (.app2 .mul (.var "l") (.var "x")))) (.pow (.var "l") (.int (-1)))))), ("y2", (.app2 .add (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "j") (.var "k")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "i")) (.var "l")))) (.pow (.var "l") (.int (-1)))) (.app2 .mul (.app2 .mul (.var "j") (.app2 .add (.var "k") (.app2 .mul (.var "l") (.var "x")))) (.pow (.var "l") (.int (-1))))))] ((.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "k") (.app2 .mul (.var "l") (.var "x"))) (.var "r")) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "y1") (.var "n"))))))) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.app1 .ln (.app2 .mul (.var "h") (.pow (.var "y2") (.var "m")))))))) := by rfl
      rw [e1, e2]
      apply subst_congr
      · refine (List.Forall₂.cons ⟨rfl, ?_⟩ (List.Forall₂.cons ⟨rfl, ?_⟩ List.Forall₂.nil))
        · simp [eval, Function.update, hm1]
          field_simp
          first
          | ring
        · simp [eval, Function.update, hm1]
          field_simp
          first
          | ring
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> simp [Defined, eval, hm1, hd])

theorem rubi33r46Nondeg_real : rubi33r46Nondeg.Holds .real := rubi33r46Nondeg_holds Interp.real
theorem rubi33r46Nondeg_complex : rubi33r46Nondeg.Holds .complex := rubi33r46Nondeg_holds Interp.complex

/-- RUBI rubi4112r75Nondeg: `x ↦ e + f x`, up to identities on 1 subterm. -/
theorem rubi4112r75Nondeg_holds {𝕜 : Type} [NontriviallyNormedField 𝕜] (I : Interp 𝕜) :
    AntiderivSubstHolds I "x" rubi4112r75Nondeg.conditions rubi4112r75Nondeg.body rubi4112r75Nondeg.result rubi4112r75Nondeg.integrals
      rubi4112r75Nondeg.substs := by
  have hm1 : I.toInt? (-1 : 𝕜) = some (-1) := by simpa using Interp.toInt?_cast I (-1)
  have hd0 : ∀ env : String → 𝕜, (∀ k ∈ rubi4112r75Nondeg.conditions, k.Holds I env) → env "f" ≠ 0 :=
    fun env hcs => by simpa [Cond.Holds, Defined, eval] using hcs (.ne (.var "f") (.int 0)) (by simp [rubi4112r75Nondeg])
  exact antiderivSubst_affine_of (I := I) rubi4112r75Nondeg.body (rubi4112r75Nondeg.integrals.head!.2) (c := "e") (d := "f")
    (by decide) (by decide) (by decide) hd0 (fun env hcs w => by
      have hd := hd0 env hcs
      have hr0 := hcs (.eq (.app2 .add (.app2 .mul (.var "f") (.var "g")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.var "h"))) (.int 0)) (by simp [rubi4112r75Nondeg])
      simp [Cond.Holds, Defined, eval] at hr0
      have e1 : rubi4112r75Nondeg.body = Expr.subst [("y1", (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))))] ((.app2 .mul (.pow (.var "y1") (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "n"))))))) (.var "p")))) := by rfl
      have e2 : Expr.subst [("x", affineSub "e" "f")] (rubi4112r75Nondeg.integrals.head!.2) =
          Expr.subst [("y1", (.app2 .mul (.app2 .mul (.var "h") (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.pow (.var "f") (.int (-1)))))] ((.app2 .mul (.pow (.var "y1") (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "n"))))))) (.var "p")))) := by rfl
      rw [e1, e2]
      apply subst_congr
      · refine (List.Forall₂.cons ⟨rfl, ?_⟩ List.Forall₂.nil)
        · simp [eval, Function.update, hm1]
          field_simp
          linear_combination (1) * hr0
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl
        simp [Defined, eval, hm1, hd])

theorem rubi4112r75Nondeg_real : rubi4112r75Nondeg.Holds .real := rubi4112r75Nondeg_holds Interp.real
theorem rubi4112r75Nondeg_complex : rubi4112r75Nondeg.Holds .complex := rubi4112r75Nondeg_holds Interp.complex

/-- RUBI rubi4112r76Nondeg: `x ↦ e + f x`, up to identities on 1 subterm. -/
theorem rubi4112r76Nondeg_holds {𝕜 : Type} [NontriviallyNormedField 𝕜] (I : Interp 𝕜) :
    AntiderivSubstHolds I "x" rubi4112r76Nondeg.conditions rubi4112r76Nondeg.body rubi4112r76Nondeg.result rubi4112r76Nondeg.integrals
      rubi4112r76Nondeg.substs := by
  have hm1 : I.toInt? (-1 : 𝕜) = some (-1) := by simpa using Interp.toInt?_cast I (-1)
  have hd0 : ∀ env : String → 𝕜, (∀ k ∈ rubi4112r76Nondeg.conditions, k.Holds I env) → env "f" ≠ 0 :=
    fun env hcs => by simpa [Cond.Holds, Defined, eval] using hcs (.ne (.var "f") (.int 0)) (by simp [rubi4112r76Nondeg])
  exact antiderivSubst_affine_of (I := I) rubi4112r76Nondeg.body (rubi4112r76Nondeg.integrals.head!.2) (c := "e") (d := "f")
    (by decide) (by decide) (by decide) hd0 (fun env hcs w => by
      have hd := hd0 env hcs
      have hr0 := hcs (.eq (.app2 .add (.app2 .mul (.var "f") (.var "g")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.var "h"))) (.int 0)) (by simp [rubi4112r76Nondeg])
      simp [Cond.Holds, Defined, eval] at hr0
      have e1 : rubi4112r76Nondeg.body = Expr.subst [("y1", (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))))] ((.app2 .mul (.pow (.var "y1") (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "n"))))))) (.var "p")))) := by rfl
      have e2 : Expr.subst [("x", affineSub "e" "f")] (rubi4112r76Nondeg.integrals.head!.2) =
          Expr.subst [("y1", (.app2 .mul (.app2 .mul (.var "h") (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.pow (.var "f") (.int (-1)))))] ((.app2 .mul (.pow (.var "y1") (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "n"))))))) (.var "p")))) := by rfl
      rw [e1, e2]
      apply subst_congr
      · refine (List.Forall₂.cons ⟨rfl, ?_⟩ List.Forall₂.nil)
        · simp [eval, Function.update, hm1]
          field_simp
          linear_combination (1) * hr0
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl
        simp [Defined, eval, hm1, hd])

theorem rubi4112r76Nondeg_real : rubi4112r76Nondeg.Holds .real := rubi4112r76Nondeg_holds Interp.real
theorem rubi4112r76Nondeg_complex : rubi4112r76Nondeg.Holds .complex := rubi4112r76Nondeg_holds Interp.complex

/-- RUBI rubi516r3Nondeg: `x ↦ c + d x`, up to identities on 1 subterm. -/
theorem rubi516r3Nondeg_holds {𝕜 : Type} [NontriviallyNormedField 𝕜] (I : Interp 𝕜) :
    AntiderivSubstHolds I "x" rubi516r3Nondeg.conditions rubi516r3Nondeg.body rubi516r3Nondeg.result rubi516r3Nondeg.integrals
      rubi516r3Nondeg.substs := by
  have hm1 : I.toInt? (-1 : 𝕜) = some (-1) := by simpa using Interp.toInt?_cast I (-1)
  have hd0 : ∀ env : String → 𝕜, (∀ k ∈ rubi516r3Nondeg.conditions, k.Holds I env) → env "d" ≠ 0 :=
    fun env hcs => by simpa [Cond.Holds, Defined, eval] using hcs (.ne (.var "d") (.int 0)) (by simp [rubi516r3Nondeg])
  exact antiderivSubst_affine_of (I := I) rubi516r3Nondeg.body (rubi516r3Nondeg.integrals.head!.2) (c := "c") (d := "d")
    (by decide) (by decide) (by decide) hd0 (fun env hcs w => by
      have hd := hd0 env hcs
      have e1 : rubi516r3Nondeg.body = Expr.subst [("y1", (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))] ((.app2 .mul (.pow (.var "y1") (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.var "n")))) := by rfl
      have e2 : Expr.subst [("x", affineSub "c" "d")] (rubi516r3Nondeg.integrals.head!.2) =
          Expr.subst [("y1", (.app2 .add (.app2 .mul (.app2 .add (.app2 .mul (.var "d") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f"))) (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.var "f") (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.pow (.var "d") (.int (-1))))))] ((.app2 .mul (.pow (.var "y1") (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.var "n")))) := by rfl
      rw [e1, e2]
      apply subst_congr
      · refine (List.Forall₂.cons ⟨rfl, ?_⟩ List.Forall₂.nil)
        · simp [eval, Function.update, hm1]
          field_simp
          first
          | ring
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl
        simp [Defined, eval, hm1, hd])

theorem rubi516r3Nondeg_real : rubi516r3Nondeg.Holds .real := rubi516r3Nondeg_holds Interp.real

/-- RUBI rubi516r4Nondeg: `x ↦ c + d x`, up to identities on 1 subterm. -/
theorem rubi516r4Nondeg_holds {𝕜 : Type} [NontriviallyNormedField 𝕜] (I : Interp 𝕜) :
    AntiderivSubstHolds I "x" rubi516r4Nondeg.conditions rubi516r4Nondeg.body rubi516r4Nondeg.result rubi516r4Nondeg.integrals
      rubi516r4Nondeg.substs := by
  have hm1 : I.toInt? (-1 : 𝕜) = some (-1) := by simpa using Interp.toInt?_cast I (-1)
  have hd0 : ∀ env : String → 𝕜, (∀ k ∈ rubi516r4Nondeg.conditions, k.Holds I env) → env "d" ≠ 0 :=
    fun env hcs => by simpa [Cond.Holds, Defined, eval] using hcs (.ne (.var "d") (.int 0)) (by simp [rubi516r4Nondeg])
  exact antiderivSubst_affine_of (I := I) rubi516r4Nondeg.body (rubi516r4Nondeg.integrals.head!.2) (c := "c") (d := "d")
    (by decide) (by decide) (by decide) hd0 (fun env hcs w => by
      have hd := hd0 env hcs
      have e1 : rubi516r4Nondeg.body = Expr.subst [("y1", (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))] ((.app2 .mul (.pow (.var "y1") (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.var "n")))) := by rfl
      have e2 : Expr.subst [("x", affineSub "c" "d")] (rubi516r4Nondeg.integrals.head!.2) =
          Expr.subst [("y1", (.app2 .add (.app2 .mul (.app2 .add (.app2 .mul (.var "d") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f"))) (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.var "f") (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.pow (.var "d") (.int (-1))))))] ((.app2 .mul (.pow (.var "y1") (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.var "n")))) := by rfl
      rw [e1, e2]
      apply subst_congr
      · refine (List.Forall₂.cons ⟨rfl, ?_⟩ List.Forall₂.nil)
        · simp [eval, Function.update, hm1]
          field_simp
          first
          | ring
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl
        simp [Defined, eval, hm1, hd])

theorem rubi516r4Nondeg_real : rubi516r4Nondeg.Holds .real := rubi516r4Nondeg_holds Interp.real

/-- RUBI rubi535r5Nondeg: `x ↦ c + d x`, up to identities on 1 subterm. -/
theorem rubi535r5Nondeg_holds {𝕜 : Type} [NontriviallyNormedField 𝕜] (I : Interp 𝕜) :
    AntiderivSubstHolds I "x" rubi535r5Nondeg.conditions rubi535r5Nondeg.body rubi535r5Nondeg.result rubi535r5Nondeg.integrals
      rubi535r5Nondeg.substs := by
  have hm1 : I.toInt? (-1 : 𝕜) = some (-1) := by simpa using Interp.toInt?_cast I (-1)
  have hd0 : ∀ env : String → 𝕜, (∀ k ∈ rubi535r5Nondeg.conditions, k.Holds I env) → env "d" ≠ 0 :=
    fun env hcs => by simpa [Cond.Holds, Defined, eval] using hcs (.ne (.var "d") (.int 0)) (by simp [rubi535r5Nondeg])
  exact antiderivSubst_affine_of (I := I) rubi535r5Nondeg.body (rubi535r5Nondeg.integrals.head!.2) (c := "c") (d := "d")
    (by decide) (by decide) (by decide) hd0 (fun env hcs w => by
      have hd := hd0 env hcs
      have hr0 := hcs (.eq (.app2 .add (.app2 .mul (.var "d") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f"))) (.int 0)) (by simp [rubi535r5Nondeg])
      simp [Cond.Holds, Defined, eval] at hr0
      have e1 : rubi535r5Nondeg.body = Expr.subst [("y1", (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))] ((.app2 .mul (.pow (.var "y1") (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.var "p")))) := by rfl
      have e2 : Expr.subst [("x", affineSub "c" "d")] (rubi535r5Nondeg.integrals.head!.2) =
          Expr.subst [("y1", (.app2 .mul (.app2 .mul (.var "f") (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.pow (.var "d") (.int (-1)))))] ((.app2 .mul (.pow (.var "y1") (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.var "p")))) := by rfl
      rw [e1, e2]
      apply subst_congr
      · refine (List.Forall₂.cons ⟨rfl, ?_⟩ List.Forall₂.nil)
        · simp [eval, Function.update, hm1]
          field_simp
          linear_combination (1) * hr0
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl
        simp [Defined, eval, hm1, hd])

theorem rubi535r5Nondeg_real : rubi535r5Nondeg.Holds .real := rubi535r5Nondeg_holds Interp.real
theorem rubi535r5Nondeg_complex : rubi535r5Nondeg.Holds .complex := rubi535r5Nondeg_holds Interp.complex

/-- RUBI rubi535r6Nondeg: `x ↦ c + d x`, up to identities on 1 subterm. -/
theorem rubi535r6Nondeg_holds {𝕜 : Type} [NontriviallyNormedField 𝕜] (I : Interp 𝕜) :
    AntiderivSubstHolds I "x" rubi535r6Nondeg.conditions rubi535r6Nondeg.body rubi535r6Nondeg.result rubi535r6Nondeg.integrals
      rubi535r6Nondeg.substs := by
  have hm1 : I.toInt? (-1 : 𝕜) = some (-1) := by simpa using Interp.toInt?_cast I (-1)
  have hd0 : ∀ env : String → 𝕜, (∀ k ∈ rubi535r6Nondeg.conditions, k.Holds I env) → env "d" ≠ 0 :=
    fun env hcs => by simpa [Cond.Holds, Defined, eval] using hcs (.ne (.var "d") (.int 0)) (by simp [rubi535r6Nondeg])
  exact antiderivSubst_affine_of (I := I) rubi535r6Nondeg.body (rubi535r6Nondeg.integrals.head!.2) (c := "c") (d := "d")
    (by decide) (by decide) (by decide) hd0 (fun env hcs w => by
      have hd := hd0 env hcs
      have hr0 := hcs (.eq (.app2 .add (.app2 .mul (.var "d") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f"))) (.int 0)) (by simp [rubi535r6Nondeg])
      simp [Cond.Holds, Defined, eval] at hr0
      have e1 : rubi535r6Nondeg.body = Expr.subst [("y1", (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))] ((.app2 .mul (.pow (.var "y1") (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))))) (.var "p")))) := by rfl
      have e2 : Expr.subst [("x", affineSub "c" "d")] (rubi535r6Nondeg.integrals.head!.2) =
          Expr.subst [("y1", (.app2 .mul (.app2 .mul (.var "f") (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.pow (.var "d") (.int (-1)))))] ((.app2 .mul (.pow (.var "y1") (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))))) (.var "p")))) := by rfl
      rw [e1, e2]
      apply subst_congr
      · refine (List.Forall₂.cons ⟨rfl, ?_⟩ List.Forall₂.nil)
        · simp [eval, Function.update, hm1]
          field_simp
          linear_combination (1) * hr0
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl
        simp [Defined, eval, hm1, hd])

theorem rubi535r6Nondeg_real : rubi535r6Nondeg.Holds .real := rubi535r6Nondeg_holds Interp.real
theorem rubi535r6Nondeg_complex : rubi535r6Nondeg.Holds .complex := rubi535r6Nondeg_holds Interp.complex

/-- RUBI rubi535r9Nondeg: `x ↦ c + d x`, up to identities on 1 subterm. -/
theorem rubi535r9Nondeg_holds {𝕜 : Type} [NontriviallyNormedField 𝕜] (I : Interp 𝕜) :
    AntiderivSubstHolds I "x" rubi535r9Nondeg.conditions rubi535r9Nondeg.body rubi535r9Nondeg.result rubi535r9Nondeg.integrals
      rubi535r9Nondeg.substs := by
  have hm1 : I.toInt? (-1 : 𝕜) = some (-1) := by simpa using Interp.toInt?_cast I (-1)
  have hd0 : ∀ env : String → 𝕜, (∀ k ∈ rubi535r9Nondeg.conditions, k.Holds I env) → env "d" ≠ 0 :=
    fun env hcs => by simpa [Cond.Holds, Defined, eval] using hcs (.ne (.var "d") (.int 0)) (by simp [rubi535r9Nondeg])
  exact antiderivSubst_affine_of (I := I) rubi535r9Nondeg.body (rubi535r9Nondeg.integrals.head!.2) (c := "c") (d := "d")
    (by decide) (by decide) (by decide) hd0 (fun env hcs w => by
      have hd := hd0 env hcs
      have e1 : rubi535r9Nondeg.body = Expr.subst [("y1", (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))] ((.app2 .mul (.pow (.var "y1") (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.var "p")))) := by rfl
      have e2 : Expr.subst [("x", affineSub "c" "d")] (rubi535r9Nondeg.integrals.head!.2) =
          Expr.subst [("y1", (.app2 .add (.app2 .mul (.app2 .add (.app2 .mul (.var "d") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f"))) (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.var "f") (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.pow (.var "d") (.int (-1))))))] ((.app2 .mul (.pow (.var "y1") (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.var "p")))) := by rfl
      rw [e1, e2]
      apply subst_congr
      · refine (List.Forall₂.cons ⟨rfl, ?_⟩ List.Forall₂.nil)
        · simp [eval, Function.update, hm1]
          field_simp
          first
          | ring
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl
        simp [Defined, eval, hm1, hd])

theorem rubi535r9Nondeg_real : rubi535r9Nondeg.Holds .real := rubi535r9Nondeg_holds Interp.real
theorem rubi535r9Nondeg_complex : rubi535r9Nondeg.Holds .complex := rubi535r9Nondeg_holds Interp.complex

/-- RUBI rubi535r10Nondeg: `x ↦ c + d x`, up to identities on 1 subterm. -/
theorem rubi535r10Nondeg_holds {𝕜 : Type} [NontriviallyNormedField 𝕜] (I : Interp 𝕜) :
    AntiderivSubstHolds I "x" rubi535r10Nondeg.conditions rubi535r10Nondeg.body rubi535r10Nondeg.result rubi535r10Nondeg.integrals
      rubi535r10Nondeg.substs := by
  have hm1 : I.toInt? (-1 : 𝕜) = some (-1) := by simpa using Interp.toInt?_cast I (-1)
  have hd0 : ∀ env : String → 𝕜, (∀ k ∈ rubi535r10Nondeg.conditions, k.Holds I env) → env "d" ≠ 0 :=
    fun env hcs => by simpa [Cond.Holds, Defined, eval] using hcs (.ne (.var "d") (.int 0)) (by simp [rubi535r10Nondeg])
  exact antiderivSubst_affine_of (I := I) rubi535r10Nondeg.body (rubi535r10Nondeg.integrals.head!.2) (c := "c") (d := "d")
    (by decide) (by decide) (by decide) hd0 (fun env hcs w => by
      have hd := hd0 env hcs
      have e1 : rubi535r10Nondeg.body = Expr.subst [("y1", (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))] ((.app2 .mul (.pow (.var "y1") (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))))) (.var "p")))) := by rfl
      have e2 : Expr.subst [("x", affineSub "c" "d")] (rubi535r10Nondeg.integrals.head!.2) =
          Expr.subst [("y1", (.app2 .add (.app2 .mul (.app2 .add (.app2 .mul (.var "d") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f"))) (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.var "f") (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.pow (.var "d") (.int (-1))))))] ((.app2 .mul (.pow (.var "y1") (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))))) (.var "p")))) := by rfl
      rw [e1, e2]
      apply subst_congr
      · refine (List.Forall₂.cons ⟨rfl, ?_⟩ List.Forall₂.nil)
        · simp [eval, Function.update, hm1]
          field_simp
          first
          | ring
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl
        simp [Defined, eval, hm1, hd])

theorem rubi535r10Nondeg_real : rubi535r10Nondeg.Holds .real := rubi535r10Nondeg_holds Interp.real
theorem rubi535r10Nondeg_complex : rubi535r10Nondeg.Holds .complex := rubi535r10Nondeg_holds Interp.complex

end OSR.IntegrationRec302
