import OSR.IntegrationRec300

/-! # Affine substitutions up to an algebraic identity

`antiderivSubst_affine_of` extends `antiderivSubst_affine` to rules whose integrand equals the
residual integrand with `x ↦ c + d x` only up to algebraic identities on some subterms: the
integrand is `K[y := A]` and the substituted residual integrand `K[y := B]`, where each `A` and
`B` have the same value and each `B` is defined. -/

namespace OSR.IntegrationRec301
open OSR OSR.Calculus OSR.IntegrationNum1 OSR.IntegrationRec300 Filter Topology

section Congr

variable {α : Type} [Field α]

theorem env_congr (I : Interp α) (ρ : String → α) :
    ∀ σ σ' : Subst, List.Forall₂ (fun p q => p.1 = q.1 ∧ eval I ρ p.2 = eval I ρ q.2) σ σ' →
      ∀ n, Subst.env I ρ σ n = Subst.env I ρ σ' n
  | [], [], _, n => rfl
  | p :: σ, q :: σ', .cons ⟨hk, hv⟩ h, n => by
    have ih := env_congr I ρ σ σ' h n
    by_cases hn : p.1 = n
    · simp [Subst.env, Subst.apply, Subst.find?, hn, ← hk, hv]
    · simpa [Subst.env, Subst.apply, Subst.find?, hn, ← hk] using ih

theorem apply_defined (I : Interp α) (ρ : String → α) :
    ∀ σ : Subst, (∀ p ∈ σ, Defined I ρ p.2) → ∀ n, Defined I ρ (σ.apply n)
  | [], _, n => by simp [Subst.apply, Subst.find?, Defined]
  | p :: σ, h, n => by
    by_cases hn : p.1 = n
    · simpa [Subst.apply, Subst.find?, hn] using h p (by simp)
    · have := apply_defined I ρ σ (fun q hq => h q (by simp [hq])) n
      simpa [Subst.apply, Subst.find?, hn] using this

/-- Replacing subterms by others with the same values keeps the value, and keeps definedness
when the new subterms are defined. -/
theorem subst_congr (I : Interp α) (ρ : String → α) (K : Expr) (σ σ' : Subst)
    (h : List.Forall₂ (fun p q => p.1 = q.1 ∧ eval I ρ p.2 = eval I ρ q.2) σ σ')
    (hd : ∀ p ∈ σ', Defined I ρ p.2) :
    (Defined I ρ (K.subst σ) → Defined I ρ (K.subst σ')) ∧
      eval I ρ (K.subst σ) = eval I ρ (K.subst σ') := by
  have henv : Subst.env I ρ σ = Subst.env I ρ σ' := funext (env_congr I ρ σ σ' h)
  refine ⟨fun hK => ?_, by rw [eval_subst, eval_subst, henv]⟩
  rw [defined_subst] at hK ⊢
  exact ⟨henv ▸ hK.1, fun n _ => apply_defined I ρ σ' hd n⟩

end Congr

section Affine

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

/-- **Affine substitution up to identities.** -/
theorem antiderivSubst_affine_of {I : Interp 𝕜} {cs : List Cond} (F H : Expr) {c d : String}
    (hc : c ≠ "x") (hd : d ≠ "x") (hdI : d ≠ "I1")
    (hd0 : ∀ env : String → 𝕜, (∀ k ∈ cs, k.Holds I env) → env d ≠ 0)
    (hF : ∀ env : String → 𝕜, (∀ k ∈ cs, k.Holds I env) → ∀ w,
      (Defined I (Function.update env "x" w) F →
        Defined I (Function.update env "x" w) (H.subst [("x", affineSub c d)])) ∧
      eval I (Function.update env "x" w) F =
        eval I (Function.update env "x" w) (H.subst [("x", affineSub c d)])) :
    AntiderivSubstHolds I "x" cs F
      (.app2 .mul (.app2 .mul (.int 1) (.pow (.var d) (.int (-1)))) (.var "I1"))
      [("I1", H)] [("I1", affineSub c d)] := by
  intro env hcs t hFt
  have h := antiderivSubst_affine (I := I) (cs := cs) H hc hd hdI hd0 env hcs t
    (hFt.mono fun w hw => (hF env hcs w).1 hw)
  refine ⟨h.1, fun Φ hΦ => ?_⟩
  obtain ⟨h1, h2⟩ := h.2 Φ hΦ
  exact ⟨h1, by rwa [(hF env hcs t).2]⟩

end Affine

end OSR.IntegrationRec301
