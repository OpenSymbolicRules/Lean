import OSR.IntegrationNum1

/-! # Strengthened variants proved by an affine substitution

A rule with one substitution `u = c + d x`, whose integrand is the residual integrand with `x`
replaced by `u` and whose result is `(1 * d⁻¹) * I1(u)`, holds in every interpretation as soon as
its conditions give `d ≠ 0`: evaluation commutes with substitution (`eval_subst`,
`defined_subst`), the inverse substitution `x = (u - c) / d` carries the definedness of the
integrand near `t` to that of the residual integrand near `u(t)`, and the chain rule gives the
derivative. `antiderivSubst_affine` states this once; each rule is an instance. -/

namespace OSR.IntegrationRec300
open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

section Affine

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

/-- The affine substitution `c + d x`. -/
def affineSub (c d : String) : Expr := .app2 .add (.var c) (.app2 .mul (.var d) (.var "x"))

theorem eval_affineSub (I : Interp 𝕜) (env : String → 𝕜) {c d : String} (hc : c ≠ "x")
    (hd : d ≠ "x") (v : 𝕜) :
    eval I (Function.update env "x" v) (affineSub c d) = env c + env d * v := by
  simp [affineSub, eval, Function.update, hc, hd]

theorem defined_affineSub (I : Interp 𝕜) (env : String → 𝕜) (c d : String) :
    Defined I env (affineSub c d) := by
  simp [affineSub, Defined]

/-- The assignment induced by `x ↦ c + d x` at `w` is the update at `c + d w`. -/
theorem subst_env_affine (I : Interp 𝕜) (env : String → 𝕜) {c d : String} (hc : c ≠ "x")
    (hd : d ≠ "x") (w : 𝕜) :
    Subst.env I (Function.update env "x" w) [("x", affineSub c d)] =
      Function.update env "x" (env c + env d * w) := by
  funext n
  by_cases hn : n = "x"
  · subst hn
    simp [Subst.env, Subst.apply, Subst.find?, eval_affineSub I env hc hd]
  · have : ("x" = n) = False := by simp [Ne.symm hn]
    simp [Subst.env, Subst.apply, Subst.find?, Ne.symm hn, eval, Function.update, hn]

/-- **Affine substitution.** -/
theorem antiderivSubst_affine {I : Interp 𝕜} {cs : List Cond} (H : Expr) {c d : String}
    (hc : c ≠ "x") (hd : d ≠ "x") (hdI : d ≠ "I1")
    (hd0 : ∀ env : String → 𝕜, (∀ k ∈ cs, k.Holds I env) → env d ≠ 0) :
    AntiderivSubstHolds I "x" cs (H.subst [("x", affineSub c d)])
      (.app2 .mul (.app2 .mul (.int 1) (.pow (.var d) (.int (-1)))) (.var "I1"))
      [("I1", H)] [("I1", affineSub c d)] := by
  intro env hcs t hF
  have h0 := hd0 env hcs
  set U : 𝕜 → 𝕜 := fun v => env c + env d * v with hU
  have hσ := subst_env_affine I env hc hd
  -- The integrand at `w` is the residual integrand at `U w`.
  have hdefw : ∀ w, Defined I (Function.update env "x" w) (H.subst [("x", affineSub c d)]) →
      Defined I (Function.update env "x" (U w)) H := by
    intro w hw
    rw [defined_subst, hσ] at hw
    exact hw.1
  have hval : ∀ w, eval I (Function.update env "x" w) (H.subst [("x", affineSub c d)]) =
      eval I (Function.update env "x" (U w)) H := by
    intro w
    rw [eval_subst, hσ]
  have hsub : substAt I env [("I1", affineSub c d)] "x" "I1" t = U t := by
    simp [substAt, eval_affineSub I env hc hd, hU]
  have hm1 : I.toInt? (-1 : 𝕜) = some (-1) := by simpa using Interp.toInt?_cast I (-1)
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    refine ⟨Filter.Eventually.of_forall fun w g hg => ?_, ?_⟩
    · simp only [List.lookup_cons, beq_self_eq_true, Option.some.injEq] at hg
      subst hg
      exact defined_affineSub I _ c d
    · rw [hsub]
      -- `x = (u - c) / d` maps a neighbourhood of `U t` into one of `t`.
      have hinv : Tendsto (fun u => (u - env c) / env d) (𝓝 (U t)) (𝓝 t) := by
        have hcont : Continuous (fun u : 𝕜 => (u - env c) / env d) := by fun_prop
        have := hcont.tendsto (U t)
        rwa [show (U t - env c) / env d = t by simp [hU]; field_simp] at this
      filter_upwards [hinv.eventually hF] with u hu
      have hUu : U ((u - env c) / env d) = u := by simp [hU]; field_simp; ring
      simpa [hUu] using hdefw _ hu
  · intro Φ hΦ
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    rw [hsub] at hΦ
    refine ⟨Filter.Eventually.of_forall fun w => ?_, ?_⟩
    · simp [Defined, eval, substEnv, Function.update, hm1, h0, hd, hdI]
    · have hfun : (fun v => eval I (substEnv I env (([("I1", H)] : List (String × Expr)).map (·.1))
          [("I1", affineSub c d)] Φ "x" v)
          (.app2 .mul (.app2 .mul (.int 1) (.pow (.var d) (.int (-1)))) (.var "I1"))) =
          fun v => (env d)⁻¹ * Φ "I1" (U v) := by
        funext v
        simp [eval, substEnv, substAt, Function.update, hm1, hd, hdI, eval_affineSub I env hc hd, hU]
      rw [hfun, hval]
      have hL : HasDerivAt U (env d) t := by
        simpa [hU] using ((hasDerivAt_id t).const_mul (env d)).const_add (env c)
      have h := (hΦ.comp t hL).const_mul (env d)⁻¹
      convert h using 1
      · funext v
        simp
      · field_simp

end Affine

/-! ## Instances -/

/-- RUBI 3.3 #1: `x ↦ d + e x`. -/
theorem rubi33r1Nondeg_holds {𝕜 : Type} [NontriviallyNormedField 𝕜] (I : Interp 𝕜) :
    AntiderivSubstHolds I "x" rubi33r1Nondeg.conditions rubi33r1Nondeg.body rubi33r1Nondeg.result rubi33r1Nondeg.integrals
      rubi33r1Nondeg.substs :=
  antiderivSubst_affine (I := I) (rubi33r1Nondeg.integrals.head!.2) (c := "d") (d := "e")
    (by decide) (by decide) (by decide) (fun env hcs => by
      simpa [Cond.Holds, Defined, eval] using hcs (.ne (.var "e") (.int 0)) (by simp [rubi33r1Nondeg]))

theorem rubi33r1Nondeg_real : rubi33r1Nondeg.Holds .real := rubi33r1Nondeg_holds Interp.real
theorem rubi33r1Nondeg_complex : rubi33r1Nondeg.Holds .complex := rubi33r1Nondeg_holds Interp.complex

/-- RUBI 3.4 #28: `x ↦ f + g x`. -/
theorem rubi34r28Nondeg_holds {𝕜 : Type} [NontriviallyNormedField 𝕜] (I : Interp 𝕜) :
    AntiderivSubstHolds I "x" rubi34r28Nondeg.conditions rubi34r28Nondeg.body rubi34r28Nondeg.result rubi34r28Nondeg.integrals
      rubi34r28Nondeg.substs :=
  antiderivSubst_affine (I := I) (rubi34r28Nondeg.integrals.head!.2) (c := "f") (d := "g")
    (by decide) (by decide) (by decide) (fun env hcs => by
      simpa [Cond.Holds, Defined, eval] using hcs (.ne (.var "g") (.int 0)) (by simp [rubi34r28Nondeg]))

theorem rubi34r28Nondeg_real : rubi34r28Nondeg.Holds .real := rubi34r28Nondeg_holds Interp.real
theorem rubi34r28Nondeg_complex : rubi34r28Nondeg.Holds .complex := rubi34r28Nondeg_holds Interp.complex

/-- RUBI 5.1.6 #1: `x ↦ c + d x`. -/
theorem rubi516r1Nondeg_holds {𝕜 : Type} [NontriviallyNormedField 𝕜] (I : Interp 𝕜) :
    AntiderivSubstHolds I "x" rubi516r1Nondeg.conditions rubi516r1Nondeg.body rubi516r1Nondeg.result rubi516r1Nondeg.integrals
      rubi516r1Nondeg.substs :=
  antiderivSubst_affine (I := I) (rubi516r1Nondeg.integrals.head!.2) (c := "c") (d := "d")
    (by decide) (by decide) (by decide) (fun env hcs => by
      simpa [Cond.Holds, Defined, eval] using hcs (.ne (.var "d") (.int 0)) (by simp [rubi516r1Nondeg]))

theorem rubi516r1Nondeg_real : rubi516r1Nondeg.Holds .real := rubi516r1Nondeg_holds Interp.real

/-- RUBI 5.1.6 #2: `x ↦ c + d x`. -/
theorem rubi516r2Nondeg_holds {𝕜 : Type} [NontriviallyNormedField 𝕜] (I : Interp 𝕜) :
    AntiderivSubstHolds I "x" rubi516r2Nondeg.conditions rubi516r2Nondeg.body rubi516r2Nondeg.result rubi516r2Nondeg.integrals
      rubi516r2Nondeg.substs :=
  antiderivSubst_affine (I := I) (rubi516r2Nondeg.integrals.head!.2) (c := "c") (d := "d")
    (by decide) (by decide) (by decide) (fun env hcs => by
      simpa [Cond.Holds, Defined, eval] using hcs (.ne (.var "d") (.int 0)) (by simp [rubi516r2Nondeg]))

theorem rubi516r2Nondeg_real : rubi516r2Nondeg.Holds .real := rubi516r2Nondeg_holds Interp.real

/-- RUBI 5.3.5 #1: `x ↦ c + d x`. -/
theorem rubi535r1Nondeg_holds {𝕜 : Type} [NontriviallyNormedField 𝕜] (I : Interp 𝕜) :
    AntiderivSubstHolds I "x" rubi535r1Nondeg.conditions rubi535r1Nondeg.body rubi535r1Nondeg.result rubi535r1Nondeg.integrals
      rubi535r1Nondeg.substs :=
  antiderivSubst_affine (I := I) (rubi535r1Nondeg.integrals.head!.2) (c := "c") (d := "d")
    (by decide) (by decide) (by decide) (fun env hcs => by
      simpa [Cond.Holds, Defined, eval] using hcs (.ne (.var "d") (.int 0)) (by simp [rubi535r1Nondeg]))

theorem rubi535r1Nondeg_real : rubi535r1Nondeg.Holds .real := rubi535r1Nondeg_holds Interp.real
theorem rubi535r1Nondeg_complex : rubi535r1Nondeg.Holds .complex := rubi535r1Nondeg_holds Interp.complex

/-- RUBI 5.3.5 #2: `x ↦ c + d x`. -/
theorem rubi535r2Nondeg_holds {𝕜 : Type} [NontriviallyNormedField 𝕜] (I : Interp 𝕜) :
    AntiderivSubstHolds I "x" rubi535r2Nondeg.conditions rubi535r2Nondeg.body rubi535r2Nondeg.result rubi535r2Nondeg.integrals
      rubi535r2Nondeg.substs :=
  antiderivSubst_affine (I := I) (rubi535r2Nondeg.integrals.head!.2) (c := "c") (d := "d")
    (by decide) (by decide) (by decide) (fun env hcs => by
      simpa [Cond.Holds, Defined, eval] using hcs (.ne (.var "d") (.int 0)) (by simp [rubi535r2Nondeg]))

theorem rubi535r2Nondeg_real : rubi535r2Nondeg.Holds .real := rubi535r2Nondeg_holds Interp.real
theorem rubi535r2Nondeg_complex : rubi535r2Nondeg.Holds .complex := rubi535r2Nondeg_holds Interp.complex

end OSR.IntegrationRec300
