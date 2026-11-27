module

public import LorentzianCalderon.Causal.Basic

public section

/-!
# Lifting paths through local diffeomorphisms

A smooth map `Ψ` with injective differential on an open set `U` has smooth local inverses
(`exists_localInverse`), and a continuous lift `c` in `U` of a path `c' = Ψ ∘ c` is a path, with
velocities `dΨ⁻¹ ċ'` (`IsPathOn.of_comp`).
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Topology
open Set Filter

variable {n : ℕ}

/-! ### Local inverses -/

/-- The differential of `Ψ` at `z` as a linear equivalence, when it is injective. -/
def fderivEquiv (Ψ : E n → E n) (z : E n) (h : Function.Injective (fderiv ℝ Ψ z)) :
    E n ≃L[ℝ] E n :=
  (LinearEquiv.ofInjectiveEndo (fderiv ℝ Ψ z : E n →ₗ[ℝ] E n) h).toContinuousLinearEquiv

@[simp]
lemma coe_fderivEquiv (Ψ : E n → E n) (z : E n) (h : Function.Injective (fderiv ℝ Ψ z)) :
    (fderivEquiv Ψ z h : E n →L[ℝ] E n) = fderiv ℝ Ψ z := by
  ext v : 1
  rfl

variable {Ψ : E n → E n} {U : Set (E n)}

/-- Inverse function theorem: near each point of an open set where `Ψ` is smooth with injective
differential, `Ψ` has a smooth local inverse. -/
theorem exists_localInverse (hU : IsOpen U) (hΨ : ContDiffOn ℝ ∞ Ψ U)
    (hinj : ∀ z ∈ U, Function.Injective (fderiv ℝ Ψ z)) {z : E n} (hz : z ∈ U) :
    ∃ φ : OpenPartialHomeomorph (E n) (E n), ⇑φ = Ψ ∧ z ∈ φ.source ∧ φ.source ⊆ U ∧
      ContDiffOn ℝ ∞ φ.symm φ.target ∧
      ∀ y ∈ φ.target, ∀ v, fderiv ℝ Ψ (φ.symm y) (fderiv ℝ φ.symm y v) = v := by
  have hderiv : ∀ w (hw : w ∈ U), HasFDerivAt Ψ (fderivEquiv Ψ w (hinj w hw) : E n →L[ℝ] E n) w :=
    fun w hw => by
      rw [coe_fderivEquiv]
      exact ((hΨ.contDiffAt (hU.mem_nhds hw)).differentiableAt (by simp)).hasFDerivAt
  have hstrict : HasStrictFDerivAt Ψ (fderivEquiv Ψ z (hinj z hz) : E n →L[ℝ] E n) z := by
    rw [coe_fderivEquiv]
    exact (hΨ.contDiffAt (hU.mem_nhds hz)).hasStrictFDerivAt (by simp)
  set φ := (hstrict.toOpenPartialHomeomorph Ψ).restrOpen U hU
  have hsrc : φ.source = (hstrict.toOpenPartialHomeomorph Ψ).source ∩ U :=
    OpenPartialHomeomorph.restrOpen_source _ _ hU
  have hsym : ∀ y ∈ φ.target, φ.symm y ∈ U := fun y hy => (hsrc ▸ φ.map_target hy).2
  refine ⟨φ, rfl, hsrc ▸ ⟨hstrict.mem_toOpenPartialHomeomorph_source, hz⟩,
    hsrc ▸ inter_subset_right, fun y hy => ?_, fun y hy v => ?_⟩
  · exact (φ.contDiffAt_symm hy (hderiv _ (hsym y hy))
      (hΨ.contDiffAt (hU.mem_nhds (hsym y hy)))).contDiffWithinAt
  · rw [(φ.hasFDerivAt_symm hy (hderiv _ (hsym y hy))).fderiv]
    have := (fderivEquiv Ψ _ (hinj _ (hsym y hy))).apply_symm_apply v
    rwa [← ContinuousLinearEquiv.coe_coe, coe_fderivEquiv] at this

/-! ### Lifting paths -/

/-- A continuous lift `c` of a path `c' = Ψ ∘ c` through a local diffeomorphism `Ψ` is a path,
with velocities `dΨ⁻¹ ċ'`. -/
theorem IsPathOn.of_comp {P Q : E n → E n → Prop} (hU : IsOpen U) (hΨ : ContDiffOn ℝ ∞ Ψ U)
    (hinj : ∀ z ∈ U, Function.Injective (fderiv ℝ Ψ z))
    (hPQ : ∀ z ∈ U, ∀ w, P (Ψ z) (fderiv ℝ Ψ z w) → Q z w) {a b : ℝ} {c c' : ℝ → E n}
    (hc' : IsPathOn P a b c') (hc : ContinuousOn c (Icc a b)) (hcU : MapsTo c (Icc a b) U)
    (hcc' : ∀ t ∈ Icc a b, Ψ (c t) = c' t) : IsPathOn Q a b c := by
  obtain ⟨hab, F, hF⟩ := isPathOn_iff.1 hc'
  refine isPathOn_iff.2 ⟨hab, F, fun x y hax hxy hyb hz => ?_⟩
  obtain ⟨hsm, hvel⟩ := isPathPiece_iff.1 (hF x y hax hxy hyb hz)
  have hsub : Icc x y ⊆ Icc a b := Icc_subset_Icc hax hyb
  have hloc : ∀ t ∈ Icc x y, ∃ φ : OpenPartialHomeomorph (E n) (E n), ⇑φ = Ψ ∧
      c t ∈ φ.source ∧ ContDiffOn ℝ ∞ φ.symm φ.target ∧
      (∀ y ∈ φ.target, ∀ v, fderiv ℝ Ψ (φ.symm y) (fderiv ℝ φ.symm y v) = v) ∧
      c =ᶠ[𝓝[Icc x y] t] φ.symm ∘ c' := by
    intro t ht
    obtain ⟨φ, hφ, hct, -, hsmooth, hinv⟩ := exists_localInverse hU hΨ hinj (hcU (hsub ht))
    refine ⟨φ, hφ, hct, hsmooth, hinv, ?_⟩
    have hev : ∀ᶠ u in 𝓝[Icc x y] t, c u ∈ φ.source :=
      (hc.mono hsub t ht) (φ.open_source.mem_nhds hct)
    filter_upwards [hev, self_mem_nhdsWithin] with u hu hux
    simp only [Function.comp_apply, ← hcc' u (hsub hux), ← hφ, φ.left_inv hu]
  refine isPathPiece_iff.2 ⟨fun t ht => ?_, fun t ht => ?_⟩
  · obtain ⟨φ, hφ, hct, hsmooth, -, heq⟩ := hloc t ht
    have htgt : c' t ∈ φ.target := by
      rw [← hcc' t (hsub ht), ← hφ]
      exact φ.map_source hct
    exact ((hsmooth.contDiffAt (φ.open_target.mem_nhds htgt)).comp_contDiffWithinAt t
      (hsm t ht)).congr_of_eventuallyEq heq (heq.self_of_nhdsWithin ht)
  · obtain ⟨φ, hφ, hct, hsmooth, hinv, heq⟩ := hloc t ht
    have htgt : c' t ∈ φ.target := by
      rw [← hcc' t (hsub ht), ← hφ]
      exact φ.map_source hct
    have hd : HasDerivWithinAt c (fderiv ℝ φ.symm (c' t) (derivWithin c' (Icc x y) t))
        (Icc x y) t :=
      (((hsmooth.contDiffAt (φ.open_target.mem_nhds htgt)).differentiableAt
        (by simp)).hasFDerivAt.comp_hasDerivWithinAt t
        ((hsm.differentiableOn (by simp) t ht).hasDerivWithinAt)).congr_of_eventuallyEq heq
        (heq.self_of_nhdsWithin ht)
    rw [hd.derivWithin (uniqueDiffOn_Icc hxy t ht)]
    have hsymm : φ.symm (c' t) = c t := by
      rw [← hcc' t (hsub ht), ← hφ, φ.left_inv hct]
    refine hPQ _ (hcU (hsub ht)) _ ?_
    rw [← hsymm, hinv _ htgt, hsymm, hcc' t (hsub ht)]
    exact hvel t ht

end

end LorentzianCalderon
