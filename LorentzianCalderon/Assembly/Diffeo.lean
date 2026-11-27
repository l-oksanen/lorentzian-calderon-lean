module

public import Mathlib

public section

/-!
# Proper local diffeomorphisms of a vector space

A proper local homeomorphism of a finite-dimensional real vector space is a covering map, hence a
homeomorphism, since the space is simply connected (blueprint, Lemma `main_proper`).
-/

open Set Function
open scoped ContDiff Topology

namespace LorentzianCalderon

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem bijective_of_isLocalHomeomorph_of_isProperMap {f : V → V} (hf : IsLocalHomeomorph f)
    (hp : IsProperMap f) : Bijective f := by
  have hloc : IsLocalHomeomorphOn f (f ⁻¹' univ) := fun x _ => hf x
  have hcov : IsCoveringMap f := by
    rw [isCoveringMap_iff_isCoveringMapOn_univ]
    refine hp.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn (fun y _ => ?_) hloc
    have hc : IsCompact (f ⁻¹' {y}) := hp.isCompact_preimage isCompact_singleton
    exact hc.finite (IsDiscrete.of_openPartialHomeomorph f subset_rfl fun e _ =>
      (hf e).imp fun φ h => ⟨h.1, h.2.symm⟩)
  set x₀ : V := 0
  have hfc : Continuous f := hf.continuous
  obtain ⟨s, ⟨hs₀, hs⟩, -⟩ :=
    hcov.existsUnique_continuousMap_lifts (ContinuousMap.id V) (f x₀) x₀ rfl
  have hfs : ∀ y, f (s y) = y := fun y => congrFun hs y
  obtain ⟨F, -, hF⟩ := hcov.existsUnique_continuousMap_lifts ⟨f, hfc⟩ x₀ x₀ rfl
  have h1 := hF (ContinuousMap.id V) ⟨rfl, rfl⟩
  have h2 := hF (s.comp ⟨f, hfc⟩) ⟨hs₀, by ext x; simp [hfs]⟩
  have hsf : ∀ x, s (f x) = x := fun x => by
    simpa using DFunLike.congr_fun (h2.trans h1.symm) x
  exact ⟨LeftInverse.injective hsf, RightInverse.surjective hfs⟩

/-- A smooth proper map of a finite-dimensional real vector space with injective differentials is
a diffeomorphism. -/
theorem exists_equiv_of_isProperMap [FiniteDimensional ℝ V] {f : V → V} (hf : ContDiff ℝ ∞ f)
    (hinj : ∀ x, Injective (fderiv ℝ f x)) (hp : IsProperMap f) :
    ∃ e : V ≃ V, ⇑e = f ∧ ContDiff ℝ ∞ e.symm := by
  let f' : V → V ≃L[ℝ] V := fun x =>
    (LinearEquiv.ofInjectiveEndo (fderiv ℝ f x : V →ₗ[ℝ] V) (hinj x)).toContinuousLinearEquiv
  have hf' : ∀ x, HasFDerivAt f (f' x : V →L[ℝ] V) x := fun x => by
    have : (f' x : V →L[ℝ] V) = fderiv ℝ f x := by ext v; rfl
    rw [this]
    exact (hf.differentiable (by simp) x).hasFDerivAt
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hloc : IsLocalHomeomorph f := fun x =>
    ⟨hf.contDiffAt.toOpenPartialHomeomorph f (hf' x) hn,
      hf.contDiffAt.mem_toOpenPartialHomeomorph_source (hf' x) hn, rfl⟩
  have hbij := bijective_of_isLocalHomeomorph_of_isProperMap hloc hp
  refine ⟨Equiv.ofBijective f hbij, rfl, contDiff_iff_contDiffAt.2 fun y => ?_⟩
  obtain ⟨x, rfl⟩ := hbij.2 y
  set φ := hf.contDiffAt.toOpenPartialHomeomorph f (hf' x) hn
  have hφ : ContDiffAt ℝ ∞ φ.symm (f x) := hf.contDiffAt.to_localInverse (hf' x) hn
  refine hφ.congr_of_eventuallyEq ?_
  filter_upwards [φ.open_target.mem_nhds
    (hf.contDiffAt.image_mem_toOpenPartialHomeomorph_target (hf' x) hn)] with z hz
  refine (Equiv.ofBijective f hbij).symm_apply_eq.2 ?_
  exact (φ.right_inv hz).symm

end LorentzianCalderon
