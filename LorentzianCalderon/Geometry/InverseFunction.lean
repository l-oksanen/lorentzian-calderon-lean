module

public import Mathlib

public section

/-!
# A global inverse function theorem near a compact set

A smooth map with invertible derivative at the points of a compact set `K`, and injective on `K`,
is a diffeomorphism from an open neighbourhood of `K` onto an open set.
-/

open Set Filter
open scoped ContDiff Topology

namespace LorentzianCalderon

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem exists_injOn_contDiffOn_inverse {f : V → V} {D K : Set V} (hD : IsOpen D)
    (hf : ContDiffOn ℝ ∞ f D) (hK : IsCompact K) (hKD : K ⊆ D) (hinj : InjOn f K)
    (hder : ∀ x ∈ K, ∃ f' : V ≃L[ℝ] V, HasFDerivAt f (f' : V →L[ℝ] V) x) :
    ∃ U, IsOpen U ∧ K ⊆ U ∧ U ⊆ D ∧ InjOn f U ∧ IsOpen (f '' U) ∧
      (∀ x ∈ U, ∃ f' : V ≃L[ℝ] V, HasFDerivAt f (f' : V →L[ℝ] V) x) ∧
      ∃ h : V → V, ContDiffOn ℝ ∞ h (f '' U) ∧ ∀ x ∈ U, h (f x) = x := by
  have hdiff : ∀ x ∈ D, HasFDerivAt f (fderiv ℝ f x) x := fun x hx =>
    ((hf.differentiableOn (by simp)).differentiableAt (hD.mem_nhds hx)).hasFDerivAt
  set B := D ∩ fderiv ℝ f ⁻¹' range ((↑) : (V ≃L[ℝ] V) → V →L[ℝ] V)
  have hB : IsOpen B :=
    (hf.continuousOn_fderiv_of_isOpen hD (by simp)).isOpen_inter_preimage hD
      ContinuousLinearEquiv.isOpen
  have hBder : ∀ x ∈ B, ∃ f' : V ≃L[ℝ] V, HasFDerivAt f (f' : V →L[ℝ] V) x := by
    rintro x ⟨hxD, f', hf'⟩
    exact ⟨f', hf' ▸ hdiff x hxD⟩
  have hKB : K ⊆ B := fun x hx => by
    obtain ⟨f', hf'⟩ := hder x hx
    exact ⟨hKD hx, f', (hdiff x (hKD hx)).unique hf' |>.symm⟩
  have loc : ∀ x ∈ B, ∃ e : OpenPartialHomeomorph V V, x ∈ e.source ∧ e.source ⊆ D ∧
      EqOn f e e.source ∧ ContDiffAt ℝ ∞ e.symm (f x) := by
    intro x hx
    obtain ⟨f', hf'⟩ := hBder x hx
    have hc : ContDiffAt ℝ ∞ f x := hf.contDiffAt (hD.mem_nhds hx.1)
    set e := hc.toOpenPartialHomeomorph f hf' (by simp)
    refine ⟨e.restrOpen D hD, ⟨hc.mem_toOpenPartialHomeomorph_source hf' (by simp), hx.1⟩,
      inter_subset_right, fun _ _ => rfl, ?_⟩
    have hsymm : (e.restrOpen D hD).symm =ᶠ[𝓝 (f x)] e.symm := by
      simp [OpenPartialHomeomorph.restrOpen]
    refine ContDiffAt.congr_of_eventuallyEq ?_ hsymm
    have := hc.to_localInverse hf' (by simp)
    exact this
  obtain ⟨t, ht, hKt, htinj⟩ := hinj.exists_isOpen_superset hK
    (fun x hx => (hf.continuousOn.continuousAt (hD.mem_nhds (hKD hx))))
    (fun x hx => by
      obtain ⟨e, hxe, -, hfe, -⟩ := loc x (hKB hx)
      exact ⟨e.source, e.open_source.mem_nhds hxe, fun a ha b hb hab => by
        rw [hfe ha, hfe hb] at hab
        exact e.injOn ha hb hab⟩)
  set U := t ∩ B
  have hU : IsOpen U := ht.inter hB
  have hUinj : InjOn f U := htinj.mono inter_subset_left
  have himg : ∀ x ∈ U, ∃ e : OpenPartialHomeomorph V V, x ∈ e.source ∧
      IsOpen (f '' (U ∩ e.source)) ∧ EqOn f e e.source ∧ ContDiffAt ℝ ∞ e.symm (f x) := by
    intro x hx
    obtain ⟨e, hxe, -, hfe, hc⟩ := loc x hx.2
    refine ⟨e, hxe, ?_, hfe, hc⟩
    rw [image_congr (fun y hy => hfe hy.2)]
    exact e.isOpen_image_of_subset_source (hU.inter e.open_source) inter_subset_right
  have hfU : IsOpen (f '' U) := by
    refine isOpen_iff_mem_nhds.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨e, hxe, ho, -, -⟩ := himg x hx
    exact mem_of_superset (ho.mem_nhds ⟨x, ⟨hx, hxe⟩, rfl⟩)
      (image_mono inter_subset_left)
  classical
  refine ⟨U, hU, subset_inter hKt hKB, fun x hx => hx.2.1, hUinj, hfU,
    fun x hx => hBder x hx.2, Function.invFunOn f U, ?_,
    fun x hx => hUinj.leftInvOn_invFunOn hx⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨e, hxe, ho, hfe, hc⟩ := himg x hx
  refine (hc.congr_of_eventuallyEq ?_).contDiffWithinAt
  refine mem_of_superset (ho.mem_nhds ⟨x, ⟨hx, hxe⟩, rfl⟩) ?_
  rintro _ ⟨z, hz, rfl⟩
  show Function.invFunOn f U (f z) = e.symm (f z)
  rw [hUinj.leftInvOn_invFunOn hz.1, hfe hz.2, e.left_inv hz.2]

end LorentzianCalderon
