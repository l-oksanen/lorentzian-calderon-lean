module

public import Mathlib

public section

/-!
# Uniform bounds by compactness

Bounds for continuous families of functions that are homogeneous of degree two, smallness of
a continuous function near the part of a compact set where it vanishes, and bounds of continuous
functions on compact sets.
-/

namespace LorentzianCalderon

open Set Metric

section Homogeneous

variable {Z W : Type*} [TopologicalSpace Z] [CompactSpace Z] [NormedAddCommGroup W]
  [NormedSpace ℝ W] [ProperSpace W] [Nontrivial W]

omit [TopologicalSpace Z] [CompactSpace Z] [ProperSpace W] [Nontrivial W] in
theorem homogeneous_eq_norm_sq {F : Z → W → ℝ} (hhom : ∀ z (t : ℝ) v, F z (t • v) = t ^ 2 * F z v)
    (z : Z) {v : W} (hv : v ≠ 0) : F z v = ‖v‖ ^ 2 * F z (‖v‖⁻¹ • v) := by
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
  rw [← hhom, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]

omit [TopologicalSpace Z] [CompactSpace Z] [ProperSpace W] [Nontrivial W] in
theorem homogeneous_zero {F : Z → W → ℝ} (hhom : ∀ z (t : ℝ) v, F z (t • v) = t ^ 2 * F z v)
    (z : Z) : F z 0 = 0 := by
  have := hhom z 0 0
  simpa using this

omit [ProperSpace W] [Nontrivial W] in
theorem mem_sphere_normalize {v : W} (hv : v ≠ 0) : ‖v‖⁻¹ • v ∈ sphere (0 : W) 1 := by
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
  simp [norm_smul, hn.ne']

omit [Nontrivial W] in
/-- A continuous family of functions homogeneous of degree two is bounded by `C ‖v‖²`. -/
theorem exists_bound_of_homogeneous {F : Z → W → ℝ}
    (hF : Continuous fun p : Z × W => F p.1 p.2)
    (hhom : ∀ z (t : ℝ) v, F z (t • v) = t ^ 2 * F z v) :
    ∃ C, ∀ z v, |F z v| ≤ C * ‖v‖ ^ 2 := by
  have hc : IsCompact ((univ : Set Z) ×ˢ sphere (0 : W) 1) :=
    isCompact_univ.prod (isCompact_sphere 0 1)
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn hF.continuousOn
  refine ⟨C, fun z v => ?_⟩
  rcases eq_or_ne v 0 with rfl | hv
  · rw [homogeneous_zero hhom]; simp
  · have h1 := hC (z, ‖v‖⁻¹ • v) ⟨mem_univ _, mem_sphere_normalize hv⟩
    rw [Real.norm_eq_abs] at h1
    rw [homogeneous_eq_norm_sq hhom z hv, abs_mul, abs_of_nonneg (by positivity), mul_comm]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)

/-- A continuous family of positive functions homogeneous of degree two is bounded below by
`c ‖v‖²` with `c > 0`. -/
theorem exists_coercive_of_homogeneous {F : Z → W → ℝ}
    (hF : Continuous fun p : Z × W => F p.1 p.2)
    (hhom : ∀ z (t : ℝ) v, F z (t • v) = t ^ 2 * F z v) (hpos : ∀ z v, v ≠ 0 → 0 < F z v) :
    ∃ c > 0, ∀ z v, c * ‖v‖ ^ 2 ≤ F z v := by
  rcases isEmpty_or_nonempty Z with hZ | ⟨⟨z₀⟩⟩
  · exact ⟨1, one_pos, fun z => isEmptyElim z⟩
  have hc : IsCompact ((univ : Set Z) ×ˢ sphere (0 : W) 1) :=
    isCompact_univ.prod (isCompact_sphere 0 1)
  have hne : ((univ : Set Z) ×ˢ sphere (0 : W) 1).Nonempty :=
    ⟨(z₀, _), mem_univ _, (NormedSpace.sphere_nonempty.2 zero_le_one).some_mem⟩
  obtain ⟨p, hp, hmin⟩ := hc.exists_isMinOn hne hF.continuousOn
  have hp0 : p.2 ≠ 0 := by
    intro h0; have := hp.2; rw [h0] at this; simp at this
  refine ⟨F p.1 p.2, hpos _ _ hp0, fun z v => ?_⟩
  rcases eq_or_ne v 0 with rfl | hv
  · rw [homogeneous_zero hhom]; simp
  · have h1 : F p.1 p.2 ≤ F z (‖v‖⁻¹ • v) :=
      hmin (show (z, ‖v‖⁻¹ • v) ∈ _ from ⟨mem_univ _, mem_sphere_normalize hv⟩)
    rw [homogeneous_eq_norm_sq hhom z hv, mul_comm]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)

end Homogeneous

/-- A continuous function vanishing where `ψ` attains its upper bound `τ` on a compact set is
small near that set. -/
theorem exists_small_near_top {Z : Type*} [TopologicalSpace Z] [T2Space Z] {K : Set Z}
    (hK : IsCompact K) {f ψ : Z → ℝ} (hf : ContinuousOn f K) (hψ : ContinuousOn ψ K) {τ : ℝ}
    (hle : ∀ z ∈ K, ψ z ≤ τ) (h0 : ∀ z ∈ K, ψ z = τ → f z = 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε > 0, ∀ z ∈ K, τ - ε ≤ ψ z → f z < δ := by
  set K' := K ∩ f ⁻¹' Ici δ
  have hK' : IsCompact K' :=
    hK.of_isClosed_subset (hf.preimage_isClosed_of_isClosed hK.isClosed isClosed_Ici)
      inter_subset_left
  rcases K'.eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun z hz _ => ?_⟩
    by_contra hfz
    have : z ∈ K' := ⟨hz, le_of_not_gt hfz⟩
    rw [he] at this; exact this
  obtain ⟨z₀, hz₀, hmax⟩ := hK'.exists_isMaxOn hne (hψ.mono inter_subset_left)
  have hlt : ψ z₀ < τ := by
    refine lt_of_le_of_ne (hle z₀ hz₀.1) fun heq => ?_
    have := h0 z₀ hz₀.1 heq
    have := hz₀.2
    simp only [mem_preimage, mem_Ici] at this
    linarith
  refine ⟨(τ - ψ z₀) / 2, by linarith, fun z hz hzψ => ?_⟩
  by_contra hfz
  have hzK' : z ∈ K' := ⟨hz, le_of_not_gt hfz⟩
  have : ψ z ≤ ψ z₀ := hmax hzK'
  linarith

section Bounds

/-- A continuous function on a compact set is bounded. -/
theorem exists_abs_le_of_continuousOn {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {f : X → ℝ} (hf : ContinuousOn f K) :
    ∃ M > 0, ∀ x ∈ K, |f x| ≤ M := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf
  exact ⟨max C 1, by positivity, fun x hx => (hC x hx).trans (le_max_left _ _)⟩

/-- A continuous positive function on a compact set has a positive lower bound. -/
theorem exists_pos_le_of_continuousOn {Z : Type*} [TopologicalSpace Z] {K : Set Z}
    (hK : IsCompact K) {f : Z → ℝ} (hf : ContinuousOn f K) (hpos : ∀ x ∈ K, 0 < f x) :
    ∃ m > 0, ∀ x ∈ K, m ≤ f x := by
  rcases K.eq_empty_or_nonempty with he | hne
  · exact ⟨1, one_pos, fun x hx => by rw [he] at hx; exact absurd hx (notMem_empty x)⟩
  obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hne hf
  exact ⟨f x₀, hpos x₀ hx₀, fun x hx => hmin hx⟩

end Bounds

end LorentzianCalderon
