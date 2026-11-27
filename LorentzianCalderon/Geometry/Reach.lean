module

public import LorentzianCalderon.Geometry.CausalClosed
public import LorentzianCalderon.Causal.TimeFlow
public import LorentzianCalderon.Facts
public import LorentzianCalderon.Local.Energy.Coform

public section

/-!
# The boundary of the causal past reaches the exterior

If every point outside a compact set `W` is the initial point of a future-inextendible timelike
ray avoiding `W`, then for `p₀ ∈ W` the horismos `E⁻(p₀) = J⁻(p₀) \ I⁻(p₀)` meets the complement
of `W` (blueprint, Lemma `lem_reach`).
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Filter

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n}

/-- An inextendible ray is continuous on `[0, ∞)`. -/
theorem IsInextendibleRay.continuousOn {P : E n → E n → Prop} {c : ℝ → E n}
    (hc : IsInextendibleRay P c) : ContinuousOn c (Ici 0) := by
  intro t ht
  have h := (hc.path (t + 1) (by linarith [mem_Ici.1 ht])).continuousOn t ⟨ht, by linarith⟩
  exact h.mono_of_mem_nhdsWithin
    (mem_nhdsWithin.2 ⟨Iio (t + 1), isOpen_Iio, by simp, fun z hz => ⟨hz.2, hz.1.le⟩⟩)

/-- Weakening the velocity condition of an inextendible ray. -/
theorem IsInextendibleRay.mono {P Q : E n → E n → Prop} {c : ℝ → E n}
    (hc : IsInextendibleRay P c) (hPQ : ∀ x v, P x v → Q x v) : IsInextendibleRay Q c :=
  ⟨fun a ha => (hc.path a ha).mono hPQ, hc.no_limit⟩

/-- A future-directed timelike ray stays in the causal future of its initial point. -/
theorem IsInextendibleRay.causalLE {c : ℝ → E n} (hc : IsInextendibleRay (IsFutureTimelike g Y) c)
    {t : ℝ} (ht : 0 ≤ t) : CausalLE g Y (c 0) (c t) := by
  rcases ht.lt_or_eq with ht | rfl
  · exact causalLE_of_isPathOn ((hc.path t ht).mono fun _ _ hv => hv.isFutureCausal)
  · exact CausalLE.refl _

/-- The chronological past of `p` contains points on which some continuous function (a Cauchy
temporal function) is arbitrarily small; in particular it is not relatively compact. -/
theorem exists_chronLT_lt (hg : IsSpacetime g Y) (p : E n) :
    ∃ ψ : E n → ℝ, Continuous ψ ∧ ∀ m : ℝ, ∃ q, ChronLT g Y q p ∧ ψ q < m := by
  obtain ⟨ψ, Φ, hψ, hΦ, hΦ0, hΦd, hΦψ⟩ := Facts.exists_cauchyTemporal hg
  refine ⟨ψ, hψ.smooth.continuous, fun m => ?_⟩
  set t := |ψ p - m| + 1
  have ht : 0 < t := by positivity
  have hsmooth : ContDiff ℝ ∞ fun s => Φ s p := hΦ.comp (contDiff_id.prodMk contDiff_const)
  have hpath : IsPathOn (IsFutureTimelike g Y) (-t) 0 fun s => Φ s p := by
    refine isPathOn_iff.2 ⟨by linarith, ∅,
      fun x y _ hxy _ _ => isPathPiece_iff.2 ⟨hsmooth.contDiffOn,
      fun r hr => ?_⟩⟩
    rw [(hΦd r p).hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hxy r hr)]
    have hc := coform_self_neg_of_future (hg.lorentzian _) (hψ.past_gradient (Φ r p))
    rw [show ∀ c : ℝ, c⁻¹ • grad g ψ (Φ r p) = (-c⁻¹) • (-grad g ψ (Φ r p)) by
      intro c; rw [smul_neg, neg_smul, neg_neg]]
    exact (hψ.past_gradient _).smul (neg_pos.2 (inv_lt_zero.2 hc))
  refine ⟨Φ (-t) p, by simpa [hΦ0] using chronLT_of_isPathOn hpath, ?_⟩
  rw [hΦψ]
  linarith [le_abs_self (ψ p - m)]

/-- Blueprint, Lemma `lem_reach`. -/
theorem exists_mem_horismos_past (hg : IsSpacetime g Y) {W : Set (E n)} (hW : IsCompact W)
    (hesc : ∀ x ∉ W, ∃ c : ℝ → E n, c 0 = x ∧ IsInextendibleRay (IsFutureTimelike g Y) c ∧
      (∀ t : ℝ, 0 ≤ t → c t ∉ W) ∧ Tendsto c atTop (cocompact (E n)))
    {p₀ : E n} (_hp₀ : p₀ ∈ W) : ∃ y ∉ W, CausalLE g Y y p₀ ∧ ¬ ChronLT g Y y p₀ := by
  by_contra hcon
  push Not at hcon
  have hsub : chronPast g Y p₀ ⊆ W := by
    intro y hy
    by_contra hyW
    obtain ⟨c, hc0, hc, hcW, hcK⟩ := hesc y hyW
    have hU : IsOpen (chronPast g Y p₀) := by
      rw [← chronFuture_neg]
      exact Facts.isOpen_chronFuture hg.neg p₀
    have hV : IsOpen (causalPast g Y p₀)ᶜ := (isClosed_causalPast hg p₀).isOpen_compl
    have hS : c '' Ici 0 ⊆ chronPast g Y p₀ := by
      refine (isPreconnected_Ici.image c hc.continuousOn).subset_left_of_subset_union hU hV
        (disjoint_compl_right_iff_subset.2 (chronPast_subset_causalPast p₀)) ?_
        ⟨y, ⟨0, self_mem_Ici, hc0⟩, hy⟩
      rintro _ ⟨t, ht, rfl⟩
      by_cases hJ : CausalLE g Y (c t) p₀
      · exact Or.inl (mem_chronPast.2 (hcon _ (hcW t ht) hJ))
      · exact Or.inr fun h => hJ (mem_causalPast.1 h)
    obtain ⟨t₀, ht₀⟩ := eventually_atTop.1
      (hcK.eventually (hg.globallyHyperbolic.compact_diamond y p₀).compl_mem_cocompact)
    have ht : 0 ≤ max t₀ 0 := le_max_right _ _
    refine ht₀ (max t₀ 0) (le_max_left _ _) ⟨?_, chronPast_subset_causalPast p₀
      (hS ⟨_, ht, rfl⟩)⟩
    simpa [mem_causalFuture, hc0] using hc.causalLE ht
  obtain ⟨ψ, hψ, hlt⟩ := exists_chronLT_lt hg p₀
  obtain ⟨m, hm⟩ := hW.bddBelow_image hψ.continuousOn
  obtain ⟨q, hq, hqm⟩ := hlt m
  exact (hm ⟨q, hsub (mem_chronPast.2 hq), rfl⟩).not_gt hqm

end

end LorentzianCalderon
