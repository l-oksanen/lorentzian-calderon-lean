module

public import LorentzianCalderon.Green.Temporal
public import LorentzianCalderon.Facts.Temporal

public section

/-!
# Imprisonment

A future-inextendible causal curve does not stay in a compact set (`Facts.imprisonment`). On a
compact set `K`, a temporal function `ψ` grows at least like `κ ‖v‖` in future causal
directions `v` (`exists_pos_mul_norm_le_fderiv`), so along a causal curve in `K` the
displacement is bounded by the growth of `ψ` (`IsPathOn.norm_sub_le`). As `ψ` is bounded on
`K`, a curve imprisoned in `K` would be Cauchy and have a limit.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Filter

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n}

/-- A path has a right derivative satisfying the velocity condition at every point but the
last. -/
theorem IsPathOn.exists_hasDerivWithinAt_Ici {P : E n → E n → Prop} {a b : ℝ} {γ : ℝ → E n}
    (h : IsPathOn P a b γ) {x : ℝ} (hx : x ∈ Ico a b) :
    ∃ d, HasDerivWithinAt γ d (Ici x) x ∧ P (γ x) d := by
  classical
  obtain ⟨-, F, hF⟩ := isPathOn_iff.1 h
  set F' := insert b (F.filter (x < ·))
  have hne : F'.Nonempty := ⟨b, Finset.mem_insert_self _ _⟩
  set y := F'.min' hne
  have hxy : x < y := (Finset.lt_min'_iff _ hne).2 fun z hz => by
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact hx.2
    · exact (Finset.mem_filter.1 hz).2
  have hyb : y ≤ b := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  obtain ⟨hsm, hvel⟩ := isPathPiece_iff.1 <| hF x y hx.1 hxy hyb fun z hz hzI =>
    (not_lt.2 (Finset.min'_le F' z
      (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hz, hzI.1⟩)))) hzI.2
  have hxI : x ∈ Icc x y := ⟨le_rfl, hxy.le⟩
  exact ⟨_, ((hsm.differentiableOn (by simp) x hxI).hasDerivWithinAt).mono_of_mem_nhdsWithin
    (Icc_mem_nhdsGE hxy), hvel x hxI⟩

/-- On a compact set, a temporal function grows at least like a multiple of the norm in future
causal directions. -/
theorem exists_pos_mul_norm_le_fderiv (hg : IsSpacetime g Y) {ψ : E n → ℝ}
    (hψs : ContDiff ℝ 1 ψ) (hψ : ∀ x, IsFutureTimelike g Y x (-grad g ψ x)) {K : Set (E n)}
    (hK : IsCompact K) :
    ∃ κ > 0, ∀ x ∈ K, ∀ v, IsFutureCausal g Y x v → κ * ‖v‖ ≤ fderiv ℝ ψ x v := by
  have hY := hg.globallyHyperbolic.timeOrientation
  set S := {p : E n × E n | p.1 ∈ K ∧ p.2 ∈ Metric.sphere (0 : E n) 1 ∧
    form (g p.1) p.2 p.2 ≤ 0 ∧ form (g p.1) p.2 (Y p.1) ≤ 0}
  have hSc : IsCompact S := by
    refine (hK.prod (isCompact_sphere (0 : E n) 1)).of_isClosed_subset ?_
      fun p hp => ⟨hp.1, hp.2.1⟩
    have h1 : Continuous fun p : E n × E n => form (g p.1) p.2 p.2 :=
      (continuous_form hg).comp (continuous_fst.prodMk (continuous_snd.prodMk continuous_snd))
    have h2 : Continuous fun p : E n × E n => form (g p.1) p.2 (Y p.1) :=
      (continuous_form hg).comp
        (continuous_fst.prodMk (continuous_snd.prodMk (hY.continuous.comp continuous_fst)))
    exact (hK.isClosed.preimage continuous_fst).inter
      ((Metric.isClosed_sphere.preimage continuous_snd).inter
        ((isClosed_le h1 continuous_const).inter (isClosed_le h2 continuous_const)))
  have hfc : Continuous fun p : E n × E n => fderiv ℝ ψ p.1 p.2 :=
    ((hψs.continuous_fderiv one_ne_zero).comp continuous_fst).clm_apply continuous_snd
  have hpos : ∀ p ∈ S, 0 < fderiv ℝ ψ p.1 p.2 := by
    rintro ⟨x, v⟩ ⟨-, hv1, hvv, hvY⟩
    have hv0 : v ≠ 0 := by
      rintro rfl
      simp at hv1
    refine fderiv_pos_of_isFutureCausal (hg.lorentzian x) (hY.timelike x) (hψ x)
      ⟨hv0, hvv, lt_of_le_of_ne hvY fun h => ?_⟩
    exact (hg.lorentzian x).form_ne_zero hvv hv0 (hY.timelike x) h
  obtain ⟨κ, hκ, hκS⟩ : ∃ κ > 0, ∀ p ∈ S, κ ≤ fderiv ℝ ψ p.1 p.2 := by
    rcases S.eq_empty_or_nonempty with hS | hS
    · exact ⟨1, one_pos, by simp [hS]⟩
    · obtain ⟨p₀, hp₀, hmin⟩ := hSc.exists_isMinOn hS hfc.continuousOn
      exact ⟨_, hpos p₀ hp₀, fun p hp => hmin hp⟩
  refine ⟨κ, hκ, fun x hx v hv => ?_⟩
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv.ne_zero
  have hu := hκS (x, ‖v‖⁻¹ • v) ⟨hx, by simp [norm_smul, hn.ne'],
    (hv.smul (inv_pos.2 hn)).causal, (hv.smul (inv_pos.2 hn)).future.le⟩
  simp only [map_smul, smul_eq_mul] at hu
  rwa [le_inv_mul_iff₀ hn, mul_comm] at hu

/-- Along a future causal path in a compact set on which `ψ` grows like `κ ‖v‖` in future
causal directions, the displacement is bounded by the growth of `ψ`. -/
theorem IsPathOn.norm_sub_le {ψ : E n → ℝ} (hψs : ContDiff ℝ 1 ψ) {K : Set (E n)} {κ : ℝ}
    (hκ : 0 < κ) (hψK : ∀ x ∈ K, ∀ v, IsFutureCausal g Y x v → κ * ‖v‖ ≤ fderiv ℝ ψ x v)
    {a b : ℝ} {γ : ℝ → E n} (hγ : IsPathOn (IsFutureCausal g Y) a b γ)
    (hγK : ∀ t ∈ Icc a b, γ t ∈ K) : κ * ‖γ b - γ a‖ ≤ ψ (γ b) - ψ (γ a) := by
  have hψd : Differentiable ℝ ψ := hψs.differentiable one_ne_zero
  have hc := hγ.continuousOn
  choose! d hd hdP using fun x (hx : x ∈ Ico a b) => hγ.exists_hasDerivWithinAt_Ici hx
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary' (a := a) (b := b)
    (f := fun t => γ t - γ a) (f' := d) (hc.sub continuousOn_const)
    (fun x hx => (hd x hx).sub_const _) (B := fun t => (ψ (γ t) - ψ (γ a)) / κ)
    (B' := fun t => fderiv ℝ ψ (γ t) (d t) / κ) (by simp)
    ((hψd.continuous.comp_continuousOn hc).sub continuousOn_const |>.div_const κ)
    (fun x hx => (((hψd (γ x)).hasFDerivAt.comp_hasDerivWithinAt x (hd x hx)).sub_const
      _).div_const κ)
    (fun x hx => by
      rw [le_div_iff₀ hκ, mul_comm]
      exact hψK _ (hγK x (Ico_subset_Icc_self hx)) _ (hdP x hx))
    ⟨hγ.lt.le, le_rfl⟩
  rwa [le_div_iff₀ hκ, mul_comm] at key

/-- Along a future-inextendible causal curve staying in a set on which `ψ` grows like `κ ‖v‖` in
future causal directions, `ψ` is unbounded: otherwise the curve would be Cauchy and have a
limit. -/
theorem IsInextendibleRay.not_forall_le {ψ : E n → ℝ} (hψs : ContDiff ℝ 1 ψ) {K : Set (E n)}
    {κ : ℝ} (hκ : 0 < κ)
    (hψK : ∀ x ∈ K, ∀ v, IsFutureCausal g Y x v → κ * ‖v‖ ≤ fderiv ℝ ψ x v)
    {c : ℝ → E n} (hc : IsInextendibleRay (IsFutureCausal g Y) c) (hcK : ∀ t ≥ 0, c t ∈ K)
    (M : ℝ) : ¬ ∀ t ≥ 0, ψ (c t) ≤ M := by
  intro hM
  have hle : ∀ s t, 0 ≤ s → s ≤ t → κ * ‖c t - c s‖ ≤ ψ (c t) - ψ (c s) := by
    intro s t hs hst
    rcases hst.lt_or_eq with hst | rfl
    · exact ((hc.path t (hs.trans_lt hst)).restrict hs hst le_rfl).norm_sub_le hψs hκ hψK
        fun r hr => hcK r (hs.trans hr.1)
    · simp
  set A := (fun t => ψ (c t)) '' Ici 0
  have hA : A.Nonempty := ⟨_, 0, self_mem_Ici, rfl⟩
  have hAb : BddAbove A := ⟨M, by
    rintro _ ⟨t, ht, rfl⟩
    exact hM t ht⟩
  have hcauchy : CauchySeq c := by
    refine Metric.cauchySeq_iff.2 fun ε hε => ?_
    obtain ⟨_, ⟨N, hN, rfl⟩, hNlt⟩ := exists_lt_of_lt_csSup hA
      (show sSup A - κ * ε < sSup A by nlinarith)
    have hbound : ∀ t ≥ N, ψ (c t) ≤ sSup A := fun t ht =>
      le_csSup hAb ⟨t, le_trans hN ht, rfl⟩
    have hhalf : ∀ s t, N ≤ s → s ≤ t → dist (c s) (c t) < ε := by
      intro s t hs hst
      have h1 := hle s t (le_trans hN hs) hst
      have h2 := hle N s hN hs
      have h3 := hbound t (hs.trans hst)
      rw [dist_comm, dist_eq_norm]
      nlinarith [norm_nonneg (c s - c N)]
    refine ⟨N, fun s hs t ht => ?_⟩
    rcases le_total s t with hst | hts
    · exact hhalf s t hs hst
    · rw [dist_comm]
      exact hhalf t s ht hts
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
  exact hc.no_limit x hx

/-- Imprisonment: a future-inextendible causal curve does not stay in a compact set. O'Neill,
Semi-Riemannian geometry, Lemma 14.13, p. 408, says more: the curve eventually leaves the
compact set for good, in a strongly causal spacetime. The proof here uses a temporal function
instead of strong causality. -/
theorem Facts.imprisonment (hg : IsSpacetime g Y) {K : Set (E n)} (hK : IsCompact K)
    {c : ℝ → E n} (hc : IsInextendibleRay (IsFutureCausal g Y) c) : ¬ ∀ t ≥ 0, c t ∈ K := by
  intro hcK
  obtain ⟨ψ, hψs, hψ⟩ := Facts.exists_temporal hg
  have hψ1 : ContDiff ℝ 1 ψ := hψs.of_le (by simp)
  obtain ⟨κ, hκ, hψK⟩ := exists_pos_mul_norm_le_fderiv hg hψ1 hψ hK
  obtain ⟨M, hM⟩ := hK.bddAbove_image hψs.continuous.continuousOn
  exact hc.not_forall_le hψ1 hκ hψK hcK M fun t ht => hM ⟨c t, hcK t ht, rfl⟩

end

end LorentzianCalderon
