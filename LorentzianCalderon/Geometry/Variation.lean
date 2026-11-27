module

public import LorentzianCalderon.Geometry.Lagrangian

public section

/-!
# Timelike curves from second-order variations of a null curve

For a variation `x(s, u) = σ(u) + s V(u) + s² Z(u)` of a null curve `σ`, the energy density
`L(x, ∂ᵤx)` vanishes at `s = 0`; if its first `s`-derivative vanishes and its second is
negative for every `u` in a compact interval, then the curves `u ↦ x(s, u)` are timelike for
all small `s > 0` (`eventually_isPathOn_variation`). This is the pointwise form of the second
variation argument of O'Neill, Semi-Riemannian geometry, Proposition 10.48, p. 296.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Filter Function

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n}

/-- A tube lemma: an open condition holding on `{0} × K`, `K` compact, holds on
`(-ε, ε) × K` for some `ε > 0`. -/
theorem eventually_forall_mem_of_continuousOn {Z : Type*} [TopologicalSpace Z] {K : Set ℝ}
    (hK : IsCompact K) {f : ℝ → ℝ → Z} (hf : ContinuousOn (uncurry f) (univ ×ˢ K))
    {O : Set Z} (hO : IsOpen O) (h0 : ∀ u ∈ K, f 0 u ∈ O) :
    ∀ᶠ s in 𝓝 0, ∀ u ∈ K, f s u ∈ O := by
  have key : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ u ∈ K, u ∈ K → f s u ∈ O :=
    hK.eventually_forall_of_forall_eventually (P := fun s u => u ∈ K → f s u ∈ O)
      fun u hu => by
        have hc : ContinuousWithinAt (uncurry f) (univ ×ˢ K) (0, u) := hf _ ⟨mem_univ _, hu⟩
        have := eventually_nhdsWithin_iff.1 (hc.preimage_mem_nhdsWithin (hO.mem_nhds (h0 u hu)))
        filter_upwards [this] with z hz
        exact fun hz2 => hz ⟨mem_univ _, hz2⟩
  filter_upwards [key] with s hs u hu using hs u hu hu

/-- If `L(a) = 0`, `dL(a) b = 0` and `d²L(a)(b, b) + 2 dL(a) c < 0` on a compact set, then
`L(a + s b + s² c) < 0` there for all small `s > 0`. -/
theorem eventually_neg_of_second_variation {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {L : F → ℝ} (hL : ContDiff ℝ ∞ L) {K : Set ℝ} (hK : IsCompact K)
    {a b c : ℝ → F} (ha : ContinuousOn a K) (hb : ContinuousOn b K) (hc : ContinuousOn c K)
    (h0 : ∀ u ∈ K, L (a u) = 0) (h1 : ∀ u ∈ K, fderiv ℝ L (a u) (b u) = 0)
    (h2 : ∀ u ∈ K, fderiv ℝ (fderiv ℝ L) (a u) (b u) (b u) + 2 * fderiv ℝ L (a u) (c u) < 0) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ K, L (a u + s • b u + s ^ 2 • c u) < 0 := by
  have hDL : ContDiff ℝ ∞ (fderiv ℝ L) := hL.fderiv_right (m := ∞) (by simp)
  have hDDL : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ L)) := hDL.fderiv_right (m := ∞) (by simp)
  set p : ℝ → ℝ → F := fun s u => a u + s • b u + s ^ 2 • c u
  set q : ℝ → ℝ → F := fun s u => b u + (2 * s) • c u
  set k2 : ℝ → ℝ → ℝ := fun s u =>
    fderiv ℝ (fderiv ℝ L) (p s u) (q s u) (q s u) + fderiv ℝ L (p s u) ((2 : ℝ) • c u)
  have hpc : ContinuousOn (uncurry p) (univ ×ˢ K) :=
    ((ha.comp continuousOn_snd fun z hz => hz.2).add
      (continuousOn_fst.smul (hb.comp continuousOn_snd fun z hz => hz.2))).add
      ((continuousOn_fst.pow 2).smul (hc.comp continuousOn_snd fun z hz => hz.2))
  have hqc : ContinuousOn (uncurry q) (univ ×ˢ K) :=
    (hb.comp continuousOn_snd fun z hz => hz.2).add
      ((continuousOn_const.mul continuousOn_fst).smul (hc.comp continuousOn_snd fun z hz => hz.2))
  have hk2 : ContinuousOn (uncurry k2) (univ ×ˢ K) :=
    (((hDDL.continuous.comp_continuousOn hpc).clm_apply hqc).clm_apply hqc).add
      ((hDL.continuous.comp_continuousOn hpc).clm_apply
        (continuousOn_const.smul (hc.comp continuousOn_snd fun z hz => hz.2)))
  have hk20 : ∀ u ∈ K, k2 0 u ∈ Iio 0 := fun u hu => by
    have := h2 u hu
    simp only [k2, p, q, mul_zero, zero_smul, add_zero, zero_pow two_ne_zero, map_smul,
      smul_eq_mul, mem_Iio]
    linarith
  obtain ⟨ε, hε, hεk⟩ := Metric.eventually_nhds_iff.1
    (eventually_forall_mem_of_continuousOn hK hk2 isOpen_Iio hk20)
  filter_upwards [Ioo_mem_nhdsGT hε] with s hs u hu
  have hp : ∀ t, HasDerivAt (fun t => p t u) (q t u) t := fun t => by
    have h := (((hasDerivAt_id t).smul_const (b u)).const_add (a u)).add
      ((hasDerivAt_pow 2 t).smul_const (c u))
    convert h using 1
    · rfl
    · simp [q]
  have hq : ∀ t, HasDerivAt (fun t => q t u) ((2 : ℝ) • c u) t := fun t => by
    have := (((hasDerivAt_id t).const_mul (2 : ℝ)).smul_const (c u)).const_add (b u)
    simp only [id, mul_one] at this
    exact this
  have hk : ∀ t, HasDerivAt (fun t => L (p t u)) (fderiv ℝ L (p t u) (q t u)) t := fun t =>
    (hL.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t (hp t)
  have hk' : ∀ t, HasDerivAt (fun t => fderiv ℝ L (p t u) (q t u)) (k2 t u) t := fun t =>
    hasDerivAt_fderiv_apply hL (hp t) (hq t)
  have hneg : ∀ t ∈ Ioo 0 s, k2 t u < 0 := fun t ht => by
    have := hεk (show dist t 0 < ε by
      rw [Real.dist_eq, sub_zero, abs_lt]; constructor <;> linarith [ht.1, ht.2, hs.2]) u hu
    exact this
  have hanti1 : StrictAntiOn (fun t => fderiv ℝ L (p t u) (q t u)) (Icc 0 s) :=
    strictAntiOn_of_deriv_neg (convex_Icc 0 s)
      (fun t _ => (hk' t).continuousAt.continuousWithinAt) fun t ht => by
        rw [interior_Icc] at ht
        rw [(hk' t).deriv]
        exact hneg t ht
  have hd0 : fderiv ℝ L (p 0 u) (q 0 u) = 0 := by
    simpa [p, q] using h1 u hu
  have hanti : StrictAntiOn (fun t => L (p t u)) (Icc 0 s) :=
    strictAntiOn_of_deriv_neg (convex_Icc 0 s)
      (fun t _ => (hk t).continuousAt.continuousWithinAt) fun t ht => by
        rw [interior_Icc] at ht
        rw [(hk t).deriv, ← hd0]
        exact hanti1 ⟨le_refl 0, hs.1.le⟩ ⟨ht.1.le, ht.2.le⟩ ht.1
  have := hanti ⟨le_refl 0, hs.1.le⟩ ⟨hs.1.le, le_rfl⟩ hs.1
  simp only [p, zero_smul, add_zero, zero_pow two_ne_zero, h0 u hu] at this
  exact this

/-- Timelike curves from a variation `σ + s V + s² Z` of a future-directed null curve `σ` whose
energy density has vanishing first and negative second `s`-derivative. -/
theorem eventually_isPathOn_variation (hg : IsSpacetime g Y) {σ V Z : ℝ → E n} {U : Set ℝ}
    (hU : IsOpen U) {α β : ℝ} (hαβ : α < β) (hsub : Icc α β ⊆ U)
    (hσ : ContDiffOn ℝ ∞ σ U) (hV : ContDiffOn ℝ ∞ V U) (hZ : ContDiffOn ℝ ∞ Z U)
    (hfut : ∀ u ∈ Icc α β, IsFutureCausal g Y (σ u) (deriv σ u))
    (hnull : ∀ u ∈ Icc α β, form (g (σ u)) (deriv σ u) (deriv σ u) = 0)
    (h1 : ∀ u ∈ Icc α β,
      fderiv ℝ (lagrangian g) (σ u, deriv σ u) (V u, deriv V u) = 0)
    (h2 : ∀ u ∈ Icc α β,
      fderiv ℝ (fderiv ℝ (lagrangian g)) (σ u, deriv σ u) (V u, deriv V u) (V u, deriv V u) +
        2 * fderiv ℝ (lagrangian g) (σ u, deriv σ u) (Z u, deriv Z u) < 0) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, IsPathOn (IsFutureTimelike g Y) α β
      (fun u => σ u + s • V u + s ^ 2 • Z u) := by
  have hK : IsCompact (Icc α β) := isCompact_Icc
  have hd : ∀ {f : ℝ → E n}, ContDiffOn ℝ ∞ f U → ∀ u ∈ U, HasDerivAt f (deriv f u) u :=
    fun hf u hu => ((hf.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hu)).hasDerivAt
  have hc : ∀ {f : ℝ → E n}, ContDiffOn ℝ ∞ f U →
      ContinuousOn (fun u => (f u, deriv f u)) (Icc α β) := fun hf =>
    (hf.continuousOn.prodMk (hf.deriv_of_isOpen hU (m := ∞) (by simp)).continuousOn).mono hsub
  set x : ℝ → ℝ → E n := fun s u => σ u + s • V u + s ^ 2 • Z u
  have hx : ∀ s, ∀ u ∈ U, HasDerivAt (x s) (deriv σ u + s • deriv V u + s ^ 2 • deriv Z u) u :=
    fun s u hu => (((hd hσ u hu).add ((hd hV u hu).const_smul s)).add
      ((hd hZ u hu).const_smul (s ^ 2)))
  have hdata : ∀ s, ∀ u ∈ U, (x s u, deriv (x s) u) =
      (σ u, deriv σ u) + s • (V u, deriv V u) + s ^ 2 • (Z u, deriv Z u) := fun s u hu => by
    rw [(hx s u hu).deriv]
    simp only [x, Prod.smul_mk, Prod.mk_add_mk]
  have hneg := eventually_neg_of_second_variation (contDiff_lagrangian hg) hK (hc hσ) (hc hV)
    (hc hZ) (fun u hu => by rw [lagrangian_def]; exact hnull u hu) h1 h2
  have hO : IsOpen { z : E n × E n | form (g z.1) z.2 (Y z.1) < 0 } := by
    have hY := hg.globallyHyperbolic.timeOrientation.continuous
    exact isOpen_lt ((contDiff_form hg).continuous.comp (continuous_fst.prodMk
      (continuous_snd.prodMk (hY.comp continuous_fst)))) continuous_const
  have hσc := (hc hσ).comp (continuousOn_snd (s := (univ : Set ℝ) ×ˢ Icc α β)) fun z hz => hz.2
  have hVc := (hc hV).comp (continuousOn_snd (s := (univ : Set ℝ) ×ˢ Icc α β)) fun z hz => hz.2
  have hZc := (hc hZ).comp (continuousOn_snd (s := (univ : Set ℝ) ×ˢ Icc α β)) fun z hz => hz.2
  have hfc : ContinuousOn (fun z : ℝ × ℝ =>
      (σ z.2, deriv σ z.2) + z.1 • (V z.2, deriv V z.2) + z.1 ^ 2 • (Z z.2, deriv Z z.2))
      (univ ×ˢ Icc α β) :=
    (hσc.add (continuousOn_fst.smul hVc)).add ((continuousOn_fst.pow 2).smul hZc)
  have hfut' := eventually_forall_mem_of_continuousOn hK (f := fun s u =>
      (σ u, deriv σ u) + s • (V u, deriv V u) + s ^ 2 • (Z u, deriv Z u)) hfc hO fun u hu => by
    simpa using (hfut u hu).future
  filter_upwards [hneg, nhdsWithin_le_nhds hfut'] with s hs hs'
  refine isPathOn_iff.2 ⟨hαβ, ∅, fun a b hαa hab hbβ _ => isPathPiece_iff.2 ⟨?_, fun t ht => ?_⟩⟩
  · exact ((hσ.add (hV.const_smul s)).add (hZ.const_smul (s ^ 2))).mono
      ((Icc_subset_Icc hαa hbβ).trans hsub)
  · have htI : t ∈ Icc α β := ⟨hαa.trans ht.1, ht.2.trans hbβ⟩
    have htU := hsub htI
    rw [(hx s t htU).hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hab t ht),
      ← (hx s t htU).deriv]
    have e := hdata s t htU
    refine ⟨?_, ?_⟩
    · have := hs t htI
      rw [← e] at this
      simpa only [lagrangian_def] using this
    · have := hs' t htI
      rw [← e] at this
      exact this

end

end LorentzianCalderon
