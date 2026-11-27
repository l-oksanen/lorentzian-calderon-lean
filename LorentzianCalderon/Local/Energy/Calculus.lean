module

public import LorentzianCalderon.Local.Differential
public import LorentzianCalderon.Local.Energy.Cutoff

public section

/-!
# Calculus on `ℝ^{1+n}` for the energy inequality

The divergence theorem for a compactly supported `C¹` vector field, the volume of thin slabs
`{a ≤ ψ ≤ a + ε}` for `ψ` with nonvanishing differential, and the nullity of its level sets.
-/

namespace LorentzianCalderon

noncomputable section
open Set MeasureTheory Filter Topology
open scoped ContDiff

variable {n : ℕ}

section Divergence

/-- The divergence theorem for the `C¹` vector field `f V`, supported in the compact set `K`
inside the open set `U` on which `f` and `V` are `C¹`. -/
theorem integral_div_eq_zero {U K : Set (E n)} (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) {f : E n → ℝ} {V : Fin (n + 1) → E n → ℝ} (hf : ContDiffOn ℝ 1 f U)
    (hV : ∀ j, ContDiffOn ℝ 1 (V j) U) (h0 : ∀ j, ∀ x ∈ U \ K, f x * V j x = 0) :
    ∫ x in K, ∑ j, (d f x j * V j x + f x * d (V j) x j) = 0 := by
  set F : Fin (n + 1) → E n → ℝ := fun j => K.indicator fun x => f x * V j x
  have hU' : ∀ j, ∀ x ∈ U, F j =ᶠ[𝓝 x] fun y => f y * V j y := by
    intro j x hx
    filter_upwards [hU.mem_nhds hx] with y hy
    by_cases hyK : y ∈ K
    · simp [F, hyK]
    · simp [F, hyK, h0 j y ⟨hy, hyK⟩]
  have hK' : ∀ j, ∀ x ∉ K, F j =ᶠ[𝓝 x] fun _ => 0 := by
    intro j x hx
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact indicator_of_notMem hy _
  have hC : ∀ j, ContDiff ℝ 1 (F j) := by
    intro j
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U
    · exact ((hf.mul (hV j)).contDiffAt (hU.mem_nhds hx)).congr_of_eventuallyEq (hU' j x hx)
    · exact contDiffAt_const.congr_of_eventuallyEq (hK' j x fun h => hx (hKU h))
  have hS : ∀ j, HasCompactSupport (F j) := fun j =>
    HasCompactSupport.intro hK fun x hx => by simp [F, hx]
  have hD : ∀ j x, d (F j) x j =
      K.indicator (fun x => d f x j * V j x + f x * d (V j) x j) x := by
    intro j x
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx, d_congr (hU' j x (hKU hx)),
        d_mul ((hf.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds (hKU hx)))
          (((hV j).differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds (hKU hx)))]
    · rw [indicator_of_notMem hx, d_congr (hK' j x hx)]
      simp [d_def]
  have hzero : ∀ j, ∫ x, d (F j) x j = 0 := by
    intro j
    have hint : Integrable fun x => fderiv ℝ (F j) x (EuclideanSpace.single j 1) :=
      (((hC j).continuous_fderiv one_ne_zero).clm_apply
        continuous_const).integrable_of_hasCompactSupport ((hS j).fderiv_apply (𝕜 := ℝ) _)
    have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      (f := fun _ => (1 : ℝ)) (g := F j) (v := EuclideanSpace.single j 1)
      (by simp) (by simpa using hint)
      (by simpa using ((hC j).continuous.integrable_of_hasCompactSupport (hS j)))
      (fun _ _ => differentiableAt_const _)
      (fun x _ => (hC j).differentiable one_ne_zero x)
    simpa [d_def] using this
  have hint : ∀ j, Integrable fun x => d (F j) x j := by
    intro j
    simp only [d_def]
    exact (((hC j).continuous_fderiv one_ne_zero).clm_apply
      continuous_const).integrable_of_hasCompactSupport ((hS j).fderiv_apply (𝕜 := ℝ) _)
  calc ∫ x in K, ∑ j, (d f x j * V j x + f x * d (V j) x j)
      = ∫ x, ∑ j, d (F j) x j := by
        rw [← integral_indicator hK.measurableSet]
        congr 1; ext x
        simp only [hD]
        by_cases hx : x ∈ K <;> simp [hx]
    _ = 0 := by
        rw [integral_finsetSum _ fun j _ => hint j]
        simp [hzero]

end Divergence

section Slab

/-- Thin slabs `{a ≤ ψ ≤ a + ε}` of a function with nonvanishing differential have volume
`O(ε)`, uniformly in `a`. -/
theorem slab_volume_le {U K : Set (E n)} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {ψ : E n → ℝ} (hψ : ContDiffOn ℝ 2 ψ U) (hdψ : ∀ x ∈ U, d ψ x ≠ 0) :
    ∃ C, ∀ a ε, 0 < ε → volume.real (K ∩ ψ ⁻¹' Icc a (a + ε)) ≤ C * ε := by
  obtain ⟨θ, hθ, hθ01, hK', hK'U, hθK⟩ := exists_cutoff hK hU hKU
  have hθ1 : ∀ x ∈ K, θ x = 1 := fun x hx => (hθK x hx).eq_of_nhds
  set K' := tsupport θ
  have hθ0 : ∀ x ∉ K', θ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  set N : E n → ℝ := fun y => ∑ i, d ψ y i ^ 2
  have hN0 : ∀ y ∈ U, N y ≠ 0 := by
    intro y hy h
    apply hdψ y hy
    ext i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (d ψ y i))).1 h i
      (Finset.mem_univ _)
    simpa using this
  have hd1 : ∀ i, ContDiffOn ℝ 1 (fun y => d ψ y i) U := contDiffOn_d_of_le hU hψ (by norm_num)
  have hN : ContDiffOn ℝ 1 N U := ContDiffOn.sum fun i _ => (hd1 i).pow 2
  set V : Fin (n + 1) → E n → ℝ := fun j y => θ y * d ψ y j / N y
  have hV : ∀ j, ContDiffOn ℝ 1 (V j) U := fun j =>
    ((hθ.of_le (by simp)).contDiffOn.mul (hd1 j)).div hN hN0
  have hψc : ContinuousOn ψ U := hψ.continuousOn
  have hdivc : ContinuousOn (fun x => ∑ j, d (V j) x j) U :=
    continuousOn_finsetSum _ fun j _ => continuousOn_d_of_contDiffOn hU (hV j) j
  set C₀ := ∫ x in K', |∑ j, d (V j) x j|
  refine ⟨2 * C₀, fun a ε hε => ?_⟩
  set h : ℝ → ℝ := fun r => 2 * ε * cutoff ((r - a) / (2 * ε) + 1 / 4)
  set h' : ℝ → ℝ := fun r => cutoffDeriv ((r - a) / (2 * ε) + 1 / 4)
  have hh : ∀ r, HasDerivAt h (h' r) r := by
    intro r
    have := ((hasDerivAt_cutoff ((r - a) / (2 * ε) + 1 / 4)).comp r
      ((((hasDerivAt_id r).sub_const a).div_const (2 * ε)).add_const (1 / 4))).const_mul
      (2 * ε)
    refine this.congr_deriv ?_
    simp only [h']
    field_simp
  have hhC : ContDiff ℝ 1 h :=
    contDiff_const.mul (contDiff_cutoff.comp ((contDiff_id.sub contDiff_const).div_const _
      |>.add contDiff_const))
  set f : E n → ℝ := fun y => h (ψ y)
  have hf : ContDiffOn ℝ 1 f U := hhC.comp_contDiffOn (hψ.of_le one_le_two)
  have h0 : ∀ j, ∀ x ∈ U \ K', f x * V j x = 0 := by
    intro j x hx
    simp [V, hθ0 x hx.2]
  have key := integral_div_eq_zero hU hK' hK'U hf hV h0
  have hsplit : ∀ x ∈ U, ∑ j, (d f x j * V j x + f x * d (V j) x j) =
      h' (ψ x) * θ x + f x * ∑ j, d (V j) x j := by
    intro x hx
    have hψd : DifferentiableAt ℝ ψ x :=
      (hψ.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hx)
    have hdf : ∀ j, d f x j = h' (ψ x) * d ψ x j := fun j => d_comp_of_hasDerivAt (hh (ψ x)) hψd j
    simp only [hdf, Finset.sum_add_distrib, ← Finset.mul_sum]
    congr 1
    simp only [V]
    have : ∑ j, h' (ψ x) * d ψ x j * (θ x * d ψ x j / N x) =
        h' (ψ x) * θ x * (∑ j, d ψ x j ^ 2) / N x := by
      rw [Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this, mul_div_assoc, div_self (hN0 x hx), mul_one]
  have hK'm : MeasurableSet K' := hK'.measurableSet
  have hgc : ContinuousOn (fun x => h' (ψ x) * θ x) U :=
    ((continuous_cutoffDeriv.comp_continuousOn
      (((hψc.sub continuousOn_const).div_const _).add continuousOn_const))).mul
      hθ.continuous.continuousOn
  have hfdc : ContinuousOn (fun x => f x * ∑ j, d (V j) x j) U :=
    (hhC.continuous.comp_continuousOn hψc).mul hdivc
  have hgi : IntegrableOn (fun x => h' (ψ x) * θ x) K' :=
    (hgc.mono hK'U).integrableOn_compact hK'
  have hfdi : IntegrableOn (fun x => f x * ∑ j, d (V j) x j) K' :=
    (hfdc.mono hK'U).integrableOn_compact hK'
  have hdivi : IntegrableOn (fun x => |∑ j, d (V j) x j|) K' :=
    (hdivc.abs.mono hK'U).integrableOn_compact hK'
  have hint_eq : ∫ x in K', h' (ψ x) * θ x = -∫ x in K', f x * ∑ j, d (V j) x j := by
    rw [setIntegral_congr_fun hK'm (fun x hx => hsplit x (hK'U hx)), integral_add hgi hfdi]
      at key
    linarith
  have hbound : -∫ x in K', f x * ∑ j, d (V j) x j ≤ 2 * C₀ * ε := by
    rw [← integral_neg]
    have : ∫ x in K', -(f x * ∑ j, d (V j) x j) ≤ ∫ x in K', 2 * ε * |∑ j, d (V j) x j| := by
      refine setIntegral_mono_on hfdi.neg (hdivi.const_mul _) hK'm fun x _ => ?_
      have hfx : |f x| ≤ 2 * ε := by
        have h1 := cutoff_nonneg ((ψ x - a) / (2 * ε) + 1 / 4)
        have h2 := cutoff_le_one ((ψ x - a) / (2 * ε) + 1 / 4)
        simp only [f, h]
        rw [abs_le]; constructor <;> nlinarith
      calc -(f x * ∑ j, d (V j) x j) ≤ |f x * ∑ j, d (V j) x j| := neg_le_abs _
        _ = |f x| * |∑ j, d (V j) x j| := abs_mul _ _
        _ ≤ 2 * ε * |∑ j, d (V j) x j| := by gcongr
    rw [integral_const_mul] at this
    linarith
  set S := K ∩ ψ ⁻¹' Icc a (a + ε)
  have hSK' : S ⊆ K' := fun x hx => by
    by_contra h'
    have := hθ0 x h'
    rw [hθ1 x hx.1] at this
    exact one_ne_zero this
  have hSm : MeasurableSet S :=
    ((hψc.mono hKU).preimage_isClosed_of_isClosed hK.isClosed isClosed_Icc).measurableSet
  have hvol : volume.real S ≤ ∫ x in K', h' (ψ x) * θ x := by
    calc volume.real S = ∫ x in S, (1 : ℝ) := by simp
      _ ≤ ∫ x in S, h' (ψ x) * θ x := by
        refine setIntegral_mono_on ?_ (hgi.mono_set hSK') hSm fun x hx => ?_
        · exact integrableOn_const (hK.measure_lt_top.trans_le' (measure_mono
            inter_subset_left)).ne
        · rw [hθ1 x hx.1, mul_one]
          have h1 : a ≤ ψ x := hx.2.1
          have h2 : ψ x ≤ a + ε := hx.2.2
          apply one_le_cutoffDeriv
          · have : 0 ≤ (ψ x - a) / (2 * ε) := div_nonneg (by linarith) (by positivity)
            linarith
          · have : (ψ x - a) / (2 * ε) ≤ 1 / 2 := by
              rw [div_le_iff₀ (by positivity)]; linarith
            linarith
      _ ≤ ∫ x in K', h' (ψ x) * θ x := by
        refine setIntegral_mono_set hgi ?_ (Eventually.of_forall hSK')
        refine (ae_restrict_iff' hK'm).2 (Eventually.of_forall fun x _ => ?_)
        exact mul_nonneg (cutoffDeriv_nonneg _) (hθ01 x).1
  linarith

end Slab

/-! ### Level sets -/

/-- Near a point where `dφ(e) = 1`, `φ` increases strictly along the direction `e`. -/
theorem lt_of_add_smul_of_fderiv_pos {φ : E n → ℝ} {U : Set (E n)} (hU : Convex ℝ U)
    (hφ : ∀ y ∈ U, DifferentiableAt ℝ φ y) {e : E n} (he : ∀ y ∈ U, 0 < fderiv ℝ φ y e)
    {p : E n} (hp : p ∈ U) {τ : ℝ} (hτ : 0 < τ) (hq : p + τ • e ∈ U) : φ p < φ (p + τ • e) := by
  have hseg : ∀ t ∈ Icc 0 τ, p + t • e ∈ U := fun t ht => by
    have := hU.add_smul_mem hp hq (t := t / τ) ⟨div_nonneg ht.1 hτ.le,
      (div_le_one hτ).2 ht.2⟩
    rwa [smul_smul, div_mul_cancel₀ t hτ.ne'] at this
  have hderiv : ∀ t ∈ Icc 0 τ, HasDerivAt (fun t : ℝ => φ (p + t • e))
      (fderiv ℝ φ (p + t • e) e) t := fun t ht => by
    have h1 : HasDerivAt (fun t : ℝ => p + t • e) e t := by
      simpa using ((hasDerivAt_id t).smul_const e).const_add p
    exact (hφ _ (hseg t ht)).hasFDerivAt.comp_hasDerivAt t h1
  have hmono := strictMonoOn_of_deriv_pos (convex_Icc 0 τ) (f := fun t : ℝ => φ (p + t • e))
    (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt) fun t ht => by
      rw [(hderiv t (interior_subset ht)).deriv]
      exact he _ (hseg t (interior_subset ht))
  simpa using hmono ⟨le_rfl, hτ.le⟩ ⟨hτ.le, le_rfl⟩ hτ

/-- A closed piece of a level set of a `C¹` function with nonvanishing differential is null: its
translates in a direction transversal to it are disjoint. -/
theorem exists_nhds_volume_level_eq_zero {V : Set (E n)} (hV : IsOpen V) {φ : E n → ℝ}
    (hφ : ContDiffOn ℝ 1 φ V) {x₀ : E n} (hx₀ : x₀ ∈ V) (hdφ : fderiv ℝ φ x₀ ≠ 0) (s : ℝ) :
    ∃ u ∈ 𝓝 x₀, volume (u ∩ φ ⁻¹' {s}) = 0 := by
  obtain ⟨w, hw⟩ : ∃ w, fderiv ℝ φ x₀ w ≠ 0 := by
    by_contra! h
    exact hdφ (ContinuousLinearMap.ext h)
  set e : E n := (fderiv ℝ φ x₀ w)⁻¹ • w
  have he : fderiv ℝ φ x₀ e = 1 := by simp [e, hw]
  have hcont : ContinuousOn (fun y => fderiv ℝ φ y e) V :=
    (hφ.continuousOn_fderiv_of_isOpen hV le_rfl).clm_apply continuousOn_const
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.1
    (hcont.isOpen_inter_preimage hV (isOpen_Ioi (a := (1 / 2 : ℝ)))) x₀
    ⟨hx₀, by simp [he]; norm_num⟩
  set U := Metric.ball x₀ r
  have hdiff : ∀ y ∈ U, DifferentiableAt ℝ φ y := fun y hy =>
    (hφ.contDiffAt (hV.mem_nhds (hrV hy).1)).differentiableAt one_ne_zero
  have hpos : ∀ y ∈ U, 0 < fderiv ℝ φ y e := fun y hy => by
    have : (1 / 2 : ℝ) < fderiv ℝ φ y e := (hrV hy).2
    linarith
  set C := Metric.closedBall x₀ (r / 2) ∩ φ ⁻¹' {s}
  have hCU : Metric.closedBall x₀ (r / 2) ⊆ U := Metric.closedBall_subset_ball (by linarith)
  have hCm : MeasurableSet C :=
    (((hφ.continuousOn.mono fun y hy => (hrV (hCU hy)).1)).preimage_isClosed_of_isClosed
      Metric.isClosed_closedBall isClosed_singleton).measurableSet
  refine ⟨Metric.closedBall x₀ (r / 2), Metric.closedBall_mem_nhds x₀ (by linarith), ?_⟩
  by_contra hC
  set c : ℕ → ℝ := fun k => (k : ℝ) / (k + 1)
  have hc : StrictMono c := fun i j hij => by
    simp only [c]
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have : (i : ℝ) < j := by exact_mod_cast hij
    nlinarith
  have hc1 : ∀ k, c k < 1 := fun k => by
    simp only [c]
    rw [div_lt_one (by positivity)]
    linarith
  set D : ℕ → Set (E n) := fun k => (· + -(c k • e)) ⁻¹' C
  have hDm : ∀ k, MeasurableSet (D k) := fun k => hCm.preimage (measurable_add_const _)
  have hDμ : ∀ k, volume (D k) = volume C := fun k => measure_preimage_add_right _ _ _
  have hdisj : ∀ i j, i < j → Disjoint (D i) (D j) := fun i j hij => by
    refine Set.disjoint_left.2 fun y hyi hyj => ?_
    simp only [D, mem_preimage, C, mem_inter_iff, mem_singleton_iff] at hyi hyj
    have hτ : 0 < c j - c i := sub_pos.2 (hc hij)
    have heq : y + -(c j • e) + (c j - c i) • e = y + -(c i • e) := by
      rw [sub_smul]
      abel
    have := lt_of_add_smul_of_fderiv_pos (convex_ball x₀ r) hdiff hpos (hCU hyj.1) hτ
      (by rw [heq]; exact hCU hyi.1)
    rw [heq, hyi.2, hyj.2] at this
    exact lt_irrefl _ this
  have hsub : ∀ k, D k ⊆ Metric.closedBall x₀ (r / 2 + ‖e‖) := fun k y hy => by
    have h1 : dist (y + -(c k • e)) x₀ ≤ r / 2 := hy.1
    have h2 : ‖c k • e‖ ≤ ‖e‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_of_le_one_left (norm_nonneg _) (hc1 k).le
    rw [Metric.mem_closedBall]
    calc dist y x₀ ≤ dist (y + -(c k • e)) x₀ + ‖c k • e‖ := by
          rw [dist_eq_norm, dist_eq_norm]
          calc ‖y - x₀‖ = ‖(y + -(c k • e) - x₀) + c k • e‖ := by congr 1; abel
            _ ≤ _ := norm_add_le _ _
      _ ≤ r / 2 + ‖e‖ := add_le_add h1 h2
  obtain ⟨m, hm⟩ := ENNReal.exists_nat_mul_gt hC
    (measure_closedBall_lt_top (μ := volume) (x := x₀) (r := r / 2 + ‖e‖)).ne
  have hsum : volume (⋃ k ∈ Finset.range m, D k) = m * volume C := by
    rw [measure_biUnion_finset (fun i _ j _ hij => ?_) fun k _ => hDm k]
    · simp [hDμ]
    · rcases lt_or_gt_of_ne hij with h | h
      · exact hdisj i j h
      · exact (hdisj j i h).symm
  have hle := measure_mono (μ := volume) (iUnion₂_subset fun k (_ : k ∈ Finset.range m) => hsub k)
  rw [hsum] at hle
  exact absurd hle (not_le.2 hm)

/-- The level sets of a `C¹` function with nonvanishing differential are Lebesgue-null. -/
theorem volume_inter_level_eq_zero {V : Set (E n)} (hV : IsOpen V) {φ : E n → ℝ}
    (hφ : ContDiffOn ℝ 1 φ V) (hdφ : ∀ x ∈ V, fderiv ℝ φ x ≠ 0) (s : ℝ) :
    volume (V ∩ φ ⁻¹' {s}) = 0 := by
  refine measure_null_of_locally_null _ fun x hx => ?_
  obtain ⟨u, hu, hu0⟩ := exists_nhds_volume_level_eq_zero hV hφ hx.1 (hdφ x hx.1) s
  exact ⟨(V ∩ φ ⁻¹' {s}) ∩ u, inter_mem_nhdsWithin _ hu,
    measure_mono_null (show (V ∩ φ ⁻¹' {s}) ∩ u ⊆ u ∩ φ ⁻¹' {s} from
      fun y hy => ⟨hy.2, hy.1.2⟩) hu0⟩

/-- The level sets of a `C¹` function with nonvanishing differential are Lebesgue-null. -/
theorem volume_levelSet_eq_zero {U K : Set (E n)} (hU : IsOpen U) (hKU : K ⊆ U) {ψ : E n → ℝ}
    (hψ : ContDiffOn ℝ 1 ψ U) (hdψ : ∀ x ∈ U, d ψ x ≠ 0) (a : ℝ) :
    volume (K ∩ ψ ⁻¹' {a}) = 0 :=
  measure_mono_null (inter_subset_inter_left _ hKU) (volume_inter_level_eq_zero hU hψ
    (fun x hx h => hdψ x hx (d_eq_zero_of_fderiv h)) a)

end

end LorentzianCalderon
