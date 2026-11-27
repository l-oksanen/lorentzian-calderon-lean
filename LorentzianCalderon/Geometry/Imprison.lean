module

public import LorentzianCalderon.Geometry.GeodesicExtension
public import LorentzianCalderon.Causal.Imprisonment

public section

/-!
# Causal geodesic rays are not imprisoned

A future-directed causal geodesic ray `r ↦ exp_y (r w)`, followed on its whole domain, leaves
every compact set (`not_forall_expMap_smul_mem`). Reparametrized on `[0, ∞)`, the ray is an
inextendible causal curve, so this follows from `Facts.imprisonment`. That it has no limit
follows from `Facts.geodesic_extension` if its domain is bounded
(`IsGeodesic.exists_extension`), and from `IsGeodesic.not_tendsto_atTop` otherwise.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Filter

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n} {γ : ℝ → E n} {I : Set ℝ}

/-- A geodesic defined on `[a, ∞)` with nonzero velocity has no limit at `∞`. -/
theorem IsGeodesic.not_tendsto_atTop (hg : IsSpacetime g Y) (hγ : IsGeodesic g γ I) {a : ℝ}
    (hI : Ici a ⊆ I) (ha : deriv γ a ≠ 0) (x : E n) : ¬ Tendsto γ atTop (𝓝 x) := by
  intro hlim
  have hne : ∀ t ≥ a, deriv γ t ≠ 0 := fun t ht =>
    hγ.deriv_ne_zero hg hI ordConnected_Ici self_mem_Ici ha ht
  set u : ℝ → E n := fun t => ‖deriv γ t‖⁻¹ • deriv γ t
  have hu : ∀ t ≥ a, u t ∈ Metric.sphere (0 : E n) 1 := fun t ht => by
    simp [u, norm_smul, hne t ht]
  set T : ℕ → ℝ := fun j => a + j
  have hTa : ∀ j, a ≤ T j := fun j => by simp [T]
  obtain ⟨v, hv, φ, hφ, hlimu⟩ := (isCompact_sphere (0 : E n) 1).tendsto_subseq
    (x := fun j => u (T j)) (fun j => hu _ (hTa j))
  have hT : Tendsto (fun j => T (φ j)) atTop atTop :=
    (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop).comp hφ.tendsto_atTop
  have hΩ := isOpen_expDomain hg (g := g)
  obtain ⟨S, hS, hSdom⟩ : ∃ S : ℝ, 0 < S ∧ InExpDomain g x (S • v) := by
    have hev : ∀ᶠ s in 𝓝 (0 : ℝ), InExpDomain g x (s • v) :=
      (by fun_prop : Continuous fun s : ℝ => (x, s • v)).continuousAt.preimage_mem_nhds
        (hΩ.mem_nhds (by simpa using inExpDomain_zero (g := g) x))
    obtain ⟨s, hs, hs'⟩ := ((hev.filter_mono (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))).and
      (self_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0))).exists
    exact ⟨s, hs', hs⟩
  have hconst : ∀ τ ∈ Icc (0 : ℝ) 1, expMap g x (τ • S • v) = x := by
    intro τ hτ
    have hd : InExpDomain g x ((τ * S) • v) := by
      rw [← smul_smul]
      exact hSdom.smul hg hτ
    have h1 : Tendsto (fun j => expMap g (γ (T (φ j))) ((τ * S) • u (T (φ j)))) atTop
        (𝓝 (expMap g x ((τ * S) • v))) := by
      have hc := (contDiffOn_expMap hg).continuousOn.continuousAt
        (hΩ.mem_nhds (show (x, (τ * S) • v) ∈ _ from hd))
      exact hc.tendsto.comp ((hlim.comp hT).prodMk_nhds (hlimu.const_smul (τ * S)))
    have h2 : Tendsto (fun j => expMap g (γ (T (φ j))) ((τ * S) • u (T (φ j)))) atTop
        (𝓝 x) := by
      have hτS : 0 ≤ τ * S := mul_nonneg hτ.1 hS.le
      have heq : ∀ j, expMap g (γ (T (φ j))) ((τ * S) • u (T (φ j))) =
          γ (‖deriv γ (T (φ j))‖⁻¹ * (τ * S) + T (φ j)) := fun j => by
        refine (hγ.expMap_smul_smul_deriv hg fun σ hσ => hI ?_).2
        rw [uIcc_of_le hτS] at hσ
        have : 0 ≤ ‖deriv γ (T (φ j))‖⁻¹ * σ := mul_nonneg (by positivity) hσ.1
        simp only [mem_Ici]
        linarith [hTa (φ j)]
      simp only [heq]
      refine hlim.comp (tendsto_atTop_mono (fun j => ?_) hT)
      have : 0 ≤ ‖deriv γ (T (φ j))‖⁻¹ * (τ * S) := mul_nonneg (by positivity) hτS
      linarith
    rw [← smul_smul] at h1
    exact tendsto_nhds_unique h1 h2
  obtain ⟨ε, hε, hσ, -, -, hσ'⟩ := InExpDomain.isGeodesic_expMap_smul hg hSdom
  have hsub : Icc (0 : ℝ) 1 ⊆ Ioo (-ε) (1 + ε) := Icc_subset_Ioo (by linarith) (by linarith)
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp at hv
  refine hσ.deriv_ne_zero hg hsub ordConnected_Icc (left_mem_Icc.2 zero_le_one)
    (by rw [hσ']; exact smul_ne_zero hS.ne' hv0) (t := 1 / 2) ⟨by norm_num, by norm_num⟩ ?_
  have hev : (fun τ : ℝ => expMap g x (τ • S • v)) =ᶠ[𝓝 (1 / 2)] fun _ => x := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)] with τ hτ
    exact hconst τ (Ioo_subset_Icc_self hτ)
  rw [hev.deriv_eq, deriv_const]

/-- A future-directed causal geodesic on `[a, b)` with a limit at `b` extends to a geodesic on
a neighbourhood of `[a, b]`. -/
theorem IsGeodesic.exists_extension (hg : IsSpacetime g Y) (hγ : IsGeodesic g γ I) {a b : ℝ}
    (hab : a < b) (hI : Ico a b ⊆ I)
    (hc : ∀ t ∈ Ioo a b, IsFutureCausal g Y (γ t) (deriv γ t)) {x : E n}
    (hlim : Tendsto γ (𝓝[<] b) (𝓝 x)) :
    ∃ (σ : ℝ → E n) (J : Set ℝ), IsGeodesic g σ J ∧ Icc a b ⊆ J ∧ σ =ᶠ[𝓝 a] γ := by
  obtain ⟨σ, J, hσ, hJ, heq⟩ := Facts.geodesic_extension hg hab
    (hγ.mono (Ioo_subset_Ico_self.trans hI) isOpen_Ioo) hc hlim
  set m := (a + b) / 2
  have ham : a < m := by simp only [m]; linarith
  have hmb : m < b := by simp only [m]; linarith
  classical
  refine ⟨fun t => if t < m then γ t else σ t, (I ∩ Iio m) ∪ Ioo a b ∪ (J ∩ Ioi m), ?_, ?_, ?_⟩
  · refine isGeodesic_of_locally (((hγ.isOpen.inter isOpen_Iio).union isOpen_Ioo).union
      (hσ.isOpen.inter isOpen_Ioi)) fun t ht => ?_
    rcases ht with (⟨htI, htm⟩ | htab) | ⟨htJ, htm⟩
    · refine ⟨γ, I, hγ, htI, ?_⟩
      filter_upwards [Iio_mem_nhds htm] with s hs
      simp [show s < m from hs]
    · refine ⟨γ, I, hγ, hI (Ioo_subset_Ico_self htab), ?_⟩
      filter_upwards [Ioo_mem_nhds htab.1 htab.2] with s hs
      split_ifs
      · rfl
      · exact (heq hs).symm
    · refine ⟨σ, J, hσ, htJ, ?_⟩
      filter_upwards [Ioi_mem_nhds htm] with s hs
      simp [not_lt.2 (show m < s from hs).le]
  · intro t ht
    rcases ht.1.eq_or_lt with rfl | h1
    · exact Or.inl (Or.inl ⟨hI ⟨le_rfl, hab⟩, ham⟩)
    rcases ht.2.eq_or_lt with rfl | h2
    · exact Or.inr ⟨hJ ⟨hab, le_rfl⟩, hmb⟩
    · exact Or.inl (Or.inr ⟨h1, h2⟩)
  · filter_upwards [Iio_mem_nhds ham] with s hs
    simp [show s < m from hs]

/-- A geodesic on `[0, b)` with admissible velocities and without limit at `b`, reparametrized
on `[0, ∞)`, is an inextendible ray. -/
theorem IsGeodesic.isInextendibleRay_comp {P : E n → E n → Prop} (hP : ScaleInvariant P)
    (hγ : IsGeodesic g γ I) {b : ℝ} (hb : 0 < b) (hI : Ico 0 b ⊆ I)
    (hv : ∀ t ∈ Ico 0 b, P (γ t) (deriv γ t)) (hlim : ∀ x, ¬ Tendsto γ (𝓝[<] b) (𝓝 x)) :
    IsInextendibleRay P fun s => γ (b * s / (1 + s)) := by
  have hφ : ∀ s, 0 ≤ s → HasDerivAt (fun s => b * s / (1 + s)) (b / (1 + s) ^ 2) s := by
    intro s hs
    have := ((hasDerivAt_id' s).const_mul b).div ((hasDerivAt_id' s).const_add 1)
      (by linarith : (0 : ℝ) < 1 + s).ne'
    exact this.congr_deriv (by ring)
  have hmem : ∀ s, 0 ≤ s → b * s / (1 + s) ∈ Ico 0 b := fun s hs =>
    ⟨by positivity, by rw [div_lt_iff₀ (by linarith)]; nlinarith⟩
  refine ⟨fun a ha => isPathOn_iff.2 ⟨ha, ∅, fun x y hx hxy hya _ => isPathPiece_iff.2 ⟨?_,
    fun t ht => ?_⟩⟩,
    fun x h => hlim x ?_⟩
  · have hc : ContDiffOn ℝ ∞ (fun s => b * s / (1 + s)) (Icc x y) :=
      (contDiffOn_const.mul contDiffOn_id).div (contDiffOn_const.add contDiffOn_id)
        fun s hs => (by linarith [hs.1] : (0 : ℝ) < 1 + s).ne'
    exact hγ.smooth.comp hc fun s hs => hI (hmem s (hx.trans hs.1))
  · have ht0 : 0 ≤ t := hx.trans ht.1
    have hd : HasDerivAt (fun s => γ (b * s / (1 + s))) _ t :=
      (hγ.hasDerivAt (hI (hmem t ht0))).scomp t (hφ t ht0)
    rw [hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hxy t ht)]
    exact (scaleInvariant_iff.1 hP) _ _ _ (by positivity) (hv _ (hmem t ht0))
  · have hsub : Tendsto (fun r => b - r) (𝓝[<] b) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun r => b - r) (𝓝 b) (𝓝 (b - b)) := tendsto_const_nhds.sub tendsto_id
        rw [sub_self] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact sub_pos.2 (mem_Iio.1 hr)
    have hψ : Tendsto (fun r => r / (b - r)) (𝓝[<] b) atTop := by
      have := (tendsto_id.mono_left (nhdsWithin_le_nhds (s := Iio b) (a := b))).pos_mul_atTop
        hb (tendsto_inv_nhdsGT_zero.comp hsub)
      simpa [div_eq_mul_inv] using this
    refine (h.comp hψ).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr' : b - r ≠ 0 := (sub_pos.2 (mem_Iio.1 hr)).ne'
    have hb' := hb.ne'
    simp only [Function.comp]
    congr 1
    field_simp
    rw [sub_add_cancel, mul_div_assoc, mul_div_cancel₀ _ hb']

/-- A future-directed causal geodesic ray cannot stay in a compact set on its whole domain. -/
theorem not_forall_expMap_smul_mem (hg : IsSpacetime g Y) {y w : E n}
    (hw : IsFutureCausal g Y y w) {K : Set (E n)} (hK : IsCompact K) :
    ¬ ∀ r : ℝ, 0 ≤ r → InExpDomain g y (r • w) → expMap g y (r • w) ∈ K := by
  intro hmem
  set c : ℝ → E n := fun r => expMap g y (r • w)
  set U := {r : ℝ | InExpDomain g y (r • w)}
  obtain ⟨hc, hc0'⟩ := isGeodesic_expMap_smul hg y w (g := g)
  have hc0 : c 0 = y := by simp [c, expMap_zero hg]
  have h0U : (0 : ℝ) ∈ U := by simpa [U] using inExpDomain_zero (g := g) y
  have hv : ∀ J ⊆ U, J.OrdConnected → 0 ∈ J → ∀ t ∈ J, IsFutureCausal g Y (c t) (deriv c t) :=
    fun J hJ hJc h0 t ht => hc.isFutureCausal hg hJ hJc h0 (by rwa [hc0, hc0']) ht
  by_cases hA : ∀ r, 0 ≤ r → r ∈ U
  · have hray : IsInextendibleRay (IsFutureCausal g Y) c :=
      ⟨fun a ha => hc.isPathOn ha (fun t ht => hA t ht.1) fun t ht =>
          hv (Ici 0) (fun t ht => hA t ht) ordConnected_Ici self_mem_Ici t ht.1,
        hc.not_tendsto_atTop hg (fun t ht => hA t ht) (by rw [hc0']; exact hw.ne_zero)⟩
    exact Facts.imprisonment hg hK hray fun t ht => hmem t ht (hA t ht)
  · push Not at hA
    set B := {r : ℝ | 0 ≤ r ∧ r ∉ U}
    have hBc : IsClosed B := isClosed_Ici.inter hc.isOpen.isClosed_compl
    have hbdd : BddBelow B := ⟨0, fun _ h => h.1⟩
    have hbB : sInf B ∈ B := hBc.csInf_mem hA hbdd
    set b := sInf B
    have hb : 0 < b := lt_of_le_of_ne hbB.1 fun h => hbB.2 (h ▸ h0U)
    have hIco : Ico 0 b ⊆ U := fun r hr => by
      by_contra h
      exact (not_le.2 hr.2) (csInf_le hbdd ⟨hr.1, h⟩)
    have hray := hc.isInextendibleRay_comp scaleInvariant_isFutureCausal hb hIco
      (hv _ hIco ordConnected_Ico ⟨le_rfl, hb⟩) fun x hx => by
        obtain ⟨σ, J, hσ, hJ, heq⟩ := hc.exists_extension hg hb hIco (fun t ht =>
          hv _ hIco ordConnected_Ico ⟨le_rfl, hb⟩ t (Ioo_subset_Ico_self ht)) hx
        have := (hσ.expMap_smul_eq hg (t := b) (by rw [uIcc_of_le hb.le]; exact hJ)).1
        rw [heq.eq_of_nhds, heq.deriv_eq, hc0', zero_smul, expMap_zero hg] at this
        exact hbB.2 this
    refine Facts.imprisonment hg hK hray fun s hs => ?_
    have hφ : b * s / (1 + s) ∈ Ico 0 b :=
      ⟨by positivity, by rw [div_lt_iff₀ (by linarith)]; nlinarith⟩
    exact hmem _ hφ.1 (hIco hφ)

end

end LorentzianCalderon
