module

public import LorentzianCalderon.Facts.Vocabulary
public import LorentzianCalderon.Local.Energy.Cutoff

public section

namespace LorentzianCalderon.Facts

noncomputable section
open scoped ContDiff Matrix Topology
open Filter Set

namespace Borel

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A smooth function with compact support has bounded derivatives. -/
theorem exists_bound_iteratedFDeriv {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : G → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (j : ℕ) :
    ∃ C, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ C :=
  (hf.continuous_iteratedFDeriv (by simp)).bounded_above_of_compact_support (hc.iteratedFDeriv j)

/-- Composition with a linear map of norm at most `1` does not increase derivatives. -/
theorem norm_iteratedFDeriv_comp_le {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] {u : G → ℝ} (hu : ContDiff ℝ ∞ u) (L : H →L[ℝ] G)
    (hL : ‖L‖ ≤ 1) (m : ℕ) (p : H) :
    ‖iteratedFDeriv ℝ m (u ∘ L) p‖ ≤ ‖iteratedFDeriv ℝ m u (L p)‖ := by
  rw [L.iteratedFDeriv_comp_right hu p (by simp)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  calc _ ≤ ‖iteratedFDeriv ℝ m u (L p)‖ * 1 := by
        gcongr
        exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun _ _ => hL
    _ = _ := mul_one _

/-- Leibniz bound for `f(x) h(r)` on `F × ℝ`. -/
theorem norm_iteratedFDeriv_mul_prod_le {f : F → ℝ} {h : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hh : ContDiff ℝ ∞ h) (j : ℕ) (p : F × ℝ) :
    ‖iteratedFDeriv ℝ j (fun q : F × ℝ => f q.1 * h q.2) p‖ ≤
      ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * ‖iteratedFDeriv ℝ l f p.1‖ *
        ‖iteratedFDeriv ℝ (j - l) h p.2‖ := by
  refine (norm_iteratedFDeriv_mul_le (hf.comp contDiff_fst) (hh.comp contDiff_snd) p
    (n := j) (by simp)).trans (Finset.sum_le_sum fun l _ => ?_)
  have h1 : ‖iteratedFDeriv ℝ l (f ∘ Prod.fst) p‖ ≤ ‖iteratedFDeriv ℝ l f p.1‖ :=
    norm_iteratedFDeriv_comp_le hf (ContinuousLinearMap.fst ℝ F ℝ)
      (ContinuousLinearMap.norm_fst_le _ _ _) l p
  have h2 : ‖iteratedFDeriv ℝ (j - l) (h ∘ Prod.snd) p‖ ≤ ‖iteratedFDeriv ℝ (j - l) h p.2‖ :=
    norm_iteratedFDeriv_comp_le hh (ContinuousLinearMap.snd ℝ F ℝ)
      (ContinuousLinearMap.norm_snd_le _ _ _) (j - l) p
  gcongr

/-- Derivatives of the rescaling `ε^k g(r/ε)`. -/
theorem norm_iteratedDeriv_rescale {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (j k : ℕ) {ε : ℝ}
    (hε : 0 < ε) (r : ℝ) :
    ‖iteratedDeriv j (fun r => ε ^ k * g (ε⁻¹ * r)) r‖ =
      ε ^ k * ε⁻¹ ^ j * ‖iteratedDeriv j g (ε⁻¹ * r)‖ := by
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_comp_const_mul (hg.of_le (by simp))]
  simp only [norm_mul, norm_pow, norm_inv, Real.norm_of_nonneg hε.le]
  ring

/-- For `j < k` and `ε ≤ 1`, the `j`-th derivative of `ε^k g(r/ε)` is `O(ε)`. -/
theorem norm_iteratedDeriv_rescale_le {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) {j k : ℕ} (hjk : j < k)
    {M : ℝ} (hM : ∀ s, ‖iteratedFDeriv ℝ j g s‖ ≤ M) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (r : ℝ) : ‖iteratedDeriv j (fun r => ε ^ k * g (ε⁻¹ * r)) r‖ ≤ ε * M := by
  rw [norm_iteratedDeriv_rescale hg j k hε0]
  have hM' := hM (ε⁻¹ * r)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hM'
  have hpow : ε ^ k * ε⁻¹ ^ j ≤ ε := by
    rw [inv_pow, ← pow_sub₀ _ hε0.ne' hjk.le]
    exact (pow_le_pow_of_le_one hε0.le hε1 (by omega : 1 ≤ k - j)).trans_eq (pow_one ε)
  exact mul_le_mul hpow hM' (norm_nonneg _) hε0.le

/-- Termwise differentiation of a series on `ℝ` with summable uniform bounds. -/
theorem iteratedDeriv_tsum_apply {f : ℕ → ℝ → ℝ} (hf : ∀ i, ContDiff ℝ ∞ (f i))
    {v : ℕ → ℕ → ℝ} (hv : ∀ j, Summable (v j))
    (hfv : ∀ j i r, ‖iteratedDeriv j (f i) r‖ ≤ v j i) (k : ℕ) (r : ℝ) :
    iteratedDeriv k (fun s => ∑' i, f i s) r = ∑' i, iteratedDeriv k (f i) r := by
  have hfv' : ∀ j i s, ‖iteratedFDeriv ℝ j (f i) s‖ ≤ v j i := fun j i s => by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]; exact hfv j i s
  have hsum : Summable fun i => iteratedFDeriv ℝ k (f i) r :=
    .of_norm_bounded (hv k) fun i => hfv' k i r
  have hk : (k : ℕ∞) ≤ ⊤ := le_top
  rw [iteratedDeriv_eq_iteratedFDeriv,
    iteratedFDeriv_tsum_apply hf (fun j _ => hv j) (fun j i s _ => hfv' j i s) hk r,
    ContinuousMultilinearMap.tsum_eval hsum]
  rfl

/-- Borel's lemma for compactly supported coefficients, smooth in `(x, r)` on all of `F × ℝ`. -/
theorem exists_of_hasCompactSupport (c : ℕ → F → ℝ) (hc : ∀ k, ContDiff ℝ ∞ (c k))
    (hcs : ∀ k, HasCompactSupport (c k)) :
    ∃ B : F × ℝ → ℝ, ContDiff ℝ ∞ B ∧ (∀ k x, iteratedDeriv k (fun r => B (x, r)) 0 = c k x) ∧
      ∀ x, (∀ k, c k x = 0) → ∀ r, B (x, r) = 0 := by
  obtain ⟨χ, hχ, -, hχc, -, hχ1⟩ :=
    exists_cutoff (V := ℝ) isCompact_singleton isOpen_univ (subset_univ {0})
  have hχ0 : χ =ᶠ[𝓝 0] 1 := hχ1 0 rfl
  set g : ℕ → ℝ → ℝ := fun k s => s ^ k / k.factorial * χ s with hg_def
  have hg : ∀ k, ContDiff ℝ ∞ (g k) := fun k => ((contDiff_id.pow k).div_const _).mul hχ
  have hgc : ∀ k, HasCompactSupport (g k) := fun k => hχc.mul_left
  choose M hM using fun k j => exists_bound_iteratedFDeriv (hg k) (hgc k) j
  choose A hA using fun k l => exists_bound_iteratedFDeriv (hc k) (hcs k) l
  have hA0 : ∀ k l, 0 ≤ A k l := fun k l => (norm_nonneg _).trans (hA k l 0)
  have hM0 : ∀ k j, 0 ≤ M k j := fun k j => (norm_nonneg _).trans (hM k j 0)
  set P : ℕ → ℕ → ℝ := fun k j => ∑ l ∈ Finset.range (j + 1),
    (j.choose l : ℝ) * A k l * M k (j - l) with hP_def
  have hP0 : ∀ k j, 0 ≤ P k j := fun k j =>
    Finset.sum_nonneg fun l _ => mul_nonneg (mul_nonneg (by positivity) (hA0 k l)) (hM0 k _)
  set S : ℕ → ℝ := fun k => ∑ j ∈ Finset.range k, P k j with hS_def
  have hS0 : ∀ k, 0 ≤ S k := fun k => Finset.sum_nonneg fun j _ => hP0 k j
  set ε : ℕ → ℝ := fun k => (2 ^ k * (S k + 1))⁻¹ with hε_def
  have hε0 : ∀ k, 0 < ε k := fun k => by have := hS0 k; positivity
  have hε1 : ∀ k, ε k ≤ 1 := fun k => inv_le_one_of_one_le₀ (one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ one_le_two) (by linarith [hS0 k]))
  have hεP : ∀ k j, j < k → ε k * P k j ≤ (1 / 2) ^ k := fun k j hjk => by
    have hPS : P k j ≤ S k := Finset.single_le_sum (fun j _ => hP0 k j) (Finset.mem_range.2 hjk)
    calc ε k * P k j ≤ ε k * (S k + 1) := by
          gcongr
          · exact (hε0 k).le
          · linarith
      _ = (1 / 2) ^ k := by
        simp only [hε_def]; have := hS0 k; field_simp
        rw [← mul_pow]; norm_num
  set h : ℕ → ℝ → ℝ := fun k r => ε k ^ k * g k ((ε k)⁻¹ * r) with hh_def
  have hh : ∀ k, ContDiff ℝ ∞ (h k) := fun k =>
    contDiff_const.mul ((hg k).comp (contDiff_const.mul contDiff_id))
  have hhb : ∀ k j, j < k → ∀ r, ‖iteratedFDeriv ℝ j (h k) r‖ ≤ ε k * M k j := fun k j hjk r => by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact norm_iteratedDeriv_rescale_le (hg k) hjk (hM k j) (hε0 k) (hε1 k) r
  set T : ℕ → F × ℝ → ℝ := fun k p => c k p.1 * h k p.2 with hT_def
  have hT : ∀ k, ContDiff ℝ ∞ (T k) := fun k =>
    ((hc k).comp contDiff_fst).mul ((hh k).comp contDiff_snd)
  have hTb : ∀ k j, j < k → ∀ p, ‖iteratedFDeriv ℝ j (T k) p‖ ≤ (1 / 2) ^ k := fun k j hjk p => by
    refine (norm_iteratedFDeriv_mul_prod_le (hc k) (hh k) j p).trans (le_trans ?_ (hεP k j hjk))
    calc _ ≤ ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * A k l * (ε k * M k (j - l)) :=
          Finset.sum_le_sum fun l _ => by
            exact mul_le_mul (mul_le_mul_of_nonneg_left (hA k l p.1) (by positivity))
              (hhb k (j - l) (by omega) p.2) (norm_nonneg _)
              (mul_nonneg (by positivity) (hA0 k l))
      _ = ε k * P k j := by
        rw [hP_def, Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
  refine ⟨fun p => ∑' k, T k p, ?_, fun k x => ?_, fun x hx r => ?_⟩
  · refine contDiff_tsum_of_eventually hT (v := fun _ k => (1 / 2) ^ k)
      (fun _ _ => summable_geometric_two) fun j _ => ?_
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_gt_atTop j] with k hk p using hTb k j hk p
  · have hjet : ∀ i j, iteratedDeriv j (h i) 0 = if j = i then 1 else 0 := fun i j => by
      have hev : h i =ᶠ[𝓝 0] fun r => ((i.factorial : ℝ))⁻¹ * r ^ i := by
        have ht : Tendsto (fun r : ℝ => (ε i)⁻¹ * r) (𝓝 0) (𝓝 0) :=
          (continuous_const_mul (ε i)⁻¹).tendsto' 0 0 (mul_zero _)
        filter_upwards [ht.eventually hχ0] with r hr
        simp only [Pi.one_apply] at hr
        simp only [hh_def, hg_def, hr, mul_one, mul_pow, inv_pow]
        field_simp [(hε0 i).ne']
      rw [hev.iteratedDeriv_eq, iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
      split_ifs <;> simp [Nat.factorial_ne_zero]
    set v : ℕ → ℕ → ℝ := fun j i =>
      if j < i then (1 / 2) ^ i else A i 0 * (ε i ^ i * (ε i)⁻¹ ^ j * M i j) with hv_def
    have hv : ∀ j, Summable (v j) := fun j => by
      refine summable_geometric_two.of_norm_bounded_eventually ?_
      rw [Nat.cofinite_eq_atTop]
      filter_upwards [eventually_gt_atTop j] with i hi
      have : (0 : ℝ) ≤ (1 / 2) ^ i := by positivity
      simp only [hv_def, hi, ↓reduceIte, Real.norm_of_nonneg this, le_refl]
    have hfv : ∀ j i r, ‖iteratedDeriv j (fun r => c i x * h i r) r‖ ≤ v j i := fun j i r => by
      have hcx : ‖c i x‖ ≤ A i 0 := by simpa using hA i 0 x
      rw [iteratedDeriv_const_mul_field, norm_mul]
      simp only [hv_def]
      split_ifs with hji
      · have hP' : A i 0 * M i j ≤ P i j := by
          have := Finset.single_le_sum (f := fun l => (j.choose l : ℝ) * A i l * M i (j - l))
            (fun l _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA0 i l)) (hM0 i (j - l)))
            (Finset.mem_range.2 (Nat.succ_pos j))
          simpa using this
        calc _ ≤ A i 0 * (ε i * M i j) := by
              refine mul_le_mul hcx ?_ (norm_nonneg _) (hA0 i 0)
              rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
              exact hhb i j hji r
          _ = ε i * (A i 0 * M i j) := by ring
          _ ≤ ε i * P i j := mul_le_mul_of_nonneg_left hP' (hε0 i).le
          _ ≤ _ := hεP i j hji
      · refine mul_le_mul hcx ?_ (norm_nonneg _) (hA0 i 0)
        rw [hh_def, norm_iteratedDeriv_rescale (hg i) j i (hε0 i)]
        refine mul_le_mul_of_nonneg_left ?_ (by have := hε0 i; positivity)
        rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
        exact hM i j _
    show iteratedDeriv k (fun r => ∑' i, c i x * h i r) 0 = c k x
    rw [iteratedDeriv_tsum_apply (fun i => contDiff_const.mul (hh i)) hv hfv k 0,
      tsum_eq_single k fun i hi => by simp [hjet, Ne.symm hi]]
    simp [hjet]
  · simp [hT_def, hx]

end Borel

variable {n : ℕ}

/-- Borel's lemma with parameters: smooth functions `b k` on an open set are the derivatives
`∂ᵣᵏ B(x, 0)` of a smooth function `B(x, r)`, which vanishes where all `b k` vanish.
Rauch, Hyperbolic partial differential equations and geometric optics, Borel's Theorem 4.3.1,
p. 128, applied to `b k / k!` (there the `b k` are Taylor coefficients). Its proof is left as
Exercise 4.3.1. Following the proof of Theorem 4.3.2, p. 129, compactly supported coefficients
`c k` give `∑ c k x rᵏ/k! χ(r/εₖ)` (`Borel.exists_of_hasCompactSupport`); here the coefficients
`ψₘ₊₁ b k`, with cut-offs `ψₘ` along a compact exhaustion of `V`, give `Bₘ`, and
`B = ∑ (ψₘ - ψₘ₋₁) Bₘ`. -/
theorem borel {V : Set (E n)} (hV : IsOpen V) {b : ℕ → E n → ℝ}
    (hb : ∀ k, ContDiffOn ℝ ∞ (b k) V) :
    ∃ B : E n → ℝ → ℝ, ContDiffOn ℝ ∞ (fun p : E n × ℝ => B p.1 p.2) (V ×ˢ Set.univ) ∧
      (∀ k, ∀ x ∈ V, iteratedDeriv k (B x) 0 = b k x) ∧
      ∀ x ∈ V, (∀ k, b k x = 0) → ∀ r, B x r = 0 := by
  have : LocallyCompactSpace V := hV.locallyCompactSpace
  let K : CompactExhaustion V := default
  set L : ℕ → Set (E n) := fun m => Subtype.val '' K m with hL_def
  set W : ℕ → Set (E n) := fun m => Subtype.val '' interior (K m) with hW_def
  have hLc : ∀ m, IsCompact (L m) := fun m => (K.isCompact m).image continuous_subtype_val
  have hWo : ∀ m, IsOpen (W m) := fun m => hV.isOpenMap_subtype_val _ isOpen_interior
  have hLW : ∀ m, L m ⊆ W (m + 1) := fun m => image_mono (K.subset_interior_succ m)
  have hWL : ∀ m, W m ⊆ L m := fun m => image_mono interior_subset
  have hLV : ∀ m, L m ⊆ V := fun m => by rintro _ ⟨y, -, rfl⟩; exact y.2
  have hLmono : Monotone L := fun m m' h => image_mono (K.subset h)
  have hmemW : ∀ x ∈ V, ∃ m, x ∈ W m := fun x hx => by
    obtain ⟨m, hm⟩ := K.exists_mem ⟨x, hx⟩
    exact ⟨m + 1, ⟨x, hx⟩, K.subset_interior_succ m hm, rfl⟩
  choose ψ hψ _ hψc hψs hψ1 using fun m => exists_cutoff (hLc m) (hWo (m + 1)) (hLW m)
  have hψ1' : ∀ m, ∀ x ∈ L m, ψ m x = 1 := fun m x hx => (hψ1 m x hx).eq_of_nhds
  have hψL : ∀ m, tsupport (ψ m) ⊆ L (m + 1) := fun m => (hψs m).trans (hWL _)
  set c : ℕ → ℕ → E n → ℝ := fun m k x => ψ (m + 1) x * b k x with hc_def
  have hc : ∀ m k, ContDiff ℝ ∞ (c m k) := fun m k => contDiff_iff_contDiffAt.2 fun x => by
    by_cases hx : x ∈ V
    · exact (hψ (m + 1)).contDiffAt.mul ((hb k).contDiffAt (hV.mem_nhds hx))
    · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 fun h => hx (hLV (m + 2) (hψL (m + 1) h))]
        with y hy
      simp [hc_def, hy]
  choose B' hB' hB'b hB'0 using fun m =>
    Borel.exists_of_hasCompactSupport (c m) (hc m) fun k => (hψc (m + 1)).mul_right
  set θ : ℕ → E n → ℝ := fun m x => if m = 0 then 0 else ψ (m - 1) x with hθ_def
  have hθ : ∀ m, ContDiff ℝ ∞ (θ m) := by
    rintro (_ | m)
    · simpa [hθ_def] using (contDiff_const : ContDiff ℝ ∞ fun _ : E n => (0 : ℝ))
    · simpa [hθ_def] using hψ m
  set φ : ℕ → E n → ℝ := fun m x => θ (m + 1) x - θ m x with hφ_def
  have hφ1 : ∀ m x, φ m x ≠ 0 → ψ (m + 1) x = 1 := fun m x hx => by
    refine hψ1' (m + 1) x (by_contra fun hL => hx ?_)
    have h1 : ψ m x = 0 := image_eq_zero_of_notMem_tsupport fun h => hL (hψL m h)
    rcases m with _ | m
    · simp [hφ_def, hθ_def, h1]
    · have h2 : ψ m x = 0 := image_eq_zero_of_notMem_tsupport fun h =>
        hL (hLmono (Nat.le_succ _) (hψL m h))
      simp [hφ_def, hθ_def, h1, h2]
  have hφ0 : ∀ M, ∀ x ∈ L M, ∀ m, M < m → φ m x = 0 := fun M x hx m hm => by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hm
    have h1 := hψ1' (M + m + 1) x (hLmono (by omega) hx)
    have h2 := hψ1' (M + m) x (hLmono (by omega) hx)
    simp [hφ_def, hθ_def, h1, h2]
  have hsum : ∀ M x, ∑ m ∈ Finset.range (M + 1), φ m x = ψ M x := fun M x => by
    simp only [hφ_def, Finset.sum_range_sub (fun m => θ m x)]
    simp [hθ_def]
  set B : E n → ℝ → ℝ := fun x r => ∑' m, φ m x * B' m (x, r) with hB_def
  have hloc : ∀ M, ∀ x ∈ L M, ∀ r,
      B x r = ∑ m ∈ Finset.range (M + 1), φ m x * B' m (x, r) := fun M x hx r =>
    tsum_eq_sum fun m hm => by
      rw [hφ0 M x hx m (by simpa using hm), zero_mul]
  refine ⟨B, ?_, fun k x hx => ?_, fun x hx hbx r => ?_⟩
  · refine contDiffOn_of_locally_contDiffOn fun p hp => ?_
    obtain ⟨M, hM⟩ := hmemW p.1 hp.1
    refine ⟨W M ×ˢ univ, (hWo M).prod isOpen_univ, ⟨hM, trivial⟩, ?_⟩
    have : ContDiff ℝ ∞ fun q : E n × ℝ => ∑ m ∈ Finset.range (M + 1), φ m q.1 * B' m q :=
      ContDiff.sum fun m _ => (((hθ (m + 1)).sub (hθ m)).comp contDiff_fst).mul (hB' m)
    exact this.contDiffOn.congr fun q hq => hloc M q.1 (hWL M hq.2.1) q.2
  · obtain ⟨M, hM⟩ := hmemW x hx
    have hxL := hWL M hM
    rw [show B x = fun r => ∑ m ∈ Finset.range (M + 1), φ m x * B' m (x, r) from
      funext (hloc M x hxL), iteratedDeriv_fun_sum (f := fun m r => φ m x * B' m (x, r))
        fun m _ => (contDiff_const.mul ((hB' m).comp
          (contDiff_const.prodMk contDiff_id))).contDiffAt.of_le (by simp)]
    simp_rw [iteratedDeriv_const_mul_field]
    calc ∑ m ∈ Finset.range (M + 1), φ m x * iteratedDeriv k (fun r => B' m (x, r)) 0
        = ∑ m ∈ Finset.range (M + 1), φ m x * b k x := Finset.sum_congr rfl fun m _ => by
          rw [hB'b]
          by_cases h : φ m x = 0
          · simp [h]
          · simp [hc_def, hφ1 m x h]
      _ = b k x := by rw [← Finset.sum_mul, hsum, hψ1' M x hxL, one_mul]
  · refine (tsum_congr fun m => ?_).trans tsum_zero
    rw [hB'0 m x (fun k => by simp [hc_def, hbx k]) r, mul_zero]

end

end LorentzianCalderon.Facts
