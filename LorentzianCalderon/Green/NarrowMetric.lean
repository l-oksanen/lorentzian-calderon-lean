module

public import LorentzianCalderon.Causal.Imprisonment
public import LorentzianCalderon.Causal.StandardTime
public import LorentzianCalderon.Causal.Steep
public import LorentzianCalderon.Local.Energy.Coform
public import LorentzianCalderon.Setting.BoxGreen
public import LorentzianCalderon.Setting.Escape

public section

/-!
# Narrowed metrics

For a temporal function `ψ` of `g`, the narrowed metric `g_ε = g + ε dψ ⊗ dψ` (`narrow`). With
`s = g(dψ, dψ) < 0` and `1 + ε s > 0` it is Lorentzian (by the matrix determinant lemma,
`det g_ε = det g · (1 + ε s)`), `N = -grad_g ψ` is a time orientation for it, `ψ` is temporal for
`(g_ε, N)` with `g_ε(dψ, dψ) = s / (1 + ε s)`, and for `ε > 0` its future causal vectors are
future timelike for `g` (`IsFutureCausal.of_narrow`).

For a standard time `ψ` (`IsStandardTime`), `-g(dψ, dψ)` is bounded, so a uniform `ε₀` works
(`IsStandardTime.exists_narrow_le`), and `ψ` is steep: `κ ‖v‖ ≤ dψ(v)` for future causal `v`
(`IsStandardTime.exists_steep`).
-/

namespace LorentzianCalderon

noncomputable section
open Set Matrix WithLp Filter
open scoped ContDiff Topology

variable {n : ℕ}

/-- The narrowed metric `g_ε = g + ε dψ ⊗ dψ`. -/
def narrow (g : MatrixField n) (ψ : E n → ℝ) (ε : ℝ) : MatrixField n :=
  fun x => g x + ε • vecMulVec (d ψ x) (d ψ x)

theorem narrow_def (g : MatrixField n) (ψ : E n → ℝ) (ε : ℝ) :
    narrow g ψ ε =
      fun x => g x + ε • vecMulVec (d ψ x) (d ψ x) := by rfl

section Algebra

variable {G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {ξ : Fin (n + 1) → ℝ} {ε : ℝ}

/-- `(G + ε ξ ξᵀ) w = G w + ε (ξ · w) ξ`. -/
theorem add_smul_vecMulVec_mulVec (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (ξ w : Fin (n + 1) → ℝ) (ε : ℝ) :
    (G + ε • vecMulVec ξ ξ) *ᵥ w = G *ᵥ w + (ε * (ξ ⬝ᵥ w)) • ξ := by
  ext i
  simp only [add_mulVec, smul_mulVec, vecMulVec_mulVec, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, op_smul_eq_smul]
  ring

/-- `(G + ε ξ ξᵀ)(v, w) = G(v, w) + ε (v · ξ)(ξ · w)`. -/
theorem bil_add_smul_vecMulVec (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (ξ v w : Fin (n + 1) → ℝ) (ε : ℝ) :
    bil (G + ε • vecMulVec ξ ξ) v w = bil G v w + ε * ((v ⬝ᵥ ξ) * (ξ ⬝ᵥ w)) := by
  rw [bil_apply, bil_apply, add_smul_vecMulVec_mulVec, dotProduct_add, dotProduct_smul,
    smul_eq_mul]
  ring

/-- The matrix determinant lemma for `G + ε ξ ξᵀ`. -/
theorem det_add_smul_vecMulVec (hG : IsUnit G.det) (ξ : Fin (n + 1) → ℝ) (ε : ℝ) :
    (G + ε • vecMulVec ξ ξ).det = G.det * (1 + ε * bil G⁻¹ ξ ξ) := by
  have h := det_add_replicateCol_mul_replicateRow (ι := Unit) hG (ε • ξ) ξ
  rw [← vecMulVec_eq, smul_vecMulVec] at h
  rw [h]
  congr 1
  rw [det_unique]
  simp [Matrix.mul_apply, replicateRow, replicateCol, bil_apply, dotProduct, mulVec,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- Sherman–Morrison on `ξ`: `(G + ε ξ ξᵀ)⁻¹(ξ, ξ) = s / (1 + ε s)` with `s = G⁻¹(ξ, ξ)`. -/
theorem bil_inv_add_smul_vecMulVec (hG : IsUnit G.det) (h1 : 1 + ε * bil G⁻¹ ξ ξ ≠ 0) :
    bil (G + ε • vecMulVec ξ ξ)⁻¹ ξ ξ = bil G⁻¹ ξ ξ / (1 + ε * bil G⁻¹ ξ ξ) := by
  set s := bil G⁻¹ ξ ξ
  set H := G + ε • vecMulVec ξ ξ
  have hH : IsUnit H.det := by
    rw [det_add_smul_vecMulVec hG]
    exact hG.mul (isUnit_iff_ne_zero.2 h1)
  have hξs : ξ ⬝ᵥ (G⁻¹ *ᵥ ξ) = s := (bil_apply _ _ _).symm
  have hHz : H *ᵥ (G⁻¹ *ᵥ ξ) = (1 + ε * s) • ξ := by
    rw [add_smul_vecMulVec_mulVec, mulVec_mulVec, mul_nonsing_inv _ hG, one_mulVec, hξs,
      add_smul, one_smul]
  have hinv : H⁻¹ *ᵥ ξ = (1 + ε * s)⁻¹ • (G⁻¹ *ᵥ ξ) := by
    have := congrArg (fun w => (1 + ε * s)⁻¹ • H⁻¹ *ᵥ w) hHz
    simp only [mulVec_mulVec, mulVec_smul, smul_smul, inv_mul_cancel₀ h1, one_smul,
      ← Matrix.mul_assoc, nonsing_inv_mul _ hH, Matrix.one_mul] at this
    exact this.symm
  rw [bil_apply, hinv, dotProduct_smul, hξs, smul_eq_mul, div_eq_inv_mul]

/-- `G + ε ξ ξᵀ` is Lorentzian if `G` is, `ξ` is timelike for `G` and `1 + ε G(ξ, ξ) > 0`. -/
theorem IsLorentzian.add_smul_vecMulVec (hG : IsLorentzian G) (hs : bil G⁻¹ ξ ξ < 0)
    (h1 : 0 < 1 + ε * bil G⁻¹ ξ ξ) : IsLorentzian (G + ε • vecMulVec ξ ξ) where
  symm := by rw [transpose_add, transpose_smul, transpose_vecMulVec, hG.symm]
  det_neg := by
    rw [det_add_smul_vecMulVec hG.isUnit_det]
    exact mul_neg_of_neg_of_pos hG.det_neg h1
  spacelike := by
    let ℓ : E n →ₗ[ℝ] ℝ :=
      { toFun := fun v => ofLp v ⬝ᵥ ξ
        map_add' := fun v w => by simp [add_dotProduct]
        map_smul' := fun c v => by simp [smul_dotProduct] }
    set N : E n := toLp 2 (G⁻¹ *ᵥ ξ)
    have hNN : form G N N < 0 := by
      rw [form_eq_bil, ofLp_toLp, hG.bil_inv_eq]
      exact hs
    have hℓN : ℓ N = bil G⁻¹ ξ ξ := by
      change (G⁻¹ *ᵥ ξ) ⬝ᵥ ξ = _
      rw [dotProduct_comm, bil_apply]
    have hsurj : Function.Surjective ℓ := fun t =>
      ⟨(t / bil G⁻¹ ξ ξ) • N, by rw [map_smul, hℓN, smul_eq_mul, div_mul_cancel₀ _ hs.ne]⟩
    refine ⟨LinearMap.ker ℓ, ⟨?_, fun v hv hv0 => ?_⟩⟩
    · have h := LinearMap.finrank_range_add_finrank_ker ℓ
      rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_self,
        finrank_euclideanSpace_fin] at h
      omega
    · have hv' : ofLp v ⬝ᵥ ξ = 0 := hv
      rw [form_eq_bil, bil_add_smul_vecMulVec, hv', zero_mul, mul_zero, add_zero,
        ← form_eq_bil]
      by_contra hle
      refine hG.form_ne_zero (not_lt.1 hle) hv0 hNN ?_
      rw [form_eq_bil, ofLp_toLp, bil_apply, mulVec_mulVec, mul_nonsing_inv _ hG.isUnit_det,
        one_mulVec, hv']

end Algebra

section Point

variable {g : MatrixField n} {Y : E n → E n} {ψ : E n → ℝ} {ε : ℝ} {x : E n}

/-- `v · du(x) = du(x) v`. -/
theorem ofLp_dotProduct_d (u : E n → ℝ) (x v : E n) : ofLp v ⬝ᵥ d u x = fderiv ℝ u x v := by
  rw [fderiv_apply_eq_sum_d]
  rfl

/-- `g_ε(v, w) = g(v, w) + ε dψ(v) dψ(w)`. -/
theorem form_narrow (g : MatrixField n) (ψ : E n → ℝ) (ε : ℝ) (x v w : E n) :
    form (narrow g ψ ε x) v w = form (g x) v w + ε * (fderiv ℝ ψ x v * fderiv ℝ ψ x w) := by
  rw [form_eq_bil, narrow, bil_add_smul_vecMulVec, ← form_eq_bil, ofLp_dotProduct_d,
    dotProduct_comm, ofLp_dotProduct_d]

/-- `g(-grad ψ, v) = -dψ(v)`. -/
theorem form_neg_grad_left (hL : IsLorentzian (g x)) (v : E n) :
    form (g x) (-grad g ψ x) v = -fderiv ℝ ψ x v := by
  rw [form_neg_left, fderiv_eq_form_grad hL]

/-- `dψ(-grad ψ) = -g(dψ, dψ)`. -/
theorem fderiv_neg_grad_self (hL : IsLorentzian (g x)) :
    fderiv ℝ ψ x (-grad g ψ x) = -coform g x (d ψ x) (d ψ x) := by
  have h := form_neg_grad_left (ψ := ψ) hL (-grad g ψ x)
  rw [form_neg_grad hL] at h
  linarith

/-- `g_ε(dψ, dψ) = s / (1 + ε s)` for `s = g(dψ, dψ)`. -/
theorem coform_narrow (hL : IsLorentzian (g x))
    (h1 : 1 + ε * coform g x (d ψ x) (d ψ x) ≠ 0) :
    coform (narrow g ψ ε) x (d ψ x) (d ψ x) =
      coform g x (d ψ x) (d ψ x) / (1 + ε * coform g x (d ψ x) (d ψ x)) := by
  simp only [coform_eq_bil] at h1 ⊢
  exact bil_inv_add_smul_vecMulVec hL.isUnit_det h1

/-- `g_ε` is Lorentzian where `dψ` is timelike and `1 + ε g(dψ, dψ) > 0`. -/
theorem isLorentzian_narrow (hL : IsLorentzian (g x)) (hs : coform g x (d ψ x) (d ψ x) < 0)
    (h1 : 0 < 1 + ε * coform g x (d ψ x) (d ψ x)) : IsLorentzian (narrow g ψ ε x) := by
  rw [coform_eq_bil] at hs h1
  exact hL.add_smul_vecMulVec hs h1

/-- `g_ε(N, N) = s (1 + ε s)` for `N = -grad_g ψ` and `s = g(dψ, dψ)`. -/
theorem form_narrow_neg_grad (hL : IsLorentzian (g x)) :
    form (narrow g ψ ε x) (-grad g ψ x) (-grad g ψ x) =
      coform g x (d ψ x) (d ψ x) * (1 + ε * coform g x (d ψ x) (d ψ x)) := by
  rw [form_narrow, form_neg_grad hL, fderiv_neg_grad_self hL]
  ring

/-- `ψ` is temporal for `g_ε` with the time orientation `N = -grad_g ψ`. -/
theorem isFutureTimelike_narrow (hL : IsLorentzian (g x)) (hs : coform g x (d ψ x) (d ψ x) < 0)
    (h1 : 0 < 1 + ε * coform g x (d ψ x) (d ψ x)) :
    IsFutureTimelike (narrow g ψ ε) (fun y => -grad g ψ y) x (-grad (narrow g ψ ε) ψ x) where
  timelike := by
    rw [form_neg_grad (isLorentzian_narrow hL hs h1), coform_narrow hL h1.ne']
    exact div_neg_of_neg_of_pos hs h1
  future := by
    rw [form_neg_grad_left (isLorentzian_narrow hL hs h1), fderiv_neg_grad_self hL, neg_neg]
    exact hs

/-- A timelike vector `v` with `g(N, v) < 0` for a future timelike `N` is future-directed. -/
theorem IsFutureTimelike.of_form_neg_left {N v : E n} (hL : IsLorentzian (g x))
    (hY : form (g x) (Y x) (Y x) < 0) (hN : IsFutureTimelike g Y x N)
    (hv : form (g x) v v < 0) (hNv : form (g x) N v < 0) : IsFutureTimelike g Y x v := by
  refine ⟨hv, lt_of_not_ge fun hge => ?_⟩
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp [form_def] at hv
  have hne : form (g x) v (Y x) ≠ 0 := hL.form_ne_zero hv.le hv0 hY
  have hpast : IsFutureCausal g Y x (-v) :=
    ⟨neg_ne_zero.2 hv0, by simpa using hv.le, by
      rw [form_neg_left]
      exact neg_neg_of_pos (lt_of_le_of_ne hge hne.symm)⟩
  have := hN.form_neg hL hY hpast
  rw [form_neg_right] at this
  linarith

/-- For `ε > 0`, a future causal vector of `(g_ε, N)` is future timelike for `(g, Y)`. -/
theorem IsFutureCausal.of_narrow (hL : IsLorentzian (g x)) (hY : form (g x) (Y x) (Y x) < 0)
    (hψ : IsFutureTimelike g Y x (-grad g ψ x)) (hε : 0 < ε)
    (h1 : 0 < 1 + ε * coform g x (d ψ x) (d ψ x)) {v : E n}
    (hv : IsFutureCausal (narrow g ψ ε) (fun y => -grad g ψ y) x v) :
    IsFutureTimelike g Y x v := by
  have hf := hv.future
  rw [form_narrow, form_comm hL.symm, form_neg_grad_left hL, fderiv_neg_grad_self hL] at hf
  have ha : 0 < fderiv ℝ ψ x v := by nlinarith
  have hc := hv.causal
  rw [form_narrow] at hc
  refine hψ.of_form_neg_left hL hY (by nlinarith [mul_pos hε (mul_pos ha ha)]) ?_
  rw [form_neg_grad_left hL]
  linarith

end Point

section Global

variable {g : MatrixField n} {Y : E n → E n} {ψ : E n → ℝ} {ε : ℝ}

/-- The entries of `g_ε` are smooth. -/
theorem contDiff_narrow (hgs : ∀ i j, ContDiff ℝ ∞ fun x => g x i j) (hψs : ContDiff ℝ ∞ ψ)
    (ε : ℝ) (i j : Fin (n + 1)) : ContDiff ℝ ∞ fun x => narrow g ψ ε x i j := by
  simp only [narrow, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  exact (hgs i j).add (contDiff_const.mul ((contDiff_d hψs i).mul (contDiff_d hψs j)))

/-- The partial derivatives of a `C¹` function are continuous. -/
theorem continuous_d_of_contDiff {u : E n → ℝ} (hu : ContDiff ℝ 1 u) (i : Fin (n + 1)) :
    Continuous fun x => d u x i := by
  simp only [d_def]
  exact (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- The entries of `g⁻¹` are continuous. -/
theorem IsSpacetime.continuous_inv_apply (hg : IsSpacetime g Y) (i j : Fin (n + 1)) :
    Continuous fun x => (g x)⁻¹ i j :=
  (contDiff_inv_apply hg.smooth (fun x => (hg.lorentzian x).det_neg.ne) i j).continuous

/-- The gradient of a `C¹` function is continuous. -/
theorem IsSpacetime.continuous_grad (hg : IsSpacetime g Y) {u : E n → ℝ} (hu : ContDiff ℝ 1 u) :
    Continuous (grad g u) := by
  rw [show grad g u = _ from funext (grad_def g u)]
  exact (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm.continuous.comp (continuous_pi fun j =>
    continuous_finsetSum _ fun k _ => (hg.continuous_inv_apply j k).mul
      (continuous_d_of_contDiff hu k))

/-- `x ↦ g(du, du)` is continuous for a `C¹` function `u`. -/
theorem IsSpacetime.continuous_coform (hg : IsSpacetime g Y) {u : E n → ℝ}
    (hu : ContDiff ℝ 1 u) : Continuous fun x => coform g x (d u x) (d u x) := by
  simp only [coform_def]
  exact continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ =>
    ((hg.continuous_inv_apply j k).mul (continuous_d_of_contDiff hu j)).mul
      (continuous_d_of_contDiff hu k)

/-- The Minkowski metric is its own inverse. -/
theorem inv_minkowski : (minkowski n)⁻¹ = minkowski n := by
  refine inv_eq_left_inv ?_
  rw [minkowski_def, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  ext i
  split_ifs <;> norm_num

namespace IsStandardTime

variable (hg : IsSpacetime g Y) (hψ : IsStandardTime g Y ψ)
include hg hψ

/-- Outside a compact set, `g` is the Minkowski metric and `dψ = σ dx⁰`. -/
theorem exists_exterior : ∃ (K : Set (E n)) (σ : ℝ), IsCompact K ∧ (σ = 1 ∨ σ = -1) ∧
    ∀ x ∉ K, g x = minkowski n ∧ ∀ k, d ψ x k = if k = 0 then σ else 0 := by
  obtain ⟨T, σ', hσ', hT⟩ := hg.exterior
  obtain ⟨C, σ, A, hC, hσ, hψC⟩ := hψ.exterior
  refine ⟨C ∪ M0 n T, σ, hC.union (isCompact_M0 T), hσ, fun x hx => ⟨(hT x fun h =>
    hx (Or.inr h)).1, fun k => ?_⟩⟩
  have hev : ψ =ᶠ[𝓝 x] fun y => σ * y 0 + A :=
    eventually_of_mem (hC.isClosed.isOpen_compl.mem_nhds fun h => hx (Or.inl h)) hψC
  rw [d_congr hev]
  have hd : DifferentiableAt ℝ (fun y : E n => y 0) x :=
    (EuclideanSpace.proj (0 : Fin (n + 1)) : E n →L[ℝ] ℝ).differentiableAt
  have := d_add (u := fun y : E n => σ * y 0) (v := fun _ => A) (x := x)
    (hd.const_mul σ) (differentiableAt_const A) k
  simp only at this
  rw [this, d_const_mul hd, d_coord, d_const]
  split_ifs <;> simp

/-- `-g(dψ, dψ)` is bounded above. -/
theorem exists_neg_coform_le : ∃ M, 0 < M ∧ ∀ x, -coform g x (d ψ x) (d ψ x) ≤ M := by
  obtain ⟨K, σ, hK, hσ, hext⟩ := exists_exterior hg hψ
  have hc := hg.continuous_coform (hψ.smooth.of_le (by simp))
  obtain ⟨M, hM⟩ := (hK.image hc.neg).bddAbove
  refine ⟨max M 1, by positivity, fun x => ?_⟩
  by_cases hx : x ∈ K
  · exact (hM ⟨x, hx, rfl⟩).trans (le_max_left _ _)
  · obtain ⟨hgx, hdx⟩ := hext x hx
    have : coform g x (d ψ x) (d ψ x) = -1 := by
      simp only [coform_def, hgx, inv_minkowski, hdx]
      simp only [minkowski_def, diagonal_apply, mul_ite, ite_mul, mul_zero, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rcases hσ with rfl | rfl <;> norm_num
    rw [this, neg_neg]
    exact le_max_right _ _

/-- A uniform `ε₀` for which every `g_ε`, `0 ≤ ε ≤ ε₀`, has `1 + ε g(dψ, dψ) ≥ 1/2`. -/
theorem exists_narrow_le : ∃ ε₀ > 0, ∀ ε ∈ Icc 0 ε₀, ∀ x,
    1 / 2 ≤ 1 + ε * coform g x (d ψ x) (d ψ x) := by
  obtain ⟨M, hM, hle⟩ := exists_neg_coform_le hg hψ
  refine ⟨1 / (2 * M), by positivity, fun ε hε x => ?_⟩
  have h1 : ε * -coform g x (d ψ x) (d ψ x) ≤ ε * M := mul_le_mul_of_nonneg_left (hle x) hε.1
  have h2 : ε * M ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_right hε.2 hM.le
    rwa [one_div, mul_inv, mul_assoc, inv_mul_cancel₀ hM.ne', mul_one, ← one_div] at this
  linarith

/-- `N = -grad_g ψ` is a time orientation for `g_ε`. -/
theorem isTimeOrientation_narrow (hε : ∀ x, 0 < 1 + ε * coform g x (d ψ x) (d ψ x)) :
    IsTimeOrientation (narrow g ψ ε) (fun x => -grad g ψ x) where
  continuous := (hg.continuous_grad (hψ.smooth.of_le (by simp))).neg
  timelike x := by
    rw [form_narrow_neg_grad (hg.lorentzian x)]
    exact mul_neg_of_neg_of_pos
      (coform_self_neg_of_future (hg.lorentzian x) (hψ.past_gradient x)) (hε x)

end IsStandardTime

end Global

end

end LorentzianCalderon
