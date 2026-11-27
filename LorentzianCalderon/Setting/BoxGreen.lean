module

public import LorentzianCalderon.Local.Differential
public import LorentzianCalderon.Local.MatrixCalculus

public section

namespace LorentzianCalderon

open MeasureTheory Set WithLp
open scoped ContDiff Matrix

variable {n : ℕ}

theorem mem_frontier_Icc_of_eq {a b x : Fin (n + 1) → ℝ} (hx : x ∈ Icc a b) {i : Fin (n + 1)}
    (hi : x i = a i ∨ x i = b i) : x ∈ frontier (Icc a b) := by
  rw [frontier, isClosed_Icc.closure_eq, ← pi_univ_Icc, interior_pi_set finite_univ]
  refine ⟨by rwa [pi_univ_Icc], fun h => ?_⟩
  have := h i (mem_univ _)
  simp only [interior_Icc] at this
  rcases hi with hi | hi <;> rw [hi] at this <;> simp at this

theorem frontier_preimage_ofLp (s : Set (Fin (n + 1) → ℝ)) :
    frontier (ofLp ⁻¹' s : Set (E n)) = ofLp ⁻¹' frontier s :=
  ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) => ℝ)).toHomeomorph.preimage_frontier
    s).symm

/-- The divergence theorem on a closed box for a `C¹` vector field vanishing on its
boundary. -/
theorem integral_divergence_box_eq_zero {a b : Fin (n + 1) → ℝ}
    (X : Fin (n + 1) → E n → ℝ) (hX : ∀ j, ContDiff ℝ 1 (X j))
    (h0 : ∀ j, ∀ x ∈ frontier (ofLp ⁻¹' Icc a b : Set (E n)), X j x = 0) :
    ∫ x in (ofLp ⁻¹' Icc a b : Set (E n)), ∑ j, d (X j) x j = 0 := by
  by_cases hab : a ≤ b
  swap
  · rw [Icc_eq_empty hab, preimage_empty, setIntegral_empty]
  have hpres := PiLp.volume_preserving_ofLp (Fin (n + 1))
  have hemb : MeasurableEmbedding (ofLp : E n → Fin (n + 1) → ℝ) :=
    (MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)).symm.measurableEmbedding
  have key := hpres.setIntegral_preimage_emb hemb
    (fun y => ∑ j, fderiv ℝ (X j) (toLp 2 y) (toLp 2 (Pi.single j 1))) (Icc a b)
  simp only [toLp_ofLp] at key
  simp only [d_def, ← PiLp.toLp_single]
  rw [key]
  have hdiff : ∀ j, Differentiable ℝ (X j) := fun j => (hX j).differentiable one_ne_zero
  have hcont : ∀ j, Continuous (fderiv ℝ (X j)) := fun j => (hX j).continuous_fderiv one_ne_zero
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) => ℝ)).symm
  refine (integral_divergence_of_hasFDerivAt_off_countable' a b hab (fun j y => X j (toLp 2 y))
    (fun j y => fderiv ℝ (X j) (toLp 2 y) ∘L (L : (Fin (n + 1) → ℝ) →L[ℝ] E n)) ∅
    countable_empty ?_ ?_ ?_).trans ?_
  · exact fun j => ((hX j).continuous.comp (PiLp.continuous_toLp 2 _)).continuousOn
  · intro x _ j
    exact (hdiff j _).hasFDerivAt.comp x L.hasFDerivAt
  · refine (Continuous.continuousOn ?_).integrableOn_compact isCompact_Icc
    refine continuous_finsetSum _ fun j _ => ?_
    exact ((hcont j).comp (PiLp.continuous_toLp 2 _)).clm_apply continuous_const
  · refine Finset.sum_eq_zero fun i _ => ?_
    rw [setIntegral_eq_zero_of_forall_eq_zero, setIntegral_eq_zero_of_forall_eq_zero, sub_zero]
    all_goals
      intro y hy
      apply h0
      rw [frontier_preimage_ofLp, mem_preimage, ofLp_toLp]
      refine mem_frontier_Icc_of_eq (i := i) ?_ (by simp)
      rw [Fin.insertNth_mem_Icc]
    · exact ⟨⟨le_rfl, hab i⟩, hy⟩
    · exact ⟨⟨hab i, le_rfl⟩, hy⟩

theorem M0_eq (T : ℝ) :
    M0 n T = ofLp ⁻¹' Icc (Fin.cons (-T) fun _ => -1) (Fin.cons T fun _ => 1) := by
  ext x
  simp only [mem_M0, mem_preimage, mem_Icc, Pi.le_def,
    Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, abs_le]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, fun i => (h3 i).1⟩, ⟨h2, fun i => (h3 i).2⟩⟩
  · rintro ⟨⟨h1, h1'⟩, ⟨h2, h2'⟩⟩
    exact ⟨⟨h1, h2⟩, fun i => ⟨h1' i, h2' i⟩⟩

theorem isCompact_M0 (T : ℝ) : IsCompact (M0 n T) := by
  rw [M0_eq]
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) => ℝ)).toHomeomorph
    |>.isCompact_preimage.2 isCompact_Icc

/-- The divergence theorem on `M₀` for a `C¹` vector field vanishing on `∂M₀`. -/
theorem integral_divergence_M0_eq_zero (T : ℝ) (X : Fin (n + 1) → E n → ℝ)
    (hX : ∀ j, ContDiff ℝ 1 (X j)) (h0 : ∀ j, ∀ x ∈ frontier (M0 n T), X j x = 0) :
    ∫ x in M0 n T, ∑ j, d (X j) x j = 0 := by
  rw [M0_eq] at h0 ⊢
  exact integral_divergence_box_eq_zero X hX h0

/-- The flux `|det g|^{1/2} g^{jk} ∂ₖu` whose divergence gives `□_g u`. -/
noncomputable def flux (g : MatrixField n) (u : E n → ℝ) (j : Fin (n + 1)) (y : E n) : ℝ :=
  √|(g y).det| * ∑ k, (g y)⁻¹ j k * d u y k

theorem flux_def (g : MatrixField n) (u : E n → ℝ) (j : Fin (n + 1)) (y : E n) :
    flux g u j y =
      √|(g y).det| * ∑ k, (g y)⁻¹ j k * d u y k := by rfl

theorem box_eq_flux (g : MatrixField n) (u : E n → ℝ) (x : E n) :
    box g u x = -(√|(g x).det|)⁻¹ * ∑ j, d (flux g u j) x j := by
  rw [box_def]
  rfl

theorem sqrt_abs_det_mul_box {g : MatrixField n} {x : E n} (hdet : (g x).det ≠ 0)
    (u : E n → ℝ) : √|(g x).det| * box g u x = -∑ j, d (flux g u j) x j := by
  have : √|(g x).det| ≠ 0 := (Real.sqrt_pos.2 (abs_pos.2 hdet)).ne'
  rw [box_eq_flux]
  field_simp

section Smooth

variable {g : MatrixField n} {u : E n → ℝ}

theorem contDiff_flux (hg : ∀ i j, ContDiff ℝ ∞ fun x => g x i j)
    (hdet : ∀ x, (g x).det ≠ 0) (hu : ContDiff ℝ ∞ u) (j : Fin (n + 1)) :
    ContDiff ℝ ∞ (flux g u j) :=
  (contDiff_sqrt_abs_det hg hdet).mul
    (ContDiff.sum fun k _ => (contDiff_inv_apply hg hdet j k).mul (contDiff_d hu k))

theorem continuous_box (hg : ∀ i j, ContDiff ℝ ∞ fun x => g x i j)
    (hdet : ∀ x, (g x).det ≠ 0) (hu : ContDiff ℝ ∞ u) : Continuous (box g u) := by
  simp only [funext (box_eq_flux g u)]
  have hρ := (contDiff_sqrt_abs_det hg hdet).continuous
  refine ((hρ.inv₀ fun x => (Real.sqrt_pos.2 (abs_pos.2 (hdet x))).ne').neg.mul ?_)
  exact continuous_finsetSum _ fun j _ => (contDiff_d (contDiff_flux hg hdet hu j) j).continuous

end Smooth

/-- Green's identity for `□_g` on `M₀`, for functions with vanishing Cauchy data on `∂M₀`
(only `w` needs to vanish to first order). -/
theorem integral_mul_box_comm {T : ℝ} {g : MatrixField n}
    (hg : ∀ i j, ContDiff ℝ ∞ fun x => g x i j) (hsymm : ∀ x, (g x)ᵀ = g x)
    (hdet : ∀ x, (g x).det ≠ 0) {w ϑ : E n → ℝ} (hw : ContDiff ℝ ∞ w)
    (hϑ : ContDiff ℝ ∞ ϑ) (hw0 : ∀ x ∈ frontier (M0 n T), w x = 0)
    (hdw0 : ∀ x ∈ frontier (M0 n T), fderiv ℝ w x = 0) :
    ∫ x in M0 n T, w x * box g ϑ x * √|(g x).det| =
      ∫ x in M0 n T, ϑ x * box g w x * √|(g x).det| := by
  set X : Fin (n + 1) → E n → ℝ := fun j y => w y * flux g ϑ j y - ϑ y * flux g w j y
  have hdiff : ∀ {f : E n → ℝ}, ContDiff ℝ ∞ f → ∀ x, DifferentiableAt ℝ f x :=
    fun hf x => (hf.differentiable (by simp)) x
  have hXs : ∀ j, ContDiff ℝ ∞ (X j) := fun j =>
    (hw.mul (contDiff_flux hg hdet hϑ j)).sub (hϑ.mul (contDiff_flux hg hdet hw j))
  have hsymm' : ∀ x j k, (g x)⁻¹ j k = (g x)⁻¹ k j := fun x j k => by
    rw [← Matrix.transpose_apply (g x)⁻¹, Matrix.transpose_nonsing_inv, hsymm]
  have hdiv : ∀ x, ∑ j, d (X j) x j =
      ϑ x * box g w x * √|(g x).det| - w x * box g ϑ x * √|(g x).det| := by
    intro x
    have hcross : ∑ j, d w x j * flux g ϑ j x = ∑ j, d ϑ x j * flux g w j x := by
      simp only [flux, Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      rw [hsymm' x j k]
      ring
    have hb1 := sqrt_abs_det_mul_box (hdet x) ϑ
    have hb2 := sqrt_abs_det_mul_box (hdet x) w
    simp only [X]
    rw [Finset.sum_congr rfl fun j _ => by
      rw [d_sub (hdiff (hw.mul (contDiff_flux hg hdet hϑ j)) x)
        (hdiff (hϑ.mul (contDiff_flux hg hdet hw j)) x),
        d_mul (hdiff hw x) (hdiff (contDiff_flux hg hdet hϑ j) x),
        d_mul (hdiff hϑ x) (hdiff (contDiff_flux hg hdet hw j) x)]]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    linear_combination hcross + w x * hb1 - ϑ x * hb2
  have hX := integral_divergence_M0_eq_zero T X (fun j => (hXs j).of_le (by simp))
    fun j x hx => by simp [X, flux, d_def, hw0 x hx, hdw0 x hx]
  have hρ := (contDiff_sqrt_abs_det hg hdet).continuous
  have hint : ∀ {f h : E n → ℝ}, ContDiff ℝ ∞ f → ContDiff ℝ ∞ h →
      IntegrableOn (fun x => f x * box g h x * √|(g x).det|) (M0 n T) := fun hf hh =>
    ((hf.continuous.mul (continuous_box hg hdet hh)).mul hρ).continuousOn.integrableOn_compact
      (isCompact_M0 T)
  simp only [hdiv] at hX
  rw [integral_sub (hint hϑ hw) (hint hw hϑ), sub_eq_zero] at hX
  exact hX.symm

end LorentzianCalderon
