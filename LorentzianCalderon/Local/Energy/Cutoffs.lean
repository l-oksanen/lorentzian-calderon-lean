module

public import LorentzianCalderon.Local.Energy.Step1

public section

/-!
# The cut-off `χ_ε` of Step 3 and the regularity of the current

`χ_ε = H_ε(τ - ψ) H_ε(ψ' - c) H_ε(φ - s)` with `H_ε(r) = H(r / ε)` for the cut-off function
`H = cutoff`. Its support lies in the lens, where `φ > s`.
-/

namespace LorentzianCalderon

noncomputable section
open Set MeasureTheory Filter Topology
open scoped ContDiff

variable {n : ℕ}

/-- The cut-off `χ_ε = H_ε(τ - ψ) H_ε(ψ' - c) H_ε(φ - s)`. -/
def chi (ψ ψ' φ : E n → ℝ) (τ c s ε : ℝ) (y : E n) : ℝ :=
  cutoff ((τ - ψ y) / ε) * cutoff ((ψ' y - c) / ε) * cutoff ((φ y - s) / ε)

theorem chi_def (ψ ψ' φ : E n → ℝ) (τ c s ε : ℝ) (y : E n) :
    chi ψ ψ' φ τ c s ε y =
      cutoff ((τ - ψ y) / ε) * cutoff ((ψ' y - c) / ε) * cutoff ((φ y - s) / ε) := by rfl

theorem chi_nonneg (ψ ψ' φ : E n → ℝ) (τ c s ε : ℝ) (y : E n) : 0 ≤ chi ψ ψ' φ τ c s ε y :=
  mul_nonneg (mul_nonneg (cutoff_nonneg _) (cutoff_nonneg _)) (cutoff_nonneg _)

theorem chi_le_one (ψ ψ' φ : E n → ℝ) (τ c s ε : ℝ) (y : E n) : chi ψ ψ' φ τ c s ε y ≤ 1 := by
  unfold chi
  have h1 := cutoff_le_one ((τ - ψ y) / ε)
  have h2 := cutoff_le_one ((ψ' y - c) / ε)
  have h3 := cutoff_le_one ((φ y - s) / ε)
  exact (mul_le_of_le_one_left (cutoff_nonneg _)
    ((mul_le_of_le_one_left (cutoff_nonneg _) h1).trans h2)).trans h3

theorem cutoff_div_of_nonpos {r ε : ℝ} (hε : 0 < ε) (hr : r ≤ 0) : cutoff (r / ε) = 0 :=
  cutoff_of_nonpos (div_nonpos_of_nonpos_of_nonneg hr hε.le)

theorem chi_eq_zero_of_le {ψ ψ' φ : E n → ℝ} {τ c s ε : ℝ} (hε : 0 < ε) {y : E n}
    (hy : φ y ≤ s) : chi ψ ψ' φ τ c s ε y = 0 := by
  rw [chi, cutoff_div_of_nonpos (r := φ y - s) hε (by linarith), mul_zero]

theorem chi_eq_zero_of_not_mem {V : Set (E n)} {ψ ψ' φ : E n → ℝ} {τ c s ε : ℝ} (hε : 0 < ε)
    {y : E n} (hyV : y ∈ V) (hy : y ∉ lens V ψ ψ' τ c) : chi ψ ψ' φ τ c s ε y = 0 := by
  simp only [lens_def, mem_ofPred_eq, not_and_or, not_le] at hy
  rcases hy with hy | hy | hy
  · exact absurd hyV hy
  · rw [chi, cutoff_div_of_nonpos hε (by linarith)]; ring
  · rw [chi, cutoff_div_of_nonpos (r := ψ' y - c) hε (by linarith)]; ring

theorem hasDerivAt_cutoff_affine (a b ε r : ℝ) :
    HasDerivAt (fun r => cutoff ((a + b * r) / ε)) (cutoffDeriv ((a + b * r) / ε) * (b / ε)) r := by
  have := (hasDerivAt_cutoff ((a + b * r) / ε)).comp r
    ((((hasDerivAt_id r).const_mul b).const_add a).div_const ε)
  exact this.congr_deriv (by ring)

theorem contDiff_cutoff_affine (a b ε : ℝ) : ContDiff ℝ 1 fun r => cutoff ((a + b * r) / ε) :=
  contDiff_cutoff.comp ((contDiff_const.add (contDiff_const.mul contDiff_id)).div_const _)

/-- The partial derivatives of `χ_ε`. -/
theorem d_chi {ψ ψ' φ : E n → ℝ} {x : E n} (hψ : DifferentiableAt ℝ ψ x)
    (hψ' : DifferentiableAt ℝ ψ' x) (hφ : DifferentiableAt ℝ φ x) (τ c s ε : ℝ)
    (j : Fin (n + 1)) :
    d (chi ψ ψ' φ τ c s ε) x j =
      cutoffDeriv ((τ - ψ x) / ε) * (-1 / ε) * d ψ x j * cutoff ((ψ' x - c) / ε) *
          cutoff ((φ x - s) / ε) +
        cutoff ((τ - ψ x) / ε) * (cutoffDeriv ((ψ' x - c) / ε) * (1 / ε) * d ψ' x j) *
          cutoff ((φ x - s) / ε) +
        cutoff ((τ - ψ x) / ε) * cutoff ((ψ' x - c) / ε) *
          (cutoffDeriv ((φ x - s) / ε) * (1 / ε) * d φ x j) := by
  have e1 : (fun y => cutoff ((τ - ψ y) / ε)) =
      fun y => (fun r => cutoff ((τ + -1 * r) / ε)) (ψ y) := by
    ext y; ring_nf
  have e2 : (fun y => cutoff ((ψ' y - c) / ε)) =
      fun y => (fun r => cutoff ((-c + 1 * r) / ε)) (ψ' y) := by
    ext y; ring_nf
  have e3 : (fun y => cutoff ((φ y - s) / ε)) =
      fun y => (fun r => cutoff ((-s + 1 * r) / ε)) (φ y) := by
    ext y; ring_nf
  have d1 : d (fun y => cutoff ((τ - ψ y) / ε)) x j =
      cutoffDeriv ((τ - ψ x) / ε) * (-1 / ε) * d ψ x j := by
    rw [e1, d_comp_of_hasDerivAt (hasDerivAt_cutoff_affine τ (-1) ε (ψ x)) hψ]; ring_nf
  have d2 : d (fun y => cutoff ((ψ' y - c) / ε)) x j =
      cutoffDeriv ((ψ' x - c) / ε) * (1 / ε) * d ψ' x j := by
    rw [e2, d_comp_of_hasDerivAt (hasDerivAt_cutoff_affine (-c) 1 ε (ψ' x)) hψ']; ring_nf
  have d3 : d (fun y => cutoff ((φ y - s) / ε)) x j =
      cutoffDeriv ((φ x - s) / ε) * (1 / ε) * d φ x j := by
    rw [e3, d_comp_of_hasDerivAt (hasDerivAt_cutoff_affine (-s) 1 ε (φ x)) hφ]; ring_nf
  have D1 : DifferentiableAt ℝ (fun y => cutoff ((τ - ψ y) / ε)) x := by
    rw [e1]; exact ((contDiff_cutoff_affine _ _ _).differentiable one_ne_zero _).comp x hψ
  have D2 : DifferentiableAt ℝ (fun y => cutoff ((ψ' y - c) / ε)) x := by
    rw [e2]; exact ((contDiff_cutoff_affine _ _ _).differentiable one_ne_zero _).comp x hψ'
  have D3 : DifferentiableAt ℝ (fun y => cutoff ((φ y - s) / ε)) x := by
    rw [e3]; exact ((contDiff_cutoff_affine _ _ _).differentiable one_ne_zero _).comp x hφ
  unfold chi
  rw [d_mul (u := fun y => cutoff ((τ - ψ y) / ε) * cutoff ((ψ' y - c) / ε)) (D1.mul D2) D3,
    d_mul D1 D2, d1, d2, d3]
  ring

theorem contDiffOn_chi {V : Set (E n)} {ψ ψ' φ : E n → ℝ} (hψ : ContDiffOn ℝ 1 ψ V)
    (hψ' : ContDiffOn ℝ 1 ψ' V) (hφ : ContDiffOn ℝ 1 φ V) (τ c s ε : ℝ) :
    ContDiffOn ℝ 1 (chi ψ ψ' φ τ c s ε) V := by
  have h1 := (contDiff_cutoff_affine τ (-1) ε).comp_contDiffOn hψ
  have h2 := (contDiff_cutoff_affine (-c) 1 ε).comp_contDiffOn hψ'
  have h3 := (contDiff_cutoff_affine (-s) 1 ε).comp_contDiffOn hφ
  refine ((h1.mul h2).mul h3).congr fun y _ => ?_
  simp only [chi, Function.comp]
  ring_nf

theorem continuous_cutoff : Continuous cutoff := contDiff_cutoff.continuous

end

end LorentzianCalderon
