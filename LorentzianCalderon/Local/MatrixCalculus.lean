module

public import Mathlib

public section

/-!
# Calculus of matrix-valued functions

Regularity of the determinant, the adjugate, the inverse and `√|det|` of a matrix field
whose entries are differentiable or `C^m` (at a point, on a set, or everywhere), and Jacobi's formula for the derivative of
the determinant.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix
open Matrix Finset

section Algebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]

/-- The adjugate as the determinant of a matrix with a column replaced. -/
theorem adjugate_apply_eq_det_updateCol (A : Matrix ι ι R) (i j : ι) :
    A.adjugate i j = (A.updateCol i (Pi.single j 1)).det := by
  rw [← det_transpose, ← updateRow_transpose, ← adjugate_apply, ← adjugate_transpose]
  rfl

/-- Swapping the roles of two columns `j ≠ l` changes the sign of the determinant. -/
theorem det_updateCol_updateCol_swap (A : Matrix ι ι R) {j l : ι} (h : j ≠ l)
    (u w : ι → R) :
    ((A.updateCol j u).updateCol l w).det = -((A.updateCol l u).updateCol j w).det := by
  have : (A.updateCol j u).updateCol l w =
      ((A.updateCol l u).updateCol j w).submatrix id (Equiv.swap j l) := by
    ext r c
    simp only [updateCol_apply, submatrix_apply, id_eq, Equiv.swap_apply_def]
    split_ifs <;> simp_all
  rw [this, det_permute', Equiv.Perm.sign_swap h]
  simp

/-- The determinant of a matrix with a column replaced, expanded along that column. -/
theorem det_updateCol_eq_sum_adjugate (A : Matrix ι ι R) (l : ι) (c : ι → R) :
    (A.updateCol l c).det = ∑ m, A.adjugate l m * c m := by
  rw [← cramer_apply, cramer_eq_adjugate_mulVec]
  rfl

end Algebra

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {A : F → Matrix ι ι ℝ} {x : F}

section ContDiff

variable {m : ℕ∞ω}

theorem contDiffAt_det (h : ∀ i j, ContDiffAt ℝ m (fun y => A y i j) x) :
    ContDiffAt ℝ m (fun y => (A y).det) x := by
  simp_rw [det_apply']
  exact ContDiffAt.sum fun σ _ => contDiffAt_const.mul (contDiffAt_prod fun i _ => h _ _)

theorem contDiffAt_adjugate (h : ∀ i j, ContDiffAt ℝ m (fun y => A y i j) x) (i j : ι) :
    ContDiffAt ℝ m (fun y => (A y).adjugate i j) x := by
  simp_rw [adjugate_apply]
  refine contDiffAt_det fun k l => ?_
  simp only [updateRow_apply]
  by_cases hk : k = j
  · simp only [hk, ite_true]
    exact contDiffAt_const
  · simpa [hk] using h k l

theorem contDiffAt_inv (h : ∀ i j, ContDiffAt ℝ m (fun y => A y i j) x)
    (hdet : (A x).det ≠ 0) (i j : ι) :
    ContDiffAt ℝ m (fun y => (A y)⁻¹ i j) x := by
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact ((contDiffAt_det h).inv hdet).mul (contDiffAt_adjugate h i j)

theorem contDiffAt_sqrt_abs_det {m : ℕ∞} (h : ∀ i j, ContDiffAt ℝ m (fun y => A y i j) x)
    (hdet : (A x).det ≠ 0) :
    ContDiffAt ℝ m (fun y => √|(A y).det|) x :=
  ((contDiffAt_det h).abs hdet).sqrt (by simpa using hdet)

theorem contDiff_det (h : ∀ i j, ContDiff ℝ m fun y => A y i j) :
    ContDiff ℝ m fun y => (A y).det :=
  contDiff_iff_contDiffAt.2 fun _ => contDiffAt_det fun i j => (h i j).contDiffAt

theorem contDiff_inv_apply (h : ∀ i j, ContDiff ℝ m fun y => A y i j)
    (hdet : ∀ y, (A y).det ≠ 0) (i j : ι) : ContDiff ℝ m fun y => (A y)⁻¹ i j :=
  contDiff_iff_contDiffAt.2 fun y => contDiffAt_inv (fun i j => (h i j).contDiffAt) (hdet y) i j

theorem contDiff_sqrt_abs_det {m : ℕ∞} (h : ∀ i j, ContDiff ℝ m fun y => A y i j)
    (hdet : ∀ y, (A y).det ≠ 0) : ContDiff ℝ m fun y => √|(A y).det| :=
  contDiff_iff_contDiffAt.2 fun y =>
    contDiffAt_sqrt_abs_det (fun i j => (h i j).contDiffAt) (hdet y)

theorem contDiffOn_det {V : Set F} (h : ∀ i j, ContDiffOn ℝ m (fun y => A y i j) V) :
    ContDiffOn ℝ m (fun y => (A y).det) V := by
  simp only [det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => h _ _)

theorem contDiffOn_inv_apply {V : Set F} (h : ∀ i j, ContDiffOn ℝ m (fun y => A y i j) V)
    (hdet : ∀ y ∈ V, (A y).det ≠ 0) (i j : ι) :
    ContDiffOn ℝ m (fun y => (A y)⁻¹ i j) V := by
  simp only [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul,
    Matrix.adjugate_apply]
  refine ((contDiffOn_det h).inv hdet).mul (contDiffOn_det fun a b => ?_)
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiffOn_const
  · exact h a b

end ContDiff

section Differentiable

theorem hasFDerivAt_det (h : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x) :
    HasFDerivAt (fun y => (A y).det)
      (∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) •
        ∑ i, (∏ j ∈ univ.erase i, A x (σ j) j) • fderiv ℝ (fun y => A y (σ i) i) x) x := by
  simp_rw [det_apply']
  exact HasFDerivAt.fun_sum fun σ _ => (HasFDerivAt.finsetProd fun i _ =>
    (h (σ i) i).hasFDerivAt).const_mul _

theorem differentiableAt_det (h : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x) :
    DifferentiableAt ℝ (fun y => (A y).det) x :=
  (hasFDerivAt_det h).differentiableAt

theorem differentiableAt_adjugate (h : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x)
    (i j : ι) : DifferentiableAt ℝ (fun y => (A y).adjugate i j) x := by
  simp_rw [adjugate_apply]
  refine differentiableAt_det fun k l => ?_
  simp only [updateRow_apply]
  by_cases hk : k = j
  · simp only [hk, ite_true]
    exact differentiableAt_const _
  · simpa [hk] using h k l

theorem differentiableAt_inv (h : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x)
    (hdet : (A x).det ≠ 0) (i j : ι) :
    DifferentiableAt ℝ (fun y => (A y)⁻¹ i j) x := by
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact ((differentiableAt_det h).inv hdet).mul (differentiableAt_adjugate h i j)

theorem differentiableAt_sqrt_abs_det (h : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x)
    (hdet : (A x).det ≠ 0) :
    DifferentiableAt ℝ (fun y => √|(A y).det|) x :=
  ((differentiableAt_det h).abs hdet).sqrt (by simpa using hdet)

/-- Jacobi's formula: the derivative of the determinant is the sum over the columns of the
determinants with that column differentiated. -/
theorem fderiv_det_apply (h : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x) (w : F) :
    fderiv ℝ (fun y => (A y).det) x w =
      ∑ l, ((A x).updateCol l fun k => fderiv ℝ (fun y => A y k l) x w).det := by
  rw [(hasFDerivAt_det h).fderiv]
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, smul_eq_mul, det_apply']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ l)]
  simp only [updateCol_apply, ite_true]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  simp [Finset.ne_of_mem_erase hi]

/-- Jacobi's formula in terms of the adjugate. -/
theorem fderiv_det_apply_eq_sum_adjugate (h : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x)
    (w : F) :
    fderiv ℝ (fun y => (A y).det) x w =
      ∑ l, ∑ k, (A x).adjugate l k * fderiv ℝ (fun y => A y k l) x w := by
  simp_rw [fderiv_det_apply h, det_updateCol_eq_sum_adjugate]

/-- Jacobi's formula in terms of the inverse: `∂ det A = det A · tr (A⁻¹ ∂A)`. -/
theorem fderiv_det_apply_eq_det_mul_trace (h : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x)
    (hdet : (A x).det ≠ 0) (w : F) :
    fderiv ℝ (fun y => (A y).det) x w =
      (A x).det * ∑ l, ∑ k, (A x)⁻¹ l k * fderiv ℝ (fun y => A y k l) x w := by
  rw [fderiv_det_apply_eq_sum_adjugate h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  field_simp

/-- The derivative of the volume density: `∂√|det A| = ½ √|det A| tr (A⁻¹ ∂A)`. -/
theorem fderiv_sqrt_abs_det_apply (h : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x)
    (hdet : (A x).det ≠ 0) (w : F) :
    fderiv ℝ (fun y => √|(A y).det|) x w =
      2⁻¹ * √|(A x).det| * ∑ l, ∑ k, (A x)⁻¹ l k * fderiv ℝ (fun y => A y k l) x w := by
  have habs : 0 < |(A x).det| := abs_pos.mpr hdet
  have hd := differentiableAt_det h
  rw [fderiv_sqrt ((hd.abs hdet)) habs.ne', _root_.smul_apply, smul_eq_mul]
  rcases hdet.lt_or_gt with hneg | hpos
  · have : (fun y => |(A y).det|) =ᶠ[nhds x] fun y => -(A y).det := by
      filter_upwards [hd.continuousAt.eventually (gt_mem_nhds hneg)] with y hy
      exact abs_of_neg hy
    rw [this.fderiv_eq, fderiv_fun_neg, _root_.neg_apply,
      fderiv_det_apply_eq_det_mul_trace h hdet, abs_of_neg hneg]
    have hs : (0 : ℝ) < √(-(A x).det) := Real.sqrt_pos.mpr (by linarith)
    field_simp
    rw [Real.sq_sqrt (by linarith)]
    ring
  · have : (fun y => |(A y).det|) =ᶠ[nhds x] fun y => (A y).det := by
      filter_upwards [hd.continuousAt.eventually (lt_mem_nhds hpos)] with y hy
      exact abs_of_pos hy
    rw [this.fderiv_eq, fderiv_det_apply_eq_det_mul_trace h hdet, abs_of_pos hpos]
    have hs : (0 : ℝ) < √((A x).det) := Real.sqrt_pos.mpr hpos
    field_simp
    rw [Real.sq_sqrt hpos.le]

end Differentiable

end

end LorentzianCalderon
