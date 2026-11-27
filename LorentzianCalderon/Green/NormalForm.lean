module

public import LorentzianCalderon.Local.BoxCalculus
public import LorentzianCalderon.Local.Energy.Coform

public section

/-!
# The wave operator of a metric with zero shift

A metric `G` with zero shift (`G₀ᵢ = Gᵢ₀ = 0` for `i ≥ 1`, `HasZeroShift`) and `G₀₀ = -N² < 0`
has `G^{00} = -1/N²` and `G^{0i} = G^{i0} = 0`. Writing `□_G` in non-divergence form
(`box_eq_sub_drift`) and multiplying by `N²` turns `□_G v = f` into the evolution equation

`∂₀²v = a^{ij} ∂ᵢ∂ⱼv + b^μ ∂_μv + N² f`  (`d2_zero_zero_eq`),

with `a^{ij} = N² G^{ij}` (`normalA`, indices `i, j ≥ 1`) and
`b^μ = N² |det G|^{-1/2} ∂ⱼ(|det G|^{1/2} G^{jμ})` (`normalB`). The principal part is positive
definite if `G` is positive definite on `{w⁰ = 0}` (`normalA_pos`), the coefficients depend
smoothly on parameters (`contDiffAt_normalA`, `contDiffAt_normalB`), and for a locally constant
diagonal metric `diag(-c, 1, …, 1)` they are `a = c · id`, `b = 0`.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Matrix Finset Filter

variable {n : ℕ}

/-- `A` has zero shift: `A₀ᵢ = Aᵢ₀ = 0` for `i ≥ 1`. -/
structure HasZeroShift (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Prop where
  left : ∀ i : Fin n, A 0 i.succ = 0
  right : ∀ i : Fin n, A i.succ 0 = 0

section Algebra

variable {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}

/-- Row `0` of `A A⁻¹ = 1`, for zero shift. -/
theorem HasZeroShift.mul_inv_zero (hA : HasZeroShift A) (hdet : A.det ≠ 0) (j : Fin (n + 1)) :
    A 0 0 * A⁻¹ 0 j = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) 0 j := by
  rw [← mul_nonsing_inv A hdet.isUnit, mul_apply, Fin.sum_univ_succ]
  simp [hA.left]

/-- `A₀₀ A^{00} = 1` for zero shift. -/
theorem HasZeroShift.inv_zero_zero (hA : HasZeroShift A) (hdet : A.det ≠ 0) :
    A 0 0 * A⁻¹ 0 0 = 1 := by
  simpa using hA.mul_inv_zero hdet 0

/-- `A^{0i} = 0` for zero shift. -/
theorem HasZeroShift.inv_zero_succ (hA : HasZeroShift A) (hdet : A.det ≠ 0) (i : Fin n) :
    A⁻¹ 0 i.succ = 0 := by
  have h := hA.mul_inv_zero hdet i.succ
  rw [one_apply_ne (Fin.succ_ne_zero i).symm] at h
  exact (mul_eq_zero.1 h).resolve_left (left_ne_zero_of_mul_eq_one (hA.inv_zero_zero hdet))

/-- `A^{i0} = 0` for zero shift. -/
theorem HasZeroShift.inv_succ_zero (hA : HasZeroShift A) (hdet : A.det ≠ 0) (i : Fin n) :
    A⁻¹ i.succ 0 = 0 := by
  have h := congrFun (congrFun (nonsing_inv_mul A hdet.isUnit) i.succ) 0
  rw [mul_apply, Fin.sum_univ_succ, one_apply_ne (Fin.succ_ne_zero i)] at h
  simp only [hA.right, mul_zero, Finset.sum_const_zero, add_zero] at h
  exact (mul_eq_zero.1 h).resolve_right (left_ne_zero_of_mul_eq_one (hA.inv_zero_zero hdet))

/-- `Σᵢⱼ A^{ij} ξᵢ ξⱼ = A(w, w)` for `w = A⁻¹(0, ξ)`, which has `w⁰ = 0`. -/
theorem sum_inv_succ_eq_form (hdet : A.det ≠ 0)
    (ξ : Fin n → ℝ) :
    ∑ i, ∑ j, A⁻¹ i.succ j.succ * ξ i * ξ j =
      form A (WithLp.toLp 2 (A⁻¹ *ᵥ Fin.cons 0 ξ)) (WithLp.toLp 2 (A⁻¹ *ᵥ Fin.cons 0 ξ)) := by
  rw [form_eq_bil, WithLp.ofLp_toLp, bil_apply, mulVec_mulVec, mul_nonsing_inv _ hdet.isUnit,
    one_mulVec, dotProduct, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, mul_zero, zero_add, Fin.cons_succ, mulVec, dotProduct,
    Fin.sum_univ_succ, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Algebra

/-- The squared lapse `N² = -G₀₀`. -/
def lapseSq (G : MatrixField n) (z : E n) : ℝ := -G z 0 0

/-- The principal coefficients `a^{ij} = N² G^{ij}` (`i, j ≥ 1`) of the normal form. -/
def normalA (G : MatrixField n) (z : E n) (i j : Fin n) : ℝ :=
  lapseSq G z * (G z)⁻¹ i.succ j.succ

/-- The first-order coefficients `b^μ = N² |det G|^{-1/2} ∂ⱼ(|det G|^{1/2} G^{jμ})` of the
normal form. -/
def normalB (G : MatrixField n) (z : E n) (k : Fin (n + 1)) : ℝ :=
  lapseSq G z * ((√|(G z).det|)⁻¹ * ∑ j, d (fun w => √|(G w).det| * (G w)⁻¹ j k) z j)

variable {G : MatrixField n} {z : E n}

/-- The normal form of `□_G` for a metric with zero shift:
`∂₀²u = a^{ij} ∂ᵢ∂ⱼu + b^μ ∂_μu + N² □_G u`. -/
theorem d2_zero_zero_eq (hG : ∀ i j, DifferentiableAt ℝ (fun y => G y i j) z)
    (hdet : (G z).det ≠ 0) (hs : HasZeroShift (G z)) {u : E n → ℝ} (hu : ContDiffAt ℝ 2 u z) :
    d2 u z 0 0 = ∑ i, ∑ j, normalA G z i j * d2 u z i.succ j.succ +
      ∑ k, normalB G z k * d u z k + lapseSq G z * box G u z := by
  have hsplit : ∑ j, ∑ k, (G z)⁻¹ j k * d2 u z j k = (G z)⁻¹ 0 0 * d2 u z 0 0 +
      ∑ i : Fin n, ∑ j : Fin n, (G z)⁻¹ i.succ j.succ * d2 u z i.succ j.succ := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.sum_univ_succ, hs.inv_zero_succ hdet, hs.inv_succ_zero hdet, zero_mul,
      Finset.sum_const_zero, add_zero, zero_add]
  rw [box_eq_sub_drift hG hdet hu, hsplit]
  simp only [normalA, normalB, lapseSq, mul_assoc, ← Finset.mul_sum]
  linear_combination (-(d2 u z 0 0)) * hs.inv_zero_zero hdet

/-- `□_G u = f` at `z` if and only if `∂₀²u = a^{ij} ∂ᵢ∂ⱼu + b^μ ∂_μu + N² f` there. -/
theorem box_eq_iff (hG : ∀ i j, DifferentiableAt ℝ (fun y => G y i j) z)
    (hdet : (G z).det ≠ 0) (hs : HasZeroShift (G z)) (h00 : G z 0 0 ≠ 0) {u : E n → ℝ}
    (hu : ContDiffAt ℝ 2 u z) (f : ℝ) :
    box G u z = f ↔ d2 u z 0 0 = ∑ i, ∑ j, normalA G z i j * d2 u z i.succ j.succ +
      ∑ k, normalB G z k * d u z k + lapseSq G z * f := by
  rw [d2_zero_zero_eq hG hdet hs hu, add_right_inj]
  refine ⟨fun h => h ▸ rfl, fun h => ?_⟩
  exact mul_left_cancel₀ (neg_ne_zero.2 h00) h

/-- The principal part is symmetric for a symmetric metric. -/
theorem normalA_symm (hsymm : (G z)ᵀ = G z) (i j : Fin n) : normalA G z i j = normalA G z j i := by
  have : ((G z)⁻¹)ᵀ = (G z)⁻¹ := by rw [transpose_nonsing_inv, hsymm]
  rw [normalA, normalA, ← this, transpose_apply, this]

/-- The principal part is positive definite if `G₀₀ < 0` and `G` is positive definite on
`{w⁰ = 0}`. -/
theorem normalA_pos (hdet : (G z).det ≠ 0) (hs : HasZeroShift (G z)) (h00 : G z 0 0 < 0)
    (hpos : ∀ w : E n, w 0 = 0 → w ≠ 0 → 0 < form (G z) w w) {ξ : Fin n → ℝ} (hξ : ξ ≠ 0) :
    0 < ∑ i, ∑ j, normalA G z i j * ξ i * ξ j := by
  have hsum : ∑ i, ∑ j, normalA G z i j * ξ i * ξ j =
      lapseSq G z * ∑ i, ∑ j, (G z)⁻¹ i.succ j.succ * ξ i * ξ j := by
    simp only [normalA, mul_assoc, Finset.mul_sum]
  rw [hsum, sum_inv_succ_eq_form hdet]
  refine mul_pos (neg_pos.2 h00) (hpos _ ?_ ?_)
  · change ((G z)⁻¹ *ᵥ Fin.cons 0 ξ) 0 = 0
    simp only [mulVec, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, mul_zero, zero_add,
      hs.inv_zero_succ hdet, zero_mul, Finset.sum_const_zero]
  · intro h0
    apply hξ
    have h1 : (G z)⁻¹ *ᵥ (Fin.cons 0 ξ : Fin (n + 1) → ℝ) = 0 := by
      simpa using congrArg WithLp.ofLp h0
    have h2 := congrArg (G z *ᵥ ·) h1
    simp only [mulVec_mulVec, mul_nonsing_inv _ hdet.isUnit, one_mulVec, mulVec_zero] at h2
    funext i
    simpa using congrFun h2 i.succ

/-- Where `G` is locally constant, the first-order coefficients vanish. -/
theorem normalB_eq_zero {C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (h : ∀ᶠ w in 𝓝 z, G w = C) (k : Fin (n + 1)) : normalB G z k = 0 := by
  have : ∀ j, d (fun w => √|(G w).det| * (G w)⁻¹ j k) z j = 0 := fun j => by
    rw [d_congr (u := fun w => √|(G w).det| * (G w)⁻¹ j k) (v := fun _ => √|C.det| * C⁻¹ j k)
      (h.mono fun w hw => by simp only [hw]), d_const]
  simp [normalB, this]

/-- The metric `diag(-c, 1, …, 1)`. -/
def lapseDiag (c : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  diagonal fun i => if i = 0 then -c else 1

theorem lapseDiag_def (c : ℝ) :
    lapseDiag (n := n) c =
      diagonal fun i => if i = 0 then -c else 1 := by rfl

/-- `diag(-1, 1, …, 1)` is the Minkowski metric. -/
theorem lapseDiag_one : lapseDiag (n := n) 1 = minkowski n := by
  rw [minkowski_def]
  rfl

/-- `diag(-c, 1, …, 1)⁻¹ = diag(-1/c, 1, …, 1)`. -/
theorem inv_lapseDiag {c : ℝ} (hc : c ≠ 0) :
    (lapseDiag (n := n) c)⁻¹ = lapseDiag c⁻¹ := by
  refine inv_eq_left_inv ?_
  rw [lapseDiag, lapseDiag, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  ext i
  split_ifs <;> field_simp

/-- `diag(-c, 1, …, 1)` has zero shift. -/
theorem HasZeroShift.lapseDiag (c : ℝ) : HasZeroShift (lapseDiag (n := n) c) where
  left i := by simp [LorentzianCalderon.lapseDiag, diagonal_apply_ne _ (Fin.succ_ne_zero i).symm]
  right i := by simp [LorentzianCalderon.lapseDiag]

/-- For `G = diag(-c, 1, …, 1)` at `z`, `N² = c` and `a = c · id`. -/
theorem normalA_of_eq_lapseDiag {c : ℝ} (hc : c ≠ 0) (h : G z = lapseDiag c) (i j : Fin n) :
    normalA G z i j = if i = j then c else 0 := by
  rw [normalA, lapseSq, h, inv_lapseDiag hc, LorentzianCalderon.lapseDiag,
    LorentzianCalderon.lapseDiag]
  simp only [diagonal_apply, Fin.succ_inj, Fin.succ_ne_zero, ite_false, ite_true]
  split_ifs <;> simp

/-- For `G = diag(-c, 1, …, 1)` at `z`, `N² = c`. -/
theorem lapseSq_of_eq_lapseDiag {c : ℝ} (h : G z = lapseDiag c) : lapseSq G z = c := by
  simp [lapseSq, h, LorentzianCalderon.lapseDiag]

section Family

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {G : P → MatrixField n}
  {q : P × E n}

/-- The squared lapse depends smoothly on parameters. -/
theorem contDiffAt_lapseSq (hG : ∀ i j, ContDiffAt ℝ ∞ (fun q : P × E n => G q.1 q.2 i j) q) :
    ContDiffAt ℝ ∞ (fun q : P × E n => lapseSq (G q.1) q.2) q :=
  (hG 0 0).neg

/-- The principal coefficients depend smoothly on parameters. -/
theorem contDiffAt_normalA (hG : ∀ i j, ContDiffAt ℝ ∞ (fun q : P × E n => G q.1 q.2 i j) q)
    (hdet : (G q.1 q.2).det ≠ 0) (i j : Fin n) :
    ContDiffAt ℝ ∞ (fun q : P × E n => normalA (G q.1) q.2 i j) q :=
  (contDiffAt_lapseSq hG).mul
    (contDiffAt_inv (A := fun q : P × E n => G q.1 q.2) hG hdet i.succ j.succ)

/-- The first-order coefficients depend smoothly on parameters. -/
theorem contDiffAt_normalB (hG : ∀ i j, ContDiffAt ℝ ∞ (fun q : P × E n => G q.1 q.2 i j) q)
    (hdet : (G q.1 q.2).det ≠ 0) (k : Fin (n + 1)) :
    ContDiffAt ℝ ∞ (fun q : P × E n => normalB (G q.1) q.2 k) q := by
  have hF : ∀ j, ContDiffAt ℝ ∞
      (fun q : P × E n => √|(G q.1 q.2).det| * (G q.1 q.2)⁻¹ j k) q := fun j =>
    (contDiffAt_sqrt_abs_det (A := fun q : P × E n => G q.1 q.2) hG hdet).mul
      (contDiffAt_inv (A := fun q : P × E n => G q.1 q.2) hG hdet j k)
  have hd : ∀ j, ContDiffAt ℝ ∞ (fun q : P × E n =>
      d (fun w => √|(G q.1 w).det| * (G q.1 w)⁻¹ j k) q.2 j) q := fun j => by
    simp only [d_def]
    have h1 : ContDiffAt ℝ ∞ (Function.uncurry fun (q' : P × E n) (w : E n) =>
        √|(G q'.1 w).det| * (G q'.1 w)⁻¹ j k) (q, q.2) := by
      have := (hF j).comp (q, q.2) (f := fun p : (P × E n) × E n => (p.1.1, p.2))
        (by fun_prop)
      exact this
    exact (ContDiffAt.fderiv h1 contDiffAt_snd (by simp)).clm_apply contDiffAt_const
  exact (contDiffAt_lapseSq hG).mul (((contDiffAt_sqrt_abs_det
    (A := fun q : P × E n => G q.1 q.2) hG hdet).inv (by simpa using hdet)).mul
    (ContDiffAt.sum fun j _ => hd j))

end Family

end

end LorentzianCalderon
