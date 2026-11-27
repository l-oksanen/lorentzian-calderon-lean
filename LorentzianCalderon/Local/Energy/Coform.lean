module

public import LorentzianCalderon.Facts.Vocabulary
public import LorentzianCalderon.Local.Energy.Algebra

public section

/-!
# Lorentzian scalar products of vectors and covectors

A Lorentzian matrix `A` gives a form of Lorentzian type (`IsLorentzForm`) on vectors, and its
inverse gives one on covectors. We translate the conditions on vectors (`form`, `grad`,
`IsFutureTimelike`, `IsFutureCausal`) into conditions on covectors (`coform`).
-/

namespace LorentzianCalderon

noncomputable section
open Matrix WithLp

variable {n : ℕ}

/-- The bilinear form `vⁱ Aᵢⱼ wʲ` on `ℝ^{1+n}` given by a matrix. -/
abbrev bil (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    LinearMap.BilinForm ℝ (Fin (n + 1) → ℝ) :=
  Matrix.toLinearMap₂' ℝ A

theorem bil_apply (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (v w : Fin (n + 1) → ℝ) :
    bil A v w = v ⬝ᵥ (A *ᵥ w) :=
  Matrix.toLinearMap₂'_apply' A v w

theorem form_eq_bil (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (v w : E n) :
    form A v w = bil A (ofLp v) (ofLp w) := by
  rw [bil, Matrix.toLinearMap₂'_apply, form_def]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [smul_eq_mul]
  ring

theorem coform_eq_bil (g : MatrixField n) (x : E n) (ξ η : Fin (n + 1) → ℝ) :
    coform g x ξ η = bil (g x)⁻¹ ξ η := by
  rw [bil, Matrix.toLinearMap₂'_apply, coform_def]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [smul_eq_mul]
  ring

theorem ofLp_grad (g : MatrixField n) (u : E n → ℝ) (x : E n) :
    ofLp (grad g u x) = (g x)⁻¹ *ᵥ d u x := by
  ext j
  simp [grad_def, Matrix.mulVec, dotProduct]

theorem bil_symm {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hA : Aᵀ = A)
    (v w : Fin (n + 1) → ℝ) : bil A v w = bil A w v := by
  rw [bil_apply, bil_apply, dotProduct_mulVec, ← mulVec_transpose, hA, dotProduct_comm]

/-- A form of Lorentzian signature on vectors is of Lorentzian type. -/
theorem IsLorentzian.isLorentzForm {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : IsLorentzian A) : IsLorentzForm (bil A) := by
  refine ⟨bil_symm hA.symm, fun β hβ ξ hξβ hξ => ?_⟩
  by_contra hle
  push Not at hle
  obtain ⟨S, hS⟩ := hA.spacelike
  let e := (WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ))
  let S' := S.map e.toLinearMap
  have hS' : Module.finrank ℝ S' = n := (LinearEquiv.finrank_map_eq e S).trans hS.finrank_eq
  have hind : LinearIndependent ℝ ![ξ, β] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : bil A (s • ξ + t • β) β = 0 := by rw [hst]; simp
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hξβ, mul_zero, zero_add] at h1
    have ht : t = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact h
      · exact absurd h hβ.ne
    subst ht
    simp only [zero_smul, add_zero, smul_eq_zero] at hst
    exact ⟨hst.resolve_right hξ, rfl⟩
  have hrange : Set.range ![ξ, β] = {ξ, β} := by
    ext; simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.mem_union,
      Set.mem_singleton_iff, Set.mem_insert_iff]
  let W := Submodule.span ℝ ({ξ, β} : Set (Fin (n + 1) → ℝ))
  have hW : Module.finrank ℝ W = 2 := by
    have := finrank_span_eq_card hind
    rw [hrange] at this
    simpa using this
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq S' W
  have hle' : Module.finrank ℝ ↥(S' ⊔ W) ≤ n + 1 := by
    have := Submodule.finrank_le (S' ⊔ W)
    simpa using this
  have hne : S' ⊓ W ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hsum
    omega
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨⟨y, hyS, rfl⟩, hzW⟩ := Submodule.mem_inf.1 hz
  have hy0 : y ≠ 0 := by rintro rfl; exact hz0 (map_zero e)
  have hpos : 0 < form A y y := hS.pos y hyS hy0
  rw [form_eq_bil] at hpos
  rw [Submodule.mem_span_pair] at hzW
  obtain ⟨a, b, hab⟩ := hzW
  have hy : ofLp y = a • ξ + b • β := by rw [hab]; rfl
  rw [hy] at hpos
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hξβ] at hpos
  rw [bil_symm hA.symm β ξ, hξβ] at hpos
  nlinarith [mul_nonneg (sq_nonneg a) (sub_nonneg.2 hle), mul_nonpos_of_nonneg_of_nonpos
    (sq_nonneg b) hβ.le]

theorem IsLorentzian.isUnit_det {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : IsLorentzian A) : IsUnit A.det :=
  isUnit_iff_ne_zero.2 hA.det_neg.ne

theorem IsLorentzian.inv_symm {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : IsLorentzian A) : A⁻¹ᵀ = A⁻¹ := by
  rw [transpose_nonsing_inv, hA.symm]

/-- `B_A(A⁻¹ξ, A⁻¹η) = B_{A⁻¹}(ξ, η)`. -/
theorem IsLorentzian.bil_inv_mulVec {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : IsLorentzian A) (ξ y : Fin (n + 1) → ℝ) :
    bil A (A⁻¹ *ᵥ ξ) y = ξ ⬝ᵥ y := by
  rw [bil_symm hA.symm, bil_apply, mulVec_mulVec, mul_nonsing_inv _ hA.isUnit_det, one_mulVec,
    dotProduct_comm]

theorem IsLorentzian.bil_inv_eq {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : IsLorentzian A) (ξ η : Fin (n + 1) → ℝ) :
    bil A (A⁻¹ *ᵥ ξ) (A⁻¹ *ᵥ η) = bil A⁻¹ ξ η := by
  rw [hA.bil_inv_mulVec, bil_apply]

/-- The inverse of a Lorentzian matrix, as a form on covectors, is of Lorentzian type. -/
theorem IsLorentzian.isLorentzForm_inv {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : IsLorentzian A) : IsLorentzForm (bil A⁻¹) := by
  refine ⟨bil_symm hA.inv_symm, fun β hβ ξ hξβ hξ => ?_⟩
  rw [← hA.bil_inv_eq] at hβ hξβ ⊢
  refine hA.isLorentzForm.pos _ hβ _ hξβ fun h => hξ ?_
  have := congrArg (A *ᵥ ·) h
  simpa [mulVec_mulVec, mul_nonsing_inv _ hA.isUnit_det] using this

/-- The covector `-g(Y, ·)` of the time orientation. -/
def timeCovector (g : MatrixField n) (Y : E n → E n) (x : E n) : Fin (n + 1) → ℝ :=
  -(g x *ᵥ ofLp (Y x))

theorem timeCovector_def (g : MatrixField n) (Y : E n → E n) (x : E n) :
    timeCovector g Y x =
      -(g x *ᵥ ofLp (Y x)) := by rfl

theorem form_neg_grad {g : MatrixField n} {x : E n} (hx : IsLorentzian (g x))
    (u v : E n → ℝ) :
    form (g x) (-grad g u x) (-grad g v x) = coform g x (d u x) (d v x) := by
  rw [form_eq_bil, coform_eq_bil, ofLp_neg, ofLp_neg, ofLp_grad, ofLp_grad]
  simp only [map_neg, LinearMap.neg_apply, neg_neg]
  exact hx.bil_inv_eq _ _

/-- The differential of a function whose negative gradient is future-directed timelike is a
timelike covector. -/
theorem coform_self_neg_of_future {g : MatrixField n} {Y : E n → E n} {x : E n}
    {ψ : E n → ℝ} (hL : IsLorentzian (g x)) (hψ : IsFutureTimelike g Y x (-grad g ψ x)) :
    coform g x (d ψ x) (d ψ x) < 0 := by
  have h1 := hψ.timelike
  rwa [form_neg_grad hL] at h1

theorem form_neg_grad_time {g : MatrixField n} {x : E n} (hx : IsLorentzian (g x))
    (u : E n → ℝ) (Y : E n → E n) :
    form (g x) (-grad g u x) (Y x) = coform g x (d u x) (timeCovector g Y x) := by
  rw [form_eq_bil, coform_eq_bil, ofLp_neg, ofLp_grad, map_neg, LinearMap.neg_apply,
    hx.bil_inv_mulVec, timeCovector, bil_apply, mulVec_neg, mulVec_mulVec,
    nonsing_inv_mul _ hx.isUnit_det, one_mulVec, dotProduct_neg]

theorem coform_timeCovector {g : MatrixField n} {x : E n} (hx : IsLorentzian (g x))
    (Y : E n → E n) :
    coform g x (timeCovector g Y x) (timeCovector g Y x) = form (g x) (Y x) (Y x) := by
  rw [coform_eq_bil, timeCovector, ← hx.bil_inv_eq, form_eq_bil, mulVec_neg, mulVec_mulVec,
    nonsing_inv_mul _ hx.isUnit_det, one_mulVec]
  simp only [map_neg, LinearMap.neg_apply, neg_neg]

end

end LorentzianCalderon
