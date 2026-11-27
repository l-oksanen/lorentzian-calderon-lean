module

public import Mathlib

public section

/-!
# Pointwise algebra of the energy-momentum tensor

For a symmetric bilinear form `B` of Lorentzian type (positive definite on the orthogonal
complement of every timelike vector), we study the energy-momentum tensor of a function with
differential `ξ` and value `w₀`, with mass term `λ`,
`T(α, β) = B(α, ξ) B(β, ξ) - ½ B(α, β) (B(ξ, ξ) + λ w₀²)`.

In the application `B` is the inner product `g^{jk}` of covectors at a point, and `α, β` are
covectors; the corresponding vectors are `-B♯α`, `-B♯β` (minus the gradients), and `T(α, β)` is
the tensor evaluated on these vectors.
-/

namespace LorentzianCalderon

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

/-- `B` is symmetric and positive definite on the orthogonal complement of every timelike
vector, as a form of Lorentzian signature is. -/
structure IsLorentzForm (B : LinearMap.BilinForm ℝ M) : Prop where
  symm : ∀ x y, B x y = B y x
  pos : ∀ β, B β β < 0 → ∀ ξ, B ξ β = 0 → ξ ≠ 0 → 0 < B ξ ξ

/-- The energy-momentum tensor `T(α, β)` of a function with differential `ξ` and value `w₀`,
with mass term `lam`. -/
noncomputable def emTensor (B : LinearMap.BilinForm ℝ M) (lam w₀ : ℝ) (ξ α β : M) : ℝ :=
  B α ξ * B β ξ - 1 / 2 * B α β * (B ξ ξ + lam * w₀ ^ 2)

theorem emTensor_def (B : LinearMap.BilinForm ℝ M) (lam w₀ : ℝ) (ξ α β : M) :
    emTensor B lam w₀ ξ α β =
      B α ξ * B β ξ - 1 / 2 * B α β * (B ξ ξ + lam * w₀ ^ 2) := by rfl

omit [AddCommGroup M] [Module ℝ M] in
theorem apply_sub_smul [AddCommGroup M] [Module ℝ M] (B : LinearMap.BilinForm ℝ M) (a b : ℝ)
    (x y z : M) : B (a • x - b • y) z = a * B x z - b * B y z := by
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]

namespace IsLorentzForm

variable {B : LinearMap.BilinForm ℝ M} (hB : IsLorentzForm B)
include hB

theorem nonneg_of_orth {β ξ : M} (hβ : B β β < 0) (h : B ξ β = 0) : 0 ≤ B ξ ξ := by
  by_cases h0 : ξ = 0
  · simp [h0]
  · exact (hB.pos β hβ ξ h h0).le

theorem eq_zero_of_orth {β ξ : M} (hβ : B β β < 0) (h : B ξ β = 0) (h2 : B ξ ξ ≤ 0) :
    ξ = 0 := by
  by_contra h0
  exact absurd (hB.pos β hβ ξ h h0) (not_lt.2 h2)

theorem apply_sub_smul_self (a b : ℝ) (x y : M) :
    B (a • x - b • y) (a • x - b • y) = a ^ 2 * B x x - 2 * a * b * B x y + b ^ 2 * B y y := by
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hB.symm y x]
  ring

/-- Two future causal vectors, one of them timelike, have negative inner product. -/
theorem neg_of_sameCone {η α β : M} (hη : B η η < 0) (hα : B α α ≤ 0) (hαη : B α η < 0)
    (hβ : B β β < 0) (hβη : B β η < 0) : B α β < 0 := by
  by_contra hαβ
  push Not at hαβ
  have horth : B (B α η • β - B β η • α) η = 0 := by
    rw [apply_sub_smul]; ring
  have h := hB.nonneg_of_orth hη horth
  rw [hB.apply_sub_smul_self, hB.symm β α] at h
  have h2 : B α η ^ 2 * B β β < 0 := mul_neg_of_pos_of_neg (pow_pos_of_ne_zero hαη.ne) hβ
  have h3 : 0 ≤ B α η * B β η * B α β := mul_nonneg (mul_pos_of_neg_of_neg hαη hβη).le hαβ
  have h4 : B β η ^ 2 * B α α ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hα
  linarith
where
  pow_pos_of_ne_zero {x : ℝ} (hx : x ≠ 0) : 0 < x ^ 2 := by positivity

/-- The dominant energy condition: `T(α, β) ≥ 0` for future causal `α` and future timelike
`β` (here: `B(α, α) ≤ 0`, `B(β, β) < 0`, `B(α, β) ≤ 0`). -/
theorem emTensor_nonneg {α β : M} (hβ : B β β < 0) (hα : B α α ≤ 0) (hαβ : B α β ≤ 0)
    {lam : ℝ} (hlam : 0 ≤ lam) (w₀ : ℝ) (ξ : M) : 0 ≤ emTensor B lam w₀ ξ α β := by
  unfold emTensor
  have hmass : 0 ≤ -(1 / 2 * B α β * (lam * w₀ ^ 2)) := by
    have := mul_nonneg hlam (sq_nonneg w₀)
    nlinarith
  rcases hαβ.lt_or_eq with hlt | heq
  · have horth : B (B α β • ξ - B ξ β • α) β = 0 := by
      rw [apply_sub_smul]; ring
    have h := hB.nonneg_of_orth hβ horth
    rw [hB.apply_sub_smul_self, hB.symm ξ α] at h
    have h3 : B ξ β ^ 2 * B α α ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hα
    have h4 : 0 ≤ B α β * (B α ξ * B β ξ - 1 / 2 * B α β * B ξ ξ) * (-2) := by
      rw [hB.symm β ξ]; nlinarith
    have h5 : 0 ≤ B α ξ * B β ξ - 1 / 2 * B α β * B ξ ξ := by
      have : 0 < B α β * (-2) := by linarith
      nlinarith
    nlinarith
  · have hα0 : α = 0 := hB.eq_zero_of_orth hβ heq (by
      have := hB.nonneg_of_orth hβ heq; linarith)
    simp [hα0]

/-- The flux through a null hypersurface: for null `α` and future timelike `β` with
`k = -B(α, β) > 0` and `m² = -B(β, β)`, `T(α, β) ≥ (m² / 2k) B(α, ξ)² + (k / 2) λ w₀²`. -/
theorem emTensor_null_ge {α β : M} (hβ : B β β < 0) (hα : B α α = 0) (hαβ : B α β < 0)
    (lam w₀ : ℝ) (ξ : M) :
    -B β β / (2 * -B α β) * B α ξ ^ 2 + -B α β / 2 * (lam * w₀ ^ 2) ≤
      emTensor B lam w₀ ξ α β := by
  have sαξ := hB.symm α ξ
  have sβξ := hB.symm β ξ
  have sαβ := hB.symm α β
  have hv : B ((-B α β) • ξ - (-B ξ β) • α) β = 0 := by
    rw [apply_sub_smul]; ring
  have ha : B ((-B β β) • α - (-B α β) • β) β = 0 := by
    rw [apply_sub_smul]; ring
  set v := (-B α β) • ξ - (-B ξ β) • α
  set a := (-B β β) • α - (-B α β) • β
  have key : ∀ t : ℝ, 0 ≤ B v v * (t * t) + (-2 * B v a) * t + B a a := by
    intro t
    have hort : B (t • v - (1 : ℝ) • a) β = 0 := by
      rw [apply_sub_smul, hv, ha]; ring
    have h := hB.nonneg_of_orth hβ hort
    rw [hB.apply_sub_smul_self] at h
    linarith
  have hd := discrim_le_zero key
  unfold discrim at hd
  have hva : B v a = B β β * B α β * B α ξ := by
    simp only [v, a, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, hα]
    linear_combination (-(B β β * B α β)) * sαξ
  have haa : B a a = -(B β β * B α β ^ 2) := by
    simp only [a, hB.apply_sub_smul_self, hα]
    ring
  have hvv : B v v = B α β ^ 2 * B ξ ξ - 2 * B α β * B ξ β * B α ξ := by
    simp only [v, hB.apply_sub_smul_self, hα]
    linear_combination (2 * B α β * B ξ β) * sαξ
  rw [hva, haa, hvv] at hd
  have hk0 : 0 < -B α β := by linarith
  have hm0 : 0 < -B β β := by linarith
  have h1 : -B β β * B α ξ ^ 2 ≤ B α β ^ 2 * B ξ ξ - 2 * B α β * B ξ β * B α ξ := by
    have : 0 < -B β β * B α β ^ 2 := mul_pos hm0 (by nlinarith)
    nlinarith
  unfold emTensor
  rw [sβξ]
  have e : -B β β / (2 * -B α β) * B α ξ ^ 2 =
      (-B β β * B α ξ ^ 2) / (2 * -B α β) := by ring
  rw [e, div_eq_mul_inv]
  have hinv : 0 < (2 * -B α β)⁻¹ := by positivity
  have : -B β β * B α ξ ^ 2 * (2 * -B α β)⁻¹ ≤
      (B α β ^ 2 * B ξ ξ - 2 * B α β * B ξ β * B α ξ) * (2 * -B α β)⁻¹ :=
    mul_le_mul_of_nonneg_right h1 hinv.le
  have e2 : (B α β ^ 2 * B ξ ξ - 2 * B α β * B ξ β * B α ξ) * (2 * -B α β)⁻¹ =
      B α ξ * B ξ β - 1 / 2 * B α β * B ξ ξ := by
    have hne : B α β ≠ 0 := hαβ.ne
    field_simp
    ring
  rw [e2] at this
  linarith

/-- `T(β, β)` is positive definite in `ξ` for timelike `β` (without mass term). -/
theorem emTensor_self_pos {β : M} (hβ : B β β < 0) {ξ : M} (hξ : ξ ≠ 0) :
    0 < emTensor B 0 0 ξ β β := by
  unfold emTensor
  simp only [zero_mul, add_zero]
  have horth : B (B β β • ξ - B ξ β • β) β = 0 := by
    rw [apply_sub_smul]; ring
  have h := hB.nonneg_of_orth hβ horth
  rw [hB.apply_sub_smul_self] at h
  have h1 : 0 ≤ B ξ β ^ 2 - B β β * B ξ ξ := by
    have : B β β * (B β β * B ξ ξ - B ξ β ^ 2) ≥ 0 := by nlinarith
    nlinarith
  rw [hB.symm β ξ]
  rcases eq_or_ne (B ξ β) 0 with h0 | h0
  · have := hB.pos β hβ ξ h0 hξ
    rw [h0]; nlinarith
  · have : 0 < B ξ β ^ 2 := by positivity
    nlinarith

end IsLorentzForm

end LorentzianCalderon
