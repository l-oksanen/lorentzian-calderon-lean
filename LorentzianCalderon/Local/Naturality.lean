module

public import LorentzianCalderon.Local.Comparison
public import LorentzianCalderon.Local.Piola

public section

/-!
# Naturality of the wave operator

If `g = Ψ^* g'` near `x`, i.e. `g = (DΨ)ᵀ (g' ∘ Ψ) DΨ`, and `DΨ(x)` is invertible, then
`□_g (v ∘ Ψ) = (□_{g'} v) ∘ Ψ` and `g(d(v₁ ∘ Ψ), d(v₂ ∘ Ψ)) = g'(dv₁, dv₂) ∘ Ψ` at `x`.
Consequently the coefficients `gbar` and `θbar` of the comparison vanish where `κ = 1`.

The proof writes the flux `√|det g| g⁻¹ d(v ∘ Ψ)` as `± adj(DΨ) (W ∘ Ψ)`, where
`W = √|det g'| g'⁻¹ dv` is the flux of `g'`, and uses the Piola identity.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Matrix Finset

variable {n : ℕ}

section Algebra

variable {ι : Type*} [Fintype ι]

theorem flux_algebra (X A J dW : ι → ι → ℝ) (W : ι → ℝ) (s : ℝ) :
    ∑ j, s * ∑ a, (X j a * W a + A j a * ∑ c, dW a c * J c j) =
      s * (∑ a, W a * ∑ j, X j a + ∑ a, ∑ c, dW a c * ∑ j, J c j * A j a) := by
  rw [← Finset.mul_sum]
  congr 1
  simp only [Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · refine (sum_comm₃ _).symm.trans ?_
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring

variable [DecidableEq ι]

theorem det_ne_zero_of_pullback {A J G : Matrix ι ι ℝ} (h : A = Jᵀ * G * J)
    (hA : A.det ≠ 0) : J.det ≠ 0 := by
  intro hJ
  apply hA
  rw [h, det_mul, hJ, mul_zero]

theorem mul_inv_pullback_mul_transpose {J : Matrix ι ι ℝ} (hJ : J.det ≠ 0)
    (G : Matrix ι ι ℝ) : J * (Jᵀ * G * J)⁻¹ * Jᵀ = G⁻¹ := by
  have hu : IsUnit J.det := hJ.isUnit
  have huT : IsUnit Jᵀ.det := by rwa [det_transpose]
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.mul_assoc, mul_nonsing_inv _ hu,
    Matrix.one_mul, Matrix.mul_assoc, nonsing_inv_mul _ huT, Matrix.mul_one]

/-- The flux of a pulled back metric. -/
theorem sqrt_abs_det_pullback_mul_sum {J : Matrix ι ι ℝ} (hJ : J.det ≠ 0) {s : ℝ}
    (hs : |J.det| = s * J.det) (G : Matrix ι ι ℝ) (p : ι → ℝ) (j : ι) :
    √|(Jᵀ * G * J).det| * ∑ k, (Jᵀ * G * J)⁻¹ j k * ∑ α, p α * J α k =
      s * ∑ a, J.adjugate j a * (√|G.det| * ∑ b, G⁻¹ a b * p b) := by
  have huT : IsUnit Jᵀ.det := by rw [det_transpose]; exact hJ.isUnit
  have hsq : √|(Jᵀ * G * J).det| = |J.det| * √|G.det| := by
    rw [det_mul, det_mul, det_transpose, show J.det * G.det * J.det = J.det * J.det * G.det by
      ring, abs_mul, abs_mul, Real.sqrt_mul (by positivity), Real.sqrt_mul_self (abs_nonneg _)]
  have hv : ∀ k, ∑ α, p α * J α k = (Jᵀ *ᵥ p) k := fun k => by
    simp [mulVec, dotProduct, mul_comm]
  have hM : ((Jᵀ * G * J)⁻¹ *ᵥ (Jᵀ *ᵥ p)) = J⁻¹ *ᵥ (G⁻¹ *ᵥ p) := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, mulVec_mulVec]
    simp only [Matrix.mul_assoc, nonsing_inv_mul _ huT, Matrix.mul_one]
    rw [← mulVec_mulVec]
  have h1 : ∑ k, (Jᵀ * G * J)⁻¹ j k * ∑ α, p α * J α k =
      ((Jᵀ * G * J)⁻¹ *ᵥ (Jᵀ *ᵥ p)) j := by
    simp only [hv]
    rfl
  rw [h1, hM, hsq, hs, Matrix.inv_def, Ring.inverse_eq_inv', smul_mulVec, Pi.smul_apply,
    smul_eq_mul]
  have h2 : (J.adjugate *ᵥ (G⁻¹ *ᵥ p)) j = ∑ a, J.adjugate j a * ∑ b, G⁻¹ a b * p b := rfl
  rw [h2, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  field_simp

end Algebra

variable {g g' : MatrixField n} {Ψ : E n → E n} {x : E n}

/-- Naturality of the wave operator under local isometries: if `g = Ψ^* g'` near `x` and
`DΨ(x)` is invertible, then `□_g (v ∘ Ψ) = (□_{g'} v) ∘ Ψ` at `x`. -/
theorem box_comp_of_pullback (hΨ : ContDiffAt ℝ 2 Ψ x) (hJ : (D Ψ x).det ≠ 0)
    (hg' : ∀ i j, DifferentiableAt ℝ (fun z => g' z i j) (Ψ x))
    (hdet' : (g' (Ψ x)).det ≠ 0)
    (hpull : ∀ᶠ y in 𝓝 x, g y = (D Ψ y)ᵀ * g' (Ψ y) * D Ψ y)
    {v : E n → ℝ} (hv : ContDiffAt ℝ 2 v (Ψ x)) :
    box g (v ∘ Ψ) x = box g' v (Ψ x) := by
  have h2 : (2 : ℕ∞ω) ≠ ∞ := by simp
  have hD := differentiableAt_D hΨ
  have hΨd : DifferentiableAt ℝ Ψ x := hΨ.differentiableAt (by simp)
  have hJc : ContinuousAt (fun y => (D Ψ y).det) x := (differentiableAt_det hD).continuousAt
  obtain ⟨s, hs⟩ : ∃ s : ℝ, ∀ᶠ y in 𝓝 x, |(D Ψ y).det| = s * (D Ψ y).det := by
    rcases hJ.lt_or_gt with hneg | hpos
    · refine ⟨-1, ?_⟩
      filter_upwards [hJc.eventually (gt_mem_nhds hneg)] with y hy
      rw [abs_of_neg hy]
      ring
    · refine ⟨1, ?_⟩
      filter_upwards [hJc.eventually (lt_mem_nhds hpos)] with y hy
      rw [abs_of_pos hy]
      ring
  have hW : ∀ a, DifferentiableAt ℝ
      (fun z => √|(g' z).det| * ∑ b, (g' z)⁻¹ a b * d v z b) (Ψ x) := fun a =>
    (differentiableAt_sqrt_abs_det hg' hdet').mul (DifferentiableAt.fun_sum fun b _ =>
      (differentiableAt_inv hg' hdet' a b).mul (differentiableAt_d hv b))
  have hF : ∀ j, (fun y => √|(g y).det| * ∑ k, (g y)⁻¹ j k * d (v ∘ Ψ) y k) =ᶠ[𝓝 x]
      fun y => s * ∑ a, (D Ψ y).adjugate j a *
        (√|(g' (Ψ y)).det| * ∑ b, (g' (Ψ y))⁻¹ a b * d v (Ψ y) b) := by
    intro j
    filter_upwards [hpull, hs, hJc.eventually_ne hJ, hΨ.eventually h2,
      hΨ.continuousAt.eventually (hv.eventually h2)] with y hy hsy hJy hΨy hvy
    have hdc : ∀ k, d (v ∘ Ψ) y k = ∑ α, d v (Ψ y) α * D Ψ y α k := fun k => by
      rw [show d (v ∘ Ψ) y k = _ from d_comp (hvy.differentiableAt (by simp))
        (hΨy.differentiableAt (by simp)) k]
      simp only [d_coord_comp (hΨy.differentiableAt (by simp))]
    simp only [hdc, hy]
    exact sqrt_abs_det_pullback_mul_sum hJy hsy _ _ j
  have hdF : ∀ j, d (fun y => √|(g y).det| * ∑ k, (g y)⁻¹ j k * d (v ∘ Ψ) y k) x j =
      s * ∑ a, (d (fun y => (D Ψ y).adjugate j a) x j *
          (√|(g' (Ψ x)).det| * ∑ b, (g' (Ψ x))⁻¹ a b * d v (Ψ x) b) +
        (D Ψ x).adjugate j a * ∑ c, d (fun z => √|(g' z).det| *
          ∑ b, (g' z)⁻¹ a b * d v z b) (Ψ x) c * D Ψ x c j) := by
    intro j
    have hadj : ∀ a, DifferentiableAt ℝ (fun y => (D Ψ y).adjugate j a) x := fun a =>
      differentiableAt_adjugate hD j a
    have hWΨ : ∀ a, DifferentiableAt ℝ (fun y => √|(g' (Ψ y)).det| *
        ∑ b, (g' (Ψ y))⁻¹ a b * d v (Ψ y) b) x := fun a => (hW a).comp x hΨd
    rw [d_congr (hF j), d_const_mul (u := fun y => ∑ a, (D Ψ y).adjugate j a *
        (√|(g' (Ψ y)).det| * ∑ b, (g' (Ψ y))⁻¹ a b * d v (Ψ y) b))
        (DifferentiableAt.fun_sum fun a _ => (hadj a).mul (hWΨ a)),
      d_sum (u := fun a y => (D Ψ y).adjugate j a *
        (√|(g' (Ψ y)).det| * ∑ b, (g' (Ψ y))⁻¹ a b * d v (Ψ y) b))
        fun a _ => (hadj a).mul (hWΨ a)]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [d_mul (hadj a) (hWΨ a)]
    congr 2
    rw [d_comp (v := fun z => √|(g' z).det| * ∑ b, (g' z)⁻¹ a b * d v z b) (hW a) hΨd]
    simp only [d_coord_comp hΨd]
  have hsum : ∑ j, d (fun y => √|(g y).det| * ∑ k, (g y)⁻¹ j k * d (v ∘ Ψ) y k) x j =
      s * (D Ψ x).det * ∑ a, d (fun z => √|(g' z).det| *
        ∑ b, (g' z)⁻¹ a b * d v z b) (Ψ x) a := by
    simp only [hdF]
    refine (flux_algebra (fun j a => d (fun y => (D Ψ y).adjugate j a) x j)
      (fun j a => (D Ψ x).adjugate j a) (D Ψ x)
      (fun a c => d (fun z => √|(g' z).det| * ∑ b, (g' z)⁻¹ a b * d v z b) (Ψ x) c)
      (fun a => √|(g' (Ψ x)).det| * ∑ b, (g' (Ψ x))⁻¹ a b * d v (Ψ x) b) s).trans ?_
    simp only [sum_d_adjugate_D hΨ, mul_zero, Finset.sum_const_zero, zero_add]
    have hJA : ∀ c a, ∑ j, D Ψ x c j * (D Ψ x).adjugate j a =
        (D Ψ x).det * if c = a then 1 else 0 := fun c a => by
      have := congrFun (congrFun (mul_adjugate (D Ψ x)) c) a
      rw [mul_apply] at this
      rw [this, Matrix.smul_apply, one_apply, smul_eq_mul]
    simp only [hJA, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => by ring
  have hsqrt : √|(g x).det| = s * (D Ψ x).det * √|(g' (Ψ x)).det| := by
    rw [hpull.self_of_nhds, det_mul, det_mul, det_transpose, ← hs.self_of_nhds,
      show (D Ψ x).det * (g' (Ψ x)).det * (D Ψ x).det =
        (D Ψ x).det * (D Ψ x).det * (g' (Ψ x)).det by ring,
      abs_mul, abs_mul, Real.sqrt_mul (by positivity), Real.sqrt_mul_self (abs_nonneg _)]
  have hsJ : s * (D Ψ x).det ≠ 0 := by
    rw [← hs.self_of_nhds]
    exact abs_ne_zero.mpr hJ
  have hs0 : s ≠ 0 := left_ne_zero_of_mul hsJ
  rw [box_def, hsum, hsqrt, box_def]
  field_simp

/-- Under a local isometry with `κ = 1`, the second-order coefficients of the comparison
vanish. -/
theorem gbar_eq_zero (hΨ : DifferentiableAt ℝ Ψ x) (hJ : (D Ψ x).det ≠ 0)
    (hpull : g x = (D Ψ x)ᵀ * g' (Ψ x) * D Ψ x) {κ : E n → ℝ} (hκ : κ x = 1)
    (α β : Fin (n + 1)) : gbar g g' Ψ κ x α β = 0 := by
  have h := congrFun (congrFun (mul_inv_pullback_mul_transpose hJ (g' (Ψ x))) α) β
  rw [← hpull] at h
  simp only [mul_apply, transpose_apply] at h
  simp only [gbar_def, hκ, one_mul, d_coord_comp hΨ, sub_eq_zero]
  rw [← h]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- Under a local isometry with `κ = 1`, the first-order coefficients of the comparison
vanish. -/
theorem θbar_eq_zero (hΨ : ContDiffAt ℝ 2 Ψ x) (hJ : (D Ψ x).det ≠ 0)
    (hg' : ∀ i j, DifferentiableAt ℝ (fun z => g' z i j) (Ψ x))
    (hdet' : (g' (Ψ x)).det ≠ 0)
    (hpull : ∀ᶠ y in 𝓝 x, g y = (D Ψ y)ᵀ * g' (Ψ y) * D Ψ y) {κ : E n → ℝ} (hκ : κ x = 1)
    (k : Fin (n + 1)) : θbar g g' Ψ κ x k = 0 := by
  rw [θbar_def, hκ, one_mul, ← box_comp_of_pullback hΨ hJ hg' hdet' hpull
    (contDiffAt_coord (Ψ := fun y => y) contDiffAt_id k)]
  exact neg_add_cancel _

/-- Naturality of the inner product of differentials under local isometries. -/
theorem cometric_comp_of_pullback (hΨ : DifferentiableAt ℝ Ψ x) (hJ : (D Ψ x).det ≠ 0)
    (hpull : g x = (D Ψ x)ᵀ * g' (Ψ x) * D Ψ x) {v₁ v₂ : E n → ℝ}
    (hv₁ : DifferentiableAt ℝ v₁ (Ψ x)) (hv₂ : DifferentiableAt ℝ v₂ (Ψ x)) :
    ∑ j, ∑ k, (g x)⁻¹ j k * d (v₁ ∘ Ψ) x j * d (v₂ ∘ Ψ) x k =
      ∑ α, ∑ β, (g' (Ψ x))⁻¹ α β * d v₁ (Ψ x) α * d v₂ (Ψ x) β := by
  have := cometric_comparison (g := g) (g' := g') hΨ hv₁ hv₂ fun _ => 1
  simp only [gbar_eq_zero (κ := fun _ => 1) hΨ hJ hpull rfl, zero_mul, Finset.sum_const_zero,
    one_mul] at this
  linarith

end

end LorentzianCalderon
