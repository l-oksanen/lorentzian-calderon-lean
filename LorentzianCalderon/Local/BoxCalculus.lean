module

public import LorentzianCalderon.Local.Differential
public import LorentzianCalderon.Local.MatrixCalculus

public section

/-!
# The wave operator in non-divergence form

At a point where the metric is differentiable,
`□_g u = -g^{jk} ∂ⱼ∂ₖu + b^k ∂ₖu` with `b^k = □_g x^k`, and the chain rule
`□_g (v ∘ Ψ) = -g(dΨ^α, dΨ^β) (∂_α∂_β v) ∘ Ψ + (□_g Ψ^k) (∂ₖv) ∘ Ψ`.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Finset

variable {n : ℕ}

theorem sum_comm₄ {ι κ μ ν M : Type*} [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ν]
    [AddCommMonoid M] (f : ι → κ → μ → ν → M) :
    ∑ a, ∑ b, ∑ c, ∑ e, f a b c e = ∑ c, ∑ e, ∑ a, ∑ b, f a b c e := by
  calc _ = ∑ a, ∑ c, ∑ e, ∑ b, f a b c e := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = _ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => Finset.sum_comm

theorem sum_comm₃ {ι κ μ M : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    [AddCommMonoid M] (f : ι → κ → μ → M) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ a, ∑ b, f a b c := by
  calc _ = ∑ a, ∑ c, ∑ b, f a b c := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem box_comp_algebra {ι : Type*} [Fintype ι] (G V : ι → ι → ℝ) (P : ι → ι → ℝ)
    (Q : ι → ι → ι → ℝ) (w b : ι → ℝ) :
    -∑ j, ∑ k, G j k * (∑ α, ∑ β, V α β * P α j * P β k + ∑ α, w α * Q α j k) +
        ∑ k, b k * ∑ α, w α * P α k =
      -∑ α, ∑ β, (∑ j, ∑ k, G j k * P α j * P β k) * V α β +
        ∑ α, (-∑ j, ∑ k, G j k * Q α j k + ∑ k, b k * P α k) * w α := by
  have e1 : ∑ j, ∑ k, G j k * ∑ α, ∑ β, V α β * P α j * P β k =
      ∑ α, ∑ β, (∑ j, ∑ k, G j k * P α j * P β k) * V α β := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [sum_comm₄]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have e2 : ∑ j, ∑ k, G j k * ∑ α, w α * Q α j k = ∑ α, (∑ j, ∑ k, G j k * Q α j k) * w α := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [sum_comm₃]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring
  have e3 : ∑ k, b k * ∑ α, w α * P α k = ∑ α, (∑ k, b k * P α k) * w α := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  simp only [mul_add, add_mul, Finset.sum_add_distrib, neg_mul, Finset.sum_neg_distrib]
  linarith

variable {g : MatrixField n} {x : E n}

theorem differentiableAt_sqrt_abs_det_mul_inv
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x) (hdet : (g x).det ≠ 0)
    (j k : Fin (n + 1)) :
    DifferentiableAt ℝ (fun y => √|(g y).det| * (g y)⁻¹ j k) x :=
  (differentiableAt_sqrt_abs_det hg hdet).mul (differentiableAt_inv hg hdet j k)

theorem box_eq_sub_drift (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hdet : (g x).det ≠ 0) {u : E n → ℝ} (hu : ContDiffAt ℝ 2 u x) :
    box g u x = -∑ j, ∑ k, (g x)⁻¹ j k * d2 u x j k -
      (√|(g x).det|)⁻¹ *
        ∑ k, (∑ j, d (fun y => √|(g y).det| * (g y)⁻¹ j k) x j) * d u x k := by
  have hs : √|(g x).det| ≠ 0 := by simpa using hdet
  have key : ∀ j, d (fun y => √|(g y).det| * ∑ k, (g y)⁻¹ j k * d u y k) x j =
      ∑ k, (d (fun y => √|(g y).det| * (g y)⁻¹ j k) x j * d u x k +
        √|(g x).det| * ((g x)⁻¹ j k * d2 u x j k)) := by
    intro j
    have : (fun y => √|(g y).det| * ∑ k, (g y)⁻¹ j k * d u y k) =
        fun y => ∑ k, √|(g y).det| * (g y)⁻¹ j k * d u y k := by
      ext y
      rw [Finset.mul_sum]
      simp only [mul_assoc]
    rw [this, d_sum (u := fun k y => √|(g y).det| * (g y)⁻¹ j k * d u y k) fun k _ => (differentiableAt_sqrt_abs_det_mul_inv hg hdet j k).mul
      (differentiableAt_d hu k)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [d_mul (differentiableAt_sqrt_abs_det_mul_inv hg hdet j k) (differentiableAt_d hu k)]
    simp only [d2_def]
    ring
  have hsum : ∑ j, d (fun y => √|(g y).det| * ∑ k, (g y)⁻¹ j k * d u y k) x j =
      ∑ k, (∑ j, d (fun y => √|(g y).det| * (g y)⁻¹ j k) x j) * d u x k +
        √|(g x).det| * ∑ j, ∑ k, (g x)⁻¹ j k * d2 u x j k := by
    rw [Finset.sum_congr rfl fun j _ => key j]
    simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [box_def, hsum]
  field_simp
  ring

/-- The first-order coefficients of `□_g` are `b^k = □_g x^k`. -/
theorem box_coord (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hdet : (g x).det ≠ 0) (m : Fin (n + 1)) :
    box g (fun y => y m) x =
      -(√|(g x).det|)⁻¹ * ∑ j, d (fun y => √|(g y).det| * (g y)⁻¹ j m) x j := by
  rw [box_eq_sub_drift hg hdet (contDiffAt_coord (Ψ := fun y => y) contDiffAt_id m)]
  simp [d2_coord, d_coord]

/-- The wave operator in non-divergence form, `□_g u = -g^{jk} ∂ⱼ∂ₖu + (□_g x^k) ∂ₖu`. -/
theorem box_eq (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hdet : (g x).det ≠ 0) {u : E n → ℝ} (hu : ContDiffAt ℝ 2 u x) :
    box g u x = -∑ j, ∑ k, (g x)⁻¹ j k * d2 u x j k +
      ∑ k, box g (fun y => y k) x * d u x k := by
  rw [box_eq_sub_drift hg hdet hu]
  simp only [box_coord hg hdet, Finset.mul_sum, Finset.sum_mul]
  rw [sub_eq_add_neg]
  congr 1
  simp only [neg_mul, mul_assoc, Finset.sum_neg_distrib]

/-- The chain rule for second derivatives. -/
theorem d2_comp {v : E n → ℝ} {Ψ : E n → E n} (hv : ContDiffAt ℝ 2 v (Ψ x))
    (hΨ : ContDiffAt ℝ 2 Ψ x) (j k : Fin (n + 1)) :
    d2 (v ∘ Ψ) x j k =
      ∑ α, ∑ β, d2 v (Ψ x) α β * d (fun y => Ψ y α) x j * d (fun y => Ψ y β) x k +
        ∑ α, d v (Ψ x) α * d2 (fun y => Ψ y α) x j k := by
  have h2 : (2 : ℕ∞ω) ≠ ∞ := by simp
  have hΨd : DifferentiableAt ℝ Ψ x := hΨ.differentiableAt (by simp)
  have hev : (fun y => d (v ∘ Ψ) y k) =ᶠ[𝓝 x]
      fun y => ∑ α, d v (Ψ y) α * d (fun z => Ψ z α) y k := by
    filter_upwards [hΨ.continuousAt.eventually (hv.eventually h2), hΨ.eventually h2]
      with y hvy hΨy
    exact d_comp (hvy.differentiableAt (by simp)) (hΨy.differentiableAt (by simp)) k
  have hdv : ∀ α, DifferentiableAt ℝ (fun y => d v (Ψ y) α) x := fun α =>
    (differentiableAt_d hv α).comp x hΨd
  have hdΨ : ∀ α, DifferentiableAt ℝ (fun y => d (fun z => Ψ z α) y k) x := fun α =>
    differentiableAt_d (contDiffAt_coord hΨ α) k
  rw [d2_def, d_congr hev, d_sum (u := fun α y => d v (Ψ y) α * d (fun z => Ψ z α) y k)
    fun α _ => (hdv α).mul (hdΨ α)]
  simp only [d_mul (hdv _) (hdΨ _), Finset.sum_add_distrib]
  congr 1
  · have : ∀ α, d (fun y => d v (Ψ y) α) x j =
        ∑ β, d2 v (Ψ x) β α * d (fun y => Ψ y β) x j := fun α => by
      simpa only [d2_def] using d_comp (v := fun z => d v z α) (differentiableAt_d hv α) hΨd j
    simp only [this, Finset.sum_mul]
    rw [Finset.sum_comm]
  · simp only [d2_def]

/-- The chain rule for the wave operator. -/
theorem box_comp (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hdet : (g x).det ≠ 0) {v : E n → ℝ} {Ψ : E n → E n} (hv : ContDiffAt ℝ 2 v (Ψ x))
    (hΨ : ContDiffAt ℝ 2 Ψ x) :
    box g (v ∘ Ψ) x =
      -∑ α, ∑ β, (∑ j, ∑ k, (g x)⁻¹ j k * d (fun y => Ψ y α) x j *
          d (fun y => Ψ y β) x k) * d2 v (Ψ x) α β +
        ∑ k, box g (fun y => Ψ y k) x * d v (Ψ x) k := by
  have hΨd : DifferentiableAt ℝ Ψ x := hΨ.differentiableAt (by simp)
  rw [box_eq hg hdet (hv.comp x hΨ)]
  simp only [d2_comp hv hΨ, box_eq hg hdet (contDiffAt_coord hΨ _)]
  have h1 : ∀ k, d (v ∘ Ψ) x k = ∑ α, d v (Ψ x) α * d (fun y => Ψ y α) x k := fun k =>
    d_comp (hv.differentiableAt (by simp)) hΨd k
  simp only [h1]
  exact box_comp_algebra (fun j k => (g x)⁻¹ j k) (d2 v (Ψ x))
    (fun α j => d (fun y => Ψ y α) x j) (fun α j k => d2 (fun y => Ψ y α) x j k) (d v (Ψ x))
    (fun k => box g (fun y => y k) x)

end

end LorentzianCalderon
