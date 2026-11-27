module

public import LorentzianCalderon.Local.Energy.Calculus

public section

/-!
# The divergence identity for the weighted energy current

For a metric with inverse `G = g⁻¹` and volume density `ρ = √|det g|`, a temporal function `ψ`
with `X = -grad ψ`, and a function `w`, the weighted current is
`Pʲ = e^{2σψ} (ρ Gʲᵏ ∂ₖw · Xw - ½ ρ Xʲ (G(dw, dw) + λ w²))`, i.e. `ρ` times the current
`e^{2σψ} T^j_b X^b` of the blueprint. Its Euclidean divergence is
`∂ⱼPʲ = e^{2σψ} (-2σ ρ T(X, X) + Xw ∂ⱼ(ρ Gʲᵏ ∂ₖw) - ρ λ w Xw + R)`, where the remainder `R`
does not involve second derivatives of `w`. Here the second derivatives of `w` cancel by the
symmetry of the Hessian.

The identity is proved for abstract coefficient functions (`G`, `ρ`, and the components `β`, `ξ`
of `dψ`, `dw`), which keeps the expressions manageable.
-/

namespace LorentzianCalderon

noncomputable section
open Set

variable {n : ℕ}

namespace Current

variable (ρ : E n → ℝ) (G : Fin (n + 1) → Fin (n + 1) → E n → ℝ)
  (β ξ : Fin (n + 1) → E n → ℝ) (ψ w : E n → ℝ) (σ lam : ℝ)

/-- The quadratic form `G(u, v)` at `y`. -/
def qf (u v : Fin (n + 1) → E n → ℝ) (y : E n) : ℝ := ∑ c, ∑ e, G c e y * u c y * v e y

theorem qf_def (u v : Fin (n + 1) → E n → ℝ) (y : E n) :
    qf G u v y =
      ∑ c, ∑ e, G c e y * u c y * v e y := by rfl

/-- The components of `X = -G β`. -/
def X (b : Fin (n + 1)) (y : E n) : ℝ := -∑ c, G b c y * β c y

theorem X_def (b : Fin (n + 1)) (y : E n) :
    X G β b y =
      -∑ c, G b c y * β c y := by rfl

/-- `X w = ξ(X)`. -/
def Xw (y : E n) : ℝ := ∑ b, X G β b y * ξ b y

theorem Xw_def (y : E n) :
    Xw G β ξ y =
      ∑ b, X G β b y * ξ b y := by rfl

/-- The flux `ρ Gʲᵏ ξₖ`. -/
def flux (j : Fin (n + 1)) (y : E n) : ℝ := ρ y * ∑ k, G j k y * ξ k y

theorem flux_def (j : Fin (n + 1)) (y : E n) :
    flux ρ G ξ j y =
      ρ y * ∑ k, G j k y * ξ k y := by rfl

/-- `G(ξ, ξ) + λ w²`. -/
def q (y : E n) : ℝ := qf G ξ ξ y + lam * w y ^ 2

theorem q_def (y : E n) :
    q G ξ w lam y =
      qf G ξ ξ y + lam * w y ^ 2 := by rfl

/-- The weighted current. -/
def P (j : Fin (n + 1)) (y : E n) : ℝ :=
  Real.exp (2 * σ * ψ y) * (flux ρ G ξ j y * Xw G β ξ y -
    1 / 2 * (ρ y * X G β j y) * q G ξ w lam y)

theorem P_def (j : Fin (n + 1)) (y : E n) :
    P ρ G β ξ ψ w σ lam j y =
      Real.exp (2 * σ * ψ y) * (flux ρ G ξ j y * Xw G β ξ y -
        1 / 2 * (ρ y * X G β j y) * q G ξ w lam y) := by rfl

/-- The remainder in the divergence identity. -/
def R (x : E n) : ℝ :=
  ∑ j, flux ρ G ξ j x * ∑ b, d (X G β b) x j * ξ b x -
    1 / 2 * (∑ j, d (fun y => ρ y * X G β j y) x j) * q G ξ w lam x -
    1 / 2 * ∑ j, (ρ x * X G β j x) * ∑ c, ∑ e, d (G c e) x j * ξ c x * ξ e x

theorem R_def (x : E n) :
    R ρ G β ξ w lam x =
      ∑ j, flux ρ G ξ j x * ∑ b, d (X G β b) x j * ξ b x -
        1 / 2 * (∑ j, d (fun y => ρ y * X G β j y) x j) * q G ξ w lam x -
        1 / 2 * ∑ j, (ρ x * X G β j x) * ∑ c, ∑ e, d (G c e) x j * ξ c x * ξ e x := by rfl

/-- `T(X, X)` for the tensor with mass term `lam`. -/
def TXX (x : E n) : ℝ :=
  qf G β ξ x * qf G β ξ x - 1 / 2 * qf G β β x * q G ξ w lam x

theorem TXX_def (x : E n) :
    TXX G β ξ w lam x =
      qf G β ξ x * qf G β ξ x - 1 / 2 * qf G β β x * q G ξ w lam x := by rfl

variable {ρ G β ξ ψ w} {x : E n}

theorem Xw_eq (hG : ∀ c e, G c e x = G e c x) : Xw G β ξ x = -qf G β ξ x := by
  simp only [Xw, X, qf, neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hG]

theorem sum_beta_flux : ∑ j, β j x * flux ρ G ξ j x = ρ x * qf G β ξ x := by
  simp only [flux, qf, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem sum_beta_X : ∑ j, β j x * X G β j x = -qf G β β x := by
  simp only [X, qf, Finset.mul_sum, mul_neg, Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem sum_X_xi : ∑ j, ρ x * X G β j x * ξ j x = ρ x * Xw G β ξ x := by
  simp only [Xw, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The cancellation of the second derivatives `H b j = ∂ⱼξ_b`. -/
theorem hessian_cancel (hG : ∀ c e, G c e x = G e c x) (H : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hH : ∀ b j, H b j = H j b) :
    ∑ j, flux ρ G ξ j x * ∑ b, X G β b x * H b j =
      1 / 2 * ∑ j, (ρ x * X G β j x) *
        ∑ c, ∑ e, (G c e x * H c j * ξ e x + G c e x * ξ c x * H e j) := by
  have h1 : ∑ j, flux ρ G ξ j x * ∑ b, X G β b x * H b j =
      ∑ b, ∑ j, ∑ k, ρ x * X G β b x * G j k x * H j b * ξ k x := by
    simp only [flux, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    rw [hH b j]; ring
  have h2 : ∑ j, (ρ x * X G β j x) * ∑ c, ∑ e, G c e x * ξ c x * H e j =
      ∑ b, ∑ j, ∑ k, ρ x * X G β b x * G j k x * H j b * ξ k x := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hG k j]; ring
  have h3 : ∑ j, (ρ x * X G β j x) * ∑ c, ∑ e, G c e x * H c j * ξ e x =
      ∑ b, ∑ j, ∑ k, ρ x * X G β b x * G j k x * H j b * ξ k x := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    ring
  have h4 : ∑ j, (ρ x * X G β j x) *
        ∑ c, ∑ e, (G c e x * H c j * ξ e x + G c e x * ξ c x * H e j) =
      ∑ j, (ρ x * X G β j x) * ∑ c, ∑ e, G c e x * H c j * ξ e x +
        ∑ j, (ρ x * X G β j x) * ∑ c, ∑ e, G c e x * ξ c x * H e j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_add_distrib]
  rw [h4, h1, h2, h3]
  ring

/-- The divergence identity, at a point where the coefficients are differentiable, `ξ` and `β`
are the components of `dw` and `dψ`, and the Hessian of `w` is symmetric. -/
theorem div_P (hρ : DifferentiableAt ℝ ρ x) (hGd : ∀ c e, DifferentiableAt ℝ (G c e) x)
    (hβ : ∀ c, DifferentiableAt ℝ (β c) x) (hξ : ∀ c, DifferentiableAt ℝ (ξ c) x)
    (hψ : DifferentiableAt ℝ ψ x) (hw : DifferentiableAt ℝ w x)
    (hwξ : ∀ j, d w x j = ξ j x) (hψβ : ∀ j, d ψ x j = β j x)
    (hH : ∀ b j, d (ξ b) x j = d (ξ j) x b) (hG : ∀ c e, G c e x = G e c x) :
    ∑ j, d (P ρ G β ξ ψ w σ lam j) x j =
      Real.exp (2 * σ * ψ x) * (-2 * σ * ρ x * TXX G β ξ w lam x +
        Xw G β ξ x * ∑ j, d (flux ρ G ξ j) x j - ρ x * lam * w x * Xw G β ξ x +
        R ρ G β ξ w lam x) := by
  have hX : ∀ b, DifferentiableAt ℝ (X G β b) x := by
    intro b; unfold X; fun_prop
  have hXw : DifferentiableAt ℝ (Xw G β ξ) x := by unfold Xw; fun_prop
  have hfl : ∀ j, DifferentiableAt ℝ (flux ρ G ξ j) x := by intro j; unfold flux; fun_prop
  have hqf : DifferentiableAt ℝ (qf G ξ ξ) x := by unfold qf; fun_prop
  have hq : DifferentiableAt ℝ (q G ξ w lam) x := by unfold q; fun_prop
  have hρX : ∀ j, DifferentiableAt ℝ (fun y => ρ y * X G β j y) x := by intro j; fun_prop
  have he : DifferentiableAt ℝ (fun y => Real.exp (2 * σ * ψ y)) x := by fun_prop
  -- derivatives of the pieces
  have dE : ∀ j, d (fun y => Real.exp (2 * σ * ψ y)) x j =
      Real.exp (2 * σ * ψ x) * (2 * σ * β j x) := by
    intro j
    rw [d_exp (by fun_prop), d_const_mul hψ, hψβ]
  have dXw : ∀ j, d (Xw G β ξ) x j =
      ∑ b, d (X G β b) x j * ξ b x + ∑ b, X G β b x * d (ξ b) x j := by
    intro j
    unfold Xw
    rw [d_sum (u := fun b y => X G β b y * ξ b y) (fun b _ => (hX b).mul (hξ b)),
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => d_mul (hX b) (hξ b) j
  have dqf : ∀ j, d (qf G ξ ξ) x j =
      ∑ c, ∑ e, d (G c e) x j * ξ c x * ξ e x +
        ∑ c, ∑ e, (G c e x * d (ξ c) x j * ξ e x + G c e x * ξ c x * d (ξ e) x j) := by
    intro j
    unfold qf
    rw [d_sum (fun c _ => by fun_prop), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [d_sum (fun e _ => by fun_prop), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [d_mul (by fun_prop) (hξ e), d_mul (hGd c e) (hξ c)]
    ring
  have dq : ∀ j, d (q G ξ w lam) x j = d (qf G ξ ξ) x j + lam * (2 * w x * ξ j x) := by
    intro j
    unfold q
    rw [d_add hqf (by fun_prop), d_const_mul (by fun_prop), d_sq hw, hwξ]
  have dP : ∀ j, d (P ρ G β ξ ψ w σ lam j) x j =
      Real.exp (2 * σ * ψ x) * (2 * σ * β j x) *
        (flux ρ G ξ j x * Xw G β ξ x - 1 / 2 * (ρ x * X G β j x) * q G ξ w lam x) +
      Real.exp (2 * σ * ψ x) * (d (flux ρ G ξ j) x j * Xw G β ξ x +
        flux ρ G ξ j x * d (Xw G β ξ) x j -
        1 / 2 * (d (fun y => ρ y * X G β j y) x j * q G ξ w lam x +
          (ρ x * X G β j x) * d (q G ξ w lam) x j)) := by
    intro j
    unfold P
    rw [d_mul he (by fun_prop), dE, d_sub (by fun_prop) (by fun_prop), d_mul (hfl j) hXw,
      d_mul (u := fun y => 1 / 2 * (ρ y * X G β j y)) (by fun_prop) hq,
      d_const_mul (hρX j)]
    ring
  obtain ⟨s1, hs1⟩ : ∃ s : Fin (n + 1) → ℝ, s = fun j => β j x * flux ρ G ξ j x := ⟨_, rfl⟩
  obtain ⟨s2, hs2⟩ : ∃ s : Fin (n + 1) → ℝ, s = fun j => β j x * X G β j x := ⟨_, rfl⟩
  obtain ⟨s3, hs3⟩ : ∃ s : Fin (n + 1) → ℝ, s = fun j => d (flux ρ G ξ j) x j := ⟨_, rfl⟩
  obtain ⟨s4, hs4⟩ : ∃ s : Fin (n + 1) → ℝ,
    s = fun j => flux ρ G ξ j x * ∑ b, d (X G β b) x j * ξ b x := ⟨_, rfl⟩
  obtain ⟨s5, hs5⟩ : ∃ s : Fin (n + 1) → ℝ,
    s = fun j => flux ρ G ξ j x * ∑ b, X G β b x * d (ξ b) x j := ⟨_, rfl⟩
  obtain ⟨s6, hs6⟩ : ∃ s : Fin (n + 1) → ℝ, s = fun j => d (fun y => ρ y * X G β j y) x j :=
    ⟨_, rfl⟩
  obtain ⟨s7, hs7⟩ : ∃ s : Fin (n + 1) → ℝ,
    s = fun j => (ρ x * X G β j x) * ∑ c, ∑ e, d (G c e) x j * ξ c x * ξ e x := ⟨_, rfl⟩
  obtain ⟨s8, hs8⟩ : ∃ s : Fin (n + 1) → ℝ, s = fun j => (ρ x * X G β j x) *
      ∑ c, ∑ e, (G c e x * d (ξ c) x j * ξ e x + G c e x * ξ c x * d (ξ e) x j) := ⟨_, rfl⟩
  obtain ⟨s9, hs9⟩ : ∃ s : Fin (n + 1) → ℝ, s = fun j => ρ x * X G β j x * ξ j x := ⟨_, rfl⟩
  set E0 := Real.exp (2 * σ * ψ x)
  set Q0 := q G ξ w lam x
  set W0 := Xw G β ξ x
  have step : ∀ j, d (P ρ G β ξ ψ w σ lam j) x j =
      E0 * (2 * σ * W0) * s1 j - E0 * σ * Q0 * ρ x * s2 j + E0 * W0 * s3 j + E0 * s4 j + E0 * s5 j -
        E0 / 2 * Q0 * s6 j - E0 / 2 * s7 j - E0 / 2 * s8 j - E0 * lam * w x * s9 j := by
    intro j
    rw [dP, dXw, dq, dqf]
    simp only [hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9]
    ring
  rw [Finset.sum_congr rfl fun j _ => step j]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h1 : ∑ j, s1 j = ρ x * qf G β ξ x := by rw [hs1]; exact sum_beta_flux
  have h2 : ∑ j, s2 j = -qf G β β x := by rw [hs2]; exact sum_beta_X
  have h5 : ∑ j, s5 j = 1 / 2 * ∑ j, s8 j := by
    rw [hs5, hs8]
    exact hessian_cancel hG (fun b j => d (ξ b) x j) hH
  have h9 : ∑ j, s9 j = ρ x * W0 := by rw [hs9]; exact sum_X_xi
  have hR : R ρ G β ξ w lam x = ∑ j, s4 j - 1 / 2 * (∑ j, s6 j) * Q0 - 1 / 2 * ∑ j, s7 j := by
    rw [hs4, hs6, hs7]; rfl
  have h3 : ∑ j, d (flux ρ G ξ j) x j = ∑ j, s3 j := by rw [hs3]
  have hW : W0 = -qf G β ξ x := Xw_eq hG
  rw [h1, h2, h5, h9, hR, h3]
  unfold TXX
  rw [hW]
  ring

end Current

end

end LorentzianCalderon
