module

public import LorentzianCalderon.Local.Energy.Setting
public import LorentzianCalderon.Setting.BoxGreen

public section

/-!
# The weighted energy current of a metric

The current `Current.P` of `Identity.lean` for the coefficients of a metric `g`: `G = g⁻¹`,
`ρ = √|det g|`, and the components of `dψ`, `dw`.
-/

namespace LorentzianCalderon

noncomputable section
open Set Matrix
open scoped ContDiff

variable {n : ℕ}

/-- The entries of the inverse metric, as functions. -/
def ginv (g : MatrixField n) (c e : Fin (n + 1)) (y : E n) : ℝ := (g y)⁻¹ c e

theorem ginv_def (g : MatrixField n) (c e : Fin (n + 1)) (y : E n) :
    ginv g c e y =
      (g y)⁻¹ c e := by rfl

theorem ginv_eq (g : MatrixField n) (c e : Fin (n + 1)) : ginv g c e = fun y => (g y)⁻¹ c e := by
  rfl

/-- The components of the differential, as functions. -/
def dc (u : E n → ℝ) (k : Fin (n + 1)) (y : E n) : ℝ := d u y k

theorem dc_def (u : E n → ℝ) (k : Fin (n + 1)) (y : E n) :
    dc u k y =
      d u y k := by rfl

theorem dc_eq (u : E n → ℝ) (k : Fin (n + 1)) : dc u k = fun y => d u y k := by rfl

/-- The weighted current `√|det g| e^{2σψ} T^j_b X^b`, `X = -grad ψ`, of the energy-momentum
tensor of `w` with mass term `lam`. -/
def current (g : MatrixField n) (ψ w : E n → ℝ) (σ lam : ℝ) (j : Fin (n + 1)) : E n → ℝ :=
  Current.P (vol g) (ginv g) (dc ψ) (dc w) ψ w σ lam j

theorem current_def (g : MatrixField n) (ψ w : E n → ℝ) (σ lam : ℝ) (j : Fin (n + 1)) :
    current g ψ w σ lam j =
      Current.P (vol g) (ginv g) (dc ψ) (dc w) ψ w σ lam j := by rfl

theorem qf_eq (g : MatrixField n) (u v : E n → ℝ) (x : E n) :
    Current.qf (ginv g) (dc u) (dc v) x = bil (g x)⁻¹ (d u x) (d v x) := by
  rw [← coform_eq_bil, Current.qf_def, coform_def]
  rfl

theorem flux_vol_ginv_dc (g : MatrixField n) (w : E n → ℝ) (j : Fin (n + 1)) :
    Current.flux (vol g) (ginv g) (dc w) j = flux g w j :=
  funext fun y => by
    rw [Current.flux_def, flux_def, vol_def]
    rfl

theorem sum_d_flux {g : MatrixField n} {x : E n} (hx : (g x).det ≠ 0) (w : E n → ℝ) :
    ∑ j, d (Current.flux (vol g) (ginv g) (dc w) j) x j = -(vol g x * box g w x) := by
  have h : vol g x * box g w x = -∑ j, d (Current.flux (vol g) (ginv g) (dc w) j) x j := by
    rw [vol_def]
    simp only [flux_vol_ginv_dc]
    exact sqrt_abs_det_mul_box hx w
  linarith

theorem ginv_symm {g : MatrixField n} {x : E n} (hx : IsLorentzian (g x)) (c e : Fin (n + 1)) :
    ginv g c e x = ginv g e c x := by
  have := congrFun (congrFun hx.inv_symm e) c
  simpa [ginv] using this

/-- Contracting the current with a covector `α` gives `-ρ e^{2σψ} T(α, dψ)`. -/
theorem sum_mul_current {g : MatrixField n} {x : E n} (hx : IsLorentzian (g x))
    (ψ w : E n → ℝ) (σ lam : ℝ) (α : Fin (n + 1) → ℝ) :
    ∑ j, α j * current g ψ w σ lam j x =
      -(Real.exp (2 * σ * ψ x) * vol g x) *
        emTensor (bil (g x)⁻¹) lam (w x) (d w x) α (d ψ x) := by
  have hXw := Current.Xw_eq (G := ginv g) (β := dc ψ) (ξ := dc w) (x := x) (ginv_symm hx)
  have h1 : ∑ j, α j * Current.flux (vol g) (ginv g) (dc w) j x =
      vol g x * bil (g x)⁻¹ α (d w x) := by
    rw [← coform_eq_bil]
    simp only [Current.flux_def, coform_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [ginv, dc]; ring
  have h2 : ∑ j, α j * (vol g x * Current.X (ginv g) (dc ψ) j x) =
      -(vol g x * bil (g x)⁻¹ α (d ψ x)) := by
    rw [← coform_eq_bil]
    simp only [Current.X_def, coform_def, Finset.mul_sum, mul_neg, Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [ginv, dc]; ring
  have h3 : ∑ j, α j * current g ψ w σ lam j x =
      Real.exp (2 * σ * ψ x) * ((∑ j, α j * Current.flux (vol g) (ginv g) (dc w) j x) *
        Current.Xw (ginv g) (dc ψ) (dc w) x -
        1 / 2 * (∑ j, α j * (vol g x * Current.X (ginv g) (dc ψ) j x)) *
          Current.q (ginv g) (dc w) w lam x) := by
    simp only [current, Current.P_def, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h3, h1, h2, hXw, Current.q_def, qf_eq, qf_eq]
  simp only [emTensor_def]
  ring

section Smooth

variable {V : Set (E n)} {g : MatrixField n} {Y : E n → E n} {ψ ψ' : E n → ℝ} {τ c : ℝ}

theorem EnergySetting.contDiffOn_X (h : EnergySetting V g Y ψ ψ' τ c) (b : Fin (n + 1)) :
    ContDiffOn ℝ ∞ (Current.X (ginv g) (dc ψ) b) V := by
  rw [show Current.X (ginv g) (dc ψ) b = fun y => -∑ c, ginv g b c y * dc ψ c y from
    funext fun y => Current.X_def _ _ _ _]
  exact (ContDiffOn.sum fun c _ => (h.contDiffOn_inv b c).mul
    (contDiffOn_d h.isOpen h.smooth_ψ c)).neg

end Smooth

/-- The divergence identity for the current of a metric. -/
theorem EnergySetting.div_current {V : Set (E n)} {g : MatrixField n} {Y : E n → E n}
    {ψ ψ' : E n → ℝ} {τ c : ℝ} (h : EnergySetting V g Y ψ ψ' τ c) {x : E n} (hx : x ∈ V)
    {w : E n → ℝ} (hw : ContDiffAt ℝ 2 w x) (σ lam : ℝ) :
    ∑ j, d (current g ψ w σ lam j) x j =
      Real.exp (2 * σ * ψ x) * (-2 * σ * vol g x * Current.TXX (ginv g) (dc ψ) (dc w) w lam x -
        vol g x * box g w x * Current.Xw (ginv g) (dc ψ) (dc w) x -
        vol g x * lam * w x * Current.Xw (ginv g) (dc ψ) (dc w) x +
        Current.R (vol g) (ginv g) (dc ψ) (dc w) w lam x) := by
  have hVx : V ∈ nhds x := h.isOpen.mem_nhds hx
  have key := Current.div_P (ρ := vol g) (G := ginv g) (β := dc ψ) (ξ := dc w) (ψ := ψ)
    (w := w) (σ := σ) (lam := lam) (x := x)
    ((h.contDiffOn_vol.contDiffAt hVx).differentiableAt (by simp))
    (fun c e => ((h.contDiffOn_inv c e).contDiffAt hVx).differentiableAt (by simp))
    (fun c => ((contDiffOn_d h.isOpen h.smooth_ψ c).contDiffAt hVx).differentiableAt
      (by simp))
    (fun c => (contDiffAt_d (m := 1) hw c).differentiableAt (by simp))
    ((h.smooth_ψ.contDiffAt hVx).differentiableAt (by simp))
    (hw.differentiableAt (by simp))
    (fun j => rfl) (fun j => rfl) (fun b j => by
      have := d2_comm hw j b
      rwa [d2_def, d2_def] at this)
    (fun c e => ginv_symm (h.lorentzian x hx) c e)
  refine key.trans ?_
  rw [sum_d_flux (h.det_ne_zero hx)]
  ring

end

end LorentzianCalderon
