module

public import LorentzianCalderon.Local.Energy.Coform
public import LorentzianCalderon.Local.Energy.Identity
public import LorentzianCalderon.Local.MatrixCalculus

public section

/-!
# The setting of the weighted energy inequality

An open set `V ⊆ ℝ^{1+n}` with a smooth Lorentzian metric `g` and a time orientation `Y`, two
temporal functions `ψ, ψ'` (the `ψ, ψ̃` of the blueprint), and levels `τ, c` such that the lens
`L = {x ∈ V | ψ x ≤ τ, c ≤ ψ' x}` is compact; and eikonal functions of future type.
-/

namespace LorentzianCalderon

noncomputable section
open Set Matrix
open scoped ContDiff

variable {n : ℕ}

/-- The lens `{x ∈ V | ψ x ≤ τ, c ≤ ψ' x}`. -/
def lens (V : Set (E n)) (ψ ψ' : E n → ℝ) (τ c : ℝ) : Set (E n) :=
  {x | x ∈ V ∧ ψ x ≤ τ ∧ c ≤ ψ' x}

theorem lens_def (V : Set (E n)) (ψ ψ' : E n → ℝ) (τ c : ℝ) :
    lens V ψ ψ' τ c =
      {x | x ∈ V ∧ ψ x ≤ τ ∧ c ≤ ψ' x} := by rfl

theorem mem_lens {V : Set (E n)} {ψ ψ' : E n → ℝ} {τ c : ℝ} {x} :
    x ∈ lens V ψ ψ' τ c ↔ x ∈ V ∧ ψ x ≤ τ ∧ c ≤ ψ' x := Iff.rfl

/-- The setting of the weighted energy inequality: `g` is a smooth Lorentzian metric on the open
set `V`, time oriented by `Y`; `ψ` and `ψ'` are temporal on `V`, and the lens is compact. -/
structure EnergySetting (V : Set (E n)) (g : MatrixField n) (Y : E n → E n) (ψ ψ' : E n → ℝ)
    (τ c : ℝ) : Prop where
  isOpen : IsOpen V
  smooth : ∀ i j, ContDiffOn ℝ ∞ (fun x => g x i j) V
  lorentzian : ∀ x ∈ V, IsLorentzian (g x)
  continuousOn_time : ContinuousOn Y V
  timelike : ∀ x ∈ V, form (g x) (Y x) (Y x) < 0
  smooth_ψ : ContDiffOn ℝ ∞ ψ V
  smooth_ψ' : ContDiffOn ℝ ∞ ψ' V
  temporal_ψ : ∀ x ∈ V, IsFutureTimelike g Y x (-grad g ψ x)
  temporal_ψ' : ∀ x ∈ V, IsFutureTimelike g Y x (-grad g ψ' x)
  isCompact : IsCompact (lens V ψ ψ' τ c)

/-- `φ` is an eikonal function of future type on `V`. -/
structure IsEikonal (V : Set (E n)) (g : MatrixField n) (Y : E n → E n) (φ : E n → ℝ) :
    Prop where
  smooth : ContDiffOn ℝ ∞ φ V
  null : ∀ x ∈ V, coform g x (d φ x) (d φ x) = 0
  ne_zero : ∀ x ∈ V, d φ x ≠ 0
  future : ∀ x ∈ V, IsFutureCausal g Y x (-grad g φ x)

/-- The volume density `√|det g|`. -/
def vol (g : MatrixField n) (y : E n) : ℝ := √|(g y).det|

theorem vol_def (g : MatrixField n) (y : E n) :
    vol g y =
      √|(g y).det| := by rfl

section Smooth

variable {k : ℕ∞} {g : MatrixField n} {V : Set (E n)}

theorem contDiffOn_vol (hV : IsOpen V) (hg : ∀ i j, ContDiffOn ℝ k (fun x => g x i j) V)
    (hdet : ∀ x ∈ V, (g x).det ≠ 0) : ContDiffOn ℝ k (vol g) V :=
  fun x hx => (contDiffAt_sqrt_abs_det (fun i j => (hg i j).contDiffAt (hV.mem_nhds hx))
    (hdet x hx)).contDiffWithinAt

theorem vol_pos {x : E n} (hx : (g x).det ≠ 0) : 0 < vol g x :=
  Real.sqrt_pos.2 (abs_pos.2 hx)

end Smooth

namespace EnergySetting

variable {V : Set (E n)} {g : MatrixField n} {Y : E n → E n} {ψ ψ' : E n → ℝ} {τ c : ℝ}
  (h : EnergySetting V g Y ψ ψ' τ c)
include h

omit h in
theorem lens_subset (_ : EnergySetting V g Y ψ ψ' τ c) : lens V ψ ψ' τ c ⊆ V :=
  fun _ hx => hx.1

theorem det_ne_zero {x : E n} (hx : x ∈ V) : (g x).det ≠ 0 :=
  (h.lorentzian x hx).det_neg.ne

theorem contDiffOn_inv (i j : Fin (n + 1)) : ContDiffOn ℝ ∞ (fun x => (g x)⁻¹ i j) V :=
  contDiffOn_inv_apply h.smooth (fun _ hx => h.det_ne_zero hx) i j

theorem contDiffOn_vol : ContDiffOn ℝ ∞ (vol g) V :=
  LorentzianCalderon.contDiffOn_vol h.isOpen h.smooth fun _ hx => h.det_ne_zero hx

theorem isLorentzForm {x : E n} (hx : x ∈ V) : IsLorentzForm (bil (g x)⁻¹) :=
  (h.lorentzian x hx).isLorentzForm_inv

/-- The covector of the time orientation is timelike. -/
theorem time_timelike {x : E n} (hx : x ∈ V) :
    bil (g x)⁻¹ (timeCovector g Y x) (timeCovector g Y x) < 0 := by
  rw [← coform_eq_bil, coform_timeCovector (h.lorentzian x hx)]
  exact h.timelike x hx

theorem timelike_of_future {u : E n → ℝ} {x : E n} (hx : x ∈ V)
    (hu : IsFutureTimelike g Y x (-grad g u x)) :
    bil (g x)⁻¹ (d u x) (d u x) < 0 ∧ bil (g x)⁻¹ (d u x) (timeCovector g Y x) < 0 := by
  have h1 := hu.timelike
  have h2 := hu.future
  rw [form_neg_grad (h.lorentzian x hx), coform_eq_bil] at h1
  rw [form_neg_grad_time (h.lorentzian x hx), coform_eq_bil] at h2
  exact ⟨h1, h2⟩

theorem psi_timelike {x : E n} (hx : x ∈ V) : bil (g x)⁻¹ (d ψ x) (d ψ x) < 0 :=
  (h.timelike_of_future hx (h.temporal_ψ x hx)).1

theorem psi'_timelike {x : E n} (hx : x ∈ V) : bil (g x)⁻¹ (d ψ' x) (d ψ' x) < 0 :=
  (h.timelike_of_future hx (h.temporal_ψ' x hx)).1

theorem psi'_psi_neg {x : E n} (hx : x ∈ V) : bil (g x)⁻¹ (d ψ' x) (d ψ x) < 0 := by
  have h1 := h.timelike_of_future hx (h.temporal_ψ x hx)
  have h2 := h.timelike_of_future hx (h.temporal_ψ' x hx)
  exact (h.isLorentzForm hx).neg_of_sameCone (h.time_timelike hx) h2.1.le h2.2 h1.1 h1.2

omit h in
theorem d_ne_zero_of_timelike (_ : EnergySetting V g Y ψ ψ' τ c) {u : E n → ℝ} {x : E n}
    (_ : x ∈ V)
    (hu : bil (g x)⁻¹ (d u x) (d u x) < 0) : d u x ≠ 0 := by
  intro h0; rw [h0] at hu; simp at hu

theorem eikonal_psi_neg {φ : E n → ℝ} (hφ : IsEikonal V g Y φ) {x : E n} (hx : x ∈ V) :
    bil (g x)⁻¹ (d φ x) (d ψ x) < 0 := by
  have h1 := h.timelike_of_future hx (h.temporal_ψ x hx)
  have hf := hφ.future x hx
  have h2 := hf.future
  rw [form_neg_grad_time (h.lorentzian x hx), coform_eq_bil] at h2
  have h3 := hφ.null x hx
  rw [coform_eq_bil] at h3
  exact (h.isLorentzForm hx).neg_of_sameCone (h.time_timelike hx) h3.le h2 h1.1 h1.2

end EnergySetting

end

end LorentzianCalderon
