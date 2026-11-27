module

public import LorentzianCalderon.Local.EnergyIntegratedInterface

public section

/-!
# The energy inequalities, as used by the local continuation step

The energy inequalities of `LorentzianCalderon.Local.Energy` and
`LorentzianCalderon.Local.EnergyIntegratedInterface`, restated for the local step, with
`StepEnergySetting` a copy of `EnergySetting`, the lens written out, and the eikonal conditions
spelled out.
-/

namespace LorentzianCalderon

noncomputable section
open Set MeasureTheory
open scoped ContDiff

variable {n : ℕ}

/-- A copy of `EnergySetting`: `g` is a smooth Lorentzian metric on the open set `V`, time
oriented by `Y`; `ψ` and `ψ'` are temporal on `V`, and the lens
`{x ∈ V | ψ x ≤ τ, c ≤ ψ' x}` is compact. -/
structure StepEnergySetting (V : Set (E n)) (g : MatrixField n) (Y : E n → E n)
    (ψ ψ' : E n → ℝ) (τ c : ℝ) : Prop where
  isOpen : IsOpen V
  smooth : ∀ i j, ContDiffOn ℝ ∞ (fun x => g x i j) V
  lorentzian : ∀ x ∈ V, IsLorentzian (g x)
  continuousOn_time : ContinuousOn Y V
  timelike : ∀ x ∈ V, form (g x) (Y x) (Y x) < 0
  smooth_ψ : ContDiffOn ℝ ∞ ψ V
  smooth_ψ' : ContDiffOn ℝ ∞ ψ' V
  temporal_ψ : ∀ x ∈ V, IsFutureTimelike g Y x (-grad g ψ x)
  temporal_ψ' : ∀ x ∈ V, IsFutureTimelike g Y x (-grad g ψ' x)
  isCompact : IsCompact {x | x ∈ V ∧ ψ x ≤ τ ∧ c ≤ ψ' x}

/-- A copy of `IsEikonal`: `φ` is an eikonal function of future type on `V`. -/
structure StepEikonal (V : Set (E n)) (g : MatrixField n) (Y : E n → E n) (φ : E n → ℝ) :
    Prop where
  smooth : ContDiffOn ℝ ∞ φ V
  null : ∀ x ∈ V, coform g x (d φ x) (d φ x) = 0
  ne_zero : ∀ x ∈ V, d φ x ≠ 0
  future : ∀ x ∈ V, IsFutureCausal g Y x (-grad g φ x)

namespace StepEnergySetting

variable {V : Set (E n)} {g : MatrixField n} {Y : E n → E n} {ψ ψ' : E n → ℝ} {τ c : ℝ}

theorem toEnergySetting (h : StepEnergySetting V g Y ψ ψ' τ c) :
    EnergySetting V g Y ψ ψ' τ c :=
  ⟨h.isOpen, h.smooth, h.lorentzian, h.continuousOn_time, h.timelike, h.smooth_ψ,
    h.smooth_ψ', h.temporal_ψ, h.temporal_ψ', by rw [lens_def]; exact h.isCompact⟩

theorem _root_.LorentzianCalderon.StepEikonal.toIsEikonal {φ : E n → ℝ}
    (hφ : StepEikonal V g Y φ) : IsEikonal V g Y φ :=
  ⟨hφ.smooth, hφ.null, hφ.ne_zero, hφ.future⟩

/-- `EnergySetting.ae_lens_ne`: the top and the bottom of the lens are null. -/
theorem ae_lens_ne (h : StepEnergySetting V g Y ψ ψ' τ c) :
    ∀ᵐ x ∂(volume.restrict {x | x ∈ V ∧ ψ x ≤ τ ∧ c ≤ ψ' x}), ψ x ≠ τ ∧ ψ' x ≠ c := by
  rw [← lens_def]
  exact h.toEnergySetting.ae_lens_ne

/-- `EnergySetting.volume_estimate_superlevel` with `φ = 0` (blueprint `eq_energy2`, with the
sup norm of the components of `dw`). -/
theorem energy_volume (h : StepEnergySetting V g Y ψ ψ' τ c) :
    ∃ C σ₀ : ℝ, ∀ σ ≥ σ₀, ∀ (U : Set (E n)) (w : E n → ℝ), IsOpen U →
      {x | x ∈ V ∧ ψ x ≤ τ ∧ c ≤ ψ' x} ⊆ U → ContDiffOn ℝ 2 w U →
      (∀ x ∈ {x | x ∈ V ∧ ψ x ≤ τ ∧ c ≤ ψ' x}, ψ x = τ → w x = 0 ∧ d w x = 0) →
      σ ^ 2 * ∫ x in {x | x ∈ V ∧ ψ x ≤ τ ∧ c ≤ ψ' x},
          Real.exp (2 * σ * ψ x) * (‖d w x‖ ^ 2 + σ ^ 2 * w x ^ 2) ≤
        C * ∫ x in {x | x ∈ V ∧ ψ x ≤ τ ∧ c ≤ ψ' x}, Real.exp (2 * σ * ψ x) * box g w x ^ 2 := by
  rw [← lens_def]
  have hd0 : ∀ x, d (fun _ : E n => (0 : ℝ)) x = 0 := fun x => by ext i; simp [d_def]
  obtain ⟨C, σ₀, hC⟩ := h.toEnergySetting.volume_estimate_superlevel
    (φ := fun _ => 0) contDiffOn_const fun x _ => by simp [hd0]
  refine ⟨C, σ₀, fun σ hσ U w hU hLU hw hvan => ?_⟩
  have hS : lens V ψ ψ' τ c ∩ {x | (-1 : ℝ) < (fun _ : E n => (0 : ℝ)) x} =
      lens V ψ ψ' τ c := by
    ext x; simp
  have := hC σ hσ (-1) U w hU hLU hw fun x hx h1 _ => hvan x hx h1
  rwa [hS] at this

/-- `EnergySetting.volume_estimate_superlevel` for an eikonal function of future type
(blueprint `eq_energy` without the surface term, with the sup norm of the components of
`dw`). -/
theorem energy_superlevel (h : StepEnergySetting V g Y ψ ψ' τ c) {φ : E n → ℝ}
    (hφ : StepEikonal V g Y φ) :
    ∃ C σ₀ : ℝ, ∀ σ ≥ σ₀, ∀ (s : ℝ) (U : Set (E n)) (w : E n → ℝ), IsOpen U →
      {x | x ∈ V ∧ ψ x ≤ τ ∧ c ≤ ψ' x} ⊆ U → ContDiffOn ℝ 2 w U →
      (∀ x ∈ {x | x ∈ V ∧ ψ x ≤ τ ∧ c ≤ ψ' x}, ψ x = τ → s ≤ φ x → w x = 0 ∧ d w x = 0) →
      σ ^ 2 * ∫ x in {x | x ∈ V ∧ ψ x ≤ τ ∧ c ≤ ψ' x} ∩ {x | s < φ x},
          Real.exp (2 * σ * ψ x) * (‖d w x‖ ^ 2 + σ ^ 2 * w x ^ 2) ≤
        C * ∫ x in {x | x ∈ V ∧ ψ x ≤ τ ∧ c ≤ ψ' x} ∩ {x | s < φ x},
          Real.exp (2 * σ * ψ x) * box g w x ^ 2 := by
  rw [← lens_def]
  exact h.toEnergySetting.volume_estimate_superlevel hφ.smooth fun x hx =>
    ⟨by rw [← coform_eq_bil, hφ.null x hx],
      (h.toEnergySetting.eikonal_psi_neg hφ.toIsEikonal hx).le⟩

/-- `EnergySetting.energy_integrated` (`EnergyIntegratedInterface`). -/
theorem energy_integrated (h : StepEnergySetting V g Y ψ ψ' τ c) {φ : E n → ℝ}
    (hφ : StepEikonal V g Y φ) :
    ∃ C σ₀ : ℝ, ∀ σ ≥ σ₀, ∀ (s₁ s₂ : ℝ) (W : Set (ℝ × E n)) (w : ℝ → E n → ℝ), s₁ ≤ s₂ →
      IsOpen W → Icc s₁ s₂ ×ˢ {x | x ∈ V ∧ ψ x ≤ τ ∧ c ≤ ψ' x} ⊆ W →
      ContDiffOn ℝ 2 (fun p : ℝ × E n => w p.1 p.2) W →
      (∀ s ∈ Icc s₁ s₂, ∀ x ∈ {x | x ∈ V ∧ ψ x ≤ τ ∧ c ≤ ψ' x}, ψ x = τ → s ≤ φ x →
        w s x = 0 ∧ fderiv ℝ (w s) x = 0) →
      σ * ∫ x in {x | x ∈ V ∧ ψ x ≤ τ ∧ c ≤ ψ' x} ∩ {x | s₁ ≤ φ x ∧ φ x ≤ s₂},
          Real.exp (2 * σ * ψ x) *
            (coform g x (d φ x) (d (w (φ x)) x) ^ 2 + σ ^ 2 * w (φ x) x ^ 2) ≤
        C * ∫ s in s₁..s₂, ∫ x in {x | x ∈ V ∧ ψ x ≤ τ ∧ c ≤ ψ' x} ∩ {x | s < φ x},
          Real.exp (2 * σ * ψ x) * box g (w s) x ^ 2 := by
  rw [← lens_def]
  exact h.toEnergySetting.energy_integrated hφ.toIsEikonal

end StepEnergySetting

end

end LorentzianCalderon
