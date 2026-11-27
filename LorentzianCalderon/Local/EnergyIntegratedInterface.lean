module

public import LorentzianCalderon.Local.Energy

public section

/-!
# The weighted energy inequality integrated over the level

Interface for the surface term of `lem_energy` (eq. `eq_energy`) after integration in `s`: for a
family `w s` of class `C²` in `(s, x)` with `w s = 0`, `d (w s) = 0` on `{ψ = τ} ∩ {φ ≥ s} ∩ L`,
integrating `σ ∫_{Γ_s ∩ L} e^{2σψ} (|Z w_s|² + σ² w_s²) dμ_s` over `s ∈ [s₁, s₂]` gives a volume
integral over `L ∩ {s₁ ≤ φ ≤ s₂}` with `s = φ(x)`. Here `Z w = -g(dφ, dw)`, whose square is
`coform g x (d φ x) (d w x) ^ 2`.
-/

namespace LorentzianCalderon

noncomputable section
open Set MeasureTheory Filter Topology
open scoped ContDiff

variable {n : ℕ}

namespace EnergySetting

variable {V : Set (E n)} {g : MatrixField n} {Y : E n → E n} {ψ ψ' : E n → ℝ} {τ c : ℝ}

/-- **Weighted energy inequality, integrated surface term** (blueprint `eq_energy` integrated
in `s`). -/
theorem energy_integrated (h : EnergySetting V g Y ψ ψ' τ c) {φ : E n → ℝ}
    (hφ : IsEikonal V g Y φ) :
    ∃ C σ₀ : ℝ, ∀ σ ≥ σ₀, ∀ (s₁ s₂ : ℝ) (W : Set (ℝ × E n)) (w : ℝ → E n → ℝ), s₁ ≤ s₂ →
      IsOpen W → Icc s₁ s₂ ×ˢ lens V ψ ψ' τ c ⊆ W →
      ContDiffOn ℝ 2 (fun p : ℝ × E n => w p.1 p.2) W →
      (∀ s ∈ Icc s₁ s₂, ∀ x ∈ lens V ψ ψ' τ c, ψ x = τ → s ≤ φ x →
        w s x = 0 ∧ fderiv ℝ (w s) x = 0) →
      σ * ∫ x in lens V ψ ψ' τ c ∩ {x | s₁ ≤ φ x ∧ φ x ≤ s₂}, Real.exp (2 * σ * ψ x) *
          (coform g x (d φ x) (d (w (φ x)) x) ^ 2 + σ ^ 2 * w (φ x) x ^ 2) ≤
        C * ∫ s in s₁..s₂, ∫ x in lens V ψ ψ' τ c ∩ {x | s < φ x},
          Real.exp (2 * σ * ψ x) * box g (w s) x ^ 2 := by
  obtain ⟨C, σ₀, hC⟩ := h.energy_surface (ψ := ψ) (ψ' := ψ') (τ := τ) (c := c) hφ
  refine ⟨C, σ₀, fun σ hσ s₁ s₂ W w hs hW hsub hw hvan => ?_⟩
  have hLV := h.lens_subset (ψ := ψ) (ψ' := ψ') (τ := τ) (c := c)
  have hLc : IsCompact (lens V ψ ψ' τ c) := h.isCompact
  obtain ⟨A, U, hA, hU, hIA, hLU, hAU⟩ := generalized_tube_lemma isCompact_Icc hLc hW hsub
  -- a margin `δ` with `[s₁ - δ, s₂ + δ] ⊆ A`
  obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.isOpen_iff.1 hA s₁ (hIA ⟨le_rfl, hs⟩)
  obtain ⟨ε₂, hε₂, hb₂⟩ := Metric.isOpen_iff.1 hA s₂ (hIA ⟨hs, le_rfl⟩)
  set δ := min ε₁ ε₂ with hδdef
  have hδ : 0 < δ := lt_min hε₁ hε₂
  have hmarg : Icc (s₁ - δ / 2) (s₂ + δ / 2) ⊆ A := by
    intro y hy
    have h1 := min_le_left ε₁ ε₂
    have h2 := min_le_right ε₁ ε₂
    rcases lt_or_ge y s₁ with hy1 | hy1
    · refine hb₁ (Metric.mem_ball.2 ?_)
      rw [Real.dist_eq, abs_of_neg (by linarith)]
      linarith [hy.1]
    rcases le_or_gt y s₂ with hy2 | hy2
    · exact hIA ⟨hy1, hy2⟩
    · refine hb₂ (Metric.mem_ball.2 ?_)
      rw [Real.dist_eq, abs_of_pos (by linarith)]
      linarith [hy.2]
  -- a cut-off `χ` in `s`, equal to `1` on `[s₁, s₂]` and supported in `A`
  set r := (s₂ - s₁) / 2 with hrdef
  have hr : 0 ≤ r := by rw [hrdef]; linarith
  let χ : ContDiffBump ((s₁ + s₂) / 2) := ⟨r + δ / 4, r + δ / 2, by positivity, by linarith⟩
  have hχ1 : ∀ s ∈ Icc s₁ s₂, χ s = 1 := by
    intro s hs'
    refine χ.one_of_mem_closedBall ?_
    rw [Real.closedBall_eq_Icc]
    have hin : χ.rIn = r + δ / 4 := rfl
    rw [hin]
    constructor <;> [linarith [hs'.1]; linarith [hs'.2]]
  have hχA : tsupport χ ⊆ A := by
    have hout : χ.rOut = r + δ / 2 := rfl
    rw [χ.tsupport_eq, Real.closedBall_eq_Icc, hout]
    refine (Icc_subset_Icc ?_ ?_).trans hmarg
    · show s₁ - δ / 2 ≤ (s₁ + s₂) / 2 - (r + δ / 2)
      rw [hrdef]; linarith
    · show (s₁ + s₂) / 2 + (r + δ / 2) ≤ s₂ + δ / 2
      rw [hrdef]; linarith
  set w' : ℝ → E n → ℝ := fun s x => χ s * w s x with hw'def
  have hw'eq : ∀ s ∈ Icc s₁ s₂, w' s = w s := fun s hs' => by
    ext x; simp only [hw'def, hχ1 s hs', one_mul]
  have hw' : ContDiffOn ℝ 2 (fun p : ℝ × E n => w' p.1 p.2) (univ ×ˢ U) := by
    intro p hp
    refine ContDiffAt.contDiffWithinAt ?_
    by_cases hpA : p.1 ∈ A
    · have hpW : W ∈ 𝓝 p := Filter.mem_of_superset ((hA.prod hU).mem_nhds ⟨hpA, hp.2⟩) hAU
      exact ((χ.contDiff (n := 2)).contDiffAt.comp p contDiffAt_fst).mul (hw.contDiffAt hpW)
    · have hev : (χ : ℝ → ℝ) =ᶠ[𝓝 p.1] 0 := notMem_tsupport_iff_eventuallyEq.1 fun h' =>
        hpA (hχA h')
      refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [continuous_fst.continuousAt.eventually hev] with q hq
      simp only [hw'def, Pi.zero_apply] at hq ⊢
      rw [hq, zero_mul]
  have hvan' : ∀ s ∈ Icc s₁ s₂, ∀ x ∈ lens V ψ ψ' τ c, ψ x = τ → s ≤ φ x →
      w' s x = 0 ∧ fderiv ℝ (w' s) x = 0 := by
    intro s hs' x hx h1 h2
    rw [hw'eq s hs']
    exact hvan s hs' x hx h1 h2
  have key := hC σ hσ s₁ s₂ U w' hs hU hLU hw' hvan'
  have hSm : MeasurableSet (lens V ψ ψ' τ c ∩ {x | s₁ ≤ φ x ∧ φ x ≤ s₂}) := by
    have := (hφ.smooth.continuousOn.mono hLV).preimage_isClosed_of_isClosed hLc.isClosed
      (isClosed_Icc (a := s₁) (b := s₂))
    exact this.measurableSet
  have hlhs : ∫ x in lens V ψ ψ' τ c ∩ {x | s₁ ≤ φ x ∧ φ x ≤ s₂}, Real.exp (2 * σ * ψ x) *
        (fderiv ℝ (w' (φ x)) x (-grad g φ x) ^ 2 + σ ^ 2 * w' (φ x) x ^ 2) =
      ∫ x in lens V ψ ψ' τ c ∩ {x | s₁ ≤ φ x ∧ φ x ≤ s₂}, Real.exp (2 * σ * ψ x) *
        (coform g x (d φ x) (d (w (φ x)) x) ^ 2 + σ ^ 2 * w (φ x) x ^ 2) := by
    refine setIntegral_congr_fun hSm fun x hx => ?_
    rw [hw'eq (φ x) hx.2, sq_fderiv_neg_grad (h.lorentzian x (hLV hx.1)), coform_eq_bil]
  have hrhs : ∫ s in s₁..s₂, ∫ x in lens V ψ ψ' τ c ∩ {x | s < φ x},
        Real.exp (2 * σ * ψ x) * box g (w' s) x ^ 2 =
      ∫ s in s₁..s₂, ∫ x in lens V ψ ψ' τ c ∩ {x | s < φ x},
        Real.exp (2 * σ * ψ x) * box g (w s) x ^ 2 := by
    refine intervalIntegral.integral_congr fun s hs' => ?_
    rw [uIcc_of_le hs] at hs'
    simp only [hw'eq s hs']
  rw [hlhs, hrhs] at key
  exact key

end EnergySetting

end

end LorentzianCalderon
