module

public import LorentzianCalderon.Induction.Cones
public import LorentzianCalderon.Green.Temporal
public import LorentzianCalderon.Local.Differential

public section

/-!
# Setting of the induction

For a Cauchy temporal function `ψ`, the superlevel sets `A ψ τ = {ψ > τ}` are open, connected
(given a flow `Φ` with `ψ (Φ t x) = ψ x + t`), future sets, and not contained in any compact set.
`ExtensionProperty` is the statement `P(τ)` of the blueprint (`def_extension`).
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Matrix

variable {n : ℕ}

/-- The superlevel set `A_τ = {ψ > τ}`. -/
def A (ψ : E n → ℝ) (τ : ℝ) : Set (E n) := { x | τ < ψ x }

theorem A_def (ψ : E n → ℝ) (τ : ℝ) :
    A ψ τ =
      { x | τ < ψ x } := by rfl

@[simp]
lemma mem_A {ψ : E n → ℝ} {τ : ℝ} {x : E n} : x ∈ A ψ τ ↔ τ < ψ x := Iff.rfl

section Topology

variable {ψ : E n → ℝ} {Φ : ℝ → E n → E n} {τ : ℝ}

lemma isOpen_A (hψ : Continuous ψ) (τ : ℝ) : IsOpen (A ψ τ) :=
  isOpen_lt continuous_const hψ

/-- `A_τ` is the image of `(τ, ∞) × ℝ^{1+n}` under `(t, x) ↦ Φ (t - ψ x) x`. -/
lemma isConnected_A (hψ : Continuous ψ) (hΦ : Continuous fun p : ℝ × E n => Φ p.1 p.2)
    (hΦ0 : ∀ x, Φ 0 x = x) (hΦψ : ∀ t x, ψ (Φ t x) = ψ x + t) (τ : ℝ) :
    IsConnected (A ψ τ) := by
  have hc : Continuous fun p : ℝ × E n => Φ (p.1 - ψ p.2) p.2 :=
    hΦ.comp ((continuous_fst.sub (hψ.comp continuous_snd)).prodMk continuous_snd)
  have himage : (fun p : ℝ × E n => Φ (p.1 - ψ p.2) p.2) '' (Ioi τ ×ˢ univ) = A ψ τ := by
    ext y
    constructor
    · rintro ⟨⟨t, x⟩, ⟨ht, -⟩, rfl⟩
      simp only [mem_A, hΦψ]
      simpa using ht
    · intro hy
      exact ⟨(ψ y, y), ⟨hy, mem_univ _⟩, by simp [hΦ0]⟩
  rw [← himage]
  exact ((isConnected_Ioi).prod isConnected_univ).image _ hc.continuousOn

/-- `A_τ` is not contained in a compact set. -/
lemma nonempty_A_diff (hψ : Continuous ψ) (hΦψ : ∀ t x, ψ (Φ t x) = ψ x + t) {K : Set (E n)}
    (hK : IsCompact K) (τ : ℝ) : (A ψ τ \ K).Nonempty := by
  obtain ⟨M, hM⟩ := (hK.image hψ).isBounded.bddAbove
  set x₀ : E n := 0
  refine ⟨Φ (max τ M + 1 - ψ x₀) x₀, ?_, fun hx => ?_⟩
  · simp only [mem_A, hΦψ]
    linarith [le_max_left τ M]
  · have := hM (mem_image_of_mem ψ hx)
    rw [hΦψ] at this
    linarith [le_max_right τ M]

end Topology

/-! ### `A_τ` is a future set -/

section Monotone

variable {g : MatrixField n} {Y : E n → E n} {ψ : E n → ℝ}

/-- `A_τ` is a future set. -/
lemma IsCauchyTemporal.mem_A_of_causalLE (hg : IsSpacetime g Y) (hψ : IsCauchyTemporal g Y ψ)
    {τ : ℝ} {p q : E n} (hp : p ∈ A ψ τ) (hpq : CausalLE g Y p q) : q ∈ A ψ τ :=
  lt_of_lt_of_le hp (hψ.le_of_causalLE hg hpq)

end Monotone

/-! ### The extension property -/

/-- The extension property `P(τ)` (blueprint, `def_extension`): `Ψ` is smooth on `A_τ`, pulls
`g'` back to `g` there, and is the identity on `A_τ \ W`. -/
structure ExtensionProperty (g g' : MatrixField n) (ψ : E n → ℝ) (W : Set (E n)) (τ : ℝ)
    (Ψ : E n → E n) : Prop where
  smooth : ContDiffOn ℝ ∞ Ψ (A ψ τ)
  pullback : ∀ x ∈ A ψ τ, g x = (D Ψ x)ᵀ * g' (Ψ x) * D Ψ x
  eq_self : ∀ x ∈ A ψ τ, x ∉ W → Ψ x = x

end

end LorentzianCalderon
