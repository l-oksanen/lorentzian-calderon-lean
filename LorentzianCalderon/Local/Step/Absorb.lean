module

public import Mathlib

public section

/-!
# The local continuation step: absorption

The bookkeeping of Steps 1–3 of `prop_local_step` with the weighted norms replaced by real
numbers depending on `σ`. For a label `a`, `NG, NΘ, NP a, NQ a, NR a` stand for the weighted
`L²(L)` norms squared of `ḡ`, `θ̄`, `φ̄_a`, `dφ̄_a`, `□_g φ̄_a`; `NT a`, `NM a` for those of
`T_a = θ̄^k (∂_k φ'_a) ∘ Ψ` and of `T_a - □_g φ̄_a`; `NW a` for that of
`|Z_a w̄_{a,φ_a}|² + σ² w̄_{a,φ_a}²`. The inequalities of Steps 1–3 hold for `σ ≥ σ₀` with
constants independent of `σ`; then for large `σ` all these norms vanish.
-/

namespace LorentzianCalderon

open Finset

variable {ι : Type*} [Fintype ι] {m : ℕ}

/-- **Absorption**: the norms of Steps 1–3 vanish for some large `σ`. -/
theorem absorb (e : Fin m → ι) {σ₀ K₁ K₂ K₃ K₄ K₅ K₆ : ℝ} (hσ₀ : 1 ≤ σ₀) (hK₁ : 0 ≤ K₁)
    (hK₂ : 0 ≤ K₂) (hK₃ : 0 ≤ K₃) (hK₄ : 0 ≤ K₄) (hK₅ : 0 ≤ K₅) (hK₆ : 0 ≤ K₆)
    {NG NΘ : ℝ → ℝ} {NP NQ NR NT NM NW : ι → ℝ → ℝ}
    (h0 : ∀ σ ≥ σ₀, 0 ≤ NG σ ∧ 0 ≤ NΘ σ ∧
      ∀ a, 0 ≤ NP a σ ∧ 0 ≤ NQ a σ ∧ 0 ≤ NR a σ ∧ 0 ≤ NT a σ ∧ 0 ≤ NM a σ ∧ 0 ≤ NW a σ)
    (hE1 : ∀ σ ≥ σ₀, ∀ a, σ * NW a σ ≤ K₁ * (NG σ + NΘ σ + NP a σ))
    (hM : ∀ σ ≥ σ₀, ∀ a, NM a σ ≤ K₂ * (NW a σ + NG σ + NP a σ + NQ a σ))
    (hT : ∀ σ ≥ σ₀, ∀ a, NT a σ ≤ K₃ * NΘ σ)
    (hR : ∀ σ ≥ σ₀, ∀ a, NR a σ ≤ 2 * NT a σ + 2 * NM a σ)
    (hTR : ∀ σ ≥ σ₀, ∀ a, NT a σ ≤ 2 * NM a σ + 2 * NR a σ)
    (hgauge : ∀ σ ≥ σ₀, ∀ i, NP (e i) σ = 0 ∧ NQ (e i) σ = 0 ∧ NR (e i) σ = 0)
    (hbasis : ∀ σ ≥ σ₀, NΘ σ ≤ K₄ * ∑ i, NT (e i) σ)
    (hE2 : ∀ σ ≥ σ₀, ∀ a, σ ^ 2 * NQ a σ + σ ^ 4 * NP a σ ≤ K₅ * NR a σ)
    (hspan : ∀ σ ≥ σ₀, NG σ ≤ K₆ * ∑ a, NQ a σ) :
    ∃ σ ≥ σ₀, NG σ = 0 ∧ NΘ σ = 0 ∧ ∀ a, NP a σ = 0 ∧ NQ a σ = 0 := by
  set A := 2 * K₄ * K₂ * m
  set B := 2 * K₃ * (1 + 2 * A) + 2 * K₂ * (3 + 2 * A) + 4 * K₂
  set c := (Fintype.card ι : ℝ)
  have hA : 0 ≤ A := by positivity
  have hB : 0 ≤ B := by positivity
  set σ := max σ₀ (2 * A * K₁ + K₁ + 2 * K₅ * B + 2 * K₆ * c * 2 * K₅ * B + 1)
  have hσ₀σ : σ₀ ≤ σ := le_max_left _ _
  have hσX : 2 * A * K₁ + K₁ + 2 * K₅ * B + 2 * K₆ * c * 2 * K₅ * B + 1 ≤ σ := le_max_right _ _
  have hc : 0 ≤ c := by positivity
  have hσ1 : 1 ≤ σ := le_trans hσ₀ hσ₀σ
  have hX1 : 0 ≤ 2 * K₅ * B := by positivity
  have hX2 : 0 ≤ 2 * K₆ * c * 2 * K₅ * B := by positivity
  have hX3 : 0 ≤ 2 * A * K₁ := by positivity
  have hσpos : 0 < σ := by linarith
  have hσsq : σ ≤ σ ^ 2 := by nlinarith
  have hσ4 : σ ^ 2 ≤ σ ^ 4 := by nlinarith
  refine ⟨σ, hσ₀σ, ?_⟩
  obtain ⟨hG0, hΘ0, hN0⟩ := h0 σ hσ₀σ
  have hMg : ∀ i, σ * NM (e i) σ ≤ K₂ * (K₁ * (NG σ + NΘ σ) + σ * NG σ) := by
    intro i
    obtain ⟨hP, hQ, -⟩ := hgauge σ hσ₀σ i
    have h1 := hM σ hσ₀σ (e i)
    have h2 := hE1 σ hσ₀σ (e i)
    rw [hP, hQ] at h1
    rw [hP] at h2
    have : σ * NM (e i) σ ≤ σ * (K₂ * (NW (e i) σ + NG σ)) := by
      have := mul_le_mul_of_nonneg_left h1 hσpos.le; linarith
    nlinarith
  have hΘσ : σ * NΘ σ ≤ A * (K₁ * (NG σ + NΘ σ) + σ * NG σ) := by
    have h1 := hbasis σ hσ₀σ
    have h2 : ∀ i, σ * NT (e i) σ ≤ 2 * (K₂ * (K₁ * (NG σ + NΘ σ) + σ * NG σ)) := by
      intro i
      have := hTR σ hσ₀σ (e i)
      rw [(hgauge σ hσ₀σ i).2.2] at this
      have := mul_le_mul_of_nonneg_left this hσpos.le
      linarith [hMg i]
    have h3 : σ * ∑ i, NT (e i) σ ≤ m * (2 * (K₂ * (K₁ * (NG σ + NΘ σ) + σ * NG σ))) := by
      rw [mul_sum]
      calc ∑ i, σ * NT (e i) σ ≤ ∑ _i : Fin m, 2 * (K₂ * (K₁ * (NG σ + NΘ σ) + σ * NG σ)) :=
            sum_le_sum fun i _ => h2 i
        _ = _ := by simp
    have h4 : σ * NΘ σ ≤ K₄ * (σ * ∑ i, NT (e i) σ) := by
      have := mul_le_mul_of_nonneg_left h1 hσpos.le; linarith
    calc σ * NΘ σ ≤ K₄ * (σ * ∑ i, NT (e i) σ) := h4
      _ ≤ K₄ * (m * (2 * (K₂ * (K₁ * (NG σ + NΘ σ) + σ * NG σ)))) :=
          mul_le_mul_of_nonneg_left h3 hK₄
      _ = A * (K₁ * (NG σ + NΘ σ) + σ * NG σ) := by ring
  have hAK : A * K₁ ≤ σ / 2 := by linarith
  have hΘ : NΘ σ ≤ (1 + 2 * A) * NG σ := by
    have : σ * NΘ σ ≤ σ / 2 * NG σ + σ / 2 * NΘ σ + A * σ * NG σ := by
      have e1 : A * (K₁ * (NG σ + NΘ σ) + σ * NG σ) =
          A * K₁ * NG σ + A * K₁ * NΘ σ + A * σ * NG σ := by ring
      nlinarith [mul_le_mul_of_nonneg_right hAK hG0, mul_le_mul_of_nonneg_right hAK hΘ0]
    nlinarith
  have hRa : ∀ a, NR a σ ≤ B * (NG σ + NP a σ + NQ a σ) := by
    intro a
    obtain ⟨hP0, hQ0, -, -, -, hW0⟩ := hN0 a
    have hW : NW a σ ≤ NG σ + NΘ σ + NP a σ := by
      have h := hE1 σ hσ₀σ a
      have hK1σ : K₁ ≤ σ := by linarith
      have : σ * NW a σ ≤ σ * (NG σ + NΘ σ + NP a σ) :=
        h.trans (mul_le_mul_of_nonneg_right hK1σ (by linarith))
      exact le_of_mul_le_mul_left this hσpos
    have h1 := hR σ hσ₀σ a
    have h2 := hT σ hσ₀σ a
    have h3 := hM σ hσ₀σ a
    have h4 : NT a σ ≤ K₃ * ((1 + 2 * A) * NG σ) := h2.trans (mul_le_mul_of_nonneg_left hΘ hK₃)
    have h5 : NM a σ ≤ K₂ * ((2 + 2 * A) * NG σ + 2 * NP a σ + NQ a σ + NG σ) := by
      refine h3.trans (mul_le_mul_of_nonneg_left ?_ hK₂)
      linarith
    have : NR a σ ≤ 2 * (K₃ * ((1 + 2 * A) * NG σ)) +
        2 * (K₂ * ((2 + 2 * A) * NG σ + 2 * NP a σ + NQ a σ + NG σ)) := by linarith
    refine this.trans ?_
    have e : B * (NG σ + NP a σ + NQ a σ) = 2 * K₃ * (1 + 2 * A) * NG σ +
        2 * K₂ * (3 + 2 * A) * NG σ + 4 * K₂ * NG σ +
        (2 * K₃ * (1 + 2 * A) + 2 * K₂ * (3 + 2 * A) + 4 * K₂) * (NP a σ + NQ a σ) := by ring
    rw [e]
    have : 0 ≤ (2 * K₃ * (1 + 2 * A) + 2 * K₂ * (3 + 2 * A)) * (NP a σ + NQ a σ) +
        2 * K₂ * NQ a σ := by positivity
    nlinarith
  have hKB : K₅ * B ≤ σ ^ 2 / 2 := by nlinarith
  have hQP : ∀ a, σ ^ 2 * NQ a σ ≤ 2 * K₅ * B * NG σ ∧ σ ^ 4 * NP a σ ≤ 2 * K₅ * B * NG σ := by
    intro a
    obtain ⟨hP0, hQ0, -⟩ := hN0 a
    have h1 := hE2 σ hσ₀σ a
    have h2 : K₅ * NR a σ ≤ K₅ * B * (NG σ + NP a σ + NQ a σ) := by
      have := mul_le_mul_of_nonneg_left (hRa a) hK₅; linarith
    have h3 : K₅ * B * NP a σ ≤ σ ^ 4 / 2 * NP a σ :=
      mul_le_mul_of_nonneg_right (hKB.trans (by nlinarith)) hP0
    have h4 : K₅ * B * NQ a σ ≤ σ ^ 2 / 2 * NQ a σ := mul_le_mul_of_nonneg_right hKB hQ0
    have h5 : 0 ≤ K₅ * B * NG σ := by positivity
    constructor <;> nlinarith
  have hG : NG σ = 0 := by
    have h1 := hspan σ hσ₀σ
    have h2 : σ ^ 2 * ∑ a, NQ a σ ≤ c * (2 * K₅ * B * NG σ) := by
      rw [mul_sum]
      calc ∑ a, σ ^ 2 * NQ a σ ≤ ∑ _a : ι, 2 * K₅ * B * NG σ := sum_le_sum fun a _ => (hQP a).1
        _ = _ := by simp [c]
    have h3 : σ ^ 2 * NG σ ≤ K₆ * (c * (2 * K₅ * B * NG σ)) := by
      have := mul_le_mul_of_nonneg_left h1 (sq_nonneg σ)
      nlinarith [mul_le_mul_of_nonneg_left h2 hK₆]
    have h4 : 2 * K₆ * c * 2 * K₅ * B ≤ σ ^ 2 - 1 := by nlinarith
    have h5 : σ ^ 2 * NG σ ≤ (σ ^ 2 - 1) / 2 * NG σ := by
      have : K₆ * (c * (2 * K₅ * B * NG σ)) = (2 * K₆ * c * 2 * K₅ * B) / 2 * NG σ := by ring
      rw [this] at h3
      exact h3.trans (mul_le_mul_of_nonneg_right (by linarith) hG0)
    nlinarith
  refine ⟨hG, le_antisymm (by simpa [hG] using hΘ) hΘ0, fun a => ?_⟩
  obtain ⟨hP0, hQ0, -⟩ := hN0 a
  obtain ⟨h1, h2⟩ := hQP a
  rw [hG, mul_zero] at h1 h2
  have hσ2 : 0 < σ ^ 2 := by positivity
  have hσ4' : 0 < σ ^ 4 := by positivity
  exact ⟨le_antisymm (nonpos_of_mul_nonpos_right (by linarith) hσ4') hP0,
    le_antisymm (nonpos_of_mul_nonpos_right (by linarith) hσ2) hQ0⟩

end LorentzianCalderon
