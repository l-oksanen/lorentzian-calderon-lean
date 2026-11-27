module

public import LorentzianCalderon.Induction.StepC
public import LorentzianCalderon.Induction.Unique

public section

/-!
# The induction

Blueprint, Lemma `lem_induction`: under the standing assumptions, `P(τ)` (`ExtensionProperty`)
holds for every `τ`. Step A (start) is `extensionProperty_id`, Step B (closedness) is
`exists_extensionProperty_of_forall_gt`, and Step C (extension) is
`ExtensionProperty.exists_extend_below` (`Induction/StepC.lean`). Maps with the extension
property at different levels are glued with `ExtensionProperty.of_local` and `eqOn_glue`.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Filter

variable {n : ℕ} {T : ℝ} {g g' : MatrixField n} {Y Y' : E n → E n} {ψ : E n → ℝ}
  {Φ : ℝ → E n → E n} {τ : ℝ}

/-! ### Gluing -/

lemma D_congr {F G : E n → E n} {x : E n} (h : F =ᶠ[𝓝 x] G) : D F x = D G x := by
  ext i j
  simp only [D_def, h.fderiv_eq]

/-- A map that agrees near each point of `A_τ` with a map having the extension property at a
lower level has the extension property at level `τ`. -/
theorem ExtensionProperty.of_local {W : Set (E n)} (hψ : Continuous ψ) {G : E n → E n}
    (h : ∀ x ∈ A ψ τ, ∃ σ < ψ x, ∃ Ψ', ExtensionProperty g g' ψ W σ Ψ' ∧ EqOn G Ψ' (A ψ σ)) :
    ExtensionProperty g g' ψ W τ G := by
  have key : ∀ x ∈ A ψ τ, ∃ Ψ', ContDiffAt ℝ ∞ Ψ' x ∧ G =ᶠ[𝓝 x] Ψ' ∧
      g x = (D Ψ' x)ᵀ * g' (Ψ' x) * D Ψ' x ∧ (x ∉ W → Ψ' x = x) := by
    intro x hx
    obtain ⟨σ, hσ, Ψ', hP, heq⟩ := h x hx
    have hmem : A ψ σ ∈ 𝓝 x := (isOpen_A hψ σ).mem_nhds (mem_A.2 hσ)
    exact ⟨Ψ', hP.smooth.contDiffAt hmem, eventually_of_mem hmem fun y hy => heq hy,
      hP.pullback x (mem_A.2 hσ), hP.eq_self x (mem_A.2 hσ)⟩
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx hxW => ?_⟩ <;>
    obtain ⟨Ψ', hc, hev, hpull, hself⟩ := key x hx
  · exact (hc.congr_of_eventuallyEq hev).contDiffWithinAt
  · rw [D_congr hev, hev.eq_of_nhds]
    exact hpull
  · rw [hev.eq_of_nhds]
    exact hself hxW

section Glue

variable (hg : IsSpacetime g Y) (hg' : IsSpacetime g' Y') (hψ : Continuous ψ)
  (hΦ : Continuous fun p : ℝ × E n => Φ p.1 p.2) (hΦ0 : ∀ x, Φ 0 x = x)
  (hΦψ : ∀ t x, ψ (Φ t x) = ψ x + t)
include hg hg' hψ hΦ hΦ0 hΦψ

/-- Uniqueness of the extension (`lem_extension_unique`) for two levels. -/
theorem ExtensionProperty.eqOn_max {τ₁ τ₂ : ℝ} {Ψ₁ Ψ₂ : E n → E n}
    (h₁ : ExtensionProperty g g' ψ (W n T) τ₁ Ψ₁) (h₂ : ExtensionProperty g g' ψ (W n T) τ₂ Ψ₂) :
    EqOn Ψ₁ Ψ₂ (A ψ (max τ₁ τ₂)) :=
  (h₁.mono (le_max_left _ _)).eqOn (h₂.mono (le_max_right _ _)) hg hg' hψ isClosed_W
    (isConnected_A hψ hΦ hΦ0 hΦψ _).isPreconnected (nonempty_A_diff hψ hΦψ isCompact_W _)

/-- Maps `F σ` with the extension property at the levels `σ ∈ I`, evaluated at levels `ℓ x`
below `ψ x`, glue to a map that agrees with each `F σ` on `A_σ`. -/
theorem eqOn_glue {I : Set ℝ} {F : ℝ → E n → E n}
    (hF : ∀ σ ∈ I, ExtensionProperty g g' ψ (W n T) σ (F σ)) {ℓ : E n → ℝ} {σ : ℝ} (hσ : σ ∈ I)
    (hℓ : ∀ x ∈ A ψ σ, ℓ x ∈ I ∧ ℓ x < ψ x) :
    EqOn (fun x => F (ℓ x) x) (F σ) (A ψ σ) := fun x hx =>
  (hF _ (hℓ x hx).1).eqOn_max hg hg' hψ hΦ hΦ0 hΦψ (hF σ hσ)
    (mem_A.2 (show max (ℓ x) σ < ψ x from max_lt (hℓ x hx).2 (mem_A.1 hx)))

/-- The glued map has the extension property at every level above which the levels `ℓ x` are
admissible. -/
theorem extensionProperty_glue {I : Set ℝ} {F : ℝ → E n → E n}
    (hF : ∀ σ ∈ I, ExtensionProperty g g' ψ (W n T) σ (F σ)) {ℓ : E n → ℝ}
    (hℓ : ∀ x ∈ A ψ τ, ℓ x ∈ I ∧ ℓ x < ψ x)
    (hℓ' : ∀ x ∈ A ψ τ, ∀ y ∈ A ψ (ℓ x), ℓ y ∈ I ∧ ℓ y < ψ y) :
    ExtensionProperty g g' ψ (W n T) τ (fun x => F (ℓ x) x) :=
  ExtensionProperty.of_local hψ fun x hx => ⟨ℓ x, (hℓ x hx).2, F (ℓ x), hF _ (hℓ x hx).1,
    eqOn_glue hg hg' hψ hΦ hΦ0 hΦψ hF (hℓ x hx).1 (hℓ' x hx)⟩

/-! ### Steps A and B -/

omit hg hg' hψ hΦ hΦ0 hΦψ in
/-- **Step A** (start): above `max_W ψ`, the identity has the extension property. -/
theorem extensionProperty_id (hgA : IsAdmissibleMetric n T g) (hg'A : IsAdmissibleMetric n T g')
    (hτ : ∀ x ∈ W n T, ψ x ≤ τ) : ExtensionProperty g g' ψ (W n T) τ id := by
  refine ⟨contDiff_id.contDiffOn, fun x hx => ?_, fun x _ _ => rfl⟩
  have hxM : x ∉ M0 n T := fun h => (not_le.2 (mem_A.1 hx)) (hτ x (M0_subset_W h))
  rw [D_id, hgA.minkowski_exterior x hxM, id, hg'A.minkowski_exterior x hxM]
  simp

/-- **Step B** (closedness): if `P(τ)` holds for all `τ > τ₀`, then `P(τ₀)` holds. -/
theorem exists_extensionProperty_of_forall_gt {τ₀ : ℝ}
    (h : ∀ τ > τ₀, ∃ Ψ, ExtensionProperty g g' ψ (W n T) τ Ψ) :
    ∃ Ψ, ExtensionProperty g g' ψ (W n T) τ₀ Ψ := by
  choose F hF using h
  set F' : ℝ → E n → E n := fun σ => if hσ : τ₀ < σ then F σ hσ else id
  have hF' : ∀ σ ∈ Ioi τ₀, ExtensionProperty g g' ψ (W n T) σ (F' σ) := fun σ hσ => by
    have hσ' : τ₀ < σ := hσ
    have : F' σ = F σ hσ' := by simp [F', hσ']
    exact this ▸ hF σ hσ
  have hℓ : ∀ y : E n, τ₀ < ψ y → (τ₀ + ψ y) / 2 ∈ Ioi τ₀ ∧ (τ₀ + ψ y) / 2 < ψ y :=
    fun y hy => ⟨show τ₀ < _ by linarith, by linarith⟩
  exact ⟨_, extensionProperty_glue hg hg' hψ hΦ hΦ0 hΦψ hF' (fun x hx => hℓ x (mem_A.1 hx))
    fun x hx y hy => hℓ y (lt_trans (hℓ x (mem_A.1 hx)).1 (mem_A.1 hy))⟩

end Glue

/-! ### The induction -/

/-- **The induction** (blueprint, `lem_induction`): under the standing assumptions, `P(τ)` holds
for every `τ`. -/
theorem exists_extensionProperty (hgA : IsAdmissibleMetric n T g)
    (hg'A : IsAdmissibleMetric n T g') (hg : IsSpacetime g Y) (hg' : IsSpacetime g' Y')
    (hY : ∀ x ∉ M0 n T, form (g x) (EuclideanSpace.single 0 1) (Y x) < 0)
    (hY' : ∀ x ∉ M0 n T, form (g' x) (EuclideanSpace.single 0 1) (Y' x) < 0)
    (hC : CauchyDataSubset n T g g') (hψ' : IsCauchyTemporal g Y ψ)
    (hΦ : ContDiff ℝ ∞ fun p : ℝ × E n => Φ p.1 p.2) (hΦ0 : ∀ x, Φ 0 x = x)
    (hΦψ : ∀ t x, ψ (Φ t x) = ψ x + t) (τ : ℝ) :
    ∃ Ψ, ExtensionProperty g g' ψ (W n T) τ Ψ := by
  have hψ := hψ'.smooth.continuous
  set S := { σ : ℝ | ∃ Ψ, ExtensionProperty g g' ψ (W n T) σ Ψ }
  have hup : ∀ σ ∈ S, ∀ σ', σ ≤ σ' → σ' ∈ S := fun σ ⟨Ψ, hP⟩ σ' h => ⟨Ψ, hP.mono h⟩
  obtain ⟨M, hM⟩ := (isCompact_W.image hψ).bddAbove
  have hMS : M ∈ S := ⟨id, extensionProperty_id hgA hg'A fun x hx => hM (mem_image_of_mem ψ hx)⟩
  by_contra hτ
  have hbdd : BddBelow S := ⟨τ, fun σ hσ => le_of_not_ge fun h => hτ (hup σ hσ τ h)⟩
  set τ₀ := sInf S
  have hτ₀ : τ₀ ∈ S := exists_extensionProperty_of_forall_gt hg hg' hψ hΦ.continuous hΦ0 hΦψ
    fun σ hσ => by
      obtain ⟨σ', hσ'S, hσ'⟩ := exists_lt_of_csInf_lt ⟨M, hMS⟩ hσ
      exact hup σ' hσ'S σ hσ'.le
  obtain ⟨Ψ, hP⟩ := hτ₀
  obtain ⟨δ, hδ, hS⟩ := hP.exists_extend_below hgA hg'A hg hg' hY hY' hC hψ' hΦ hΦ0 hΦψ
  have := csInf_le hbdd hS
  linarith

end

end LorentzianCalderon
