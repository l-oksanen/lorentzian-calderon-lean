module

public import LorentzianCalderon.Geometry.NullPregeodesic
public import LorentzianCalderon.Geometry.Exp
public import LorentzianCalderon.Green.Temporal
public import LorentzianCalderon.Facts.Temporal

public section

/-!
# Junctions of causal geodesics

* A future causal geodesic segment is never closed (`IsGeodesic.apply_ne_of_isFutureCausal`).
* Two future causal geodesic segments whose concatenation is not chronological meet with
  positively proportional velocities (`exists_pos_smul_of_not_chronLT`).
* First arrival: if `σ(0) ≪ σ(b)` fails along the future causal geodesic `σ`, then `σ(t)`,
  `0 < t < b`, is reached by `exp_{σ(0)}` on future causal vectors only at `t σ̇(0)`
  (`eq_smul_of_expMap_eq`).
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Filter

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n}

/-- A future causal geodesic segment is not closed. -/
theorem IsGeodesic.apply_ne_of_isFutureCausal (hg : IsSpacetime g Y) {γ : ℝ → E n} {I : Set ℝ}
    (hγ : IsGeodesic g γ I) {a b : ℝ} (hab : a < b) (hI : Icc a b ⊆ I)
    (hf : IsFutureCausal g Y (γ a) (deriv γ a)) : γ a ≠ γ b := by
  intro hγab
  have hfut : ∀ t ∈ Icc a b, IsFutureCausal g Y (γ t) (deriv γ t) := fun t ht =>
    hγ.isFutureCausal hg hI ordConnected_Icc (left_mem_Icc.2 hab.le) hf ht
  obtain ⟨ψ, hψs, hψ⟩ := Facts.exists_temporal hg
  have := lt_of_isPathOn hg (hψs.differentiable (by simp)) hψ (hγ.isPathOn hab hI hfut)
  rw [hγab] at this
  exact lt_irrefl _ this

/-- Two future causal geodesic segments, `γ₁` on `[a, m]` and `γ₂` on `[m, b]`, with
`γ₁ m = γ₂ m`, concatenate to a future causal path on `[a, b]`. -/
theorem IsGeodesic.isPathOn_append (hg : IsSpacetime g Y) {γ₁ γ₂ : ℝ → E n} {I₁ I₂ : Set ℝ}
    (h₁ : IsGeodesic g γ₁ I₁) (h₂ : IsGeodesic g γ₂ I₂) {a m b : ℝ} (ham : a < m) (hmb : m < b)
    (hI₁ : Icc a m ⊆ I₁) (hI₂ : Icc m b ⊆ I₂) (hf₁ : IsFutureCausal g Y (γ₁ a) (deriv γ₁ a))
    (hf₂ : IsFutureCausal g Y (γ₂ m) (deriv γ₂ m)) (hjoin : γ₁ m = γ₂ m) :
    IsPathOn (IsFutureCausal g Y) a b (fun t => if t ≤ m then γ₁ t else γ₂ t) :=
  (h₁.isPathOn ham hI₁ fun _ ht =>
      h₁.isFutureCausal hg hI₁ ordConnected_Icc (left_mem_Icc.2 ham.le) hf₁ ht).append
    (h₂.isPathOn hmb hI₂ fun _ ht =>
      h₂.isFutureCausal hg hI₂ ordConnected_Icc (left_mem_Icc.2 hmb.le) hf₂ ht) hjoin

/-- Junction of causal geodesics: two future causal geodesic segments whose concatenation is not
chronological meet with positively proportional velocities. -/
theorem exists_pos_smul_of_not_chronLT (hg : IsSpacetime g Y) {γ₁ γ₂ : ℝ → E n}
    {I₁ I₂ : Set ℝ} (h₁ : IsGeodesic g γ₁ I₁) (h₂ : IsGeodesic g γ₂ I₂) {a₁ b₁ a₂ b₂ : ℝ}
    (hab₁ : a₁ < b₁) (hab₂ : a₂ < b₂) (hI₁ : Icc a₁ b₁ ⊆ I₁) (hI₂ : Icc a₂ b₂ ⊆ I₂)
    (hf₁ : IsFutureCausal g Y (γ₁ a₁) (deriv γ₁ a₁))
    (hf₂ : IsFutureCausal g Y (γ₂ a₂) (deriv γ₂ a₂)) (hjoin : γ₁ b₁ = γ₂ a₂)
    (hnot : ¬ ChronLT g Y (γ₁ a₁) (γ₂ b₂)) : ∃ κ > (0 : ℝ), deriv γ₁ b₁ = κ • deriv γ₂ a₂ := by
  set c₁ := 2 * (b₁ - a₁)
  set c₂ := 2 * (b₂ - a₂)
  set d₂ := 2 * a₂ - b₂
  have hc₁ : 0 < c₁ := by simp only [c₁]; linarith
  have hc₂ : 0 < c₂ := by simp only [c₂]; linarith
  have e₁0 : c₁ * 0 + a₁ = a₁ := by ring
  have e₁ : c₁ * (1 / 2) + a₁ = b₁ := by simp only [c₁]; ring
  have e₂ : c₂ * (1 / 2) + d₂ = a₂ := by simp only [c₂, d₂]; ring
  have e₂1 : c₂ * 1 + d₂ = b₂ := by simp only [c₂, d₂]; ring
  have hI₁' : Icc 0 (1 / 2) ⊆ (fun s => c₁ * s + a₁) ⁻¹' I₁ := fun t ht =>
    hI₁ ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  have hI₂' : Icc (1 / 2) 1 ⊆ (fun s => c₂ * s + d₂) ⁻¹' I₂ := fun t ht =>
    hI₂ ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  have hb₁ : b₁ ∈ I₁ := hI₁ (right_mem_Icc.2 hab₁.le)
  have ha₂ : a₂ ∈ I₂ := hI₂ (left_mem_Icc.2 hab₂.le)
  have hd₁ : HasDerivAt (fun s => γ₁ (c₁ * s + a₁)) (c₁ • deriv γ₁ b₁) (1 / 2) := by
    have := h₁.hasDerivAt_comp_affine (s := 1 / 2) (by rw [e₁]; exact hb₁)
    rwa [e₁] at this
  have hd₂ : HasDerivAt (fun s => γ₂ (c₂ * s + d₂)) (c₂ • deriv γ₂ a₂) (1 / 2) := by
    have := h₂.hasDerivAt_comp_affine (s := 1 / 2) (by rw [e₂]; exact ha₂)
    rwa [e₂] at this
  have hf₁' : IsFutureCausal g Y (γ₁ (c₁ * 0 + a₁)) (deriv (fun s => γ₁ (c₁ * s + a₁)) 0) := by
    rw [h₁.deriv_comp_affine (by rw [e₁0]; exact hI₁ (left_mem_Icc.2 hab₁.le)), e₁0]
    exact hf₁.smul hc₁
  have hf₂' : IsFutureCausal g Y (γ₂ (c₂ * (1 / 2) + d₂))
      (deriv (fun s => γ₂ (c₂ * s + d₂)) (1 / 2)) := by
    rw [hd₂.deriv, e₂]
    exact hf₂.smul hc₂
  set γ := fun t : ℝ => if t ≤ 1 / 2 then γ₁ (c₁ * t + a₁) else γ₂ (c₂ * t + d₂)
  have hpath : IsPathOn (IsFutureCausal g Y) 0 1 γ :=
    (h₁.comp_affine c₁ a₁).isPathOn_append hg (h₂.comp_affine c₂ d₂) (by norm_num)
      (by norm_num) hI₁' hI₂' hf₁' hf₂' (by simp only [e₁, e₂, hjoin])
  have hγ0 : γ 0 = γ₁ a₁ := by simp [γ]
  have hγm : γ (1 / 2) = γ₁ b₁ := by simp only [γ, le_refl, ite_true, e₁]
  obtain ⟨σ, I', h, hσ, -, hhm, hhc, hhI, hγσ⟩ :=
    isNullPregeodesicOn_iff.1 <| show IsNullPregeodesicOn g 0 1 γ by
    by_contra hn
    apply hnot
    have := Facts.chronLT_of_not_nullPregeodesic hg hpath hn
    have hγ1 : γ 1 = γ₂ b₂ := by simp only [γ, e₂1]; norm_num
    rwa [hγ0, hγ1] at this
  have hm : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hp : h (1 / 2) ∈ I' := hhI ⟨1 / 2, hm, rfl⟩
  have hσd : HasStrictDerivAt σ (deriv σ (h (1 / 2))) (h (1 / 2)) :=
    (hσ.smooth.contDiffAt (hσ.isOpen.mem_nhds hp)).hasStrictDerivAt (by simp)
  have hσ' : deriv σ (h (1 / 2)) ≠ 0 := by
    intro h0
    have hJ : Icc (h 0) (h 1) ⊆ I' := fun y hy => hhI (intermediate_value_Icc zero_le_one hhc hy)
    have h01 : h 0 ∈ Icc (h 0) (h 1) := left_mem_Icc.2 (hhm (left_mem_Icc.2 zero_le_one)
      (right_mem_Icc.2 zero_le_one) zero_le_one)
    have hpJ : h (1 / 2) ∈ Icc (h 0) (h 1) := ⟨hhm (left_mem_Icc.2 zero_le_one) hm hm.1,
      hhm hm (right_mem_Icc.2 zero_le_one) hm.2⟩
    have hc := (IsGeodesic.eqOn hg hσ (isGeodesic_const (σ (h (1 / 2)))) hJ (subset_univ _)
      ordConnected_Icc hpJ rfl (by rw [h0, deriv_const])).1 h01
    refine h₁.apply_ne_of_isFutureCausal hg hab₁ hI₁ hf₁ ?_
    rw [← hγ0, ← hγm, hγσ 0 (left_mem_Icc.2 zero_le_one), hγσ _ hm]
    exact hc
  have hne₁ : deriv γ₁ b₁ ≠ 0 := (h₁.isFutureCausal hg hI₁ ordConnected_Icc
    (left_mem_Icc.2 hab₁.le) hf₁ (right_mem_Icc.2 hab₁.le)).ne_zero
  obtain ⟨κ₁, hκ₁, e1⟩ := exists_pos_smul_of_eq_comp (by norm_num : (0 : ℝ) < 1 / 2)
    (right_mem_Icc.2 (by norm_num)) hd₁.hasDerivWithinAt hσd
    (hhm.mono (Icc_subset_Icc le_rfl hm.2))
    ((hhc _ hm).mono (Icc_subset_Icc le_rfl hm.2))
    (fun t ht => by
      rw [← hγσ t ⟨ht.1, ht.2.trans hm.2⟩]
      simp only [γ, ht.2, ite_true])
    (smul_ne_zero hc₁.ne' hne₁) hσ'
  obtain ⟨κ₂, hκ₂, e2⟩ := exists_pos_smul_of_eq_comp (by norm_num : (1 / 2 : ℝ) < 1)
    (left_mem_Icc.2 (by norm_num)) hd₂.hasDerivWithinAt hσd
    (hhm.mono (Icc_subset_Icc hm.1 le_rfl))
    ((hhc _ hm).mono (Icc_subset_Icc hm.1 le_rfl))
    (fun t ht => by
      rw [← hγσ t ⟨hm.1.trans ht.1, ht.2⟩]
      simp only [γ]
      split_ifs with hle
      · obtain rfl : t = 1 / 2 := le_antisymm hle ht.1
        rw [e₁, e₂, hjoin]
      · rfl)
    (smul_ne_zero hc₂.ne' hf₂.ne_zero) hσ'
  refine ⟨c₁⁻¹ * κ₁ * (κ₂⁻¹ * c₂), by positivity, ?_⟩
  have e1' : deriv γ₁ b₁ = (c₁⁻¹ * κ₁) • deriv σ (h (1 / 2)) := by
    rw [mul_smul, ← e1, smul_smul, inv_mul_cancel₀ hc₁.ne', one_smul]
  have e2' : deriv σ (h (1 / 2)) = (κ₂⁻¹ * c₂) • deriv γ₂ a₂ := by
    rw [mul_smul, e2, smul_smul, inv_mul_cancel₀ hκ₂.ne', one_smul]
  rw [e1', e2', smul_smul]

/-- First arrival: if `σ(b)` is not in the chronological future of `σ(0)` along the future
causal geodesic `σ`, then for `0 < t < b` the only future causal vector `w` with
`exp_{σ(0)} w = σ(t)` is `t σ̇(0)`. -/
theorem eq_smul_of_expMap_eq (hg : IsSpacetime g Y) {σ : ℝ → E n} {I : Set ℝ} {b : ℝ}
    (hσ : IsGeodesic g σ I) (hI : Icc 0 b ⊆ I) (hfut : IsFutureCausal g Y (σ 0) (deriv σ 0))
    (hfirst : ¬ ChronLT g Y (σ 0) (σ b)) {t : ℝ} (ht : t ∈ Ioo 0 b) {w : E n}
    (hw : IsFutureCausal g Y (σ 0) w) (hdom : InExpDomain g (σ 0) w)
    (hexp : expMap g (σ 0) w = σ t) : w = t • deriv σ 0 := by
  obtain ⟨ε, hε, hc, -, hc0, hc'0⟩ := hdom.isGeodesic_expMap_smul hg
  set c := fun r : ℝ => expMap g (σ 0) (r • w)
  have hc0' : c 0 = σ 0 := hc0
  have hIc : Icc 0 1 ⊆ Ioo (-ε) (1 + ε) := fun r hr => ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hcf : IsFutureCausal g Y (c 0) (deriv c 0) := by rw [hc0', hc'0]; exact hw
  have hc1 : c 1 = σ t := by simp [c, hexp]
  have hσt : IsFutureCausal g Y (σ t) (deriv σ t) := hσ.isFutureCausal hg hI ordConnected_Icc
    (left_mem_Icc.2 (ht.1.trans ht.2).le) hfut ⟨ht.1.le, ht.2.le⟩
  obtain ⟨κ, hκ, hcκ⟩ := exists_pos_smul_of_not_chronLT hg hc hσ zero_lt_one ht.2 hIc
    ((Icc_subset_Icc ht.1.le le_rfl).trans hI) hcf hσt hc1 (by rwa [hc0'])
  have hσ' := hσ.comp_affine κ (t - κ)
  have key : ∀ r₀, 0 ≤ r₀ → r₀ ≤ 1 → 0 ≤ κ * r₀ + (t - κ) →
      EqOn c (fun r => σ (κ * r + (t - κ))) (Icc r₀ 1) ∧
        EqOn (deriv c) (deriv fun r => σ (κ * r + (t - κ))) (Icc r₀ 1) := by
    intro r₀ hr₀ hr₀1 hκr₀
    have hJ : Icc r₀ 1 ⊆ (fun r => κ * r + (t - κ)) ⁻¹' I := fun r hr =>
      hI ⟨by nlinarith [hr.1], by nlinarith [hr.2, ht.2]⟩
    have e1 : κ * 1 + (t - κ) = t := by ring
    refine IsGeodesic.eqOn hg hc hσ' ((Icc_subset_Icc hr₀ le_rfl).trans hIc) hJ ordConnected_Icc
      (right_mem_Icc.2 hr₀1) (by simp only [hc1, e1]) ?_
    rw [hσ.deriv_comp_affine (by rw [e1]; exact hI ⟨ht.1.le, ht.2.le⟩), e1, hcκ]
  rcases lt_or_ge t κ with hlt | hle
  · set r₀ := 1 - t / κ
    have hr₀ : 0 < r₀ := by simp only [r₀]; rw [sub_pos, div_lt_one hκ]; exact hlt
    have hr₀1 : r₀ ≤ 1 := by simp only [r₀]; linarith [div_pos ht.1 hκ]
    have e0 : κ * r₀ + (t - κ) = 0 := by simp only [r₀]; field_simp; ring
    have h := (key r₀ hr₀.le hr₀1 e0.ge).1 (left_mem_Icc.2 hr₀1)
    refine absurd ?_ (hc.apply_ne_of_isFutureCausal hg hr₀
      ((Icc_subset_Icc le_rfl hr₀1).trans hIc) hcf)
    rw [h, hc0']
    simp only [e0]
  · have e0 : κ * 0 + (t - κ) = t - κ := by ring
    obtain ⟨h0, h0'⟩ := key 0 le_rfl zero_le_one (by rw [e0]; linarith)
    rcases hle.lt_or_eq with hlt | rfl
    · refine absurd ?_ (hσ.apply_ne_of_isFutureCausal hg (sub_pos.2 hlt)
        ((Icc_subset_Icc le_rfl (by linarith [ht.2])).trans hI) hfut)
      rw [← hc0', h0 (left_mem_Icc.2 zero_le_one)]
      simp only [e0]
    · rw [← hc'0, h0' (left_mem_Icc.2 zero_le_one),
        hσ.deriv_comp_affine (by
          rw [e0, sub_self]
          exact hI (left_mem_Icc.2 (by linarith [ht.1, ht.2]))), e0, sub_self]

end

end LorentzianCalderon
