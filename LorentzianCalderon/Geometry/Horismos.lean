module

public import LorentzianCalderon.Geometry.PushUp
public import LorentzianCalderon.Geometry.Junction
public import LorentzianCalderon.Causal.Steep

public section

/-!
# Null geodesics between horismos-related points

If `p ≤ q`, `p ≠ q` and not `p ≪ q`, a causal curve from `p` to `q` is a null pregeodesic
(`Facts.chronLT_of_not_nullPregeodesic`), so `p` and `q` are joined by a future null geodesic
(`Facts.exists_causal_geodesic`).
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Filter

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n}

/-- Points `p ≤ q`, `p ≠ q`, with `p ≪ q` false are joined by a future null geodesic. O'Neill,
Semi-Riemannian geometry, Proposition 14.19, p. 411, and Lemma 14.16, p. 410, in the case that
the points are not chronologically related, where the maximal geodesic is null; here it is
obtained from Proposition 10.46 (`Facts.chronLT_of_not_nullPregeodesic`) instead. -/
theorem Facts.exists_causal_geodesic (hg : IsSpacetime g Y) {p q : E n}
    (hpq : CausalLE g Y p q) (hne : p ≠ q) (hnot : ¬ ChronLT g Y p q) :
    ∃ (σ : ℝ → E n) (I : Set ℝ), IsGeodesic g σ I ∧ Icc 0 1 ⊆ I ∧ σ 0 = p ∧ σ 1 = q ∧
      (∀ t ∈ Icc (0 : ℝ) 1, IsFutureCausal g Y (σ t) (deriv σ t)) ∧
      ∀ t ∈ I, form (g (σ t)) (deriv σ t) (deriv σ t) = 0 := by
  obtain ⟨γ, hγ, rfl, rfl⟩ := CausalLE.exists_isPathOn hpq hne zero_lt_one
  obtain ⟨τ, I', h, hτ, hnull, hhm, hhc, hhI, hγτ⟩ :=
    isNullPregeodesicOn_iff.1 <| show IsNullPregeodesicOn g 0 1 γ by
    by_contra hn
    exact hnot (Facts.chronLT_of_not_nullPregeodesic hg hγ hn)
  have h0 := hγτ 0 ⟨le_rfl, zero_le_one⟩
  have h1 := hγτ 1 ⟨zero_le_one, le_rfl⟩
  set a := h 0
  set b := h 1
  have hab' : a ≤ b := hhm (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one) zero_le_one
  have hab : a < b := lt_of_le_of_ne hab' fun e => hne (by rw [h0, h1, e])
  have hJ : Icc a b ⊆ I' := fun y hy => hhI (intermediate_value_Icc zero_le_one hhc hy)
  have ha : a ∈ Icc a b := left_mem_Icc.2 hab'
  have hτa0 : deriv τ a ≠ 0 := by
    intro h0'
    have := (IsGeodesic.eqOn hg hτ (isGeodesic_const (τ a)) hJ (subset_univ _) ordConnected_Icc
      ha rfl (by rw [h0', deriv_const])).1 (right_mem_Icc.2 hab')
    exact hne (by rw [h0, h1]; exact this.symm)
  have hcaus : form (g (τ a)) (deriv τ a) (deriv τ a) ≤ 0 := (hnull a (hJ ha)).le
  have hYt := hg.globallyHyperbolic.timeOrientation.timelike (τ a)
  have hfut : IsFutureCausal g Y (τ a) (deriv τ a) := by
    refine ⟨hτa0, hcaus, lt_of_le_of_ne (not_lt.1 fun hpos => ?_)
      ((hg.lorentzian (τ a)).form_ne_zero hcaus hτa0 hYt)⟩
    obtain ⟨ψ, hψ⟩ := exists_lt_of_causalLE hg
    have hρ := hτ.comp_affine (-1) 0
    have hJρ : Icc (-b) (-a) ⊆ (fun s => -1 * s + 0) ⁻¹' I' := fun s hs =>
      hJ ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hρa : deriv (fun s => τ (-1 * s + 0)) (-a) = -deriv τ a := by
      rw [hτ.deriv_comp_affine (by simpa using hJ ha)]
      simp
    have hfρ : IsFutureCausal g Y (τ (-1 * -a + 0)) (deriv (fun s => τ (-1 * s + 0)) (-a)) := by
      rw [hρa, show -1 * -a + 0 = a by ring]
      refine ⟨neg_ne_zero.2 hτa0, by simpa [form_neg_left, form_neg_right] using hcaus, ?_⟩
      rw [form_neg_left]
      linarith
    have hle := hρ.causalLE (a := -b) (b := -a) (by linarith) hJρ fun t ht =>
      hρ.isFutureCausal hg hJρ ordConnected_Icc (right_mem_Icc.2 (by linarith)) hfρ ht
    simp only [neg_mul, one_mul, neg_neg, add_zero] at hle
    have e1 := hψ _ _ hpq hne
    have e2 := hψ _ _ hle fun e => hne (by rw [h0, h1, e])
    rw [h0, h1] at e1
    linarith
  set σ := fun s => τ ((b - a) * s + a) with hσ_def
  have hσ := hτ.comp_affine (b - a) a
  have hI : Icc 0 1 ⊆ (fun s => (b - a) * s + a) ⁻¹' I' := fun s hs =>
    hJ ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
  have hσ0' : IsFutureCausal g Y (σ 0) (deriv σ 0) := by
    rw [hτ.deriv_comp_affine (by simpa using hJ ha)]
    simp only [σ, mul_zero, zero_add]
    exact hfut.smul (sub_pos.2 hab)
  refine ⟨σ, _, hσ, hI, by simp [σ, h0], by simp [σ, h1], fun t ht =>
    hσ.isFutureCausal hg hI ordConnected_Icc (left_mem_Icc.2 zero_le_one) hσ0' ht,
    fun t ht => ?_⟩
  rw [hτ.deriv_comp_affine ht, form_smul_left, form_smul_right, hnull _ ht, mul_zero, mul_zero]

end

end LorentzianCalderon
