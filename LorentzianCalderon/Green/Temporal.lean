module

public import LorentzianCalderon.Causal.Basic
public import LorentzianCalderon.Local.Differential

public section

/-!
# Temporal functions increase along causal curves

A smooth function `ψ` with `-grad ψ` future-directed timelike increases strictly along causal
curves, by the reverse sign lemma `IsFutureTimelike.form_neg`.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Filter

variable {n : ℕ}

section Sign

variable {g : MatrixField n} {Y : E n → E n} {x N v : E n}

theorem fderiv_eq_form_grad {ψ : E n → ℝ} (hL : IsLorentzian (g x)) (v : E n) :
    fderiv ℝ ψ x v = form (g x) (grad g ψ x) v := by
  have hdet : IsUnit (g x).det := hL.det_neg.ne.isUnit
  have hgrad : (grad g ψ x).ofLp = (g x)⁻¹ *ᵥ d ψ x := by
    ext j
    simp [grad_def, Matrix.mulVec, dotProduct]
  rw [form_eq_dotProduct, hgrad, fderiv_apply_eq_sum_d, dotProduct_comm, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, Matrix.transpose_nonsing_inv, hL.symm, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  simp [dotProduct, mul_comm]

/-- A function whose negative gradient is future-directed timelike has positive derivative in
future-directed causal directions. -/
theorem fderiv_pos_of_isFutureCausal (hL : IsLorentzian (g x))
    (hY : form (g x) (Y x) (Y x) < 0) {ψ : E n → ℝ}
    (hψ : IsFutureTimelike g Y x (-grad g ψ x)) (hv : IsFutureCausal g Y x v) :
    0 < fderiv ℝ ψ x v := by
  have h := hψ.form_neg hL hY hv
  rw [form_neg_left, ← fderiv_eq_form_grad hL] at h
  linarith

/-- A Cauchy temporal function increases in future-directed causal directions. -/
theorem IsCauchyTemporal.fderiv_pos {ψ : E n → ℝ} (hg : IsSpacetime g Y)
    (hψ : IsCauchyTemporal g Y ψ) (hv : IsFutureCausal g Y x v) : 0 < fderiv ℝ ψ x v :=
  fderiv_pos_of_isFutureCausal (hg.lorentzian x) (hg.globallyHyperbolic.timeOrientation.timelike x)
    (hψ.past_gradient x) hv

end Sign

section Monotone

variable {g : MatrixField n} {Y : E n → E n} {ψ : E n → ℝ} {p q : E n}

/-- A function whose negative gradient is future-directed timelike increases strictly along
causal paths. -/
theorem lt_of_isPathOn (hg : IsSpacetime g Y) (hψd : Differentiable ℝ ψ)
    (hψ : ∀ x, IsFutureTimelike g Y x (-grad g ψ x)) {a b : ℝ} {γ : ℝ → E n}
    (hγ : IsPathOn (IsFutureCausal g Y) a b γ) : ψ (γ a) < ψ (γ b) := by
  obtain ⟨k, s, hs, hγ⟩ := isPathOn_def.1 hγ
  have hpiece : ∀ i : Fin (k + 1), ψ (γ (s i.castSucc)) < ψ (γ (s i.succ)) := by
    intro i
    have hlt : s i.castSucc < s i.succ := hs.strictMono i.castSucc_lt_succ
    have hsm := hγ.smooth i
    have hvel := hγ.velocity i
    rw [piece_def] at hsm hvel
    have hmono : StrictMonoOn (ψ ∘ γ) (Icc (s i.castSucc) (s i.succ)) := by
      refine strictMonoOn_of_deriv_pos (convex_Icc _ _)
        (hψd.continuous.comp_continuousOn hsm.continuousOn) fun t ht => ?_
      rw [interior_Icc] at ht
      have htI : t ∈ Icc (s i.castSucc) (s i.succ) := Ioo_subset_Icc_self ht
      have hγt : HasDerivAt γ (derivWithin γ (Icc (s i.castSucc) (s i.succ)) t) t :=
        ((hsm.differentiableOn (by simp) t htI).hasDerivWithinAt).hasDerivAt
          (Icc_mem_nhds ht.1 ht.2)
      rw [((hψd (γ t)).hasFDerivAt.comp_hasDerivAt t hγt).deriv]
      exact fderiv_pos_of_isFutureCausal (hg.lorentzian _)
        (hg.globallyHyperbolic.timeOrientation.timelike _) (hψ _) (hvel t htI)
    exact hmono ⟨le_rfl, hlt.le⟩ ⟨hlt.le, le_rfl⟩ hlt
  have hsm : StrictMono fun i => ψ (γ (s i)) := Fin.strictMono_iff_lt_succ.2 hpiece
  have := hsm (show (0 : Fin (k + 2)) < Fin.last (k + 1) from Fin.last_pos)
  simpa only [hs.first, hs.last] using this

/-- A function whose negative gradient is future-directed timelike increases strictly along
causal curves. -/
theorem lt_of_causalLE (hg : IsSpacetime g Y) (hψd : Differentiable ℝ ψ)
    (hψ : ∀ x, IsFutureTimelike g Y x (-grad g ψ x)) (h : CausalLE g Y p q) (hpq : p ≠ q) :
    ψ p < ψ q := by
  obtain ⟨γ, hγ, rfl, rfl⟩ := (causalLE_iff.1 h).resolve_left hpq
  exact lt_of_isPathOn hg hψd hψ hγ

theorem le_of_causalLE (hg : IsSpacetime g Y) (hψd : Differentiable ℝ ψ)
    (hψ : ∀ x, IsFutureTimelike g Y x (-grad g ψ x)) (h : CausalLE g Y p q) : ψ p ≤ ψ q := by
  by_cases hpq : p = q
  · rw [hpq]
  · exact (lt_of_causalLE hg hψd hψ h hpq).le

lemma IsCauchyTemporal.lt_of_isPathOn (hψ : IsCauchyTemporal g Y ψ) (hg : IsSpacetime g Y)
    {a b : ℝ} {γ : ℝ → E n} (hγ : IsPathOn (IsFutureCausal g Y) a b γ) : ψ (γ a) < ψ (γ b) :=
  LorentzianCalderon.lt_of_isPathOn hg (hψ.smooth.differentiable (by simp)) hψ.past_gradient hγ

lemma IsCauchyTemporal.le_of_causalLE (hψ : IsCauchyTemporal g Y ψ) (hg : IsSpacetime g Y)
    (h : CausalLE g Y p q) : ψ p ≤ ψ q :=
  LorentzianCalderon.le_of_causalLE hg (hψ.smooth.differentiable (by simp)) hψ.past_gradient h

/-- A lower bound of a Cauchy temporal function on `K` is a lower bound on `J⁺(K)`. -/
lemma IsCauchyTemporal.le_of_mem_causalFutureSet (hψ : IsCauchyTemporal g Y ψ)
    (hg : IsSpacetime g Y) {K : Set (E n)} {c : ℝ} (hK : ∀ x ∈ K, c ≤ ψ x) {x : E n}
    (hx : x ∈ causalFutureSet g Y K) : c ≤ ψ x := by
  obtain ⟨p, hp, hpx⟩ := mem_causalFutureSet.1 hx
  exact (hK p hp).trans (hψ.le_of_causalLE hg (mem_causalFuture.1 hpx))

end Monotone

end

end LorentzianCalderon
