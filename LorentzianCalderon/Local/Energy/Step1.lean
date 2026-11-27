module

public import LorentzianCalderon.Local.Energy.Pointwise

public section

/-!
# Step 1: the pointwise inequality for the divergence of the current
-/

namespace LorentzianCalderon

noncomputable section
open Set Matrix
open scoped ContDiff

variable {n : ℕ}

/-- The values at `x` of the coefficients of the remainder of the divergence identity. -/
def remCoeffs (g : MatrixField n) (ψ : E n → ℝ) (x : E n) :
    ℝ × (Fin (n + 1) → Fin (n + 1) → ℝ) × (Fin (n + 1) → Fin (n + 1) → ℝ) × ℝ ×
      (Fin (n + 1) → ℝ) × (Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → ℝ) :=
  (vol g x, fun c e => (g x)⁻¹ c e, fun b j => d (Current.X (ginv g) (dc ψ) b) x j,
    ∑ j, d (fun y => vol g y * Current.X (ginv g) (dc ψ) j y) x j,
    fun j => Current.X (ginv g) (dc ψ) j x, fun c e j => d (ginv g c e) x j)

/-- `remForm` with uncurried coefficients. -/
def remForm' (q : ℝ × (Fin (n + 1) → Fin (n + 1) → ℝ) × (Fin (n + 1) → Fin (n + 1) → ℝ) × ℝ ×
      (Fin (n + 1) → ℝ) × (Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → ℝ)) (v : Jet n) : ℝ :=
  remForm q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2 v

theorem R_eq (g : MatrixField n) (ψ w : E n → ℝ) {lam : ℝ} (hlam : 0 ≤ lam) (x : E n) :
    Current.R (vol g) (ginv g) (dc ψ) (dc w) w lam x =
      remForm' (remCoeffs g ψ x) (d w x, √lam * w x) := by
  simp only [Current.R_def, Current.flux_def, Current.q_def, Current.qf_def, remForm', remForm_def,
    remCoeffs, lin_def,
    quad_def, ginv_def, dc_def]
  rw [mul_pow, Real.sq_sqrt hlam]

theorem TXX_eq (g : MatrixField n) (ψ w : E n → ℝ) {lam : ℝ} (hlam : 0 ≤ lam) (x : E n) :
    Current.TXX (ginv g) (dc ψ) (dc w) w lam x = txxForm (g x)⁻¹ (d ψ x) (d w x, √lam * w x) := by
  simp only [Current.TXX_def, Current.q_def, qf_eq, txxForm_def, emTensor_def]
  rw [mul_pow, Real.sq_sqrt hlam]
  ring

theorem Xw_eq' {g : MatrixField n} {x : E n} (hx : IsLorentzian (g x)) (ψ w : E n → ℝ) :
    Current.Xw (ginv g) (dc ψ) (dc w) x = -bil (g x)⁻¹ (d ψ x) (d w x) := by
  rw [Current.Xw_eq (ginv_symm hx), qf_eq]

theorem continuous_txxForm_comp {Z : Type*} [TopologicalSpace Z]
    {A : Z → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {β : Z → Fin (n + 1) → ℝ}
    (hA : Continuous A) (hβ : Continuous β) :
    Continuous fun p : Z × Jet n => txxForm (A p.1) (β p.1) p.2 := by
  have := continuous_txxForm.comp (((hA.prodMk hβ).comp continuous_fst).prodMk continuous_snd)
  exact this

theorem continuous_bil_sq_comp {Z : Type*} [TopologicalSpace Z]
    {A : Z → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {β : Z → Fin (n + 1) → ℝ}
    (hA : Continuous A) (hβ : Continuous β) :
    Continuous fun p : Z × (Fin (n + 1) → ℝ) => bil (A p.1) (β p.1) p.2 ^ 2 := by
  have hc : Continuous fun q : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ × (Fin (n + 1) → ℝ)) ×
      (Fin (n + 1) → ℝ) => bil q.1.1 q.1.2 q.2 ^ 2 := by
    simp only [bil, Matrix.toLinearMap₂'_apply, smul_eq_mul]
    fun_prop
  have := hc.comp (((hA.prodMk hβ).comp continuous_fst).prodMk continuous_snd)
  exact this

theorem continuous_remForm_comp {Z : Type*} [TopologicalSpace Z]
    {κ : Z → ℝ × (Fin (n + 1) → Fin (n + 1) → ℝ) × (Fin (n + 1) → Fin (n + 1) → ℝ) × ℝ ×
      (Fin (n + 1) → ℝ) × (Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → ℝ)}
    (hκ : Continuous κ) : Continuous fun p : Z × Jet n => remForm' (κ p.1) p.2 := by
  have := continuous_remForm.comp ((hκ.comp continuous_fst).prodMk continuous_snd)
  exact this

namespace EnergySetting

variable {V : Set (E n)} {g : MatrixField n} {Y : E n → E n} {ψ ψ' : E n → ℝ} {τ c : ℝ}
  (h : EnergySetting V g Y ψ ψ' τ c)
include h

theorem continuousOn_inv (i j : Fin (n + 1)) : ContinuousOn (fun x => (g x)⁻¹ i j) V :=
  (h.contDiffOn_inv i j).continuousOn

theorem continuousOn_dψ (i : Fin (n + 1)) : ContinuousOn (fun x => d ψ x i) V :=
  (contDiffOn_d h.isOpen h.smooth_ψ i).continuousOn

theorem continuous_restrict_inv :
    Continuous fun x : lens V ψ ψ' τ c => (g x)⁻¹ :=
  continuous_matrix fun i j => ((h.continuousOn_inv i j).mono h.lens_subset).domRestrict

theorem continuous_restrict_dψ : Continuous fun x : lens V ψ ψ' τ c => d ψ x :=
  continuous_pi fun i => ((h.continuousOn_dψ i).mono h.lens_subset).domRestrict

theorem continuousOn_remCoeffs : ContinuousOn (remCoeffs g ψ) V := by
  have hd : ∀ {f : E n → ℝ}, ContDiffOn ℝ ∞ f V → ∀ j, ContinuousOn (fun x => d f x j) V :=
    fun hf j => continuousOn_d_of_contDiffOn h.isOpen (hf.of_le (by simp)) j
  refine h.contDiffOn_vol.continuousOn.prodMk (ContinuousOn.prodMk ?_ (ContinuousOn.prodMk ?_
    (ContinuousOn.prodMk ?_ (ContinuousOn.prodMk ?_ ?_))))
  · exact continuousOn_pi.2 fun c => continuousOn_pi.2 fun e => h.continuousOn_inv c e
  · exact continuousOn_pi.2 fun b => continuousOn_pi.2 fun j => hd (h.contDiffOn_X b) j
  · exact continuousOn_finsetSum _ fun j _ => hd (h.contDiffOn_vol.mul (h.contDiffOn_X j)) j
  · exact continuousOn_pi.2 fun j => (h.contDiffOn_X j).continuousOn
  · exact continuousOn_pi.2 fun c => continuousOn_pi.2 fun e => continuousOn_pi.2 fun j => by
      rw [ginv_eq]
      exact hd (h.contDiffOn_inv c e) j

/-- Coercivity of `T(X, X)` on the lens. -/
theorem exists_txx_coercive :
    ∃ cT > 0, ∀ x ∈ lens V ψ ψ' τ c, ∀ v : Jet n, cT * ‖v‖ ^ 2 ≤ txxForm (g x)⁻¹ (d ψ x) v := by
  have : CompactSpace (lens V ψ ψ' τ c) := isCompact_iff_compactSpace.1 h.isCompact
  have hF := continuous_txxForm_comp h.continuous_restrict_inv h.continuous_restrict_dψ
  obtain ⟨cT, hcT, hle⟩ := exists_coercive_of_homogeneous
    (F := fun (x : lens V ψ ψ' τ c) (v : Jet n) => txxForm (g x)⁻¹ (d ψ x) v) hF
    (fun x t v => txxForm_smul _ _ t v)
    (fun x v hv => txxForm_pos (h.isLorentzForm (h.lens_subset x.2))
      (h.psi_timelike (h.lens_subset x.2)) hv)
  exact ⟨cT, hcT, fun x hx v => hle ⟨x, hx⟩ v⟩

/-- Bound for `(Xw)²` on the lens. -/
theorem exists_Xw_bound :
    ∃ C, ∀ x ∈ lens V ψ ψ' τ c, ∀ ξ : Fin (n + 1) → ℝ,
      |bil (g x)⁻¹ (d ψ x) ξ ^ 2| ≤ C * ‖ξ‖ ^ 2 := by
  have : CompactSpace (lens V ψ ψ' τ c) := isCompact_iff_compactSpace.1 h.isCompact
  have hF := continuous_bil_sq_comp h.continuous_restrict_inv h.continuous_restrict_dψ
  obtain ⟨C, hC⟩ := exists_bound_of_homogeneous
    (F := fun (x : lens V ψ ψ' τ c) (ξ : Fin (n + 1) → ℝ) => bil (g x)⁻¹ (d ψ x) ξ ^ 2) hF
    (fun x t v => by simp only [map_smul, smul_eq_mul]; ring)
  exact ⟨C, fun x hx ξ => hC ⟨x, hx⟩ ξ⟩

/-- Bound for the remainder on the lens. -/
theorem exists_rem_bound :
    ∃ C, ∀ x ∈ lens V ψ ψ' τ c, ∀ v : Jet n, |remForm' (remCoeffs g ψ x) v| ≤ C * ‖v‖ ^ 2 := by
  have : CompactSpace (lens V ψ ψ' τ c) := isCompact_iff_compactSpace.1 h.isCompact
  have hF := continuous_remForm_comp (n := n)
    (h.continuousOn_remCoeffs.mono h.lens_subset).domRestrict
  obtain ⟨C, hC⟩ := exists_bound_of_homogeneous
    (F := fun (x : lens V ψ ψ' τ c) (v : Jet n) => remForm' (remCoeffs g ψ x) v) hF
    (fun x t v => remForm_smul _ _ _ _ _ _ t v)
  exact ⟨C, fun x hx v => hC ⟨x, hx⟩ v⟩

theorem exists_vol_bounds :
    ∃ ρ₀ > 0, ∃ ρ₁ > 0, ∀ x ∈ lens V ψ ψ' τ c, ρ₀ ≤ vol g x ∧ vol g x ≤ ρ₁ := by
  have hcont := h.contDiffOn_vol.continuousOn.mono h.lens_subset
  obtain ⟨ρ₀, hρ₀, hle⟩ := exists_pos_le_of_continuousOn h.isCompact hcont
    fun x hx => vol_pos (h.det_ne_zero (h.lens_subset hx))
  obtain ⟨ρ₁, hρ₁, hge⟩ := exists_abs_le_of_continuousOn h.isCompact hcont
  exact ⟨ρ₀, hρ₀, ρ₁, hρ₁, fun x hx => ⟨hle x hx, (le_abs_self _).trans (hge x hx)⟩⟩

/-- **Step 1**: the pointwise inequality for the divergence of the current with mass term
`λ = ε₀² σ²` on the lens. -/
theorem step1 : ∃ ε₀ > 0, ∃ a > 0, ∃ b > 0, ∃ σ₀ > 0, ∀ σ ≥ σ₀, ∀ (w : E n → ℝ) (x : E n),
    x ∈ lens V ψ ψ' τ c → ContDiffAt ℝ 2 w x →
      ∑ j, d (current g ψ w σ (ε₀ ^ 2 * σ ^ 2) j) x j ≤
        Real.exp (2 * σ * ψ x) *
          (-(a * σ) * (‖d w x‖ ^ 2 + σ ^ 2 * w x ^ 2) + b / σ * box g w x ^ 2) := by
  obtain ⟨cT, hcT, hT⟩ := h.exists_txx_coercive
  obtain ⟨CW, hW⟩ := h.exists_Xw_bound
  obtain ⟨CR, hR⟩ := h.exists_rem_bound
  obtain ⟨ρ₀, hρ₀, ρ₁, hρ₁, hρ⟩ := h.exists_vol_bounds
  set K := √(max CW 0) + 1 with hK
  have hK0 : 0 < K := by positivity
  have hKsq : CW ≤ K ^ 2 := by
    have h1 : (√(max CW 0)) ^ 2 = max CW 0 := Real.sq_sqrt (le_max_right _ _)
    have h2 : 0 ≤ √(max CW 0) := Real.sqrt_nonneg _
    nlinarith [le_max_left CW 0]
  set c₁ := ρ₀ * cT with hc₁
  have hc₁0 : 0 < c₁ := by positivity
  set ε₀ := c₁ / (2 * ρ₁ * K) with hε₀
  have hε₀0 : 0 < ε₀ := by positivity
  set CR' := max CR 0
  refine ⟨ε₀, hε₀0, c₁ * min 1 (ε₀ ^ 2) / 4, by positivity, ρ₁ ^ 2 * K ^ 2 / c₁, by positivity,
    max 1 (4 * CR' / c₁), by positivity, fun σ hσ w x hxL hw => ?_⟩
  have hx : x ∈ V := h.lens_subset hxL
  have hσ1 : 1 ≤ σ := (le_max_left _ _).trans hσ
  have hσ0 : 0 < σ := by linarith
  have hσR : CR' ≤ σ * c₁ / 4 := by
    have := (le_max_right _ _).trans hσ
    rw [div_le_iff₀ hc₁0] at this
    linarith
  set lam := ε₀ ^ 2 * σ ^ 2 with hlam
  have hlam0 : 0 ≤ lam := by positivity
  have hsqrt : √lam = ε₀ * σ := by
    rw [hlam, ← mul_pow, Real.sqrt_sq (by positivity)]
  rw [h.div_current hx hw σ lam, TXX_eq g ψ w hlam0, R_eq g ψ w hlam0,
    Xw_eq' (h.lorentzian x hx), hsqrt]
  set ξ := d w x
  set s := ε₀ * σ * w x with hs
  set v : Jet n := (ξ, s)
  set ρ := vol g x
  set B := bil (g x)⁻¹ (d ψ x) ξ
  set T := txxForm (g x)⁻¹ (d ψ x) v
  set R := remForm' (remCoeffs g ψ x) v
  set Ψ := ‖ξ‖ ^ 2 + s ^ 2 with hΨ
  have hρ0 := (hρ x hxL).1
  have hρ1 := (hρ x hxL).2
  have hvΨ : ‖v‖ ^ 2 ≤ Ψ := norm_jet_sq_le v
  have hΨv : Ψ ≤ 2 * ‖v‖ ^ 2 := norm_jet_sq_ge v
  -- the four terms
  have hTb : ρ₀ * cT / 2 * Ψ ≤ ρ * T := by
    have h1 : cT / 2 * Ψ ≤ T := by have := hT x hxL v; nlinarith
    have h2 : 0 ≤ cT / 2 * Ψ := by positivity
    calc ρ₀ * cT / 2 * Ψ = ρ₀ * (cT / 2 * Ψ) := by ring
      _ ≤ ρ * T := mul_le_mul hρ0 h1 h2 (by linarith)
  have hBb : |B| ≤ K * ‖ξ‖ := by
    have h1 : B ^ 2 ≤ (K * ‖ξ‖) ^ 2 := by
      have := (le_abs_self _).trans (hW x hxL ξ)
      have h3 : CW * ‖ξ‖ ^ 2 ≤ K ^ 2 * ‖ξ‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hKsq (by positivity)
      nlinarith
    exact abs_le_of_sq_le_sq h1 (by positivity)
  have hRb : R ≤ CR' * Ψ := by
    have h1 := (le_abs_self _).trans (hR x hxL v)
    have h2 : CR * ‖v‖ ^ 2 ≤ CR' * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    have h3 : CR' * ‖v‖ ^ 2 ≤ CR' * Ψ := mul_le_mul_of_nonneg_left hvΨ (le_max_right _ _)
    linarith
  have hbox : -(ρ * box g w x * -B) ≤ σ * c₁ / 4 * ‖ξ‖ ^ 2 +
      ρ₁ ^ 2 * K ^ 2 / c₁ / σ * box g w x ^ 2 := by
    have h1 : -(ρ * box g w x * -B) ≤ ρ₁ * K * |box g w x| * ‖ξ‖ := by
      have : -(ρ * box g w x * -B) ≤ ρ * |box g w x| * |B| := by
        rw [show -(ρ * box g w x * -B) = ρ * (box g w x * B) by ring]
        calc ρ * (box g w x * B) ≤ |ρ * (box g w x * B)| := le_abs_self _
          _ = ρ * |box g w x| * |B| := by
            rw [abs_mul, abs_mul, abs_of_pos (by linarith : 0 < ρ)]; ring
      calc _ ≤ ρ * |box g w x| * |B| := this
        _ ≤ ρ₁ * |box g w x| * (K * ‖ξ‖) := by gcongr
        _ = ρ₁ * K * |box g w x| * ‖ξ‖ := by ring
    have h2 : ρ₁ * K * |box g w x| * ‖ξ‖ ≤ σ * c₁ / 4 * ‖ξ‖ ^ 2 +
        ρ₁ ^ 2 * K ^ 2 / c₁ / σ * box g w x ^ 2 := by
      have hpos : 0 < σ * c₁ := by positivity
      set y := ρ₁ * K * |box g w x|
      have e : ρ₁ ^ 2 * K ^ 2 / c₁ / σ * box g w x ^ 2 = y ^ 2 / (σ * c₁) := by
        simp only [y, mul_pow, sq_abs]; field_simp
      rw [e, ← sub_nonneg]
      have e2 : σ * c₁ / 4 * ‖ξ‖ ^ 2 + y ^ 2 / (σ * c₁) - y * ‖ξ‖ =
          (σ * c₁ / 2 * ‖ξ‖ - y) ^ 2 / (σ * c₁) := by
        field_simp; ring
      rw [e2]; positivity
    linarith
  have hmass : -(ρ * lam * w x * -B) ≤ σ * c₁ / 4 * Ψ := by
    have h1 : -(ρ * lam * w x * -B) ≤ ρ₁ * K * (ε₀ * σ) * (|s| * ‖ξ‖) := by
      have e : -(ρ * lam * w x * -B) = ρ * (ε₀ * σ) * (s * B) := by
        rw [hlam, hs]; ring
      rw [e]
      have : s * B ≤ |s| * (K * ‖ξ‖) := by
        calc s * B ≤ |s * B| := le_abs_self _
          _ = |s| * |B| := abs_mul _ _
          _ ≤ |s| * (K * ‖ξ‖) := by gcongr
      have hεσ : 0 ≤ ε₀ * σ := by positivity
      have hρpos : 0 ≤ ρ := by linarith
      calc ρ * (ε₀ * σ) * (s * B) ≤ ρ * (ε₀ * σ) * (|s| * (K * ‖ξ‖)) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ ≤ ρ₁ * (ε₀ * σ) * (|s| * (K * ‖ξ‖)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hρ1 hεσ) (by positivity)
        _ = ρ₁ * K * (ε₀ * σ) * (|s| * ‖ξ‖) := by ring
    have h2 : |s| * ‖ξ‖ ≤ Ψ / 2 := by
      have := sq_nonneg (|s| - ‖ξ‖)
      rw [hΨ, ← sq_abs s]; nlinarith
    have h3 : ρ₁ * K * ε₀ = c₁ / 2 := by
      rw [hε₀]; field_simp
    calc -(ρ * lam * w x * -B) ≤ ρ₁ * K * (ε₀ * σ) * (|s| * ‖ξ‖) := h1
      _ ≤ ρ₁ * K * (ε₀ * σ) * (Ψ / 2) := by gcongr
      _ = σ * c₁ / 4 * Ψ := by rw [show ρ₁ * K * (ε₀ * σ) = σ * (ρ₁ * K * ε₀) by ring, h3]; ring
  have hΨmin : min 1 (ε₀ ^ 2) * (‖ξ‖ ^ 2 + σ ^ 2 * w x ^ 2) ≤ Ψ := by
    have h1 : min 1 (ε₀ ^ 2) ≤ 1 := min_le_left _ _
    have h2 : min 1 (ε₀ ^ 2) ≤ ε₀ ^ 2 := min_le_right _ _
    have h3 : 0 ≤ ‖ξ‖ ^ 2 := sq_nonneg _
    have h4 : 0 ≤ σ ^ 2 * w x ^ 2 := by positivity
    have e : s ^ 2 = ε₀ ^ 2 * (σ ^ 2 * w x ^ 2) := by rw [hs]; ring
    rw [hΨ, e]
    have h5 := mul_le_mul_of_nonneg_right h1 h3
    have h6 := mul_le_mul_of_nonneg_right h2 h4
    linarith only [h5, h6]
  have hξΨ : ‖ξ‖ ^ 2 ≤ Ψ := by rw [hΨ]; linarith only [sq_nonneg s]
  have hfinal : -2 * σ * ρ * T - ρ * box g w x * -B - ρ * lam * w x * -B + R ≤
      -(c₁ * min 1 (ε₀ ^ 2) / 4 * σ) * (‖ξ‖ ^ 2 + σ ^ 2 * w x ^ 2) +
        ρ₁ ^ 2 * K ^ 2 / c₁ / σ * box g w x ^ 2 := by
    have h1 : -2 * σ * ρ * T ≤ -(σ * c₁) * Ψ := by
      have : σ * (ρ₀ * cT / 2 * Ψ) ≤ σ * (ρ * T) := mul_le_mul_of_nonneg_left hTb hσ0.le
      rw [hc₁]; linarith
    have h2 : σ * c₁ / 4 * ‖ξ‖ ^ 2 ≤ σ * c₁ / 4 * Ψ :=
      mul_le_mul_of_nonneg_left hξΨ (by positivity)
    have h3 : CR' * Ψ ≤ σ * c₁ / 4 * Ψ := mul_le_mul_of_nonneg_right hσR (by positivity)
    have h4 : -(σ * c₁ / 4) * Ψ ≤
        -(c₁ * min 1 (ε₀ ^ 2) / 4 * σ) * (‖ξ‖ ^ 2 + σ ^ 2 * w x ^ 2) := by
      have := mul_le_mul_of_nonneg_left hΨmin (by positivity : 0 ≤ σ * c₁ / 4)
      linarith
    linarith
  exact mul_le_mul_of_nonneg_left hfinal (Real.exp_pos _).le

end EnergySetting

end

end LorentzianCalderon
