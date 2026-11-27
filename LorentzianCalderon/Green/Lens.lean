module

public import LorentzianCalderon.Green.NarrowMetric
public import LorentzianCalderon.Local.Energy

public section

/-!
# Vanishing on lenses

`EnergySetting.eq_zero_of_box`: in the setting of the weighted energy inequality, a solution of
`□_g w = 0` on the lens `L = {x ∈ V | ψ x ≤ τ, c ≤ ψ' x}` with `w = 0`, `dw = 0` on the top
`{ψ = τ} ∩ L` vanishes on `{x ∈ V | ψ x < τ, c < ψ' x}`. With the time orientation reversed and
`ψ` replaced by `-ψ`, this is finite propagation speed for data at the bottom.

*Frozen lenses* for the narrowed metric `g_ε` (`exists_frozen_radius`): at a point `w` freeze
`ǧ = g_{ε/2}(w)`. On a ball `B(w, r)`, with `r` uniform for `w` in a compact set, every vector
`v ≠ 0` that is future causal for `ǧ` is future timelike for `g`, has `ǧ(v, N) < 0`, and its
covector `ǧ v` is timelike for `g_ε`. So `Q(p) = -ǧ(y - p, y - p)` is temporal for `g_ε` with
the past orientation `-N` on `B(w, r) ∩ {Q > 0} ∩ {dψ_w(y - p) > 0}`, and straight segments to
`y` from there are `g`-timelike.
-/

namespace LorentzianCalderon

noncomputable section
open Set Matrix WithLp Filter MeasureTheory Metric
open scoped ContDiff Topology

variable {n : ℕ}

namespace EnergySetting

variable {V : Set (E n)} {g : MatrixField n} {Y : E n → E n} {ψ ψ' : E n → ℝ} {τ c : ℝ}

/-- **Vanishing on a lens.** A `C²` solution of `□_g w = 0` on the lens with vanishing Cauchy
data on its top vanishes below the top and above the bottom. -/
theorem eq_zero_of_box (h : EnergySetting V g Y ψ ψ' τ c) {U : Set (E n)} {w : E n → ℝ}
    (hU : IsOpen U) (hLU : lens V ψ ψ' τ c ⊆ U) (hw : ContDiffOn ℝ 2 w U)
    (hbox : ∀ x ∈ lens V ψ ψ' τ c, box g w x = 0)
    (htop : ∀ x ∈ lens V ψ ψ' τ c, ψ x = τ → w x = 0 ∧ fderiv ℝ w x = 0) :
    ∀ x ∈ V, ψ x < τ → c < ψ' x → w x = 0 := by
  intro x hxV hxτ hxc
  obtain ⟨C, σ₀, H⟩ := h.energy_volume
  set σ := max σ₀ 1
  have hσ1 : 1 ≤ σ := le_max_right _ _
  have hineq := H σ (le_max_left _ _) U w hU hLU hw htop
  set L := lens V ψ ψ' τ c
  have hLm : MeasurableSet L := h.isCompact.measurableSet
  have hz : ∫ y in L, Real.exp (2 * σ * ψ y) * box g w y ^ 2 = 0 := by
    rw [setIntegral_congr_fun hLm (g := fun _ => 0) fun y hy => by simp [hbox y hy]]
    simp
  rw [hz, mul_zero] at hineq
  set f : E n → ℝ := fun y => Real.exp (2 * σ * ψ y) * (‖fderiv ℝ w y‖ ^ 2 + σ ^ 2 * w y ^ 2)
  have hf0 : ∀ y, 0 ≤ f y := fun y => by positivity
  have hfc : ContinuousOn f L :=
    ((Real.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (h.smooth_ψ.continuousOn.mono h.lens_subset)))).mul
      ((((hw.continuousOn_fderiv_of_isOpen hU one_le_two).norm.pow 2).add
        (continuousOn_const.mul (hw.continuousOn.pow 2))).mono hLU)
  have hI0 : ∫ y in L, f y = 0 := by
    have hnn := setIntegral_nonneg (μ := volume) hLm fun y _ => hf0 y
    have : 0 < σ ^ 2 := by positivity
    nlinarith
  have hae := (setIntegral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall hf0)
    (hfc.integrableOn_compact h.isCompact)).1 hI0
  set O := {y | y ∈ V ∧ ψ y < τ ∧ c < ψ' y}
  have hOL : O ⊆ L := fun y hy => mem_lens.2 ⟨hy.1, hy.2.1.le, hy.2.2.le⟩
  have hO : IsOpen O := by
    have h1 := h.smooth_ψ.continuousOn.isOpen_inter_preimage h.isOpen (isOpen_Iio (a := τ))
    have h2 := (h.smooth_ψ'.continuousOn.mono inter_subset_left).isOpen_inter_preimage h1
      (isOpen_Ioi (a := c))
    convert h2 using 1
    ext y
    simp only [O, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Iio, mem_Ioi]
    tauto
  have heq := Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset hOL hae) hO
    (hfc.mono hOL) continuousOn_const (show x ∈ O from ⟨hxV, hxτ, hxc⟩)
  simp only [Pi.zero_apply, f] at heq
  have h2 := (mul_eq_zero.1 heq).resolve_left (Real.exp_pos _).ne'
  have h3 : σ ^ 2 * w x ^ 2 = 0 := by
    have := sq_nonneg ‖fderiv ℝ w x‖
    have := mul_nonneg (sq_nonneg σ) (sq_nonneg (w x))
    linarith
  have hσ0 : σ ^ 2 ≠ 0 := by positivity
  exact pow_eq_zero_iff two_ne_zero |>.1 ((mul_eq_zero.1 h3).resolve_left hσ0)

end EnergySetting

/-- `grad (-u) = -grad u`. -/
theorem grad_neg (g : MatrixField n) (u : E n → ℝ) (x : E n) :
    grad g (fun y => -u y) x = -grad g u x := by
  ext j
  simp [grad_def, d_neg]

section Bottom

variable {W : Set (E n)} {g : MatrixField n} {Y : E n → E n} {φ₁ φ₂ : E n → ℝ} {t₀ c : ℝ}

/-- **Vanishing on a lens, data at the bottom.** Let `φ₁, φ₂` be temporal for `(g, Y)` on the
open set `W`, with `L = {x ∈ W | t₀ ≤ φ₁ x, φ₂ x ≤ c}` compact. A `C²` solution of `□_g V = 0` on
`L` with `V = 0`, `dV = 0` on the bottom `{φ₁ = t₀} ∩ L` vanishes on
`{x ∈ W | t₀ < φ₁ x, φ₂ x < c}`. This is `EnergySetting.eq_zero_of_box` for the orientation
`-Y` and the functions `-φ₁, -φ₂`. -/
theorem eq_zero_of_bottom (hW : IsOpen W) (hgs : ∀ i j, ContDiffOn ℝ ∞ (fun x => g x i j) W)
    (hgL : ∀ x ∈ W, IsLorentzian (g x)) (hY : ContinuousOn Y W)
    (hYt : ∀ x ∈ W, form (g x) (Y x) (Y x) < 0) (hφ₁ : ContDiffOn ℝ ∞ φ₁ W)
    (hφ₂ : ContDiffOn ℝ ∞ φ₂ W) (ht₁ : ∀ x ∈ W, IsFutureTimelike g Y x (-grad g φ₁ x))
    (ht₂ : ∀ x ∈ W, IsFutureTimelike g Y x (-grad g φ₂ x))
    (hK : IsCompact {x | x ∈ W ∧ t₀ ≤ φ₁ x ∧ φ₂ x ≤ c}) {U : Set (E n)} {V : E n → ℝ}
    (hU : IsOpen U) (hLU : {x | x ∈ W ∧ t₀ ≤ φ₁ x ∧ φ₂ x ≤ c} ⊆ U) (hV : ContDiffOn ℝ 2 V U)
    (hbox : ∀ x, x ∈ W → t₀ ≤ φ₁ x → φ₂ x ≤ c → box g V x = 0)
    (hbot : ∀ x, x ∈ W → φ₂ x ≤ c → φ₁ x = t₀ → V x = 0 ∧ fderiv ℝ V x = 0) :
    ∀ x ∈ W, t₀ < φ₁ x → φ₂ x < c → V x = 0 := by
  have hL : lens W (fun x => -φ₁ x) (fun x => -φ₂ x) (-t₀) (-c) =
      {x | x ∈ W ∧ t₀ ≤ φ₁ x ∧ φ₂ x ≤ c} := by
    ext x
    simp [lens_def]
  have htemp : ∀ {φ : E n → ℝ}, (∀ x ∈ W, IsFutureTimelike g Y x (-grad g φ x)) →
      ∀ x ∈ W, IsFutureTimelike g (-Y) x (-grad g (fun y => -φ y) x) := fun hφ x hx => by
    rw [grad_neg, isFutureTimelike_neg_iff, neg_neg]
    exact hφ x hx
  have hset : EnergySetting W g (-Y) (fun x => -φ₁ x) (fun x => -φ₂ x) (-t₀) (-c) :=
    ⟨hW, hgs, hgL, hY.neg, fun x hx => by simpa using hYt x hx, hφ₁.neg, hφ₂.neg,
      htemp ht₁, htemp ht₂, hL ▸ hK⟩
  intro x hx h1 h2
  refine hset.eq_zero_of_box hU (hL ▸ hLU) hV (fun y hy => ?_) (fun y hy hyt => ?_) x hx
    (by simpa using h1) (by simpa using h2)
  · rw [hL] at hy
    exact hbox y hy.1 hy.2.1 hy.2.2
  · rw [hL] at hy
    exact hbot y hy.1 hy.2.2 (by simpa using hyt)

/-- The coarse lens function `t + a ⟨y - y_c⟩` in coordinates `x = (t, y)`, with
`⟨y⟩ = √(1 + |y|²)`. -/
def tentTime (a : ℝ) (xc x : E n) : ℝ := x 0 + a * √(1 + ∑ i : Fin n, (x - xc) i.succ ^ 2)

theorem tentTime_def (a : ℝ) (xc x : E n) :
    tentTime a xc x =
      x 0 + a * √(1 + ∑ i : Fin n, (x - xc) i.succ ^ 2) := by rfl

/-- `tentTime` is continuous. -/
theorem continuous_tentTime (a : ℝ) (xc : E n) : Continuous (tentTime a xc) := by
  unfold tentTime
  fun_prop

/-- The differential of `t + a ⟨y - y_c⟩`. -/
theorem hasFDerivAt_tentTime (a : ℝ) (xc x : E n) :
    HasFDerivAt (tentTime a xc)
      ((EuclideanSpace.proj (0 : Fin (n + 1)) : E n →L[ℝ] ℝ) +
        (a * (2 * √(1 + ∑ i : Fin n, (x - xc) i.succ ^ 2))⁻¹) •
          ∑ i : Fin n, (2 * (x - xc) i.succ) •
            (EuclideanSpace.proj i.succ : E n →L[ℝ] ℝ)) x := by
  have hc : ∀ i : Fin n, HasFDerivAt (fun x : E n => (x - xc) i.succ)
      (EuclideanSpace.proj i.succ : E n →L[ℝ] ℝ) x := fun i => by
    have := (EuclideanSpace.proj i.succ : E n →L[ℝ] ℝ).hasFDerivAt.comp x
      ((hasFDerivAt_id x).sub_const xc)
    simpa [Function.comp_def] using this
  have hS := HasFDerivAt.fun_sum (u := Finset.univ) fun i _ => (hc i).pow 2
  have hpos : 0 < 1 + ∑ i : Fin n, (x - xc) i.succ ^ 2 :=
    add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hsq := (hS.const_add 1).sqrt hpos.ne'
  have h := (EuclideanSpace.proj (0 : Fin (n + 1)) : E n →L[ℝ] ℝ).hasFDerivAt.add
    (hsq.const_mul a)
  convert h using 1
  · ext v
    simp [tentTime]
  · ext v
    simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

/-- Coarse lenses (tents) `{t₀ ≤ t, t + a⟨y - y_c⟩ ≤ c}` are compact. -/
theorem isCompact_tent {a : ℝ} (ha : 0 < a) (xc : E n) (t₀ c : ℝ) :
    IsCompact {x : E n | t₀ ≤ x 0 ∧ tentTime a xc x ≤ c} := by
  refine Metric.isCompact_of_isClosed_isBounded ((isClosed_le continuous_const
    ((EuclideanSpace.proj (0 : Fin (n + 1)) : E n →L[ℝ] ℝ).continuous)).inter
      (isClosed_le (continuous_tentTime a xc) continuous_const)) ?_
  set M := |t₀| + |c| + (c - t₀) / a + |xc 0|
  refine (Metric.isBounded_closedBall (x := xc) (r := 2 * M)).subset fun x hx => ?_
  obtain ⟨h1, h2⟩ := hx
  set S := ∑ i : Fin n, (x - xc) i.succ ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsq : √S ≤ √(1 + S) := Real.sqrt_le_sqrt (by linarith)
  have hx0 : a * √(1 + S) ≤ c - t₀ := by simp only [tentTime] at h2; linarith
  have hsqS : √S ≤ (c - t₀) / a := by
    rw [le_div_iff₀ ha]
    nlinarith [mul_le_mul_of_nonneg_left hsq ha.le]
  have hn := EuclideanSpace.real_norm_sq_eq (x - xc)
  rw [Fin.sum_univ_succ] at hn
  have hd0 : |(x - xc) 0| ≤ |t₀| + |c| + |xc 0| := by
    have : x 0 ≤ c := by
      have := Real.sqrt_nonneg (1 + S)
      simp only [tentTime] at h2
      nlinarith
    rw [PiLp.sub_apply]
    calc |x 0 - xc 0| ≤ |x 0| + |xc 0| := abs_sub _ _
      _ ≤ |t₀| + |c| + |xc 0| := by
        gcongr
        rw [abs_le]
        constructor <;> cases abs_cases t₀ <;> cases abs_cases c <;> linarith
  have hM0 : 0 ≤ (c - t₀) / a := (Real.sqrt_nonneg S).trans hsqS
  rw [mem_closedBall, dist_eq_norm]
  have hnorm : ‖x - xc‖ ≤ |(x - xc) 0| + √S := by
    refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_
    rw [hn]
    nlinarith [Real.sq_sqrt hS, sq_abs ((x - xc) 0), mul_nonneg (abs_nonneg ((x - xc) 0))
      (Real.sqrt_nonneg S)]
  have : 0 ≤ M := by positivity
  linarith

end Bottom

/-- `H⁻¹(H v - c ξ, H v - c ξ) = H(v, v) - 2 c (v · ξ) + c² H⁻¹(ξ, ξ)`. -/
theorem IsLorentzian.bil_inv_mulVec_sub {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hH : IsLorentzian H) (v ξ : Fin (n + 1) → ℝ) (c : ℝ) :
    bil H⁻¹ (H *ᵥ v - c • ξ) (H *ᵥ v - c • ξ) =
      bil H v v - 2 * c * (v ⬝ᵥ ξ) + c ^ 2 * bil H⁻¹ ξ ξ := by
  have key : ∀ y, bil H⁻¹ (H *ᵥ v) y = v ⬝ᵥ y := fun y => by
    rw [bil_symm hH.inv_symm, bil_apply, mulVec_mulVec, nonsing_inv_mul _ hH.isUnit_det,
      one_mulVec, dotProduct_comm]
  have hsym : bil H⁻¹ ξ (H *ᵥ v) = v ⬝ᵥ ξ := by rw [bil_symm hH.inv_symm, key]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, key,
    hsym]
  simp only [bil_apply]
  ring

section Frozen

variable {g : MatrixField n} {Y : E n → E n} {ψ : E n → ℝ} {ε : ℝ}

/-- `g_{ε/2}(w) v = g_ε(w) v - (ε/2) dψ_w(v) dψ_w`. -/
theorem narrow_half_mulVec (g : MatrixField n) (ψ : E n → ℝ) (ε : ℝ) (w v : E n) :
    narrow g ψ (ε / 2) w *ᵥ ofLp v =
      narrow g ψ ε w *ᵥ ofLp v - ((ε / 2) * fderiv ℝ ψ w v) • d ψ w := by
  simp only [narrow_def, add_smul_vecMulVec_mulVec, dotProduct_comm (d ψ w), ofLp_dotProduct_d]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The four comparisons at the frozen point itself, for a future causal vector of `ǧ`. -/
theorem frozen_pointwise (hg : IsSpacetime g Y) (hψ : IsStandardTime g Y ψ) (hε : 0 < ε)
    (hε1 : ∀ x, 1 / 2 ≤ 1 + ε * coform g x (d ψ x) (d ψ x)) {w v : E n} (hv : v ≠ 0)
    (hvv : form (narrow g ψ (ε / 2) w) v v ≤ 0) (hvf : 0 ≤ fderiv ℝ ψ w v) :
    coform (narrow g ψ ε) w (narrow g ψ (ε / 2) w *ᵥ ofLp v)
        (narrow g ψ (ε / 2) w *ᵥ ofLp v) < 0 ∧
      form (narrow g ψ (ε / 2) w) v (-grad g ψ w) < 0 ∧
      form (g w) v v < 0 ∧ 0 < fderiv ℝ ψ w v := by
  have hL := hg.lorentzian w
  set a := fderiv ℝ ψ w v
  set s := coform g w (d ψ w) (d ψ w)
  have hs : s < 0 := coform_self_neg_of_future hL (hψ.past_gradient w)
  have h1 := hε1 w
  rw [form_narrow] at hvv
  have hvN : form (g w) v (-grad g ψ w) = -a := by
    rw [form_comm hL.symm, form_neg_grad_left hL]
  have ha : 0 < a := by
    refine lt_of_le_of_ne hvf fun h0 => ?_
    have hNN : form (g w) (-grad g ψ w) (-grad g ψ w) < 0 := by rw [form_neg_grad hL]; exact hs
    refine hL.form_ne_zero ?_ hv hNN (by rw [hvN, ← h0, neg_zero])
    nlinarith [mul_nonneg hε.le (mul_self_nonneg a)]
  have hF3 : form (g w) v v < 0 := by nlinarith [mul_pos hε (mul_pos ha ha)]
  refine ⟨?_, ?_, hF3, ha⟩
  · have hLε := isLorentzian_narrow (ε := ε) hL hs (by linarith)
    rw [narrow_half_mulVec, coform_eq_bil, hLε.bil_inv_mulVec_sub, ← coform_eq_bil,
      coform_narrow hL (by linarith), ← form_eq_bil, form_narrow, ofLp_dotProduct_d]
    have hq : s / (1 + ε * s) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hs.le (by linarith)
    nlinarith [mul_pos hε (mul_pos ha ha), mul_nonneg (sq_nonneg (ε / 2 * a)) (neg_nonneg.2 hq)]
  · rw [form_narrow, hvN, fderiv_neg_grad_self hL]
    nlinarith [mul_pos hε ha, mul_pos (mul_pos hε ha) (neg_pos.2 hs)]

/-- Continuity of `form` in the matrix and the vectors. -/
theorem continuous_form_of {X : Type*} [TopologicalSpace X]
    {A : X → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {u v : X → E n}
    (hA : ∀ i j, Continuous fun x => A x i j) (hu : Continuous u) (hv : Continuous v) :
    Continuous fun x => form (A x) (u x) (v x) := by
  simp only [form_def]
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    ((((EuclideanSpace.proj i : E n →L[ℝ] ℝ).continuous.comp hu)).mul (hA i j)).mul
      ((EuclideanSpace.proj j : E n →L[ℝ] ℝ).continuous.comp hv)

/-- Continuity of `coform` in the point and the covectors. -/
theorem continuous_coform_of {X : Type*} [TopologicalSpace X] {g : MatrixField n}
    {p : X → E n} {ξ η : X → Fin (n + 1) → ℝ}
    (hA : ∀ i j, Continuous fun x => (g (p x))⁻¹ i j) (hξ : ∀ i, Continuous fun x => ξ x i)
    (hη : ∀ i, Continuous fun x => η x i) :
    Continuous fun x => coform g (p x) (ξ x) (η x) := by
  simp only [coform_def]
  exact continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ =>
    ((hA j k).mul (hξ j)).mul (hη k)

/-- **Frozen cones.** For `w` in a compact set and `p ∈ B(w, r)`, a vector `v ≠ 0` that is
future causal for `ǧ = g_{ε/2}(w)` (with `dψ_w(v) ≥ 0`) has `ǧ v` timelike for `g_ε(p)`,
`ǧ(v, N(p)) < 0`, and is timelike for `g(p)` with `dψ_p(v) > 0`. -/
theorem exists_frozen_radius (hg : IsSpacetime g Y) (hψ : IsStandardTime g Y ψ) (hε : 0 < ε)
    (hε1 : ∀ x, 1 / 2 ≤ 1 + ε * coform g x (d ψ x) (d ψ x)) {B : Set (E n)}
    (hB : IsCompact B) :
    ∃ r > 0, ∀ w ∈ B, ∀ p, dist p w < r → ∀ v, v ≠ 0 →
      form (narrow g ψ (ε / 2) w) v v ≤ 0 → 0 ≤ fderiv ℝ ψ w v →
      coform (narrow g ψ ε) p (narrow g ψ (ε / 2) w *ᵥ ofLp v)
          (narrow g ψ (ε / 2) w *ᵥ ofLp v) < 0 ∧
        form (narrow g ψ (ε / 2) w) v (-grad g ψ p) < 0 ∧
        form (g p) v v < 0 ∧ 0 < fderiv ℝ ψ p v := by
  have hψ1 : ContDiff ℝ 1 ψ := hψ.smooth.of_le (by simp)
  have hnar : ∀ ε' i j, Continuous fun x => narrow g ψ ε' x i j := fun ε' i j =>
    (contDiff_narrow hg.smooth hψ.smooth ε' i j).continuous
  have hinv : ∀ i j, Continuous fun x => (narrow g ψ ε x)⁻¹ i j := fun i j =>
    (contDiff_inv_apply (contDiff_narrow hg.smooth hψ.smooth ε) (fun x =>
      (isLorentzian_narrow (hg.lorentzian x) (coform_self_neg_of_future (hg.lorentzian x)
        (hψ.past_gradient x)) (by linarith [hε1 x])).det_neg.ne) i j).continuous
  have hN : Continuous fun x => -grad g ψ x := (hg.continuous_grad hψ1).neg
  have hfd : Continuous fun q : E n × E n => fderiv ℝ ψ q.1 q.2 :=
    ((hψ1.continuous_fderiv one_ne_zero).comp continuous_fst).clm_apply continuous_snd
  set cov : E n × E n → Fin (n + 1) → ℝ := fun q => narrow g ψ (ε / 2) q.1 *ᵥ ofLp q.2
  have hcov : ∀ i, Continuous fun q : E n × E n => cov q i := fun i => by
    simp only [cov, mulVec, dotProduct]
    exact continuous_finsetSum _ fun j _ => ((hnar (ε / 2) i j).comp continuous_fst).mul
      ((EuclideanSpace.proj j : E n →L[ℝ] ℝ).continuous.comp continuous_snd)
  set Φ : E n × E n × E n → ℝ := fun q =>
    max (max (coform (narrow g ψ ε) q.2.1 (cov (q.1, q.2.2)) (cov (q.1, q.2.2)))
      (form (narrow g ψ (ε / 2) q.1) q.2.2 (-grad g ψ q.2.1)))
      (max (form (g q.2.1) q.2.2 q.2.2) (-fderiv ℝ ψ q.2.1 q.2.2))
  have hΦ : Continuous Φ := by
    have hw : Continuous fun q : E n × E n × E n => q.1 := continuous_fst
    have hp : Continuous fun q : E n × E n × E n => q.2.1 := continuous_fst.comp continuous_snd
    have hv : Continuous fun q : E n × E n × E n => q.2.2 := continuous_snd.comp continuous_snd
    refine ((continuous_coform_of (fun i j => (hinv i j).comp hp)
      (fun i => (hcov i).comp (hw.prodMk hv)) (fun i => (hcov i).comp (hw.prodMk hv))).max
      (continuous_form_of (fun i j => (hnar _ i j).comp hw) hv (hN.comp hp))).max
      ((continuous_form_of (fun i j => (hg.smooth i j).continuous.comp hp) hv hv).max
        (hfd.comp (hp.prodMk hv)).neg)
  set S := {q : E n × E n | q.1 ∈ B ∧ q.2 ∈ sphere (0 : E n) 1 ∧
    form (narrow g ψ (ε / 2) q.1) q.2 q.2 ≤ 0 ∧ 0 ≤ fderiv ℝ ψ q.1 q.2}
  have hS : IsCompact S := by
    refine (hB.prod (isCompact_sphere (0 : E n) 1)).of_isClosed_subset ?_
      fun q hq => ⟨hq.1, hq.2.1⟩
    exact (hB.isClosed.preimage continuous_fst).inter
      ((isClosed_sphere.preimage continuous_snd).inter
        ((isClosed_le (continuous_form_of (fun i j => (hnar _ i j).comp continuous_fst)
          continuous_snd continuous_snd) continuous_const).inter
          (isClosed_le continuous_const hfd)))
  set K' := (fun q : E n × E n => (q.1, q.1, q.2)) '' S
  have hK' : IsCompact K' := hS.image (by fun_prop)
  have hU : IsOpen {q | Φ q < 0} := isOpen_lt hΦ continuous_const
  have hK'U : K' ⊆ {q | Φ q < 0} := by
    rintro _ ⟨⟨w, v⟩, ⟨-, hv1, hvv, hvf⟩, rfl⟩
    have hv0 : v ≠ 0 := by
      rintro rfl
      simp at hv1
    obtain ⟨h1, h2, h3, h4⟩ := frozen_pointwise hg hψ hε hε1 hv0 hvv hvf
    simp only [mem_ofPred_eq, Φ, cov, max_lt_iff]
    exact ⟨⟨h1, h2⟩, h3, by linarith⟩
  obtain ⟨r, hr, hsub⟩ := hK'.exists_thickening_subset_open hU hK'U
  refine ⟨r, hr, fun w hw p hp v hv0 hvv hvf => ?_⟩
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv0
  set u := ‖v‖⁻¹ • v
  have hvu : v = ‖v‖ • u := by simp [u, smul_smul, hn.ne']
  have huS : (w, u) ∈ S := by
    refine ⟨hw, by simp [u, norm_smul, hn.ne'], ?_, ?_⟩
    · simp only [u, form_smul_left, form_smul_right]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
        (mul_nonpos_of_nonneg_of_nonpos (by positivity) hvv)
    · simp only [u, map_smul, smul_eq_mul]
      positivity
  have hmem : (w, p, u) ∈ {q | Φ q < 0} := by
    refine hsub (Metric.mem_thickening_iff.2 ⟨(w, w, u), ⟨(w, u), huS, rfl⟩, ?_⟩)
    simp only [Prod.dist_eq, dist_self]
    simpa using hp
  simp only [mem_ofPred_eq, Φ, cov, max_lt_iff] at hmem
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hmem
  rw [hvu]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [coform_eq_bil] at h1
    simp only [ofLp_smul, mulVec_smul, coform_eq_bil, map_smul, LinearMap.smul_apply,
      smul_eq_mul]
    exact mul_neg_of_pos_of_neg hn (mul_neg_of_pos_of_neg hn h1)
  · rw [form_smul_left]
    exact mul_neg_of_pos_of_neg hn h2
  · rw [form_smul_left, form_smul_right]
    exact mul_neg_of_pos_of_neg hn (mul_neg_of_pos_of_neg hn h3)
  · rw [map_smul, smul_eq_mul]
    exact mul_pos hn (by linarith)

end Frozen

section Quadratic

variable (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)

/-- The form `A`, as a continuous bilinear map. -/
def formCLM : E n →L[ℝ] E n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ
    LinearMap.mk₂ ℝ (form A) (fun _ _ _ => form_add_left _ _ _ _)
      (fun _ _ _ => form_smul_left _ _ _ _) (fun _ _ _ => form_add_right _ _ _ _)
      (fun _ _ _ => form_smul_right _ _ _ _))

/-- `formCLM A u v = A(u, v)`. -/
theorem formCLM_apply (u v : E n) : formCLM A u v = form A u v := by rfl

/-- `Q(p) = -A(y - p, y - p)`. -/
def frozenQ (y p : E n) : ℝ := -form A (y - p) (y - p)

theorem frozenQ_def (y p : E n) :
    frozenQ A y p = -form A (y - p) (y - p) := by rfl

/-- `Q` is smooth. -/
theorem contDiff_frozenQ (y : E n) : ContDiff ℝ ∞ (frozenQ A y) := by
  have : frozenQ A y = fun p => -formCLM A (y - p) (y - p) := by rfl
  rw [this]
  exact ((formCLM A).isBoundedBilinearMap.contDiff.comp
    ((contDiff_const.sub contDiff_id).prodMk (contDiff_const.sub contDiff_id))).neg

variable {A}

/-- `dQ_p(u) = 2 A(y - p, u)` for symmetric `A`. -/
theorem fderiv_frozenQ_apply (hA : Aᵀ = A) (y p u : E n) :
    fderiv ℝ (frozenQ A y) p u = 2 * form A (y - p) u := by
  have hf : HasFDerivAt (fun p : E n => y - p) (-ContinuousLinearMap.id ℝ (E n)) p := by
    simpa using (hasFDerivAt_id p).const_sub y
  have h := ((formCLM A).hasFDerivAt_of_bilinear hf hf).fun_neg
  have e : frozenQ A y = fun p => -formCLM A (y - p) (y - p) := rfl
  rw [e, h.fderiv]
  simp [formCLM_apply, ContinuousLinearMap.compL_apply]
  rw [form_comm hA u p, form_comm hA u y, form_sub_left]
  ring

/-- `dQ_p = 2 A (y - p)` as a covector, for symmetric `A`. -/
theorem d_frozenQ (hA : Aᵀ = A) (y p : E n) :
    d (frozenQ A y) p = (2 : ℝ) • (A *ᵥ ofLp (y - p)) := by
  ext k
  rw [d_def, fderiv_frozenQ_apply hA, form_comm hA, form_eq_bil, bil_apply]
  simp [EuclideanSpace.single, dotProduct]

end Quadratic

end

end LorentzianCalderon
