module

public import LorentzianCalderon.Waves.Source
public import LorentzianCalderon.Waves.Amplitude
public import LorentzianCalderon.Waves.Transport

public section

/-!
# One-sided retarded waves

Blueprint `lem_onesided`, for a spacetime `(g, Y)`. The hypotheses are the conclusions of the
emission lemma `lem_emission` (`IsEmission`): a null geodesic `σ`, an eikonal phase `φ` of
future type on an open set `T ⊇ σ([t₁, t₂])` with `φ ∘ σ = 0` and `Z = -grad φ` tangent to `σ`
there, and a timelike curve `μ` with `J⁺(μ s) ∩ T = {φ ≥ s}`.

The conclusions (`IsOneSidedWave`) are a cut-off `θ` near `σ(t_*)`, an open neighbourhood `V`
of `p₀ = σ(1)`, a smooth family `u_s` and sources `F_s` supported in `supp θ ∩ {φ = s}` such
that `G^ret F_s = u_s H(φ - s)` on `V` with `u_s > 0` on the front, together with the
conormal properties of `lem_conormal`(b) on `V`.

The construction is split in two steps:
* `IsAmplitude`: the output of the flow-box construction (transport equations and Borel's
  lemma): an amplitude `B(x, r)` on an open set `𝓑` whose wave `ũ_s = B(·, φ - s)` satisfies
  `2 Z ũ_s + ũ_s □φ = θ` on `{φ = s}` and `□ ũ_s = R(·, φ - s)` with a remainder `R` such that
  `R_+ = R H` is smooth, a cut-off `χ` and the neighbourhood `V`.
* `IsAmplitude.isOneSidedWave`: the sources `F_s = □Π_s - χ R_+(·, φ - s) - E_s` with
  `Π_s = χ ũ_s H(φ - s)` and the identity `G^ret F_s = Π_s - w_s - G^ret E_s`, where
  `w_s = G^ret (χ R_+(·, φ - s))`. As functionals, `F_s ψ = ∫ H(φ - s) ũ_s □(χ ψ) dV -
  ∫ χ R_+(·, φ - s) ψ dV`; the support of `F_s` follows from the weak jump identity.
-/

namespace LorentzianCalderon

noncomputable section
open MeasureTheory Set Filter Function
open scoped ContDiff Topology

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n}

/-! ### Hypotheses and conclusions -/

/-- `φ` is eikonal of future type on the open set `T`: smooth, `g(dφ, dφ) = 0`, `dφ ≠ 0`, and
`Z = -grad φ` is future-directed. -/
structure IsFutureEikonal (g : MatrixField n) (Y : E n → E n) (φ : E n → ℝ) (T : Set (E n)) :
    Prop where
  isOpen : IsOpen T
  smooth : ContDiffOn ℝ ∞ φ T
  eikonal : ∀ x ∈ T, coform g x (d φ x) (d φ x) = 0
  d_ne_zero : ∀ x ∈ T, d φ x ≠ 0
  future : ∀ x ∈ T, IsFutureCausal g Y x (-grad g φ x)

/-- The conclusions of the emission lemma `lem_emission`, the hypotheses of `lem_onesided`:
`σ` is a future-directed null geodesic on `[0, b]` with `σ(b) ∉ I⁺(σ(0))`,
`0 < t₁ < 1 < t₂ < b`, `φ` is eikonal of future type on the open set `T ⊇ σ([t₁, t₂])` with
values in `(-η, η)`, `φ(σ(t)) = 0` and `Z(σ(t))` a positive multiple of `σ'(t)` for
`t ∈ [t₁, t₂]`, and `μ` is a future-directed timelike curve with `J⁺(μ(s)) ∩ T = {φ ≥ s}` for
`|s| < η`. -/
structure IsEmission (g : MatrixField n) (Y : E n → E n) (σ : ℝ → E n) (b t₁ t₂ η : ℝ)
    (T : Set (E n)) (φ : E n → ℝ) (μ : ℝ → E n) : Prop where
  geodesic : ∃ I, IsGeodesic g σ I ∧ Icc 0 b ⊆ I
  null : ∀ t ∈ Icc 0 b, form (g (σ t)) (deriv σ t) (deriv σ t) = 0
  future : ∀ t ∈ Icc 0 b, IsFutureCausal g Y (σ t) (deriv σ t)
  notMem_chronFuture : σ b ∉ chronFuture g Y (σ 0)
  t₁_pos : 0 < t₁
  t₁_lt_one : t₁ < 1
  one_lt_t₂ : 1 < t₂
  t₂_lt : t₂ < b
  η_pos : 0 < η
  image_subset : σ '' Icc t₁ t₂ ⊆ T
  eikonal : IsFutureEikonal g Y φ T
  mem_Ioo : ∀ x ∈ T, φ x ∈ Ioo (-η) η
  front : ∀ t ∈ Icc t₁ t₂, φ (σ t) = 0
  tangent : ∀ t ∈ Icc t₁ t₂, ∃ c : ℝ, 0 < c ∧ -grad g φ (σ t) = c • deriv σ t
  curve_smooth : ContDiffOn ℝ ∞ μ (Ioo (-η) η)
  curve_timelike : ∀ s ∈ Ioo (-η) η, IsFutureTimelike g Y (μ s) (deriv μ s)
  causalFuture_inter : ∀ s ∈ Ioo (-η) η, causalFuture g Y (μ s) ∩ T = {x ∈ T | s ≤ φ x}

/-- The conclusions of `lem_onesided` and of `lem_conormal`(b): `θ ≥ 0` is a test function
supported in `N ∩ T`; `V ⊆ T` is an open neighbourhood of `p₀` disjoint from `supp θ`; for
`|s| < η`, `F s` is a source supported in `supp θ ∩ {φ = s} ⊆ J⁺(μ(s))` whose retarded solution
is `u_s H(φ - s)` on `V`, with `u_s > 0` on `{φ = s}`, `□ u_s = (φ - s) a_s` with `a_s = 0` on
`{φ > s}`, and `2 Z u_s + u_s □φ = (φ - s) b_s`. -/
structure IsOneSidedWave (g : MatrixField n) (Y : E n → E n) (φ : E n → ℝ) (T N : Set (E n))
    (μ : ℝ → E n) (η : ℝ) (p₀ : E n) (θ : E n → ℝ) (V : Set (E n))
    (u a b : ℝ → E n → ℝ) (F : ℝ → (E n → ℝ) → ℝ) : Prop where
  theta_smooth : ContDiff ℝ ∞ θ
  theta_hasCompactSupport : HasCompactSupport θ
  tsupport_theta_subset : tsupport θ ⊆ N ∩ T
  theta_nonneg : ∀ x, 0 ≤ θ x
  isOpen : IsOpen V
  mem : p₀ ∈ V
  subset : V ⊆ T
  disjoint : Disjoint V (tsupport θ)
  smooth : ContDiffOn ℝ ∞ (fun p : ℝ × E n => u p.1 p.2) (Ioo (-η) η ×ˢ V)
  source : ∀ s ∈ Ioo (-η) η, IsSource (F s) (tsupport θ ∩ {x | φ x = s})
  source_subset : ∀ s ∈ Ioo (-η) η, tsupport θ ∩ {x | φ x = s} ⊆ causalFuture g Y (μ s)
  retarded : ∀ s ∈ Ioo (-η) η,
    AgreesOn g (retardedS g Y (F s)) ({x | s ≤ φ x}.indicator (u s)) V
  pos : ∀ s ∈ Ioo (-η) η, ∀ x ∈ V, φ x = s → 0 < u s x
  a_smooth : ContDiffOn ℝ ∞ (fun p : ℝ × E n => a p.1 p.2) (Ioo (-η) η ×ˢ V)
  b_smooth : ContDiffOn ℝ ∞ (fun p : ℝ × E n => b p.1 p.2) (Ioo (-η) η ×ˢ V)
  box_eq : ∀ s ∈ Ioo (-η) η, ∀ x ∈ V, box g (u s) x = (φ x - s) * a s x
  a_eq_zero : ∀ s ∈ Ioo (-η) η, ∀ x ∈ V, s < φ x → a s x = 0
  transport : ∀ s ∈ Ioo (-η) η, ∀ x ∈ V,
    2 * -coform g x (d φ x) (d (u s) x) + u s x * box g φ x = (φ x - s) * b s x

/-- The output of the flow-box construction of `lem_onesided`. On the open set `Bx ⊆ T`, the
amplitude `B(x, r)` is smooth, its waves `ũ_s = B(·, φ - s)` satisfy the transport equation
`2 Z ũ_s + ũ_s □φ = θ` on `{φ = s}` and `□ ũ_s = R(·, φ - s)`, where `R` vanishes to infinite
order at `r = 0`, so that `R_+ = R H` is smooth. The cut-off `χ`, supported in `Bx`, is `1` near
the points of the support of `B` below the level `ϱout` of a Cauchy temporal function `ϱ`. The
open set `V` lies below that level, where `χ = 1`, outside `supp θ`, and `B(·, 0) > 0` on it. -/
structure IsAmplitude (g : MatrixField n) (Y : E n → E n) (φ : E n → ℝ) (T : Set (E n))
    (θ : E n → ℝ) (Bx : Set (E n)) (B R : E n → ℝ → ℝ) (χ ϱ : E n → ℝ) (ϱout : ℝ)
    (V : Set (E n)) : Prop where
  isOpen : IsOpen Bx
  subset : Bx ⊆ T
  smooth : ContDiffOn ℝ ∞ (fun q : E n × ℝ => B q.1 q.2) (Bx ×ˢ univ)
  transport : ∀ s, ∀ x ∈ Bx, φ x = s →
    2 * -coform g x (d φ x) (d (fun y => B y (φ y - s)) x) + B x 0 * box g φ x = θ x
  remainder_smooth : ContDiffOn ℝ ∞ (fun q : E n × ℝ => R q.1 q.2) (Bx ×ˢ univ)
  remainder_pos_smooth :
    ContDiffOn ℝ ∞ (fun q : E n × ℝ => if 0 < q.2 then R q.1 q.2 else 0) (Bx ×ˢ univ)
  remainder_zero : ∀ x ∈ Bx, R x 0 = 0
  box_eq : ∀ s, ∀ x ∈ Bx, box g (fun y => B y (φ y - s)) x = R x (φ x - s)
  cutoff_smooth : ContDiff ℝ ∞ χ
  cutoff_hasCompactSupport : HasCompactSupport χ
  tsupport_cutoff_subset : tsupport χ ⊆ Bx
  temporal : IsCauchyTemporal g Y ϱ
  cutoff_eq_one : ∀ x ∈ Bx, ϱ x < ϱout → ∀ r, B x r ≠ 0 → ∀ᶠ y in 𝓝 x, χ y = 1
  isOpen_V : IsOpen V
  cutoff_eq_one_of_mem : ∀ x ∈ V, χ x = 1
  lt_of_mem : ∀ x ∈ V, ϱ x < ϱout
  disjoint : Disjoint V (tsupport θ)
  pos : ∀ x ∈ V, 0 < B x 0

/-! ### The sources and the solutions -/

variable (φ χ : E n → ℝ) (R : E n → ℝ → ℝ) in
/-- The smooth part `χ R_+(·, φ - s)` of `□ Π_s`. -/
def remainderSource (s : ℝ) (x : E n) : ℝ :=
  χ x * if 0 < φ x - s then R x (φ x - s) else 0

theorem remainderSource_def (φ χ : E n → ℝ) (R : E n → ℝ → ℝ) (s : ℝ) (x : E n) :
    remainderSource φ χ R s x =
      χ x * if 0 < φ x - s then R x (φ x - s) else 0 := by rfl

variable (g) (φ χ : E n → ℝ) (B R : E n → ℝ → ℝ) in
/-- The source `F_s = □Π_s - χ R_+(·, φ - s) - E_s`, with `Π_s = χ ũ_s H(φ - s)` and
`E_s = [□, χ](ũ_s H(φ - s))`, as a functional:
`F_s ψ = ∫ H(φ - s) ũ_s □(χ ψ) dV - ∫ χ R_+(·, φ - s) ψ dV`. -/
def waveSource (s : ℝ) : (E n → ℝ) → ℝ := fun ψ =>
  (∫ x, {x | s < φ x}.indicator (fun y => B y (φ y - s)) x * box g (fun y => χ y * ψ y) x *
      √|(g x).det|) -
    ∫ x, remainderSource φ χ R s x * ψ x * √|(g x).det|

variable (g Y) (φ χ : E n → ℝ) (B R : E n → ℝ → ℝ) in
/-- The wave `u_s = χ ũ_s - w_s` with `w_s = G^ret (χ R_+(·, φ - s))`. -/
def oneSidedWave (s : ℝ) (x : E n) : ℝ :=
  χ x * B x (φ x - s) - retarded g Y (remainderSource φ χ R s) x

section Assembly

variable {φ θ χ ϱ : E n → ℝ} {T Bx V : Set (E n)} {B R : E n → ℝ → ℝ} {ϱout : ℝ}

theorem IsAmplitude.contDiffOn_wave (hφ : IsFutureEikonal g Y φ T)
    (hA : IsAmplitude g Y φ T θ Bx B R χ ϱ ϱout V) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E n => B p.2 (φ p.2 - p.1)) (univ ×ˢ Bx) :=
  contDiffOn_comp_sub (hφ.smooth.mono hA.subset) hA.smooth

theorem IsAmplitude.contDiffOn_wave_apply (hφ : IsFutureEikonal g Y φ T)
    (hA : IsAmplitude g Y φ T θ Bx B R χ ϱ ϱout V) (s : ℝ) :
    ContDiffOn ℝ ∞ (fun y => B y (φ y - s)) Bx :=
  (hA.contDiffOn_wave hφ).comp (contDiff_const.prodMk contDiff_id).contDiffOn
    fun _ hx => ⟨mem_univ _, hx⟩

theorem IsAmplitude.contDiff_cutoff_mul_wave (hφ : IsFutureEikonal g Y φ T)
    (hA : IsAmplitude g Y φ T θ Bx B R χ ϱ ϱout V) :
    ContDiff ℝ ∞ (fun p : ℝ × E n => χ p.2 * B p.2 (φ p.2 - p.1)) :=
  contDiff_mul_param (f := fun s x => B x (φ x - s)) hA.isOpen hA.cutoff_smooth
    hA.tsupport_cutoff_subset (hA.contDiffOn_wave hφ)

theorem IsAmplitude.contDiff_remainderSource (hφ : IsFutureEikonal g Y φ T)
    (hA : IsAmplitude g Y φ T θ Bx B R χ ϱ ϱout V) :
    ContDiff ℝ ∞ (fun p : ℝ × E n => remainderSource φ χ R p.1 p.2) :=
  contDiff_mul_param (f := fun s x => if 0 < φ x - s then R x (φ x - s) else 0) hA.isOpen
    hA.cutoff_smooth hA.tsupport_cutoff_subset
    (contDiffOn_comp_sub (B := fun x r => if 0 < r then R x r else 0)
      (hφ.smooth.mono hA.subset) hA.remainder_pos_smooth)

theorem IsAmplitude.contDiff_remainderSource_apply (hφ : IsFutureEikonal g Y φ T)
    (hA : IsAmplitude g Y φ T θ Bx B R χ ϱ ϱout V) (s : ℝ) :
    ContDiff ℝ ∞ (remainderSource φ χ R s) :=
  (hA.contDiff_remainderSource hφ).comp (contDiff_const.prodMk contDiff_id)

theorem support_remainderSource_subset (s : ℝ) :
    support (remainderSource φ χ R s) ⊆ tsupport χ := fun x hx =>
  subset_tsupport _ fun h => hx (by simp [remainderSource, h])

theorem IsAmplitude.hasCompactSupport_remainderSource
    (hA : IsAmplitude g Y φ T θ Bx B R χ ϱ ϱout V) (s : ℝ) :
    HasCompactSupport (remainderSource φ χ R s) :=
  HasCompactSupport.intro hA.cutoff_hasCompactSupport fun _ hx =>
    notMem_support.1 fun h => hx (support_remainderSource_subset s h)

theorem IsAmplitude.tsupport_remainderSource_subset (hφ : IsFutureEikonal g Y φ T)
    (hA : IsAmplitude g Y φ T θ Bx B R χ ϱ ϱout V) (s : ℝ) :
    tsupport (remainderSource φ χ R s) ⊆ tsupport χ ∩ φ ⁻¹' Ici s := by
  refine closure_minimal (fun x hx => ⟨support_remainderSource_subset s hx, ?_⟩)
    ((hφ.smooth.continuousOn.mono
      (hA.tsupport_cutoff_subset.trans hA.subset)).preimage_isClosed_of_isClosed
      (isClosed_tsupport _) isClosed_Ici)
  by_contra h
  simp only [mem_preimage, mem_Ici, not_le] at h
  exact hx (by simp [remainderSource, show ¬ 0 < φ x - s by linarith])

theorem IsAmplitude.contDiff_oneSidedWave (hg : IsSpacetime g Y) (hφ : IsFutureEikonal g Y φ T)
    (hA : IsAmplitude g Y φ T θ Bx B R χ ϱ ϱout V) :
    ContDiff ℝ ∞ (fun p : ℝ × E n => oneSidedWave g Y φ χ B R p.1 p.2) :=
  (hA.contDiff_cutoff_mul_wave hφ).sub (contDiff_retarded_param hg
    (hA.contDiff_remainderSource hφ) hA.cutoff_hasCompactSupport
    support_remainderSource_subset)

theorem IsAmplitude.subset_of_mem (hA : IsAmplitude g Y φ T θ Bx B R χ ϱ ϱout V) : V ⊆ Bx :=
  fun x hx => hA.tsupport_cutoff_subset
    (subset_tsupport _ (show x ∈ support χ by simp [hA.cutoff_eq_one_of_mem x hx]))

/-- The cut-off `χ` is `1` near the points of `V`. -/
theorem IsAmplitude.cutoff_eventuallyEq (hA : IsAmplitude g Y φ T θ Bx B R χ ϱ ϱout V)
    {x : E n} (hx : x ∈ V) : ∀ᶠ y in 𝓝 x, χ y = 1 :=
  eventually_of_mem (hA.isOpen_V.mem_nhds hx) hA.cutoff_eq_one_of_mem

theorem IsAmplitude.cutoff_mul_eventuallyEq (hA : IsAmplitude g Y φ T θ Bx B R χ ϱ ϱout V)
    {x : E n} (hx : x ∈ V) (f : E n → ℝ) : (fun y => χ y * f y) =ᶠ[𝓝 x] f := by
  filter_upwards [hA.cutoff_eventuallyEq hx] with y hy
  rw [hy, one_mul]

/-- `w_s` vanishes on `V ∩ {φ < s}`: its source lies in `{φ ≥ s} ∩ T ⊆ J⁺(μ(s))`. -/
theorem IsAmplitude.retarded_eq_zero_of_lt (hφ : IsFutureEikonal g Y φ T)
    (hA : IsAmplitude g Y φ T θ Bx B R χ ϱ ϱout V) {μ : ℝ → E n} {s : ℝ}
    (hμ : causalFuture g Y (μ s) ∩ T = {x ∈ T | s ≤ φ x}) {x : E n} (hx : x ∈ V)
    (hxs : φ x < s) : retarded g Y (remainderSource φ χ R s) x = 0 := by
  by_contra hw
  obtain ⟨p, hp, hpx⟩ := mem_causalFutureSet.1 (support_retarded_subset hw)
  obtain ⟨hpχ, hps⟩ := hA.tsupport_remainderSource_subset hφ s hp
  have hpT : p ∈ T := hA.subset (hA.tsupport_cutoff_subset hpχ)
  have hp' : p ∈ causalFuture g Y (μ s) ∩ T := by rw [hμ]; exact ⟨hpT, hps⟩
  have hxT : x ∈ T := hA.subset (hA.subset_of_mem hx)
  have hx' : x ∈ causalFuture g Y (μ s) ∩ T :=
    ⟨mem_causalFuture.2 ((mem_causalFuture.1 hp'.1).trans (mem_causalFuture.1 hpx)), hxT⟩
  rw [hμ] at hx'
  exact absurd hx'.2 (not_le.2 hxs)

theorem IsFutureEikonal.fderiv_ne_zero (hφ : IsFutureEikonal g Y φ T) {x : E n} (hx : x ∈ T) :
    fderiv ℝ φ x ≠ 0 := fun h => hφ.d_ne_zero x hx (by ext j; simp [d_def, h])

/-- `w_s` and its differential vanish on `V ∩ {φ = s}`. -/
theorem IsAmplitude.retarded_eq_zero_of_eq (hφ : IsFutureEikonal g Y φ T)
    (hA : IsAmplitude g Y φ T θ Bx B R χ ϱ ϱout V) {μ : ℝ → E n} {s : ℝ}
    (hμ : causalFuture g Y (μ s) ∩ T = {x ∈ T | s ≤ φ x}) {x : E n} (hx : x ∈ V)
    (hxs : φ x = s) : retarded g Y (remainderSource φ χ R s) x = 0 ∧
      fderiv ℝ (retarded g Y (remainderSource φ χ R s)) x = 0 := by
  set w := retarded g Y (remainderSource φ χ R s)
  have hxT : x ∈ T := hA.subset (hA.subset_of_mem hx)
  have hcl : x ∈ closure (V ∩ {y | φ y < φ x}) :=
    mem_closure_lt_of_fderiv_ne_zero (hA.isOpen_V.mem_nhds hx)
      ((hφ.smooth.contDiffAt (hφ.isOpen.mem_nhds hxT)).differentiableAt (by simp))
      (hφ.fderiv_ne_zero hxT)
  rw [hxs] at hcl
  have hO : IsOpen (V ∩ {y | φ y < s}) :=
    (hφ.smooth.continuousOn.mono fun y hy => hA.subset (hA.subset_of_mem hy)).isOpen_inter_preimage
      hA.isOpen_V isOpen_Iio
  have hw0 : ∀ y ∈ V ∩ {y | φ y < s}, w y = 0 := fun y hy =>
    hA.retarded_eq_zero_of_lt hφ hμ hy.1 hy.2
  refine ⟨(isClosed_eq contDiff_retarded.continuous continuous_const).closure_subset_iff.2
    hw0 hcl, ?_⟩
  exact (isClosed_eq (contDiff_retarded.continuous_fderiv (by simp))
    continuous_const).closure_subset_iff.2
    (fun y hy => fderiv_eq_zero_of_isOpen hO hw0 hy) hcl

/-- Integrability of the pairing of `H(φ - s) f` with a function `q` supported in an open set
on which `φ` is continuous and `f` is smooth. -/
theorem integrable_indicator_mul {φ f q : E n → ℝ} {U : Set (E n)} (hU : IsOpen U)
    (hφ : ContinuousOn φ U) (hf : ContDiffOn ℝ ∞ f U) (hq : ContDiff ℝ ∞ q)
    (hqc : HasCompactSupport q) (hqU : tsupport q ⊆ U) (s : ℝ) {ρ : E n → ℝ}
    (hρ : Continuous ρ) :
    Integrable fun x => {x | s < φ x}.indicator f x * q x * ρ x := by
  have hc : ContDiff ℝ ∞ fun x => q x * f x := contDiff_mul_of_tsupport_subset hU hq hqU hf
  have hi : Integrable fun x => q x * f x * ρ x :=
    integrable_of_eq_zero_off (hc.continuous.mul hρ) hqc fun x hx => by
      simp [image_eq_zero_of_notMem_tsupport hx]
  have hO : MeasurableSet (U ∩ φ ⁻¹' Ioi s) :=
    (hφ.isOpen_inter_preimage hU isOpen_Ioi).measurableSet
  refine (hi.indicator hO).congr (Eventually.of_forall fun x => ?_)
  dsimp only
  by_cases hxU : x ∈ U
  · by_cases hxs : s < φ x
    · rw [indicator_of_mem (show x ∈ U ∩ φ ⁻¹' Ioi s from ⟨hxU, hxs⟩),
        indicator_of_mem (show x ∈ {x | s < φ x} from hxs)]
      ring
    · simp [indicator_of_notMem (show x ∉ U ∩ φ ⁻¹' Ioi s from fun h => hxs h.2),
        indicator_of_notMem (show x ∉ {x | s < φ x} from hxs)]
  · have : q x = 0 := image_eq_zero_of_notMem_tsupport fun h => hxU (hqU h)
    simp [indicator_of_notMem (show x ∉ U ∩ φ ⁻¹' Ioi s from fun h => hxU h.1), this]

variable (hg : IsSpacetime g Y) (hφ : IsFutureEikonal g Y φ T)
  (hA : IsAmplitude g Y φ T θ Bx B R χ ϱ ϱout V)
include hg hφ hA

theorem IsAmplitude.integrable_waveSource_left {ψ : E n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (s : ℝ) :
    Integrable fun x => {x | s < φ x}.indicator (fun y => B y (φ y - s)) x *
      box g (fun y => χ y * ψ y) x * √|(g x).det| :=
  integrable_indicator_mul hA.isOpen (hφ.smooth.continuousOn.mono hA.subset)
    (hA.contDiffOn_wave_apply hφ s) (contDiff_box hg.smooth hg.det_ne_zero
      (hA.cutoff_smooth.mul hψ)) (hasCompactSupport_box hA.cutoff_hasCompactSupport.mul_right)
    ((tsupport_box_subset _).trans ((tsupport_mul_subset_left (f := χ) (g := ψ)).trans
      hA.tsupport_cutoff_subset)) s (contDiff_sqrt_abs_det hg.smooth hg.det_ne_zero).continuous

theorem IsAmplitude.integrable_waveSource_right {ψ : E n → ℝ} (hψ : Continuous ψ) (s : ℝ) :
    Integrable fun x => remainderSource φ χ R s x * ψ x * √|(g x).det| :=
  integrable_of_eq_zero_off
    (((hA.contDiff_remainderSource_apply hφ s).continuous.mul hψ).mul
      (contDiff_sqrt_abs_det hg.smooth hg.det_ne_zero).continuous)
    (hA.hasCompactSupport_remainderSource s) fun x hx => by
      simp [image_eq_zero_of_notMem_tsupport hx]

/-- The source `F_s` is supported in `supp θ ∩ {φ = s}`. -/
theorem IsAmplitude.isSource_waveSource (hθ : HasCompactSupport θ) (hθT : tsupport θ ⊆ T)
    (s : ℝ) : IsSource (waveSource g φ χ B R s) (tsupport θ ∩ {x | φ x = s}) where
  isCompact := hθ.isCompact.of_isClosed_subset
    ((hφ.smooth.continuousOn.mono hθT).preimage_isClosed_of_isClosed (isClosed_tsupport _)
      isClosed_singleton) inter_subset_left
  map_add φ₁ φ₂ h₁ h₂ := by
    simp only [waveSource]
    have hb : ∀ x, box g (fun y => χ y * (φ₁ + φ₂) y) x =
        box g (fun y => χ y * φ₁ y) x + box g (fun y => χ y * φ₂ y) x := fun x => by
      rw [← box_add hg.smooth hg.det_ne_zero (hA.cutoff_smooth.mul h₁)
        (hA.cutoff_smooth.mul h₂)]
      congr 1
      ext y
      simp only [Pi.add_apply]
      ring
    simp only [hb]
    simp only [mul_add, add_mul, Pi.add_apply]
    rw [integral_add (hA.integrable_waveSource_left hg hφ h₁ s)
        (hA.integrable_waveSource_left hg hφ h₂ s),
      integral_add (hA.integrable_waveSource_right hg hφ h₁.continuous s)
        (hA.integrable_waveSource_right hg hφ h₂.continuous s)]
    ring
  map_smul c ψ hψ := by
    simp only [waveSource]
    have hb : ∀ x, box g (fun y => χ y * (c • ψ) y) x = c * box g (fun y => χ y * ψ y) x :=
      fun x => by
        rw [← box_const_mul hg.smooth hg.det_ne_zero (hA.cutoff_smooth.mul hψ)]
        congr 1
        ext y
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
    simp only [hb]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_sub, ← integral_const_mul, ← integral_const_mul]
    congr 1
    · congr 1
      ext x
      ring
    · congr 1
      ext x
      ring
  eq_zero ψ hψ hψ0 := by
    set h : E n → ℝ := fun y => χ y * ψ y
    have hh : ContDiff ℝ ∞ h := hA.cutoff_smooth.mul hψ
    have hhc : HasCompactSupport h := hA.cutoff_hasCompactSupport.mul_right
    have hhB : tsupport h ⊆ Bx :=
      (tsupport_mul_subset_left (f := χ) (g := ψ)).trans hA.tsupport_cutoff_subset
    have hjump := integral_indicator_mul_box_eq hg.smooth hg.symm hg.det_ne_zero hA.isOpen
      (hA.contDiffOn_wave_apply hφ s) (hφ.smooth.mono hA.subset) hh hhc hhB
      (fun x hx => hφ.eikonal x (hA.subset hx)) (fun x hx => hφ.d_ne_zero x (hA.subset hx))
      (s := s) fun x hx hxs => by
        rw [show B x (φ x - s) = B x 0 by rw [hxs, sub_self],
          hA.transport s x (hhB hx) hxs]
        by_contra hθx
        have hxK : x ∈ tsupport θ ∩ {x | φ x = s} := ⟨subset_tsupport _ hθx, hxs⟩
        have hev : h =ᶠ[𝓝 x] 0 := by
          filter_upwards [hψ0.filter_mono (nhds_le_nhdsSet hxK)] with y hy
          simp [h, hy]
        exact notMem_tsupport_iff_eventuallyEq.2 hev hx
    simp only [waveSource]
    rw [hjump, sub_eq_zero]
    congr 1
    ext x
    by_cases hx : x ∈ Bx
    · simp only [indicator_apply, mem_ofPred_eq, remainderSource, sub_pos, h]
      split_ifs with hxs
      · rw [hA.box_eq s x hx]
        ring
      · ring
    · have hχ : χ x = 0 :=
        image_eq_zero_of_notMem_tsupport fun h' => hx (hA.tsupport_cutoff_subset h')
      simp [h, remainderSource, hχ]

omit hφ in
/-- The past of a subset of `V` lies below the level `ϱout`. -/
theorem IsAmplitude.lt_of_mem_causalPastSet {K : Set (E n)} (hK : K ⊆ V) {x : E n}
    (hx : x ∈ causalPastSet g Y K) : ϱ x < ϱout := by
  obtain ⟨q, hq, hxq⟩ := mem_causalPastSet.1 hx
  exact (hA.temporal.le_of_causalLE hg (mem_causalPast.1 hxq)).trans_lt (hA.lt_of_mem q (hK hq))

/-- `G^ret F_s = H(φ - s) ũ_s - w_s` on `V`. -/
theorem IsAmplitude.retardedS_waveSource {s : ℝ} {h : E n → ℝ} (hh : ContDiff ℝ ∞ h)
    (hh' : HasCompactSupport h) (hhV : tsupport h ⊆ V) :
    retardedS g Y (waveSource g φ χ B R s) h =
      ∫ x, ({x | s < φ x}.indicator (fun y => B y (φ y - s)) x -
        retarded g Y (remainderSource φ χ R s) x) * h x * √|(g x).det| := by
  have hVB := hA.subset_of_mem
  have h0 : ∀ x ∉ V, h x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h' => hx (hhV h')
  have hleft : ∀ x, {x | s < φ x}.indicator (fun y => B y (φ y - s)) x *
      box g (fun y => χ y * advanced g Y h y) x * √|(g x).det| =
      {x | s < φ x}.indicator (fun y => B y (φ y - s)) x * h x * √|(g x).det| := by
    intro x
    by_cases hu : {x | s < φ x}.indicator (fun y => B y (φ y - s)) x = 0
    · simp [hu]
    congr 2
    have hB : B x (φ x - s) ≠ 0 := fun hB => hu (by simp [indicator_apply, hB])
    by_cases hxB : x ∈ Bx
    · by_cases hϱ : ϱ x < ϱout
      · rw [← box_advanced hg hh hh' x]
        refine box_congr ?_
        filter_upwards [hA.cutoff_eq_one x hxB hϱ _ hB] with y hy
        rw [hy, one_mul]
      · have hxJ : x ∉ causalPastSet g Y (tsupport h) := fun hJ =>
          hϱ (hA.lt_of_mem_causalPastSet hg hhV hJ)
        rw [h0 x fun hxV => hϱ (hA.lt_of_mem x hxV)]
        refine box_eq_zero_of_eventuallyEq ?_
        filter_upwards [advanced_eventuallyEq_zero hxJ] with y hy
        simp [show advanced g Y h y = 0 from hy]
    · have hev : χ =ᶠ[𝓝 x] 0 :=
        notMem_tsupport_iff_eventuallyEq.1 fun h' => hxB (hA.tsupport_cutoff_subset h')
      rw [h0 x fun hxV => hxB (hVB hxV)]
      refine box_eq_zero_of_eventuallyEq ?_
      filter_upwards [hev] with y hy
      simp [show χ y = 0 from hy]
  have hρ := (contDiff_sqrt_abs_det hg.smooth hg.det_ne_zero).continuous
  simp only [retardedS_def, waveSource, hleft]
  rw [← integral_retarded_mul hg (hA.contDiff_remainderSource_apply hφ s)
    (hA.hasCompactSupport_remainderSource s) hh hh', ← integral_sub]
  · congr 1
    ext x
    ring
  · exact integrable_indicator_mul hA.isOpen (hφ.smooth.continuousOn.mono hA.subset)
      (hA.contDiffOn_wave_apply hφ s) hh hh' (hhV.trans hVB) s hρ
  · exact integrable_of_eq_zero_off ((contDiff_retarded.continuous.mul hh.continuous).mul hρ)
      hh' fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx]

/-- **One-sided retarded waves** (`lem_onesided`), from the output of the flow-box
construction. -/
theorem IsAmplitude.isOneSidedWave {N : Set (E n)} {μ : ℝ → E n} {η : ℝ} {p₀ : E n}
    (hμ : ∀ s ∈ Ioo (-η) η, causalFuture g Y (μ s) ∩ T = {x ∈ T | s ≤ φ x})
    (hφη : ∀ x ∈ T, φ x ∈ Ioo (-η) η) (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ)
    (hθN : tsupport θ ⊆ N ∩ T) (hθ0 : ∀ x, 0 ≤ θ x) (hp₀ : p₀ ∈ V) :
    ∃ a b : ℝ → E n → ℝ, IsOneSidedWave g Y φ T N μ η p₀ θ V (oneSidedWave g Y φ χ B R) a b
      (waveSource g φ χ B R) := by
  set u := oneSidedWave g Y φ χ B R with hu_def
  set w := fun s => retarded g Y (remainderSource φ χ R s)
  have hu : ContDiff ℝ ∞ fun p : ℝ × E n => u p.1 p.2 := hA.contDiff_oneSidedWave hg hφ
  have hVB := hA.subset_of_mem
  have hVT : V ⊆ T := hVB.trans hA.subset
  have hφV : ContDiffOn ℝ ∞ φ V := hφ.smooth.mono hVT
  have hVsub : (univ : Set ℝ) ×ˢ V ⊆ univ ×ˢ Bx := prod_mono subset_rfl hVB
  have hχu : ∀ s, ContDiff ℝ ∞ fun y => χ y * B y (φ y - s) := fun s =>
    (hA.contDiff_cutoff_mul_wave hφ).comp (contDiff_const.prodMk contDiff_id)
  have hrem : ∀ s, ContDiff ℝ ∞ (remainderSource φ χ R s) :=
    hA.contDiff_remainderSource_apply hφ
  have hloc : ∀ s, ∀ x ∈ V, u s =ᶠ[𝓝 x] fun y => B y (φ y - s) - w s y := fun s x hx => by
    filter_upwards [hA.cutoff_eventuallyEq hx] with y hy
    simp [u, oneSidedWave, w, hy]
  have hval : ∀ s, ∀ x ∈ V, u s x = B x (φ x - s) - w s x := fun s x hx =>
    (hloc s x hx).eq_of_nhds
  have hdiffB : ∀ s, ∀ x ∈ V, DifferentiableAt ℝ (fun y => B y (φ y - s)) x := fun s x hx =>
    ((hA.contDiffOn_wave_apply hφ s).contDiffAt (hA.isOpen.mem_nhds (hVB hx))).differentiableAt
      (by simp)
  have hbox : ∀ s, ∀ x ∈ V, box g (u s) x =
      R x (φ x - s) - if 0 < φ x - s then R x (φ x - s) else 0 := fun s x hx => by
    have h1 : u s = fun y => χ y * B y (φ y - s) - w s y := rfl
    rw [h1, box_sub hg.smooth hg.det_ne_zero (hχu s) contDiff_retarded,
      box_congr (hA.cutoff_mul_eventuallyEq hx _), hA.box_eq s x (hVB hx),
      box_retarded hg (hrem s) (hA.hasCompactSupport_remainderSource s)]
    simp [remainderSource, hA.cutoff_eq_one_of_mem x hx]
  obtain ⟨a, ha, hfa⟩ := exists_eq_sub_mul_of_eq_zero hA.isOpen_V hφV
    (f := fun s x => R x (φ x - s) - if 0 < φ x - s then R x (φ x - s) else 0)
    (((contDiffOn_comp_sub (hφ.smooth.mono hA.subset) hA.remainder_smooth).sub
      (contDiffOn_comp_sub (B := fun x r => if 0 < r then R x r else 0)
        (hφ.smooth.mono hA.subset) hA.remainder_pos_smooth)).mono hVsub)
    fun x hx => by simp [hA.remainder_zero x (hVB hx)]
  have hcoef : ContDiffOn ℝ ∞ (fun p : ℝ × E n =>
      2 * -coform g p.2 (d φ p.2) (d (u p.1) p.2) + u p.1 p.2 * box g φ p.2) (univ ×ˢ V) := by
    have hsnd : MapsTo (fun p : ℝ × E n => p.2) (univ ×ˢ V) T := fun p hp => hVT hp.2
    have hdφ : ∀ j, ContDiffOn ℝ ∞ (fun p : ℝ × E n => d φ p.2 j) (univ ×ˢ V) := fun j =>
      (contDiffOn_d hφ.isOpen hφ.smooth j).comp contDiff_snd.contDiffOn hsnd
    have hbφ : ContDiffOn ℝ ∞ (fun p : ℝ × E n => box g φ p.2) (univ ×ˢ V) :=
      (contDiffOn_box hg.smooth hg.det_ne_zero hφ.isOpen hφ.smooth).comp
        contDiff_snd.contDiffOn hsnd
    simp only [coform_def]
    refine (contDiffOn_const.mul (ContDiffOn.neg (ContDiffOn.sum fun j _ =>
      ContDiffOn.sum fun k _ => ?_))).add (hu.contDiffOn.mul hbφ)
    exact ((((contDiff_inv_apply hg.smooth hg.det_ne_zero j k).comp contDiff_snd).contDiffOn.mul
      (hdφ j)).mul (contDiff_d_param hu k).contDiffOn)
  obtain ⟨b, hb, hfb⟩ := exists_eq_sub_mul_of_eq_zero hA.isOpen_V hφV
    (f := fun s x => 2 * -coform g x (d φ x) (d (u s) x) + u s x * box g φ x) hcoef
    fun x hx => by
      have hs := hφη x (hVT hx)
      obtain ⟨hw0, hdw0⟩ := hA.retarded_eq_zero_of_eq hφ (hμ _ hs) hx rfl
      have hd : d (u (φ x)) x = d (fun y => B y (φ y - φ x)) x := by
        funext j
        rw [d_congr (hloc _ x hx), d_sub (hdiffB _ x hx)
          (contDiff_retarded.differentiable (by simp) x)]
        simp [d_def, hdw0]
      rw [hd, hval _ x hx, show w (φ x) x = 0 from hw0, sub_zero, sub_self,
        hA.transport _ x (hVB hx) rfl]
      exact image_eq_zero_of_notMem_tsupport (Set.disjoint_left.1 hA.disjoint hx)
  have hnull : ∀ s, ∀ᵐ x, x ∉ V ∩ φ ⁻¹' {s} := fun s =>
    measure_eq_zero_iff_ae_notMem.1 (volume_inter_level_eq_zero hA.isOpen_V
      (hφV.of_le (by simp)) (fun x hx => hφ.fderiv_ne_zero (hVT hx)) s)
  refine ⟨a, b, {
    theta_smooth := hθ
    theta_hasCompactSupport := hθc
    tsupport_theta_subset := hθN
    theta_nonneg := hθ0
    isOpen := hA.isOpen_V
    mem := hp₀
    subset := hVT
    disjoint := hA.disjoint
    smooth := hu.contDiffOn
    source := fun s _ => hA.isSource_waveSource hg hφ hθc (hθN.trans inter_subset_right) s
    source_subset := fun s hs y hy => by
      have hyT : y ∈ T := (hθN hy.1).2
      have : y ∈ causalFuture g Y (μ s) ∩ T := by
        rw [hμ s hs]
        exact ⟨hyT, le_of_eq hy.2.symm⟩
      exact this.1
    retarded := fun s hs => agreesOn_iff.2 fun h hh hh' hhV => by
      rw [hA.retardedS_waveSource hg hφ hh hh' hhV]
      refine integral_congr_ae ?_
      filter_upwards [hnull s] with x hx
      by_cases hxV : x ∈ V
      · have hxs : φ x ≠ s := fun h' => hx ⟨hxV, h'⟩
        have hux := hval s x hxV
        rcases lt_or_gt_of_ne hxs with hlt | hgt
        · have : retarded g Y (remainderSource φ χ R s) x = 0 :=
            hA.retarded_eq_zero_of_lt hφ (hμ s hs) hxV hlt
          simp [not_lt.2 hlt.le, not_le.2 hlt, this]
        · simp [hgt, hgt.le, hux, w]
      · have : h x = 0 := image_eq_zero_of_notMem_tsupport fun h' => hxV (hhV h')
        simp [this]
    pos := fun s hs x hx hxs => by
      rw [hval s x hx, show w s x = 0 from (hA.retarded_eq_zero_of_eq hφ (hμ s hs) hx hxs).1,
        sub_zero, hxs, sub_self]
      exact hA.pos x hx
    a_smooth := ha.mono (prod_mono (subset_univ _) subset_rfl)
    b_smooth := hb.mono (prod_mono (subset_univ _) subset_rfl)
    box_eq := fun s _ x hx => by rw [hbox s x hx, hfa s x hx]
    a_eq_zero := fun s _ x hx hxs => by
      have h1 := hfa s x hx
      simp only [sub_pos.2 hxs, ite_true, sub_self] at h1
      exact (mul_eq_zero.1 h1.symm).resolve_left (sub_ne_zero.2 (ne_of_gt hxs))
    transport := fun s _ x hx => hfb s x hx }⟩

end Assembly

/-! ### The construction -/

/-- The output of the flow-box step of `lem_onesided`: the transport hierarchy
`2 Z b₀ + b₀ □φ = θ`, `2 Z b_{k+1} + b_{k+1} □φ = -□ b_k` on the open set `Bx ⊆ T` (solved along
the flow lines of `Z / Zϱ` from the level `ϱ = ϱ_in`), the cut-off `χ` (equal to `1` near the
points below the level `ϱout` where some `b_k` does not vanish) and the neighbourhood `V`. -/
structure IsTransport (g : MatrixField n) (Y : E n → E n) (φ : E n → ℝ) (T : Set (E n))
    (θ : E n → ℝ) (Bx : Set (E n)) (b : ℕ → E n → ℝ) (χ ϱ : E n → ℝ) (ϱout : ℝ)
    (V : Set (E n)) : Prop where
  isOpen : IsOpen Bx
  subset : Bx ⊆ T
  smooth : ∀ k, ContDiffOn ℝ ∞ (b k) Bx
  transport_zero : ∀ x ∈ Bx, 2 * -coform g x (d φ x) (d (b 0) x) + b 0 x * box g φ x = θ x
  transport_succ : ∀ k, ∀ x ∈ Bx,
    2 * -coform g x (d φ x) (d (b (k + 1)) x) + b (k + 1) x * box g φ x = -box g (b k) x
  cutoff_smooth : ContDiff ℝ ∞ χ
  cutoff_hasCompactSupport : HasCompactSupport χ
  tsupport_cutoff_subset : tsupport χ ⊆ Bx
  temporal : IsCauchyTemporal g Y ϱ
  cutoff_eq_one : ∀ x ∈ Bx, ϱ x < ϱout → (∃ k, b k x ≠ 0) → ∀ᶠ y in 𝓝 x, χ y = 1
  isOpen_V : IsOpen V
  cutoff_eq_one_of_mem : ∀ x ∈ V, χ x = 1
  lt_of_mem : ∀ x ∈ V, ϱ x < ϱout
  disjoint : Disjoint V (tsupport θ)
  pos : ∀ x ∈ V, 0 < b 0 x

/-- **Flow box and transport equations** (`lem_onesided`, first two steps): the cut-off `θ` near
`σ(t_*)`, the solutions `b_k` of the transport hierarchy and the cut-offs. This packages
`exists_transport_of_emission`, which needs only part of the hypotheses of `IsEmission`. -/
theorem IsEmission.exists_isTransport (hg : IsSpacetime g Y) {σ : ℝ → E n} {b t₁ t₂ η : ℝ}
    {T : Set (E n)} {φ : E n → ℝ} {μ : ℝ → E n} (hE : IsEmission g Y σ b t₁ t₂ η T φ μ)
    {t : ℝ} (ht : t ∈ Ioo t₁ 1) {N : Set (E n)} (hN : IsOpen N) (htN : σ t ∈ N) :
    ∃ (θ : E n → ℝ) (Bx : Set (E n)) (bk : ℕ → E n → ℝ) (χ ϱ : E n → ℝ) (ϱout : ℝ)
      (V : Set (E n)), ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧ tsupport θ ⊆ N ∩ T ∧
      (∀ x, 0 ≤ θ x) ∧ 0 < θ (σ t) ∧ σ 1 ∈ V ∧ IsTransport g Y φ T θ Bx bk χ ϱ ϱout V := by
  obtain ⟨θ, Bx, bk, χ, ϱ, ϱout, V, hθ, hθc, hθN, hθ0, hθt, h1V, hBo, hBT, hbk, htr0, htrs,
      hχ, hχc, hχB, hϱ, hχ1, hVo, hχV, hϱV, hVθ, hpos⟩ :=
    exists_transport_of_emission hg hE.geodesic hE.future (hE.t₁_pos) hE.t₂_lt hE.one_lt_t₂
      hE.eikonal.isOpen hE.eikonal.smooth hE.eikonal.future hE.image_subset hE.tangent ht hN htN
  exact ⟨θ, Bx, bk, χ, ϱ, ϱout, V, hθ, hθc, hθN, hθ0, hθt, h1V, {
    isOpen := hBo
    subset := hBT
    smooth := hbk
    transport_zero := htr0
    transport_succ := htrs
    cutoff_smooth := hχ
    cutoff_hasCompactSupport := hχc
    tsupport_cutoff_subset := hχB
    temporal := hϱ
    cutoff_eq_one := hχ1
    isOpen_V := hVo
    cutoff_eq_one_of_mem := hχV
    lt_of_mem := hϱV
    disjoint := hVθ
    pos := hpos }⟩

theorem IsTransport.exists_isAmplitude (hg : IsSpacetime g Y) {φ θ χ ϱ : E n → ℝ}
    {T Bx V : Set (E n)} {b : ℕ → E n → ℝ} {ϱout : ℝ} (hφ : IsFutureEikonal g Y φ T)
    (hT : IsTransport g Y φ T θ Bx b χ ϱ ϱout V) :
    ∃ B R : E n → ℝ → ℝ, IsAmplitude g Y φ T θ Bx B R χ ϱ ϱout V := by
  obtain ⟨B, R, hB, hR, hRp, hR0, hB0, hBb, hbox, hZ⟩ :=
    exists_amplitude_of_transport hg.smooth hg.symm hg.det_ne_zero hT.isOpen
      (hφ.smooth.mono hT.subset) (fun x hx => hφ.eikonal x (hT.subset hx)) hT.smooth
      hT.transport_succ
  exact ⟨B, R, {
    isOpen := hT.isOpen
    subset := hT.subset
    smooth := hB
    transport := fun s x hx hxs => by
      rw [hZ s x hx hxs, hB0 x hx]
      exact hT.transport_zero x hx
    remainder_smooth := hR
    remainder_pos_smooth := hRp
    remainder_zero := hR0
    box_eq := hbox
    cutoff_smooth := hT.cutoff_smooth
    cutoff_hasCompactSupport := hT.cutoff_hasCompactSupport
    tsupport_cutoff_subset := hT.tsupport_cutoff_subset
    temporal := hT.temporal
    cutoff_eq_one := fun x hx hϱ r hr => hT.cutoff_eq_one x hx hϱ (hBb x hx r hr)
    isOpen_V := hT.isOpen_V
    cutoff_eq_one_of_mem := hT.cutoff_eq_one_of_mem
    lt_of_mem := hT.lt_of_mem
    disjoint := hT.disjoint
    pos := fun x hx => by
      rw [hB0 x (hT.tsupport_cutoff_subset (subset_tsupport _ (show x ∈ support χ by
        simp [hT.cutoff_eq_one_of_mem x hx])))]
      exact hT.pos x hx }⟩

/-- **One-sided retarded waves** (`lem_onesided`): from the conclusions of the emission lemma,
for `t ∈ (t₁, 1)` and an open neighbourhood `N` of `σ(t)`, there are a cut-off `θ ≥ 0` near
`σ(t)` with `θ(σ(t)) > 0`, an open neighbourhood `V ⊆ T` of `σ(1)` and sources
`F_s` supported in `supp θ ∩ {φ = s} ⊆ J⁺(μ(s))` with `G^ret F_s = u_s H(φ - s)` on `V`, where
`u_s > 0` on `{φ = s}` and `u` satisfies the conormal properties of `lem_conormal`(b). -/
theorem IsEmission.exists_isOneSidedWave (hg : IsSpacetime g Y) {σ : ℝ → E n} {b t₁ t₂ η : ℝ}
    {T : Set (E n)} {φ : E n → ℝ} {μ : ℝ → E n} (hE : IsEmission g Y σ b t₁ t₂ η T φ μ)
    {t : ℝ} (ht : t ∈ Ioo t₁ 1) {N : Set (E n)} (hN : IsOpen N) (htN : σ t ∈ N) :
    ∃ (θ : E n → ℝ) (V : Set (E n)) (u a b : ℝ → E n → ℝ) (F : ℝ → (E n → ℝ) → ℝ),
      0 < θ (σ t) ∧ IsOneSidedWave g Y φ T N μ η (σ 1) θ V u a b F := by
  obtain ⟨θ, Bx, bk, χ, ϱ, ϱout, V, hθ, hθc, hθN, hθ0, hθt, h1V, hT⟩ :=
    hE.exists_isTransport hg ht hN htN
  obtain ⟨B, R, hA⟩ := hT.exists_isAmplitude hg hE.eikonal
  obtain ⟨a, b', hw⟩ := hA.isOneSidedWave hg hE.eikonal hE.causalFuture_inter hE.mem_Ioo hθ hθc
    hθN hθ0 h1V
  exact ⟨θ, V, _, a, b', _, hθt, hw⟩

end

end LorentzianCalderon
