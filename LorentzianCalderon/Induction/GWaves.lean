module

public import LorentzianCalderon.Induction.PropagationA
public import LorentzianCalderon.Induction.GWavesPhase
public import LorentzianCalderon.Induction.GWavesAmplitude
public import LorentzianCalderon.ODE.Dependence
public import LorentzianCalderon.Local.Energy.Coform

public section

/-!
# The `g`-waves near a frontier point

Blueprint, Lemma `lem_g_waves`: under `P(τ)`, at a frontier point `q₀ ∈ Σ_τ ∩ W` with limit
`p₀ = σ(1)` of `Ψ` (`ExtensionProperty.frontier`), the retarded solutions `G^ret_g F_s` of the
sources of a one-sided wave for `g'` near `p₀` are one-sided waves for `g` near `q₀`, with the
conormal properties used by the local continuation step (`ExtensionProperty.g_waves`).

The transfer of causal relations (`lem_causal_transfer`) is a hypothesis.

* Step 1, the phase: `φ♮ = φ' ∘ Ψ̂` is eikonal of future type on `{ψ ≥ τ}` near `q₀`, and the
  method of characteristics extends it to a neighbourhood of `q₀`
  (`exists_isFutureEikonal_extension`).
* Step 2, one-sidedness: `G^ret_g F_s` vanishes on `{φ < s}` near `q₀`. The integral curve of
  `Z = -grad φ` from a point near `q₀` reaches `A_τ` within the domain of `φ`
  (`IsFutureEikonal.exists_causalLE`), and the transfer of causal relations and
  `J⁺_{g'}(μ(s)) ∩ 𝒯 = {φ' ≥ s}` exclude it from `J⁺_g(supp F_s)`.
* Step 3, above the frontier: `G^ret_g F_s = (u'_s ∘ Ψ) H(φ - s)` on `A_τ` near `q₀`
  (`ExtensionProperty.agreesOn_retardedS_comp`), and the conormal properties of `u'_s ∘ Ψ` there
  (naturality of `□` and of the cometric).
* Step 4, the amplitude across `Σ_τ`: `exists_wave_of_frontier` (`lem_ind_frontier_wave`).
-/

namespace LorentzianCalderon

noncomputable section
open MeasureTheory Set Filter Function
open scoped ContDiff Matrix Topology

variable {n : ℕ}

/-! ### Auxiliary facts -/

section Aux

variable {g : MatrixField n} {Y : E n → E n} {ψ : E n → ℝ}

theorem locallyIntegrableOn_indicator_le {V : Set (E n)} (hV : IsOpen V) {φ u : E n → ℝ}
    (hφ : ContinuousOn φ V) (hu : ContinuousOn u V) (s : ℝ) :
    LocallyIntegrableOn ({x | s ≤ φ x}.indicator u) V := by
  rw [locallyIntegrableOn_iff hV.isLocallyClosed]
  intro k hkV hk
  have hm : MeasurableSet (V \ (V ∩ φ ⁻¹' Iio s)) :=
    hV.measurableSet.diff (hφ.isOpen_inter_preimage hV isOpen_Iio).measurableSet
  refine ((hu.mono hkV).integrableOn_compact hk).indicator hm |>.congr_fun
    (fun x hx => ?_) hk.measurableSet
  have hxV := hkV hx
  by_cases hxs : s ≤ φ x
  · rw [indicator_of_mem (show x ∈ V \ (V ∩ φ ⁻¹' Iio s) from ⟨hxV, fun h => not_lt.2 hxs h.2⟩),
      indicator_of_mem (show x ∈ {x | s ≤ φ x} from hxs)]
  · rw [indicator_of_notMem (show x ∉ V \ (V ∩ φ ⁻¹' Iio s) from
        fun h => h.2 ⟨hxV, not_le.1 hxs⟩),
      indicator_of_notMem (show x ∉ {x | s ≤ φ x} from hxs)]

theorem IsFutureEikonal.mono {φ : E n → ℝ} {U U' : Set (E n)} (h : IsFutureEikonal g Y φ U)
    (hU' : IsOpen U') (hUU' : U' ⊆ U) : IsFutureEikonal g Y φ U' :=
  ⟨hU', h.smooth.mono hUU', fun x hx => h.eikonal x (hUU' hx),
    fun x hx => h.d_ne_zero x (hUU' hx), fun x hx => h.future x (hUU' hx)⟩

lemma hasDerivWithinAt_singleton {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (f' : F) (t : ℝ) : HasDerivWithinAt f f' {t} t :=
  HasFDerivWithinAt.of_not_accPt (by rw [accPt_iff_clusterPt, inf_principal]; simp [ClusterPt])

/-- The set of `(t, t₀, x₀, p)` for which the solution of `ẋ = Z(x)` in `U` with `x(t₀) = x₀`
reaches the time `t`. -/
def fieldDomain (Z : E n → E n) (U : Set (E n)) : Set (ℝ × ℝ × E n × ℝ) :=
  { q | q.2.2.2 ∈ (univ : Set ℝ) ∧ ∃ (x : ℝ → E n) (I : Set ℝ),
    Facts.IsODESolution (fun _ y _ => Z y) U q.2.2.2 x I ∧ q.1 ∈ I ∧ q.2.1 ∈ I ∧
      x q.2.1 = q.2.2.1 }

/-- **Null generators reach `A_τ`**: the integral curves of `Z = -grad φ` of an eikonal function
of future type are future-directed causal curves along which `φ` is constant and `ψ` increases;
from every point near `q₀` one of them reaches `{ψ > ψ(q₀)}` within the domain of `φ`. -/
theorem IsFutureEikonal.exists_causalLE (hg : IsSpacetime g Y) (hψ : IsCauchyTemporal g Y ψ)
    {U : Set (E n)} {φ : E n → ℝ} (hφ : IsFutureEikonal g Y φ U) {q₀ : E n} (hq₀ : q₀ ∈ U) :
    ∃ U₀, IsOpen U₀ ∧ q₀ ∈ U₀ ∧
      ∀ x ∈ U₀, ∃ x' ∈ U, ψ q₀ < ψ x' ∧ φ x' = φ x ∧ CausalLE g Y x x' := by
  set Z : E n → E n := fun x => -grad g φ x with hZdef
  have hZ : ContDiffOn ℝ ∞ Z U :=
    (contDiffOn_grad hg.smooth hg.det_ne_zero hφ.isOpen hφ.smooth).neg
  obtain ⟨X, hD, hX, hrep'⟩ := Facts.ode_smooth_dependence (P := ℝ) hφ.isOpen hZ
  have hdom : fieldDomain Z U = { q : ℝ × ℝ × E n × ℝ | ∃ (x : ℝ → E n) (I : Set ℝ),
      Facts.IsODESolution (fun _ y _ => Z y) U q.2.2.2 x I ∧ q.1 ∈ I ∧ q.2.1 ∈ I ∧
        x q.2.1 = q.2.2.1 } := by
    ext q
    simp [fieldDomain]
  rw [← hdom] at hD hX
  have hrep : ∀ (p : ℝ) (x : ℝ → E n) (I : Set ℝ), p ∈ (univ : Set ℝ) →
      Facts.IsODESolution (fun _ y _ => Z y) U p x I → ∀ t₀ ∈ I, ∀ t ∈ I,
        X (t, t₀, x t₀, p) = x t := fun p x I _ => hrep' p x I
  have h0 : ((0 : ℝ), (0 : ℝ), q₀, (0 : ℝ)) ∈ fieldDomain Z U :=
    ⟨mem_univ _, fun _ => q₀, {0}, ⟨ordConnected_singleton, fun _ _ => hq₀,
      fun t ht => by rw [mem_singleton_iff.1 ht]; exact hasDerivWithinAt_singleton _ _ _⟩,
      rfl, rfl, rfl⟩
  -- the solution from `x` reaching `t₁ > 0`, as a causal curve
  have hcurve : ∀ t₁ : ℝ, 0 < t₁ → ∀ x, (t₁, 0, x, 0) ∈ fieldDomain Z U →
      X (t₁, 0, x, 0) ∈ U ∧ ψ x < ψ (X (t₁, 0, x, 0)) ∧ φ (X (t₁, 0, x, 0)) = φ x ∧
        CausalLE g Y x (X (t₁, 0, x, 0)) := by
    rintro t₁ ht₁ x ⟨-, y, I, hy, ht₁I, h0I, hy0⟩
    simp only at hy0
    have hsub : Icc 0 t₁ ⊆ I := hy.interval.out h0I ht₁I
    have hXy : ∀ t ∈ I, X (t, 0, x, 0) = y t := fun t ht => by
      simpa [hy0] using hrep 0 y I (mem_univ _) hy 0 h0I t ht
    have hyU : ∀ t ∈ Icc 0 t₁, y t ∈ U := fun t ht => hy.mem t (hsub ht)
    have hdy : ∀ t ∈ Icc 0 t₁, HasDerivWithinAt y (Z (y t)) (Icc 0 t₁) t := fun t ht =>
      (hy.deriv t (hsub ht)).mono hsub
    have hsm : ContDiffOn ℝ ∞ y (Icc 0 t₁) := by
      refine (hX.comp (contDiff_id.prodMk contDiff_const).contDiffOn fun t ht =>
        ⟨mem_univ _, y, I, hy, hsub ht, h0I, hy0⟩).congr fun t ht => ?_
      simp [hXy t (hsub ht)]
    have hderiv : ∀ t ∈ Icc 0 t₁, derivWithin y (Icc 0 t₁) t = Z (y t) := fun t ht =>
      (hdy t ht).derivWithin (uniqueDiffOn_Icc ht₁ t ht)
    have hpiece : IsPathPiece (IsFutureCausal g Y) 0 t₁ y :=
      isPathPiece_iff.2 ⟨hsm, fun t ht => by rw [hderiv t ht]; exact hφ.future _ (hyU t ht)⟩
    have hpath : IsPathOn (IsFutureCausal g Y) 0 t₁ y :=
      isPathOn_iff.2 ⟨ht₁, ∅, fun a b ha hab hb _ => hpiece.mono_interval ha hab hb⟩
    have hφc : ∀ t ∈ Icc 0 t₁, φ (y t) = φ (y 0) := by
      refine constant_of_derivWithin_zero (f := fun t => φ (y t)) ?_ fun t ht => ?_
      · exact (hφ.smooth.differentiableOn (by simp)).comp (hsm.differentiableOn (by simp))
          fun t ht => hyU t ht
      · have hφd : HasFDerivAt φ (fderiv ℝ φ (y t)) (y t) :=
          ((hφ.smooth.differentiableOn (by simp)).differentiableAt
            (hφ.isOpen.mem_nhds (hyU t (Ico_subset_Icc_self ht)))).hasFDerivAt
        rw [show (fun t => φ (y t)) = φ ∘ y from rfl,
          (hφd.comp_hasDerivWithinAt t (hdy t (Ico_subset_Icc_self ht))).derivWithin
          (uniqueDiffOn_Icc ht₁ t (Ico_subset_Icc_self ht))]
        have := form_neg_grad (hg.lorentzian (y t)) φ φ
        rw [form_neg_left, hφ.eikonal _ (hyU t (Ico_subset_Icc_self ht))] at this
        show fderiv ℝ φ (y t) (Z (y t)) = 0
        rw [fderiv_eq_form_grad (hg.lorentzian _)]
        linarith
    rw [hXy t₁ ht₁I]
    refine ⟨hyU t₁ ⟨ht₁.le, le_rfl⟩, ?_, ?_, ?_⟩
    · have := hψ.lt_of_isPathOn hg hpath
      rwa [← hy0]
    · rw [hφc t₁ ⟨ht₁.le, le_rfl⟩, hy0]
    · have := causalLE_of_isPathOn hpath
      rwa [hy0] at this
  obtain ⟨t₁, ht₁, ht₁D⟩ : ∃ t₁ : ℝ, 0 < t₁ ∧ (t₁, (0 : ℝ), q₀, (0 : ℝ)) ∈ fieldDomain Z U := by
    have hc : Continuous fun t : ℝ => (t, (0 : ℝ), q₀, (0 : ℝ)) := by fun_prop
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hD.preimage hc) 0 h0
    refine ⟨ε / 2, by positivity, hball ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hc : Continuous fun x : E n => (t₁, (0 : ℝ), x, (0 : ℝ)) := by fun_prop
  have hU₁ : IsOpen ((fun x : E n => (t₁, (0 : ℝ), x, (0 : ℝ))) ⁻¹' fieldDomain Z U) :=
    hD.preimage hc
  have hψX : ContinuousOn (fun x => ψ (X (t₁, 0, x, 0)))
      ((fun x : E n => (t₁, (0 : ℝ), x, (0 : ℝ))) ⁻¹' fieldDomain Z U) :=
    hψ.smooth.continuous.comp_continuousOn (hX.continuousOn.comp hc.continuousOn fun x hx => hx)
  refine ⟨_ ∩ (fun x => ψ (X (t₁, 0, x, 0))) ⁻¹' Ioi (ψ q₀),
    hψX.isOpen_inter_preimage hU₁ isOpen_Ioi, ⟨ht₁D, (hcurve t₁ ht₁ q₀ ht₁D).2.1⟩,
    fun x hx => ?_⟩
  obtain ⟨hxU, -, hxφ, hxc⟩ := hcurve t₁ ht₁ x hx.1
  exact ⟨_, hxU, hx.2, hxφ, hxc⟩

end Aux

/-! ### The future type of the phase at the frontier -/

section Future

variable {g g' : MatrixField n} {Y Y' : E n → E n} {ψ : E n → ℝ} {τ : ℝ} {Ψ : E n → E n}

/-- At `q₀ ∈ Σ_τ`, `-grad (φ' ∘ Ψ̂)` is future-directed if `-grad φ'` is, for a smooth extension
`Ψ̂` of `Ψ` near `q₀` which pulls `g'` back to `g` at `q₀`, when `Ψ` preserves the time
orientation on `A_τ`. -/
theorem form_neg_grad_comp_neg (hg : IsSpacetime g Y) (hg' : IsSpacetime g' Y')
    (hψ : IsCauchyTemporal g Y ψ)
    (hT : ∀ x ∈ A ψ τ, IsFutureTimelike g' Y' (Ψ x) (fderiv ℝ Ψ x (Y x)))
    {B : Set (E n)} (hB : IsOpen B) {Ψh : E n → E n} (hΨh : ContDiffOn ℝ ∞ Ψh B)
    (hagree : ∀ x ∈ B ∩ A ψ τ, Ψh x = Ψ x) {q₀ : E n} (hq₀B : q₀ ∈ B) (hq₀ : ψ q₀ = τ)
    (hpull : g q₀ = (D Ψh q₀)ᵀ * g' (Ψh q₀) * D Ψh q₀) {φ' : E n → ℝ}
    (hφ' : DifferentiableAt ℝ φ' (Ψh q₀))
    (hfut' : IsFutureCausal g' Y' (Ψh q₀) (-grad g' φ' (Ψh q₀))) :
    form (g q₀) (-grad g (φ' ∘ Ψh) q₀) (Y q₀) < 0 := by
  have hYt := hg.globallyHyperbolic.timeOrientation.timelike
  have hY't := hg'.globallyHyperbolic.timeOrientation.timelike
  have hΨd : ∀ x ∈ B, DifferentiableAt ℝ Ψh x := fun x hx =>
    (hΨh.differentiableOn (by simp)).differentiableAt (hB.mem_nhds hx)
  set w := fderiv ℝ Ψh q₀ (Y q₀)
  have hform : ∀ v v', form (g q₀) v v' =
      form (g' (Ψh q₀)) (fderiv ℝ Ψh q₀ v) (fderiv ℝ Ψh q₀ v') := fun v v' => by
    rw [form_pullback hpull, D_mulVec, D_mulVec]
  have hwt : form (g' (Ψh q₀)) w w < 0 := by rw [← hform]; exact hYt q₀
  set f : E n → ℝ := fun x => form (g' (Ψh x)) (fderiv ℝ Ψh x (Y x)) (Y' (Ψh x))
  have hf : ContinuousOn f B :=
    continuousOn_form (fun i j => (hg'.smooth i j).continuous.comp_continuousOn hΨh.continuousOn)
      ((hΨh.continuousOn_fderiv_of_isOpen hB (by simp)).clm_apply
        hg.globallyHyperbolic.timeOrientation.continuous.continuousOn)
      (hg'.globallyHyperbolic.timeOrientation.continuous.comp_continuousOn hΨh.continuousOn)
  have hfA : ∀ x ∈ B ∩ A ψ τ, f x < 0 := fun x hx => by
    have hBA : IsOpen (B ∩ A ψ τ) := hB.inter (isOpen_A hψ.smooth.continuous τ)
    have hev : Ψh =ᶠ[𝓝 x] Ψ := eventually_of_mem (hBA.mem_nhds hx) hagree
    simp only [f, hev.fderiv_eq, hagree x hx]
    exact (hT x hx.2).future
  have hcl : q₀ ∈ closure (B ∩ A ψ τ) := by
    have hdψ : fderiv ℝ ψ q₀ ≠ 0 := fun h' =>
      fderiv_apply_unitNormal_ne_zero hg hψ q₀ (by rw [h']; rfl)
    exact hB.inter_closure ⟨hq₀B, mem_closure_A (hψ.smooth.of_le (by simp)) hdψ hq₀⟩
  have hfq₀ : f q₀ ≤ 0 :=
    ContinuousWithinAt.closure_le hcl ((hf q₀ hq₀B).mono inter_subset_left)
      continuousWithinAt_const fun x hx => (hfA x hx).le
  have hw0 : w ≠ 0 := fun h => by rw [h, form_zero_left] at hwt; exact lt_irrefl 0 hwt
  have hwf : IsFutureTimelike g' Y' (Ψh q₀) w :=
    ⟨hwt, lt_of_le_of_ne hfq₀ ((hg'.lorentzian _).form_ne_zero hwt.le hw0 (hY't _))⟩
  have hneg := hwf.form_neg (hg'.lorentzian _) (hY't _) hfut'
  rw [form_comm (hg'.lorentzian _).symm, form_neg_left,
    ← fderiv_eq_form_grad (hg'.lorentzian _)] at hneg
  rw [form_neg_left, ← fderiv_eq_form_grad (hg.lorentzian _),
    fderiv_comp q₀ hφ' (hΨd q₀ hq₀B)]
  simpa using hneg

end Future

/-! ### The statement -/

variable (g Y ψ τ Ψ) in
/-- The conclusions of `lem_g_waves` and the conormal properties of `lem_conormal`(b) near the
frontier point `q₀`, for the one-sided wave `(φ', V', u', θ, F)` of `g'`: on the open
neighbourhood `V` of `q₀`, `φ` is eikonal of future type with `φ(q₀) = 0` and `φ = φ' ∘ Ψ` on
`V ∩ A_τ`, `Ψ(V ∩ A_τ) ⊆ V'`; for `|s| < η₂`, `G^ret_g F_s = u_s H(φ - s)` on `V`, which is
disjoint from `supp θ`, `u_s = u'_s ∘ Ψ` on `V ∩ A_τ ∩ {φ ≥ s}`, `u_s > 0` on `{φ = s}`,
`□ u_s = (φ - s) a_s` with `a_s = 0` on `{φ > s}`, and `2 Z u_s + u_s □φ = (φ - s) b_s`. -/
structure IsFrontierWave (φ' : E n → ℝ) (V' : Set (E n)) (u' : ℝ → E n → ℝ)
    (θ : E n → ℝ) (F : ℝ → (E n → ℝ) → ℝ) (q₀ : E n) (V : Set (E n)) (η₂ : ℝ)
    (φ : E n → ℝ) (u a b : ℝ → E n → ℝ) : Prop where
  isOpen : IsOpen V
  mem : q₀ ∈ V
  eikonal : IsFutureEikonal g Y φ V
  image_subset : Ψ '' (V ∩ A ψ τ) ⊆ V'
  eq_comp : ∀ x ∈ V ∩ A ψ τ, φ x = φ' (Ψ x)
  phase_zero : φ q₀ = 0
  smooth : ContDiffOn ℝ ∞ (fun p : ℝ × E n => u p.1 p.2) (Ioo (-η₂) η₂ ×ˢ V)
  retarded : ∀ s ∈ Ioo (-η₂) η₂,
    AgreesOn g (retardedS g Y (F s)) ({x | s ≤ φ x}.indicator (u s)) V
  disjoint : Disjoint V (tsupport θ)
  eq_comp_wave : ∀ s ∈ Ioo (-η₂) η₂, ∀ x ∈ V ∩ A ψ τ, s ≤ φ x → u s x = u' s (Ψ x)
  pos : ∀ s ∈ Ioo (-η₂) η₂, ∀ x ∈ V, φ x = s → 0 < u s x
  a_smooth : ContDiffOn ℝ ∞ (fun p : ℝ × E n => a p.1 p.2) (Ioo (-η₂) η₂ ×ˢ V)
  b_smooth : ContDiffOn ℝ ∞ (fun p : ℝ × E n => b p.1 p.2) (Ioo (-η₂) η₂ ×ˢ V)
  box_eq : ∀ s ∈ Ioo (-η₂) η₂, ∀ x ∈ V, box g (u s) x = (φ x - s) * a s x
  a_eq_zero : ∀ s ∈ Ioo (-η₂) η₂, ∀ x ∈ V, s < φ x → a s x = 0
  transport : ∀ s ∈ Ioo (-η₂) η₂, ∀ x ∈ V,
    2 * -coform g x (d φ x) (d (u s) x) + u s x * box g φ x = (φ x - s) * b s x

namespace ExtensionProperty

variable {T : ℝ} {g g' : MatrixField n} {Y Y' : E n → E n} {ψ : E n → ℝ} {τ : ℝ}
  {Ψ : E n → E n} {Φ : ℝ → E n → E n}

/-- **No escape** (`lem_no_escape`) in the setting of the induction: `Ψ` preserves the time
orientation on `A_τ`. -/
theorem isFutureTimelike_fderiv_of_admissible (hP : ExtensionProperty g g' ψ (W n T) τ Ψ)
    (hgA : IsAdmissibleMetric n T g) (hg'A : IsAdmissibleMetric n T g')
    (hg : IsSpacetime g Y) (hg' : IsSpacetime g' Y')
    (hY : ∀ x ∉ M0 n T, form (g x) (EuclideanSpace.single 0 1) (Y x) < 0)
    (hY' : ∀ x ∉ M0 n T, form (g' x) (EuclideanSpace.single 0 1) (Y' x) < 0)
    (hψ : IsCauchyTemporal g Y ψ) (hΦ : Continuous fun p : ℝ × E n => Φ p.1 p.2)
    (hΦ0 : ∀ x, Φ 0 x = x) (hΦψ : ∀ t x, ψ (Φ t x) = ψ x + t) {x : E n} (hx : x ∈ A ψ τ)
    {v : E n} (hv : IsFutureTimelike g Y x v) :
    IsFutureTimelike g' Y' (Ψ x) (fderiv ℝ Ψ x v) := by
  have hψc := hψ.smooth.continuous
  refine hP.isFutureTimelike_fderiv hg hg' hψc isClosed_W
    (isConnected_A hψc hΦ hΦ0 hΦψ τ).isPreconnected (nonempty_A_diff hψc hΦψ isCompact_W τ)
    (fun y hy w hw => ?_) hx hv
  have hyM : y ∉ M0 n T := fun h => hy (M0_subset_W h)
  exact (isFutureTimelike_iff_of_minkowski (hg'A.minkowski_exterior y hyM)
    (hg'.globallyHyperbolic.timeOrientation.timelike y) (hY' y hyM)).2
    ((isFutureTimelike_iff_of_minkowski (hgA.minkowski_exterior y hyM)
      (hg.globallyHyperbolic.timeOrientation.timelike y) (hY y hyM)).1 hw)

/-- **Structure of the `g`-waves near a frontier point** (blueprint, Lemma `lem_g_waves`), under
`P(τ)` and the transfer of causal relations `hct` (`lem_causal_transfer`). Let `q₀ ∈ Σ_τ ∩ W`
and `p₀` the limit of `Ψ` at `q₀` (`ExtensionProperty.frontier`), `p₀ = σ(1)` for the emission
data of `g'` (`IsEmission`), and `(θ, V', u', F)` a one-sided wave of `g'` near `p₀` with
sources in `O` (`IsEmission.exists_isOneSidedWave`). Then the retarded solutions
`G^ret_g F_s` are one-sided waves near `q₀` (`IsFrontierWave`) for `|s| < η₂ ≤ η`. -/
theorem g_waves (hP : ExtensionProperty g g' ψ (W n T) τ Ψ)
    (hgA : IsAdmissibleMetric n T g) (hg'A : IsAdmissibleMetric n T g')
    (hg : IsSpacetime g Y) (hg' : IsSpacetime g' Y')
    (hY : ∀ x ∉ M0 n T, form (g x) (EuclideanSpace.single 0 1) (Y x) < 0)
    (hY' : ∀ x ∉ M0 n T, form (g' x) (EuclideanSpace.single 0 1) (Y' x) < 0)
    (hC : CauchyDataSubset n T g g') (hψ : IsCauchyTemporal g Y ψ)
    (hΦ : Continuous fun p : ℝ × E n => Φ p.1 p.2) (hΦ0 : ∀ x, Φ 0 x = x)
    (hΦψ : ∀ t x, ψ (Φ t x) = ψ x + t)
    (hct : ∀ x ∈ A ψ τ, ∀ y ∈ O n T, CausalLE g Y y x → CausalLE g' Y' y (Ψ x))
    {m : ℕ} {v' : Fin m → E n → ℝ} (hv' : ∀ i, ContDiff ℝ ∞ (v' i))
    (hbox' : ∀ i x, box g' (v' i) x = 0)
    (himm : ∀ x ∈ W n T, Injective (fderiv ℝ (fun y i => v' i y) x)) {q₀ p₀ : E n}
    (hq₀ : ψ q₀ = τ) (hq₀W : q₀ ∈ W n T) (hp₀W : p₀ ∈ W n T)
    (hlim : Tendsto Ψ (𝓝[A ψ τ] q₀) (𝓝 p₀)) (hp₀V : ∀ i, v' i p₀ = transfer n T g (v' i) q₀)
    {σ : ℝ → E n} {b₀ t₁ t₂ η : ℝ} {𝒯 : Set (E n)} {φ' : E n → ℝ} {μ : ℝ → E n}
    (hE : IsEmission g' Y' σ b₀ t₁ t₂ η 𝒯 φ' μ) (hσ : σ 1 = p₀) {θ : E n → ℝ}
    {V' : Set (E n)} {u' a' b' : ℝ → E n → ℝ} {F : ℝ → (E n → ℝ) → ℝ}
    (hw : IsOneSidedWave g' Y' φ' 𝒯 (O n T) μ η p₀ θ V' u' a' b' F) :
    ∃ (V : Set (E n)) (η₂ : ℝ) (φ : E n → ℝ) (u a b : ℝ → E n → ℝ), 0 < η₂ ∧ η₂ ≤ η ∧
      IsFrontierWave g Y ψ τ Ψ φ' V' u' θ F q₀ V η₂ φ u a b := by
  obtain ⟨B, hBo, hq₀B, Ψh, hΨh, hΨhq₀, hagreeΨ, hpull, -⟩ :=
    hP.frontier_extension hgA hg'A hg hg' hY hY' hC hψ hv' hbox' himm hq₀ hp₀W hlim hp₀V
  have hφ' := hE.eikonal
  have hη := hE.η_pos
  have hV'T := hw.subset
  set B₁ := (B ∩ Ψh ⁻¹' V') ∩ (tsupport θ)ᶜ with hB₁def
  have hB₁o : IsOpen B₁ :=
    (hΨh.continuousOn.isOpen_inter_preimage hBo hw.isOpen).inter
      (isClosed_tsupport θ).isOpen_compl
  have hq₀B₁ : q₀ ∈ B₁ := ⟨⟨hq₀B, by rw [mem_preimage, hΨhq₀]; exact hw.mem⟩,
    fun h => mem_O.1 (hw.tsupport_theta_subset h).1 hq₀W⟩
  have hB₁B : B₁ ⊆ B := fun x hx => hx.1.1
  have hB₁V' : ∀ x ∈ B₁, Ψh x ∈ V' := fun x hx => hx.1.2
  have hΨB₁ : ∀ x ∈ B₁ ∩ A ψ τ, Ψ x = Ψh x := fun x hx => (hagreeΨ x ⟨hB₁B hx.1, hx.2⟩).symm
  have hΨhd : ∀ x ∈ B, DifferentiableAt ℝ Ψh x := fun x hx =>
    (hΨh.differentiableOn (by simp)).differentiableAt (hBo.mem_nhds hx)
  have hΨhc : ∀ x ∈ B, ContDiffAt ℝ ∞ Ψh x := fun x hx => hΨh.contDiffAt (hBo.mem_nhds hx)
  have hφ'c : ∀ y ∈ V', ContDiffAt ℝ ∞ φ' y := fun y hy =>
    hφ'.smooth.contDiffAt (hφ'.isOpen.mem_nhds (hV'T hy))
  have hu's : ∀ s ∈ Ioo (-η) η, ContDiffOn ℝ ∞ (u' s) V' := fun s hs =>
    hw.smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn fun x hx => ⟨hs, hx⟩
  have hu'c : ∀ s ∈ Ioo (-η) η, ∀ y ∈ V', ContDiffAt ℝ ∞ (u' s) y := fun s hs y hy =>
    (hu's s hs).contDiffAt (hw.isOpen.mem_nhds hy)
  /- Step 1: the phase. -/
  have hφn : ContDiffOn ℝ ∞ (φ' ∘ Ψh) B₁ :=
    hφ'.smooth.comp (hΨh.mono hB₁B) fun x hx => hV'T (hB₁V' x hx)
  have heik : ∀ x ∈ B₁, τ ≤ ψ x → coform g x (d (φ' ∘ Ψh) x) (d (φ' ∘ Ψh) x) = 0 := by
    intro x hx hxτ
    have hp := hpull x (hB₁B hx) hxτ
    have := cometric_comp_of_pullback (hΨhd x (hB₁B hx))
      (det_ne_zero_of_pullback hp (hg.det_ne_zero x)) hp
      ((hφ'c _ (hB₁V' x hx)).differentiableAt (by simp))
      ((hφ'c _ (hB₁V' x hx)).differentiableAt (by simp))
    simp only [coform_def] at this ⊢
    rw [this]
    simpa [coform_def] using hφ'.eikonal _ (hV'T (hB₁V' x hx))
  have hfut : IsFutureCausal g Y q₀ (-grad g (φ' ∘ Ψh) q₀) := by
    have hp₀V' : Ψh q₀ ∈ V' := hB₁V' q₀ hq₀B₁
    have hlt := form_neg_grad_comp_neg hg hg' hψ
      (fun x hx => hP.isFutureTimelike_fderiv_of_admissible hgA hg'A hg hg' hY hY' hψ hΦ hΦ0
        hΦψ hx ⟨hg.globallyHyperbolic.timeOrientation.timelike x,
          hg.globallyHyperbolic.timeOrientation.timelike x⟩)
      hBo hΨh hagreeΨ hq₀B hq₀ (hpull q₀ hq₀B hq₀.ge)
      ((hφ'c _ hp₀V').differentiableAt (by simp)) (hφ'.future _ (hV'T hp₀V'))
    refine ⟨fun h => by rw [h, form_zero_left] at hlt; exact lt_irrefl 0 hlt, ?_, hlt⟩
    rw [form_neg_grad (hg.lorentzian q₀), heik q₀ hq₀B₁ hq₀.ge]
  obtain ⟨U, hUB₁, hUo, hq₀U, φ, hφ, hφeq⟩ :=
    exists_isFutureEikonal_extension hg hψ hq₀ hB₁o hq₀B₁ hφn heik hfut
  /- Step 4: one-sidedness. -/
  obtain ⟨U₀, hU₀o, hq₀U₀, hflow⟩ := hφ.exists_causalLE hg hψ hq₀U
  set U₂ := U ∩ U₀
  have hU₂o : IsOpen U₂ := hUo.inter hU₀o
  have hq₀U₂ : q₀ ∈ U₂ := ⟨hq₀U, hq₀U₀⟩
  have hU₂B₁ : U₂ ⊆ B₁ := fun x hx => hUB₁ hx.1
  have hφ₂ : IsFutureEikonal g Y φ U₂ := hφ.mono hU₂o inter_subset_left
  have hφA : ∀ x ∈ B₁ ∩ A ψ τ, x ∈ U → φ x = φ' (Ψ x) := fun x hx hxU => by
    rw [hφeq x hxU (mem_A.1 hx.2).le, hΨB₁ x hx]
    rfl
  have hK : ∀ s ∈ Ioo (-η) η, IsSource (F s) (tsupport θ ∩ {x | φ' x = s}) := hw.source
  have hKO : ∀ s, tsupport θ ∩ {x | φ' x = s} ⊆ O n T := fun s y hy =>
    (hw.tsupport_theta_subset hy.1).1
  have hvan : ∀ s ∈ Ioo (-η) η, VanishesOn (retardedS g Y (F s)) (U₂ ∩ {x | φ x < s}) := by
    intro s hs
    refine ((hK s hs).vanishesOn_retardedS hg).mono fun x hx hxJ => ?_
    obtain ⟨x', hx'U, hx'ψ, hx'φ, hxx'⟩ := hflow x hx.1.2
    have hx'A : x' ∈ A ψ τ := by rw [mem_A, ← hq₀]; exact hx'ψ
    obtain ⟨y, hy, hyx⟩ := mem_causalFutureSet.1 hxJ
    have hyΨ := hct x' hx'A y (hKO s hy) (CausalLE.trans (mem_causalFuture.1 hyx) hxx')
    have hμ : Ψ x' ∈ causalFuture g' Y' (μ s) ∩ 𝒯 :=
      ⟨mem_causalFuture.2 (CausalLE.trans (mem_causalFuture.1 (hw.source_subset s hs hy)) hyΨ), by
        rw [hΨB₁ x' ⟨hUB₁ hx'U, hx'A⟩]; exact hV'T (hB₁V' x' (hUB₁ hx'U))⟩
    rw [hE.causalFuture_inter s hs] at hμ
    have := hφA x' ⟨hUB₁ hx'U, hx'A⟩ hx'U
    have h1 : s ≤ φ' (Ψ x') := hμ.2
    have h2 : φ x < s := hx.2
    linarith
  /- Step 2: above the frontier. -/
  set un : ℝ → E n → ℝ := fun s x => u' s (Ψh x)
  have hagree : ∀ s ∈ Ioo (-η) η,
      AgreesOn g (retardedS g Y (F s)) ({x | s ≤ φ x}.indicator (un s)) (U₂ ∩ A ψ τ) := by
    intro s hs
    have h := hP.agreesOn_retardedS_comp hgA hg'A hg hg' hY hY' hC hψ hΦ hΦ0 hΦψ (hK s hs)
      (hKO s) hw.isOpen (locallyIntegrableOn_indicator_le hw.isOpen
        (hφ'.smooth.continuousOn.mono hV'T) (hu's s hs).continuousOn s) (hw.retarded s hs)
    refine (h.mono fun x hx => ⟨hx.2, ?_⟩).congr fun x hx => ?_
    · rw [mem_preimage, hΨB₁ x ⟨hU₂B₁ hx.1, hx.2⟩]
      exact hB₁V' x (hU₂B₁ hx.1)
    · have hx₁ : x ∈ B₁ ∩ A ψ τ := ⟨hU₂B₁ hx.1, hx.2⟩
      simp only [indicator_apply, mem_ofPred_eq, un, hφA x hx₁ hx.1.1, hΨB₁ x hx₁]
  /- The conormal properties above the frontier, by naturality. -/
  set an : ℝ → E n → ℝ := fun s x => a' s (Ψh x)
  set bn : ℝ → E n → ℝ := fun s x => b' s (Ψh x)
  have hU₂A : IsOpen (U₂ ∩ A ψ τ) := hU₂o.inter (isOpen_A hψ.smooth.continuous τ)
  have hcomp : ∀ {S : Set (E n)}, S ⊆ B₁ → ∀ {f : ℝ → E n → ℝ},
      ContDiffOn ℝ ∞ (fun p : ℝ × E n => f p.1 p.2) (Ioo (-η) η ×ˢ V') →
      ContDiffOn ℝ ∞ (fun p : ℝ × E n => f p.1 (Ψh p.2)) (Ioo (-η) η ×ˢ S) :=
    fun hS f hf => hf.comp (contDiff_fst.contDiffOn.prodMk
      ((hΨh.mono (hS.trans hB₁B)).comp contDiff_snd.contDiffOn fun p hp => hp.2))
      fun p hp => ⟨hp.1, hB₁V' _ (hS hp.2)⟩
  have hloc : ∀ x ∈ U₂ ∩ A ψ τ, Ψh x ∈ V' ∧ φ x = φ' (Ψh x) ∧
      φ =ᶠ[𝓝 x] φ' ∘ Ψh ∧ (∀ᶠ y in 𝓝 x, g y = (D Ψh y)ᵀ * g' (Ψh y) * D Ψh y) ∧
      (D Ψh x).det ≠ 0 := fun x hx =>
    ⟨hB₁V' x (hU₂B₁ hx.1), hφeq x hx.1.1 (mem_A.1 hx.2).le,
      eventually_of_mem (hU₂A.mem_nhds hx) fun y hy => hφeq y hy.1.1 (mem_A.1 hy.2).le,
      eventually_of_mem (hU₂A.mem_nhds hx) fun y hy => hpull y (hB₁B (hU₂B₁ hy.1))
        (mem_A.1 hy.2).le,
      det_ne_zero_of_pullback (hpull x (hB₁B (hU₂B₁ hx.1)) (mem_A.1 hx.2).le) (hg.det_ne_zero x)⟩
  have hboxc : ∀ x ∈ U₂ ∩ A ψ τ, ∀ {v : E n → ℝ}, ContDiffAt ℝ ∞ v (Ψh x) →
      box g (v ∘ Ψh) x = box g' v (Ψh x) := fun x hx v hv =>
    box_comp_of_pullback ((hΨhc x (hB₁B (hU₂B₁ hx.1))).of_le (by simp)) (hloc x hx).2.2.2.2
      (fun i j => (hg'.smooth i j).differentiable (by simp) _) (hg'.det_ne_zero _)
      (hloc x hx).2.2.2.1 (hv.of_le (by simp))
  have hbox : ∀ s ∈ Ioo (-η) η, ∀ x ∈ U₂ ∩ A ψ τ, box g (un s) x = (φ x - s) * an s x := by
    intro s hs x hx
    obtain ⟨hxV', hφx, -⟩ := hloc x hx
    rw [show un s = u' s ∘ Ψh from rfl, hboxc x hx (hu'c s hs _ hxV'), hw.box_eq s hs _ hxV',
      hφx]
  have ha0 : ∀ s ∈ Ioo (-η) η, ∀ x ∈ U₂ ∩ A ψ τ, s < φ x → an s x = 0 := by
    intro s hs x hx hsx
    obtain ⟨hxV', hφx, -⟩ := hloc x hx
    exact hw.a_eq_zero s hs _ hxV' (hφx ▸ hsx)
  have htr : ∀ s ∈ Ioo (-η) η, ∀ x ∈ U₂ ∩ A ψ τ,
      2 * -coform g x (d φ x) (d (un s) x) + un s x * box g φ x = (φ x - s) * bn s x := by
    intro s hs x hx
    obtain ⟨hxV', hφx, hev, -, hJ⟩ := hloc x hx
    have hc := cometric_comp_of_pullback (hΨhd x (hB₁B (hU₂B₁ hx.1))) hJ
      (hpull x (hB₁B (hU₂B₁ hx.1)) (mem_A.1 hx.2).le) ((hφ'c _ hxV').differentiableAt (by simp))
      ((hu'c s hs _ hxV').differentiableAt (by simp))
    have ht := hw.transport s hs _ hxV'
    rw [box_congr hev, hboxc x hx (hφ'c _ hxV'), d_congr hev, hφx]
    simp only [coform_def] at ht ⊢
    rw [show un s = u' s ∘ Ψh from rfl, hc]
    exact ht
  have hpos : ∀ s ∈ Ioo (-η) η, ∀ x ∈ U₂ ∩ A ψ τ, φ x = s → 0 < un s x := by
    intro s hs x hx hsx
    obtain ⟨hxV', hφx, -⟩ := hloc x hx
    exact hw.pos s hs _ hxV' (hφx ▸ hsx)
  /- Steps 3 and 5: the amplitude. -/
  obtain ⟨V, η₂, w, a₂, b₂, hVo, hq₀V, hVU, hη₂, hη₂η, hws, hwr, hweq, hwpos, ha₂, hb₂, hbox₂,
      ha₂0, htr₂⟩ :=
    exists_wave_of_frontier hg hψ hq₀ hφ₂ hq₀U₂ hη hK
      (fun s _ => Set.disjoint_left.2 fun x hx hxK => (hU₂B₁ hx).2 hxK.1)
      (hcomp (fun x hx => hU₂B₁ hx) hw.smooth) hbox ha0 htr hpos hagree hvan
  have hVB₁ : ∀ x ∈ V, x ∈ B₁ := fun x hx => hU₂B₁ (hVU hx)
  refine ⟨V, η₂, φ, w, a₂, b₂, hη₂, hη₂η, {
    isOpen := hVo
    mem := hq₀V
    eikonal := hφ₂.mono hVo hVU
    image_subset := ?_
    eq_comp := fun x hx => hφA x ⟨hVB₁ x hx.1, hx.2⟩ (hVU hx.1).1
    phase_zero := ?_
    smooth := hws
    retarded := hwr
    disjoint := Set.disjoint_left.2 fun x hx h => (hVB₁ x hx).2 h
    eq_comp_wave := fun s hs x hx hsx => by
      rw [hweq s hs x hx hsx, hΨB₁ x ⟨hVB₁ x hx.1, hx.2⟩]
    pos := hwpos
    a_smooth := ha₂
    b_smooth := hb₂
    box_eq := hbox₂
    a_eq_zero := ha₂0
    transport := htr₂ }⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [hΨB₁ x ⟨hVB₁ x hx.1, hx.2⟩]
    exact hB₁V' x (hVB₁ x hx.1)
  · rw [hφeq q₀ hq₀U hq₀.ge, comp_apply, hΨhq₀, ← hσ]
    exact hE.front 1 ⟨hE.t₁_lt_one.le, hE.one_lt_t₂.le⟩

end ExtensionProperty

end

end LorentzianCalderon
