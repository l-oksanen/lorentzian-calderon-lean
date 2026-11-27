module

public import LorentzianCalderon.ODE.Dependence

public section

/-!
# Flows of ordinary differential equations

Consequences of `Facts.ode_smooth_dependence`: the solution map `X(t, t₀, x₀, p)` on its
domain `flowDom` is a solution in `t`, has the flow property, and is unique.
-/

namespace LorentzianCalderon

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

set_option linter.unusedSectionVars false

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The points `(t, t₀, x₀, p)` such that the solution with `x(t₀) = x₀` reaches the time `t`. -/
def flowDom (F : ℝ → V → P → V) (U : Set V) (W : Set P) : Set (ℝ × ℝ × V × P) :=
  { q | q.2.2.2 ∈ W ∧ ∃ (x : ℝ → V) (I : Set ℝ),
    Facts.IsODESolution F U q.2.2.2 x I ∧ q.1 ∈ I ∧ q.2.1 ∈ I ∧ x q.2.1 = q.2.2.1 }

theorem mem_flowDom {F : ℝ → V → P → V} {U : Set V} {W : Set P} {q} :
    q ∈ flowDom F U W ↔ q.2.2.2 ∈ W ∧ ∃ (x : ℝ → V) (I : Set ℝ),
      Facts.IsODESolution F U q.2.2.2 x I ∧ q.1 ∈ I ∧ q.2.1 ∈ I ∧ x q.2.1 = q.2.2.1 := Iff.rfl

/-- The conclusion of `Facts.ode_smooth_dependence`. -/
structure IsFlow (F : ℝ → V → P → V) (U : Set V) (W : Set P) (X : ℝ × ℝ × V × P → V) :
    Prop where
  isOpen : IsOpen (flowDom F U W)
  smooth : ContDiffOn ℝ ∞ X (flowDom F U W)
  eq : ∀ (p : P) (x : ℝ → V) (I : Set ℝ), p ∈ W → Facts.IsODESolution F U p x I →
    ∀ t₀ ∈ I, ∀ t ∈ I, X (t, t₀, x t₀, p) = x t

/-- The flow of an autonomous smooth field, with a dummy parameter. -/
theorem exists_isFlow [FiniteDimensional ℝ V] {F : V → V} {U : Set V} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) : ∃ X, IsFlow (P := P) (fun _ y _ => F y) U univ X := by
  obtain ⟨X, h1, h2, h3⟩ := Facts.ode_smooth_dependence (P := P) hU hF
  have hD : flowDom (P := P) (fun _ y _ => F y) U univ = { q : ℝ × ℝ × V × P |
      ∃ (x : ℝ → V) (I : Set ℝ), Facts.IsODESolution (fun _ y _ => F y) U q.2.2.2 x I ∧
        q.1 ∈ I ∧ q.2.1 ∈ I ∧ x q.2.1 = q.2.2.1 } := by
    ext q
    simp [flowDom]
  refine ⟨X, ⟨?_, ?_, fun p x I _ hx => h3 p x I hx⟩⟩ <;> rw [hD]
  exacts [h1, h2]

namespace IsFlow

variable {F : ℝ → V → P → V} {U : Set V} {W : Set P} {X : ℝ × ℝ × V × P → V}
  (hX : IsFlow F U W X)
include hX

theorem mem_of_sol {p : P} {x : ℝ → V} {I : Set ℝ} (hp : p ∈ W)
    (hx : Facts.IsODESolution F U p x I) {t t₀ : ℝ} (ht : t ∈ I) (ht₀ : t₀ ∈ I) :
    (t, t₀, x t₀, p) ∈ flowDom F U W ∧ X (t, t₀, x t₀, p) = x t :=
  ⟨⟨hp, x, I, hx, ht, ht₀, rfl⟩, hX.eq p x I hp hx t₀ ht₀ t ht⟩

theorem self {t t₀ : ℝ} {x₀ : V} {p : P} (h : (t, t₀, x₀, p) ∈ flowDom F U W) :
    (t₀, t₀, x₀, p) ∈ flowDom F U W ∧ X (t₀, t₀, x₀, p) = x₀ := by
  obtain ⟨hp, x, I, hx, -, ht₀, hx₀⟩ := h
  have := hX.mem_of_sol hp hx ht₀ ht₀
  simp only at hx₀ this
  rwa [hx₀] at this

theorem mem_U {q : ℝ × ℝ × V × P} (h : q ∈ flowDom F U W) : X q ∈ U := by
  obtain ⟨hp, x, I, hx, ht, ht₀, hx₀⟩ := h
  have := hX.eq _ x I hp hx _ ht₀ _ ht
  rw [hx₀] at this
  rw [show q = (q.1, q.2.1, q.2.2.1, q.2.2.2) from rfl, this]
  exact hx.mem _ ht

omit hX in
/-- The time slices of the domain are intervals. -/
theorem mem_of_uIcc {t₁ t₂ t₀ t : ℝ} {x₀ : V} {p : P}
    (h₁ : (t₁, t₀, x₀, p) ∈ flowDom F U W) (h₂ : (t₂, t₀, x₀, p) ∈ flowDom F U W)
    (ht : t ∈ uIcc t₁ t₂) : (t, t₀, x₀, p) ∈ flowDom F U W := by
  obtain ⟨hp, x₁, I₁, hx₁, ht₁, ht₀₁, hx₁₀⟩ := h₁
  obtain ⟨-, x₂, I₂, hx₂, ht₂, ht₀₂, hx₂₀⟩ := h₂
  rcases uIcc_subset_uIcc_union_uIcc (b := t₀) ht with h | h
  · rw [uIcc_comm] at h
    exact ⟨hp, x₁, I₁, hx₁, hx₁.interval.uIcc_subset ht₀₁ ht₁ h, ht₀₁, hx₁₀⟩
  · exact ⟨hp, x₂, I₂, hx₂, hx₂.interval.uIcc_subset ht₀₂ ht₂ h, ht₀₂, hx₂₀⟩

theorem mem_of_uIcc_self {t₀ t s : ℝ} {x₀ : V} {p : P} (h : (t, t₀, x₀, p) ∈ flowDom F U W)
    (hs : s ∈ uIcc t₀ t) : (s, t₀, x₀, p) ∈ flowDom F U W :=
  IsFlow.mem_of_uIcc (hX.self h).1 h hs

theorem contDiffAt {q : ℝ × ℝ × V × P} (h : q ∈ flowDom F U W) : ContDiffAt ℝ ∞ X q :=
  hX.smooth.contDiffAt (hX.isOpen.mem_nhds h)

omit hX in
theorem continuous_slice (t₀ : ℝ) (x₀ : V) (p : P) :
    Continuous fun s : ℝ => (s, t₀, x₀, p) :=
  continuous_id.prodMk continuous_const

theorem eventually_mem {t t₀ : ℝ} {x₀ : V} {p : P} (h : (t, t₀, x₀, p) ∈ flowDom F U W) :
    ∀ᶠ s in 𝓝 t, (s, t₀, x₀, p) ∈ flowDom F U W :=
  (continuous_slice t₀ x₀ p).continuousAt.preimage_mem_nhds (hX.isOpen.mem_nhds h)

/-- The solution map is a solution in `t`. -/
theorem hasDerivAt {t t₀ : ℝ} {x₀ : V} {p : P} (h : (t, t₀, x₀, p) ∈ flowDom F U W) :
    HasDerivAt (fun s => X (s, t₀, x₀, p)) (F t (X (t, t₀, x₀, p)) p) t := by
  have hd : DifferentiableAt ℝ (fun s => X (s, t₀, x₀, p)) t :=
    ((hX.contDiffAt h).differentiableAt (by simp)).comp t
      (differentiable_id.prodMk (differentiable_const _)).differentiableAt
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hX.eventually_mem h)
  set t' := if t₀ ≤ t then t + ε / 2 else t - ε / 2
  have htt' : t ≠ t' := by
    simp only [t']
    split_ifs <;> linarith
  have ht'm : (t', t₀, x₀, p) ∈ flowDom F U W := hball (by
    simp only [t', Real.dist_eq]
    split_ifs
    · rw [show t + ε / 2 - t = ε / 2 by ring, abs_of_pos (by positivity)]
      linarith
    · rw [show t - ε / 2 - t = -(ε / 2) by ring, abs_neg, abs_of_pos (by positivity)]
      linarith)
  obtain ⟨hp, x, I, hx, ht'I, ht₀I, hx₀⟩ := ht'm
  simp only at hp hx ht'I ht₀I hx₀
  have htuI : uIcc t t' ⊆ I := by
    refine hx.interval.uIcc_subset ?_ ht'I
    refine hx.interval.uIcc_subset ht₀I ht'I ?_
    simp only [t']
    split_ifs with h'
    · exact mem_uIcc.2 (Or.inl ⟨h', by linarith⟩)
    · exact mem_uIcc.2 (Or.inr ⟨by linarith, by linarith⟩)
  have htI : t ∈ I := htuI left_mem_uIcc
  have hXx : ∀ s ∈ I, X (s, t₀, x₀, p) = x s := fun s hs => by
    rw [← hx₀]
    exact hX.eq p x I hp hx t₀ ht₀I s hs
  have h1 : HasDerivWithinAt (fun s => X (s, t₀, x₀, p)) (F t (X (t, t₀, x₀, p)) p) I t := by
    rw [hXx t htI]
    exact (hx.deriv t htI).congr (fun s hs => hXx s hs) (hXx t htI)
  have hu : UniqueDiffWithinAt ℝ I t :=
    ((uniqueDiffOn_Icc (min_lt_max.2 htt')) t left_mem_uIcc).mono htuI
  rw [← hu.eq_deriv _ hd.hasDerivAt.hasDerivWithinAt h1]
  exact hd.hasDerivAt

theorem isSolution {J : Set ℝ} (hJ : J.OrdConnected) {t₀ : ℝ} {x₀ : V} {p : P}
    (h : ∀ s ∈ J, (s, t₀, x₀, p) ∈ flowDom F U W) :
    Facts.IsODESolution F U p (fun s => X (s, t₀, x₀, p)) J where
  interval := hJ
  mem s hs := hX.mem_U (h s hs)
  deriv s hs := (hX.hasDerivAt (h s hs)).hasDerivWithinAt

/-- The flow property. -/
theorem flow {t t₁ t₀ : ℝ} {x₀ : V} {p : P} (h : (t, t₀, x₀, p) ∈ flowDom F U W)
    (h₁ : (t₁, t₀, x₀, p) ∈ flowDom F U W) :
    (t, t₁, X (t₁, t₀, x₀, p), p) ∈ flowDom F U W ∧
      X (t, t₁, X (t₁, t₀, x₀, p), p) = X (t, t₀, x₀, p) :=
  hX.mem_of_sol h.1 (hX.isSolution ordConnected_uIcc fun _ hs => IsFlow.mem_of_uIcc h h₁ hs)
    left_mem_uIcc right_mem_uIcc

/-- A function with derivative `1` along the solutions is the time. -/
theorem time_eq {τ : V → ℝ} {t t₀ : ℝ} {x₀ : V} {p : P}
    (hτ : ∀ y ∈ U, ∀ s, HasFDerivAt τ (fderiv ℝ τ y) y ∧ fderiv ℝ τ y (F s y p) = 1)
    (h : (t, t₀, x₀, p) ∈ flowDom F U W) : τ (X (t, t₀, x₀, p)) = τ x₀ + (t - t₀) := by
  obtain ⟨hs, hX₀⟩ := hX.self h
  set k : ℝ → ℝ := fun s => τ (X (s, t₀, x₀, p)) - s
  have hk : ∀ s ∈ uIcc t₀ t, HasDerivAt k 0 s := fun s hs => by
    have hm := hX.mem_of_uIcc_self h hs
    obtain ⟨h1, h2⟩ := hτ _ (hX.mem_U hm) s
    have := (h1.comp_hasDerivAt s (hX.hasDerivAt hm)).sub (hasDerivAt_id s)
    rw [h2, sub_self] at this
    exact this
  have hcont : ContinuousOn k (uIcc t₀ t) := fun s hs => (hk s hs).continuousAt.continuousWithinAt
  have key : ∀ a b, uIcc a b = uIcc t₀ t → k b = k a := fun a b hab => by
    rcases le_total a b with hle | hle
    · have hI : Icc a b = uIcc t₀ t := by rw [← hab, uIcc_of_le hle]
      refine constant_of_has_deriv_right_zero (hI ▸ hcont)
        (fun s hs => (hk s (hI ▸ Ico_subset_Icc_self hs)).hasDerivWithinAt) b
        (right_mem_Icc.2 hle)
    · have hI : Icc b a = uIcc t₀ t := by rw [← hab, uIcc_of_ge hle]
      exact (constant_of_has_deriv_right_zero (hI ▸ hcont)
        (fun s hs => (hk s (hI ▸ Ico_subset_Icc_self hs)).hasDerivWithinAt) a
        (right_mem_Icc.2 hle)).symm
  have := key t₀ t rfl
  simp only [k, hX₀] at this
  linarith

end IsFlow

/-- A derivative within a nondegenerate interval is the derivative, at a point of
differentiability. -/
lemma hasDerivAt_of_hasDerivWithinAt_uIcc {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : ℝ → W} {f' : W} {c d t : ℝ} (hcd : c ≠ d) (ht : t ∈ uIcc c d)
    (hf : DifferentiableAt ℝ f t) (h : HasDerivWithinAt f f' (uIcc c d) t) : HasDerivAt f f' t := by
  have := hf.hasDerivAt
  rwa [(uniqueDiffOn_Icc (inf_lt_sup.2 hcd) t ht).eq_deriv _ this.hasDerivWithinAt h] at this

/-- The scalar linear equation `β' = -a β + f`, `β(t₀) = 0`, with `a`, `f` continuous on
`[t₀, t₁]`, has a solution there, by the integrating factor
`β(s) = e^{-A(s)} ∫_{t₀}^s e^{A} f`, `A(s) = ∫_{t₀}^s a`. -/
theorem exists_linear_scalar_ode {a f : ℝ → ℝ} {t₀ t₁ : ℝ} (ha : ContinuousOn a (uIcc t₀ t₁))
    (hf : ContinuousOn f (uIcc t₀ t₁)) :
    ∃ β : ℝ → ℝ, β t₀ = 0 ∧ ∀ s ∈ uIcc t₀ t₁, HasDerivAt β (-a s * β s + f s) s := by
  have hle : min t₀ t₁ ≤ max t₀ t₁ := min_le_max
  set p : ℝ → ℝ := fun s => projIcc (min t₀ t₁) (max t₀ t₁) hle s
  have hpm : ∀ s, p s ∈ uIcc t₀ t₁ := fun s => (projIcc _ _ hle s).2
  have hp : Continuous p := continuous_subtype_val.comp continuous_projIcc
  have hps : ∀ s ∈ uIcc t₀ t₁, p s = s := fun s hs => by
    simp only [p, projIcc_of_mem hle hs]
  set a' := a ∘ p
  set f' := f ∘ p
  have ha' : Continuous a' := ha.comp_continuous hp hpm
  have hf' : Continuous f' := hf.comp_continuous hp hpm
  set A : ℝ → ℝ := fun s => ∫ σ in t₀..s, a' σ
  have hA : ∀ s, HasDerivAt A (a' s) s := fun s =>
    intervalIntegral.integral_hasDerivAt_right (ha'.intervalIntegrable _ _)
      ha'.aestronglyMeasurable.stronglyMeasurableAtFilter ha'.continuousAt
  have hAc : Continuous A := continuous_iff_continuousAt.2 fun s => (hA s).continuousAt
  set h : ℝ → ℝ := fun σ => Real.exp (A σ) * f' σ
  have hh : Continuous h := (Real.continuous_exp.comp hAc).mul hf'
  set I : ℝ → ℝ := fun s => ∫ σ in t₀..s, h σ
  have hI : ∀ s, HasDerivAt I (h s) s := fun s =>
    intervalIntegral.integral_hasDerivAt_right (hh.intervalIntegrable _ _)
      hh.aestronglyMeasurable.stronglyMeasurableAtFilter hh.continuousAt
  refine ⟨fun s => Real.exp (-A s) * I s, by simp [I], fun s hs => ?_⟩
  have hd := ((hA s).neg.exp).mul (hI s)
  convert hd using 1
  simp only [h, a', f', Function.comp_apply, hps s hs]
  have : Real.exp (-A s) * Real.exp (A s) = 1 := by rw [← Real.exp_add]; simp
  linear_combination (-f s) * this

end

end LorentzianCalderon
