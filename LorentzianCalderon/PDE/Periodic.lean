module

public import Mathlib

public section

/-!
# The periodic core: shared interface

Second-order hyperbolic systems with scalar principal part on the torus `ℝⁿ / ℤⁿ`, with
parameters. The unknowns are functions
`V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι` of a parameter `l`, a time `t` and a
space point `y`, periodic in `y`. They solve

`∂ₜ²V = a^{ij} ∂ᵢ∂ⱼV + Bₜ ∂ₜV + Bⁱ ∂ᵢV + C V + F`.

The partial derivatives `dt`, `dy i`, `dpar k` map functions of this shape to functions of the
same shape, so they iterate (`dt (dt V)`, `dy i (dy j V)`), which is what the prolongation of
P5 needs. The unknowns live in `EuclideanSpace ℝ ι` for a finite index type `ι`: it has an inner
product (energy estimates), real coordinates (Fourier coefficients), and prolongation only
changes `ι` (to `ι × Option (…)`, say) without reindexing to `Fin r`.

Contents: the coefficients `HypCoeffs` with `HypCoeffs.IsGood`, the operator
`HypCoeffs.apply`, `IsPeriodic`, `IsPeriodicSmooth` (closed under `dt`, `dy`, `dpar` and
`A.apply`), bounds of periodic families (`exists_bound_of_isPeriodic`), the unit cell `cell` and
`cellIntegral`, `trigPoly` (smooth and periodic: `contDiff_isPeriodic_of_mem_trigPoly`), and the
calculus used by P2–P7: `cellIntegral_fderiv_eq_zero` (`∫ ∂ᵢu = 0`),
`cellIntegral_inner_fderiv` (integration by parts), `hasFDerivAt_cellIntegral`,
`hasDerivAt_cellIntegral` and `contDiff_cellIntegral` (differentiation under the integral), and
the Grönwall form `le_exp_mul_of_hasDerivAt_le`.
-/

namespace LorentzianCalderon.PDE

universe u

noncomputable section
open scoped ContDiff RealInnerProductSpace Topology
open Set MeasureTheory Function Real

variable {n p : ℕ} {ι : Type*} [Fintype ι]

/-! ## Periodicity -/

/-- `f` is `ℤⁿ`-periodic: invariant under translation by each unit vector. See
`IsPeriodic.add_int` for invariance under all of `ℤⁿ`. -/
def IsPeriodic {X : Type*} (f : (Fin n → ℝ) → X) : Prop :=
  ∀ (i : Fin n) (y : Fin n → ℝ), f (y + Pi.single i 1) = f y

theorem isPeriodic_iff {X : Type*} {f : (Fin n → ℝ) → X} :
    IsPeriodic f ↔
      ∀ (i : Fin n) (y : Fin n → ℝ), f (y + Pi.single i 1) = f y := Iff.rfl

theorem IsPeriodic.add_single {X : Type*} {f : (Fin n → ℝ) → X} (hf : IsPeriodic f) (i : Fin n)
    (y : Fin n → ℝ) : f (y + Pi.single i 1) = f y :=
  isPeriodic_iff.1 hf i y

/-- The closed unit cell `[0, 1]ⁿ`. -/
def cell (n : ℕ) : Set (Fin n → ℝ) := Icc 0 1

theorem cell_def (n : ℕ) : cell n = Icc 0 1 := by rfl

theorem mem_cell {y : Fin n → ℝ} : y ∈ cell n ↔ 0 ≤ y ∧ y ≤ 1 := Iff.rfl

theorem isCompact_cell : IsCompact (cell n) := isCompact_Icc

theorem measurableSet_cell : MeasurableSet (cell n) := measurableSet_Icc

theorem fract_mem_cell (y : Fin n → ℝ) : (fun i => Int.fract (y i)) ∈ cell n :=
  ⟨fun _ => Int.fract_nonneg _, fun _ => (Int.fract_lt_one _).le⟩

theorem IsPeriodic.add_int {X : Type*} {f : (Fin n → ℝ) → X} (hf : IsPeriodic f)
    (k : Fin n → ℤ) (y : Fin n → ℝ) : f (y + fun i => (k i : ℝ)) = f y := by
  have hk : (fun i => (k i : ℝ)) = ∑ i, (k i : ℝ) • (Pi.single i 1 : Fin n → ℝ) := by
    ext j; simp [Pi.single_apply]
  rw [hk]
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ← ih, add_comm _ (∑ x ∈ s, _), ← add_assoc]
    set z := y + ∑ x ∈ s, (k x : ℝ) • (Pi.single x 1 : Fin n → ℝ)
    have hper : Periodic (fun x : ℝ => f (z + x • (Pi.single a 1 : Fin n → ℝ))) 1 := by
      intro x
      simp only [add_smul, one_smul, ← add_assoc]
      exact hf a _
    simpa using hper.int_mul_eq (k a)

theorem IsPeriodic.apply_fract {X : Type*} {f : (Fin n → ℝ) → X} (hf : IsPeriodic f)
    (y : Fin n → ℝ) : f y = f (fun i => Int.fract (y i)) := by
  conv_lhs => rw [show y = (fun i => Int.fract (y i)) + fun i => ((⌊y i⌋ : ℤ) : ℝ) by
    ext i; exact (Int.fract_add_floor _).symm]
  exact hf.add_int _ _

theorem IsPeriodic.comp {X Z : Type*} {f : (Fin n → ℝ) → X} (hf : IsPeriodic f) (g : X → Z) :
    IsPeriodic (g ∘ f) := fun i y => by simp [hf i y]

/-- A continuous family of periodic functions is bounded on `K × ℝⁿ` for compact `K`. -/
theorem exists_bound_of_isPeriodic {X G : Type*} [TopologicalSpace X] [NormedAddCommGroup G]
    {f : X → (Fin n → ℝ) → G} (hf : Continuous (uncurry f)) (hp : ∀ x, IsPeriodic (f x))
    {K : Set X} (hK : IsCompact K) : ∃ C, ∀ x ∈ K, ∀ y, ‖f x y‖ ≤ C := by
  obtain ⟨C, hC⟩ := (hK.prod isCompact_cell).exists_bound_of_continuousOn hf.continuousOn
  exact ⟨C, fun x hx y => (hp x).apply_fract y ▸ hC (x, _) ⟨hx, fract_mem_cell y⟩⟩

/-! ## Partial derivatives of families -/

/-- Time derivative `∂ₜV`. -/
def dt {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X) : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X :=
  fun l t y => deriv (fun s => V l s y) t

theorem dt_def {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X) :
    dt V =
      fun l t y => deriv (fun s => V l s y) t := by rfl

theorem dt_apply {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X) (l : Fin p → ℝ) (t : ℝ) (y : Fin n → ℝ) :
    dt V l t y = deriv (fun s => V l s y) t := by rfl

/-- Space derivative `∂ᵢV = ∂V/∂yᵢ`, along the coordinate vector `Pi.single i 1`. -/
def dy {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (i : Fin n)
    (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X) : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X :=
  fun l t y => fderiv ℝ (V l t) y (Pi.single i 1)

theorem dy_def {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (i : Fin n)
    (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X) :
    dy i V =
      fun l t y => fderiv ℝ (V l t) y (Pi.single i 1) := by rfl

theorem dy_apply {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X) (i : Fin n) (l : Fin p → ℝ) (t : ℝ) (y : Fin n → ℝ) :
    dy i V l t y = fderiv ℝ (V l t) y (Pi.single i 1) := by rfl

/-- Parameter derivative `∂V/∂lₖ`, along the coordinate vector `Pi.single k 1`. -/
def dpar {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (k : Fin p)
    (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X) : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X :=
  fun l t y => fderiv ℝ (fun m => V m t y) l (Pi.single k 1)

theorem dpar_def {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (k : Fin p)
    (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X) :
    dpar k V =
      fun l t y => fderiv ℝ (fun m => V m t y) l (Pi.single k 1) := by rfl

theorem dpar_apply {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X) (k : Fin p) (l : Fin p → ℝ) (t : ℝ) (y : Fin n → ℝ) :
    dpar k V l t y = fderiv ℝ (fun m => V m t y) l (Pi.single k 1) := by rfl

/-- `V` is smooth in `(l, t, y)` jointly and `ℤⁿ`-periodic in `y`.

Caveat: `↿V` uncurries through every function arrow, so the codomain must not be a function
type (such as `Fin r → ℝ`); `ℝ`, `EuclideanSpace ℝ ι` and spaces of continuous linear maps are
fine. -/
structure IsPeriodicSmooth {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X) : Prop where
  smooth : ContDiff ℝ ∞ ↿V
  periodic : ∀ l t, IsPeriodic (V l t)

/-! ## Coefficients and the operator -/

/-- The coefficients of `∂ₜ²V = a^{ij} ∂ᵢ∂ⱼV + Bₜ ∂ₜV + Bⁱ ∂ᵢV + C V`: the scalar principal part
`a i j`, the same for every component of `V`, and the lower order terms `bt` (of `∂ₜV`), `b i` (of
`∂ᵢV`) and `c` (of `V`), as linear maps of `EuclideanSpace ℝ ι`. All are functions of
`(l, t, y)`. -/
structure HypCoeffs (p n : ℕ) (ι : Type*) [Fintype ι] where
  a : Fin n → Fin n → (Fin p → ℝ) → ℝ → (Fin n → ℝ) → ℝ
  bt : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι
  b : Fin n → (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι
  c : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι

namespace HypCoeffs

/-- The hypotheses of the periodic core: all coefficients smooth in `(l, t, y)` and periodic in
`y`; `a` symmetric and positive definite, uniformly for `(l, t)` in a compact set and all `y`. -/
structure IsGood (A : HypCoeffs p n ι) : Prop where
  smooth_a : ∀ i j, ContDiff ℝ ∞ ↿(A.a i j)
  smooth_bt : ContDiff ℝ ∞ ↿A.bt
  smooth_b : ∀ i, ContDiff ℝ ∞ ↿(A.b i)
  smooth_c : ContDiff ℝ ∞ ↿A.c
  periodic_a : ∀ i j l t, IsPeriodic (A.a i j l t)
  periodic_bt : ∀ l t, IsPeriodic (A.bt l t)
  periodic_b : ∀ i l t, IsPeriodic (A.b i l t)
  periodic_c : ∀ l t, IsPeriodic (A.c l t)
  symm : ∀ i j, A.a i j = A.a j i
  pos : ∀ K : Set ((Fin p → ℝ) × ℝ), IsCompact K → ∃ κ > 0, ∀ l t, (l, t) ∈ K →
    ∀ (y ξ : Fin n → ℝ), κ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, A.a i j l t y * ξ i * ξ j

/-- The operator `A V = a^{ij} ∂ᵢ∂ⱼV + Bₜ ∂ₜV + Bⁱ ∂ᵢV + C V`, so that the equation of the
periodic core reads `dt (dt V) = A.apply V + F`. -/
def apply (A : HypCoeffs p n ι) (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι) :
    (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι :=
  fun l t y => ∑ i, ∑ j, A.a i j l t y • dy i (dy j V) l t y + A.bt l t y (dt V l t y) +
    ∑ i, A.b i l t y (dy i V l t y) + A.c l t y (V l t y)

theorem apply_def (A : HypCoeffs p n ι) (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι) :
    apply A V =
      fun l t y => ∑ i, ∑ j, A.a i j l t y • dy i (dy j V) l t y + A.bt l t y (dt V l t y) +
        ∑ i, A.b i l t y (dy i V l t y) + A.c l t y (V l t y) := by rfl

end HypCoeffs

/-! ## The unit cell and trigonometric polynomials -/

/-- Integral over the unit cell `[0, 1]ⁿ`, i.e. over the torus for periodic `f`. -/
def cellIntegral {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : (Fin n → ℝ) → G) : G :=
  ∫ y in cell n, f y

theorem cellIntegral_def {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : (Fin n → ℝ) → G) :
    cellIntegral f =
      ∫ y in cell n, f y := by rfl

/-- The phase `2π k·y` of the Fourier mode `k`. -/
def phase (k : Fin n → ℤ) (y : Fin n → ℝ) : ℝ := 2 * π * ∑ i, (k i : ℝ) * y i

theorem phase_def (k : Fin n → ℤ) (y : Fin n → ℝ) :
    phase k y =
      2 * π * ∑ i, (k i : ℝ) * y i := by rfl

/-- Real trigonometric polynomials of degree at most `N` (in the sup norm of the frequency
`k ∈ ℤⁿ`) with values in `EuclideanSpace ℝ ι`: the span of `y ↦ cos (2π k·y) • v` and
`y ↦ sin (2π k·y) • v` with `|kᵢ| ≤ N`. The Galerkin solutions of P6 take values in it. -/
def trigPoly (ι : Type*) [Fintype ι] (n N : ℕ) :
    Submodule ℝ ((Fin n → ℝ) → EuclideanSpace ℝ ι) :=
  Submodule.span ℝ {f | ∃ k : Fin n → ℤ, (∀ i, |k i| ≤ N) ∧ ∃ v : EuclideanSpace ℝ ι,
    f = (fun y => Real.cos (phase k y) • v) ∨ f = (fun y => Real.sin (phase k y) • v)}

theorem trigPoly_def (ι : Type*) [Fintype ι] (n N : ℕ) :
    trigPoly ι n N =
      Submodule.span ℝ {f | ∃ k : Fin n → ℤ, (∀ i, |k i| ≤ N) ∧ ∃ v : EuclideanSpace ℝ ι,
        f = (fun y => Real.cos (phase k y) • v) ∨ f = (fun y => Real.sin (phase k y) • v)} := by rfl

theorem phase_add_single (k : Fin n → ℤ) (y : Fin n → ℝ) (i : Fin n) :
    phase k (y + Pi.single i 1) = phase k y + (k i : ℤ) * (2 * π) := by
  simp only [phase, Pi.add_apply, mul_add, Finset.sum_add_distrib, Pi.single_apply, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- Trigonometric polynomials are smooth and periodic. -/
theorem contDiff_isPeriodic_of_mem_trigPoly {N : ℕ} {f : (Fin n → ℝ) → EuclideanSpace ℝ ι}
    (hf : f ∈ trigPoly ι n N) : ContDiff ℝ ∞ f ∧ IsPeriodic f := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨k, -, v, rfl | rfl⟩ := hg
    · exact ⟨by simp only [phase]; fun_prop, fun i y => by
        simp only [phase_add_single, Real.cos_add_int_mul_two_pi]⟩
    · exact ⟨by simp only [phase]; fun_prop, fun i y => by
        simp only [phase_add_single, Real.sin_add_int_mul_two_pi]⟩
  | zero => exact ⟨contDiff_const, fun _ _ => rfl⟩
  | add f g _ _ hf hg => exact ⟨hf.1.add hg.1, fun i y => by simp [hf.2 i y, hg.2 i y]⟩
  | smul a f _ hf => exact ⟨hf.1.const_smul a, fun i y => by simp [hf.2 i y]⟩

/-! ## Closure of `IsPeriodicSmooth` under the derivatives and the operator -/

section Closure

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X}

theorem IsPeriodicSmooth.dy (hV : IsPeriodicSmooth V) (i : Fin n) :
    IsPeriodicSmooth (dy i V) where
  smooth := by
    have h : ContDiff ℝ ∞ fun z : (Fin p → ℝ) × ℝ × (Fin n → ℝ) =>
        fderiv ℝ (fun y => V z.1 z.2.1 y) z.2.2 :=
      ContDiff.fderiv
        (f := fun (z : (Fin p → ℝ) × ℝ × (Fin n → ℝ)) (y : Fin n → ℝ) => V z.1 z.2.1 y)
        (hV.smooth.comp (f := fun q : ((Fin p → ℝ) × ℝ × (Fin n → ℝ)) × (Fin n → ℝ) =>
          (q.1.1, q.1.2.1, q.2)) (by fun_prop)) (by fun_prop) le_rfl
    exact h.clm_apply contDiff_const
  periodic l t j y := by
    simp only [PDE.dy]
    rw [← fderiv_comp_add_right]
    congr 2
    ext y'
    exact hV.periodic l t j y'

theorem IsPeriodicSmooth.dt (hV : IsPeriodicSmooth V) : IsPeriodicSmooth (dt V) where
  smooth := by
    have h : ContDiff ℝ ∞ fun z : (Fin p → ℝ) × ℝ × (Fin n → ℝ) =>
        fderiv ℝ (fun s => V z.1 s z.2.2) z.2.1 :=
      ContDiff.fderiv (f := fun (z : (Fin p → ℝ) × ℝ × (Fin n → ℝ)) (s : ℝ) => V z.1 s z.2.2)
        (hV.smooth.comp (f := fun q : ((Fin p → ℝ) × ℝ × (Fin n → ℝ)) × ℝ =>
          (q.1.1, q.2, q.1.2.2)) (by fun_prop)) (by fun_prop) le_rfl
    exact h.clm_apply contDiff_const
  periodic l t j y := by
    simp only [PDE.dt]
    congr 1
    ext s
    exact hV.periodic l s j y

theorem IsPeriodicSmooth.dpar (hV : IsPeriodicSmooth V) (k : Fin p) :
    IsPeriodicSmooth (dpar k V) where
  smooth := by
    have h : ContDiff ℝ ∞ fun z : (Fin p → ℝ) × ℝ × (Fin n → ℝ) =>
        fderiv ℝ (fun m => V m z.2.1 z.2.2) z.1 :=
      ContDiff.fderiv
        (f := fun (z : (Fin p → ℝ) × ℝ × (Fin n → ℝ)) (m : Fin p → ℝ) => V m z.2.1 z.2.2)
        (hV.smooth.comp (f := fun q : ((Fin p → ℝ) × ℝ × (Fin n → ℝ)) × (Fin p → ℝ) =>
          (q.2, q.1.2.1, q.1.2.2)) (by fun_prop)) contDiff_fst le_rfl
    exact h.clm_apply contDiff_const
  periodic l t j y := by
    simp only [PDE.dpar]
    congr 2
    ext m
    exact hV.periodic m t j y

/-- The slices `V l t` of a smooth periodic family are smooth. -/
theorem IsPeriodicSmooth.contDiff_slice (hV : IsPeriodicSmooth V) (l : Fin p → ℝ) (t : ℝ) :
    ContDiff ℝ ∞ (V l t) :=
  hV.smooth.comp (f := fun y : Fin n → ℝ => (l, t, y)) (by fun_prop)

end Closure

theorem HypCoeffs.IsGood.apply {A : HypCoeffs p n ι} (hA : A.IsGood)
    {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι} (hV : IsPeriodicSmooth V) :
    IsPeriodicSmooth (A.apply V) where
  smooth := by
    have h2 i j := ((hV.dy j).dy i).smooth
    have h1 i := (hV.dy i).smooth
    have ht := hV.dt.smooth
    have h0 := hV.smooth
    exact ((ContDiff.sum fun i _ => ContDiff.sum fun j _ => (hA.smooth_a i j).smul (h2 i j)).add
      (hA.smooth_bt.clm_apply ht)).add
      (ContDiff.sum fun i _ => (hA.smooth_b i).clm_apply (h1 i)) |>.add
      (hA.smooth_c.clm_apply h0)
  periodic l t k y := by
    simp only [HypCoeffs.apply, hA.periodic_a _ _ l t k y, hA.periodic_bt l t k y,
      hA.periodic_b _ l t k y, hA.periodic_c l t k y, ((hV.dy _).dy _).periodic l t k y,
      hV.dt.periodic l t k y, (hV.dy _).periodic l t k y, hV.periodic l t k y]

/-! ## Calculus on the unit cell -/

section Cell

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

omit [NormedSpace ℝ G] in
theorem integrableOn_cell {f : (Fin n → ℝ) → G} (hf : Continuous f) :
    IntegrableOn f (cell n) :=
  hf.continuousOn.integrableOn_compact isCompact_cell

private theorem insertNth_eq_add (i : Fin (n + 1)) (x : ℝ) (w : Fin n → ℝ) :
    Fin.insertNth i x w = Fin.insertNth i 0 w + x • (Pi.single i 1 : Fin (n + 1) → ℝ) := by
  ext j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
  · simp
  · simp [Fin.succAbove_ne]

/-- `∫_cell ∂ᵢu = 0` for a periodic `C¹` function `u`. -/
theorem cellIntegral_fderiv_eq_zero [CompleteSpace G] {u : (Fin n → ℝ) → G}
    (hu : ContDiff ℝ 1 u) (hp : IsPeriodic u) (i : Fin n) :
    cellIntegral (fun y => fderiv ℝ u y (Pi.single i 1)) = 0 := by
  cases n with
  | zero => exact i.elim0
  | succ m =>
  set e : Fin (m + 1) → ℝ := Pi.single i 1
  set g : (Fin (m + 1) → ℝ) → G := fun y => fderiv ℝ u y e
  have hg : Continuous g := (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  set μ₁ : Measure ℝ := volume.restrict (Icc 0 1)
  have hμ : volume.restrict (cell (m + 1)) = Measure.pi fun _ => μ₁ := by
    rw [cell, ← pi_univ_Icc, volume_pi, Measure.restrict_pi_pi]
    rfl
  have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ₁) i).symm
  have hint : Integrable g (Measure.pi fun _ => μ₁) := by
    rw [← hμ]; exact integrableOn_cell hg
  rw [cellIntegral, hμ, ← hmp.integral_comp', integral_prod_symm]
  · refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Equiv.coe_fn_mk]
    simp only [μ₁, Pi.zero_apply]
    set c : Fin (m + 1) → ℝ := Fin.insertNth (α := fun _ => ℝ) i 0 w
    have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => u (c + x • e)) (g (c + x • e)) x := fun x =>
      ((hu.differentiable one_ne_zero).differentiableAt.hasFDerivAt).comp_hasDerivAt x
        (by simpa only [one_smul, id] using ((hasDerivAt_id x).smul_const e).const_add c)
    have hgc : Continuous fun x : ℝ => g (c + x • e) := hg.comp (by fun_prop)
    have hfun : ∀ x : ℝ, Fin.insertNth i x w = c + x • e := fun x => insertNth_eq_add i x w
    simp only [hfun]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
        (hgc.intervalIntegrable 0 1)]
    simp [e, hp i c]
  · exact (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hint

/-- Integration by parts on the cell: `∫ ⟪∂ᵢu, v⟫ = -∫ ⟪u, ∂ᵢv⟫` for periodic `C¹` `u`, `v`. -/
theorem cellIntegral_inner_fderiv {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {u v : (Fin n → ℝ) → F} (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) (hpu : IsPeriodic u)
    (hpv : IsPeriodic v) (i : Fin n) :
    cellIntegral (fun y => ⟪fderiv ℝ u y (Pi.single i 1), v y⟫) =
      -cellIntegral (fun y => ⟪u y, fderiv ℝ v y (Pi.single i 1)⟫) := by
  have hdu := hu.differentiable one_ne_zero
  have hdv := hv.differentiable one_ne_zero
  have h := cellIntegral_fderiv_eq_zero (hu.inner ℝ hv)
    (fun j y => by simp only [hpu j y, hpv j y]) i
  simp only [cellIntegral] at h ⊢
  simp_rw [fderiv_inner_apply ℝ (hdu _) (hdv _)] at h
  have hc1 : Continuous fun y => ⟪u y, fderiv ℝ v y (Pi.single i 1)⟫ :=
    hu.continuous.inner ((hv.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have hc2 : Continuous fun y => ⟪fderiv ℝ u y (Pi.single i 1), v y⟫ :=
    ((hu.continuous_fderiv one_ne_zero).clm_apply continuous_const).inner hv.continuous
  rw [integral_add (integrableOn_cell hc1) (integrableOn_cell hc2)] at h
  exact eq_neg_of_add_eq_zero_right h

/-- Differentiation under `∫_cell` in a finite-dimensional parameter `x` (no periodicity
needed: the cell is compact). -/
theorem hasFDerivAt_cellIntegral {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] {f : X → (Fin n → ℝ) → G} (hf : ContDiff ℝ 1 (uncurry f))
    (x₀ : X) :
    HasFDerivAt (fun x => cellIntegral (f x))
      (cellIntegral fun y => fderiv ℝ (fun x => f x y) x₀) x₀ := by
  have hF' : Continuous fun z : X × (Fin n → ℝ) => fderiv ℝ (fun x => f x z.2) z.1 :=
    (ContDiff.fderiv (n := 0) (f := fun (z : X × (Fin n → ℝ)) (x : X) => f x z.2)
      (hf.comp (f := fun q : (X × (Fin n → ℝ)) × X => (q.2, q.1.2)) (by fun_prop))
      contDiff_fst (by simp)).continuous
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x₀ 1).prod isCompact_cell).exists_bound_of_continuousOn
    hF'.continuousOn
  have hdiff : ∀ y, Differentiable ℝ fun x => f x y := fun y =>
    (hf.comp (contDiff_id.prodMk contDiff_const)).differentiable one_ne_zero
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (bound := fun _ => C)
    (F' := fun x y => fderiv ℝ (fun x => f x y) x)
    (Metric.closedBall_mem_nhds x₀ one_pos) ?_ ?_ ?_ ?_
    (integrableOn_const (μ := volume) (s := cell n) (C := C) isCompact_cell.measure_ne_top) ?_
  · exact Filter.Eventually.of_forall fun x => (hf.continuous.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact integrableOn_cell (hf.continuous.comp (continuous_const.prodMk continuous_id))
  · exact (hF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_cell]
    exact Filter.Eventually.of_forall fun y hy x hx => hC (x, y) ⟨hx, hy⟩
  · exact Filter.Eventually.of_forall fun y x _ => (hdiff y x).hasFDerivAt

/-- Differentiation under `∫_cell` in time. -/
theorem hasDerivAt_cellIntegral {f : ℝ → (Fin n → ℝ) → G} (hf : ContDiff ℝ 1 (uncurry f))
    (t₀ : ℝ) :
    HasDerivAt (fun t => cellIntegral (f t))
      (cellIntegral fun y => deriv (fun t => f t y) t₀) t₀ := by
  have h := (hasFDerivAt_cellIntegral hf t₀).hasDerivAt
  have hF' : Continuous fun y => fderiv ℝ (fun t => f t y) t₀ :=
    (ContDiff.fderiv (n := 0) (f := fun (y : Fin n → ℝ) (t : ℝ) => f t y)
      (hf.comp (f := fun q : (Fin n → ℝ) × ℝ => (q.2, q.1)) (by fun_prop))
      contDiff_const (by simp)).continuous
  rwa [cellIntegral, ContinuousLinearMap.integral_apply (integrableOn_cell hF')] at h

omit [NormedAddCommGroup G] [NormedSpace ℝ G] in
/-- `x ↦ ∫_cell f x` is smooth if `f` is jointly smooth. -/
theorem contDiff_cellIntegral {X G : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [NormedAddCommGroup G] [NormedSpace ℝ G] {f : X → (Fin n → ℝ) → G} (hf : ContDiff ℝ ∞ (uncurry f)) :
    ContDiff ℝ ∞ fun x => cellIntegral (f x) := by
  refine contDiff_infty.2 fun k => ?_
  induction k generalizing G with
  | zero =>
    exact contDiff_zero.2 (continuous_parametric_integral_of_continuous hf.continuous
      isCompact_cell)
  | succ k ih =>
    have h1 : ContDiff ℝ 1 (uncurry f) := hf.of_le (by exact_mod_cast le_top)
    refine contDiff_succ_iff_hasFDerivAt.2 ⟨_, ih (f := fun x y => fderiv ℝ (fun x => f x y) x)
      ?_, fun x => hasFDerivAt_cellIntegral h1 x⟩
    exact ContDiff.fderiv (f := fun (z : X × (Fin n → ℝ)) (x : X) => f x z.2)
      (hf.comp (f := fun q : (X × (Fin n → ℝ)) × X => (q.2, q.1.2)) (by fun_prop))
      contDiff_fst le_rfl

end Cell

/-! ## Grönwall -/

/-- Grönwall's inequality with a time-dependent source: if `E' ≤ C E + G` on `[t₀, t₁]` with
`C ≥ 0` and `G ≥ 0` continuous, then `E t ≤ e^{C (t - t₀)} (E t₀ + ∫_{t₀}^t G)`. -/
theorem le_exp_mul_of_hasDerivAt_le {E E' G : ℝ → ℝ} {C t₀ t₁ : ℝ} (hC : 0 ≤ C)
    (hE : ∀ t ∈ Icc t₀ t₁, HasDerivAt E (E' t) t) (hG : Continuous G)
    (hG0 : ∀ t ∈ Icc t₀ t₁, 0 ≤ G t) (hle : ∀ t ∈ Ioo t₀ t₁, E' t ≤ C * E t + G t) :
    ∀ t ∈ Icc t₀ t₁, E t ≤ exp (C * (t - t₀)) * (E t₀ + ∫ s in t₀..t, G s) := by
  set w : ℝ → ℝ := fun s => exp (-(C * (s - t₀)))
  have hw : ∀ s, HasDerivAt w (-C * w s) s := fun s => by
    have := ((((hasDerivAt_id s).sub_const t₀).const_mul C).neg).exp
    simpa [w, mul_comm] using this
  have hwG : Continuous fun s => w s * G s := by fun_prop
  set φ : ℝ → ℝ := fun s => w s * E s - ∫ r in t₀..s, w r * G r
  have hφ : ∀ s ∈ Icc t₀ t₁, HasDerivAt φ (w s * (E' s - C * E s - G s)) s := fun s hs => by
    have := ((hw s).mul (hE s hs)).sub (hwG.integral_hasStrictDerivAt t₀ s).hasDerivAt
    convert this using 1
    ring
  have hanti : AntitoneOn φ (Icc t₀ t₁) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc t₀ t₁)
      (fun s hs => (hφ s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hφ s (interior_subset hs)).differentiableAt.differentiableWithinAt)
      fun s hs => ?_
    rw [interior_Icc] at hs
    rw [(hφ s (Ioo_subset_Icc_self hs)).deriv]
    exact mul_nonpos_of_nonneg_of_nonpos (exp_pos _).le (by linarith [hle s hs])
  intro t ht
  have h1 := hanti ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1
  simp only [φ, w, sub_self, mul_zero, neg_zero, exp_zero, one_mul,
    intervalIntegral.integral_same, sub_zero] at h1
  have h2 : ∫ r in t₀..t, w r * G r ≤ ∫ r in t₀..t, G r := by
    refine intervalIntegral.integral_mono_on ht.1 (hwG.intervalIntegrable _ _)
      (hG.intervalIntegrable _ _) fun r hr => ?_
    have hG0r := hG0 r ⟨hr.1, hr.2.trans ht.2⟩
    have : w r ≤ 1 := exp_le_one_iff.2 (by nlinarith [hr.1])
    nlinarith
  have h3 : E t = exp (C * (t - t₀)) * (w t * E t) := by
    rw [← mul_assoc, ← exp_add]; simp
  rw [h3]
  exact mul_le_mul_of_nonneg_left (by linarith) (exp_pos _).le

end

end LorentzianCalderon.PDE
