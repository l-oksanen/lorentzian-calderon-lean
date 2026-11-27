module

public import LorentzianCalderon.Defs

public section

/-!
# Vocabulary for the cited facts

Definitions needed to state the facts quoted from the literature, for a smooth Lorentzian
metric `g` on `ℝ^{1+n}` with a time orientation `Y`. They build on the definitions of the
challenge (`Defs.lean`) and are part of the review surface together with the facts.

Curves are parametrized on intervals of `ℝ`. Inextendible curves are parametrized on
`[0, ∞)` (one-sided) or on `ℝ` (two-sided); every inextendible curve can be reparametrized
so, and the notions below do not depend on the parametrization.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Filter

variable {n : ℕ}

/-- `g` is a smooth Lorentzian metric on `ℝ^{1+n}`, `n ≥ 2`, globally hyperbolic for the time
orientation `Y`, and Minkowskian outside a box. -/
structure IsSpacetime (g : MatrixField n) (Y : E n → E n) : Prop where
  two_le : 2 ≤ n
  smooth : ∀ i j, ContDiff ℝ ∞ fun x => g x i j
  lorentzian : ∀ x, IsLorentzian (g x)
  globallyHyperbolic : IsGloballyHyperbolic g Y
  /-- `g` is Minkowskian outside a box, where `σ∂ₜ` is future-directed for a sign `σ`. -/
  exterior : ∃ (T σ : ℝ), (σ = 1 ∨ σ = -1) ∧ ∀ x ∉ M0 n T,
    g x = minkowski n ∧ form (g x) (σ • EuclideanSpace.single 0 1) (Y x) < 0

/-- The inner product `g(ξ, η) = g^{jk} ξ_j η_k` of covectors at `x`. -/
def coform (g : MatrixField n) (x : E n) (ξ η : Fin (n + 1) → ℝ) : ℝ :=
  ∑ j, ∑ k, (g x)⁻¹ j k * ξ j * η k

theorem coform_def (g : MatrixField n) (x : E n) (ξ η : Fin (n + 1) → ℝ) :
    coform g x ξ η =
      ∑ j, ∑ k, (g x)⁻¹ j k * ξ j * η k := by rfl

/-- The gradient `grad_g u = g^{-1} du`, as a vector. -/
def grad (g : MatrixField n) (u : E n → ℝ) (x : E n) : E n :=
  (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm fun j => ∑ k, (g x)⁻¹ j k * d u x k

theorem grad_def (g : MatrixField n) (u : E n → ℝ) (x : E n) :
    grad g u x =
      (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm fun j => ∑ k, (g x)⁻¹ j k * d u x k := by rfl

/-- `v` is a future-directed timelike vector at `x`. -/
structure IsFutureTimelike (g : MatrixField n) (Y : E n → E n) (x v : E n) : Prop where
  timelike : form (g x) v v < 0
  future : form (g x) v (Y x) < 0

/-- `s` is a partition `a = s 0 < s 1 < ⋯ < s (k + 1) = b` of `[a, b]`. -/
structure IsPartitionOf {k : ℕ} (a b : ℝ) (s : Fin (k + 2) → ℝ) : Prop where
  strictMono : StrictMono s
  first : s 0 = a
  last : s (Fin.last (k + 1)) = b

/-- `γ` is smooth on each piece of the partition `s`, with one-sided velocities satisfying `P`
(e.g. `P = IsFutureCausal g Y`). -/
structure IsPiecewisePath {k : ℕ} (P : E n → E n → Prop) (s : Fin (k + 2) → ℝ) (γ : ℝ → E n) :
    Prop where
  smooth : ∀ i, ContDiffOn ℝ ∞ γ (piece s i)
  velocity : ∀ i, ∀ t ∈ piece s i, P (γ t) (derivWithin γ (piece s i) t)

/-- `γ` is a piecewise smooth curve on `[a, b]` with velocities satisfying `P`. -/
def IsPathOn (P : E n → E n → Prop) (a b : ℝ) (γ : ℝ → E n) : Prop :=
  ∃ (k : ℕ) (s : Fin (k + 2) → ℝ), IsPartitionOf a b s ∧ IsPiecewisePath P s γ

theorem isPathOn_def {P : E n → E n → Prop} {a b : ℝ} {γ : ℝ → E n} :
    IsPathOn P a b γ ↔
      ∃ (k : ℕ) (s : Fin (k + 2) → ℝ), IsPartitionOf a b s ∧ IsPiecewisePath P s γ := Iff.rfl

/-- `p ≪ q`: there is a piecewise smooth future-directed timelike curve from `p` to `q`. -/
def ChronLT (g : MatrixField n) (Y : E n → E n) (p q : E n) : Prop :=
  ∃ γ : ℝ → E n, IsPathOn (IsFutureTimelike g Y) 0 1 γ ∧ γ 0 = p ∧ γ 1 = q

theorem chronLT_iff {g : MatrixField n} {Y : E n → E n} {p q : E n} :
    ChronLT g Y p q ↔
      ∃ γ : ℝ → E n, IsPathOn (IsFutureTimelike g Y) 0 1 γ ∧ γ 0 = p ∧ γ 1 = q := Iff.rfl

/-- The chronological future `I⁺(p)`. -/
def chronFuture (g : MatrixField n) (Y : E n → E n) (p : E n) : Set (E n) :=
  { x | ChronLT g Y p x }

theorem mem_chronFuture {g : MatrixField n} {Y : E n → E n} {p x : E n} :
    x ∈ chronFuture g Y p ↔ ChronLT g Y p x := Iff.rfl

/-- The chronological past `I⁻(q)`. -/
def chronPast (g : MatrixField n) (Y : E n → E n) (q : E n) : Set (E n) :=
  { x | ChronLT g Y x q }

theorem mem_chronPast {g : MatrixField n} {Y : E n → E n} {q x : E n} :
    x ∈ chronPast g Y q ↔ ChronLT g Y x q := Iff.rfl

/-- The causal future `J⁺(A)` of a set. -/
def causalFutureSet (g : MatrixField n) (Y : E n → E n) (A : Set (E n)) : Set (E n) :=
  ⋃ p ∈ A, causalFuture g Y p

theorem causalFutureSet_def (g : MatrixField n) (Y : E n → E n) (A : Set (E n)) :
    causalFutureSet g Y A =
      ⋃ p ∈ A, causalFuture g Y p := by rfl

theorem mem_causalFutureSet {g : MatrixField n} {Y : E n → E n} {A : Set (E n)} {x : E n} :
    x ∈ causalFutureSet g Y A ↔ ∃ p ∈ A, x ∈ causalFuture g Y p := by
  simp [causalFutureSet]

/-- The causal past `J⁻(A)` of a set. -/
def causalPastSet (g : MatrixField n) (Y : E n → E n) (A : Set (E n)) : Set (E n) :=
  ⋃ p ∈ A, causalPast g Y p

theorem causalPastSet_def (g : MatrixField n) (Y : E n → E n) (A : Set (E n)) :
    causalPastSet g Y A =
      ⋃ p ∈ A, causalPast g Y p := by rfl

theorem mem_causalPastSet {g : MatrixField n} {Y : E n → E n} {A : Set (E n)} {x : E n} :
    x ∈ causalPastSet g Y A ↔ ∃ p ∈ A, x ∈ causalPast g Y p := by
  simp [causalPastSet]

/-- `c` is an inextendible curve on `[0, ∞)` with velocities satisfying `P`: piecewise smooth
on every `[0, a]`, and without limit as the parameter tends to `∞`. With
`P = IsFutureCausal g Y` these are the future-inextendible causal curves, and with
`P = IsFutureCausal g (-Y)` the past-inextendible ones. -/
structure IsInextendibleRay (P : E n → E n → Prop) (c : ℝ → E n) : Prop where
  path : ∀ a > 0, IsPathOn P 0 a c
  no_limit : ∀ x, ¬ Tendsto c atTop (𝓝 x)

/-- `c` is a two-sided inextendible curve on `ℝ` with velocities satisfying `P`. -/
structure IsInextendibleLine (P : E n → E n → Prop) (c : ℝ → E n) : Prop where
  path : ∀ a b, a < b → IsPathOn P a b c
  no_limit_atTop : ∀ x, ¬ Tendsto c atTop (𝓝 x)
  no_limit_atBot : ∀ x, ¬ Tendsto c atBot (𝓝 x)

/-- A Cauchy hypersurface: a set met exactly once by every inextendible timelike curve. -/
def IsCauchyHypersurface (g : MatrixField n) (Y : E n → E n) (S : Set (E n)) : Prop :=
  ∀ c, IsInextendibleLine (IsFutureTimelike g Y) c → ∃! t, c t ∈ S

theorem isCauchyHypersurface_iff {g : MatrixField n} {Y : E n → E n} {S : Set (E n)} :
    IsCauchyHypersurface g Y S ↔
      ∀ c, IsInextendibleLine (IsFutureTimelike g Y) c → ∃! t, c t ∈ S := Iff.rfl

/-- `ψ` is a Cauchy temporal function: smooth, with `-grad ψ` future-directed timelike, and
all level sets Cauchy hypersurfaces. -/
structure IsCauchyTemporal (g : MatrixField n) (Y : E n → E n) (ψ : E n → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ ψ
  past_gradient : ∀ x, IsFutureTimelike g Y x (-grad g ψ x)
  cauchy : ∀ c : ℝ, IsCauchyHypersurface g Y (ψ ⁻¹' {c})

/-- The future-directed unit normal `ν = -grad ψ / √(-g(dψ, dψ))` of the level sets of `ψ`. -/
def unitNormal (g : MatrixField n) (ψ : E n → ℝ) (x : E n) : E n :=
  (Real.sqrt (-coform g x (d ψ x) (d ψ x)))⁻¹ • (-grad g ψ x)

theorem unitNormal_def (g : MatrixField n) (ψ : E n → ℝ) (x : E n) :
    unitNormal g ψ x =
      (Real.sqrt (-coform g x (d ψ x) (d ψ x)))⁻¹ • (-grad g ψ x) := by rfl

/-- The Christoffel symbols `Γᵏᵢⱼ = ½ gᵏˡ (∂ᵢ gⱼₗ + ∂ⱼ gᵢₗ - ∂ₗ gᵢⱼ)`. -/
def christoffel (g : MatrixField n) (x : E n) (k i j : Fin (n + 1)) : ℝ :=
  (1 / 2) * ∑ l, (g x)⁻¹ k l *
    (d (fun y => g y j l) x i + d (fun y => g y i l) x j - d (fun y => g y i j) x l)

theorem christoffel_def (g : MatrixField n) (x : E n) (k i j : Fin (n + 1)) :
    christoffel g x k i j =
      (1 / 2) * ∑ l, (g x)⁻¹ k l *
        (d (fun y => g y j l) x i + d (fun y => g y i l) x j - d (fun y => g y i j) x l) := by rfl

/-- `γ` is a geodesic on the open interval `I`: `γ̈ᵏ + Γᵏᵢⱼ γ̇ⁱ γ̇ʲ = 0`. -/
structure IsGeodesic (g : MatrixField n) (γ : ℝ → E n) (I : Set ℝ) : Prop where
  isOpen : IsOpen I
  smooth : ContDiffOn ℝ ∞ γ I
  equation : ∀ t ∈ I, ∀ k, deriv (deriv γ) t k +
    ∑ i, ∑ j, christoffel g (γ t) k i j * deriv γ t i * deriv γ t j = 0

/-- `(y, w)` lies in the domain of the exponential map: the geodesic with initial point `y` and
velocity `w` is defined on an open interval containing `[0, 1]`. -/
def InExpDomain (g : MatrixField n) (y w : E n) : Prop :=
  ∃ (γ : ℝ → E n) (I : Set ℝ),
    IsGeodesic g γ I ∧ Set.Icc 0 1 ⊆ I ∧ γ 0 = y ∧ deriv γ 0 = w

theorem inExpDomain_iff {g : MatrixField n} {y w : E n} :
    InExpDomain g y w ↔
      ∃ (γ : ℝ → E n) (I : Set ℝ),
        IsGeodesic g γ I ∧ Set.Icc 0 1 ⊆ I ∧ γ 0 = y ∧ deriv γ 0 = w := Iff.rfl

open Classical in
/-- The exponential map `exp_y w = γ(1)` for the geodesic `γ` with `γ(0) = y`, `γ'(0) = w`;
junk value `y` outside its domain. Geodesics are unique, so the value does not depend on the
choice of `γ`. -/
def expMap (g : MatrixField n) (y w : E n) : E n :=
  if h : InExpDomain g y w then h.choose 1 else y

open Classical in
theorem expMap_def (g : MatrixField n) (y w : E n) :
    expMap g y w =
      if h : InExpDomain g y w then (inExpDomain_iff.1 h).choose 1 else y := by rfl

/-- `exp_y` is singular at `w`, i.e. `exp_y w` is conjugate to `y` along the geodesic
`t ↦ exp_y (t w)`. -/
def IsConjugateAt (g : MatrixField n) (y w : E n) : Prop :=
  ¬ Function.Bijective (fderiv ℝ (expMap g y) w)

theorem isConjugateAt_iff {g : MatrixField n} {y w : E n} :
    IsConjugateAt g y w ↔
      ¬ Function.Bijective (fderiv ℝ (expMap g y) w) := Iff.rfl

/-- The path `γ` on `[a, b]` is a null pregeodesic: a monotone reparametrization of a null
geodesic. -/
def IsNullPregeodesicOn (g : MatrixField n) (a b : ℝ) (γ : ℝ → E n) : Prop :=
  ∃ (σ : ℝ → E n) (I : Set ℝ) (h : ℝ → ℝ), IsGeodesic g σ I ∧
    (∀ t ∈ I, form (g (σ t)) (deriv σ t) (deriv σ t) = 0) ∧
    MonotoneOn h (Set.Icc a b) ∧ ContinuousOn h (Set.Icc a b) ∧ h '' Set.Icc a b ⊆ I ∧
    ∀ t ∈ Set.Icc a b, γ t = σ (h t)

theorem isNullPregeodesicOn_iff {g : MatrixField n} {a b : ℝ} {γ : ℝ → E n} :
    IsNullPregeodesicOn g a b γ ↔
      ∃ (σ : ℝ → E n) (I : Set ℝ) (h : ℝ → ℝ), IsGeodesic g σ I ∧
        (∀ t ∈ I, form (g (σ t)) (deriv σ t) (deriv σ t) = 0) ∧
        MonotoneOn h (Set.Icc a b) ∧ ContinuousOn h (Set.Icc a b) ∧ h '' Set.Icc a b ⊆ I ∧
        ∀ t ∈ Set.Icc a b, γ t = σ (h t) := Iff.rfl

end

end LorentzianCalderon
