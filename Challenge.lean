module

public import Mathlib

public section

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix

/-!
Uniqueness for the Lorentzian Calderón problem from Cauchy data sets, for the
box `M₀ = [-T, T] × B̄ ⊆ ℝ^{1+n}`, where `B = (-1, 1)ⁿ` is the open unit cube,
and for metrics that are Minkowskian outside `M₀`.

Points of `ℝ^{1+n}` are `x = (x 0, x 1, …, x n)`, with time `x 0`. A metric is a
smooth matrix-valued function `g : ℝ^{1+n} → ℝ^{(1+n)×(1+n)}` in Cartesian
coordinates.

The Cauchy data set of `g` consists of the pairs `(u|_{∂M₀}, ∂_ν u|_{∂M₀})` of the
smooth solutions of `□_g u = 0` in `M₀`, the normal derivative being taken on the
open faces of `∂M₀`. Two solutions `u, v` have the same such pair if and only if
`u = v` and `du = dv` on all of `∂M₀`: equal values on the open faces give equal
tangential derivatives there, and the open faces are dense in `∂M₀`. This is the
form used below. A function smooth up to the boundary of the box extends to a
smooth function on `ℝ^{1+n}`, so the solutions are taken to be smooth functions on
`ℝ^{1+n}` that solve the equation in `M₀`.

Causal curves are piecewise smooth with future-directed causal velocities, as in
O'Neill, Semi-Riemannian geometry (1983). Global hyperbolicity is compactness of
the causal diamonds `J⁺(p) ∩ J⁻(q)`. Since `ℝ^{1+n}` is not compact and has
dimension `1 + n ≥ 3`, this is equivalent to the traditional definition, which also
requires strong causality, by Hounnonkpe and Minguzzi, Class. Quantum Grav. 36
(2019), 197001, Theorem 2.8.
-/

/-- The spacetime `ℝ^{1+n}`; the coordinate `0` is time. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin (n + 1))

/-- Fields of `(1+n) × (1+n)` matrices on `ℝ^{1+n}`, such as metrics and Jacobians. -/
abbrev MatrixField (n : ℕ) := E n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ

-- `minkowski` and `M0` are exposed: their bodies use an automatically generated proof of
-- `n + 1 ≠ 0`, whose name otherwise contains the module name, so that the copies in
-- `Challenge` and `LorentzianCalderon.Defs` would differ for Comparator.
/-- The Minkowski metric `diag(-1, 1, …, 1)`. -/
@[expose] def minkowski (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.diagonal fun i => if i = 0 then -1 else 1

/-- The closed box `M₀ = [-T, T] × [-1, 1]ⁿ`, the closure of `Q_T = (-T, T) × B`. -/
@[expose] def M0 (n : ℕ) (T : ℝ) : Set (E n) :=
  { x | |x 0| ≤ T } ∩ { x | ∀ i : Fin n, |x i.succ| ≤ 1 }

/-- The bilinear form `A(v, w) = vⁱ Aᵢⱼ wʲ`. -/
def form {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (v w : E n) : ℝ :=
  ∑ i, ∑ j, v i * A i j * w j

/-- Differential `du(x)` in Cartesian coordinates, `d u x i = ∂ᵢu(x)`. -/
def d {n : ℕ} (u : E n → ℝ) (x : E n) : Fin (n + 1) → ℝ :=
  fun i => fderiv ℝ u x (EuclideanSpace.single i 1)

/-- Jacobian matrix, `D Ψ x i j = ∂ⱼΨⁱ(x)`. -/
def D {n : ℕ} (Ψ : E n → E n) : MatrixField n :=
  fun x => Matrix.of fun i j => fderiv ℝ Ψ x (EuclideanSpace.single j 1) i

/-- The wave operator
`□_g u = -|det g|^{-1/2} ∂ⱼ(|det g|^{1/2} g^{jk} ∂ₖu)`, so that `□ = ∂ₜ² - Δₓ`
for the Minkowski metric. -/
def box {n : ℕ} (g : MatrixField n) (u : E n → ℝ) (x : E n) : ℝ :=
  -(Real.sqrt |(g x).det|)⁻¹ *
    ∑ j, d (fun y => Real.sqrt |(g y).det| * ∑ k, (g y)⁻¹ j k * d u y k) x j

/-- `V` is an `n`-dimensional subspace on which the form `A` is positive definite. -/
structure IsSpacelikeSubspace {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (V : Submodule ℝ (E n)) : Prop where
  finrank_eq : Module.finrank ℝ V = n
  pos : ∀ v ∈ V, v ≠ 0 → 0 < form A v v

/-- `A` is a Lorentzian scalar product: symmetric of signature `(-, +, …, +)`.
Being positive definite on an `n`-dimensional subspace gives at least `n` positive
eigenvalues, and the negative determinant makes the remaining one negative. -/
structure IsLorentzian {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Prop where
  symm : Aᵀ = A
  det_neg : A.det < 0
  spacelike : ∃ V, IsSpacelikeSubspace A V

/-- A time orientation of `g`: a continuous timelike vector field `Y`. A causal vector
`v` is future-directed when `g(v, Y) < 0`. -/
structure IsTimeOrientation {n : ℕ} (g : MatrixField n) (Y : E n → E n) : Prop where
  continuous : Continuous Y
  timelike : ∀ x, form (g x) (Y x) (Y x) < 0

/-- `v` is a future-directed causal vector at `x`. -/
structure IsFutureCausal {n : ℕ} (g : MatrixField n) (Y : E n → E n) (x v : E n) :
    Prop where
  ne_zero : v ≠ 0
  causal : form (g x) v v ≤ 0
  future : form (g x) v (Y x) < 0

/-- `s` is a partition `0 = s 0 < s 1 < ⋯ < s (k + 1) = 1` of `[0, 1]`. -/
structure IsPartition {k : ℕ} (s : Fin (k + 2) → ℝ) : Prop where
  strictMono : StrictMono s
  first : s 0 = 0
  last : s (Fin.last (k + 1)) = 1

/-- The `i`-th subinterval `[s i, s (i + 1)]` of the partition `s`. -/
def piece {k : ℕ} (s : Fin (k + 2) → ℝ) (i : Fin (k + 1)) : Set ℝ :=
  Set.Icc (s i.castSucc) (s i.succ)

/-- `γ` is a future-directed causal curve from `p = γ 0` to `q = γ 1`, smooth on each
piece of the partition `s`, with one-sided velocities at the break points. -/
structure IsCausalCurve {n k : ℕ} (g : MatrixField n) (Y : E n → E n) (p q : E n)
    (s : Fin (k + 2) → ℝ) (γ : ℝ → E n) : Prop where
  partition : IsPartition s
  source : γ 0 = p
  target : γ 1 = q
  smooth : ∀ i, ContDiffOn ℝ ∞ γ (piece s i)
  causal : ∀ i, ∀ t ∈ piece s i, IsFutureCausal g Y (γ t) (derivWithin γ (piece s i) t)

/-- `p ≤ q`: `p = q`, or there is a piecewise smooth future-directed causal curve from
`p` to `q`. -/
def CausalLE {n : ℕ} (g : MatrixField n) (Y : E n → E n) (p q : E n) : Prop :=
  p = q ∨ ∃ (k : ℕ) (s : Fin (k + 2) → ℝ) (γ : ℝ → E n), IsCausalCurve g Y p q s γ

/-- The causal future `J⁺(p)`. -/
def causalFuture {n : ℕ} (g : MatrixField n) (Y : E n → E n) (p : E n) : Set (E n) :=
  { x | CausalLE g Y p x }

/-- The causal past `J⁻(q)`. -/
def causalPast {n : ℕ} (g : MatrixField n) (Y : E n → E n) (q : E n) : Set (E n) :=
  { x | CausalLE g Y x q }

/-- `g` is globally hyperbolic for the time orientation `Y`: the causal diamonds
`J⁺(p) ∩ J⁻(q)` are compact. -/
structure IsGloballyHyperbolic {n : ℕ} (g : MatrixField n) (Y : E n → E n) : Prop where
  timeOrientation : IsTimeOrientation g Y
  compact_diamond : ∀ p q, IsCompact (causalFuture g Y p ∩ causalPast g Y q)

/-- `g` is a smooth Lorentzian metric on `ℝ^{1+n}`, equal to the Minkowski metric
outside `M₀`, and globally hyperbolic for some time orientation. -/
structure IsAdmissibleMetric (n : ℕ) (T : ℝ) (g : MatrixField n) : Prop where
  smooth : ∀ i j, ContDiff ℝ ∞ fun x => g x i j
  lorentzian : ∀ x, IsLorentzian (g x)
  minkowski_exterior : ∀ x ∉ M0 n T, g x = minkowski n
  globallyHyperbolic : ∃ Y, IsGloballyHyperbolic g Y

/-- `u` is smooth and solves `□_g u = 0` in `M₀`. -/
structure IsSolution (n : ℕ) (T : ℝ) (g : MatrixField n) (u : E n → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ u
  wave : ∀ x ∈ M0 n T, box g u x = 0

/-- `u` and `v` have the same Cauchy data on `∂M₀`: equal values and differentials. -/
structure SameCauchyData (n : ℕ) (T : ℝ) (u v : E n → ℝ) : Prop where
  value : ∀ x ∈ frontier (M0 n T), u x = v x
  differential : ∀ x ∈ frontier (M0 n T), fderiv ℝ u x = fderiv ℝ v x

/-- The Cauchy data set of `g₁` is contained in that of `g₂`: every solution for `g₁`
has the Cauchy data on `∂M₀` of some solution for `g₂`. -/
def CauchyDataSubset (n : ℕ) (T : ℝ) (g₁ g₂ : MatrixField n) : Prop :=
  ∀ u, IsSolution n T g₁ u → ∃ v, IsSolution n T g₂ v ∧ SameCauchyData n T u v

/-- `g₁` and `g₂` have the same Cauchy data set on `∂M₀`. -/
structure SameCauchyDataSet (n : ℕ) (T : ℝ) (g₁ g₂ : MatrixField n) : Prop where
  subset : CauchyDataSubset n T g₁ g₂
  supset : CauchyDataSubset n T g₂ g₁

/-- `Ψ` is a diffeomorphism of `ℝ^{1+n}` that is the identity outside `M₀` and pulls
`g'` back to `g`, i.e. `g = Ψ^* g'`. -/
structure IsIsometryFixingExterior (n : ℕ) (T : ℝ) (Ψ : E n ≃ E n)
    (g g' : MatrixField n) : Prop where
  smooth : ContDiff ℝ ∞ Ψ
  smooth_inv : ContDiff ℝ ∞ Ψ.symm
  fixes_exterior : ∀ x ∉ M0 n T, Ψ x = x
  isometry : ∀ x, g x = (D Ψ x)ᵀ * g' (Ψ x) * D Ψ x

/-- Main theorem: for `n ≥ 2`, two metrics that are Minkowskian outside the box
`M₀` and have the same Cauchy data set on `∂M₀` agree up to a diffeomorphism that is
the identity outside `M₀`. -/
theorem main (n : ℕ) (hn : 2 ≤ n) (T : ℝ) (hT : 0 < T) (g g' : MatrixField n)
    (hg : IsAdmissibleMetric n T g) (hg' : IsAdmissibleMetric n T g')
    (hC : SameCauchyDataSet n T g g') :
    ∃ Ψ : E n ≃ E n, IsIsometryFixingExterior n T Ψ g g' := by
  sorry

end

end LorentzianCalderon
