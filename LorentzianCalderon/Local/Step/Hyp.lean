module

public import LorentzianCalderon.Local.Step.EnergyInterface
public import LorentzianCalderon.Local.Naturality
public import LorentzianCalderon.Local.Comparison

public section

/-!
# The hypotheses of the local continuation step

Blueprint, Proposition `prop_local_step`. The data are bundled in `StepData`, the hypotheses
(L0)–(L4) in `StepData.Hyp`. Condition (L1) is replaced by the pointwise conormal conditions of
`lem_conormal`(b), for both metrics: with `Z u = -g(dφ, du)`,
* `□_g u_{a,s} = (φ_a - s) A_{a,s}` with `A_{a,s} = 0` on `{φ_a > s}`,
* `2 Z_a u_{a,s} + u_{a,s} □_g φ_a = (φ_a - s) B_{a,s}`,

and likewise for `g'`, with `u, A, B` continuous in `(s, x)` and `u` smooth in `(s, x)`.
-/

namespace LorentzianCalderon

noncomputable section
open Set Matrix
open scoped ContDiff

/-- The data of the local continuation step: metrics `g, g'` with time orientations `Y, Y'`,
open sets `V, V'`, the map `Ψ : V → V'`, the temporal function `ψ` with the point `q₀`, the
interval `J` of levels, the eikonal functions `φ a`, `φ' a`, the amplitudes `u a s`, `u' a s` with
the coefficients `A, B, A', B'` of `lem_conormal`(b), and the `n + 1` gauge labels `e`. -/
structure StepData (n : ℕ) (ι : Type*) where
  g : MatrixField n
  g' : MatrixField n
  Y : E n → E n
  Y' : E n → E n
  V : Set (E n)
  V' : Set (E n)
  Ψ : E n → E n
  ψ : E n → ℝ
  q₀ : E n
  J : Set ℝ
  φ : ι → E n → ℝ
  φ' : ι → E n → ℝ
  u : ι → ℝ → E n → ℝ
  u' : ι → ℝ → E n → ℝ
  A : ι → ℝ → E n → ℝ
  B : ι → ℝ → E n → ℝ
  A' : ι → ℝ → E n → ℝ
  B' : ι → ℝ → E n → ℝ
  e : Fin (n + 1) → ι

variable {n : ℕ} {ι : Type*}

namespace StepData

/-- The level `τ = ψ(q₀)`. -/
def τ (S : StepData n ι) : ℝ := S.ψ S.q₀

theorem τ_def (S : StepData n ι) :
    τ S =
      S.ψ S.q₀ := by rfl

/-- The hypotheses (L0)–(L4) of `prop_local_step`, with (L1) in the pointwise form of
`lem_conormal`(b). -/
structure Hyp (S : StepData n ι) : Prop where
  two_le : 2 ≤ n
  smooth_g : ∀ i j, ContDiff ℝ ∞ fun x => S.g x i j
  lorentzian_g : ∀ x, IsLorentzian (S.g x)
  time_g : IsTimeOrientation S.g S.Y
  smooth_g' : ∀ i j, ContDiff ℝ ∞ fun x => S.g' x i j
  lorentzian_g' : ∀ x, IsLorentzian (S.g' x)
  time_g' : IsTimeOrientation S.g' S.Y'
  /-- (L0) -/
  isOpen_V : IsOpen S.V
  isOpen_V' : IsOpen S.V'
  smooth_Ψ : ContDiffOn ℝ ∞ S.Ψ S.V
  mapsTo_Ψ : MapsTo S.Ψ S.V S.V'
  smooth_ψ : ContDiffOn ℝ ∞ S.ψ S.V
  temporal : ∀ x ∈ S.V, IsFutureTimelike S.g S.Y x (-grad S.g S.ψ x)
  mem_V : S.q₀ ∈ S.V
  /-- (L1): the levels form an open interval. -/
  isOpen_J : IsOpen S.J
  ordConnected_J : S.J.OrdConnected
  eikonal : ∀ a, StepEikonal S.V S.g S.Y (S.φ a)
  eikonal' : ∀ a, StepEikonal S.V' S.g' S.Y' (S.φ' a)
  mem_J : ∀ a, ∀ x ∈ S.V, S.φ a x ∈ S.J
  mem_J' : ∀ a, ∀ x ∈ S.V', S.φ' a x ∈ S.J
  smooth_u : ∀ a, ContDiffOn ℝ ∞ (fun p : ℝ × E n => S.u a p.1 p.2) (S.J ×ˢ S.V)
  smooth_u' : ∀ a, ContDiffOn ℝ ∞ (fun p : ℝ × E n => S.u' a p.1 p.2) (S.J ×ˢ S.V')
  continuous_A : ∀ a, ContinuousOn (fun p : ℝ × E n => S.A a p.1 p.2) (S.J ×ˢ S.V)
  continuous_B : ∀ a, ContinuousOn (fun p : ℝ × E n => S.B a p.1 p.2) (S.J ×ˢ S.V)
  continuous_A' : ∀ a, ContinuousOn (fun p : ℝ × E n => S.A' a p.1 p.2) (S.J ×ˢ S.V')
  continuous_B' : ∀ a, ContinuousOn (fun p : ℝ × E n => S.B' a p.1 p.2) (S.J ×ˢ S.V')
  wave : ∀ a, ∀ s ∈ S.J, ∀ x ∈ S.V, box S.g (S.u a s) x = (S.φ a x - s) * S.A a s x
  wave_zero : ∀ a, ∀ s ∈ S.J, ∀ x ∈ S.V, s < S.φ a x → S.A a s x = 0
  transport : ∀ a, ∀ s ∈ S.J, ∀ x ∈ S.V,
    2 * -coform S.g x (d (S.φ a) x) (d (S.u a s) x) + S.u a s x * box S.g (S.φ a) x =
      (S.φ a x - s) * S.B a s x
  wave' : ∀ a, ∀ s ∈ S.J, ∀ z ∈ S.V', box S.g' (S.u' a s) z = (S.φ' a z - s) * S.A' a s z
  wave_zero' : ∀ a, ∀ s ∈ S.J, ∀ z ∈ S.V', s < S.φ' a z → S.A' a s z = 0
  transport' : ∀ a, ∀ s ∈ S.J, ∀ z ∈ S.V',
    2 * -coform S.g' z (d (S.φ' a) z) (d (S.u' a s) z) + S.u' a s z * box S.g' (S.φ' a) z =
      (S.φ' a z - s) * S.B' a s z
  /-- (L1): `u_{a,s} > 0` on `{φ_a = s}`. -/
  pos : ∀ a, ∀ s ∈ S.J, ∀ x ∈ S.V, S.φ a x = s → 0 < S.u a s x
  /-- (L2), on `V₊ = {x ∈ V | τ < ψ x}`. -/
  pullback_top : ∀ x ∈ S.V, S.τ < S.ψ x → S.g x = (D S.Ψ x)ᵀ * S.g' (S.Ψ x) * D S.Ψ x
  phase_top : ∀ a, ∀ x ∈ S.V, S.τ < S.ψ x → S.φ' a (S.Ψ x) = S.φ a x
  amplitude_top : ∀ a, ∀ s ∈ S.J, ∀ x ∈ S.V, S.τ < S.ψ x → s ≤ S.φ a x →
    S.u a s x = S.u' a s (S.Ψ x)
  /-- (L3) -/
  gauge : ∀ i, ∀ x ∈ S.V, S.φ' (S.e i) (S.Ψ x) = S.φ (S.e i) x
  basis : ∀ z ∈ S.V', LinearIndependent ℝ fun i => d (S.φ' (S.e i)) z
  /-- (L4) -/
  span : ∀ z ∈ S.V', ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ, Mᵀ = M →
    M ∈ Submodule.span ℝ
      (insert (S.g' z) (range fun a => vecMulVec (d (S.φ' a) z) (d (S.φ' a) z)))

end StepData

end

end LorentzianCalderon
