module

public import LorentzianCalderon.ODE.Smooth

public section

/-!
# Smooth dependence on initial data

The solution map `X(t, t₀, x₀, p)` of an autonomous equation `ẋ = F(x)` with a dummy parameter
`p`, as the call sites use it, from the flow of `ODE/Smooth.lean`. The names are in the
namespace `Facts`, with the other results from the literature.
-/

namespace LorentzianCalderon.Facts

noncomputable section
open scoped ContDiff Topology
open Filter

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- `x` solves `ẋ = F(t, x, p)` on the interval `I`, staying in `U`. -/
structure IsODESolution (F : ℝ → V → P → V) (U : Set V) (p : P) (x : ℝ → V) (I : Set ℝ) :
    Prop where
  interval : I.OrdConnected
  mem : ∀ t ∈ I, x t ∈ U
  deriv : ∀ t ∈ I, HasDerivWithinAt x (F t (x t) p) I t

/-- Smooth dependence on initial data, for an autonomous equation `ẋ = F(x)` (with a dummy
parameter `p`): the set of `(t, t₀, x₀, p)` for which the solution with `x(t₀) = x₀` reaches the
time `t` is open, and the solution is a smooth function of `(t, t₀, x₀, p)` there, namely
`Fl(t - t₀, x₀)` for the flow `Fl` of `F`. Hartman, Ordinary differential equations, 2nd ed.,
Chapter V, Theorems 3.1 and 4.1, in the special case of a field independent of the time and
of the parameter. -/
theorem ode_smooth_dependence {F : V → V} {U : Set V} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) :
    ∃ X : ℝ × ℝ × V × P → V,
      IsOpen { q : ℝ × ℝ × V × P | ∃ (x : ℝ → V) (I : Set ℝ),
        IsODESolution (fun _ y _ => F y) U q.2.2.2 x I ∧ q.1 ∈ I ∧ q.2.1 ∈ I ∧
          x q.2.1 = q.2.2.1 } ∧
      ContDiffOn ℝ ∞ X { q : ℝ × ℝ × V × P | ∃ (x : ℝ → V) (I : Set ℝ),
        IsODESolution (fun _ y _ => F y) U q.2.2.2 x I ∧ q.1 ∈ I ∧ q.2.1 ∈ I ∧
          x q.2.1 = q.2.2.1 } ∧
      ∀ (p : P) (x : ℝ → V) (I : Set ℝ), IsODESolution (fun _ y _ => F y) U p x I →
        ∀ t₀ ∈ I, ∀ t ∈ I, X (t, t₀, x t₀, p) = x t := by
  have hFL := ODEFlow.locallyLipschitzOn_of_contDiffOn hU (hF.of_le (by simp))
  obtain ⟨hD, hS⟩ := ODEFlow.contDiffOn_flow hU hF
  set π : ℝ × ℝ × V × P → ℝ × V := fun q => (q.1 - q.2.1, q.2.2.1)
  have hπ : ContDiff ℝ ∞ π := by fun_prop
  have hsol : ∀ (p : P) (x : ℝ → V) (I : Set ℝ),
      IsODESolution (fun _ y _ => F y) U p x I → ∀ t₀ : ℝ,
        ODEFlow.IsSol F U (fun s => x (s + t₀)) ((· + t₀) ⁻¹' I) :=
    fun p x I hx t₀ => (⟨hx.interval, hx.mem, hx.deriv⟩ : ODEFlow.IsSol F U x I).comp_add t₀
  have hDeq : { q : ℝ × ℝ × V × P | ∃ (x : ℝ → V) (I : Set ℝ),
      IsODESolution (fun _ y _ => F y) U q.2.2.2 x I ∧ q.1 ∈ I ∧ q.2.1 ∈ I ∧
        x q.2.1 = q.2.2.1 } = π ⁻¹' ODEFlow.dom F U := by
    ext q
    rw [Set.mem_preimage, ODEFlow.mem_dom]
    constructor
    · rintro ⟨x, I, hx, ht, ht₀, hx₀⟩
      exact ⟨_, _, hsol _ x I hx q.2.1, by simpa using ht₀, by simpa [π] using ht,
        by simpa using hx₀⟩
    · rintro ⟨c, I, hc, h0, ht, hc0⟩
      have h := hc.comp_add (-q.2.1)
      exact ⟨_, _, ⟨h.interval, h.mem, h.deriv⟩, by simpa [π, ← sub_eq_add_neg] using ht,
        by simpa using h0, by simpa using hc0⟩
  refine ⟨fun q => ODEFlow.flow F U (π q), ?_, ?_, ?_⟩
  · rw [hDeq]
    exact hD.preimage hπ.continuous
  · rw [hDeq]
    exact hS.comp hπ.contDiffOn fun q hq => hq
  · intro p x I hx t₀ ht₀ t ht
    have := ODEFlow.flow_eq hFL (hsol p x I hx t₀) (show (0 : ℝ) ∈ _ by simpa using ht₀)
      (show t - t₀ ∈ _ by simpa using ht)
    simpa using this

end

end LorentzianCalderon.Facts
