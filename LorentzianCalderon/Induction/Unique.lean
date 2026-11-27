module

public import LorentzianCalderon.Induction.Setup
public import LorentzianCalderon.Local.Rigidity
public import LorentzianCalderon.Green.Basic

public section

/-!
# Uniqueness of the extension

Blueprint `lem_extension_unique`: two maps with the extension property at level `τ` agree, by
rigidity of local isometries on the connected set `A ψ τ`.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set

variable {n : ℕ} {g g' : MatrixField n} {Y Y' : E n → E n} {ψ : E n → ℝ} {W : Set (E n)}
  {τ : ℝ} {Ψ Ψ' : E n → E n}

theorem ExtensionProperty.eqOn (h : ExtensionProperty g g' ψ W τ Ψ)
    (h' : ExtensionProperty g g' ψ W τ Ψ') (hg : IsSpacetime g Y) (hg' : IsSpacetime g' Y')
    (hψ : Continuous ψ) (hW : IsClosed W) (hconn : IsPreconnected (A ψ τ))
    (hne : (A ψ τ \ W).Nonempty) : EqOn Ψ Ψ' (A ψ τ) := by
  refine eqOn_of_pullback_eq (isOpen_A hψ τ) hconn (fun i j => (hg.smooth i j).contDiffOn)
    (fun x _ => hg.det_ne_zero x) hg'.smooth hg'.symm hg'.det_ne_zero h.smooth h'.smooth
    h.pullback h'.pullback ((isOpen_A hψ τ).sdiff hW) sdiff_subset hne ?_
  intro x hx
  rw [h.eq_self x hx.1 hx.2, h'.eq_self x hx.1 hx.2]

/-- The restriction of a map with the extension property to a higher level keeps it. -/
theorem ExtensionProperty.mono (h : ExtensionProperty g g' ψ W τ Ψ) {τ₁ : ℝ} (hτ : τ ≤ τ₁) :
    ExtensionProperty g g' ψ W τ₁ Ψ where
  smooth := h.smooth.mono fun _ hx => mem_A.2 (lt_of_le_of_lt hτ (mem_A.1 hx))
  pullback x hx := h.pullback x (mem_A.2 (lt_of_le_of_lt hτ (mem_A.1 hx)))
  eq_self x hx := h.eq_self x (mem_A.2 (lt_of_le_of_lt hτ (mem_A.1 hx)))

end

end LorentzianCalderon
