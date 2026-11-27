module

public import LorentzianCalderon.Geometry.CausalClosed
public import LorentzianCalderon.Geometry.PushUp

public section

/-!
# Chronology

No point is chronologically related to itself (`not_chronLT_self`). If `p ≪ p`, the set
`I⁺(p) ∩ I⁻(p)` is open, nonempty, and closed: a limit `y` of its points satisfies `p ≤ y ≤ p`
by closedness of `J^±(p)`, so `p ≪ p ≤ y` and `y ≤ p ≪ p` give `p ≪ y ≪ p` by push-up. Hence
it is all of `ℝ^{1+n}`, and the diamond `J⁺(p) ∩ J⁻(p)` would be the whole noncompact space.
This is Clarke and Joshi's observation that compact diamonds exclude total viciousness.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Filter

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n}

/-- Chronology: `p ≪ p` never holds. -/
theorem not_chronLT_self (hg : IsSpacetime g Y) (p : E n) : ¬ ChronLT g Y p p := by
  intro hpp
  set S := chronFuture g Y p ∩ chronPast g Y p
  have hopen : IsOpen S := (Facts.isOpen_chronFuture hg p).inter (isOpen_chronPast hg p)
  have hclosed : IsClosed S := by
    refine isClosed_of_closure_subset fun y hy => ?_
    have h1 : CausalLE g Y p y := mem_causalFuture.1 <| (isClosed_causalFuture hg p).closure_subset
      (closure_mono (inter_subset_left.trans (chronFuture_subset_causalFuture p)) hy)
    have h2 : CausalLE g Y y p := mem_causalPast.1 <| (isClosed_causalPast hg p).closure_subset
      (closure_mono (inter_subset_right.trans (chronPast_subset_causalPast p)) hy)
    exact ⟨mem_chronFuture.2 (hpp.trans_causalLE hg h1), mem_chronPast.2 (h2.trans_chronLT hg hpp)⟩
  have huniv : S = univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨p, mem_chronFuture.2 hpp,
    mem_chronPast.2 hpp⟩
  have hcomp := hg.globallyHyperbolic.compact_diamond p p
  have : causalFuture g Y p ∩ causalPast g Y p = univ := eq_univ_of_univ_subset fun x _ =>
    have hx : x ∈ S := huniv ▸ mem_univ x
    ⟨mem_causalFuture.2 (ChronLT.causalLE (mem_chronFuture.1 hx.1)),
      mem_causalPast.2 (ChronLT.causalLE (mem_chronPast.1 hx.2))⟩
  rw [this] at hcomp
  exact noncompact_univ (E n) hcomp

/-- `p ≪ q ≪ p` never holds. -/
theorem not_chronLT_of_chronLT (hg : IsSpacetime g Y) {p q : E n} (hpq : ChronLT g Y p q) :
    ¬ ChronLT g Y q p := fun hqp => not_chronLT_self hg p (hpq.trans hqp)

end

end LorentzianCalderon
