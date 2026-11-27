module

public import LorentzianCalderon.Geometry.Span

public section

/-!
# Open conditions for the local gauge

Blueprint, Lemma `lem_ind_local_extension`, Step C2: the basis and spanning properties of the
differentials of the phases at `p₀` persist near `p₀`, as linear independence of finitely many
continuously varying vectors is an open condition.
-/

namespace LorentzianCalderon

open Matrix Set Filter
open scoped Topology

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

/-- Linear independence of finitely many continuously varying vectors is an open condition. -/
theorem eventually_linearIndependent {κ : Type*} [Finite κ] {m : ℕ} {f : κ → X → (Fin m → ℝ)}
    {p : X} (hf : ∀ k i, ContinuousAt (fun z => f k z i) p)
    (h : LinearIndependent ℝ fun k => f k p) :
    ∀ᶠ z in 𝓝 p, LinearIndependent ℝ fun k => f k z := by
  have hc : ContinuousAt (fun z k => f k z) p :=
    continuousAt_pi.2 fun k => continuousAt_pi.2 fun i => hf k i
  exact Filter.Tendsto.eventually (p := fun v : κ → Fin m → ℝ => LinearIndependent ℝ v) hc
    h.eventually

/-- The property that finitely many continuously varying symmetric matrices span the symmetric
matrices is an open condition. -/
theorem eventually_forall_mem_span {κ : Type*} [Finite κ]
    {F : κ → X → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {p : X}
    (hF : ∀ k i j, ContinuousAt (fun z => F k z i j) p) (hsymm : ∀ k z, (F k z)ᵀ = F k z)
    (hspan : ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ, Mᵀ = M →
      M ∈ Submodule.span ℝ (range fun k => F k p)) :
    ∀ᶠ z in 𝓝 p, ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ, Mᵀ = M →
      M ∈ Submodule.span ℝ (range fun k => F k z) := by
  classical
  obtain ⟨κ', a, ha, hspa, hli⟩ := exists_linearIndependent' ℝ (fun k => F k p)
  have : Finite κ' := Finite.of_injective a ha
  have := Fintype.ofFinite κ'
  have hle : ∀ z, Submodule.span ℝ (range fun k => F k z) ≤ symmetricMatrices n := fun z =>
    Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact mem_symmetricMatrices.2 (hsymm k z))
  have hSp : Submodule.span ℝ (range fun k => F k p) = symmetricMatrices n :=
    le_antisymm (hle p) fun M hM => hspan M (mem_symmetricMatrices.1 hM)
  have hrank : Module.finrank ℝ (symmetricMatrices n) = Fintype.card κ' := by
    rw [← hSp, ← hspa]
    exact finrank_span_eq_card hli
  have hc : ContinuousAt (fun z (k : κ') (i j : Fin (n + 1)) => F (a k) z i j) p :=
    continuousAt_pi.2 fun k => continuousAt_pi.2 fun i => continuousAt_pi.2 fun j => hF (a k) i j
  have hev : ∀ᶠ z in 𝓝 p,
      LinearIndependent ℝ fun (k : κ') (i j : Fin (n + 1)) => F (a k) z i j :=
    Filter.Tendsto.eventually
      (p := fun v : κ' → Fin (n + 1) → Fin (n + 1) → ℝ => LinearIndependent ℝ v) hc
      (LinearIndependent.eventually (f := fun (k : κ')
      (i j : Fin (n + 1)) => F (a k) p i j) hli)
  filter_upwards [hev] with z hz M hM
  have hz' : LinearIndependent ℝ fun k => F (a k) z := hz
  have hle' : Submodule.span ℝ (range fun k => F (a k) z) ≤ symmetricMatrices n :=
    (Submodule.span_mono (range_comp_subset_range a fun k => F k z)).trans (hle z)
  have heq : Submodule.span ℝ (range fun k => F (a k) z) = symmetricMatrices n :=
    Submodule.eq_of_le_of_finrank_eq hle' (by rw [finrank_span_eq_card hz', hrank])
  have hMs : M ∈ symmetricMatrices n := mem_symmetricMatrices.2 hM
  rw [← heq] at hMs
  exact Submodule.span_mono (range_comp_subset_range a fun k => F k z) hMs

end LorentzianCalderon
