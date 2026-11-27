module

public import LorentzianCalderon.Local.Energy.Compactness

public section

/-!
# Uniform bounds on compact sets

Bounds by compactness used in the local continuation step: a continuous family of positive
quadratic forms is uniformly coercive. Applied to the basis
property (L3) and the spanning property (L4).
-/

namespace LorentzianCalderon

open Set Matrix

/-- A continuous family of positive quadratic forms over a compact set is uniformly
coercive. -/
theorem exists_coercive_on {X W : Type*} [TopologicalSpace X] [NormedAddCommGroup W]
    [NormedSpace ℝ W] [ProperSpace W] [Nontrivial W] {K : Set X} (hK : IsCompact K)
    {F : X → W → ℝ} (hF : ContinuousOn (fun p : X × W => F p.1 p.2) (K ×ˢ univ))
    (hhom : ∀ z (t : ℝ) v, F z (t • v) = t ^ 2 * F z v)
    (hpos : ∀ z ∈ K, ∀ v, v ≠ 0 → 0 < F z v) :
    ∃ c > 0, ∀ z ∈ K, ∀ v, c * ‖v‖ ^ 2 ≤ F z v := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  obtain ⟨c, hc, h⟩ := exists_coercive_of_homogeneous (Z := K) (W := W)
    (F := fun z v => F z v)
    (hF.comp_continuous (continuous_subtype_val.prodMap continuous_id)
      fun p => ⟨p.1.2, mem_univ _⟩)
    (fun z t v => hhom z t v) fun z v hv => hpos z z.2 v hv
  exact ⟨c, hc, fun z hz v => h ⟨z, hz⟩ v⟩

variable {n : ℕ}

/-- If finitely many covectors `ξ_i` span, `θ ↦ Σ_i (θ · ξ_i)²` is positive definite. -/
theorem sum_sq_dotProduct_pos {ξ : Fin (n + 1) → Fin (n + 1) → ℝ} (hξ : LinearIndependent ℝ ξ)
    {θ : Fin (n + 1) → ℝ} (hθ : θ ≠ 0) : 0 < ∑ i, (∑ k, θ k * ξ i k) ^ 2 := by
  by_contra hle
  push Not at hle
  have h0 : ∀ i, ∑ k, θ k * ξ i k = 0 := fun i => by
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (∑ k, θ k * ξ i k))).1
      (le_antisymm hle (Finset.sum_nonneg fun i _ => sq_nonneg _)) i (Finset.mem_univ _)
    exact pow_eq_zero_iff (two_ne_zero) |>.1 this
  set b := basisOfLinearIndependentOfCardEqFinrank hξ (by simp)
  have hv : ∀ v, θ ⬝ᵥ v = 0 := fun v => by
    rw [← b.sum_repr v, dotProduct_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [dotProduct_smul, coe_basisOfLinearIndependentOfCardEqFinrank]
    simp [dotProduct, h0 i]
  exact hθ (dotProduct_self_eq_zero.1 (hv θ))

/-- If `{A} ∪ {ξ_a ξ_aᵀ}` spans the symmetric matrices, a symmetric matrix orthogonal to all of
them vanishes. -/
theorem eq_zero_of_span {ι : Type*} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {ξ : ι → Fin (n + 1) → ℝ}
    (hspan : ∀ N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ, Nᵀ = N →
      N ∈ Submodule.span ℝ (insert A (range fun a => vecMulVec (ξ a) (ξ a))))
    {M : Fin (n + 1) → Fin (n + 1) → ℝ} (hM : ∀ α β, M α β = M β α)
    (hA : ∑ α, ∑ β, A α β * M α β = 0)
    (hξ : ∀ a, ∑ α, ∑ β, M α β * ξ a α * ξ a β = 0) : M = 0 := by
  let ℓ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun N => ∑ α, ∑ β, M α β * N α β
      map_add' := fun N N' => by
        simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c N => by
        simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring }
  have hle : Submodule.span ℝ (insert A (range fun a => vecMulVec (ξ a) (ξ a))) ≤
      LinearMap.ker ℓ := by
    rw [Submodule.span_le]
    rintro N (rfl | ⟨a, rfl⟩)
    · simp only [SetLike.mem_coe, LinearMap.mem_ker]
      show ∑ α, ∑ β, M α β * N α β = 0
      rw [← hA]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    · simp only [SetLike.mem_coe, LinearMap.mem_ker]
      show ∑ α, ∑ β, M α β * vecMulVec (ξ a) (ξ a) α β = 0
      rw [← hξ a]
      simp only [vecMulVec_apply]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hMs : (Matrix.of M)ᵀ = Matrix.of M := by
    ext α β; simp [hM β α]
  have h := hle (hspan _ hMs)
  simp only [LinearMap.mem_ker] at h
  change ∑ α, ∑ β, M α β * M α β = 0 at h
  have h2 : ∀ α β, M α β = 0 := by
    intro α β
    have hα := (Finset.sum_eq_zero_iff_of_nonneg (fun α _ => Finset.sum_nonneg
      fun β _ => mul_self_nonneg (M α β))).1 h α (Finset.mem_univ _)
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun β _ => mul_self_nonneg (M α β))).1 hα β
      (Finset.mem_univ _)
    exact mul_self_eq_zero.1 this
  funext α β
  exact h2 α β

end LorentzianCalderon
