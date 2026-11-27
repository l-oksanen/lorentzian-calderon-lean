module

public import LorentzianCalderon.Defs

public section

/-!
# Partial derivatives in Cartesian coordinates

Calculus rules for the partial derivatives `d u x i = ∂ᵢu(x)` of `Defs.lean`, and the second
derivatives `d2 u x i j = ∂ᵢ∂ⱼu(x)`.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Finset

variable {n : ℕ}

/-- Second derivative in Cartesian coordinates, `d2 u x i j = ∂ᵢ∂ⱼu(x)`. -/
def d2 (u : E n → ℝ) (x : E n) (i j : Fin (n + 1)) : ℝ :=
  d (fun y => d u y j) x i

theorem d2_def (u : E n → ℝ) (x : E n) (i j : Fin (n + 1)) :
    d2 u x i j =
      d (fun y => d u y j) x i := by rfl

theorem clm_apply_eq_sum {G : Type*} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
    (L : E n →L[ℝ] G) (w : E n) :
    L w = ∑ i, w i • L (EuclideanSpace.single i 1) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).sum_repr w]
  simp [map_sum]

theorem apply_eq_sum_d (ℓ : E n →L[ℝ] ℝ) (w : E n) :
    ℓ w = ∑ j, ℓ (EuclideanSpace.single j 1) * w j := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).sum_repr w]
  simp [map_sum, mul_comm]

theorem fderiv_apply_eq_sum_d (u : E n → ℝ) (x w : E n) :
    fderiv ℝ u x w = ∑ i, w i * d u x i := by
  rw [clm_apply_eq_sum]
  simp [d_def, smul_eq_mul]

theorem fderiv_coord_apply {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : G → E n} {x : G} (hf : DifferentiableAt ℝ f x) (k : Fin (n + 1)) (w : G) :
    fderiv ℝ (fun y => f y k) x w = fderiv ℝ f x w k := by
  have := ((EuclideanSpace.proj k : E n →L[ℝ] ℝ).hasFDerivAt.comp x hf.hasFDerivAt).fderiv
  exact congrArg (· w) this

theorem d_coord_comp {Ψ : E n → E n} {x : E n} (hΨ : DifferentiableAt ℝ Ψ x)
    (α j : Fin (n + 1)) : d (fun y => Ψ y α) x j = D Ψ x α j := by
  rw [d_def, D_def]
  exact fderiv_coord_apply hΨ α _

theorem d_coord (x : E n) (k j : Fin (n + 1)) :
    d (fun y : E n => y k) x j = if j = k then 1 else 0 := by
  rw [d_coord_comp (Ψ := fun y => y) differentiableAt_id]
  simp [D_def, eq_comm]

theorem d_const (c : ℝ) (x : E n) (j : Fin (n + 1)) : d (fun _ => c) x j = 0 := by
  simp [d_def]

theorem d_congr {u v : E n → ℝ} {x : E n} (h : u =ᶠ[𝓝 x] v) : d u x = d v x := by
  ext j
  simp [d_def, h.fderiv_eq]

theorem d_add {u v : E n → ℝ} {x : E n} (hu : DifferentiableAt ℝ u x)
    (hv : DifferentiableAt ℝ v x) (j : Fin (n + 1)) :
    d (fun y => u y + v y) x j = d u x j + d v x j := by
  simp [d_def, fderiv_fun_add hu hv]

theorem d_mul {u v : E n → ℝ} {x : E n} (hu : DifferentiableAt ℝ u x)
    (hv : DifferentiableAt ℝ v x) (j : Fin (n + 1)) :
    d (fun y => u y * v y) x j = d u x j * v x + u x * d v x j := by
  simp [d_def, fderiv_fun_mul hu hv]
  ring

theorem d_sub {u v : E n → ℝ} {x : E n} (hu : DifferentiableAt ℝ u x)
    (hv : DifferentiableAt ℝ v x) (j : Fin (n + 1)) :
    d (fun y => u y - v y) x j = d u x j - d v x j := by
  simp [d_def, fderiv_fun_sub hu hv]

theorem d_neg {u : E n → ℝ} {x : E n} (j : Fin (n + 1)) :
    d (fun y => -u y) x j = -d u x j := by
  simp [d_def, fderiv_fun_neg]

theorem d_const_mul {u : E n → ℝ} {x : E n} (hu : DifferentiableAt ℝ u x) (c : ℝ)
    (j : Fin (n + 1)) : d (fun y => c * u y) x j = c * d u x j := by
  simp [d_def, fderiv_const_mul hu]

theorem d_sum {ι : Type*} {s : Finset ι} {u : ι → E n → ℝ} {x : E n}
    (hu : ∀ i ∈ s, DifferentiableAt ℝ (u i) x) (j : Fin (n + 1)) :
    d (fun y => ∑ i ∈ s, u i y) x j = ∑ i ∈ s, d (u i) x j := by
  simp [d_def, fderiv_fun_sum hu]

/-- The chain rule for a function of one variable applied to `u`. -/
theorem d_comp_of_hasDerivAt {u : E n → ℝ} {x : E n} {φ : ℝ → ℝ} {φ' : ℝ}
    (hφ : HasDerivAt φ φ' (u x)) (hu : DifferentiableAt ℝ u x) (j : Fin (n + 1)) :
    d (fun y => φ (u y)) x j = φ' * d u x j := by
  have := (hφ.comp_hasFDerivAt x hu.hasFDerivAt).fderiv
  simp [d_def, show (fun y => φ (u y)) = φ ∘ u from rfl, this]

theorem d_exp {u : E n → ℝ} {x : E n} (hu : DifferentiableAt ℝ u x) (j : Fin (n + 1)) :
    d (fun y => Real.exp (u y)) x j = Real.exp (u x) * d u x j :=
  d_comp_of_hasDerivAt (Real.hasDerivAt_exp _) hu j

theorem d_sq {u : E n → ℝ} {x : E n} (hu : DifferentiableAt ℝ u x) (j : Fin (n + 1)) :
    d (fun y => u y ^ 2) x j = 2 * u x * d u x j := by
  rw [d_comp_of_hasDerivAt (hasDerivAt_pow 2 (u x)) hu j]
  ring

theorem d_eq_zero_of_fderiv {u : E n → ℝ} {x : E n} (h : fderiv ℝ u x = 0) : d u x = 0 := by
  ext i; simp [d_def, h]

/-- Partial derivatives in `x` of a function of `(s, x)`. -/
theorem d_param_eq {U : ℝ → E n → ℝ} {s : ℝ} {z : E n}
    (hU : DifferentiableAt ℝ (fun p : ℝ × E n => U p.1 p.2) (s, z)) (k : Fin (n + 1)) :
    d (U s) z k = fderiv ℝ (fun p : ℝ × E n => U p.1 p.2) (s, z) (0, EuclideanSpace.single k 1) := by
  have hi : HasFDerivAt (fun y : E n => ((s, y) : ℝ × E n))
      (ContinuousLinearMap.inr ℝ ℝ (E n)) z :=
    (hasFDerivAt_const s z).prodMk (hasFDerivAt_id z)
  have := (hU.hasFDerivAt.comp z hi).fderiv
  simp only [d_def]
  rw [show U s = (fun p : ℝ × E n => U p.1 p.2) ∘ fun y : E n => ((s, y) : ℝ × E n) from rfl,
    this]
  rfl

/-- The chain rule in coordinates: `∂ⱼ(v ∘ Ψ) = (∂_α v) ∘ Ψ · ∂ⱼΨ^α`. -/
theorem d_comp {v : E n → ℝ} {Ψ : E n → E n} {x : E n} (hv : DifferentiableAt ℝ v (Ψ x))
    (hΨ : DifferentiableAt ℝ Ψ x) (j : Fin (n + 1)) :
    d (fun y => v (Ψ y)) x j = ∑ α, d v (Ψ x) α * d (fun y => Ψ y α) x j := by
  have : d (fun y => v (Ψ y)) x j = fderiv ℝ v (Ψ x) (fderiv ℝ Ψ x (EuclideanSpace.single j 1)) :=
    (d_def _ _ _).trans (congrArg (· (EuclideanSpace.single j 1)) (fderiv_comp x hv hΨ))
  rw [this, fderiv_apply_eq_sum_d]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [d_coord_comp hΨ, mul_comm, D_def]

theorem contDiffAt_d {m : ℕ∞ω} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ (m + 1) u x) (k : Fin (n + 1)) :
    ContDiffAt ℝ m (fun y => d u y k) x := by
  simp only [d_def]
  exact (hu.fderiv_right le_rfl).clm_apply contDiffAt_const

theorem differentiableAt_d {u : E n → ℝ} {x : E n} (hu : ContDiffAt ℝ 2 u x)
    (k : Fin (n + 1)) : DifferentiableAt ℝ (fun y => d u y k) x :=
  (contDiffAt_d (m := 1) hu k).differentiableAt one_ne_zero

theorem contDiff_d {u : E n → ℝ} (hu : ContDiff ℝ ∞ u) (i : Fin (n + 1)) :
    ContDiff ℝ ∞ fun x => d u x i := by
  simp only [d_def]
  exact (contDiff_infty_iff_fderiv.1 hu).2.clm_apply contDiff_const

theorem contDiffOn_d_of_le {m k : ℕ∞ω} {V : Set (E n)} (hV : IsOpen V) {u : E n → ℝ}
    (hu : ContDiffOn ℝ k u V) (hmk : m + 1 ≤ k) (i : Fin (n + 1)) :
    ContDiffOn ℝ m (fun y => d u y i) V := by
  simp only [d_def]
  exact (hu.fderiv_of_isOpen hV hmk).clm_apply contDiffOn_const

theorem contDiffOn_d {V : Set (E n)} (hV : IsOpen V) {u : E n → ℝ} (hu : ContDiffOn ℝ ∞ u V)
    (i : Fin (n + 1)) : ContDiffOn ℝ ∞ (fun y => d u y i) V :=
  contDiffOn_d_of_le hV hu (by simp) i

theorem continuousOn_d_of_contDiffOn {V : Set (E n)} (hV : IsOpen V) {u : E n → ℝ}
    (hu : ContDiffOn ℝ 1 u V) (i : Fin (n + 1)) : ContinuousOn (fun y => d u y i) V :=
  (contDiffOn_d_of_le (m := 0) hV hu (by simp) i).continuousOn

theorem continuousOn_d {V : Set (E n)} (hV : IsOpen V) {u : E n → ℝ}
    (hu : ContDiffOn ℝ 1 u V) : ContinuousOn (d u) V :=
  continuousOn_pi.2 fun i => continuousOn_d_of_contDiffOn hV hu i

theorem contDiff_coordinate (k : Fin (n + 1)) : ContDiff ℝ ∞ fun y : E n => y k :=
  (EuclideanSpace.proj k : E n →L[ℝ] ℝ).contDiff

theorem D_id (x : E n) : D id x = 1 := by
  ext i j
  simp [D_def, fderiv_id, Matrix.one_apply]

theorem contDiffAt_coord {m : ℕ∞ω} {Ψ : E n → E n} {x : E n}
    (hΨ : ContDiffAt ℝ m Ψ x) (α : Fin (n + 1)) : ContDiffAt ℝ m (fun y => Ψ y α) x :=
  contDiffAt_euclidean.mp hΨ α

theorem d2_eq_fderiv_fderiv {u : E n → ℝ} {x : E n}
    (hu : DifferentiableAt ℝ (fderiv ℝ u) x) (i j : Fin (n + 1)) :
    d2 u x i j =
      fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  simp only [d2, d_def]
  rw [fderiv_clm_apply hu (differentiableAt_const _)]
  simp

/-- Second derivatives commute. -/
theorem d2_comm {u : E n → ℝ} {x : E n} (hu : ContDiffAt ℝ 2 u x) (i j : Fin (n + 1)) :
    d2 u x i j = d2 u x j i := by
  have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [d2_eq_fderiv_fderiv hd, d2_eq_fderiv_fderiv hd]
  exact hu.isSymmSndFDerivAt (by simp) _ _

theorem d2_coord (x : E n) (k i j : Fin (n + 1)) : d2 (fun y : E n => y k) x i j = 0 := by
  simp only [d2, d_coord, d_const]

end

end LorentzianCalderon
