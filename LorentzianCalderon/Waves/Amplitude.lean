module

public import LorentzianCalderon.Waves.Calculus
public import LorentzianCalderon.Facts.Borel

public section

/-!
# Amplitudes from the transport hierarchy

For solutions `b_k` of the transport hierarchy `2 Z b_{k+1} + b_{k+1} □φ = -□ b_k` on an open set
`U` where `φ` is eikonal, Borel's lemma gives an amplitude `B(x, r)` with Taylor coefficients `b_k`
at `r = 0`. By the chain rule (`lem_calculus`(b)), `□ B(·, φ - s) = R(·, φ - s)` with
`R(x, r) = □_x B(x, r) + 2 Z_x ∂_r B(x, r) + (□φ)(x) ∂_r B(x, r)`, and `∂_r^k R(x, 0) =
□ b_k + 2 Z b_{k+1} + b_{k+1} □φ = 0`, so that `R_+ = R H` is smooth.
-/

namespace LorentzianCalderon

noncomputable section
open MeasureTheory Set Filter Function
open scoped ContDiff Topology Matrix

variable {n : ℕ} {g : MatrixField n}

variable (g) in
/-- The remainder `R(x, r) = □_x B(x, r) + 2 Z_x ∂_r B(x, r) + (□φ)(x) ∂_r B(x, r)` of an amplitude
`B`, with `Z = -grad φ`. -/
def amplitudeRemainder (φ : E n → ℝ) (B : E n → ℝ → ℝ) (x : E n) (r : ℝ) : ℝ :=
  box g (fun y => B y r) x + 2 * -coform g x (d φ x) (d (fun y => deriv (B y) r) x) +
    box g φ x * deriv (B x) r

theorem amplitudeRemainder_def (φ : E n → ℝ) (B : E n → ℝ → ℝ) (x : E n) (r : ℝ) :
    amplitudeRemainder g φ B x r =
      box g (fun y => B y r) x + 2 * -coform g x (d φ x) (d (fun y => deriv (B y) r) x) +
        box g φ x * deriv (B x) r := by rfl

variable {U : Set (E n)} {φ : E n → ℝ} {B : E n → ℝ → ℝ}

theorem hasFDerivAt_uncurry (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ (fun q : E n × ℝ => B q.1 q.2) (U ×ˢ univ)) {x : E n} (hx : x ∈ U)
    (r : ℝ) : HasFDerivAt (fun q : E n × ℝ => B q.1 q.2)
      (fderiv ℝ (fun q : E n × ℝ => B q.1 q.2) (x, r)) (x, r) :=
  ((hB.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hx, mem_univ _⟩)).differentiableAt
    (by simp)).hasFDerivAt

/-- The partial derivatives of `B` are those of the uncurried function. -/
theorem hasFDerivAt_slice (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ (fun q : E n × ℝ => B q.1 q.2) (U ×ˢ univ)) {x : E n} (hx : x ∈ U)
    (r : ℝ) : HasFDerivAt (fun y => B y r)
      ((fderiv ℝ (fun q : E n × ℝ => B q.1 q.2) (x, r)).comp
        (ContinuousLinearMap.inl ℝ (E n) ℝ)) x := by
  have hi : HasFDerivAt (fun y : E n => (y, r)) (ContinuousLinearMap.inl ℝ (E n) ℝ) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const r x)
  exact (hasFDerivAt_uncurry hU hB hx r).comp x hi

theorem hasDerivAt_slice (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ (fun q : E n × ℝ => B q.1 q.2) (U ×ˢ univ)) {x : E n} (hx : x ∈ U)
    (r : ℝ) : HasDerivAt (B x) (fderiv ℝ (fun q : E n × ℝ => B q.1 q.2) (x, r) (0, 1)) r := by
  have h1 : HasDerivAt (fun r : ℝ => (x, r)) ((0, 1) : E n × ℝ) r :=
    (hasDerivAt_const r x).prodMk (hasDerivAt_id r)
  exact (hasFDerivAt_uncurry hU hB hx r).comp_hasDerivAt r h1

/-- The first-order chain rule for `B(y, φ(y) - s)`. -/
theorem d_comp_sub (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ (fun q : E n × ℝ => B q.1 q.2) (U ×ˢ univ)) {x : E n} (hx : x ∈ U)
    (hφ : DifferentiableAt ℝ φ x) (s : ℝ) (k : Fin (n + 1)) :
    d (fun y => B y (φ y - s)) x k =
      d (fun y => B y (φ x - s)) x k + deriv (B x) (φ x - s) * d φ x k := by
  set L := fderiv ℝ (fun q : E n × ℝ => B q.1 q.2) (x, φ x - s)
  have hpath : HasFDerivAt (fun y => (y, φ y - s))
      ((ContinuousLinearMap.id ℝ (E n)).prod (fderiv ℝ φ x)) x :=
    (hasFDerivAt_id x).prodMk (hφ.hasFDerivAt.sub_const s)
  have hcomp : HasFDerivAt (fun y => B y (φ y - s))
      (L.comp ((ContinuousLinearMap.id ℝ (E n)).prod (fderiv ℝ φ x))) x := by
    have := (hasFDerivAt_uncurry hU hB hx (φ x - s)).comp x hpath
    exact this
  simp only [d_def]
  rw [hcomp.fderiv, (hasFDerivAt_slice hU hB hx (φ x - s)).fderiv,
    (hasDerivAt_slice hU hB hx (φ x - s)).deriv]
  set v := EuclideanSpace.single k (1 : ℝ)
  have : ((v, fderiv ℝ φ x v) : E n × ℝ) = (v, 0) + fderiv ℝ φ x v • ((0, 1) : E n × ℝ) := by
    simp
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.inl_apply]
  rw [this, map_add, map_smul, smul_eq_mul, mul_comm]

/-- The chain rule for the transport term: `Z B(·, φ - s) = (Z_x B)(·, φ - s)`, since
`Zφ = -g(dφ, dφ) = 0`. -/
theorem coform_d_comp_sub (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ (fun q : E n × ℝ => B q.1 q.2) (U ×ˢ univ)) (hφ : ContDiffOn ℝ ∞ φ U)
    (heik : ∀ x ∈ U, coform g x (d φ x) (d φ x) = 0) (s : ℝ) {x : E n} (hx : x ∈ U) :
    coform g x (d φ x) (d (fun y => B y (φ y - s)) x) =
      coform g x (d φ x) (d (fun y => B y (φ x - s)) x) := by
  have hφd : DifferentiableAt ℝ φ x :=
    (hφ.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have h := heik x hx
  simp only [coform_def] at h ⊢
  simp only [d_comp_sub hU hB hx hφd s, mul_add, Finset.sum_add_distrib]
  have : ∑ j, ∑ k, (g x)⁻¹ j k * d φ x j * (deriv (B x) (φ x - s) * d φ x k) =
      deriv (B x) (φ x - s) * ∑ j, ∑ k, (g x)⁻¹ j k * d φ x j * d φ x k := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  rw [this, h, mul_zero, add_zero]

/-! ### Partial derivatives of families -/

section Families

/-- `B : E n → ℝ → ℝ` is smooth as a function of `(x, r)` on `U × ℝ`. -/
def SmoothFamily (U : Set (E n)) (B : E n → ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ (fun q : E n × ℝ => B q.1 q.2) (U ×ˢ univ)

theorem smoothFamily_iff {U : Set (E n)} {B : E n → ℝ → ℝ} :
    SmoothFamily U B ↔
      ContDiffOn ℝ ∞ (fun q : E n × ℝ => B q.1 q.2) (U ×ˢ univ) := Iff.rfl

/-- The partial derivative `∂_r B`. -/
def rDeriv (B : E n → ℝ → ℝ) : E n → ℝ → ℝ := fun y r => deriv (B y) r

theorem rDeriv_def (B : E n → ℝ → ℝ) :
    rDeriv B =
      fun y r => deriv (B y) r := by rfl

/-- The partial derivative `∂_j B` in `x`. -/
def xDeriv (B : E n → ℝ → ℝ) (j : Fin (n + 1)) : E n → ℝ → ℝ := fun y r => d (fun z => B z r) y j

variable {U : Set (E n)} {B : E n → ℝ → ℝ}

theorem rDeriv_eq (hU : IsOpen U) (hB : SmoothFamily U B) {x : E n} (hx : x ∈ U) (r : ℝ) :
    rDeriv B x r = fderiv ℝ (fun q : E n × ℝ => B q.1 q.2) (x, r) (0, 1) :=
  (hasDerivAt_slice hU hB hx r).deriv

theorem xDeriv_eq (hU : IsOpen U) (hB : SmoothFamily U B) {x : E n} (hx : x ∈ U) (r : ℝ)
    (j : Fin (n + 1)) :
    xDeriv B j x r =
      fderiv ℝ (fun q : E n × ℝ => B q.1 q.2) (x, r) (EuclideanSpace.single j 1, 0) := by
  simp only [xDeriv, d_def, (hasFDerivAt_slice hU hB hx r).fderiv]
  rfl

theorem SmoothFamily.fderiv_apply (hU : IsOpen U) (hB : SmoothFamily U B) (v : E n × ℝ) :
    ContDiffOn ℝ ∞ (fun q : E n × ℝ => fderiv ℝ (fun q : E n × ℝ => B q.1 q.2) q v)
      (U ×ˢ univ) :=
  (hB.fderiv_of_isOpen (hU.prod isOpen_univ) (by simp)).clm_apply contDiffOn_const

theorem SmoothFamily.rDeriv_family (hU : IsOpen U) (hB : SmoothFamily U B) :
    SmoothFamily U (rDeriv B) :=
  (hB.fderiv_apply hU (0, 1)).congr fun q hq => rDeriv_eq hU hB hq.1 q.2

theorem SmoothFamily.xDeriv_family (hU : IsOpen U) (hB : SmoothFamily U B) (j : Fin (n + 1)) :
    SmoothFamily U (xDeriv B j) :=
  (hB.fderiv_apply hU (EuclideanSpace.single j 1, 0)).congr fun q hq => xDeriv_eq hU hB hq.1 q.2 j

theorem SmoothFamily.slice (hB : SmoothFamily U B) {x : E n} (hx : x ∈ U) :
    ContDiff ℝ ∞ (B x) :=
  contDiffOn_univ.1 (hB.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    fun r _ => ⟨hx, mem_univ r⟩)

theorem SmoothFamily.contDiffAt_slice_x (hU : IsOpen U) (hB : SmoothFamily U B) {x : E n}
    (hx : x ∈ U) (r : ℝ) : ContDiffAt ℝ ∞ (fun y => B y r) x :=
  (hB.comp (contDiff_id.prodMk contDiff_const).contDiffOn
    fun _ hy => ⟨hy, mem_univ r⟩).contDiffAt (hU.mem_nhds hx)

/-- Derivatives in `x` and `r` commute. -/
theorem xDeriv_rDeriv (hU : IsOpen U) (hB : SmoothFamily U B) {x : E n} (hx : x ∈ U) (r : ℝ)
    (j : Fin (n + 1)) : xDeriv (rDeriv B) j x r = rDeriv (xDeriv B j) x r := by
  set Bh := fun q : E n × ℝ => B q.1 q.2
  have hW : IsOpen (U ×ˢ (univ : Set ℝ)) := hU.prod isOpen_univ
  have hxr : (x, r) ∈ U ×ˢ (univ : Set ℝ) := ⟨hx, mem_univ r⟩
  have hD : ContDiffAt ℝ ∞ (fderiv ℝ Bh) (x, r) :=
    (hB.fderiv_of_isOpen hW (by simp)).contDiffAt (hW.mem_nhds hxr)
  have hDd : DifferentiableAt ℝ (fderiv ℝ Bh) (x, r) := hD.differentiableAt (by simp)
  have hsym := (hB.contDiffAt (hW.mem_nhds hxr)).isSymmSndFDerivAt (n := ∞) (by simp)
  have h1 : xDeriv (rDeriv B) j x r =
      fderiv ℝ (fderiv ℝ Bh) (x, r) (EuclideanSpace.single j 1, 0) (0, 1) := by
    rw [xDeriv_eq hU (hB.rDeriv_family hU) hx r j]
    have hev : (fun q : E n × ℝ => rDeriv B q.1 q.2) =ᶠ[𝓝 (x, r)]
        fun q => fderiv ℝ Bh q (0, 1) := by
      filter_upwards [hW.mem_nhds hxr] with q hq
      exact rDeriv_eq hU hB hq.1 q.2
    rw [hev.fderiv_eq, fderiv_clm_apply hDd (differentiableAt_const _)]
    simp
  have h2 : rDeriv (xDeriv B j) x r =
      fderiv ℝ (fderiv ℝ Bh) (x, r) (0, 1) (EuclideanSpace.single j 1, 0) := by
    rw [rDeriv_eq hU (hB.xDeriv_family hU j) hx r]
    have hev : (fun q : E n × ℝ => xDeriv B j q.1 q.2) =ᶠ[𝓝 (x, r)]
        fun q => fderiv ℝ Bh q (EuclideanSpace.single j 1, 0) := by
      filter_upwards [hW.mem_nhds hxr] with q hq
      exact xDeriv_eq hU hB hq.1 q.2 j
    rw [hev.fderiv_eq, fderiv_clm_apply hDd (differentiableAt_const _)]
    simp
  rw [h1, h2, hsym]

theorem SmoothFamily.hasDerivAt (hB : SmoothFamily U B) {x : E n} (hx : x ∈ U) (r : ℝ) :
    HasDerivAt (B x) (rDeriv B x r) r :=
  ((hB.slice hx).differentiable (by simp) r).hasDerivAt

theorem xDeriv_congr {F G : E n → ℝ → ℝ} (hU : IsOpen U) (h : ∀ z ∈ U, ∀ r, F z r = G z r)
    {x : E n} (hx : x ∈ U) (r : ℝ) (j : Fin (n + 1)) : xDeriv F j x r = xDeriv G j x r := by
  simp only [xDeriv]
  rw [d_congr (eventually_of_mem (hU.mem_nhds hx) fun z hz => h z hz r)]

theorem rDeriv_xDeriv_xDeriv (hU : IsOpen U) (hB : SmoothFamily U B) {x : E n} (hx : x ∈ U) (r : ℝ)
    (j k : Fin (n + 1)) :
    rDeriv (xDeriv (xDeriv B k) j) x r = xDeriv (xDeriv (rDeriv B) k) j x r := by
  rw [← xDeriv_rDeriv hU (hB.xDeriv_family hU k) hx r j]
  exact xDeriv_congr hU (fun z hz r => (xDeriv_rDeriv hU hB hz r k).symm) hx r j

variable (g) in
/-- The wave operator in `x`, `□_x B(·, r)`. -/
def boxx (B : E n → ℝ → ℝ) : E n → ℝ → ℝ := fun y r => box g (fun z => B z r) y

variable (hg : ∀ i j, ContDiff ℝ ∞ fun x => g x i j) (hdet : ∀ x, (g x).det ≠ 0)
include hg hdet

theorem boxx_eq (hU : IsOpen U) (hB : SmoothFamily U B) {x : E n} (hx : x ∈ U) (r : ℝ) :
    boxx g B x r = -∑ j, ∑ k, (g x)⁻¹ j k * xDeriv (xDeriv B k) j x r +
      ∑ k, box g (fun y => y k) x * xDeriv B k x r := by
  have h := box_eq (fun i j => (hg i j).differentiable (by simp) x) (hdet x)
    ((hB.contDiffAt_slice_x hU hx r).of_le (by simp))
  simp only [d2_def] at h
  exact h

theorem SmoothFamily.boxx_family (hU : IsOpen U) (hB : SmoothFamily U B) :
    SmoothFamily U (boxx g B) := by
  refine ContDiffOn.congr ?_ fun q hq => boxx_eq hg hdet hU hB hq.1 q.2
  refine (ContDiffOn.sum fun j _ => ContDiffOn.sum fun k _ => ?_).neg.add
    (ContDiffOn.sum fun k _ => ?_)
  · exact ((contDiff_inv_apply hg hdet j k).comp contDiff_fst).contDiffOn.mul
      ((hB.xDeriv_family hU k).xDeriv_family hU j)
  · exact ((contDiff_box hg hdet (contDiff_coordinate k)).comp contDiff_fst).contDiffOn.mul
      (hB.xDeriv_family hU k)

theorem rDeriv_boxx (hU : IsOpen U) (hB : SmoothFamily U B) {x : E n} (hx : x ∈ U) (r : ℝ) :
    rDeriv (boxx g B) x r = boxx g (rDeriv B) x r := by
  have hfun : boxx g B x = fun r => -∑ j, ∑ k, (g x)⁻¹ j k * xDeriv (xDeriv B k) j x r +
      ∑ k, box g (fun y => y k) x * xDeriv B k x r := funext fun r => boxx_eq hg hdet hU hB hx r
  have hder : HasDerivAt (boxx g B x) (-∑ j, ∑ k, (g x)⁻¹ j k * rDeriv (xDeriv (xDeriv B k) j) x r +
      ∑ k, box g (fun y => y k) x * rDeriv (xDeriv B k) x r) r := by
    rw [hfun]
    refine (HasDerivAt.fun_sum fun j _ => HasDerivAt.fun_sum fun k _ => ?_).neg.add
      (HasDerivAt.fun_sum fun k _ => ?_)
    · exact (((hB.xDeriv_family hU k).xDeriv_family hU j).hasDerivAt hx r).const_mul _
    · exact ((hB.xDeriv_family hU k).hasDerivAt hx r).const_mul _
  rw [rDeriv, hder.deriv, boxx_eq hg hdet hU (hB.rDeriv_family hU) hx r]
  simp only [rDeriv_xDeriv_xDeriv hU hB hx r, xDeriv_rDeriv hU hB hx r]

end Families

section Remainder

variable (hg : ∀ i j, ContDiff ℝ ∞ fun x => g x i j) (hdet : ∀ x, (g x).det ≠ 0)
include hg hdet

omit hg hdet in
theorem amplitudeRemainder_eq (B : E n → ℝ → ℝ) (x : E n) (r : ℝ) :
    amplitudeRemainder g φ B x r = boxx g B x r +
      2 * -∑ j, ∑ k, (g x)⁻¹ j k * d φ x j * xDeriv (rDeriv B) k x r +
        box g φ x * rDeriv B x r := by
  rw [amplitudeRemainder_def, coform_def]
  rfl

theorem rDeriv_amplitudeRemainder (hU : IsOpen U) (hB : SmoothFamily U B) {x : E n} (hx : x ∈ U)
    (r : ℝ) : rDeriv (amplitudeRemainder g φ B) x r = amplitudeRemainder g φ (rDeriv B) x r := by
  have hder : HasDerivAt (amplitudeRemainder g φ B x) (rDeriv (boxx g B) x r +
      2 * -∑ j, ∑ k, (g x)⁻¹ j k * d φ x j * rDeriv (xDeriv (rDeriv B) k) x r +
        box g φ x * rDeriv (rDeriv B) x r) r := by
    have hfun : amplitudeRemainder g φ B x = fun r => boxx g B x r +
        2 * -∑ j, ∑ k, (g x)⁻¹ j k * d φ x j * xDeriv (rDeriv B) k x r + box g φ x * rDeriv B x r :=
      funext fun r => amplitudeRemainder_eq B x r
    rw [hfun]
    have h1 := (hB.boxx_family hg hdet hU).hasDerivAt hx r
    refine (h1.add ((HasDerivAt.fun_sum fun j _ => HasDerivAt.fun_sum fun k _ => ?_).neg.const_mul
      2)).add (((hB.rDeriv_family hU).hasDerivAt hx r).const_mul _)
    exact (((hB.rDeriv_family hU).xDeriv_family hU k).hasDerivAt hx r).const_mul _
  rw [rDeriv, hder.deriv, rDeriv_boxx hg hdet hU hB hx r, amplitudeRemainder_eq]
  simp only [← xDeriv_rDeriv hU (hB.rDeriv_family hU) hx r]

theorem SmoothFamily.remainder (hU : IsOpen U) (hB : SmoothFamily U B)
    (hφ : ContDiffOn ℝ ∞ φ U) : SmoothFamily U (amplitudeRemainder g φ B) := by
  have hsnd : MapsTo (fun q : E n × ℝ => q.1) (U ×ˢ univ) U := fun q hq => hq.1
  rw [show amplitudeRemainder g φ B = _ from funext₂ fun x r => amplitudeRemainder_eq B x r]
  refine ((hB.boxx_family hg hdet hU).add (contDiffOn_const.mul (ContDiffOn.neg
    (ContDiffOn.sum fun j _ => ContDiffOn.sum fun k _ => ?_)))).add ?_
  · exact ((((contDiff_inv_apply hg hdet j k).comp contDiff_fst).contDiffOn.mul
      ((contDiffOn_d hU hφ j).comp contDiff_fst.contDiffOn hsnd)).mul
      ((hB.rDeriv_family hU).xDeriv_family hU k))
  · exact ((contDiffOn_box hg hdet hU hφ).comp contDiff_fst.contDiffOn hsnd).mul
      (hB.rDeriv_family hU)

omit hg hdet in
/-- The `r`-derivatives of the family `B`. -/
theorem iteratedDeriv_family (hU : IsOpen U) (hB : SmoothFamily U B) (k : ℕ) :
    SmoothFamily U (fun y r => iteratedDeriv k (B y) r) := by
  induction k with
  | zero => simpa using hB
  | succ k ih =>
    refine (ih.rDeriv_family hU).congr fun q _ => ?_
    simp [rDeriv, iteratedDeriv_succ]

theorem iteratedDeriv_amplitudeRemainder_eq (hU : IsOpen U) (hB : SmoothFamily U B) (k : ℕ)
    {x : E n} (hx : x ∈ U) :
    iteratedDeriv k (amplitudeRemainder g φ B x) =
      amplitudeRemainder g φ (fun y r => iteratedDeriv k (B y) r) x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext r
    have := rDeriv_amplitudeRemainder (φ := φ) hg hdet hU (iteratedDeriv_family hU hB k) hx r
    simp only [rDeriv] at this
    rw [this]
    congr 1
    funext y r
    rw [iteratedDeriv_succ]
    rfl

end Remainder

theorem box_comp_sub_algebra {ι : Type*} [Fintype ι] (G P H : ι → ι → ℝ)
    (hG : ∀ i j, G i j = G j i) (a q c f : ι → ℝ) (p t : ℝ) :
    -∑ j, ∑ k, G j k * (P j k + q k * f j + ((q j + t * f j) * f k + p * H j k)) +
        ∑ k, c k * (a k + p * f k) =
      (-∑ j, ∑ k, G j k * P j k + ∑ k, c k * a k) + 2 * -∑ j, ∑ k, G j k * f j * q k +
        (-∑ j, ∑ k, G j k * H j k + ∑ k, c k * f k) * p - t * ∑ j, ∑ k, G j k * f j * f k := by
  have hc : ∑ j, ∑ k, G j k * (q j * f k) = ∑ j, ∑ k, G j k * f j * q k := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hG k j]
    ring
  have e1 : ∑ j, ∑ k, G j k * (P j k + q k * f j + ((q j + t * f j) * f k + p * H j k)) =
      ∑ j, ∑ k, G j k * P j k + ∑ j, ∑ k, G j k * f j * q k +
        ∑ j, ∑ k, G j k * (q j * f k) + t * ∑ j, ∑ k, G j k * f j * f k +
        p * ∑ j, ∑ k, G j k * H j k := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have e2 : ∑ k, c k * (a k + p * f k) = ∑ k, c k * a k + p * ∑ k, c k * f k := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e1, e2, hc]
  ring

/-- **The chain rule for the wave operator**:
`□ B(·, φ - s) = R(·, φ - s) - g(dφ, dφ) ∂_r² B(·, φ - s)`. -/
theorem box_comp_sub_eq_sub (hg : ∀ i j, ContDiff ℝ ∞ fun x => g x i j)
    (hsymm : ∀ x, (g x)ᵀ = g x) (hdet : ∀ x, (g x).det ≠ 0) (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ (fun q : E n × ℝ => B q.1 q.2) (U ×ˢ univ)) (hφ : ContDiffOn ℝ ∞ φ U)
    (s : ℝ) {x : E n} (hx : x ∈ U) :
    box g (fun y => B y (φ y - s)) x = amplitudeRemainder g φ B x (φ x - s) -
      rDeriv (rDeriv B) x (φ x - s) * coform g x (d φ x) (d φ x) := by
  have hBf : SmoothFamily U B := hB
  have hφa : ∀ y ∈ U, ContDiffAt ℝ ∞ φ y := fun y hy => hφ.contDiffAt (hU.mem_nhds hy)
  have hφd : ∀ y ∈ U, DifferentiableAt ℝ φ y := fun y hy => (hφa y hy).differentiableAt (by simp)
  have hcomp : ∀ {F : E n → ℝ → ℝ}, SmoothFamily U F → ∀ y ∈ U,
      ContDiffAt ℝ ∞ (fun z => F z (φ z - s)) y := fun {F} hF y hy => by
    have h1 : ContDiffAt ℝ ∞ (fun q : E n × ℝ => F q.1 q.2) (y, φ y - s) :=
      hF.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hy, mem_univ _⟩)
    exact h1.comp (f := fun z => (z, φ z - s)) y
      (contDiffAt_id.prodMk ((hφa y hy).sub contDiffAt_const))
  have hdiff : ∀ {F : E n → ℝ → ℝ}, SmoothFamily U F → ∀ y ∈ U,
      DifferentiableAt ℝ (fun z => F z (φ z - s)) y := fun hF y hy =>
    (hcomp hF y hy).differentiableAt (by simp)
  have hdu : ∀ y ∈ U, ∀ k, d (fun z => B z (φ z - s)) y k =
      xDeriv B k y (φ y - s) + rDeriv B y (φ y - s) * d φ y k := fun y hy k =>
    d_comp_sub hU hB hy (hφd y hy) s k
  have hdF : ∀ {F : E n → ℝ → ℝ}, SmoothFamily U F → ∀ j, d (fun z => F z (φ z - s)) x j =
      xDeriv F j x (φ x - s) + rDeriv F x (φ x - s) * d φ x j := fun hF j =>
    d_comp_sub hU hF hx (hφd x hx) s j
  have hd2 : ∀ j k, d2 (fun z => B z (φ z - s)) x j k =
      xDeriv (xDeriv B k) j x (φ x - s) + xDeriv (rDeriv B) k x (φ x - s) * d φ x j +
        ((xDeriv (rDeriv B) j x (φ x - s) + rDeriv (rDeriv B) x (φ x - s) * d φ x j) * d φ x k +
          rDeriv B x (φ x - s) * d2 φ x j k) := by
    intro j k
    have hev : (fun y => d (fun z => B z (φ z - s)) y k) =ᶠ[𝓝 x]
        fun y => xDeriv B k y (φ y - s) + rDeriv B y (φ y - s) * d φ y k :=
      eventually_of_mem (hU.mem_nhds hx) fun y hy => hdu y hy k
    have hdφk := differentiableAt_d ((hφa x hx).of_le (by simp)) k
    have h2 : DifferentiableAt ℝ (fun y => rDeriv B y (φ y - s) * d φ y k) x :=
      (hdiff (hBf.rDeriv_family hU) x hx).mul hdφk
    rw [d2_def, d_congr hev, d_add (u := fun y => xDeriv B k y (φ y - s))
      (v := fun y => rDeriv B y (φ y - s) * d φ y k) (hdiff (hBf.xDeriv_family hU k) x hx) h2,
      d_mul (u := fun y => rDeriv B y (φ y - s)) (hdiff (hBf.rDeriv_family hU) x hx) hdφk,
      hdF (hBf.xDeriv_family hU k), hdF (hBf.rDeriv_family hU), ← xDeriv_rDeriv hU hBf hx]
    rw [d2_def]
  have hgd : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x := fun i j =>
    (hg i j).differentiable (by simp) x
  have hG : ∀ i j, (g x)⁻¹ i j = (g x)⁻¹ j i := fun i j => by
    rw [← Matrix.transpose_apply (g x)⁻¹, Matrix.transpose_nonsing_inv, hsymm]
  rw [box_eq hgd (hdet x) ((hcomp hBf x hx).of_le (by simp))]
  simp only [hd2, hdu x hx]
  rw [box_comp_sub_algebra _ _ _ hG, amplitudeRemainder_eq,
    boxx_eq hg hdet hU hBf hx, box_eq hgd (hdet x) ((hφa x hx).of_le (by simp))]
  rw [coform_def]

/-- **The chain rule for the wave operator** (`lem_calculus`(b)): for an eikonal `φ`,
`□ B(·, φ - s) = R(·, φ - s)`. -/
theorem box_comp_sub_eq (hg : ∀ i j, ContDiff ℝ ∞ fun x => g x i j)
    (hsymm : ∀ x, (g x)ᵀ = g x) (hdet : ∀ x, (g x).det ≠ 0) (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ (fun q : E n × ℝ => B q.1 q.2) (U ×ˢ univ)) (hφ : ContDiffOn ℝ ∞ φ U)
    (heik : ∀ x ∈ U, coform g x (d φ x) (d φ x) = 0) (s : ℝ) {x : E n} (hx : x ∈ U) :
    box g (fun y => B y (φ y - s)) x = amplitudeRemainder g φ B x (φ x - s) := by
  rw [box_comp_sub_eq_sub hg hsymm hdet hU hB hφ s hx, heik x hx, mul_zero, sub_zero]

/-- The remainder of a smooth amplitude is smooth. -/
theorem contDiffOn_amplitudeRemainder (hg : ∀ i j, ContDiff ℝ ∞ fun x => g x i j)
    (hdet : ∀ x, (g x).det ≠ 0) (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ (fun q : E n × ℝ => B q.1 q.2) (U ×ˢ univ)) (hφ : ContDiffOn ℝ ∞ φ U) :
    ContDiffOn ℝ ∞ (fun q : E n × ℝ => amplitudeRemainder g φ B q.1 q.2) (U ×ˢ univ) :=
  SmoothFamily.remainder hg hdet hU hB hφ

/-- The Taylor coefficients of the remainder at `r = 0`:
`∂_r^k R(x, 0) = □ b_k + 2 Z b_{k+1} + (□φ) b_{k+1}` when `∂_r^k B(·, 0) = b_k`. -/
theorem iteratedDeriv_amplitudeRemainder (hg : ∀ i j, ContDiff ℝ ∞ fun x => g x i j)
    (hdet : ∀ x, (g x).det ≠ 0) (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ (fun q : E n × ℝ => B q.1 q.2) (U ×ˢ univ))
    {b : ℕ → E n → ℝ} (hBb : ∀ k, ∀ x ∈ U, iteratedDeriv k (B x) 0 = b k x) (k : ℕ)
    {x : E n} (hx : x ∈ U) :
    iteratedDeriv k (amplitudeRemainder g φ B x) 0 =
      box g (b k) x + 2 * -coform g x (d φ x) (d (b (k + 1)) x) + box g φ x * b (k + 1) x := by
  have hk : ∀ z ∈ U, iteratedDeriv k (B z) 0 = b k z := hBb k
  have hk1 : ∀ z ∈ U, rDeriv (fun y r => iteratedDeriv k (B y) r) z 0 = b (k + 1) z :=
      fun z hz => by
    rw [← hBb (k + 1) z hz, iteratedDeriv_succ]
    rfl
  rw [iteratedDeriv_amplitudeRemainder_eq hg hdet hU hB k hx, amplitudeRemainder_eq,
    hk1 x hx]
  have hbox : boxx g (fun y r => iteratedDeriv k (B y) r) x 0 = box g (b k) x :=
    box_congr (eventually_of_mem (hU.mem_nhds hx) hk)
  have hd : ∀ j, xDeriv (rDeriv fun y r => iteratedDeriv k (B y) r) j x 0 = d (b (k + 1)) x j :=
    fun j => d_congr (eventually_of_mem (hU.mem_nhds hx) hk1) ▸ rfl
  simp only [hbox, hd, coform_def]

theorem iteratedDeriv_succ_id_mul {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    iteratedDeriv (k + 1) (fun r => r * f r) 0 = (k + 1) * iteratedDeriv k f 0 := by
  have : (fun r : ℝ => r * f r) = fun r => id r * f r := rfl
  rw [this, iteratedDeriv_fun_mul contDiff_id.contDiffAt (hf.of_le (by simp)).contDiffAt,
    Finset.sum_eq_single 1]
  · simp [iteratedDeriv_id]
  · intro i _ hi
    simp [iteratedDeriv_id, hi]
  · intro h
    simp at h

/-- `r ↦ max(r, 0)^(k+1)` is of class `C^k`. -/
theorem contDiff_max_zero_pow : ∀ k : ℕ, ContDiff ℝ k fun r : ℝ => max r 0 ^ (k + 1)
  | 0 => contDiff_zero.2 ((continuous_id.max continuous_const).pow _)
  | k + 1 => by
    have hder : ∀ r : ℝ, HasDerivAt (fun r : ℝ => max r 0 ^ (k + 2))
        ((k + 2 : ℝ) * max r 0 ^ (k + 1)) r := by
      intro r
      rcases lt_trichotomy r 0 with hr | rfl | hr
      · refine (hasDerivAt_const r (0 : ℝ)).congr_of_eventuallyEq ?_ |>.congr_deriv ?_
        · filter_upwards [Iio_mem_nhds hr] with y hy
          simp [max_eq_right (le_of_lt (show y < 0 from hy))]
        · simp [max_eq_right hr.le]
      · rw [hasDerivAt_iff_isLittleO_nhds_zero]
        refine Asymptotics.IsBigO.trans_isLittleO (g := fun h : ℝ => h ^ (k + 2)) ?_
          (Asymptotics.isLittleO_pow_id (by omega))
        refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun h => ?_)
        simp only [zero_add, max_self]
        rw [zero_pow (by omega), zero_pow (by omega)]
        simp only [sub_zero, mul_zero, smul_zero, norm_pow, Real.norm_eq_abs, one_mul]
        refine pow_le_pow_left₀ (abs_nonneg _) ?_ _
        rcases le_total h 0 with h0 | h0
        · simp [max_eq_right h0]
        · simp [max_eq_left h0]
      · have hev : (fun r : ℝ => max r 0 ^ (k + 2)) =ᶠ[𝓝 r] fun y => y ^ (k + 2) := by
          filter_upwards [Ioi_mem_nhds hr] with y hy
          rw [max_eq_left (le_of_lt (show 0 < y from hy))]
        have := (hasDerivAt_pow (k + 2) r).congr_of_eventuallyEq hev
        convert this using 1
        rw [max_eq_left hr.le]
        push_cast
        ring_nf
    rw [show ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiff_succ_iff_deriv]
    refine ⟨fun r => (hder r).differentiableAt, fun h => absurd h (by simp), ?_⟩
    rw [show deriv (fun r : ℝ => max r 0 ^ (k + 1 + 1)) =
      fun r => (k + 2 : ℝ) * max r 0 ^ (k + 1) from funext fun r => (hder r).deriv]
    exact contDiff_const.mul (contDiff_max_zero_pow k)

/-- A function vanishing to infinite order at `r = 0` is `r^m` times a smooth function, for
every `m`. -/
theorem exists_eq_pow_mul_of_flat {U : Set (E n)} (hU : IsOpen U) {R : E n → ℝ → ℝ}
    (hR : ContDiffOn ℝ ∞ (fun q : E n × ℝ => R q.1 q.2) (U ×ˢ univ))
    (hflat : ∀ k, ∀ x ∈ U, iteratedDeriv k (R x) 0 = 0) (m : ℕ) :
    ∃ Q : E n → ℝ → ℝ, ContDiffOn ℝ ∞ (fun q : E n × ℝ => Q q.1 q.2) (U ×ˢ univ) ∧
      (∀ k, ∀ x ∈ U, iteratedDeriv k (Q x) 0 = 0) ∧ ∀ x ∈ U, ∀ r, R x r = r ^ m * Q x r := by
  induction m with
  | zero => exact ⟨R, hR, hflat, fun x _ r => by simp⟩
  | succ m ih =>
    obtain ⟨Q, hQ, hQflat, hRQ⟩ := ih
    have hQs : ContDiffOn ℝ ∞ (fun p : ℝ × E n => Q p.2 p.1) (univ ×ˢ U) :=
      hQ.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn fun p hp => ⟨hp.2, hp.1⟩
    obtain ⟨c, hc, hQc⟩ := exists_eq_sub_mul_of_eq_zero hU contDiffOn_const (f := fun s x => Q x s)
      hQs fun x hx => by simpa using hQflat 0 x hx
    have hc' : ContDiffOn ℝ ∞ (fun q : E n × ℝ => -c q.2 q.1) (U ×ˢ univ) :=
      (hc.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn fun q hq => ⟨hq.2, hq.1⟩).neg
    have hQx : ∀ x ∈ U, Q x = fun r => r * -c r x := fun x hx => funext fun r => by
      rw [hQc r x hx]
      ring
    have hsl : ∀ x ∈ U, ContDiff ℝ ∞ fun r => -c r x := fun x hx =>
      contDiffOn_univ.1 (hc'.comp (contDiff_const.prodMk contDiff_id).contDiffOn
        fun r _ => ⟨hx, mem_univ r⟩)
    refine ⟨fun x r => -c r x, hc', fun k x hx => ?_, fun x hx r => ?_⟩
    · have h := hQflat (k + 1) x hx
      rw [hQx x hx, iteratedDeriv_succ_id_mul (hsl x hx)] at h
      exact (mul_eq_zero.1 h).resolve_left (by positivity)
    · rw [hRQ x hx r, congr_fun (hQx x hx) r]
      ring

/-- A smooth function vanishing to infinite order at `r = 0` times the Heaviside function `H(r)`
is smooth. -/
theorem contDiffOn_ite_pos_of_flat {R : E n → ℝ → ℝ}
    (hR : ContDiffOn ℝ ∞ (fun q : E n × ℝ => R q.1 q.2) (U ×ˢ univ)) (hU : IsOpen U)
    (hflat : ∀ k, ∀ x ∈ U, iteratedDeriv k (R x) 0 = 0) :
    ContDiffOn ℝ ∞ (fun q : E n × ℝ => if 0 < q.2 then R q.1 q.2 else 0) (U ×ˢ univ) := by
  refine contDiffOn_infty.2 fun m => ?_
  obtain ⟨Q, hQ, -, hRQ⟩ := exists_eq_pow_mul_of_flat hU hR hflat (m + 1)
  refine ((((contDiff_max_zero_pow m).comp contDiff_snd).contDiffOn).mul
    (hQ.of_le (by simp))).congr fun q hq => ?_
  simp only [Function.comp_apply]
  split_ifs with h
  · rw [hRQ q.1 hq.1, max_eq_left h.le]
  · rw [max_eq_right (not_lt.1 h)]
    simp

/-- **Borel's lemma and the remainder** (`lem_calculus`(b) and the Borel step of
`lem_onesided`): for solutions `b_k` of the transport hierarchy on an open set where `φ` is
eikonal, there is an amplitude `B(x, r)` with `B(·, 0) = b₀`, vanishing where all `b_k` vanish,
such that `□ B(·, φ - s) = R(·, φ - s)` with `R` vanishing to infinite order at `r = 0`, so that
`R_+ = R H` is smooth. On `{φ = s}`, `Z B(·, φ - s) = Z b₀`. -/
theorem exists_amplitude_of_transport
    (hg : ∀ i j, ContDiff ℝ ∞ fun x => g x i j) (hsymm : ∀ x, (g x)ᵀ = g x)
    (hdet : ∀ x, (g x).det ≠ 0) (hU : IsOpen U) (hφ : ContDiffOn ℝ ∞ φ U)
    (heik : ∀ x ∈ U, coform g x (d φ x) (d φ x) = 0) {b : ℕ → E n → ℝ}
    (hb : ∀ k, ContDiffOn ℝ ∞ (b k) U)
    (htr : ∀ k, ∀ x ∈ U,
      2 * -coform g x (d φ x) (d (b (k + 1)) x) + b (k + 1) x * box g φ x = -box g (b k) x) :
    ∃ B R : E n → ℝ → ℝ,
      ContDiffOn ℝ ∞ (fun q : E n × ℝ => B q.1 q.2) (U ×ˢ univ) ∧
      ContDiffOn ℝ ∞ (fun q : E n × ℝ => R q.1 q.2) (U ×ˢ univ) ∧
      ContDiffOn ℝ ∞ (fun q : E n × ℝ => if 0 < q.2 then R q.1 q.2 else 0) (U ×ˢ univ) ∧
      (∀ x ∈ U, R x 0 = 0) ∧ (∀ x ∈ U, B x 0 = b 0 x) ∧
      (∀ x ∈ U, ∀ r, B x r ≠ 0 → ∃ k, b k x ≠ 0) ∧
      (∀ s, ∀ x ∈ U, box g (fun y => B y (φ y - s)) x = R x (φ x - s)) ∧
      ∀ s, ∀ x ∈ U, φ x = s →
        coform g x (d φ x) (d (fun y => B y (φ y - s)) x) = coform g x (d φ x) (d (b 0) x) := by
  obtain ⟨B, hB, hBb, hB0⟩ := Facts.borel hU hb
  have hflat : ∀ k, ∀ x ∈ U, iteratedDeriv k (amplitudeRemainder g φ B x) 0 = 0 :=
    fun k x hx => by
      rw [iteratedDeriv_amplitudeRemainder (φ := φ) hg hdet hU hB hBb k hx, mul_comm (box g φ x),
        add_assoc, htr k x hx, add_neg_cancel]
  have hBzero : ∀ x ∈ U, B x 0 = b 0 x := fun x hx => by
    simpa using hBb 0 x hx
  refine ⟨B, amplitudeRemainder g φ B, hB, contDiffOn_amplitudeRemainder hg hdet hU hB hφ,
    contDiffOn_ite_pos_of_flat (contDiffOn_amplitudeRemainder hg hdet hU hB hφ) hU hflat,
    fun x hx => by simpa using hflat 0 x hx, hBzero, fun x hx r hr => ?_,
    fun s x hx => box_comp_sub_eq hg hsymm hdet hU hB hφ heik s hx, fun s x hx hxs => ?_⟩
  · by_contra h
    exact hr (hB0 x hx (fun k => by_contra fun hk => h ⟨k, hk⟩) r)
  · rw [coform_d_comp_sub hU hB hφ heik s hx, hxs, sub_self]
    congr 1
    refine d_congr (eventually_of_mem (hU.mem_nhds hx) fun y hy => hBzero y hy)

end

end LorentzianCalderon
