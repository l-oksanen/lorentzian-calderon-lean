module

public import LorentzianCalderon.Local.Step.Unique

public section

/-!
# The local continuation step: the conformal factor

Steps 4 and 5 of `prop_local_step`, in a form that avoids the conformal change of the wave
operator. With `g'' = Ψ^* g'` (`gpb`), Step 3 gives `g⁻¹ = κ g''⁻¹` on `V° ∩ {ψ < τ}`. Put
`e = √|det g| κ / √|det g''|`, so that `√|det g| g⁻¹ = e √|det g''| g''⁻¹` there. Then
`□_g Ψ^k = κ □_{g''} Ψ^k - (√|det g|)⁻¹ Σ_j ∂_j e √|det g''| (g''⁻¹ DΨᵀ)_{jk}`, and `θ̄ = 0`
together with the naturality `□_{g''} Ψ^k = (□_{g'} z^k) ∘ Ψ` gives `de = 0`. So `□_g (e - 1) = 0`
on `V°`, `e = 1` above the top, and unique continuation gives `e = 1`; as `e² = κ^{1-n}` and
`n ≥ 2`, `κ = 1`, that is `Ψ^* g' = g` on `V°`.
-/

namespace LorentzianCalderon

noncomputable section
open Set Matrix Filter MeasureTheory Metric
open scoped ContDiff Topology

variable {n : ℕ} {ι : Type*}

namespace StepData

/-- The pulled back metric `g'' = Ψ^* g'`. -/
def gpb (S : StepData n ι) (x : E n) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  (D S.Ψ x)ᵀ * S.g' (S.Ψ x) * D S.Ψ x

/-- `e = √|det g| κ / √|det g''|`. -/
def ef (S : StepData n ι) (x : E n) : ℝ := √|(S.g x).det| * S.κ x / √|(S.gpb x).det|

variable {S : StepData n ι} (hS : S.Hyp)
include hS

theorem Hyp.contDiffAt_D {x : E n} (hx : x ∈ S.V) (i j : Fin (n + 1)) :
    ContDiffAt ℝ ∞ (fun y => D S.Ψ y i j) x := by
  have h := (hS.contDiffOn_dΨ i j).contDiffAt (hS.isOpen_V.mem_nhds hx)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [hS.isOpen_V.mem_nhds hx] with y hy
  exact (d_coord_comp (hS.differentiableAt_Ψ hy) i j).symm

theorem Hyp.contDiffAt_gpb {x : E n} (hx : x ∈ S.V) (i j : Fin (n + 1)) :
    ContDiffAt ℝ ∞ (fun y => S.gpb y i j) x := by
  simp only [gpb, mul_apply, transpose_apply]
  exact ContDiffAt.sum fun l _ => (ContDiffAt.sum fun m _ => (hS.contDiffAt_D hx m i).mul
    ((hS.contDiffOn_g'Ψ m l).contDiffAt (hS.isOpen_V.mem_nhds hx))).mul (hS.contDiffAt_D hx l j)

theorem Hyp.det_gpb_ne_zero {x : E n} (hJ : (D S.Ψ x).det ≠ 0) : (S.gpb x).det ≠ 0 := by
  simp only [gpb, det_mul, det_transpose]
  exact mul_ne_zero (mul_ne_zero hJ (hS.det_ne_zero' _)) hJ

theorem Hyp.contDiffAt_ef {x : E n} (hx : x ∈ S.V) (hJ : (D S.Ψ x).det ≠ 0) :
    ContDiffAt ℝ ∞ S.ef x :=
  ((contDiffAt_sqrt_abs_det (fun i j => (hS.smooth_g i j).contDiffAt) (hS.det_ne_zero x)).mul
    ((hS.contDiffOn_κ).contDiffAt (hS.isOpen_V.mem_nhds hx))).div
    (contDiffAt_sqrt_abs_det (hS.contDiffAt_gpb hx) (hS.det_gpb_ne_zero hJ))
    (Real.sqrt_pos.2 (abs_pos.2 (hS.det_gpb_ne_zero hJ))).ne'

/-- Step 4: where `ḡ = 0`, `g⁻¹ = κ g''⁻¹`. -/
theorem Hyp.inv_eq_of_gb {x : E n} (hx : x ∈ S.V) (hJ : (D S.Ψ x).det ≠ 0)
    (hgb : ∀ α β, S.gb x α β = 0) : (S.g x)⁻¹ = S.κ x • (S.gpb x)⁻¹ := by
  set M := D S.Ψ x
  have hM : IsUnit M.det := hJ.isUnit
  have hMT : IsUnit Mᵀ.det := by rw [det_transpose]; exact hM
  have h1 : M * (S.g x)⁻¹ * Mᵀ = S.κ x • (S.g' (S.Ψ x))⁻¹ := by
    ext α β
    have := hgb α β
    simp only [gb_def, gbar_def, sub_eq_zero, d_coord_comp (hS.differentiableAt_Ψ hx)] at this
    simp only [mul_apply, transpose_apply, Matrix.smul_apply, smul_eq_mul, ← this,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have h2 : (S.g x)⁻¹ = M⁻¹ * (S.κ x • (S.g' (S.Ψ x))⁻¹) * Mᵀ⁻¹ := by
    rw [← h1, Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hMT, Matrix.mul_one,
      ← Matrix.mul_assoc, nonsing_inv_mul _ hM, Matrix.one_mul]
  rw [h2, gpb, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_assoc]

omit hS in
theorem vec_eq_zero_of_vecMul {v : Fin (n + 1) → ℝ} {N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hN : IsUnit N.det) (h : v ᵥ* N = 0) : v = 0 := by
  have : v = (v ᵥ* N) ᵥ* N⁻¹ := by rw [vecMul_vecMul, mul_nonsing_inv _ hN, vecMul_one]
  rw [this, h, zero_vecMul]

namespace Ball

variable {R : ℝ} (hB : S.Ball R)
include hB

/-- Step 5: `de = 0` below the top. -/
theorem d_ef_eq_zero [Fintype ι] {x : E n} (hx : x ∈ S.Vlow R) : d S.ef x = 0 := by
  have hxB := Vo_subset hB (mem_Vlow.1 hx).1
  have hxV := hB.subset hxB
  have hJ := hB.det x hxB
  have hVl := (isOpen_Vlow hS hB).mem_nhds hx
  have h123 := steps123 hS hB
  set F : Fin (n + 1) → Fin (n + 1) → E n → ℝ := fun j k y =>
    √|(S.gpb y).det| * ∑ l, (S.gpb y)⁻¹ j l * d (fun y => S.Ψ y k) y l
  have hρg : √|(S.g x).det| ≠ 0 := (Real.sqrt_pos.2 (abs_pos.2 (hS.det_ne_zero x))).ne'
  have hρh : √|(S.gpb x).det| ≠ 0 :=
    (Real.sqrt_pos.2 (abs_pos.2 (hS.det_gpb_ne_zero hJ))).ne'
  have hfl : ∀ j k, (fun y => √|(S.g y).det| * ∑ l, (S.g y)⁻¹ j l *
      d (fun y => S.Ψ y k) y l) =ᶠ[𝓝 x] fun y => S.ef y * F j k y := by
    intro j k
    filter_upwards [hVl] with y hy
    have hyB := Vo_subset hB (mem_Vlow.1 hy).1
    have hyJ := hB.det y hyB
    have hρhy : √|(S.gpb y).det| ≠ 0 := (Real.sqrt_pos.2 (abs_pos.2 (hS.det_gpb_ne_zero hyJ))).ne'
    rw [hS.inv_eq_of_gb (hB.subset hyB) hyJ (h123 y hy).1]
    simp only [F, ef, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    field_simp
  have hef : DifferentiableAt ℝ S.ef x := (hS.contDiffAt_ef hxV hJ).differentiableAt (by simp)
  have hF : ∀ j k, DifferentiableAt ℝ (F j k) x := fun j k =>
    ((contDiffAt_sqrt_abs_det (hS.contDiffAt_gpb hxV) (hS.det_gpb_ne_zero hJ)).mul
      (ContDiffAt.sum fun l _ => (contDiffAt_inv (hS.contDiffAt_gpb hxV)
        (hS.det_gpb_ne_zero hJ) j l).mul ((hS.contDiffOn_dΨ k l).contDiffAt
          (hS.isOpen_V.mem_nhds hxV)))).differentiableAt (by simp)
  have hA : ∀ k, ∑ j, d S.ef x j * F j k x = 0 := by
    intro k
    have hbg : box S.g (fun y => S.Ψ y k) x =
        -(√|(S.g x).det|)⁻¹ * ∑ j, (d S.ef x j * F j k x + S.ef x * d (F j k) x j) := by
      simp only [box_def]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show d (fun y => √|(S.g y).det| * ∑ l, (S.g y)⁻¹ j l * d (fun y => S.Ψ y k) y l) x j =
        d (fun y => S.ef y * F j k y) x j from congrFun (d_congr (hfl j k)) j]
      exact d_mul hef (hF j k) j
    have hbh : box S.gpb (fun y => S.Ψ y k) x =
        -(√|(S.gpb x).det|)⁻¹ * ∑ j, d (F j k) x j := by
      rw [box_def]
    have hnat : box S.gpb ((fun z : E n => z k) ∘ S.Ψ) x = box S.g' (fun z => z k) (S.Ψ x) :=
      box_comp_of_pullback ((hS.smooth_Ψ.contDiffAt (hS.isOpen_V.mem_nhds hxV)).of_le (by simp))
        hJ (fun i j => ((hS.smooth_g' i j).differentiable (by simp)) _) (hS.det_ne_zero' _)
        (Eventually.of_forall fun _ => rfl) ((contDiff_coordinate k).contDiffAt.of_le (by simp))
    have hθ : S.θb x k = 0 := (h123 x hx).2.1 k
    simp only [θb_def, θbar_def] at hθ
    have hκ : S.ef x * √|(S.gpb x).det| / √|(S.g x).det| = S.κ x := by
      simp only [ef]; field_simp
    have e1 : box S.g (fun y => S.Ψ y k) x = S.κ x * box S.gpb (fun y => S.Ψ y k) x := by
      rw [show box S.gpb (fun y => S.Ψ y k) x = box S.gpb ((fun z : E n => z k) ∘ S.Ψ) x
        from rfl, hnat]
      linarith
    rw [hbg, hbh, Finset.sum_add_distrib, ← Finset.mul_sum, ← hκ] at e1
    field_simp at e1
    linarith
  have hv : d S.ef x ᵥ* ((S.gpb x)⁻¹ * (D S.Ψ x)ᵀ) = 0 := by
    ext k
    have := hA k
    simp only [F, d_coord_comp (hS.differentiableAt_Ψ hxV)] at this
    simp only [vecMul, dotProduct, mul_apply, transpose_apply, Pi.zero_apply]
    have e : ∑ j, d S.ef x j * (√|(S.gpb x).det| * ∑ l, (S.gpb x)⁻¹ j l * D S.Ψ x k l) =
        √|(S.gpb x).det| * ∑ j, d S.ef x j * ∑ l, (S.gpb x)⁻¹ j l * D S.Ψ x k l := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [e] at this
    exact (mul_eq_zero.1 this).resolve_left hρh
  have hN : IsUnit ((S.gpb x)⁻¹ * (D S.Ψ x)ᵀ).det := by
    rw [det_mul, det_transpose]
    exact (isUnit_nonsing_inv_det _ (hS.det_gpb_ne_zero hJ).isUnit).mul hJ.isUnit
  exact vec_eq_zero_of_vecMul hN hv

omit hS hB in
theorem box_eq_zero_of_d {g : MatrixField n} {u : E n → ℝ} {x : E n}
    (h : ∀ᶠ y in 𝓝 x, d u y = 0) : box g u x = 0 := by
  have : ∀ j, d (fun y => √|(g y).det| * ∑ k, (g y)⁻¹ j k * d u y k) x j = 0 := by
    intro j
    have hev : (fun y => √|(g y).det| * ∑ k, (g y)⁻¹ j k * d u y k) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [h] with y hy
      simp [hy]
    rw [congrFun (d_congr hev) j]
    simp [d_def]
  simp [box_def, this]

omit hB in
theorem ef_eq_one_of_top {x : E n} (hx : x ∈ S.V) (hψ : S.τ < S.ψ x) : S.ef x = 1 := by
  have hpull := hS.pullback_top x hx hψ
  have hρ : √|(S.g x).det| ≠ 0 := (Real.sqrt_pos.2 (abs_pos.2 (hS.det_ne_zero x))).ne'
  simp only [ef, κ_eq_one hS hx hpull, mul_one, gpb, ← hpull]
  exact div_self hρ

/-- `e = 1` on `V°`, by unique continuation. -/
theorem ef_eq_one [Fintype ι] : ∀ x ∈ S.Vo R, S.ef x = 1 := by
  have hVo := isOpen_Vo hS hB
  have hsm : ContDiffOn ℝ ∞ (fun y => S.ef y - 1) (S.Vo R) := fun y hy =>
    ((hS.contDiffAt_ef (hB.subset (Vo_subset hB hy)) (hB.det y (Vo_subset hB hy))).sub
      contDiffAt_const).contDiffWithinAt
  have hup : ∀ y ∈ S.Vo R, S.τ < S.ψ y → S.ef y - 1 = 0 := fun y hy hψ => by
    rw [ef_eq_one_of_top hS (hB.subset (Vo_subset hB hy)) hψ, sub_self]
  have hbup : ∀ y ∈ S.Vo R, S.τ < S.ψ y → box S.g (fun y => S.ef y - 1) y = 0 :=
    fun y hy hψ => box_eq_zero_of_eventuallyEq (Filter.eventually_of_mem
      ((isOpen_Vo_top hS hB).mem_nhds ⟨hy, hψ⟩) fun z hz => hup z hz.1 hz.2)
  intro x hx
  have := unique_continuation hS hB hsm (fun y hy => ?_) hup x hx
  · linarith
  rcases lt_trichotomy (S.ψ y) S.τ with hlt | heq | hgt
  · refine box_eq_zero_of_d (Filter.eventually_of_mem ((isOpen_Vlow hS hB).mem_nhds (mem_Vlow.2
    ⟨hy, hlt⟩))
      fun z hz => ?_)
    have hzV := hB.subset (Vo_subset hB (mem_Vlow.1 hz).1)
    ext k
    rw [show d (fun y => S.ef y - 1) z k = d S.ef z k - d (fun _ => (1 : ℝ)) z k by
      simp only [d_def]
      rw [fderiv_fun_sub ((hS.contDiffAt_ef hzV (hB.det z (Vo_subset hB
        (mem_Vlow.1 hz).1))).differentiableAt
        (by simp)) (differentiableAt_const _)]
      rfl, d_ef_eq_zero hS hB hz]
    simp [d_def]
  · have hc : ContinuousAt (box S.g (fun y => S.ef y - 1)) y :=
      (contDiffOn_box hS.smooth_g hS.det_ne_zero hVo hsm).continuousOn.continuousAt
        (hVo.mem_nhds hy)
    exact eq_zero_of_mem_closure hc (fun z hz => hbup z hz.1 hz.2)
      (mem_closure_Vo_top hS hB hy heq)
  · exact hbup y hy hgt

/-- **Steps 4, 5**: `κ = 1` and `Ψ^* g' = g` on `V°`. -/
theorem pullback_Vo [Fintype ι] : ∀ x ∈ S.Vo R,
    S.κ x = 1 ∧ S.g x = (D S.Ψ x)ᵀ * S.g' (S.Ψ x) * D S.Ψ x := by
  intro x hx
  have hxB := Vo_subset hB hx
  have hxV := hB.subset hxB
  rcases lt_trichotomy (S.ψ x) S.τ with hlt | heq | hgt
  · have hJ := hB.det x hxB
    have hinv := hS.inv_eq_of_gb hxV hJ ((steps123 hS hB) x (mem_Vlow.2 ⟨hx, hlt⟩)).1
    have he := ef_eq_one hS hB x hx
    have hκ0 : 0 < S.κ x := lt_trans (by norm_num) (hB.κ_pos x hxB)
    have hdg := hS.det_ne_zero x
    have hdh := hS.det_gpb_ne_zero hJ
    have hdet : (S.gpb x).det = S.κ x ^ (n + 1) * (S.g x).det := by
      have := congrArg Matrix.det hinv
      rw [det_smul, Fintype.card_fin, det_nonsing_inv, det_nonsing_inv] at this
      simp only [Ring.inverse_eq_inv'] at this
      rw [inv_eq_iff_eq_inv, mul_inv, inv_inv] at this
      rw [this, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hκ0.ne'), one_mul]
    have hκ1 : S.κ x = 1 := by
      simp only [ef] at he
      have hρh : 0 < √|(S.gpb x).det| := Real.sqrt_pos.2 (abs_pos.2 hdh)
      rw [div_eq_one_iff_eq hρh.ne'] at he
      have h5 : |(S.gpb x).det| = S.κ x ^ (n + 1) * |(S.g x).det| := by
        rw [hdet, abs_mul, abs_of_pos (pow_pos hκ0 _)]
      have h2 : |(S.g x).det| * S.κ x ^ 2 = |(S.g x).det| * S.κ x ^ (n + 1) := by
        have := congrArg (fun t => t ^ 2) he
        beta_reduce at this
        rw [mul_pow, Real.sq_sqrt (abs_nonneg _), Real.sq_sqrt (abs_nonneg _), h5] at this
        linarith
      have hg0 : 0 < |(S.g x).det| := abs_pos.2 hdg
      have h3 : S.κ x ^ 2 = S.κ x ^ (n + 1) := mul_left_cancel₀ hg0.ne' h2
      have h4 : S.κ x ^ (n - 1) = 1 := by
        have e : S.κ x ^ (n + 1) = S.κ x ^ 2 * S.κ x ^ (n - 1) := by
          rw [← pow_add]; congr 1; have := hS.two_le; omega
        rw [e] at h3
        have := pow_pos hκ0 2
        field_simp at h3
        linarith
      exact (pow_eq_one_iff_of_nonneg hκ0.le (by have := hS.two_le; omega)).1 h4
    refine ⟨hκ1, ?_⟩
    rw [hκ1, one_smul] at hinv
    have := congrArg (·⁻¹) hinv
    rwa [nonsing_inv_nonsing_inv _ hdg.isUnit, nonsing_inv_nonsing_inv _ hdh.isUnit] at this
  · have hpull := hS.pullback_of_closure hxV (closure_mono
      (fun y (hy : y ∈ {y | y ∈ S.Vo R ∧ S.τ < S.ψ y}) =>
        (⟨hB.subset (Vo_subset hB hy.1), hy.2⟩ : y ∈ {y | y ∈ S.V ∧ S.τ < S.ψ y}))
      (mem_closure_Vo_top hS hB hx heq))
    exact ⟨κ_eq_one hS hxV hpull, hpull⟩
  · have hpull := hS.pullback_top x hxV hgt
    exact ⟨κ_eq_one hS hxV hpull, hpull⟩

end Ball

end StepData

end

end LorentzianCalderon
