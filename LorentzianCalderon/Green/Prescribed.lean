module

public import LorentzianCalderon.Green.Basic
public import LorentzianCalderon.Waves.Amplitude
public import LorentzianCalderon.Local.Energy.Coform
public import LorentzianCalderon.Causal.TimeFlow

public section

/-!
# Solutions with a prescribed differential

For every covector `ζ` at `p` there is a smooth solution of `□_g v = 0` with `dv(p) = ζ`
(`Facts.exists_solution_fderiv_eq`, blueprint Lemma `set_prescribed_differential`). Let `ψ` be a Cauchy
temporal function and `c = ψ(p)`. The level set `{ψ = c}` is noncharacteristic, `g(dψ, dψ) < 0`,
so the Taylor coefficients `b_k` of an amplitude `B(x, r)` can be chosen recursively, starting
from `b₀ = χ ζ` and `b₁ = 0`, such that `□ B(·, ψ - c) = R(·, ψ - c)` with `R` vanishing to
infinite order at `r = 0` (Borel's lemma). Then `w = B(·, ψ - c)` has `dw(p) = ζ`, and
`F₊ = H(ψ - c) □w`, `F₋ = □w - F₊` are smooth test functions supported in `{ψ ≥ c}` and
`{ψ ≤ c}`. The solution is `v = w - G^ret F₊ - G^adv F₋`: the corrections vanish on
`{ψ < c}` and `{ψ > c}` respectively, so their differentials vanish at `p`.
-/

namespace LorentzianCalderon

noncomputable section
open Set Filter Function
open scoped ContDiff Matrix Topology

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n}

section Coefficients

variable (g) in
/-- The recursion for the Taylor coefficients: `b_{k+2}` from `b_k` and `b_{k+1}`, solving
`□ b_k - 2 g(dψ, db_{k+1}) + (□ψ) b_{k+1} - g(dψ, dψ) b_{k+2} = 0`. -/
def nextCoeff (ψ b₀ b₁ : E n → ℝ) : E n → ℝ := fun x =>
  (box g b₀ x + 2 * -coform g x (d ψ x) (d b₁ x) + box g ψ x * b₁ x) /
    coform g x (d ψ x) (d ψ x)

variable (g) in
/-- The pairs `(b_k, b_{k+1})` of Taylor coefficients, from `b₀` and `b₁ = 0`. -/
def coeffPair (ψ b₀ : E n → ℝ) : ℕ → (E n → ℝ) × (E n → ℝ)
  | 0 => (b₀, 0)
  | k + 1 => ((coeffPair ψ b₀ k).2, nextCoeff g ψ (coeffPair ψ b₀ k).1 (coeffPair ψ b₀ k).2)

variable (g) in
/-- The Taylor coefficients `b_k`. -/
def coeff (ψ b₀ : E n → ℝ) (k : ℕ) : E n → ℝ := (coeffPair g ψ b₀ k).1

variable {ψ b₀ : E n → ℝ}

theorem coeff_succ_succ (k : ℕ) :
    coeff g ψ b₀ (k + 2) = nextCoeff g ψ (coeff g ψ b₀ k) (coeff g ψ b₀ (k + 1)) := by rfl

theorem contDiff_coeffPair (hg : ∀ i j, ContDiff ℝ ∞ fun x => g x i j)
    (hdet : ∀ x, (g x).det ≠ 0) (hψ : ContDiff ℝ ∞ ψ)
    (hψ0 : ∀ x, coform g x (d ψ x) (d ψ x) ≠ 0) (hb₀ : ContDiff ℝ ∞ b₀) (k : ℕ) :
    ContDiff ℝ ∞ (coeffPair g ψ b₀ k).1 ∧ ContDiff ℝ ∞ (coeffPair g ψ b₀ k).2 := by
  induction k with
  | zero => exact ⟨hb₀, contDiff_const⟩
  | succ k ih =>
    refine ⟨ih.2, ContDiff.div ?_ (contDiff_coform_d hg hdet hψ hψ) hψ0⟩
    exact ((contDiff_box hg hdet ih.1).add (contDiff_const.mul
      (contDiff_coform_d hg hdet hψ ih.2).neg)).add ((contDiff_box hg hdet hψ).mul ih.2)

theorem contDiff_coeff (hg : ∀ i j, ContDiff ℝ ∞ fun x => g x i j)
    (hdet : ∀ x, (g x).det ≠ 0) (hψ : ContDiff ℝ ∞ ψ)
    (hψ0 : ∀ x, coform g x (d ψ x) (d ψ x) ≠ 0) (hb₀ : ContDiff ℝ ∞ b₀) (k : ℕ) :
    ContDiff ℝ ∞ (coeff g ψ b₀ k) :=
  (contDiff_coeffPair hg hdet hψ hψ0 hb₀ k).1

theorem d_eq_zero_of_isOpen {u : E n → ℝ} {O : Set (E n)} (hO : IsOpen O)
    (hu : ∀ y ∈ O, u y = 0) {x : E n} (hx : x ∈ O) : d u x = 0 := by
  funext j
  simp [d_def, fderiv_eq_zero_of_isOpen hO hu hx]

theorem box_eq_zero_of_isOpen {u : E n → ℝ} {O : Set (E n)} (hO : IsOpen O)
    (hu : ∀ y ∈ O, u y = 0) {x : E n} (hx : x ∈ O) : box g u x = 0 := by
  rw [box_congr (eventuallyEq_zero_of_isOpen hO hu hx)]
  simp [box_def, d_def]

/-- The coefficients vanish on an open set where `b₀` vanishes. -/
theorem coeffPair_eq_zero {O : Set (E n)} (hO : IsOpen O) (hb₀ : ∀ y ∈ O, b₀ y = 0) (k : ℕ) :
    ∀ y ∈ O, (coeffPair g ψ b₀ k).1 y = 0 ∧ (coeffPair g ψ b₀ k).2 y = 0 := by
  induction k with
  | zero => exact fun y hy => ⟨hb₀ y hy, rfl⟩
  | succ k ih =>
    intro y hy
    refine ⟨(ih y hy).2, ?_⟩
    simp only [coeffPair, nextCoeff, box_eq_zero_of_isOpen hO (fun z hz => (ih z hz).1) hy,
      d_eq_zero_of_isOpen hO (fun z hz => (ih z hz).2) hy, (ih y hy).2]
    simp [coform_def]

end Coefficients

/-- The remainder for a noncharacteristic phase:
`R(x, r) = R₀(x, r) - g(dψ, dψ) ∂_r² B(x, r)` with `R₀` the remainder of `amplitudeRemainder`. -/
def noncharRemainder (g : MatrixField n) (ψ : E n → ℝ) (B : E n → ℝ → ℝ) (x : E n) (r : ℝ) :
    ℝ :=
  amplitudeRemainder g ψ B x r - rDeriv (rDeriv B) x r * coform g x (d ψ x) (d ψ x)

theorem iteratedDeriv_rDeriv_rDeriv (B : E n → ℝ → ℝ) (k : ℕ) (x : E n) :
    iteratedDeriv k (rDeriv (rDeriv B) x) = iteratedDeriv (k + 2) (B x) := by
  rw [iteratedDeriv_succ', iteratedDeriv_succ']
  simp only [rDeriv_def]

/-- **Solutions with a prescribed differential.** Derived from `Facts.exists_retarded` and
`Facts.borel`; see the module docstring. -/
theorem Facts.exists_solution_fderiv_eq (hg : IsSpacetime g Y) (p : E n) (ζ : E n →L[ℝ] ℝ) :
    ∃ v : E n → ℝ, ContDiff ℝ ∞ v ∧ (∀ x, box g v x = 0) ∧ fderiv ℝ v p = ζ := by
  obtain ⟨ψ, -, hψ, -⟩ := Facts.exists_cauchyTemporal hg
  have hψs : ContDiff ℝ ∞ ψ := hψ.smooth
  have hneg : ∀ x, coform g x (d ψ x) (d ψ x) < 0 := fun x =>
    coform_self_neg_of_future (hg.lorentzian x) (hψ.past_gradient x)
  have hψ0 : ∀ x, coform g x (d ψ x) (d ψ x) ≠ 0 := fun x => (hneg x).ne
  let χ : ContDiffBump p := ⟨1, 2, one_pos, one_lt_two⟩
  set K := tsupport χ
  have hK : IsCompact K := χ.hasCompactSupport
  have hKo : IsOpen Kᶜ := (isClosed_tsupport _).isOpen_compl
  set b₀ : E n → ℝ := fun x => χ x * ζ x
  have hb₀ : ContDiff ℝ ∞ b₀ := χ.contDiff.mul ζ.contDiff
  set b := coeff g ψ b₀
  have hb : ∀ k, ContDiff ℝ ∞ (b k) := contDiff_coeff hg.smooth hg.det_ne_zero hψs hψ0 hb₀
  have hbK : ∀ k, ∀ y ∈ Kᶜ, b k y = 0 := fun k y hy =>
    (coeffPair_eq_zero hKo (fun z hz => by
      simp [b₀, image_eq_zero_of_notMem_tsupport hz]) k y hy).1
  obtain ⟨B, hB, hBb, hB0⟩ := Facts.borel isOpen_univ fun k => (hb k).contDiffOn
  have hBf : SmoothFamily univ B := (smoothFamily_iff.2 hB)
  have hBb' : ∀ k x, iteratedDeriv k (B x) 0 = b k x := fun k x => hBb k x (mem_univ x)
  set R := noncharRemainder g ψ B
  have hR : ContDiffOn ℝ ∞ (fun q : E n × ℝ => R q.1 q.2) (univ ×ˢ univ) := by
    refine (contDiffOn_amplitudeRemainder hg.smooth hg.det_ne_zero isOpen_univ hB
      hψs.contDiffOn).sub
      ((smoothFamily_iff.1 ((hBf.rDeriv_family isOpen_univ).rDeriv_family isOpen_univ)).mul ?_)
    exact ((contDiff_coform_d hg.smooth hg.det_ne_zero hψs hψs).comp contDiff_fst).contDiffOn
  have hflat : ∀ k, ∀ x ∈ (univ : Set (E n)), iteratedDeriv k (R x) 0 = 0 := by
    intro k x _
    have h1 : ContDiff ℝ ∞ (amplitudeRemainder g ψ B x) :=
      (SmoothFamily.remainder hg.smooth hg.det_ne_zero isOpen_univ hBf hψs.contDiffOn).slice
        (mem_univ x)
    have h2 : ContDiff ℝ ∞ (rDeriv (rDeriv B) x) :=
      ((hBf.rDeriv_family isOpen_univ).rDeriv_family isOpen_univ).slice (mem_univ x)
    have hRx : R x = amplitudeRemainder g ψ B x -
        fun r => coform g x (d ψ x) (d ψ x) * rDeriv (rDeriv B) x r := by
      funext r
      simp only [R, noncharRemainder, Pi.sub_apply]
      ring
    rw [hRx, iteratedDeriv_sub (h1.contDiffAt.of_le (by simp))
      ((contDiff_const.mul h2).contDiffAt.of_le (by simp)), iteratedDeriv_const_mul_field,
      iteratedDeriv_rDeriv_rDeriv, hBb' (k + 2),
      iteratedDeriv_amplitudeRemainder hg.smooth hg.det_ne_zero isOpen_univ hB hBb k (mem_univ x),
      show b (k + 2) = nextCoeff g ψ (b k) (b (k + 1)) from coeff_succ_succ k]
    simp only [nextCoeff]
    field_simp [hψ0 x]
    ring
  set c := ψ p
  set w : E n → ℝ := fun y => B y (ψ y - c)
  have hw : ContDiff ℝ ∞ w := contDiffOn_univ.1 (hB.comp
    (contDiff_id.prodMk (hψs.sub contDiff_const)).contDiffOn fun _ _ => ⟨mem_univ _, mem_univ _⟩)
  have hboxw : ∀ x, box g w x = R x (ψ x - c) := fun x =>
    box_comp_sub_eq_sub hg.smooth hg.symm hg.det_ne_zero isOpen_univ hB hψs.contDiffOn c
      (mem_univ x)
  have hwK : ∀ y ∈ Kᶜ, w y = 0 := fun y hy => by
    exact hB0 y (mem_univ y) (fun k => hbK k y hy) _
  have hboxK : ∀ y ∈ Kᶜ, box g w y = 0 := fun y hy => box_eq_zero_of_isOpen hKo hwK hy
  set Fp : E n → ℝ := fun x => if 0 < ψ x - c then R x (ψ x - c) else 0
  have hFp : ContDiff ℝ ∞ Fp := by
    have := contDiffOn_ite_pos_of_flat hR isOpen_univ hflat
    exact contDiffOn_univ.1 (this.comp (contDiff_id.prodMk (hψs.sub contDiff_const)).contDiffOn
      fun _ _ => ⟨mem_univ _, mem_univ _⟩)
  set Fm : E n → ℝ := fun x => box g w x - Fp x
  have hFm : ContDiff ℝ ∞ Fm := (contDiff_box hg.smooth hg.det_ne_zero hw).sub hFp
  have hFpK : ∀ y ∈ Kᶜ, Fp y = 0 := fun y hy => by
    simp only [Fp]
    split_ifs
    · rw [← hboxw]
      exact hboxK y hy
    · rfl
  have hFmK : ∀ y ∈ Kᶜ, Fm y = 0 := fun y hy => by simp [Fm, hFpK y hy, hboxK y hy]
  have hcs : ∀ {F : E n → ℝ}, (∀ y ∈ Kᶜ, F y = 0) → HasCompactSupport F := fun hF =>
    HasCompactSupport.intro hK fun y hy => hF y hy
  have hFp' := hcs hFpK
  have hFm' := hcs hFmK
  have hFpc : tsupport Fp ⊆ {x | c ≤ ψ x} := closure_minimal (fun x hx => by
      by_contra h
      simp only [mem_ofPred_eq, not_le] at h
      exact hx (by simp [Fp, show ¬ c < ψ x by linarith]))
    (isClosed_le continuous_const hψs.continuous)
  have hFmc : tsupport Fm ⊆ {x | ψ x ≤ c} := closure_minimal (fun x hx => by
      by_contra h
      simp only [mem_ofPred_eq, not_le] at h
      exact hx (by simp [Fm, Fp, hboxw x, show c < ψ x by linarith]))
    (isClosed_le hψs.continuous continuous_const)
  set uP := retarded g Y Fp
  set uM := advanced g Y Fm
  have huP : ∀ y ∈ {x | ψ x < c}, uP y = 0 := fun y hy => by
    by_contra h
    have := hψ.le_of_mem_causalFutureSet hg (fun x hx => hFpc hx)
      (support_retarded_subset h)
    exact (not_le.2 hy) this
  have huM : ∀ y ∈ {x | c < ψ x}, uM y = 0 := fun y hy => by
    by_contra h
    obtain ⟨q, hq, hyq⟩ := mem_causalPastSet.1 (support_advanced_subset h)
    exact (not_le.2 hy) ((hψ.le_of_causalLE hg (mem_causalPast.1 hyq)).trans (hFmc hq))
  have hdψ : fderiv ℝ ψ p ≠ 0 := fun h0 => by
    have : d ψ p = 0 := funext fun j => by simp [d_def, h0]
    have h := hneg p
    simp [this, coform_def] at h
  have hψd : DifferentiableAt ℝ ψ p := hψs.differentiable (by simp) p
  have hfd0 : ∀ {u : E n → ℝ} {O : Set (E n)}, ContDiff ℝ ∞ u → IsOpen O →
      (∀ y ∈ O, u y = 0) → p ∈ closure O → fderiv ℝ u p = 0 := fun {u} {O} hu hO hu0 hpO =>
    closure_minimal (s := O) (t := {x | fderiv ℝ u x = 0})
      (fun x hx => fderiv_eq_zero_of_isOpen hO hu0 hx)
      (isClosed_eq (hu.continuous_fderiv (by simp)) continuous_const) hpO
  have hpP : p ∈ closure {x | ψ x < c} := by
    simpa using mem_closure_lt_of_fderiv_ne_zero univ_mem hψd hdψ
  have hpM : p ∈ closure {x | c < ψ x} := by
    have := mem_closure_lt_of_fderiv_ne_zero (φ := fun x => -ψ x) univ_mem hψd.neg
      (by rw [fderiv_fun_neg]; exact neg_ne_zero.2 hdψ)
    simpa [c] using this
  have hdP : fderiv ℝ uP p = 0 :=
    hfd0 contDiff_retarded (isOpen_lt hψs.continuous continuous_const) huP hpP
  have hdM : fderiv ℝ uM p = 0 :=
    hfd0 contDiff_advanced (isOpen_lt continuous_const hψs.continuous) huM hpM
  have hb₀p : fderiv ℝ b₀ p = ζ := by
    have hev : b₀ =ᶠ[𝓝 p] ζ := by
      filter_upwards [Metric.ball_mem_nhds p one_pos] with y hy
      simp [b₀, χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)]
    rw [hev.fderiv_eq, ζ.fderiv]
  have hb1 : b 1 = 0 := rfl
  have hwp : fderiv ℝ w p = ζ := by
    ext v
    rw [fderiv_apply_eq_sum_d, ← hb₀p, fderiv_apply_eq_sum_d]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [d_comp_sub isOpen_univ hB (mem_univ p) hψd c j, sub_self]
    have h0 : (fun y => B y 0) = b₀ := funext fun y => by
      have := hBb' 0 y
      rw [iteratedDeriv_zero] at this
      exact this
    have h1 : deriv (B p) 0 = 0 := by
      have := hBb' 1 p
      rw [iteratedDeriv_one, hb1] at this
      exact this
    rw [h0, h1, zero_mul, add_zero]
  have hdiff : ∀ {u : E n → ℝ}, ContDiff ℝ ∞ u → DifferentiableAt ℝ u p := fun hu =>
    hu.differentiable (by simp) p
  refine ⟨fun x => w x - uP x - uM x, (hw.sub contDiff_retarded).sub contDiff_advanced,
    fun x => ?_, ?_⟩
  · rw [box_sub hg.smooth hg.det_ne_zero (hw.sub contDiff_retarded) contDiff_advanced,
      box_sub hg.smooth hg.det_ne_zero hw contDiff_retarded, box_retarded hg hFp hFp',
      box_advanced hg hFm hFm']
    simp only [Fm]
    ring
  · have hsub := ((hdiff hw).hasFDerivAt.sub (hdiff (contDiff_retarded (g := g) (Y := Y)
      (f := Fp))).hasFDerivAt).sub (hdiff (contDiff_advanced (g := g) (Y := Y) (f := Fm))).hasFDerivAt
    rw [show (fun x => w x - uP x - uM x) = w - uP - uM from rfl, hsub.fderiv, hwp, hdP, hdM,
      sub_zero, sub_zero]

end

end LorentzianCalderon
