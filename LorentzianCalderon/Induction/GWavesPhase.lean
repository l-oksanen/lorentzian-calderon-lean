module

public import LorentzianCalderon.Induction.GWavesHamilton
public import LorentzianCalderon.Induction.Frontier
public import LorentzianCalderon.Waves.Transport

public section

/-!
# The phase of the `g`-waves near a frontier point

Blueprint, Lemma `lem_g_waves`, Step 1: a smooth function `φ♮` near `q₀ ∈ Σ_τ` which is eikonal
on `{ψ ≥ τ}`, with `-grad φ♮(q₀)` future-directed, agrees on `{ψ ≥ τ}` with a function which is
eikonal of future type on a neighbourhood of `q₀` (`exists_isFutureEikonal_extension`).

The proof is the method of characteristics: the phase is defined by `φ(𝔉(y)) = φ♮(x̄(y))`,
where `x̄` parametrizes `Σ_τ` near `q₀` and `𝔉(y) = π Φ_{r(y)}(x̄(y), dφ♮(x̄(y)))` for the Hamilton
flow `Φ` of `𝓗 = ½ g^{-1}(ξ, ξ)`, and `dφ = ξ` along the characteristics follows from the
characteristic identity `fderiv_inner_hamFlow`. On `{ψ ≥ τ}` the characteristics are the integral
curves of `grad φ♮` with `ξ = dφ♮`, by uniqueness for the Hamilton flow
(`fderiv_toLp_d_grad`).
-/

namespace LorentzianCalderon

noncomputable section
open Set Filter Function WithLp
open scoped ContDiff Topology RealInnerProductSpace

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n} {ψ : E n → ℝ}

lemma toLp_d_eq_vecOf (φ : E n → ℝ) (x : E n) : toLp 2 (d φ x) = vecOf (fderiv ℝ φ x) := by
  rw [vecOf_def]
  ext i
  simp [d_def]

lemma inner_toLp_d (φ : E n → ℝ) (x v : E n) : ⟪toLp 2 (d φ x), v⟫ = fderiv ℝ φ x v := by
  rw [toLp_d_eq_vecOf, inner_vecOf]

/-- If `x ↦ 𝓗(x, dφ(x))` vanishes on `B ∩ {ψ ≥ τ}`, then along `grad φ` the covector `dφ`
moves by the Hamilton equation `ξ̇ = -∂_x 𝓗` at the points of `B ∩ {ψ ≥ τ}`. -/
theorem fderiv_toLp_d_grad (hg : IsSpacetime g Y) (hψ : IsCauchyTemporal g Y ψ) {τ : ℝ}
    {B : Set (E n)} (hB : IsOpen B) {φn : E n → ℝ} (hφn : ContDiffOn ℝ ∞ φn B)
    (heik : ∀ x ∈ B, τ ≤ ψ x → coform g x (d φn x) (d φn x) = 0) {x : E n} (hxB : x ∈ B)
    (hxτ : τ ≤ ψ x) :
    fderiv ℝ (fun y => toLp 2 (d φn y)) x (grad g φn x) =
      -hamGradX (hamG g) (x, toLp 2 (d φn x)) := by
  set Ξn : E n → E n := fun y => toLp 2 (d φn y)
  have hΞn : ContDiffOn ℝ ∞ Ξn B := by
    have : Ξn = fun y => vecOfL (fderiv ℝ φn y) :=
      funext fun y => by rw [vecOfL_apply, ← toLp_d_eq_vecOf]
    rw [this]
    exact vecOfL.contDiff.comp_contDiffOn (hφn.fderiv_of_isOpen hB le_rfl)
  have hφa : ContDiffAt ℝ ∞ φn x := hφn.contDiffAt (hB.mem_nhds hxB)
  have hdφd : DifferentiableAt ℝ (fderiv ℝ φn) x :=
    ((hφn.fderiv_of_isOpen hB (m := ∞) le_rfl).contDiffAt (hB.mem_nhds hxB)).differentiableAt
      (by simp)
  have hDΞ : ∀ u, fderiv ℝ Ξn x u = vecOf (fderiv ℝ (fderiv ℝ φn) x u) := fun u => by
    have : Ξn = fun y => vecOfL (fderiv ℝ φn y) :=
      funext fun y => by rw [vecOfL_apply, ← toLp_d_eq_vecOf]
    rw [this, fderiv_fun_comp x vecOfL.differentiableAt hdφd]
    simp [ContinuousLinearMap.fderiv, vecOfL_apply]
  have hsymm := hφa.isSymmSndFDerivAt (n := ∞) (by simp)
  set k : E n → ℝ := fun y => hamG g (y, Ξn y)
  have hk : ContDiffOn ℝ ∞ k B :=
    (contDiff_hamG hg).comp_contDiffOn (contDiffOn_id.prodMk hΞn)
  have hk0 : ∀ y ∈ B, τ ≤ ψ y → k y = 0 := fun y hy hyτ => by
    simp [k, Ξn, hamG_def, heik y hy hyτ]
  have hBA : IsOpen (B ∩ A ψ τ) := hB.inter (isOpen_A hψ.smooth.continuous τ)
  have hdk : fderiv ℝ k x = 0 := by
    have hcl : x ∈ closure (B ∩ A ψ τ) := by
      rcases hxτ.lt_or_eq with h | h
      · exact subset_closure ⟨hxB, (mem_A.2 h)⟩
      · have hdψ : fderiv ℝ ψ x ≠ 0 := fun h' =>
          fderiv_apply_unitNormal_ne_zero hg hψ x (by rw [h']; rfl)
        exact hB.inter_closure ⟨hxB, mem_closure_A (hψ.smooth.of_le (by simp)) hdψ h.symm⟩
    have hzero : ∀ y ∈ B ∩ A ψ τ, ‖fderiv ℝ k y‖ ≤ (0 : ℝ) := fun y hy => by
      have hev : k =ᶠ[𝓝 y] fun _ => (0 : ℝ) :=
        eventually_of_mem (hBA.mem_nhds hy) fun y' hy' => hk0 y' hy'.1 (mem_A.1 hy'.2).le
      rw [hev.fderiv_eq, fderiv_const_apply, norm_zero]
    have hc : ContinuousWithinAt (fun y => ‖fderiv ℝ k y‖) (B ∩ A ψ τ) x :=
      ((hk.continuousOn_fderiv_of_isOpen hB (by simp)).norm x hxB).mono inter_subset_left
    exact norm_le_zero_iff.1 (ContinuousWithinAt.closure_le hcl hc continuousWithinAt_const hzero)
  have hΞd : DifferentiableAt ℝ Ξn x :=
    (hΞn.contDiffAt (hB.mem_nhds hxB)).differentiableAt (by simp)
  refine ext_inner_right ℝ fun u => ?_
  have h1 : fderiv ℝ k x u = 0 := by rw [hdk]; rfl
  have hku : fderiv ℝ k x u = fderiv ℝ (hamG g) (x, Ξn x) (u, fderiv ℝ Ξn x u) := by
    have h := ((contDiff_hamG hg).differentiable (by simp) (x, Ξn x)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).prodMk hΞd.hasFDerivAt)
    rw [show k = hamG g ∘ (fun y => (id y, Ξn y)) from rfl, h.fderiv]
    rfl
  rw [hku, fderiv_apply_eq_inner, hamGradξ_hamG hg, raise_d] at h1
  simp only at h1
  rw [hDΞ, real_inner_comm (vecOf _) (grad g φn x), inner_vecOf, hsymm u (grad g φn x),
    ← inner_vecOf, ← hDΞ] at h1
  rw [inner_neg_left]
  linarith

/-- **The phase** (`lem_g_waves`, Step 1): the solution of the eikonal equation by the method of
characteristics, from the initial covectors `dφ♮` on `Σ_τ`. -/
theorem exists_isFutureEikonal_extension (hg : IsSpacetime g Y) (hψ : IsCauchyTemporal g Y ψ)
    {τ : ℝ} {q₀ : E n} (hq₀ : ψ q₀ = τ) {B : Set (E n)} (hB : IsOpen B) (hq₀B : q₀ ∈ B)
    {φn : E n → ℝ} (hφn : ContDiffOn ℝ ∞ φn B)
    (heik : ∀ x ∈ B, τ ≤ ψ x → coform g x (d φn x) (d φn x) = 0)
    (hfut : IsFutureCausal g Y q₀ (-grad g φn q₀)) :
    ∃ U ⊆ B, IsOpen U ∧ q₀ ∈ U ∧ ∃ φ : E n → ℝ, IsFutureEikonal g Y φ U ∧
      ∀ x ∈ U, τ ≤ ψ x → φ x = φn x := by
  have hYt := hg.globallyHyperbolic.timeOrientation.timelike
  set 𝓗 := hamG g with h𝓗def
  have h𝓗 : ContDiff ℝ ∞ 𝓗 := contDiff_hamG hg
  obtain ⟨𝒟, Fl, h𝒟o, hFl, -, hFl0, hFlt, hFlseg, hFluniq⟩ :=
    exists_flow isOpen_univ (contDiff_hamField h𝓗).contDiffOn
  have hcons : ∀ p ∈ 𝒟, 𝓗 (Fl p) = 𝓗 p.2 := by
    intro p hp
    have key := eq_of_hasDerivAt_zero_uIcc (f := fun s => 𝓗 (Fl (s, p.2))) (t := p.1)
      fun s hs => by
        have hsD := hFlseg p hp s hs
        have := (h𝓗.differentiable (by simp) (Fl (s, p.2))).hasFDerivAt.comp_hasDerivAt s
          (hFlt _ hsD)
        rw [fderiv_hamField_eq_zero] at this
        exact this
    simpa [(hFl0 p.2 (mem_univ _)).2] using key
  /- A chart `x̄` of `Σ_τ` near `q₀`. -/
  set γ := grad g φn q₀
  set ℓ := fderiv ℝ ψ q₀
  have hℓγ : ℓ γ < 0 := by
    have := hψ.fderiv_pos hg hfut
    rw [map_neg] at this
    linarith
  set c := (ℓ γ)⁻¹
  set e := c • γ
  have hℓe : ℓ e = 1 := by
    simp only [e, c, map_smul, smul_eq_mul]
    exact inv_mul_cancel₀ hℓγ.ne
  set Ξ : E n → E n := fun x => x + (ψ x - τ - ℓ (x - q₀)) • e
  have hψd : HasFDerivAt ψ ℓ q₀ := (hψ.smooth.differentiable (by simp) q₀).hasFDerivAt
  have hlin : ∀ x, HasFDerivAt (fun x : E n => ℓ (x - q₀)) ℓ x := fun x => by
    have := ℓ.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const q₀)
    rwa [ContinuousLinearMap.comp_id] at this
  have hΞs : ContDiff ℝ ∞ Ξ :=
    contDiff_id.add (((hψ.smooth.sub contDiff_const).sub
      (ℓ.contDiff.comp (contDiff_id.sub contDiff_const))).smul contDiff_const)
  have hΞid : fderiv ℝ Ξ q₀ = ContinuousLinearMap.id ℝ (E n) := by
    have h1 : HasFDerivAt Ξ _ q₀ :=
      (hasFDerivAt_id q₀).add (((hψd.sub_const τ).sub (hlin q₀)).smul_const e)
    rw [h1.fderiv]
    ext v : 1
    simp
  have hℓΞ : ∀ x, ℓ (Ξ x - q₀) = ψ x - τ := fun x => by
    simp only [Ξ, add_sub_right_comm, map_add, map_smul, hℓe, smul_eq_mul, mul_one]
    ring
  have hΞq₀ : Ξ q₀ = q₀ := by simp [Ξ, hq₀]
  obtain ⟨ΞL, hΞL, hq₀ΞL, -, hΞLs, hΞLd⟩ :=
    exists_localInverse_of_fderiv_eq_id isOpen_univ hΞs.contDiffOn (mem_univ q₀) hΞid
  have hq₀T : q₀ ∈ ΞL.target := by
    have := ΞL.map_source hq₀ΞL
    rwa [hΞL, hΞq₀] at this
  have hΞLq₀ : ΞL.symm q₀ = q₀ := by
    have := ΞL.left_inv hq₀ΞL
    rwa [hΞL, hΞq₀] at this
  have hΞLdq₀ : fderiv ℝ ΞL.symm q₀ = ContinuousLinearMap.id ℝ (E n) := by
    ext v : 1
    have := hΞLd q₀ hq₀T v
    rwa [hΞLq₀, hΞid] at this
  set P : E n → E n := fun y => y - ℓ (y - q₀) • e
  have hPs : ContDiff ℝ ∞ P :=
    contDiff_id.sub ((ℓ.contDiff.comp (contDiff_id.sub contDiff_const)).smul contDiff_const)
  have hPd : ∀ y v, fderiv ℝ P y v = v - ℓ v • e := fun y v => by
    have h1 : HasFDerivAt P _ y := (hasFDerivAt_id y).sub ((hlin y).smul_const e)
    rw [h1.fderiv]
    simp
  have hPq₀ : P q₀ = q₀ := by simp [P]
  set xb : E n → E n := fun y => ΞL.symm (P y)
  have hxbψ : ∀ y, P y ∈ ΞL.target → ψ (xb y) = τ := fun y hy => by
    have h1 := hℓΞ (xb y)
    have h2 : Ξ (xb y) = P y := by rw [← hΞL]; exact ΞL.right_inv hy
    rw [h2] at h1
    have h3 : ℓ (P y - q₀) = 0 := by
      simp only [P, sub_right_comm, map_sub, map_smul, hℓe, smul_eq_mul, mul_one]
      ring
    linarith
  set O₁ := P ⁻¹' ΞL.target
  have hO₁ : IsOpen O₁ := ΞL.open_target.preimage hPs.continuous
  have hxbs : ContDiffOn ℝ ∞ xb O₁ := hΞLs.comp hPs.contDiffOn fun y hy => hy
  set S₀ := O₁ ∩ xb ⁻¹' B
  have hS₀ : IsOpen S₀ := hxbs.continuousOn.isOpen_inter_preimage hO₁ hB
  have hxbq₀ : xb q₀ = q₀ := by simp only [xb, hPq₀, hΞLq₀]
  have hq₀S₀ : q₀ ∈ S₀ := ⟨by simp [O₁, hPq₀, hq₀T], by simp [hxbq₀, hq₀B]⟩
  have hdxbq₀ : ∀ v, fderiv ℝ xb q₀ v = v - ℓ v • e := fun v => by
    have hsd : DifferentiableAt ℝ ΞL.symm (P q₀) := by
      rw [hPq₀]
      exact (hΞLs.contDiffAt (ΞL.open_target.mem_nhds hq₀T)).differentiableAt (by simp)
    rw [show xb = ΞL.symm ∘ P from rfl, fderiv_comp q₀ hsd (hPs.differentiable (by simp) q₀)]
    simp [hPq₀, hΞLdq₀, hPd]
  /- The characteristics `Γ(r, y) = Φ_r(x̄(y), dφ♮(x̄(y)))`. -/
  have hdφn : ContDiffOn ℝ ∞ (fun x => toLp 2 (d φn x)) B := by
    have : (fun x => toLp 2 (d φn x)) = fun x => vecOfL (fderiv ℝ φn x) :=
      funext fun x => by rw [vecOfL_apply, ← toLp_d_eq_vecOf]
    rw [this]
    exact vecOfL.contDiff.comp_contDiffOn (hφn.fderiv_of_isOpen hB le_rfl)
  set zb : E n → E n × E n := fun y => (xb y, toLp 2 (d φn (xb y)))
  have hzbs : ContDiffOn ℝ ∞ zb S₀ :=
    (hxbs.mono inter_subset_left).prodMk (hdφn.comp (hxbs.mono inter_subset_left)
      fun y hy => hy.2)
  set Γ : ℝ × E n → E n × E n := fun p => Fl (p.1, zb p.2)
  set D := (univ ×ˢ S₀) ∩ (fun p : ℝ × E n => (p.1, zb p.2)) ⁻¹' 𝒟
  have hm : ContDiffOn ℝ ∞ (fun p : ℝ × E n => (p.1, zb p.2)) (univ ×ˢ S₀) :=
    contDiff_fst.contDiffOn.prodMk (hzbs.comp contDiff_snd.contDiffOn fun p hp => hp.2)
  have hDo : IsOpen D := hm.continuousOn.isOpen_inter_preimage (isOpen_univ.prod hS₀) h𝒟o
  have hΓs : ContDiffOn ℝ ∞ Γ D := hFl.comp (hm.mono inter_subset_left) fun p hp => hp.2
  have hΓd : ∀ p ∈ D, DifferentiableAt ℝ Γ p := fun p hp =>
    (hΓs.contDiffAt (hDo.mem_nhds hp)).differentiableAt (by simp)
  have hq₀D : ((0 : ℝ), q₀) ∈ D := ⟨⟨mem_univ _, hq₀S₀⟩, (hFl0 _ (mem_univ _)).1⟩
  have hΓ0 : ∀ y, Γ (0, y) = zb y := fun y => (hFl0 _ (mem_univ _)).2
  have hDseg : ∀ p ∈ D, ∀ s ∈ uIcc 0 p.1, (s, p.2) ∈ D := fun p hp s hs =>
    ⟨⟨mem_univ _, hp.1.2⟩, hFlseg (p.1, zb p.2) hp.2 s hs⟩
  have hH : ∀ p ∈ D, 𝓗 (Γ p) = 0 := fun p hp => by
    rw [hcons _ hp.2]
    have hy := hp.1.2
    simp [zb, 𝓗, hamG_def, heik _ hy.2 (hxbψ _ hy.1).ge]
  have hflowΓ : ∀ p ∈ D, fderiv ℝ Γ p (1, 0) = hamField 𝓗 (Γ p) := fun p hp =>
    fderiv_apply_one_zero (hΓd p hp) (hFlt (p.1, zb p.2) hp.2)
  have hk : ∀ p ∈ D, ∀ w, ⟪(Γ p).2, (fderiv ℝ Γ p (0, w)).1⟫ =
      fderiv ℝ (fun y => φn (xb y)) p.2 w := by
    intro p hp w
    set kf : ℝ × E n → ℝ := fun q => ⟪(Γ q).2, (fderiv ℝ Γ q (0, w)).1⟫
    have hdΓs : ContDiffOn ℝ ∞ (fderiv ℝ Γ) D := hΓs.fderiv_of_isOpen hDo le_rfl
    have hkd : ∀ q ∈ D, DifferentiableAt ℝ kf q := fun q hq =>
      (differentiableAt_snd.comp q (hΓd q hq)).inner ℝ
        (differentiableAt_fst.comp q
          (((hdΓs.contDiffAt (hDo.mem_nhds hq)).differentiableAt (by simp)).clm_apply
            (differentiableAt_const _)))
    have hzero : ∀ q ∈ D, fderiv ℝ kf q (1, 0) = 0 := fun q hq => by
      rw [fderiv_inner_hamFlow h𝓗 (inner_hamGradξ_hamG hg) hDo hΓs hflowΓ hq w]
      have hev : 𝓗 ∘ Γ =ᶠ[𝓝 q] fun _ => (0 : ℝ) :=
        eventually_of_mem (hDo.mem_nhds hq) fun q' hq' => hH q' hq'
      rw [hev.fderiv_eq, fderiv_const_apply]
      rfl
    have hconst := eq_of_hasDerivAt_zero_uIcc (f := fun s => kf (s, p.2)) (t := p.1)
      fun s hs => by
        have hsD := hDseg p hp s hs
        have hl : HasDerivAt (fun s : ℝ => (s, p.2)) ((1 : ℝ), (0 : E n)) s :=
          (hasDerivAt_id _).prodMk (hasDerivAt_const _ _)
        have := (hkd _ hsD).hasFDerivAt.comp_hasDerivAt s hl
        rwa [hzero _ hsD] at this
    rw [Prod.mk.eta] at hconst
    rw [show ⟪(Γ p).2, (fderiv ℝ Γ p (0, w)).1⟫ = kf p from rfl, hconst]
    -- the value at `r = 0`
    have hy : p.2 ∈ S₀ := hp.1.2
    have h0D : ((0 : ℝ), p.2) ∈ D := hDseg p hp 0 (by simp)
    have hev : (fun y => Γ (0, y)) =ᶠ[𝓝 p.2] zb := Eventually.of_forall hΓ0
    have hzbd : DifferentiableAt ℝ zb p.2 :=
      (hzbs.contDiffAt (hS₀.mem_nhds hy)).differentiableAt (by simp)
    have hxbd : DifferentiableAt ℝ xb p.2 :=
      (hxbs.contDiffAt (hO₁.mem_nhds hy.1)).differentiableAt (by simp)
    have hφd : DifferentiableAt ℝ φn (xb p.2) :=
      (hφn.contDiffAt (hB.mem_nhds hy.2)).differentiableAt (by simp)
    simp only [kf]
    rw [fderiv_apply_zero_left (hΓd _ h0D), hev.fderiv_eq, hΓ0]
    have hfst : (fderiv ℝ zb p.2 w).1 = fderiv ℝ xb p.2 w := by
      rw [(hxbd.hasFDerivAt.prodMk (hzbd.hasFDerivAt.snd)).fderiv]
      rfl
    rw [hfst, inner_toLp_d, fderiv_fun_comp p.2 hφd hxbd]
    rfl
  /- The map `𝔉(y) = π Γ(r(y), y)`. -/
  set r : E n → ℝ := fun y => c * ℓ (y - q₀)
  have hrs : ContDiff ℝ ∞ r := contDiff_const.mul (ℓ.contDiff.comp (contDiff_id.sub contDiff_const))
  have hrd : ∀ y v, fderiv ℝ r y v = c * ℓ v := fun y v => by
    have h1 : HasFDerivAt r _ y := (hlin y).const_mul c
    rw [h1.fderiv]
    simp
  set mr : E n → ℝ × E n := fun y => (r y, y)
  have hmrs : ContDiff ℝ ∞ mr := hrs.prodMk contDiff_id
  set S₁ := mr ⁻¹' D
  have hS₁ : IsOpen S₁ := hDo.preimage hmrs.continuous
  set 𝔉 : E n → E n := fun y => (Γ (mr y)).1
  have h𝔉s : ContDiffOn ℝ ∞ 𝔉 S₁ :=
    contDiff_fst.comp_contDiffOn (hΓs.comp hmrs.contDiffOn fun y hy => hy)
  have hr0 : r q₀ = 0 := by simp [r]
  have hq₀S₁ : q₀ ∈ S₁ := by
    show (r q₀, q₀) ∈ D
    rw [hr0]
    exact hq₀D
  have hd𝔉 : ∀ y ∈ S₁, ∀ v, fderiv ℝ 𝔉 y v =
      (c * ℓ v) • (hamField 𝓗 (Γ (mr y))).1 + (fderiv ℝ Γ (mr y) (0, v)).1 := by
    intro y hy v
    have hΓmd := hΓd _ hy
    have h1 := (hΓmd.hasFDerivAt.comp y (hmrs.differentiable (by simp) y).hasFDerivAt).fst
    rw [show 𝔉 = fun x => ((Γ ∘ mr) x).1 from rfl, h1.fderiv]
    have hmv : fderiv ℝ mr y v = (c * ℓ v) • ((1 : ℝ), (0 : E n)) + ((0 : ℝ), v) := by
      have h2 : HasFDerivAt mr _ y := (hrs.differentiable (by simp) y).hasFDerivAt.prodMk
        (hasFDerivAt_id y)
      rw [h2.fderiv]
      simp [hrd]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', hmv, map_add,
      map_smul, hflowΓ _ hy]
  have hpair : ∀ y ∈ S₁, ∀ v, ⟪(Γ (mr y)).2, fderiv ℝ 𝔉 y v⟫ =
      fderiv ℝ (fun y => φn (xb y)) y v := by
    intro y hy v
    rw [hd𝔉 y hy v, inner_add_right, inner_smul_right, hk _ hy v]
    have : ⟪(Γ (mr y)).2, (hamField 𝓗 (Γ (mr y))).1⟫ = 0 := by
      rw [hamField_fst,
        inner_hamGradξ_hamG hg, show hamG g (Γ (mr y)) = 0 from hH _ hy, mul_zero]
    rw [this, mul_zero, zero_add]
  have hzbq₀ : zb q₀ = (q₀, toLp 2 (d φn q₀)) := by simp [zb, hxbq₀]
  have hΓq₀ : Γ (mr q₀) = (q₀, toLp 2 (d φn q₀)) := by
    show Γ (r q₀, q₀) = _
    rw [hr0, hΓ0, hzbq₀]
  have h𝔉q₀ : 𝔉 q₀ = q₀ := by simp only [𝔉, hΓq₀]
  have hd𝔉q₀ : fderiv ℝ 𝔉 q₀ = ContinuousLinearMap.id ℝ (E n) := by
    ext v : 1
    rw [hd𝔉 q₀ hq₀S₁ v]
    have hzbd : DifferentiableAt ℝ zb q₀ :=
      (hzbs.contDiffAt (hS₀.mem_nhds hq₀S₀)).differentiableAt (by simp)
    have hxbd : DifferentiableAt ℝ xb q₀ :=
      (hxbs.contDiffAt (hO₁.mem_nhds hq₀S₀.1)).differentiableAt (by simp)
    have hev : (fun y => Γ (0, y)) =ᶠ[𝓝 q₀] zb := Eventually.of_forall hΓ0
    have hmq : mr q₀ = (0, q₀) := by simp [mr, hr0]
    rw [hmq, fderiv_apply_zero_left (hΓd _ hq₀D), hev.fderiv_eq, hΓ0, hzbq₀]
    have hfst : (fderiv ℝ zb q₀ v).1 = fderiv ℝ xb q₀ v := by
      rw [(hxbd.hasFDerivAt.prodMk (hzbd.hasFDerivAt.snd)).fderiv]
      rfl
    rw [hfst, hdxbq₀]
    have hγ : hamGradξ 𝓗 (q₀, toLp 2 (d φn q₀)) = γ :=
      (hamGradξ_hamG hg _).trans (raise_d _ _)
    simp only [hamField_def, hγ, e, smul_smul, ContinuousLinearMap.id_apply]
    rw [mul_comm c (ℓ v)]
    module
  /- `ψ` decreases along the characteristics near `(0, q₀)`. -/
  set ρ : ℝ × E n → ℝ := fun p => fderiv ℝ ψ (Γ p).1 ((hamField 𝓗 (Γ p)).1)
  have hρc : ContinuousOn ρ D :=
    ((hψ.smooth.continuous_fderiv (by simp)).comp_continuousOn
      (continuous_fst.comp_continuousOn hΓs.continuousOn)).clm_apply
      ((continuous_fst.comp (contDiff_hamField h𝓗).continuous).comp_continuousOn
        hΓs.continuousOn)
  have hγq₀ : hamGradξ 𝓗 (q₀, toLp 2 (d φn q₀)) = γ :=
    (hamGradξ_hamG hg _).trans (raise_d _ _)
  have hρq₀ : ρ (0, q₀) < 0 := by
    have : Γ (0, q₀) = (q₀, toLp 2 (d φn q₀)) := by rw [hΓ0, hzbq₀]
    simp only [ρ, this, hamField_def, hγq₀]
    simpa only [grad_def, hamField_def] using hℓγ
  obtain ⟨δ₁, hδ₁, hball₁⟩ := Metric.isOpen_iff.1
    (hρc.isOpen_inter_preimage hDo isOpen_Iio) _ ⟨hq₀D, hρq₀⟩
  have hψΓ : ∀ s y, (s, y) ∈ D → HasDerivAt (fun s => ψ (Γ (s, y)).1) (ρ (s, y)) s := by
    intro s y hsy
    have h1 : HasDerivAt (fun s' => Fl (s', zb y)) (hamField 𝓗 (Fl (s, zb y))) s :=
      hFlt (s, zb y) hsy.2
    have h2 : HasFDerivAt (fun z : E n × E n => ψ z.1)
        ((fderiv ℝ ψ (Fl (s, zb y)).1).comp (ContinuousLinearMap.fst ℝ (E n) (E n)))
        (Fl (s, zb y)) :=
      (hψ.smooth.differentiable (by simp) _).hasFDerivAt.comp _ (hasFDerivAt_fst)
    have h3 := h2.comp_hasDerivAt s h1
    exact h3
  /- The integral curves of `grad φ♮`. -/
  obtain ⟨𝒟₂, Fl₂, h𝒟₂o, hFl₂, hFl₂B, hFl₂0, hFl₂t, -, -⟩ :=
    exists_flow hB (contDiffOn_grad hg.smooth hg.det_ne_zero hB hφn)
  have hgradc : ContinuousOn (grad g φn) B :=
    (contDiffOn_grad hg.smooth hg.det_ne_zero hB hφn).continuousOn
  set N₂ := B ∩ {x | fderiv ℝ ψ x (grad g φn x) < 0}
  have hN₂ : IsOpen N₂ :=
    ((hψ.smooth.continuous_fderiv (by simp)).continuousOn.clm_apply hgradc).isOpen_inter_preimage
      hB isOpen_Iio
  have hq₀N₂ : q₀ ∈ N₂ := ⟨hq₀B, hℓγ⟩
  obtain ⟨δ₂, hδ₂, hball₂⟩ := Metric.isOpen_iff.1
    (hFl₂.continuousOn.isOpen_inter_preimage h𝒟₂o hN₂) ((0 : ℝ), q₀)
    ⟨(hFl₂0 q₀ hq₀B).1, by show Fl₂ (0, q₀) ∈ N₂; rw [(hFl₂0 q₀ hq₀B).2]; exact hq₀N₂⟩
  set δ := min δ₁ δ₂
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  /- The domain of the local inverse. -/
  set S₂ := (S₁ ∩ {y | |r y| < δ ∧ dist y q₀ < δ}) ∩ xb ⁻¹' Metric.ball q₀ δ
  have hS₁S₀ : S₁ ⊆ S₀ := fun y hy => hy.1.2
  have hS₂o : IsOpen S₂ := by
    have h1 : IsOpen (S₁ ∩ {y | |r y| < δ ∧ dist y q₀ < δ}) :=
      hS₁.inter ((isOpen_lt (continuous_abs.comp hrs.continuous) continuous_const).inter
        (isOpen_lt (continuous_id.dist continuous_const) continuous_const))
    exact (hxbs.continuousOn.mono fun y hy => (hS₁S₀ hy.1).1).isOpen_inter_preimage h1
      Metric.isOpen_ball
  have hS₂S₁ : S₂ ⊆ S₁ := fun y hy => hy.1.1
  have hq₀S₂ : q₀ ∈ S₂ := ⟨⟨hq₀S₁, by simp [hr0, hδ]⟩, by simp [hxbq₀, hδ]⟩
  obtain ⟨𝔉L, h𝔉L, hq₀src, hsrc, h𝔉Ls, h𝔉Ld⟩ :=
    exists_localInverse_of_fderiv_eq_id hS₂o (h𝔉s.mono hS₂S₁) hq₀S₂ hd𝔉q₀
  have hsymS₂ : ∀ x ∈ 𝔉L.target, 𝔉L.symm x ∈ S₂ := fun x hx => hsrc (𝔉L.map_target hx)
  have h𝔉sym : ∀ x ∈ 𝔉L.target, 𝔉 (𝔉L.symm x) = x := fun x hx => by
    rw [← h𝔉L]; exact 𝔉L.right_inv hx
  have hq₀tgt : q₀ ∈ 𝔉L.target := by
    have := 𝔉L.map_source hq₀src
    rwa [h𝔉L, h𝔉q₀] at this
  have hsymq₀ : 𝔉L.symm q₀ = q₀ := by
    have := 𝔉L.left_inv hq₀src
    rwa [h𝔉L, h𝔉q₀] at this
  /- The phase `φ = φ♮ ∘ x̄ ∘ 𝔉⁻¹`. -/
  set φ : E n → ℝ := fun x => φn (xb (𝔉L.symm x))
  have hxbB : ∀ y ∈ S₁, xb y ∈ B := fun y hy => (hS₁S₀ hy).2
  have hhs : ContDiffOn ℝ ∞ (fun y => φn (xb y)) S₁ :=
    hφn.comp (hxbs.mono fun y hy => (hS₁S₀ hy).1) hxbB
  have hφs : ContDiffOn ℝ ∞ φ 𝔉L.target :=
    hhs.comp h𝔉Ls fun x hx => hS₂S₁ (hsymS₂ x hx)
  have hdφ : ∀ x ∈ 𝔉L.target, toLp 2 (d φ x) = (Γ (mr (𝔉L.symm x))).2 := by
    intro x hx
    set y := 𝔉L.symm x
    have hyS₂ := hsymS₂ x hx
    have hysrc : y ∈ 𝔉L.source := 𝔉L.map_target hx
    have hφd : DifferentiableAt ℝ φ x :=
      (hφs.contDiffAt (𝔉L.open_target.mem_nhds hx)).differentiableAt (by simp)
    have h𝔉d : DifferentiableAt ℝ 𝔉 y :=
      (h𝔉s.contDiffAt (hS₁.mem_nhds (hS₂S₁ hyS₂))).differentiableAt (by simp)
    have hev : φ ∘ 𝔉 =ᶠ[𝓝 y] fun y => φn (xb y) :=
      eventually_of_mem (𝔉L.open_source.mem_nhds hysrc) fun y' hy' => by
        simp only [comp_apply, φ]
        rw [← h𝔉L, 𝔉L.left_inv hy']
    refine ext_inner_right ℝ fun u => ?_
    have hu := h𝔉Ld x hx u
    rw [inner_toLp_d, ← hu, hpair y (hS₂S₁ hyS₂), ← hev.fderiv_eq,
      fderiv_comp y (by rw [h𝔉sym x hx]; exact hφd) h𝔉d, ContinuousLinearMap.comp_apply,
      h𝔉sym x hx]
  have hΓ1 : ∀ x ∈ 𝔉L.target, (Γ (mr (𝔉L.symm x))).1 = x := h𝔉sym
  have heikφ : ∀ x ∈ 𝔉L.target, coform g x (d φ x) (d φ x) = 0 := by
    intro x hx
    have h1 := hH _ (hS₂S₁ (hsymS₂ x hx))
    have h2 : Γ (mr (𝔉L.symm x)) = (x, toLp 2 (d φ x)) :=
      Prod.ext (hΓ1 x hx) (hdφ x hx).symm
    rw [h2] at h1
    simp only [𝓗, hamG_def] at h1
    linarith
  have hdφq₀ : d φ q₀ = d φn q₀ := by
    have := hdφ q₀ hq₀tgt
    rw [hsymq₀, hΓq₀] at this
    exact congrArg ofLp this
  have hgradq₀ : grad g φ q₀ = γ := by
    simp only [γ, grad_def, hdφq₀]
  /- The future type. -/
  set fut : E n → ℝ := fun x => form (g x) (-grad g φ x) (Y x)
  have hfutc : ContinuousOn fut (𝔉L.target ∩ B) :=
    continuousOn_form (fun i j => (hg.smooth i j).continuous.continuousOn)
      ((contDiffOn_grad hg.smooth hg.det_ne_zero 𝔉L.open_target hφs).continuousOn.neg.mono
        inter_subset_left)
      hg.globallyHyperbolic.timeOrientation.continuous.continuousOn
  set T := (𝔉L.target ∩ B) ∩ fut ⁻¹' Iio 0
  have hTo : IsOpen T := hfutc.isOpen_inter_preimage (𝔉L.open_target.inter hB) isOpen_Iio
  have hq₀T' : q₀ ∈ T := ⟨⟨hq₀tgt, hq₀B⟩, by
    show form (g q₀) (-grad g φ q₀) (Y q₀) < 0
    rw [hgradq₀]
    exact hfut.future⟩
  have hTt : T ⊆ 𝔉L.target := fun x hx => hx.1.1
  refine ⟨T, fun x hx => hx.1.2, hTo, hq₀T', φ, ?_, ?_⟩
  · have hne : ∀ x ∈ T, -grad g φ x ≠ 0 := fun x hx h => by
      have := hx.2
      simp only [mem_preimage, mem_Iio, fut, h, form_zero_left] at this
      exact lt_irrefl 0 this
    refine ⟨hTo, hφs.mono hTt, fun x hx => heikφ x (hTt hx), fun x hx h => hne x hx ?_,
      fun x hx => ⟨hne x hx, ?_, hx.2⟩⟩
    · simp [grad_def, h]; rfl
    · rw [form_neg_grad (hg.lorentzian x), heikφ x (hTt hx)]
  · /- Agreement with `φ♮` on `{ψ ≥ τ}`. -/
    intro x hxT hxτ
    have hx := hTt hxT
    set y := 𝔉L.symm x
    have hyS₂ := hsymS₂ x hx
    have hyD : mr y ∈ D := hS₂S₁ hyS₂
    set r₀ := r y
    have hr₀δ : |r₀| < δ := hyS₂.1.2.1
    have hyδ : dist y q₀ < δ := hyS₂.1.2.2
    have hxbδ : dist (xb y) q₀ < δ := hyS₂.2
    have hyS₀ : y ∈ S₀ := hS₁S₀ (hS₂S₁ hyS₂)
    have hx𝔉 : (Γ (r₀, y)).1 = x := hΓ1 x hx
    -- the characteristic through `x` starts on `Σ_τ` at a parameter `r₀ ≤ 0`
    have hN₁ : ∀ s, |s| ≤ |r₀| → (s, y) ∈ D ∧ ρ (s, y) < 0 := fun s hs => by
      have : ((s, y) : ℝ × E n) ∈ Metric.ball ((0 : ℝ), q₀) δ₁ := by
        rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero, max_lt_iff]
        exact ⟨by linarith [min_le_left δ₁ δ₂], by linarith [min_le_left δ₁ δ₂]⟩
      exact hball₁ this
    have hr₀ : r₀ ≤ 0 := by
      by_contra hpos
      push Not at hpos
      have hab : ∀ s ∈ Icc 0 r₀, |s| ≤ |r₀| := fun s hs => by
        rw [abs_of_nonneg hs.1, abs_of_pos hpos]; exact hs.2
      obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (fun s => ψ (Γ (s, y)).1)
        (fun s => ρ (s, y)) hpos
        (fun s hs => (hψΓ s y (hN₁ s (hab s hs)).1).continuousAt.continuousWithinAt)
        fun s hs => hψΓ s y (hN₁ s (hab s (Ioo_subset_Icc_self hs))).1
      have hρξ := (hN₁ ξ (hab ξ (Ioo_subset_Icc_self hξ))).2
      have h0 : ψ (Γ (0, y)).1 = τ := by rw [hΓ0]; exact hxbψ y hyS₀.1
      rw [hslope] at hρξ
      rw [hx𝔉, h0] at hρξ
      have : 0 ≤ (ψ x - τ) / (r₀ - 0) := div_nonneg (by linarith) (by linarith)
      linarith
    -- the integral curve of `grad φ♮` from `x̄(y)` backwards
    set cγ : ℝ → E n := fun s => Fl₂ (s, xb y)
    have hO₂ : ∀ s ∈ Icc r₀ 0, (s, xb y) ∈ 𝒟₂ ∧ cγ s ∈ N₂ := fun s hs => by
      have hsr : |s| ≤ |r₀| := by
        rw [abs_of_nonpos hs.2, abs_of_nonpos hr₀]; linarith [hs.1]
      have : ((s, xb y) : ℝ × E n) ∈ Metric.ball ((0 : ℝ), q₀) δ₂ := by
        rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero, max_lt_iff]
        exact ⟨by linarith [min_le_right δ₁ δ₂], by linarith [min_le_right δ₁ δ₂]⟩
      exact hball₂ this
    have hcγ0 : cγ 0 = xb y := (hFl₂0 _ hyS₀.2).2
    have hcγd : ∀ s ∈ Icc r₀ 0, HasDerivAt cγ (grad g φn (cγ s)) s := fun s hs =>
      hFl₂t (s, xb y) (hO₂ s hs).1
    have hcγψ : ∀ s ∈ Icc r₀ 0, τ ≤ ψ (cγ s) := by
      intro s hs
      rcases hs.2.lt_or_eq with hs0 | hs0
      · obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (fun s => ψ (cγ s))
          (fun s => fderiv ℝ ψ (cγ s) (grad g φn (cγ s))) hs0
          (fun u hu => ((hψ.smooth.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt u
            (hcγd u ⟨hs.1.trans hu.1, hu.2⟩)).continuousAt.continuousWithinAt)
          fun u hu => (hψ.smooth.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt u
            (hcγd u ⟨hs.1.trans hu.1.le, hu.2.le⟩)
        have hneg : fderiv ℝ ψ (cγ ξ) (grad g φn (cγ ξ)) < 0 :=
          (hO₂ ξ ⟨hs.1.trans hξ.1.le, hξ.2.le⟩).2.2
        rw [hslope] at hneg
        rw [hcγ0, hxbψ y hyS₀.1] at hneg
        have := (div_neg_iff.1 hneg)
        rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · linarith
        · linarith
      · rw [hs0, hcγ0, hxbψ y hyS₀.1]
    have hcγB : ∀ s ∈ Icc r₀ 0, cγ s ∈ B := fun s hs => (hO₂ s hs).2.1
    -- `(cγ, dφ♮ ∘ cγ)` is the characteristic through `zb y`
    set C : ℝ → E n × E n := fun s => (cγ s, toLp 2 (d φn (cγ s)))
    have hCd : ∀ s ∈ Icc r₀ 0, HasDerivWithinAt C (hamField 𝓗 (C s)) (Icc r₀ 0) s := by
      intro s hs
      have hdφd : DifferentiableAt ℝ (fun x => toLp 2 (d φn x)) (cγ s) :=
        (hdφn.contDiffAt (hB.mem_nhds (hcγB s hs))).differentiableAt (by simp)
      have h2 := hdφd.hasFDerivAt.comp_hasDerivAt s (hcγd s hs)
      rw [fderiv_toLp_d_grad hg hψ hB hφn heik (hcγB s hs) (hcγψ s hs)] at h2
      have h1 := hcγd s hs
      have hξ : hamGradξ 𝓗 (C s) = grad g φn (cγ s) := (hamGradξ_hamG hg _).trans (raise_d _ _)
      rw [← hξ] at h1
      rw [show hamField 𝓗 (C s) = (hamGradξ 𝓗 (C s), -hamGradX 𝓗 (C s)) from hamField_def 𝓗 _]
      exact (h1.prodMk h2).hasDerivWithinAt
    have hC0 : C 0 = zb y := by
      show (cγ 0, toLp 2 (d φn (cγ 0))) = zb y
      rw [hcγ0]
    have huniq := (hFluniq C (Icc r₀ 0) ordConnected_Icc ⟨hr₀, le_rfl⟩ (fun _ _ => mem_univ _)
      hCd r₀ ⟨le_rfl, hr₀⟩).2
    rw [hC0] at huniq
    have hxc : x = cγ r₀ := by
      rw [← hx𝔉]
      exact congrArg Prod.fst huniq
    -- `φ♮` is constant along `cγ`
    have hconst := eq_of_hasDerivAt_zero_uIcc (f := fun s => φn (cγ s)) (t := r₀)
      fun s hs => by
        rw [uIcc_of_ge hr₀] at hs
        have hφd : DifferentiableAt ℝ φn (cγ s) :=
          (hφn.contDiffAt (hB.mem_nhds (hcγB s hs))).differentiableAt (by simp)
        have := hφd.hasFDerivAt.comp_hasDerivAt s (hcγd s hs)
        have key := form_neg_grad (hg.lorentzian (cγ s)) φn φn
        rw [form_neg_left, form_neg_right, neg_neg, heik _ (hcγB s hs) (hcγψ s hs),
          ← fderiv_eq_form_grad (hg.lorentzian _)] at key
        rwa [key] at this
    rw [hcγ0] at hconst
    show φn (xb y) = φn x
    rw [hxc, hconst]

end

end LorentzianCalderon
