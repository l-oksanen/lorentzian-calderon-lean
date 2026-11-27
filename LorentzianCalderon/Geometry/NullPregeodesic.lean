module

public import LorentzianCalderon.Geometry.LocalCausality

public section

/-!
# Causal curves that are not null pregeodesics

O'Neill, Semi-Riemannian geometry, Proposition 10.46, p. 294: a future causal curve from `p` to
`q` that is not a null pregeodesic can be replaced by a timelike one, `p ≪ q`
(`Facts.chronLT_of_not_nullPregeodesic`).

O'Neill deforms the curve by variations. Here the proof is local-to-global instead: subdivide
the curve so that any two consecutive pieces lie in one totally normal set. If `p ≪ q` fails,
then by local push-up (`IsTotallyNormal.chronLT_of_chronLT_of_isPathOn` and its time dual) no
two subdivision points are chronologically related, so by local causality
(`IsTotallyNormal.isFutureTimelike_or_radial`) each pair of consecutive pieces is a monotone
reparametrization of a radial null geodesic. These overlap on a piece, where their velocities are
positively proportional, so they continue one maximal null geodesic
(`IsGeodesic.inExpDomain_of_eq`), and `γ` is a null pregeodesic.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Filter Metric

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n}

/-- The domain `{z | (y, z u) ∈ dom exp}` of the ray `z ↦ exp_y (z u)` is an interval. -/
theorem ordConnected_inExpDomain_smul (hg : IsSpacetime g Y) (y u : E n) :
    {z : ℝ | InExpDomain g y (z • u)}.OrdConnected := by
  refine ⟨fun z₁ hz₁ z₂ hz₂ z hz => ?_⟩
  have key : ∀ w : ℝ, InExpDomain g y (w • u) → ∀ r ∈ Icc (0 : ℝ) 1,
      InExpDomain g y ((r * w) • u) := fun w hw r hr => by
    simpa [smul_smul] using hw.smul hg hr
  rcases le_total 0 z with h0 | h0
  · rcases (h0.trans hz.2).lt_or_eq with hpos | heq
    · have := key z₂ hz₂ (z / z₂) ⟨div_nonneg h0 hpos.le, (div_le_one hpos).2 hz.2⟩
      rwa [div_mul_cancel₀ _ hpos.ne'] at this
    · have hz0 : z = 0 := le_antisymm (heq ▸ hz.2) h0
      simpa [hz0] using key z₂ hz₂ 0 ⟨le_rfl, zero_le_one⟩
  · rcases (hz.1.trans h0).lt_or_eq with hneg | heq
    · have := key z₁ hz₁ (z / z₁) ⟨div_nonneg_of_nonpos h0 hneg.le, (div_le_one_of_neg hneg).2 hz.1⟩
      rwa [div_mul_cancel₀ _ hneg.ne] at this
    · have hz0 : z = 0 := le_antisymm h0 (heq ▸ hz.1)
      simpa [hz0] using key z₁ hz₁ 0 ⟨le_rfl, zero_le_one⟩

/-- The ray `z ↦ exp_y (z u)`, `u ≠ 0`, has nonzero strict derivative on its domain. -/
theorem hasStrictDerivAt_expMap_smul (hg : IsSpacetime g Y) {y u : E n} (hu : u ≠ 0) {z : ℝ}
    (hz : InExpDomain g y (z • u)) :
    HasStrictDerivAt (fun r : ℝ => expMap g y (r • u))
        (deriv (fun r : ℝ => expMap g y (r • u)) z) z ∧
      deriv (fun r : ℝ => expMap g y (r • u)) z ≠ 0 := by
  obtain ⟨hS, hS0⟩ := isGeodesic_expMap_smul hg y u
  refine ⟨(hS.smooth.contDiffAt (hS.isOpen.mem_nhds hz)).hasStrictDerivAt (by simp), ?_⟩
  have h0 : (0 : ℝ) ∈ {r : ℝ | InExpDomain g y (r • u)} := by
    simpa using inExpDomain_zero (g := g) y
  exact hS.deriv_ne_zero hg ((ordConnected_inExpDomain_smul hg y u).uIcc_subset h0 hz)
    ordConnected_uIcc left_mem_uIcc (by rwa [hS0]) right_mem_uIcc

/-- A geodesic that agrees to first order with the ray `z ↦ exp_y (z u)` at one time `z₀` is that
ray on its whole (interval) domain, which lies in the domain of the ray. -/
theorem IsGeodesic.inExpDomain_of_eq (hg : IsSpacetime g Y) {ψ : ℝ → E n} {J : Set ℝ}
    (hψ : IsGeodesic g ψ J) (hJ : J.OrdConnected) {y u : E n} {z₀ : ℝ} (hz₀ : z₀ ∈ J)
    (hdom : InExpDomain g y (z₀ • u)) (h0 : ψ z₀ = expMap g y (z₀ • u))
    (h0' : deriv ψ z₀ = deriv (fun z : ℝ => expMap g y (z • u)) z₀) :
    ∀ z ∈ J, InExpDomain g y (z • u) ∧ ψ z = expMap g y (z • u) := by
  classical
  obtain ⟨hS, hS0⟩ := isGeodesic_expMap_smul hg y u
  set I := {z : ℝ | InExpDomain g y (z • u)}
  have hI := ordConnected_inExpDomain_smul hg y u
  have heq := IsGeodesic.eqOn hg hψ hS inter_subset_left inter_subset_right (hJ.inter hI)
    ⟨hz₀, hdom⟩ h0 h0'
  set Θ : ℝ → E n := fun z => if z ∈ I then expMap g y (z • u) else ψ z
  have hΘI : ∀ z ∈ I, Θ z = expMap g y (z • u) := fun z hz => by
    simp only [Θ, hz, ite_true]
  have hΘJ : ∀ z ∈ J, Θ z = ψ z := fun z hz => by
    by_cases hzI : z ∈ I
    · rw [hΘI z hzI]
      exact (heq.1 ⟨hz, hzI⟩).symm
    · simp only [Θ, hzI, ite_false]
  have hΘ : IsGeodesic g Θ (I ∪ J) := by
    refine isGeodesic_of_locally (hS.isOpen.union hψ.isOpen) fun z hz => ?_
    by_cases hzI : z ∈ I
    · exact ⟨_, I, hS, hzI, eventually_of_mem (hS.isOpen.mem_nhds hzI) hΘI⟩
    · exact ⟨ψ, J, hψ, hz.resolve_left hzI, eventually_of_mem
        (hψ.isOpen.mem_nhds (hz.resolve_left hzI)) hΘJ⟩
  have h0I : (0 : ℝ) ∈ I := by simpa [I] using inExpDomain_zero (g := g) y
  have hΘ0 : Θ 0 = y := by rw [hΘI 0 h0I, zero_smul, expMap_zero hg]
  have hΘ0' : deriv Θ 0 = u := by
    have hev : Θ =ᶠ[𝓝 0] fun z => expMap g y (z • u) :=
      eventually_of_mem (hS.isOpen.mem_nhds h0I) hΘI
    rw [hev.deriv_eq, hS0]
  have hIJ : (I ∪ J).OrdConnected := isPreconnected_iff_ordConnected.1
    (IsPreconnected.union z₀ hdom hz₀ (isPreconnected_iff_ordConnected.2 hI)
      (isPreconnected_iff_ordConnected.2 hJ))
  intro z hz
  have := hΘ.expMap_smul_eq hg (hIJ.uIcc_subset (Or.inl h0I) (Or.inr hz))
  rw [hΘ0, hΘ0', hΘJ z hz] at this
  exact ⟨this.1, this.2.symm⟩

/-- Gluing step: a monotone reparametrization `γ = exp_{γ 0} (h(·) u)` on `[0, t₁]` of the ray
`z ↦ exp_{γ 0} (z u)`, and one `γ = exp_{γ s} (λ(·) v)` on `[s, t₂]`, `s < t₁ ≤ t₂`, of the ray
from `γ s`, combine to one of the first ray on `[0, t₂]`. -/
theorem exists_reparam_of_overlap (hg : IsSpacetime g Y) {γ : ℝ → E n} {s t₁ t₂ : ℝ}
    (hγ : IsPathOn (IsFutureCausal g Y) 0 t₂ γ) (hs : 0 ≤ s) (hst : s < t₁) (ht : t₁ ≤ t₂)
    {u : E n} (hu : u ≠ 0) {h : ℝ → ℝ} (hh : MonotoneOn h (Icc 0 t₁))
    (hhc : ContinuousOn h (Icc 0 t₁))
    (hrep : ∀ r ∈ Icc 0 t₁, InExpDomain g (γ 0) (h r • u) ∧ γ r = expMap g (γ 0) (h r • u))
    {v : E n} (hv : v ≠ 0) {lam : ℝ → ℝ} (hlam : MonotoneOn lam (Icc s t₂))
    (hlamc : ContinuousOn lam (Icc s t₂))
    (hrep' : ∀ r ∈ Icc s t₂, InExpDomain g (γ s) (lam r • v) ∧
      γ r = expMap g (γ s) (lam r • v)) :
    ∃ h' : ℝ → ℝ, MonotoneOn h' (Icc 0 t₂) ∧ ContinuousOn h' (Icc 0 t₂) ∧
      ∀ r ∈ Icc 0 t₂, InExpDomain g (γ 0) (h' r • u) ∧ γ r = expMap g (γ 0) (h' r • u) := by
  classical
  obtain ⟨x, y, hx, hxy, hy, hpiece⟩ := hγ.exists_isPathPiece hs hst ht
  set r₀ := (x + y) / 2
  have hr₀ : r₀ ∈ Ioo x y := ⟨by simp only [r₀]; linarith, by simp only [r₀]; linarith⟩
  have hr₀' : r₀ ∈ Icc x y := Ioo_subset_Icc_self hr₀
  have hc : HasDerivWithinAt γ (derivWithin γ (Icc x y) r₀) (Icc x y) r₀ :=
    ((isPathPiece_iff.1 hpiece).1.differentiableOn (by simp) r₀ hr₀').hasDerivWithinAt
  have hc0 := ((isPathPiece_iff.1 hpiece).2 r₀ hr₀').ne_zero
  have hsub₁ : Icc x y ⊆ Icc 0 t₁ := Icc_subset_Icc (hs.trans hx) hy
  have hsub₂ : Icc x y ⊆ Icc s t₂ := Icc_subset_Icc hx (hy.trans ht)
  obtain ⟨hdu, hdu0⟩ := hasStrictDerivAt_expMap_smul hg hu (hrep r₀ (hsub₁ hr₀')).1
  obtain ⟨κ₁, hκ₁, e₁⟩ := exists_pos_smul_of_eq_comp hxy hr₀' hc hdu (hh.mono hsub₁)
    ((hhc.mono hsub₁) r₀ hr₀') (fun r hr => (hrep r (hsub₁ hr)).2) hc0 hdu0
  have hlr₀ := (hrep' r₀ (hsub₂ hr₀')).1
  obtain ⟨hdv, hdv0⟩ := hasStrictDerivAt_expMap_smul hg hv hlr₀
  obtain ⟨κ₂, hκ₂, e₂⟩ := exists_pos_smul_of_eq_comp hxy hr₀' hc hdv (hlam.mono hsub₂)
    ((hlamc.mono hsub₂) r₀ hr₀') (fun r hr => (hrep' r (hsub₂ hr)).2) hc0 hdv0
  set Su : ℝ → E n := fun z => expMap g (γ 0) (z • u)
  set Sv : ℝ → E n := fun z => expMap g (γ s) (z • v)
  set μ := κ₁ / κ₂
  have hμ : 0 < μ := div_pos hκ₁ hκ₂
  have hvel : deriv Sv (lam r₀) = μ • deriv Su (h r₀) := by
    have : κ₂ • deriv Sv (lam r₀) = κ₁ • deriv Su (h r₀) := e₂.symm.trans e₁
    calc deriv Sv (lam r₀) = κ₂⁻¹ • (κ₂ • deriv Sv (lam r₀)) := by
          rw [smul_smul, inv_mul_cancel₀ hκ₂.ne', one_smul]
      _ = μ • deriv Su (h r₀) := by rw [this, smul_smul, inv_mul_eq_div]
  obtain ⟨hSv, -⟩ := isGeodesic_expMap_smul hg (γ s) v
  set c := μ⁻¹
  set d := lam r₀ - μ⁻¹ * h r₀
  set ψ : ℝ → E n := fun z => Sv (c * z + d)
  have hψ : IsGeodesic g ψ ((fun z => c * z + d) ⁻¹' {z : ℝ | InExpDomain g (γ s) (z • v)}) :=
    hSv.comp_affine c d
  have hc' : 0 < c := inv_pos.2 hμ
  have hJ : ((fun z => c * z + d) ⁻¹' {z : ℝ | InExpDomain g (γ s) (z • v)}).OrdConnected := by
    refine ⟨fun a ha b hb z hz => (ordConnected_inExpDomain_smul hg (γ s) v).out ha hb ?_⟩
    exact ⟨by nlinarith [hz.1], by nlinarith [hz.2]⟩
  have hz₀ : c * h r₀ + d = lam r₀ := by simp only [c, d]; ring
  have hz₀J : h r₀ ∈ (fun z => c * z + d) ⁻¹' {z : ℝ | InExpDomain g (γ s) (z • v)} := by
    simp only [mem_preimage, hz₀]
    exact hlr₀
  have hψ0 : ψ (h r₀) = Su (h r₀) := by
    simp only [ψ, hz₀, Sv, Su]
    rw [← (hrep' r₀ (hsub₂ hr₀')).2, (hrep r₀ (hsub₁ hr₀')).2]
  have hψ0' : deriv ψ (h r₀) = deriv Su (h r₀) := by
    rw [hSv.deriv_comp_affine (by rw [hz₀]; exact hlr₀), hz₀, hvel, smul_smul,
      inv_mul_cancel₀ hμ.ne', one_smul]
  have hmax := hψ.inExpDomain_of_eq hg hJ hz₀J (hrep r₀ (hsub₁ hr₀')).1 hψ0 hψ0'
  set φ : ℝ → ℝ := fun x => μ * (x - lam r₀) + h r₀
  have hφ : ∀ x, c * φ x + d = x := fun x => by
    simp only [c, d, φ]
    field_simp
    ring
  have hrep₂ : ∀ r ∈ Icc s t₂, InExpDomain g (γ 0) (φ (lam r) • u) ∧
      γ r = expMap g (γ 0) (φ (lam r) • u) := by
    intro r hr
    have hmem : φ (lam r) ∈ (fun z => c * z + d) ⁻¹' {z : ℝ | InExpDomain g (γ s) (z • v)} := by
      simp only [mem_preimage, hφ]
      exact (hrep' r hr).1
    obtain ⟨h1, h2⟩ := hmax _ hmem
    refine ⟨h1, ?_⟩
    rw [← h2, (hrep' r hr).2]
    simp only [ψ, Sv, hφ]
  have hφr₀ : φ (lam r₀) = h r₀ := by simp [φ]
  refine ⟨fun r => if r ≤ r₀ then h r else φ (lam r), ?_, ?_, ?_⟩
  · intro a ha b hb hab
    have hφm : ∀ a ∈ Icc s t₂, ∀ b ∈ Icc s t₂, a ≤ b → φ (lam a) ≤ φ (lam b) :=
      fun a ha b hb hab => by
        simp only [φ]
        nlinarith [hlam ha hb hab]
    by_cases hb' : b ≤ r₀
    · have ha' : a ≤ r₀ := hab.trans hb'
      simp only [ha', hb', ite_true]
      exact hh ⟨ha.1, ha'.trans (hr₀'.2.trans hy)⟩ ⟨hb.1, hb'.trans (hr₀'.2.trans hy)⟩ hab
    · have hbI : b ∈ Icc s t₂ := ⟨hx.trans (hr₀'.1.trans (not_le.1 hb').le), hb.2⟩
      simp only [hb', ite_false]
      by_cases ha' : a ≤ r₀
      · simp only [ha', ite_true]
        calc h a ≤ h r₀ := hh ⟨ha.1, ha'.trans (hr₀'.2.trans hy)⟩
              (hsub₁ hr₀') ha'
          _ = φ (lam r₀) := hφr₀.symm
          _ ≤ φ (lam b) := hφm _ (hsub₂ hr₀') _ hbI (not_le.1 hb').le
      · simp only [ha', ite_false]
        exact hφm a ⟨hx.trans (hr₀'.1.trans (not_le.1 ha').le), ha.2⟩ b hbI hab
  · refine ContinuousOn.if ?_ ?_ ?_
    · intro a ha
      have : a = r₀ := by
        have h := ha.2
        rw [show {a : ℝ | a ≤ r₀} = Iic r₀ from rfl, frontier_Iic] at h
        exact h
      rw [this, hφr₀]
    · refine hhc.mono fun a ha => ⟨ha.1.1, ?_⟩
      have h := ha.2
      rw [show {a : ℝ | a ≤ r₀} = Iic r₀ from rfl, closure_Iic] at h
      exact (show a ≤ r₀ from h).trans (hr₀'.2.trans hy)
    · have hφc : ContinuousOn (fun r => φ (lam r)) (Icc s t₂) :=
        ((continuous_const.mul (continuous_id.sub continuous_const)).add
          continuous_const).comp_continuousOn hlamc
      refine hφc.mono fun a ha => ⟨?_, ha.1.2⟩
      have h := ha.2
      rw [show {a : ℝ | ¬ a ≤ r₀} = Ioi r₀ from by ext; simp, closure_Ioi] at h
      exact hx.trans (hr₀'.1.trans h)
  · intro r hr
    by_cases hr' : r ≤ r₀
    · simp only [hr', ite_true]
      exact hrep r ⟨hr.1, hr'.trans (hr₀'.2.trans hy)⟩
    · simp only [hr', ite_false]
      exact hrep₂ r ⟨hx.trans (hr₀'.1.trans (not_le.1 hr').le), hr.2⟩

/-- A causal curve on `[0, 1]` whose endpoints are not chronologically related is a monotone
reparametrization of a null ray `z ↦ exp_{γ 0} (z u)`. -/
theorem exists_expMap_reparam_unit (hg : IsSpacetime g Y) {γ : ℝ → E n}
    (hγ : IsPathOn (IsFutureCausal g Y) 0 1 γ) (hc : ¬ ChronLT g Y (γ 0) (γ 1)) :
    ∃ u : E n, u ≠ 0 ∧ form (g (γ 0)) u u = 0 ∧ ∃ h : ℝ → ℝ, MonotoneOn h (Icc 0 1) ∧
      ContinuousOn h (Icc 0 1) ∧
      ∀ r ∈ Icc (0 : ℝ) 1, InExpDomain g (γ 0) (h r • u) ∧ γ r = expMap g (γ 0) (h r • u) := by
  have hcover : ∀ t : Icc (0 : ℝ) 1, ∃ V : Set ℝ, IsOpen V ∧ (t : ℝ) ∈ V ∧
      ∃ W ρ L, IsTotallyNormal g W ρ L ∧ ∀ s ∈ V ∩ Icc 0 1, γ s ∈ W := by
    intro t
    obtain ⟨W, ρ, L, htW, hW⟩ := exists_isTotallyNormal hg (γ t)
    obtain ⟨V, hV, hVeq⟩ := continuousOn_iff'.1 hγ.continuousOn W hW.isOpen
    refine ⟨V, hV, ?_, W, ρ, L, hW, fun s hs => ?_⟩
    · have : (t : ℝ) ∈ γ ⁻¹' W ∩ Icc 0 1 := ⟨htW, t.2⟩
      rw [hVeq] at this
      exact this.1
    · rw [← hVeq] at hs
      exact hs.1
  choose V hVo hVt hVW using hcover
  obtain ⟨δ, hδ, hδV⟩ := lebesgue_number_lemma_of_metric isCompact_Icc hVo
    fun t ht => mem_iUnion.2 ⟨⟨t, ht⟩, hVt ⟨t, ht⟩⟩
  have hloc : ∀ a b, 0 ≤ a → a ≤ b → b ≤ 1 → b - a < δ →
      ∃ W ρ L, IsTotallyNormal g W ρ L ∧ ∀ s ∈ Icc a b, γ s ∈ W := by
    intro a b ha hab hb hδab
    obtain ⟨i, hi⟩ := hδV a ⟨ha, hab.trans hb⟩
    obtain ⟨W, ρ, L, hW, hWγ⟩ := hVW i
    refine ⟨W, ρ, L, hW, fun s hs => hWγ s ⟨hi ?_, ha.trans hs.1, hs.2.trans hb⟩⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hs.1, hs.2]
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / δ)
  have hN0 : (0 : ℝ) < N := lt_trans (by positivity) hN
  have hN1 : 1 ≤ N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · simp [h] at hN0
    · exact h
  have hstep : 2 / (N : ℝ) < δ := by
    rw [div_lt_iff₀ hδ] at hN
    rw [div_lt_iff₀ hN0]
    linarith
  set t : ℕ → ℝ := fun k => k / N with ht_def
  have ht0 : t 0 = 0 := by simp [ht_def]
  have htN : t N = 1 := div_self hN0.ne'
  have htlt : ∀ j k, j < k → t j < t k := fun j k h => by
    simp only [ht_def]
    exact div_lt_div_of_pos_right (by exact_mod_cast h) hN0
  have htle : ∀ j k, j ≤ k → t j ≤ t k := fun j k h => by
    simp only [ht_def]
    exact div_le_div_of_nonneg_right (by exact_mod_cast h) hN0.le
  have ht0le : ∀ k, 0 ≤ t k := fun k => ht0 ▸ htle 0 k (Nat.zero_le k)
  have htle1 : ∀ k ≤ N, t k ≤ 1 := fun k hk => htN ▸ htle k N hk
  have hwin : ∀ j k, j < k → k ≤ N → k ≤ j + 2 → ∃ W ρ L, IsTotallyNormal g W ρ L ∧
      ∀ s ∈ Icc (t j) (t k), γ s ∈ W := by
    intro j k hjk hkN hk
    refine hloc _ _ (ht0le j) (htlt j k hjk).le (htle1 k hkN) ?_
    have e : t k - t j = ((k : ℝ) - j) / N := by simp only [ht_def]; ring
    rw [e]
    refine lt_of_le_of_lt (div_le_div_of_nonneg_right ?_ hN0.le) hstep
    have : (k : ℝ) ≤ j + 2 := by exact_mod_cast hk
    linarith
  have hpath : ∀ j k, j < k → k ≤ N → IsPathOn (IsFutureCausal g Y) (t j) (t k) γ :=
    fun j k hjk hkN => hγ.restrict (ht0le j) (htlt j k hjk) (htle1 k hkN)
  have hfwd : ∀ x m j, j + m = N → ChronLT g Y x (γ (t j)) → ChronLT g Y x (γ 1) := by
    intro x m
    induction m with
    | zero =>
      intro j hj h
      rw [add_zero] at hj
      rwa [hj, htN] at h
    | succ m ih =>
      intro j hj h
      obtain ⟨W, ρ, L, hW, hWγ⟩ := hwin j (j + 1) (by omega) (by omega) (by omega)
      exact ih (j + 1) (by omega) (hW.chronLT_of_chronLT_of_isPathOn hg h
        (hpath j (j + 1) (by omega) (by omega)) hWγ)
  have hbwd : ∀ z j, j ≤ N → ChronLT g Y (γ (t j)) z → ChronLT g Y (γ 0) z := by
    intro z j
    induction j with
    | zero =>
      intro _ h
      rwa [ht0] at h
    | succ j ih =>
      intro hj h
      obtain ⟨W, ρ, L, hW, hWγ⟩ := hwin j (j + 1) (by omega) hj (by omega)
      exact ih (by omega) (hW.chronLT_of_isPathOn_of_chronLT hg (hpath j (j + 1) (by omega) hj)
        hWγ h)
  have hno : ∀ j k, j ≤ k → k ≤ N → ¬ ChronLT g Y (γ (t j)) (γ (t k)) := fun j k hjk hkN h =>
    hc (hfwd _ (N - k) k (by omega) (hbwd _ j (hjk.trans hkN) h))
  have hrad : ∀ j k, j < k → k ≤ N → k ≤ j + 2 → ∃ v : E n, v ≠ 0 ∧
      form (g (γ (t j))) v v = 0 ∧ InExpDomain g (γ (t j)) v ∧ ∃ lam : ℝ → ℝ,
        MonotoneOn lam (Icc (t j) (t k)) ∧ ContinuousOn lam (Icc (t j) (t k)) ∧
        lam (t j) = 0 ∧ lam (t k) = 1 ∧
        ∀ r ∈ Icc (t j) (t k), γ r = expMap g (γ (t j)) (lam r • v) := by
    intro j k hjk hkN hk
    obtain ⟨W, ρ, L, hW, hWγ⟩ := hwin j k hjk hkN hk
    have htjk := htlt j k hjk
    have hjW := hWγ (t j) ⟨le_rfl, htjk.le⟩
    have hkW := hWγ (t k) ⟨htjk.le, le_rfl⟩
    have hdom := hW.inExpDomain _ hjW _ (hW.mem_ball _ hjW _ hkW)
    rcases hW.isFutureTimelike_or_radial hg (hpath j k hjk hkN) hWγ with
      hT | ⟨hv, hnull, ⟨lam, h1, h2, h3, h4, h5⟩, -⟩
    · refine absurd ?_ (hno j k hjk.le hkN)
      have := hdom.chronLT hg hT
      rwa [hW.expMap_inv _ hjW _ hkW] at this
    · exact ⟨_, hv.ne_zero, hnull, hdom, lam, h1, h2, h3, h4, h5⟩
  have hinv : ∀ k, 1 ≤ k → k ≤ N → ∃ u : E n, u ≠ 0 ∧ form (g (γ 0)) u u = 0 ∧
      ∃ h : ℝ → ℝ, MonotoneOn h (Icc 0 (t k)) ∧ ContinuousOn h (Icc 0 (t k)) ∧
        ∀ r ∈ Icc 0 (t k), InExpDomain g (γ 0) (h r • u) ∧ γ r = expMap g (γ 0) (h r • u) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      intro hN1'
      obtain ⟨v, hv, hnull, hvdom, lam, h1, h2, h3, h4, h5⟩ := hrad 0 1 one_pos hN1' (by omega)
      rw [ht0] at hnull hvdom h1 h2 h3 h5
      have h01 := htlt 0 1 one_pos
      rw [ht0] at h01
      refine ⟨v, hv, hnull, lam, h1, h2, fun r hr => ⟨hvdom.smul hg ⟨?_, ?_⟩, h5 r hr⟩⟩
      · exact h3 ▸ h1 ⟨le_rfl, h01.le⟩ hr hr.1
      · exact h4 ▸ h1 hr ⟨h01.le, le_rfl⟩ hr.2
    | succ k hk ih =>
      intro hkN
      obtain ⟨u, hu, hnull, h, hh, hhc, hrep⟩ := ih (by omega)
      obtain ⟨v, hv, -, hvdom, lam, h1, h2, h3, h4, h5⟩ :=
        hrad (k - 1) (k + 1) (by omega) hkN (by omega)
      have hpath0 : IsPathOn (IsFutureCausal g Y) 0 (t (k + 1)) γ := by
        have := hpath 0 (k + 1) (by omega) hkN
        rwa [ht0] at this
      obtain ⟨h', hh', hh'c, hrep'⟩ := exists_reparam_of_overlap hg hpath0 (ht0le _)
        (htlt (k - 1) k (by omega)) (htle k (k + 1) (by omega)) hu hh hhc hrep hv h1 h2
        fun r hr => ⟨hvdom.smul hg ⟨h3 ▸ h1 ⟨le_rfl, (htlt _ _ (by omega)).le⟩ hr hr.1,
          h4 ▸ h1 hr ⟨(htlt _ _ (by omega)).le, le_rfl⟩ hr.2⟩, h5 r hr⟩
      exact ⟨u, hu, hnull, h', hh', hh'c, hrep'⟩
  obtain ⟨u, hu, hnull, h, hh, hhc, hrep⟩ := hinv N hN1 le_rfl
  rw [htN] at hh hhc hrep
  exact ⟨u, hu, hnull, h, hh, hhc, hrep⟩

/-- A causal curve on `[a, b]` whose endpoints are not chronologically related is a monotone
reparametrization of a ray `z ↦ exp_{γ a} (z u)`. -/
theorem exists_expMap_reparam (hg : IsSpacetime g Y) {γ : ℝ → E n} {a b : ℝ}
    (hγ : IsPathOn (IsFutureCausal g Y) a b γ) (hc : ¬ ChronLT g Y (γ a) (γ b)) :
    ∃ u : E n, u ≠ 0 ∧ ∃ h : ℝ → ℝ, MonotoneOn h (Icc a b) ∧ ContinuousOn h (Icc a b) ∧
      ∀ r ∈ Icc a b, InExpDomain g (γ a) (h r • u) ∧ γ r = expMap g (γ a) (h r • u) := by
  have hba : 0 < b - a := sub_pos.2 hγ.lt
  have hγ' := hγ.toUnit scaleInvariant_isFutureCausal
  have h0 : γ ((b - a) * 0 + a) = γ a := by simp
  have h1 : γ ((b - a) * 1 + a) = γ b := by simp
  obtain ⟨u, hu, -, h, hh, hhc, hrep⟩ := exists_expMap_reparam_unit hg hγ' (by
    simp only [h0, h1]
    exact hc)
  have hφ : MapsTo (fun t => (t - a) / (b - a)) (Icc a b) (Icc 0 1) := fun t ht =>
    ⟨div_nonneg (by linarith [ht.1]) hba.le, (div_le_one hba).2 (by linarith [ht.2])⟩
  refine ⟨u, hu, h ∘ fun t => (t - a) / (b - a), hh.comp ?_ hφ,
    hhc.comp (by fun_prop) hφ, fun r hr => ?_⟩
  · exact fun x _ y _ hxy => div_le_div_of_nonneg_right (by linarith) hba.le
  have hr' : γ ((b - a) * ((r - a) / (b - a)) + a) = γ r := by
    congr 1
    field_simp
    ring
  obtain ⟨hd, he⟩ := hrep _ (hφ hr)
  simp only [h0, hr'] at hd he
  exact ⟨hd, he⟩

namespace Facts

/-- A causal curve from `p` to `q` that is not a null pregeodesic can be replaced by a
timelike curve. O'Neill, Semi-Riemannian geometry, Proposition 10.46, p. 294. -/
theorem chronLT_of_not_nullPregeodesic {g : MatrixField n} {Y : E n → E n}
    (hg : IsSpacetime g Y) {γ : ℝ → E n} (hγ : IsPathOn (IsFutureCausal g Y) 0 1 γ)
    (hnot : ¬ IsNullPregeodesicOn g 0 1 γ) :
    ChronLT g Y (γ 0) (γ 1) := by
  by_contra hc
  obtain ⟨u, -, hnull, h, hh, hhc, hrep⟩ := exists_expMap_reparam_unit hg hγ hc
  apply hnot
  obtain ⟨hS, hS0⟩ := isGeodesic_expMap_smul hg (γ 0) u
  have h0 : (0 : ℝ) ∈ {r : ℝ | InExpDomain g (γ 0) (r • u)} := by
    simpa using inExpDomain_zero (g := g) (γ 0)
  refine isNullPregeodesicOn_iff.2 ⟨_, _, h, hS, fun z hz => ?_, hh, hhc, ?_,
    fun r hr => (hrep r hr).2⟩
  · rw [hS.form_deriv_eq hg ((ordConnected_inExpDomain_smul hg _ u).uIcc_subset h0 hz)
      ordConnected_uIcc right_mem_uIcc left_mem_uIcc, hS0]
    simpa [expMap_zero hg] using hnull
  · rintro _ ⟨r, hr, rfl⟩
    exact (hrep r hr).1

end Facts

end

end LorentzianCalderon
