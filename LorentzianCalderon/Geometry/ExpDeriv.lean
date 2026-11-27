module

public import LorentzianCalderon.Geometry.GeodesicExtension
public import LorentzianCalderon.Geometry.Gauss

public section

/-!
# The derivative of the exponential map

The map `(y, w) ↦ (y, exp_y w)` and its derivative, the velocity `d(exp_y)_w w` of the radial
geodesic `t ↦ exp_y (t w)` at `t = 1`, and the Gauss lemma in the form
`g(d(exp_y)_w w, d(exp_y)_w ξ) = g_y(w, ξ)` for all `w` in the domain, `w = 0` included.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Filter

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n}

/-- If a curve with nonzero velocity `c'` at `x` is a monotone continuous reparametrization of a
curve `σ` with nonzero velocity `σ'` at `h x`, then `c'` is a positive multiple of `σ'`. -/
theorem exists_pos_smul_of_eq_comp {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {c σ : ℝ → V} {h : ℝ → ℝ} {α β x : ℝ} {c' σ' : V} (hαβ : α < β) (hx : x ∈ Icc α β)
    (hc : HasDerivWithinAt c c' (Icc α β) x) (hσ : HasStrictDerivAt σ σ' (h x))
    (hhm : MonotoneOn h (Icc α β)) (hhc : ContinuousWithinAt h (Icc α β) x)
    (heq : ∀ t ∈ Icc α β, c t = σ (h t)) (hc' : c' ≠ 0) (hσ' : σ' ≠ 0) :
    ∃ κ > (0 : ℝ), c' = κ • σ' := by
  obtain ⟨ℓ₀, -, hℓ₀⟩ := exists_dual_vector ℝ σ' (norm_ne_zero_iff.2 hσ')
  set ℓ : V →L[ℝ] ℝ := ‖σ'‖⁻¹ • ℓ₀
  have hℓ : ℓ σ' = 1 := by simp [ℓ, hℓ₀, norm_ne_zero_iff.2 hσ']
  have hf : HasStrictDerivAt (fun s => ℓ (σ s)) 1 (h x) := by
    convert ℓ.hasStrictFDerivAt.comp_hasStrictDerivAt (h x) hσ using 1 <;>
      first | rfl | exact hℓ.symm
  set ψ := hf.localInverse _ _ _ one_ne_zero
  have hψ : HasDerivAt ψ 1 (ℓ (c x)) := by
    simpa [heq x hx] using (hf.to_localInverse one_ne_zero).hasDerivAt
  have hev : h =ᶠ[𝓝[Icc α β] x] fun t => ψ (ℓ (c t)) := by
    filter_upwards [hhc.tendsto.eventually (hf.eventually_left_inverse one_ne_zero),
      self_mem_nhdsWithin] with t ht hts
    rw [heq t hts]
    exact ht.symm
  have hh : HasDerivWithinAt h (ℓ c') (Icc α β) x := by
    have := hψ.comp_hasDerivWithinAt x (ℓ.hasFDerivAt.comp_hasDerivWithinAt x hc)
    rw [one_mul] at this
    exact this.congr_of_eventuallyEq hev (hev.self_of_nhdsWithin hx)
  have hcomp : HasDerivWithinAt c (ℓ c' • σ') (Icc α β) x :=
    (hσ.hasDerivAt.scomp_hasDerivWithinAt x hh).congr_of_mem (fun t ht => heq t ht) hx
  have hu := uniqueDiffOn_Icc hαβ x hx
  have hcκ : c' = ℓ c' • σ' := hu.eq_deriv _ hc hcomp
  refine ⟨ℓ c', lt_of_le_of_ne ?_ fun h0 => hc' ?_, hcκ⟩
  · rw [← hh.derivWithin hu]
    exact hhm.derivWithin_nonneg
  · rw [hcκ, ← h0, zero_smul]


theorem InExpDomain.causalLE (hg : IsSpacetime g Y) {y w : E n} (h : InExpDomain g y w)
    (hw : IsFutureCausal g Y y w) : CausalLE g Y y (expMap g y w) := by
  obtain ⟨ε, hε, hγ, -, h0, h0'⟩ := h.isGeodesic_expMap_smul hg
  have hsub : Icc (0 : ℝ) 1 ⊆ Ioo (-ε) (1 + ε) := fun r hr =>
    ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hfut : IsFutureCausal g Y (expMap g y ((0 : ℝ) • w))
      (deriv (fun t : ℝ => expMap g y (t • w)) 0) := by rwa [h0, h0']
  have := hγ.causalLE zero_le_one hsub fun r hr =>
    hγ.isFutureCausal hg hsub ordConnected_Icc ⟨le_rfl, zero_le_one⟩ hfut hr
  rwa [h0, one_smul] at this

theorem InExpDomain.chronLT (hg : IsSpacetime g Y) {y w : E n} (h : InExpDomain g y w)
    (hw : IsFutureTimelike g Y y w) : ChronLT g Y y (expMap g y w) := by
  obtain ⟨ε, hε, hγ, -, h0, h0'⟩ := h.isGeodesic_expMap_smul hg
  have hsub : Icc (0 : ℝ) 1 ⊆ Ioo (-ε) (1 + ε) := fun r hr =>
    ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hfut : IsFutureTimelike g Y (expMap g y ((0 : ℝ) • w))
      (deriv (fun t : ℝ => expMap g y (t • w)) 0) := by rwa [h0, h0']
  have := hγ.chronLT zero_lt_one hsub fun r hr =>
    hγ.isFutureTimelike hg hsub ordConnected_Icc ⟨le_rfl, zero_le_one⟩ hfut hr
  rwa [h0, one_smul] at this


/-! ### The map `(y, w) ↦ (y, exp_y w)` -/

/-- The map `𝐞(y, w) = (y, exp_y w)`. -/
def expPair (g : MatrixField n) (p : E n × E n) : E n × E n := (p.1, expMap g p.1 p.2)

theorem expPair_def (g : MatrixField n) (p : E n × E n) :
    expPair g p =
      (p.1, expMap g p.1 p.2) := by rfl

theorem expPair_mk (g : MatrixField n) (y v : E n) : expPair g (y, v) = (y, expMap g y v) := by
  rfl

theorem expPair_fst (g : MatrixField n) (p : E n × E n) : (expPair g p).1 = p.1 := by rfl

theorem expPair_snd (g : MatrixField n) (p : E n × E n) : (expPair g p).2 = expMap g p.1 p.2 := by
  rfl

theorem contDiffOn_expPair (hg : IsSpacetime g Y) :
    ContDiffOn ℝ ∞ (expPair g) { p | InExpDomain g p.1 p.2 } :=
  contDiffOn_fst.prodMk (contDiffOn_expMap hg)

theorem hasFDerivAt_expMap_prod (hg : IsSpacetime g Y) {p : E n × E n}
    (hp : InExpDomain g p.1 p.2) :
    HasFDerivAt (fun q : E n × E n => expMap g q.1 q.2)
      (fderiv ℝ (fun q : E n × E n => expMap g q.1 q.2) p) p :=
  (((contDiffOn_expMap hg).differentiableOn (by simp)).differentiableAt
    ((isOpen_expDomain hg).mem_nhds hp)).hasFDerivAt

theorem hasFDerivAt_expMap (hg : IsSpacetime g Y) {p : E n × E n}
    (hp : InExpDomain g p.1 p.2) :
    HasFDerivAt (expMap g p.1)
      ((fderiv ℝ (fun q : E n × E n => expMap g q.1 q.2) p).comp
        (ContinuousLinearMap.inr ℝ (E n) (E n))) p.2 := by
  have h : HasFDerivAt (fun q : E n × E n => expMap g q.1 q.2)
      (fderiv ℝ (fun q : E n × E n => expMap g q.1 q.2) p) (p.1, p.2) :=
    hasFDerivAt_expMap_prod hg hp
  exact h.comp p.2 (hasFDerivAt_prodMk_right p.1 p.2)

/-- `𝐞` has invertible derivative where `exp_y` does. -/
theorem exists_hasFDerivAt_expPair (hg : IsSpacetime g Y) {p : E n × E n}
    (hp : InExpDomain g p.1 p.2) (hbij : Function.Bijective (fderiv ℝ (expMap g p.1) p.2)) :
    ∃ f' : (E n × E n) ≃L[ℝ] (E n × E n), HasFDerivAt (expPair g) (f' : _ →L[ℝ] _) p := by
  set L := fderiv ℝ (fun q : E n × E n => expMap g q.1 q.2) p
  set M := (ContinuousLinearMap.fst ℝ (E n) (E n)).prod L
  have hM : HasFDerivAt (expPair g) M p := hasFDerivAt_fst.prodMk (hasFDerivAt_expMap_prod hg hp)
  have hpart := (hasFDerivAt_expMap hg hp).fderiv
  have hinj : Function.Injective M := by
    refine (injective_iff_map_eq_zero M).2 ?_
    rintro ⟨a, c⟩ hac
    simp only [M, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
      Prod.mk_eq_zero] at hac
    obtain ⟨rfl, hc⟩ := hac
    have : fderiv ℝ (expMap g p.1) p.2 c = 0 := by
      rw [hpart]
      simpa using hc
    have hc0 : c = 0 := hbij.1 (by rw [this, map_zero])
    simp [hc0]
  refine ⟨(LinearEquiv.ofInjectiveEndo (M : (E n × E n) →ₗ[ℝ] (E n × E n))
    hinj).toContinuousLinearEquiv, ?_⟩
  convert hM using 1
  ext x <;> simp [LinearEquiv.coe_ofInjectiveEndo]

/-- Conversely, invertibility of the derivative of `𝐞` gives that of `exp_y`. -/
theorem bijective_fderiv_expMap (hg : IsSpacetime g Y) {p : E n × E n}
    (hp : InExpDomain g p.1 p.2) {f' : (E n × E n) ≃L[ℝ] (E n × E n)}
    (hf' : HasFDerivAt (expPair g) (f' : _ →L[ℝ] _) p) :
    Function.Bijective (fderiv ℝ (expMap g p.1) p.2) := by
  set L := fderiv ℝ (fun q : E n × E n => expMap g q.1 q.2) p
  have hM : HasFDerivAt (expPair g) ((ContinuousLinearMap.fst ℝ (E n) (E n)).prod L) p :=
    hasFDerivAt_fst.prodMk (hasFDerivAt_expMap_prod hg hp)
  have heq := hf'.unique hM
  rw [(hasFDerivAt_expMap hg hp).fderiv]
  have hinj : Function.Injective (L.comp (ContinuousLinearMap.inr ℝ (E n) (E n))) := by
    intro a c hac
    have h1 : f' (0, a) = f' (0, c) := by
      rw [← ContinuousLinearEquiv.coe_coe, heq]
      simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst']
      simpa using hac
    simpa using f'.injective h1
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := (L.comp
    (ContinuousLinearMap.inr ℝ (E n) (E n)) : E n →ₗ[ℝ] E n))).1 hinj⟩

/-- The velocity of `t ↦ exp_y (t w)` at `t = 1` is `d(exp_y)_w w`. -/
theorem hasDerivAt_expMap_smul_one (hg : IsSpacetime g Y) {y w : E n} (h : InExpDomain g y w) :
    HasDerivAt (fun t : ℝ => expMap g y (t • w)) (fderiv ℝ (expMap g y) w w) 1 := by
  have hd : HasFDerivAt (expMap g y) (fderiv ℝ (expMap g y) w) ((1 : ℝ) • w) := by
    rw [one_smul]
    exact (hasFDerivAt_expMap hg (p := (y, w)) h).differentiableAt.hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => t • w) ((1 : ℝ) • w) 1 := (hasDerivAt_id 1).smul_const w
  have := hd.comp_hasDerivAt (1 : ℝ) hl
  rw [one_smul] at this
  exact this


/-- `d(exp_y)_0` is the identity. -/
theorem fderiv_expMap_zero (hg : IsSpacetime g Y) (y : E n) :
    fderiv ℝ (expMap g y) 0 = ContinuousLinearMap.id ℝ (E n) := by
  have hd : HasFDerivAt (expMap g y) (fderiv ℝ (expMap g y) 0) 0 :=
    (hasFDerivAt_expMap hg (p := (y, 0)) (inExpDomain_zero y)).differentiableAt.hasFDerivAt
  ext1 v
  have hl : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  have h0 : HasFDerivAt (expMap g y) (fderiv ℝ (expMap g y) 0) ((0 : ℝ) • v) := by
    rwa [zero_smul]
  have := (h0.comp_hasDerivAt (0 : ℝ) hl).deriv
  rw [Function.comp_def, (isGeodesic_expMap_smul hg y v).2] at this
  exact this.symm

/-- The Gauss lemma `g(d(exp_y)_w w, d(exp_y)_w ξ) = g_y(w, ξ)`, including `w = 0`. -/
theorem form_fderiv_expMap_radial (hg : IsSpacetime g Y) {y w : E n} (h : InExpDomain g y w)
    (ξ : E n) :
    form (g (expMap g y w)) (fderiv ℝ (expMap g y) w w) (fderiv ℝ (expMap g y) w ξ) =
      form (g y) w ξ :=
  Facts.gauss hg h ξ

/-- The radial velocity `d(exp_y)_w w` is future-directed causal if `w` is. -/
theorem InExpDomain.isFutureCausal_fderiv (hg : IsSpacetime g Y) {y w : E n}
    (h : InExpDomain g y w) (hw : IsFutureCausal g Y y w) :
    IsFutureCausal g Y (expMap g y w) (fderiv ℝ (expMap g y) w w) := by
  obtain ⟨ε, hε, hγ, -, h0, h0'⟩ := h.isGeodesic_expMap_smul hg
  have hsub : Icc (0 : ℝ) 1 ⊆ Ioo (-ε) (1 + ε) := fun r hr =>
    ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hfut : IsFutureCausal g Y (expMap g y ((0 : ℝ) • w))
      (deriv (fun t : ℝ => expMap g y (t • w)) 0) := by rwa [h0, h0']
  have := hγ.isFutureCausal hg hsub ordConnected_Icc ⟨le_rfl, zero_le_one⟩ hfut
    ⟨zero_le_one, le_rfl⟩
  rwa [(hasDerivAt_expMap_smul_one hg h).deriv, one_smul] at this

/-- The radial velocity `d(exp_y)_w w` is future-directed timelike if `w` is. -/
theorem InExpDomain.isFutureTimelike_fderiv (hg : IsSpacetime g Y) {y w : E n}
    (h : InExpDomain g y w) (hw : IsFutureTimelike g Y y w) :
    IsFutureTimelike g Y (expMap g y w) (fderiv ℝ (expMap g y) w w) := by
  obtain ⟨ε, hε, hγ, -, h0, h0'⟩ := h.isGeodesic_expMap_smul hg
  have hsub : Icc (0 : ℝ) 1 ⊆ Ioo (-ε) (1 + ε) := fun r hr =>
    ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hfut : IsFutureTimelike g Y (expMap g y ((0 : ℝ) • w))
      (deriv (fun t : ℝ => expMap g y (t • w)) 0) := by rwa [h0, h0']
  have := hγ.isFutureTimelike hg hsub ordConnected_Icc ⟨le_rfl, zero_le_one⟩ hfut
    ⟨zero_le_one, le_rfl⟩
  rwa [(hasDerivAt_expMap_smul_one hg h).deriv, one_smul] at this

end

end LorentzianCalderon
