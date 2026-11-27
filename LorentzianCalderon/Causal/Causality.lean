module

public import LorentzianCalderon.Causal.Chronology
public import LorentzianCalderon.Geometry.NullPregeodesic

public section

/-!
# Causality

The causal relation is antisymmetric (`causalLE_antisymm`), after Hounnonkpe and Minguzzi,
Class. Quantum Grav. 36 (2019), 197001, Theorem 2.7, whose dimension argument is made local
here.

Suppose `p ≤ q ≤ p` with `p ≠ q`, and let `ℓ` be the causal loop `p → q → p`. By chronology no
two points of `ℓ` are chronologically related, so `ℓ` is a monotone reparametrization of a null
ray `z ↦ exp_p (z u)` (`exists_expMap_reparam`). Let `F = I⁺(p)` and `b ∈ ∂F`. Then `p ≤ b`,
`b ∉ F`, and `q ≪ b` would give `p ≪ b`; so the causal curve `ℓ` followed by a causal curve from
`p` to `b` is, from `q` on, a reparametrized null ray from `q`, which overlaps `ℓ` and hence
continues the ray from `p` (`exists_reparam_of_overlap`). So `∂F` lies on the single smooth
curve `z ↦ exp_p (z u)` (`frontier_chronFuture_subset_ray`).

On the other hand, every line `τ ↦ z + τ Y_p` with `z` near `p` runs from `I⁻(p)`, which is
disjoint from `F`, into `F`, so it meets `∂F`. Hence the map `(μ, τ) ↦ exp_p (μ u) + τ Y_p`, a
smooth map of a plane into `ℝ^{1+n}`, covers a ball around `p`. Since `1 + n ≥ 3`, the plane is
a null set, and so is its image (`addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`):
a contradiction.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Filter MeasureTheory

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n}

/-- If `p ≤ q ≤ p` with `p ≠ q`, the frontier of `I⁺(p)` lies on one ray from `p`. -/
theorem frontier_chronFuture_subset_ray (hg : IsSpacetime g Y) {p q : E n}
    (hpq : CausalLE g Y p q) (hqp : CausalLE g Y q p) (hne : p ≠ q) :
    ∃ u : E n, frontier (chronFuture g Y p) ⊆
      (fun z : ℝ => expMap g p (z • u)) '' {z | InExpDomain g p (z • u)} := by
  classical
  obtain ⟨γ₁, h₁, h₁0, h₁1⟩ := hpq.exists_isPathOn hne (zero_lt_one' ℝ)
  obtain ⟨γ₂, h₂, h₂1, h₂2⟩ := hqp.exists_isPathOn (Ne.symm hne) (by norm_num : (1 : ℝ) < 2)
  set ℓ : ℝ → E n := fun t => if t ≤ 1 then γ₁ t else γ₂ t
  have hℓ : IsPathOn (IsFutureCausal g Y) 0 2 ℓ := h₁.append h₂ (by rw [h₁1, h₂1])
  have hℓ0 : ℓ 0 = p := by simp [ℓ, h₁0]
  have hℓ1 : ℓ 1 = q := by simp [ℓ, h₁1]
  have hℓ2 : ℓ 2 = p := by norm_num [ℓ, h₂2]
  obtain ⟨u, hu, h, hh, hhc, hrep⟩ :=
    exists_expMap_reparam hg hℓ (by rw [hℓ0, hℓ2]; exact not_chronLT_self hg p)
  refine ⟨u, fun b hb => ?_⟩
  have hbF : b ∉ chronFuture g Y p := by
    have := hb.2
    rwa [(Facts.isOpen_chronFuture hg p).interior_eq] at this
  have hpb : CausalLE g Y p b := mem_causalFuture.1 <| (isClosed_causalFuture hg p).closure_subset
    (closure_mono (chronFuture_subset_causalFuture p) hb.1)
  by_cases hbp : b = p
  · exact ⟨0, by simpa using inExpDomain_zero (g := g) p, by simp [expMap_zero hg, hbp]⟩
  obtain ⟨σ, hσ, hσ2, hσ3⟩ := hpb.exists_isPathOn (Ne.symm hbp) (by norm_num : (2 : ℝ) < 3)
  set α : ℝ → E n := fun t => if t ≤ 2 then ℓ t else σ t
  have hα : IsPathOn (IsFutureCausal g Y) 0 3 α := hℓ.append hσ (by rw [hℓ2, hσ2])
  have hαℓ : ∀ t ≤ 2, α t = ℓ t := fun t ht => by simp [α, ht]
  have hα3 : α 3 = b := by norm_num [α, hσ3]
  have hnot : ¬ ChronLT g Y (α 1) (α 3) := by
    rw [hαℓ 1 (by norm_num), hℓ1, hα3]
    exact fun hqb => hbF (mem_chronFuture.2 (hpq.trans_chronLT hg hqb))
  obtain ⟨v, hv, lam, hlam, hlamc, hrep'⟩ :=
    exists_expMap_reparam hg (hα.restrict zero_le_one (by norm_num) le_rfl) hnot
  have hrepα : ∀ r ∈ Icc (0 : ℝ) 2, InExpDomain g (α 0) (h r • u) ∧
      α r = expMap g (α 0) (h r • u) := fun r hr => by
    rw [hαℓ 0 (by norm_num), hαℓ r hr.2]
    exact hrep r hr
  obtain ⟨h', -, -, hrep''⟩ := exists_reparam_of_overlap hg hα zero_le_one one_lt_two
    (by norm_num) hu hh hhc hrepα hv hlam hlamc hrep'
  obtain ⟨hd, he⟩ := hrep'' 3 ⟨by norm_num, le_rfl⟩
  rw [hαℓ 0 (by norm_num), hℓ0] at hd he
  rw [hα3] at he
  exact ⟨h' 3, hd, he.symm⟩

/-- The plane spanned by the first two coordinate vectors is a proper subspace of `ℝ^{1+n}`,
`n ≥ 2`. -/
theorem span_single_ne_top (hn : 2 ≤ n) (i j : Fin (n + 1)) :
    Submodule.span ℝ (range ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single j 1]) ≠
      ⊤ := by
  intro htop
  have h1 := finrank_range_le_card (R := ℝ)
    ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single j (1 : ℝ)]
  rw [Set.finrank, htop, finrank_top, finrank_euclideanSpace_fin] at h1
  simp at h1
  omega

/-- Causality: the causal relation is antisymmetric. Hounnonkpe and Minguzzi, Globally
hyperbolic spacetimes can be defined without the 'causal' condition, Class. Quantum Grav. 36
(2019), 197001, Theorem 2.7, for spacetimes of dimension at least `3` with compact causal
diamonds that are not compact. -/
theorem causalLE_antisymm (hg : IsSpacetime g Y) {p q : E n} (hpq : CausalLE g Y p q)
    (hqp : CausalLE g Y q p) : p = q := by
  classical
  by_contra hne
  obtain ⟨u, hR⟩ := frontier_chronFuture_subset_ray hg hpq hqp hne
  set c : ℝ → E n := fun z => expMap g p (z • u)
  set D := {z : ℝ | InExpDomain g p (z • u)}
  obtain ⟨hS, -⟩ := isGeodesic_expMap_smul hg p u
  set F := chronFuture g Y p
  have hFo : IsOpen F := Facts.isOpen_chronFuture hg p
  set e := Y p
  have hYt := hg.globallyHyperbolic.timeOrientation.timelike p
  obtain ⟨ε, hε, hεP⟩ := exists_isFutureTimelike_of_dist_lt hg (w := e) ⟨hYt, hYt⟩
  set k := ε / (2 * (‖e‖ + 1))
  have hk : 0 < k := by positivity
  have hke : k * ‖e‖ < ε := by
    have : k * (‖e‖ + 1) = ε / 2 := by
      simp only [k]
      field_simp
    nlinarith [norm_nonneg e]
  have hline : ∀ a b, -k ≤ a → a < b → b ≤ k → ChronLT g Y (p + a • e) (p + b • e) := by
    intro a b ha hab hb
    refine chronLT_of_isPathOn (isPathOn_line hab fun t ht => hεP _ _ ?_ (by simpa using hε))
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    calc |t| * ‖e‖ ≤ k * ‖e‖ :=
          mul_le_mul_of_nonneg_right (abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩)
            (norm_nonneg e)
      _ < ε := hke
  have hminus : ChronLT g Y (p + (-k) • e) p := by
    simpa using hline (-k) 0 le_rfl (by linarith) hk.le
  have hplus : p + k • e ∈ F := by
    simpa [F, mem_chronFuture] using hline 0 k (by linarith) hk le_rfl
  obtain ⟨δ₁, hδ₁, hball₁⟩ := Metric.isOpen_iff.1 (isOpen_chronPast hg p) _ (mem_chronPast.2 hminus)
  obtain ⟨δ₂, hδ₂, hball₂⟩ := Metric.isOpen_iff.1 hFo _ hplus
  set δ := min δ₁ δ₂
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  have hn := hg.two_le
  set i₁ : Fin (n + 1) := ⟨1, by omega⟩
  have hi₁ : i₁ ≠ 0 := by simp [i₁, Fin.ext_iff]
  set P := Submodule.span ℝ (range ![EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ),
    EuclideanSpace.single i₁ 1])
  set G : E n → E n := fun x => c (x 0) + x i₁ • e
  set s := (P : Set (E n)) ∩ {x | x 0 ∈ D}
  have hcover : Metric.ball p δ ⊆ G '' s := by
    intro z hz
    rw [Metric.mem_ball] at hz
    set f : ℝ → E n := fun τ => z + τ • e
    have hf : Continuous f := by fun_prop
    have hfF : f k ∈ F := hball₂ <| by
      rw [Metric.mem_ball, dist_eq_norm, show f k - (p + k • e) = z - p by simp [f],
        ← dist_eq_norm]
      exact hz.trans_le (min_le_right _ _)
    have hfP : f (-k) ∉ F := by
      have : ChronLT g Y (f (-k)) p := mem_chronPast.1 <| hball₁ <| by
        rw [Metric.mem_ball, dist_eq_norm, show f (-k) - (p + (-k) • e) = z - p by
          simp [f], ← dist_eq_norm]
        exact hz.trans_le (min_le_left _ _)
      exact fun h => not_chronLT_of_chronLT hg (mem_chronFuture.1 h) this
    obtain ⟨τ, -, hτ1, hτ2⟩ := isPreconnected_closed_iff.1 (isPreconnected_Icc (a := -k) (b := k))
      (f ⁻¹' closure F) (f ⁻¹' Fᶜ) (isClosed_closure.preimage hf)
      (hFo.isClosed_compl.preimage hf)
      (fun τ _ => (em (f τ ∈ F)).elim (fun h => Or.inl (subset_closure h)) Or.inr)
      ⟨k, ⟨by linarith, le_rfl⟩, subset_closure hfF⟩ ⟨-k, ⟨le_rfl, by linarith⟩, hfP⟩
    have hfr : f τ ∈ frontier F := by
      rw [hFo.frontier_eq]
      exact ⟨hτ1, hτ2⟩
    obtain ⟨μ, hμ, hμe⟩ := hR hfr
    refine ⟨μ • EuclideanSpace.single 0 1 + (-τ) • EuclideanSpace.single i₁ 1, ⟨?_, ?_⟩, ?_⟩
    · exact P.add_mem (P.smul_mem _ (Submodule.subset_span ⟨0, rfl⟩))
        (P.smul_mem _ (Submodule.subset_span ⟨1, rfl⟩))
    · simpa [hi₁.symm] using hμ
    · simp only [G, c] at hμe ⊢
      simp [hi₁, hi₁.symm, hμe, f]
  have hdiff : DifferentiableOn ℝ G s := by
    intro x hx
    have hc : DifferentiableAt ℝ c (x 0) :=
      (hS.smooth.differentiableOn (by simp)).differentiableAt (hS.isOpen.mem_nhds hx.2)
    have h0 : DifferentiableAt ℝ (fun y : E n => y 0) x :=
      (EuclideanSpace.proj (0 : Fin (n + 1)) : E n →L[ℝ] ℝ).differentiableAt
    have h1 : DifferentiableAt ℝ (fun y : E n => y i₁) x :=
      (EuclideanSpace.proj i₁ : E n →L[ℝ] ℝ).differentiableAt
    exact ((hc.comp x h0).add (h1.smul_const e)).differentiableWithinAt
  have hnull : volume (G '' s) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hdiff
      (measure_mono_null inter_subset_left (Measure.addHaar_submodule volume P
        (span_single_ne_top hn 0 i₁)))
  exact (Metric.measure_ball_pos volume p hδ).ne'
    (measure_mono_null hcover hnull)

end

end LorentzianCalderon
