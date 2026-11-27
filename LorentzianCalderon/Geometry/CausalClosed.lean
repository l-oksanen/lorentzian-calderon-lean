module

public import LorentzianCalderon.Causal.Chron

public section

/-!
# Closedness of the causal relation

`J⁺(p)` is closed: a limit `x` of points of `J⁺(p)` lies in `I⁻(q)` for some `q`, and so do the
points near it, which therefore lie in the compact diamond `J⁺(p) ∩ J⁻(q)`. The causal relation
is closed (`Facts.isClosed_causalLE`): if `pₖ ≤ xₖ` converge to `(p, x)`, then every `a ≪ p`
satisfies `a ≪ pₖ` for large `k`, hence `a ≤ x` by closedness of `J⁺(a)`, and `p ≤ x` by
closedness of `J⁻(x)`, as such `a` approach `p`. Hence `J^±(K)` is closed for compact `K`, and
`J⁺(K) ∩ J⁻(K')`, a closed subset of a finite union of causal diamonds, is compact for compact
`K, K'`.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Filter

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n}

/-- Every point is a limit of points of its chronological past. -/
theorem exists_chronLT_dist_lt (hg : IsSpacetime g Y) (x : E n) {ε : ℝ} (hε : 0 < ε) :
    ∃ p, dist p x < ε ∧ ChronLT g Y p x := by
  have hYt := hg.globallyHyperbolic.timeOrientation.timelike x
  obtain ⟨ε₀, hε₀, hεP⟩ := exists_isFutureTimelike_of_dist_lt hg (w := Y x) ⟨hYt, hYt⟩
  set m := min ε₀ ε
  have hm : 0 < m := lt_min hε₀ hε
  set s := m / (2 * (‖Y x‖ + 1))
  have hs : 0 < s := by positivity
  have hsY : s * ‖Y x‖ < m := by
    have : s * (‖Y x‖ + 1) = m / 2 := by
      simp only [s]
      field_simp
    nlinarith [norm_nonneg (Y x)]
  refine ⟨x - s • Y x, ?_, ?_⟩
  · rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg hs.le]
    exact hsY.trans_le (min_le_right _ _)
  have := chronLT_of_isPathOn (isPathOn_line (x := x - s • Y x) (v := Y x) hs fun r hr =>
    hεP _ _ ?_ (by simpa using hε₀))
  · simpa using this
  · rw [dist_eq_norm, show x - s • Y x + r • Y x - x = (r - s) • Y x by
      simp only [sub_smul]; abel, norm_smul, Real.norm_of_nonpos (by linarith [hr.2])]
    nlinarith [norm_nonneg (Y x), hr.1, min_le_left ε₀ ε]

theorem isClosed_causalFuture (hg : IsSpacetime g Y) (p : E n) :
    IsClosed (causalFuture g Y p) := by
  refine isClosed_of_closure_subset fun x hx => ?_
  obtain ⟨q, hq⟩ := exists_chronLT_right hg x
  have hD := (hg.globallyHyperbolic.compact_diamond p q).isClosed
  have h1 : x ∈ closure (chronPast g Y q ∩ causalFuture g Y p) :=
    (isOpen_chronPast hg q).inter_closure ⟨mem_chronPast.2 hq, hx⟩
  have h2 : closure (chronPast g Y q ∩ causalFuture g Y p) ⊆
      causalFuture g Y p ∩ causalPast g Y q :=
    closure_minimal
      (fun y hy => ⟨hy.2, mem_causalPast.2 (ChronLT.causalLE (mem_chronPast.1 hy.1))⟩) hD
  exact (h2 h1).1

theorem isClosed_causalPast (hg : IsSpacetime g Y) (p : E n) :
    IsClosed (causalPast g Y p) := by
  rw [← causalFuture_neg]
  exact isClosed_causalFuture hg.neg p

/-- The causal relation is closed. O'Neill, Semi-Riemannian geometry, Lemma 14.22, p. 412, for
globally hyperbolic spacetimes in the traditional sense (Hounnonkpe–Minguzzi, Theorem 2.8);
derived here from the compactness of causal diamonds. -/
theorem Facts.isClosed_causalLE (hg : IsSpacetime g Y) :
    IsClosed { pq : E n × E n | CausalLE g Y pq.1 pq.2 } := by
  refine isClosed_of_closure_subset fun ⟨p, x⟩ hpx => ?_
  by_contra hn
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isClosed_causalPast hg x).isOpen_compl p
    fun h => hn (mem_causalPast.1 h)
  obtain ⟨a, hap, ha⟩ := exists_chronLT_dist_lt hg p hε
  refine hball (Metric.mem_ball.2 hap)
    (mem_causalPast.2 (mem_causalFuture.1 ((isClosed_causalFuture hg a).closure_subset ?_)))
  refine mem_closure_iff_nhds.2 fun M hM => ?_
  obtain ⟨⟨p', x'⟩, ⟨hp', hx'⟩, hR⟩ := mem_closure_iff_nhds.1 hpx _
    (prod_mem_nhds ((Facts.isOpen_chronFuture hg a).mem_nhds (mem_chronFuture.2 ha)) hM)
  exact ⟨x', hx', mem_causalFuture.2 ((ChronLT.causalLE (mem_chronFuture.1 hp')).trans hR)⟩

theorem isClosed_causalFutureSet (hg : IsSpacetime g Y) {K : Set (E n)} (hK : IsCompact K) :
    IsClosed (causalFutureSet g Y K) := by
  refine IsSeqClosed.isClosed fun {q'} {q} hq' hlim => ?_
  have hq'' : ∀ m, ∃ p ∈ K, CausalLE g Y p (q' m) := fun m => by
    simpa [mem_causalFutureSet, mem_causalFuture] using hq' m
  choose p' hpK hpq using hq''
  obtain ⟨p, hp, φ, hφ, hlimp⟩ := hK.tendsto_subseq hpK
  have : CausalLE g Y p q :=
    (Facts.isClosed_causalLE hg).mem_of_tendsto (hlimp.prodMk_nhds (hlim.comp hφ.tendsto_atTop))
      (Eventually.of_forall fun m => hpq (φ m))
  exact mem_causalFutureSet.2 ⟨p, hp, mem_causalFuture.2 this⟩

theorem isClosed_causalPastSet (hg : IsSpacetime g Y) {K : Set (E n)} (hK : IsCompact K) :
    IsClosed (causalPastSet g Y K) := by
  rw [← causalFutureSet_neg]
  exact isClosed_causalFutureSet hg.neg hK

/-- `J⁺(K) ∩ J⁻(K')` is compact for compact `K, K'`. Bär–Ginoux–Pfäffle, Wave equations on
Lorentzian manifolds and quantization, Lemma A.5.7, p. 176. -/
theorem Facts.isCompact_causalFutureSet_inter_causalPastSet (hg : IsSpacetime g Y)
    {K K' : Set (E n)} (hK : IsCompact K) (hK' : IsCompact K') :
    IsCompact (causalFutureSet g Y K ∩ causalPastSet g Y K') := by
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_superset_causalFutureSet_inter_causalPastSet hg hK hK'
  exact hC.of_isClosed_subset ((isClosed_causalFutureSet hg hK).inter
    (isClosed_causalPastSet hg hK')) hsub

end

end LorentzianCalderon
