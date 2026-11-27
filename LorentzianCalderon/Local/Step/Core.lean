module

public import LorentzianCalderon.Local.Step.Weighted

public section

/-!
# The local continuation step: Steps 1–3

The energy inequalities on the lens `L = L_{R/2}` applied to `w̄_{a,s}` (integrated in `s`) and
to `φ̄_a`, combined with the pointwise bounds of `Bounds.lean` and the absorption argument
`absorb`: for some `σ`, the weighted norms of `ḡ`, `θ̄`, `φ̄_a` vanish, hence `ḡ = 0`, `θ̄ = 0`
and `φ'_a ∘ Ψ = φ_a` on `V° ∩ {ψ < τ}`.
-/

namespace LorentzianCalderon

noncomputable section
open Set Matrix Filter MeasureTheory Metric
open scoped ContDiff Topology

variable {n : ℕ} {ι : Type*}

namespace StepData

variable {S : StepData n ι} (hS : S.Hyp)
include hS

namespace Ball

variable {R : ℝ} (hB : S.Ball R)
include hB

theorem setting' : StepEnergySetting (ball S.q₀ R) S.g S.Y S.ψ S.ψt S.τ (S.τ - (R / 2) ^ 2) :=
  setting hS hB (half_pos hB).le (half_lt hB)

theorem measurableSet_L_superlevel (a : ι) (s : ℝ) :
    MeasurableSet (S.L R (R / 2) ∩ {x | s < S.φ a x}) := by
  have e : S.L R (R / 2) ∩ {x | s < S.φ a x} =
      S.L R (R / 2) ∩ (S.V ∩ S.φ a ⁻¹' Ioi s) := by
    ext x
    exact ⟨fun h => ⟨h.1, L_subset_V hB h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  rw [e]
  exact (measurableSet_L hS hB).inter
    ((hS.continuousOn_φ a).isOpen_inter_preimage hS.isOpen_V isOpen_Ioi).measurableSet

/-- The inner integral of the integrated energy inequality, bounded by the comparison
coefficients. -/
theorem inner_le (a : ι) {s₁ s₂ : ℝ} (hJ : Icc s₁ s₂ ⊆ S.J) {Kb : ℝ} (hKb0 : 0 ≤ Kb)
    (hKb : ∀ s ∈ Icc s₁ s₂, ∀ x ∈ S.L R (R / 2), s ≤ S.φ a x →
      box S.g (S.wb a s) x ^ 2 ≤ Kb * (S.Gq x + S.Θq x + S.Pq a x))
    (σ : ℝ) {s : ℝ} (hs : s ∈ Icc s₁ s₂) :
    ∫ x in S.L R (R / 2) ∩ {x | s < S.φ a x}, Real.exp (2 * σ * S.ψ x) * box S.g (S.wb a s) x ^ 2
      ≤ Kb * S.N R σ (fun x => S.Gq x + S.Θq x + S.Pq a x) := by
  have hsJ := hJ hs
  have hm := measurableSet_L_superlevel hS hB a s
  have hw : ContDiffOn ℝ ∞ (S.wb a s) S.V := by
    rw [wb_eq]
    exact (hS.contDiffOn_u a hsJ).sub (hS.contDiffOn_u'Ψ_slice a hsJ)
  have hc : ContinuousOn (fun x => S.Gq x + S.Θq x + S.Pq a x) S.V :=
    (hS.continuousOn_Gq.add hS.continuousOn_Θq).add (hS.continuousOn_Pq a)
  have hi1 := (integrableOn hS hB ((hS.continuousOn_box hw).pow 2) σ).mono_set
    (inter_subset_left (t := {x | s < S.φ a x}))
  have hi2 := integrableOn hS hB (hc.const_smul Kb) σ
  rw [← N_const_mul, N_def]
  calc ∫ x in S.L R (R / 2) ∩ {x | s < S.φ a x},
        Real.exp (2 * σ * S.ψ x) * box S.g (S.wb a s) x ^ 2
      ≤ ∫ x in S.L R (R / 2) ∩ {x | s < S.φ a x},
          Real.exp (2 * σ * S.ψ x) * (Kb * (S.Gq x + S.Θq x + S.Pq a x)) :=
        setIntegral_mono_on hi1 (hi2.mono_set inter_subset_left) hm fun x hx =>
          mul_le_mul_of_nonneg_left (hKb s hs x hx.1 hx.2.le) (Real.exp_pos _).le
    _ ≤ _ := by
        refine setIntegral_mono_set hi2 ((ae_restrict_iff' (measurableSet_L hS hB)).2
          (Eventually.of_forall fun x hx => ?_)) (Eventually.of_forall inter_subset_left)
        have := hS.continuousOn_Gq
        simp only [Pi.zero_apply]
        refine mul_nonneg (Real.exp_pos _).le (mul_nonneg hKb0 ?_)
        simp only [Gq_def, Θq_def, Pq_def]; positivity

/-- **Integrated energy inequality for `w̄_a`** (the surface terms of Steps 1, 2). -/
theorem energy_wb (a : ι) : ∃ K σ₁ : ℝ, 0 ≤ K ∧ ∀ σ ≥ σ₁,
    σ * S.N R σ (S.Wq a σ) ≤ K * (S.N R σ S.Gq + S.N R σ S.Θq + S.N R σ (S.Pq a)) := by
  obtain ⟨C, σ₀, H⟩ := (setting' hS hB).energy_integrated (eikonal hS hB a)
  have hLc := isCompact_L' hS hB
  have hLV := L_subset_V (S := S) hB
  have hne : (S.L R (R / 2)).Nonempty := ⟨_, q₀_mem_L hB⟩
  obtain ⟨x₁, hx₁, hmin⟩ := hLc.exists_isMinOn hne ((hS.continuousOn_φ a).mono hLV)
  obtain ⟨x₂, hx₂, hmax⟩ := hLc.exists_isMaxOn hne ((hS.continuousOn_φ a).mono hLV)
  set s₁ := S.φ a x₁
  set s₂ := S.φ a x₂
  have hs12 : s₁ ≤ s₂ := hmin hx₂
  have hJ : Icc s₁ s₂ ⊆ S.J :=
    hS.ordConnected_J.out (hS.mem_J a x₁ (hLV hx₁)) (hS.mem_J a x₂ (hLV hx₂))
  obtain ⟨Kb, hKb0, hKb⟩ := bound_box hS hLc hLV a hJ
  refine ⟨max C 0 * ((s₂ - s₁) * Kb), σ₀, by
    have := sub_nonneg.2 hs12; positivity, fun σ hσ => ?_⟩
  have hc : ContinuousOn (fun x => S.Gq x + S.Θq x + S.Pq a x) S.V :=
    (hS.continuousOn_Gq.add hS.continuousOn_Θq).add (hS.continuousOn_Pq a)
  have hNn : 0 ≤ S.N R σ (fun x => S.Gq x + S.Θq x + S.Pq a x) :=
    N_nonneg hS hB σ fun x _ => by simp only [Gq_def, Θq_def, Pq_def]; positivity
  have h := H σ hσ s₁ s₂ (S.J ×ˢ S.V) (S.wb a) hs12 hS.isOpen_JV
    (fun p hp => ⟨hJ hp.1, hLV (mem_L.2 hp.2)⟩) ((hS.contDiffOn_wb a).of_le (by simp))
    fun s hs x hx hψ hsx => hS.wb_top a (hJ hs) (hLV (mem_L.2 hx)) hψ hsx
  have hLs : S.L R (R / 2) ∩ {x | s₁ ≤ S.φ a x ∧ S.φ a x ≤ s₂} = S.L R (R / 2) :=
    inter_eq_left.2 fun x hx => ⟨hmin hx, hmax hx⟩
  replace h : σ * ∫ x in S.L R (R / 2) ∩ {x | s₁ ≤ S.φ a x ∧ S.φ a x ≤ s₂},
      Real.exp (2 * σ * S.ψ x) * S.Wq a σ x ≤ C * ∫ s in s₁..s₂,
        ∫ x in S.L R (R / 2) ∩ {x | s < S.φ a x},
          Real.exp (2 * σ * S.ψ x) * box S.g (S.wb a s) x ^ 2 := by
    simp only [L_def, Wq_def, Zq_def]
    exact h
  rw [hLs] at h
  set I := ∫ s in s₁..s₂, ∫ x in S.L R (R / 2) ∩ {x | s < S.φ a x},
    Real.exp (2 * σ * S.ψ x) * box S.g (S.wb a s) x ^ 2
  have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg hs12 fun s _ =>
    setIntegral_nonneg (measurableSet_L_superlevel hS hB a s) fun x _ =>
      mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hI : I ≤ (s₂ - s₁) * (Kb * S.N R σ (fun x => S.Gq x + S.Θq x + S.Pq a x)) := by
    by_cases hint : IntervalIntegrable (fun s => ∫ x in S.L R (R / 2) ∩ {x | s < S.φ a x},
        Real.exp (2 * σ * S.ψ x) * box S.g (S.wb a s) x ^ 2) volume s₁ s₂
    · have := intervalIntegral.integral_mono_on hs12 hint intervalIntegrable_const
        fun s hs => inner_le hS hB a hJ hKb0 hKb σ hs
      simp only [intervalIntegral.integral_const, smul_eq_mul] at this
      exact this.trans_eq (by ring)
    · rw [show I = 0 from intervalIntegral.integral_undef hint]
      have := sub_nonneg.2 hs12
      positivity
  have hN : S.N R σ (fun x => S.Gq x + S.Θq x + S.Pq a x) =
      S.N R σ S.Gq + S.N R σ S.Θq + S.N R σ (S.Pq a) := by
    have e1 := N_add hS hB (f := fun x => S.Gq x + S.Θq x) (h := S.Pq a)
      (hS.continuousOn_Gq.add hS.continuousOn_Θq) (hS.continuousOn_Pq a) σ
    have e2 := N_add hS hB (f := S.Gq) (h := S.Θq) hS.continuousOn_Gq hS.continuousOn_Θq σ
    rw [e1, e2]
  calc σ * S.N R σ (S.Wq a σ) ≤ C * I := by simpa only [N_def] using h
    _ ≤ max C 0 * I := mul_le_mul_of_nonneg_right (le_max_left _ _) hI0
    _ ≤ max C 0 * ((s₂ - s₁) * (Kb * S.N R σ (fun x => S.Gq x + S.Θq x + S.Pq a x))) :=
        mul_le_mul_of_nonneg_left hI (le_max_right _ _)
    _ = _ := by rw [hN]; ring

/-- **Energy inequality for `φ̄_a`** (Step 2): `σ² ‖dφ̄_a‖² + σ⁴ ‖φ̄_a‖² ≤ C ‖□_g φ̄_a‖²`. -/
theorem energy_φb : ∃ K σ₁ : ℝ, 0 ≤ K ∧ ∀ σ ≥ σ₁, ∀ a,
    σ ^ 2 * S.N R σ (S.Qq a) + σ ^ 4 * S.N R σ (S.Pq a) ≤ K * S.N R σ (S.Rq a) := by
  obtain ⟨C, σ₀, H⟩ := (setting' hS hB).energy_volume
  have hLV := L_subset_V (S := S) hB
  refine ⟨max C 0, σ₀, le_max_right _ _, fun σ hσ a => ?_⟩
  have h := H σ hσ (ball S.q₀ R) (S.φb a) isOpen_ball (fun x hx => hx.1)
    (((hS.contDiffOn_φb a).mono hB.subset).of_le (by simp)) fun x hx hψ => by
      obtain ⟨h1, h2⟩ := hS.φb_top a (hLV (mem_L.2 hx)) hψ
      exact ⟨h1, d_eq_zero_of_fderiv h2⟩
  replace h : σ ^ 2 * S.N R σ (fun x => S.Qq a x + σ ^ 2 * S.Pq a x) ≤ C * S.N R σ (S.Rq a) := by
    simp only [N_def, L_def, Qq_def, Pq_def, Rq_def]
    exact h
  have e1 := N_add hS hB (f := S.Qq a) (h := fun x => σ ^ 2 * S.Pq a x) (hS.continuousOn_Qq a)
    (continuousOn_const.mul (hS.continuousOn_Pq a)) σ
  beta_reduce at e1
  rw [e1, N_const_mul] at h
  have hR0 : 0 ≤ S.N R σ (S.Rq a) := N_nonneg hS hB σ fun x _ => S.Rq_nonneg a x
  calc σ ^ 2 * S.N R σ (S.Qq a) + σ ^ 4 * S.N R σ (S.Pq a)
      = σ ^ 2 * (S.N R σ (S.Qq a) + σ ^ 2 * S.N R σ (S.Pq a)) := by ring
    _ ≤ C * S.N R σ (S.Rq a) := h
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hR0

end Ball

omit hS in
theorem exists_uniform [Fintype ι] {P : ι → ℝ → ℝ → Prop}
    (h : ∀ a, ∃ K σ₁ : ℝ, 0 ≤ K ∧ P a K σ₁)
    (hmono : ∀ a K K' σ σ', K ≤ K' → σ ≤ σ' → P a K σ → P a K' σ') :
    ∃ K σ₁ : ℝ, 0 ≤ K ∧ ∀ a, P a K σ₁ := by
  choose K σ hK hP using h
  refine ⟨∑ a, K a, ∑ a, |σ a|, Finset.sum_nonneg fun a _ => hK a, fun a => ?_⟩
  refine hmono a _ _ _ _ (Finset.single_le_sum (fun a _ => hK a) (Finset.mem_univ a))
    ((le_abs_self _).trans (Finset.single_le_sum (f := fun a => |σ a|)
      (fun a _ => abs_nonneg _) (Finset.mem_univ a))) (hP a)

omit hS in
theorem exists_uniform' [Fintype ι] {P : ι → ℝ → Prop} (h : ∀ a, ∃ K, 0 ≤ K ∧ P a K)
    (hmono : ∀ a K K', K ≤ K' → P a K → P a K') : ∃ K, 0 ≤ K ∧ ∀ a, P a K := by
  obtain ⟨K, -, hK, hP⟩ := exists_uniform (P := fun a K _ => P a K)
    (fun a => let ⟨K, hK, hP⟩ := h a; ⟨K, 0, hK, hP⟩) fun a K K' _ _ hKK' _ hP =>
      hmono a K K' hKK' hP
  exact ⟨K, hK, hP⟩

theorem Hyp.φb_gauge (i : Fin (n + 1)) {x : E n} (hx : x ∈ S.V) :
    S.φb (S.e i) =ᶠ[𝓝 x] 0 :=
  Filter.eventually_of_mem (hS.isOpen_V.mem_nhds hx) fun y hy => by
    simp [φb_def, hS.gauge i y hy]

namespace Ball

variable {R : ℝ} (hB : S.Ball R)
include hB

theorem N_add4 {f₁ f₂ f₃ f₄ : E n → ℝ} (h₁ : ContinuousOn f₁ S.V) (h₂ : ContinuousOn f₂ S.V)
    (h₃ : ContinuousOn f₃ S.V) (h₄ : ContinuousOn f₄ S.V) (σ : ℝ) :
    S.N R σ (fun x => f₁ x + f₂ x + f₃ x + f₄ x) =
      S.N R σ f₁ + S.N R σ f₂ + S.N R σ f₃ + S.N R σ f₄ := by
  have e1 := N_add hS hB (f := fun x => f₁ x + f₂ x + f₃ x) (h := f₄) ((h₁.add h₂).add h₃) h₄ σ
  have e2 := N_add hS hB (f := fun x => f₁ x + f₂ x) (h := f₃) (h₁.add h₂) h₃ σ
  have e3 := N_add hS hB (f := f₁) (h := f₂) h₁ h₂ σ
  beta_reduce at e1 e2
  rw [e1, e2, e3]

/-- **Steps 1–3**: `ḡ = 0`, `θ̄ = 0` and `φ'_a ∘ Ψ = φ_a` on `V° ∩ {ψ < τ}`. -/
theorem steps123 [Fintype ι] : ∀ x ∈ S.Vlow R,
    (∀ α β, S.gb x α β = 0) ∧ (∀ k, S.θb x k = 0) ∧ ∀ a, S.φb a x = 0 := by
  have hLc := isCompact_L' hS hB
  have hLV := L_subset_V (S := S) hB
  obtain ⟨K₁, σ₁, hK₁, hE1⟩ := exists_uniform (P := fun a K σ₁ => ∀ σ ≥ σ₁,
      σ * S.N R σ (S.Wq a σ) ≤ K * (S.N R σ S.Gq + S.N R σ S.Θq + S.N R σ (S.Pq a)))
    (fun a => energy_wb hS hB a) fun a K K' σ σ' hK hσ hP τ hτ => by
      refine (hP τ (hσ.trans hτ)).trans (mul_le_mul_of_nonneg_right hK ?_)
      have := N_nonneg hS hB τ (f := S.Gq) fun x _ => S.Gq_nonneg x
      have := N_nonneg hS hB τ (f := S.Θq) fun x _ => S.Θq_nonneg x
      have := N_nonneg hS hB τ (f := S.Pq a) fun x _ => S.Pq_nonneg a x
      linarith
  obtain ⟨K₅, σ₅, hK₅, hE2⟩ := energy_φb hS hB
  obtain ⟨K₂, hK₂, hM⟩ := exists_uniform' (P := fun a K => ∀ x ∈ S.L R (R / 2),
      S.Mq a x ≤ K * (S.Zq a x ^ 2 + S.wb a (S.φ a x) x ^ 2 + S.Gq x + S.Pq a x + S.Qq a x))
    (fun a => bound_transport hS hLc hLV a) fun a K K' hK hP x hx =>
      (hP x hx).trans (mul_le_mul_of_nonneg_right hK
        (by simp only [Gq_def, Pq_def, Qq_def]; positivity))
  obtain ⟨K₃, hK₃, hT⟩ := exists_uniform' (P := fun a K => ∀ x ∈ S.L R (R / 2),
      S.Tq a x ≤ K * S.Θq x)
    (fun a => bound_T hS hLc hLV a) fun a K K' hK hP x hx =>
      (hP x hx).trans (mul_le_mul_of_nonneg_right hK (S.Θq_nonneg x))
  obtain ⟨K₄, hK₄, hbasis⟩ := bound_basis hS hLc hLV
  obtain ⟨K₆, hK₆, hspan⟩ := bound_span hS hLc hLV
  have cG := hS.continuousOn_Gq
  have cΘ := hS.continuousOn_Θq
  have cP := hS.continuousOn_Pq
  have cQ := hS.continuousOn_Qq
  have cR := hS.continuousOn_Rq
  have cT := hS.continuousOn_Tq
  have cM := hS.continuousOn_Mq
  have cW := hS.continuousOn_Wq
  have hgv : ∀ i, ∀ x ∈ S.V, S.φb (S.e i) x = 0 := fun i x hx => (hS.φb_gauge i hx).self_of_nhds
  set σ₀ := max 1 (max σ₁ σ₅)
  obtain ⟨σ, hσ, hG, hΘ, hPQ⟩ := absorb S.e (σ₀ := σ₀) (le_max_left _ _) hK₁ hK₂ hK₃ hK₄ hK₅ hK₆
    (NG := fun σ => S.N R σ S.Gq) (NΘ := fun σ => S.N R σ S.Θq)
    (NP := fun a σ => S.N R σ (S.Pq a)) (NQ := fun a σ => S.N R σ (S.Qq a))
    (NR := fun a σ => S.N R σ (S.Rq a)) (NT := fun a σ => S.N R σ (S.Tq a))
    (NM := fun a σ => S.N R σ (S.Mq a)) (NW := fun a σ => S.N R σ (S.Wq a σ))
    (fun σ _ => ⟨N_nonneg hS hB σ fun x _ => S.Gq_nonneg x,
      N_nonneg hS hB σ fun x _ => S.Θq_nonneg x,
      fun a => ⟨N_nonneg hS hB σ fun x _ => S.Pq_nonneg a x,
        N_nonneg hS hB σ fun x _ => S.Qq_nonneg a x,
        N_nonneg hS hB σ fun x _ => S.Rq_nonneg a x, N_nonneg hS hB σ fun x _ => S.Tq_nonneg a x,
        N_nonneg hS hB σ fun x _ => S.Mq_nonneg a x,
        N_nonneg hS hB σ fun x _ => S.Wq_nonneg a σ x⟩⟩)
    (fun σ hσ a => hE1 a σ (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hσ))
    (fun σ hσ a => by
      have hσ1 : 1 ≤ σ := le_trans (le_max_left _ _) hσ
      have := N_mono hS hB (f := S.Mq a)
        (h := fun x => K₂ * (S.Wq a σ x + S.Gq x + S.Pq a x + S.Qq a x)) (cM a)
        (continuousOn_const.mul ((((cW a σ).add cG).add (cP a)).add (cQ a))) σ
        fun x hx => by
          refine (hM a x hx).trans (mul_le_mul_of_nonneg_left ?_ hK₂)
          have : S.wb a (S.φ a x) x ^ 2 ≤ σ ^ 2 * S.wb a (S.φ a x) x ^ 2 :=
            le_mul_of_one_le_left (sq_nonneg _) (by nlinarith)
          simp only [Wq_def]; linarith
      rwa [N_const_mul, N_add4 hS hB (cW a σ) cG (cP a) (cQ a)] at this)
    (fun σ _ a => by
      have := N_mono hS hB (f := S.Tq a) (h := fun x => K₃ * S.Θq x) (cT a)
        (continuousOn_const.mul cΘ) σ (hT a)
      rwa [N_const_mul] at this)
    (fun σ _ a => by
      have := N_mono hS hB (f := S.Rq a) (h := fun x => 2 * S.Tq a x + 2 * S.Mq a x) (cR a)
        ((continuousOn_const.mul (cT a)).add (continuousOn_const.mul (cM a))) σ fun x _ => by
          simp only [Rq_def, Tq_def, Mq_def]
          nlinarith [sq_nonneg (2 * S.T a x - box S.g (S.φb a) x)]
      have e := N_add hS hB (f := fun x => 2 * S.Tq a x) (h := fun x => 2 * S.Mq a x)
        (continuousOn_const.mul (cT a)) (continuousOn_const.mul (cM a)) σ
      beta_reduce at e
      rwa [e, N_const_mul, N_const_mul] at this)
    (fun σ _ a => by
      have := N_mono hS hB (f := S.Tq a) (h := fun x => 2 * S.Mq a x + 2 * S.Rq a x) (cT a)
        ((continuousOn_const.mul (cM a)).add (continuousOn_const.mul (cR a))) σ fun x _ => by
          simp only [Rq_def, Tq_def, Mq_def]
          nlinarith [sq_nonneg (S.T a x - 2 * box S.g (S.φb a) x)]
      have e := N_add hS hB (f := fun x => 2 * S.Mq a x) (h := fun x => 2 * S.Rq a x)
        (continuousOn_const.mul (cM a)) (continuousOn_const.mul (cR a)) σ
      beta_reduce at e
      rwa [e, N_const_mul, N_const_mul] at this)
    (fun σ _ i => ⟨N_eq_zero hS hB σ fun x hx => by simp [Pq_def, hgv i x (hLV hx)],
      N_eq_zero hS hB σ fun x hx => by
        rw [Qq_def, show d (S.φb (S.e i)) x = 0 by
          rw [d_congr (hS.φb_gauge i (hLV hx))]; ext k; simp [d_def]]
        simp,
      N_eq_zero hS hB σ fun x hx => by
        simp [Rq_def, box_eq_zero_of_eventuallyEq (hS.φb_gauge i (hLV hx))]⟩)
    (fun σ _ => by
      have := N_mono hS hB (f := S.Θq) (h := fun x => K₄ * ∑ i, S.Tq (S.e i) x) cΘ
        (continuousOn_const.mul (continuousOn_finsetSum _ fun i _ => cT (S.e i))) σ hbasis
      rwa [N_const_mul, N_sum hS hB _ fun i => cT (S.e i)] at this)
    (fun σ hσ a => hE2 σ (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hσ) a)
    (fun σ _ => by
      have := N_mono hS hB (f := S.Gq) (h := fun x => K₆ * ∑ a, S.Qq a x) cG
        (continuousOn_const.mul (continuousOn_finsetSum _ fun a _ => cQ a)) σ hspan
      rwa [N_const_mul, N_sum hS hB _ cQ] at this)
  intro x hx
  have hG0 := eq_zero_of_N_eq_zero hS hB cG σ (fun x _ => S.Gq_nonneg x) hG x hx
  have hΘ0 := eq_zero_of_N_eq_zero hS hB cΘ σ (fun x _ => S.Θq_nonneg x) hΘ x hx
  simp only [Gq_def, Θq_def, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    pow_eq_zero_iff] at hG0 hΘ0
  refine ⟨fun α β => ?_, fun k => ?_, fun a => ?_⟩
  · have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun α _ => Finset.sum_nonneg
      fun β _ => abs_nonneg (S.gb x α β)).1 hG0 α (Finset.mem_univ _)
    exact abs_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg fun β _ => abs_nonneg _).1 h1 β
      (Finset.mem_univ _))
  · exact abs_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg fun k _ => abs_nonneg _).1 hΘ0 k
      (Finset.mem_univ _))
  · have := eq_zero_of_N_eq_zero hS hB (cP a) σ (fun x _ => S.Pq_nonneg a x) (hPQ a).1 x hx
    simpa [Pq_def] using this

end Ball

end StepData

end

end LorentzianCalderon
