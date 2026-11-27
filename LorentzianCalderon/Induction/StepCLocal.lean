module

public import LorentzianCalderon.Induction.StepCDirections
public import LorentzianCalderon.Induction.StepCWaves
public import LorentzianCalderon.Induction.StepCGauge
public import LorentzianCalderon.Induction.StepCOpen
public import LorentzianCalderon.Local.Step
public import LorentzianCalderon.Geometry.Reach

public section

/-!
# The induction, Steps C1–C4: the local extension

Blueprint, Lemma `lem_ind_local_extension`, Steps C1 (directions), C2 (local gauge), C3
(application of the local step) and C4 (identity outside `W`): near every `q₀ ∈ Σ_τ ∩ W` there is
a local isometry which agrees with `Ψ` on `A_τ` and is the identity outside `W`.

In C2, the neighbourhood `V` of `q₀` is required to have its points outside `W` in `V'` (which
is automatic if `q₀ ∈ int W`, and follows from `p₀ = q₀` otherwise).
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Filter Matrix

variable {n : ℕ} {T : ℝ} {g g' : MatrixField n} {Y Y' : E n → E n} {ψ : E n → ℝ}
  {Φ : ℝ → E n → E n} {τ : ℝ} {Ψ : E n → E n}

/-- **Steps C1–C4** of `lem_ind_local_extension`: under `P(τ)`, every `q₀ ∈ Σ_τ ∩ W` has an open
neighbourhood `U` with a local isometry `Ψ₀` on `U` that agrees with `Ψ` on `U ∩ A_τ` and is the
identity on `U \ W`. -/
theorem ExtensionProperty.exists_local_extension (hP : ExtensionProperty g g' ψ (W n T) τ Ψ)
    (hgA : IsAdmissibleMetric n T g) (hg'A : IsAdmissibleMetric n T g')
    (hg : IsSpacetime g Y) (hg' : IsSpacetime g' Y')
    (hY : ∀ x ∉ M0 n T, form (g x) (EuclideanSpace.single 0 1) (Y x) < 0)
    (hY' : ∀ x ∉ M0 n T, form (g' x) (EuclideanSpace.single 0 1) (Y' x) < 0)
    (hC : CauchyDataSubset n T g g') (hψ : IsCauchyTemporal g Y ψ)
    (hΦ : Continuous fun p : ℝ × E n => Φ p.1 p.2) (hΦ0 : ∀ x, Φ 0 x = x)
    (hΦψ : ∀ t x, ψ (Φ t x) = ψ x + t) {q₀ : E n} (hq₀W : q₀ ∈ W n T) (hq₀ : ψ q₀ = τ) :
    ∃ U : Set (E n), IsOpen U ∧ q₀ ∈ U ∧ ∃ Ψ₀ : E n → E n,
      ContDiffOn ℝ ∞ Ψ₀ U ∧ (∀ x ∈ U, g x = (D Ψ₀ x)ᵀ * g' (Ψ₀ x) * D Ψ₀ x) ∧
      EqOn Ψ₀ Ψ (U ∩ A ψ τ) ∧ ∀ x ∈ U, x ∉ W n T → Ψ₀ x = x := by
  classical
  have hψc := hψ.smooth.continuous
  /- The immersion `v'` and the cluster point `p₀`. -/
  obtain ⟨m, v', hv', hbox', N, -, hWN, himmN⟩ :=
    exists_solution_coords hg' (isCompact_W (n := n) (T := T))
  have himm : ∀ x ∈ W n T, Function.Injective (fderiv ℝ (fun y i => v' i y) x) :=
    fun x hx => himmN x (hWN hx)
  obtain ⟨p₀, hp₀W, hlim, hp₀V, hfr, -⟩ := hP.frontier hgA hg'A hg hg' hY hY' hC hψ hΦ hΦ0 hΦψ
    hv' hbox' himm hq₀ hq₀W
  /- C1: the directions and the waves. -/
  have hn : 0 < n := by have := hg.two_le; omega
  obtain ⟨y, hyW, hyp, hnot⟩ := exists_mem_horismos_past hg' isCompact_W
    (fun x hx => by
      simpa only [mem_O] using exists_isInextendibleRay_subset_O hn
        hg'.globallyHyperbolic.timeOrientation hg'A.minkowski_exterior hY' (mem_O.2 hx)) hp₀W
  obtain ⟨ζ₀, hζ₀⟩ :=
    exists_isAdmissibleDirection hg' isOpen_O (fun h => (mem_O.1 h) hp₀W) (mem_O.2 hyW) hyp hnot
  obtain ⟨s, bv, hs, hbs, hbv, hspan⟩ := hζ₀.exists_finset_span hg' isOpen_O
  have hwaves := fun a : s => hP.exists_waves hgA hg'A hg hg' hY hY' hC hψ hΦ hΦ0 hΦψ hv' hbox'
    himm hq₀ hq₀W hp₀W hlim hp₀V (hs a.1 a.2).2
  choose φ' 𝒯 μ η θ V'a u' a' b' F Va η₂ φ u Aa Ba c hc hdφ' hφ'0 heik' hw hη₂ hη₂η hfw
    using hwaves
  set e : Fin (n + 1) → s := fun i => ⟨bv i, hbs i⟩
  have hdφ'p : ∀ a : s, d (φ' a) p₀ = -c a • a.1 := by
    intro a
    rw [hdφ' a, WithLp.ofLp_toLp, mulVec_mulVec, mul_nonsing_inv _ (hg'.det_ne_zero p₀).isUnit,
      one_mulVec]
  obtain ⟨η₃, hη₃, hη₃le⟩ : ∃ η₃ > 0, ∀ a, η₃ ≤ η₂ a := by
    have : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ a, ε ≤ η₂ a := eventually_all.2 fun a =>
      mem_of_superset (Ioc_mem_nhdsGT (hη₂ a)) fun ε hε => hε.2
    obtain ⟨ε, h1, h2⟩ := (this.and self_mem_nhdsWithin).exists
    exact ⟨ε, h2, h1⟩
  set J := Ioo (-η₃) η₃
  have hJ : ∀ a, J ⊆ Ioo (-η₂ a) (η₂ a) := fun a =>
    Ioo_subset_Ioo (by linarith [hη₃le a]) (hη₃le a)
  have hJ' : ∀ a, J ⊆ Ioo (-η a) (η a) := fun a =>
    (hJ a).trans (Ioo_subset_Ioo (by linarith [hη₂η a]) (hη₂η a))
  /- C2: the neighbourhood `V'` of `p₀`. -/
  obtain ⟨Uinj, -, ϖ, hUinjo, hp₀Uinj, -, -, -, hϖ⟩ :=
    exists_leftInverse_of_injective_fderiv (contDiff_pi.2 hv') (himm p₀ hp₀W)
  have hp₀V'a : ∀ a, p₀ ∈ V'a a := fun a => (hw a).mem
  have hφ'sm : ∀ a, ContDiffOn ℝ ∞ (φ' a) (V'a a) := fun a =>
    (heik' a).smooth.mono (hw a).subset
  have hdc : ∀ a k, ContinuousAt (fun z => d (φ' a) z k) p₀ := fun a k =>
    continuousAt_d (hw a).isOpen (hφ'sm a) (hp₀V'a a) k
  have hbasis₀ : LinearIndependent ℝ fun i => d (φ' (e i)) p₀ := by
    have hne : ∀ i, -c (e i) ≠ 0 := fun i => by linarith [hc (e i)]
    have := hbv.units_smul fun i => Units.mk0 (-c (e i)) (hne i)
    convert this using 1
    ext i k
    simp [hdφ'p, e]
  set F : Option s → E n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun k z =>
    k.elim (g' z) fun a => vecMulVec (d (φ' a) z) (d (φ' a) z)
  have hFc : ∀ k i j, ContinuousAt (fun z => F k z i j) p₀ := by
    rintro (_ | a) i j
    · exact (hg'.smooth i j).continuous.continuousAt
    · exact (hdc a i).mul (hdc a j)
  have hFs : ∀ k z, (F k z)ᵀ = F k z := by
    rintro (_ | a) z
    · exact hg'.symm z
    · exact transpose_vecMulVec _ _
  have hFspan : ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ, Mᵀ = M →
      M ∈ Submodule.span ℝ (range fun k => F k p₀) := by
    intro M hM
    refine Submodule.span_le.2 ?_ (hspan M hM)
    rintro _ (rfl | ⟨ξ, hξ, rfl⟩)
    · exact Submodule.subset_span ⟨none, rfl⟩
    · have hc0 : c ⟨ξ, hξ⟩ ≠ 0 := (hc _).ne'
      have : vecMulVec ξ ξ = (c ⟨ξ, hξ⟩ ^ 2)⁻¹ • F (some ⟨ξ, hξ⟩) p₀ := by
        ext i j
        simp only [F, Option.elim_some, hdφ'p, vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply,
          smul_eq_mul]
        field_simp
      show vecMulVec ξ ξ ∈ _
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨some ⟨ξ, hξ⟩, rfl⟩)
  have hev' : ∀ᶠ z in 𝓝 p₀, z ∈ Uinj ∧ (∀ a, z ∈ V'a a) ∧ (∀ a, φ' a z ∈ J) ∧
      (LinearIndependent ℝ fun i => d (φ' (e i)) z) ∧
      ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ, Mᵀ = M → M ∈ Submodule.span ℝ
        (insert (g' z) (range fun a => vecMulVec (d (φ' a) z) (d (φ' a) z))) := by
    refine (show ∀ᶠ z in 𝓝 p₀, z ∈ Uinj from hUinjo.mem_nhds hp₀Uinj).and ((eventually_all.2 fun a =>
      (hw a).isOpen.mem_nhds (hp₀V'a a)).and ((eventually_all.2 fun a => ?_).and
        ((eventually_linearIndependent (fun i k => hdc (e i) k) hbasis₀).and ?_)))
    · have hcont : ContinuousAt (φ' a) p₀ :=
        (hφ'sm a).continuousOn.continuousAt ((hw a).isOpen.mem_nhds (hp₀V'a a))
      exact hcont.eventually_mem (by rw [hφ'0 a]; exact Ioo_mem_nhds (by linarith) hη₃)
    · filter_upwards [eventually_forall_mem_span hFc hFs hFspan] with z hz M hM
      refine Submodule.span_mono ?_ (hz M hM)
      rintro _ ⟨_ | a, rfl⟩
      · exact mem_insert _ _
      · exact mem_insert_of_mem _ ⟨a, rfl⟩
  obtain ⟨V'₀, hV'₀p, hV'₀o, hp₀V'₀⟩ := eventually_nhds_iff.1 hev'
  obtain ⟨h, hh, hp₀h, hhsub, hhsm⟩ := exists_localInverse_phaseMap hV'₀o
    (f := fun i => φ' (e i)) (fun i => (hφ'sm (e i)).mono fun z hz => (hV'₀p z hz).2.1 (e i))
    (fun z hz => (hV'₀p z hz).2.2.2.1) hp₀V'₀
  set V' := h.source
  have hV' : ∀ z ∈ V', z ∈ Uinj ∧ (∀ a, z ∈ V'a a) ∧ (∀ a, φ' a z ∈ J) ∧
      (LinearIndependent ℝ fun i => d (φ' (e i)) z) ∧
      ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ, Mᵀ = M → M ∈ Submodule.span ℝ
        (insert (g' z) (range fun a => vecMulVec (d (φ' a) z) (d (φ' a) z))) :=
    fun z hz => hV'₀p z (hhsub hz)
  /- C2: the neighbourhood `V` of `q₀` and the local gauge `Ψ₀`. -/
  set ΦI := phaseMap fun i => φ (e i)
  have hq₀Va : ∀ a, q₀ ∈ Va a := fun a => (hfw a).mem
  have hφsm : ∀ a, ContDiffOn ℝ ∞ (φ a) (Va a) := fun a => (hfw a).eikonal.smooth
  have hφc : ∀ a, ContinuousAt (φ a) q₀ := fun a =>
    (hφsm a).continuousOn.continuousAt ((hfw a).isOpen.mem_nhds (hq₀Va a))
  have hΦIc : ContinuousAt ΦI q₀ :=
    (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm.continuous.continuousAt.comp
      (continuousAt_pi.2 fun i => (by simpa only [phaseMap_def] using hφc (e i)))
  have hΦIq₀ : ΦI q₀ ∈ h.target := by
    have : ΦI q₀ = h p₀ := by
      rw [hh]
      ext i
      simp [ΦI, (hfw _).phase_zero, hφ'0]
    rw [this]
    exact h.map_source hp₀h
  have hev : ∀ᶠ x in 𝓝 q₀, (∀ a, x ∈ Va a) ∧ (∀ a, φ a x ∈ J) ∧ ΦI x ∈ h.target ∧
      (x ∈ A ψ τ → Ψ x ∈ V') ∧ (x ∉ W n T → x ∈ V') := by
    refine (eventually_all.2 fun a => (hfw a).isOpen.mem_nhds (hq₀Va a)).and
      ((eventually_all.2 fun a => (hφc a).eventually_mem ?_).and
        ((hΦIc.eventually_mem (h.open_target.mem_nhds hΦIq₀)).and
          ((eventually_nhdsWithin_iff.1 (hlim (h.open_source.mem_nhds hp₀h))).and ?_)))
    · rw [(hfw a).phase_zero]
      exact Ioo_mem_nhds (by linarith) hη₃
    · by_cases hint : q₀ ∈ interior (W n T)
      · filter_upwards [isOpen_interior.mem_nhds hint] with x hx hxW
        exact absurd (interior_subset hx) hxW
      · have hpq : p₀ = q₀ := hfr ⟨subset_closure hq₀W, hint⟩
        filter_upwards [h.open_source.mem_nhds (hpq ▸ hp₀h)] with x hx _
        exact hx
  obtain ⟨V, hVp, hVo, hq₀V⟩ := eventually_nhds_iff.1 hev
  set Ψ₀ : E n → E n := fun x => h.symm (ΦI x)
  have hΨ₀V' : ∀ x ∈ V, Ψ₀ x ∈ V' := fun x hx => h.map_target (hVp x hx).2.2.1
  have hgauge : ∀ x ∈ V, ∀ i, φ' (e i) (Ψ₀ x) = φ (e i) x := by
    intro x hx i
    have h1 := h.right_inv (hVp x hx).2.2.1
    rw [hh] at h1
    have := congr_arg (fun w : E n => w i) h1
    simpa [ΦI, Ψ₀] using this
  have hΨ₀A : ∀ x ∈ V, τ < ψ x → Ψ₀ x = Ψ x := by
    intro x hx hxA
    have hΨx := (hVp x hx).2.2.2.1 (mem_A.2 hxA)
    have : ΦI x = h (Ψ x) := by
      rw [hh]
      ext i
      simp [ΦI, (hfw (e i)).eq_comp x ⟨(hVp x hx).1 (e i), (mem_A.2 hxA)⟩]
    simp only [Ψ₀, this, h.left_inv hΨx]
  have hΨ₀sm : ContDiffOn ℝ ∞ Ψ₀ V :=
    hhsm.comp (contDiffOn_phaseMap fun i => (hφsm (e i)).mono fun x hx => (hVp x hx).1 (e i))
      fun x hx => (hVp x hx).2.2.1
  have hVA : IsOpen (V ∩ A ψ τ) := hVo.inter (isOpen_A hψc τ)
  have hpulltop : ∀ x ∈ V, τ < ψ x → g x = (D Ψ₀ x)ᵀ * g' (Ψ₀ x) * D Ψ₀ x := by
    intro x hx hxA
    have hev : Ψ₀ =ᶠ[𝓝 x] Ψ :=
      eventually_of_mem (hVA.mem_nhds ⟨hx, (mem_A.2 hxA)⟩) fun y hy => hΨ₀A y hy.1 (mem_A.1 hy.2)
    rw [show D Ψ₀ x = D Ψ x by ext i j; simp only [D_def, hev.fderiv_eq], hΨ₀A x hx hxA]
    exact hP.pullback x (mem_A.2 hxA)
  /- C3: the local step. -/
  let S : StepData n s :=
    { g := g, g' := g', Y := Y, Y' := Y', V := V, V' := V', Ψ := Ψ₀, ψ := ψ, q₀ := q₀, J := J,
      φ := φ, φ' := φ', u := u, u' := u', A := Aa, B := Ba, A' := a', B' := b', e := e }
  have hτS : S.τ = τ := by simpa only [StepData.τ_def] using hq₀
  have hS : S.Hyp :=
    { two_le := hg.two_le
      smooth_g := hg.smooth
      lorentzian_g := hg.lorentzian
      time_g := hg.globallyHyperbolic.timeOrientation
      smooth_g' := hg'.smooth
      lorentzian_g' := hg'.lorentzian
      time_g' := hg'.globallyHyperbolic.timeOrientation
      isOpen_V := hVo
      isOpen_V' := h.open_source
      smooth_Ψ := hΨ₀sm
      mapsTo_Ψ := hΨ₀V'
      smooth_ψ := hψ.smooth.contDiffOn
      temporal := fun x _ => hψ.past_gradient x
      mem_V := hq₀V
      isOpen_J := isOpen_Ioo
      ordConnected_J := ordConnected_Ioo
      eikonal := fun a =>
        ⟨(hφsm a).mono fun x hx => (hVp x hx).1 a,
          fun x hx => (hfw a).eikonal.eikonal x ((hVp x hx).1 a),
          fun x hx => (hfw a).eikonal.d_ne_zero x ((hVp x hx).1 a),
          fun x hx => (hfw a).eikonal.future x ((hVp x hx).1 a)⟩
      eikonal' := fun a =>
        ⟨(hφ'sm a).mono fun z hz => (hV' z hz).2.1 a,
          fun z hz => (heik' a).eikonal z ((hw a).subset ((hV' z hz).2.1 a)),
          fun z hz => (heik' a).d_ne_zero z ((hw a).subset ((hV' z hz).2.1 a)),
          fun z hz => (heik' a).future z ((hw a).subset ((hV' z hz).2.1 a))⟩
      mem_J := fun a x hx => (hVp x hx).2.1 a
      mem_J' := fun a z hz => (hV' z hz).2.2.1 a
      smooth_u := fun a => (hfw a).smooth.mono (prod_mono (hJ a) fun x hx => (hVp x hx).1 a)
      smooth_u' := fun a => (hw a).smooth.mono (prod_mono (hJ' a) fun z hz => (hV' z hz).2.1 a)
      continuous_A := fun a => (hfw a).a_smooth.continuousOn.mono
        (prod_mono (hJ a) fun x hx => (hVp x hx).1 a)
      continuous_B := fun a => (hfw a).b_smooth.continuousOn.mono
        (prod_mono (hJ a) fun x hx => (hVp x hx).1 a)
      continuous_A' := fun a => (hw a).a_smooth.continuousOn.mono
        (prod_mono (hJ' a) fun z hz => (hV' z hz).2.1 a)
      continuous_B' := fun a => (hw a).b_smooth.continuousOn.mono
        (prod_mono (hJ' a) fun z hz => (hV' z hz).2.1 a)
      wave := fun a s hs x hx => (hfw a).box_eq s (hJ a hs) x ((hVp x hx).1 a)
      wave_zero := fun a s hs x hx => (hfw a).a_eq_zero s (hJ a hs) x ((hVp x hx).1 a)
      transport := fun a s hs x hx => (hfw a).transport s (hJ a hs) x ((hVp x hx).1 a)
      wave' := fun a s hs z hz => (hw a).box_eq s (hJ' a hs) z ((hV' z hz).2.1 a)
      wave_zero' := fun a s hs z hz => (hw a).a_eq_zero s (hJ' a hs) z ((hV' z hz).2.1 a)
      transport' := fun a s hs z hz => (hw a).transport s (hJ' a hs) z ((hV' z hz).2.1 a)
      pos := fun a s hs x hx => (hfw a).pos s (hJ a hs) x ((hVp x hx).1 a)
      pullback_top := fun x hx hxτ => hpulltop x hx (hτS ▸ hxτ)
      phase_top := fun a x hx hxτ => by
        show φ' a (Ψ₀ x) = φ a x
        rw [hΨ₀A x hx (hτS ▸ hxτ)]
        exact ((hfw a).eq_comp x ⟨(hVp x hx).1 a, hτS ▸ (mem_A.2 hxτ)⟩).symm
      amplitude_top := fun a s hs x hx hxτ hsx => by
        show u a s x = u' a s (Ψ₀ x)
        rw [hΨ₀A x hx (hτS ▸ hxτ)]
        exact (hfw a).eq_comp_wave s (hJ a hs) x ⟨(hVp x hx).1 a, hτS ▸ (mem_A.2 hxτ)⟩ hsx
      gauge := fun i x hx => hgauge x hx i
      basis := fun z hz => (hV' z hz).2.2.2.1
      span := fun z hz => (hV' z hz).2.2.2.2 }
  obtain ⟨Vo, hVoo, hq₀Vo, hVoV, hdet, hpull, -, -, huc⟩ := StepData.prop_local_step hS
  have hpull' : ∀ x ∈ Vo, g x = (D Ψ₀ x)ᵀ * g' (Ψ₀ x) * D Ψ₀ x := hpull
  refine ⟨Vo, hVoo, hq₀Vo, Ψ₀, hΨ₀sm.mono hVoV, hpull',
    fun x hx => hΨ₀A x (hVoV hx.1) (mem_A.1 hx.2),
    fun x hx hxW => ?_⟩
  /- C4: the identity outside `W`. -/
  have hxV := hVoV hx
  have hxV' : x ∈ V' := (hVp x hxV).2.2.2.2 hxW
  have hΨx : Ψ₀ x ∈ V' := hΨ₀V' x hxV
  have key : ∀ i, v' i (Ψ₀ x) = v' i x := by
    intro i
    obtain ⟨ht1, ht2, ht3⟩ := transfer_spec hgA hg'A hg hg' hY hY' hC (hv' i) (hbox' i)
    have hcomp : ContDiffOn ℝ ∞ (fun y => v' i (Ψ₀ y)) Vo :=
      (hv' i).comp_contDiffOn (hΨ₀sm.mono hVoV)
    have hwbox : ∀ y ∈ Vo, box g (fun y => transfer n T g (v' i) y - v' i (Ψ₀ y)) y = 0 := by
      intro y hy
      rw [box_sub_of_contDiffOn hg.smooth hg.det_ne_zero hVoo ht1.contDiffOn hcomp hy, ht2]
      have hb := box_comp_of_pullback (Ψ := Ψ₀) (x := y)
        ((hΨ₀sm.contDiffAt (hVo.mem_nhds (hVoV hy))).of_le (by simp)) (hdet y hy)
        (fun i j => ((hg'.smooth i j).differentiable (by simp)) _) (hg'.det_ne_zero _)
        (eventually_of_mem (hVoo.mem_nhds hy) hpull') ((hv' i).contDiffAt.of_le (by simp))
      rw [show (fun y => v' i (Ψ₀ y)) = v' i ∘ Ψ₀ from rfl, hb, hbox' i]
      ring
    have hwtop : ∀ y ∈ Vo, S.τ < S.ψ y →
        (fun y => transfer n T g (v' i) y - v' i (Ψ₀ y)) y = 0 := by
      intro y hy hyτ
      have hyA : y ∈ A ψ τ := by rw [mem_A, ← hτS]; exact hyτ
      simp only [hP.transfer_eq_comp hgA hg'A hg hg' hY hY' hC hψ (hv' i) (hbox' i) y hyA,
        hΨ₀A y (hVoV hy) (mem_A.1 hyA), sub_self]
    have := huc _ (ht1.contDiffOn.sub hcomp) hwbox hwtop x hx
    simp only [ht3 x (mem_O.2 hxW)] at this
    linarith
  calc Ψ₀ x = ϖ (fun i => v' i (Ψ₀ x)) := (hϖ _ (hV' _ hΨx).1).symm
    _ = ϖ (fun i => v' i x) := by simp only [key]
    _ = x := hϖ x (hV' x hxV').1

end

end LorentzianCalderon
