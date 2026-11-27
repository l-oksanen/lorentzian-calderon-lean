module

public import LorentzianCalderon.Waves.OneSided

public section

/-!
# Transport equations across the frontier

Blueprint `lem_ind_amplitude`: the transport hierarchy `(eq_ind_tri)` is solved along the integral
curves of `Ẑ = Z / Zψ`, with `Z = -grad φ`, from a level `ψ = τ₀` above the frontier. Here the
solutions are made to agree with given solutions above a level `ℓ < τ₀`
(`FlowBoxData.exists_transport_eq`), so that no initial values on `Σ_{τ₀}` need to be
prescribed; the positivity of the leading term propagates along the flow lines.
-/

namespace LorentzianCalderon

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

variable {n : ℕ}

namespace FlowBoxData

variable {T : Set (E n)} {ϱ : E n → ℝ} {Zh : E n → E n} {X : ℝ × ℝ × E n × ℝ → E n}
  (hD : FlowBoxData T ϱ Zh X) (τ₀ : ℝ)
include hD

theorem flowProj_mem {x : E n} (hx : x ∈ boxSet T ϱ Zh τ₀) :
    flowProj ϱ X τ₀ x ∈ boxSet T ϱ Zh τ₀ ∧ ϱ (flowProj ϱ X τ₀ x) = τ₀ := by
  obtain ⟨h1, h2, -⟩ := hD.flowLine τ₀ hx (mem_boxSet.1 hx).2
  rw [flowProj_def]
  exact ⟨h1, h2⟩

/-- A function with vanishing derivative along `Ẑ` is constant on the flow lines. -/
theorem eq_flowProj_of_fderiv_eq_zero {m : E n → ℝ}
    (hm : ContDiffOn ℝ 1 m (boxSet T ϱ Zh τ₀))
    (h0 : ∀ x ∈ boxSet T ϱ Zh τ₀, fderiv ℝ m x (Zh x) = 0) {x : E n}
    (hx : x ∈ boxSet T ϱ Zh τ₀) : m x = m (flowProj ϱ X τ₀ x) := by
  have hB : IsOpen (boxSet T ϱ Zh τ₀) := hD.isOpen_boxSet τ₀
  set k : ℝ → ℝ := fun s => m (X (s, ϱ x, x, 0))
  have hk : ∀ s ∈ uIcc τ₀ (ϱ x), HasDerivAt k 0 s := fun s hs => by
    have hmem := hD.mem_of_uIcc τ₀ hx hs
    have hy := (hD.flowLine τ₀ hx hmem).1
    have hm' : HasFDerivAt m (fderiv ℝ m (X (s, ϱ x, x, 0))) (X (s, ϱ x, x, 0)) :=
      ((hm.contDiffAt (hB.mem_nhds hy)).differentiableAt one_ne_zero).hasFDerivAt
    have := hm'.comp_hasDerivAt s (hD.flow.hasDerivAt hmem)
    simp only [zField_def, h0 _ hy] at this
    exact this
  have hcont : ContinuousOn k (uIcc τ₀ (ϱ x)) := fun s hs =>
    (hk s hs).continuousAt.continuousWithinAt
  have key : k (ϱ x) = k τ₀ := by
    rcases le_total τ₀ (ϱ x) with hle | hle
    · have hI : Icc τ₀ (ϱ x) = uIcc τ₀ (ϱ x) := (uIcc_of_le hle).symm
      exact constant_of_has_deriv_right_zero (hI ▸ hcont)
        (fun s hs => (hk s (hI ▸ Ico_subset_Icc_self hs)).hasDerivWithinAt) (ϱ x)
        (right_mem_Icc.2 hle)
    · have hI : Icc (ϱ x) τ₀ = uIcc τ₀ (ϱ x) := (uIcc_of_ge hle).symm
      exact (constant_of_has_deriv_right_zero (hI ▸ hcont)
        (fun s hs => (hk s (hI ▸ Ico_subset_Icc_self hs)).hasDerivWithinAt) τ₀
        (right_mem_Icc.2 hle)).symm
  simp only [k, (hD.self τ₀ hx).2] at key
  simpa only [flowProj_def] using key

/-- **Transport with prescribed values above a level.** If `β` solves `Ẑβ + a β = f` above the
level `ℓ < τ₀`, there is a solution on the flow box which equals `β` above that level. -/
theorem exists_transport_eq {a f β : E n → ℝ} (ha : ContDiffOn ℝ ∞ a (boxSet T ϱ Zh τ₀))
    (hf : ContDiffOn ℝ ∞ f (boxSet T ϱ Zh τ₀)) (hβ : ContDiffOn ℝ ∞ β (boxSet T ϱ Zh τ₀))
    {ℓ : ℝ} (hℓ : ℓ < τ₀)
    (hβeq : ∀ x ∈ boxSet T ϱ Zh τ₀, ℓ < ϱ x → fderiv ℝ β x (Zh x) + a x * β x = f x) :
    ∃ b : E n → ℝ, ContDiffOn ℝ ∞ b (boxSet T ϱ Zh τ₀) ∧
      (∀ x ∈ boxSet T ϱ Zh τ₀, fderiv ℝ b x (Zh x) + a x * b x = f x) ∧
      ∀ x ∈ boxSet T ϱ Zh τ₀, ℓ < ϱ x → b x = β x := by
  set B := boxSet T ϱ Zh τ₀
  have hB : IsOpen B := hD.isOpen_boxSet τ₀
  have hBT : B ⊆ T := boxSet_subset τ₀
  have hdβ : ContDiffOn ℝ ∞ (fun x => fderiv ℝ β x (Zh x)) B :=
    (hβ.fderiv_of_isOpen hB (by simp)).clm_apply (hD.Zh_smooth.mono hBT)
  obtain ⟨c, hc, hceq, hc0, -⟩ := hD.exists_transport τ₀ ha
    (hf.sub (hdβ.add (ha.mul hβ)))
  refine ⟨fun x => β x + c x, hβ.add hc, fun x hx => ?_, fun x hx hℓx => ?_⟩
  · have hdβx : DifferentiableAt ℝ β x :=
      (hβ.contDiffAt (hB.mem_nhds hx)).differentiableAt (by simp)
    have hdcx : DifferentiableAt ℝ c x :=
      (hc.contDiffAt (hB.mem_nhds hx)).differentiableAt (by simp)
    have := hceq x hx
    rw [fderiv_fun_add hdβx hdcx, add_apply]
    linarith
  · have : c x = 0 := hc0 x hx fun y hy _ hyl => by
      have hℓy : ℓ < ϱ y := by
        rcases le_total τ₀ (ϱ x) with h | h
        · rw [uIcc_of_le h] at hyl; linarith [hyl.1]
        · rw [uIcc_of_ge h] at hyl; linarith [hyl.1]
      simp [hβeq y hy hℓy]
    simp [this]

end FlowBoxData

variable {g : MatrixField n} {Y : E n → E n} {ψ φ : E n → ℝ} {T : Set (E n)}

/-- The flow box of `Ẑ = Z / Zψ` for an eikonal phase `φ` of future type and a Cauchy temporal
function `ψ`, around a point `q₀`: `-g(dφ, db) = p Ẑb` with `p = Zψ > 0`. -/
theorem exists_flowBox_eikonal (hg : IsSpacetime g Y) (hψ : IsCauchyTemporal g Y ψ)
    (hφ : IsFutureEikonal g Y φ T) {q₀ : E n} (hq₀ : q₀ ∈ T) :
    ∃ (Zh : E n → E n) (X : ℝ × ℝ × E n × ℝ → E n) (p : E n → ℝ) (τ₀ : ℝ),
      FlowBoxData T ψ Zh X ∧ ψ q₀ < τ₀ ∧ q₀ ∈ boxSet T ψ Zh τ₀ ∧ ContDiffOn ℝ ∞ p T ∧
      (∀ x ∈ T, 0 < p x) ∧
      ∀ x ∈ T, ∀ b : E n → ℝ, -coform g x (d φ x) (d b x) = p x * fderiv ℝ b x (Zh x) := by
  set p : E n → ℝ := fun x => fderiv ℝ ψ x (-grad g φ x) with hp_def
  set Zh : E n → E n := fun x => (p x)⁻¹ • -grad g φ x with hZh_def
  have hp : ∀ x ∈ T, 0 < p x := fun x hx => hψ.fderiv_pos hg (hφ.future x hx)
  have hZs : ContDiffOn ℝ ∞ (fun x => -grad g φ x) T :=
    (contDiffOn_grad hg.smooth hg.det_ne_zero hφ.isOpen hφ.smooth).neg
  have hps : ContDiffOn ℝ ∞ p T :=
    (hψ.smooth.fderiv_right (m := ∞) (by simp)).contDiffOn.clm_apply hZs
  have hZhs : ContDiffOn ℝ ∞ Zh T := (hps.inv fun x hx => (hp x hx).ne').smul hZs
  have htime : ∀ x ∈ T, fderiv ℝ ψ x (Zh x) = 1 := fun x hx => by
    simp only [Zh, map_smul, smul_eq_mul]
    exact inv_mul_cancel₀ (hp x hx).ne'
  obtain ⟨X, hX⟩ := exists_isFlow (P := ℝ) hφ.isOpen hZhs
  replace hX : IsFlow (zField Zh) T univ X := by rw [zField_def]; exact hX
  have hD : FlowBoxData T ψ Zh X := ⟨hφ.isOpen, hψ.smooth, hZhs, htime, hX⟩
  have hsol : Facts.IsODESolution (zField Zh) T 0 (fun _ => q₀) {ψ q₀} :=
    { interval := ordConnected_singleton
      mem := fun _ _ => hq₀
      deriv := fun t ht => by
        rw [mem_singleton_iff] at ht
        subst ht
        exact HasFDerivWithinAt.of_not_accPt (by
          rw [accPt_iff_clusterPt, inf_principal]
          simp [ClusterPt]) }
  have hm : (ψ q₀, ψ q₀, q₀, (0 : ℝ)) ∈ flowDom (zField Zh) T univ :=
    mem_flowDom.2 ⟨mem_univ _, _, _, hsol, rfl, rfl, rfl⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hX.eventually_mem hm)
  refine ⟨Zh, X, p, ψ q₀ + ε / 2, hD, by linarith, mem_boxSet.2 ⟨hq₀, hball ?_⟩, hps, hp,
    fun x hx b => ?_⟩
  · rw [Real.dist_eq, show ψ q₀ + ε / 2 - ψ q₀ = ε / 2 by ring, abs_of_pos (by positivity)]
    linarith
  · rw [neg_coform_eq_fderiv (hg.symm x) φ b]
    have : -grad g φ x = p x • Zh x := by
      simp only [Zh, smul_smul, mul_inv_cancel₀ (hp x hx).ne', one_smul]
    rw [this, map_smul, smul_eq_mul]

/-- **The transport hierarchy across the frontier** (`lem_ind_amplitude`): solutions `bn` of
the hierarchy above the level `ℓ < τ₀`, with `bn 0 > 0` on the level `τ₀`, extend to solutions on
the whole flow box, with positive leading term. -/
theorem exists_hierarchy (hg : IsSpacetime g Y) (hφ : IsFutureEikonal g Y φ T)
    {Zh : E n → E n} {X : ℝ × ℝ × E n × ℝ → E n} (hD : FlowBoxData T ψ Zh X) {p : E n → ℝ}
    (hp : ContDiffOn ℝ ∞ p T) (hp0 : ∀ x ∈ T, 0 < p x)
    (hpZ : ∀ x ∈ T, ∀ b : E n → ℝ, -coform g x (d φ x) (d b x) = p x * fderiv ℝ b x (Zh x))
    {τ₀ ℓ : ℝ} (hℓ : ℓ < τ₀) {bn : ℕ → E n → ℝ}
    (hbn : ∀ k, ContDiffOn ℝ ∞ (bn k) (boxSet T ψ Zh τ₀))
    (h0 : ∀ x ∈ boxSet T ψ Zh τ₀, ℓ < ψ x →
      2 * -coform g x (d φ x) (d (bn 0) x) + bn 0 x * box g φ x = 0)
    (hs : ∀ k, ∀ x ∈ boxSet T ψ Zh τ₀, ℓ < ψ x →
      2 * -coform g x (d φ x) (d (bn (k + 1)) x) + bn (k + 1) x * box g φ x = -box g (bn k) x)
    (hpos : ∀ x ∈ boxSet T ψ Zh τ₀, ψ x = τ₀ → 0 < bn 0 x) :
    ∃ b : ℕ → E n → ℝ, (∀ k, ContDiffOn ℝ ∞ (b k) (boxSet T ψ Zh τ₀)) ∧
      (∀ x ∈ boxSet T ψ Zh τ₀, 2 * -coform g x (d φ x) (d (b 0) x) + b 0 x * box g φ x = 0) ∧
      (∀ k, ∀ x ∈ boxSet T ψ Zh τ₀,
        2 * -coform g x (d φ x) (d (b (k + 1)) x) + b (k + 1) x * box g φ x = -box g (b k) x) ∧
      (∀ k, ∀ x ∈ boxSet T ψ Zh τ₀, ℓ < ψ x → b k x = bn k x) ∧
      ∀ x ∈ boxSet T ψ Zh τ₀, 0 < b 0 x := by
  set B := boxSet T ψ Zh τ₀
  have hB : IsOpen B := hD.isOpen_boxSet τ₀
  have hBT : B ⊆ T := FlowBoxData.boxSet_subset τ₀
  set a : E n → ℝ := fun x => box g φ x / (2 * p x)
  have hboxφ : ContDiffOn ℝ ∞ (box g φ) T :=
    contDiffOn_box hg.smooth hg.det_ne_zero hφ.isOpen hφ.smooth
  have ha : ContDiffOn ℝ ∞ a B :=
    (hboxφ.mono hBT).div (contDiffOn_const.mul (hp.mono hBT)) fun x hx =>
      mul_ne_zero two_ne_zero (hp0 x (hBT hx)).ne'
  have hconv : ∀ x ∈ B, ∀ (b : E n → ℝ) (F : ℝ),
      2 * -coform g x (d φ x) (d b x) + b x * box g φ x = F ↔
        fderiv ℝ b x (Zh x) + a x * b x = F / (2 * p x) := fun x hx b F => by
    have hp' : 2 * p x ≠ 0 := mul_ne_zero two_ne_zero (hp0 x (hBT hx)).ne'
    have e : (fderiv ℝ b x (Zh x) + a x * b x) * (2 * p x) =
        2 * (p x * fderiv ℝ b x (Zh x)) + b x * box g φ x := by
      have hpx : p x ≠ 0 := (hp0 x (hBT hx)).ne'
      simp only [a]
      field_simp
    rw [hpZ x (hBT hx) b, eq_div_iff hp', e]
  have hboxB : ∀ {b : E n → ℝ}, ContDiffOn ℝ ∞ b B →
      ContDiffOn ℝ ∞ (fun x => -box g b x / (2 * p x)) B :=
    fun hb => (contDiffOn_box hg.smooth hg.det_ne_zero hB hb).neg.div
      (contDiffOn_const.mul (hp.mono hBT)) fun x hx =>
        mul_ne_zero two_ne_zero (hp0 x (hBT hx)).ne'
  have hO : IsOpen (B ∩ {x | ℓ < ψ x}) :=
    hB.inter (isOpen_lt continuous_const hD.ϱ_smooth.continuous)
  have step : ∀ k (b : E n → ℝ), ContDiffOn ℝ ∞ b B → (∀ x ∈ B, ℓ < ψ x → b x = bn k x) →
      ∃ b' : E n → ℝ, (ContDiffOn ℝ ∞ b' B ∧ ∀ x ∈ B, ℓ < ψ x → b' x = bn (k + 1) x) ∧
        ∀ x ∈ B, 2 * -coform g x (d φ x) (d b' x) + b' x * box g φ x = -box g b x := by
    intro k b hb hbe
    obtain ⟨b', hb', hb'eq, hb'e⟩ := hD.exists_transport_eq τ₀ ha (hboxB hb) (hbn (k + 1)) hℓ
      fun x hx hℓx => by
        have hev : b =ᶠ[𝓝 x] bn k := eventually_of_mem (hO.mem_nhds ⟨hx, hℓx⟩)
          fun y hy => hbe y hy.1 hy.2
        rw [box_congr hev]
        exact (hconv x hx _ _).1 (hs k x hx hℓx)
    exact ⟨b', ⟨hb', hb'e⟩, fun x hx => (hconv x hx _ _).2 (hb'eq x hx)⟩
  obtain ⟨b₀, hb₀, hb₀eq, hb₀e⟩ := hD.exists_transport_eq τ₀ (f := fun _ => 0) ha
    contDiffOn_const (hbn 0) hℓ fun x hx hℓx => by
      have := (hconv x hx _ _).1 (h0 x hx hℓx)
      simpa using this
  let P : ℕ → (E n → ℝ) → Prop := fun k b =>
    ContDiffOn ℝ ∞ b B ∧ ∀ x ∈ B, ℓ < ψ x → b x = bn k x
  let seq : (k : ℕ) → {b : E n → ℝ // P k b} := fun k =>
    Nat.rec (motive := fun k => {b : E n → ℝ // P k b}) ⟨b₀, hb₀, hb₀e⟩
      (fun k ih => ⟨Classical.choose (step k ih.1 ih.2.1 ih.2.2),
        (Classical.choose_spec (step k ih.1 ih.2.1 ih.2.2)).1⟩) k
  have hseq : ∀ k, ∀ x ∈ B, 2 * -coform g x (d φ x) (d (seq (k + 1)).1 x) +
      (seq (k + 1)).1 x * box g φ x = -box g (seq k).1 x := fun k =>
    (Classical.choose_spec (step k (seq k).1 (seq k).2.1 (seq k).2.2)).2
  have hseq0 : (seq 0).1 = b₀ := rfl
  refine ⟨fun k => (seq k).1, fun k => (seq k).2.1, fun x hx => ?_, hseq,
    fun k => (seq k).2.2, ?_⟩
  · show 2 * -coform g x (d φ x) (d b₀ x) + b₀ x * box g φ x = 0
    rw [hconv x hx _ _, hb₀eq x hx]
    simp
  · obtain ⟨L, hL, hLeq, -, -⟩ := hD.exists_transport τ₀ (a := fun _ => 0) (f := a)
      contDiffOn_const ha
    set m : E n → ℝ := fun y => b₀ y * Real.exp (L y)
    have hm : ContDiffOn ℝ ∞ m B := hb₀.mul hL.exp
    have hm0 : ∀ x ∈ B, fderiv ℝ m x (Zh x) = 0 := fun x hx => by
      have h1 : HasFDerivAt b₀ (fderiv ℝ b₀ x) x :=
        ((hb₀.contDiffAt (hB.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
      have h2 : HasFDerivAt L (fderiv ℝ L x) x :=
        ((hL.contDiffAt (hB.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
      have h3 : HasFDerivAt m (b₀ x • (Real.exp (L x) • fderiv ℝ L x) +
          Real.exp (L x) • fderiv ℝ b₀ x) x := h1.mul h2.exp
      rw [h3.fderiv]
      have e1 := hb₀eq x hx
      have e2 := hLeq x hx
      simp only [add_apply, smul_apply, smul_eq_mul,
        zero_mul, add_zero] at e1 e2 ⊢
      rw [e2]
      linear_combination Real.exp (L x) * e1
    intro x hx
    obtain ⟨hπB, hπτ⟩ := hD.flowProj_mem τ₀ hx
    have hmx := hD.eq_flowProj_of_fderiv_eq_zero τ₀ (hm.of_le (by simp)) hm0 hx
    have hπpos : 0 < b₀ (flowProj ψ X τ₀ x) := by
      rw [hb₀e _ hπB (by rw [hπτ]; exact hℓ)]
      exact hpos _ hπB hπτ
    have : 0 < m x := by
      rw [hmx]
      exact mul_pos hπpos (Real.exp_pos _)
    show 0 < b₀ x
    exact (mul_pos_iff_of_pos_right (Real.exp_pos _)).1 this

end

end LorentzianCalderon
