module

public import LorentzianCalderon.Local.Step.Quantities

public section

/-!
# The local continuation step: pointwise bounds

Uniform pointwise bounds on a compact set `K ⊆ V` for the quantities of `Quantities.lean`, with
constants depending only on the data:
* `bound_box` (Steps 1, 2 on `D_{a,s}`): `(□_g w̄_{a,s})² ≤ C (|ḡ|² + |θ̄|² + φ̄_a²)` for
  `s ≤ φ_a`, `s` in a compact interval inside `J`;
* `bound_transport` (Steps 1, 2 on `Γ_{a,s}`):
  `(T_a - □_g φ̄_a)² ≤ C (|Z_a w̄|² + w̄² + |ḡ|² + φ̄_a² + |dφ̄_a|²)` at `s = φ_a`;
* `bound_T`: `T_a² ≤ C |θ̄|²`;
* `bound_basis` (L3): `|θ̄|² ≤ C Σ_i T_{e i}²`;
* `bound_span` (L4, Step 3): `|ḡ|² ≤ C Σ_a |dφ̄_a|²`.
-/

namespace LorentzianCalderon

noncomputable section
open Set Matrix Filter
open scoped ContDiff Topology

variable {n : ℕ} {ι : Type*}

section Elementary

theorem abs_sum_mul_le {κ : Type*} (s : Finset κ) (a b : κ → ℝ) {M : ℝ}
    (hb : ∀ i ∈ s, |b i| ≤ M) : |∑ i ∈ s, a i * b i| ≤ (∑ i ∈ s, |a i|) * M := by
  calc |∑ i ∈ s, a i * b i| ≤ ∑ i ∈ s, |a i * b i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, |a i| * M := Finset.sum_le_sum fun i hi => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hb i hi) (abs_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem abs_sum_sum_mul_le {m : ℕ} (a b : Fin m → Fin m → ℝ) {M : ℝ}
    (hb : ∀ i j, |b i j| ≤ M) : |∑ i, ∑ j, a i j * b i j| ≤ (∑ i, ∑ j, |a i j|) * M := by
  calc |∑ i, ∑ j, a i j * b i j| ≤ ∑ i, |∑ j, a i j * b i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (∑ j, |a i j|) * M :=
        Finset.sum_le_sum fun i _ => abs_sum_mul_le _ _ _ fun j _ => hb i j
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem abs_coform_le (g : MatrixField n) (x : E n) (ξ η : Fin (n + 1) → ℝ) :
    |coform g x ξ η| ≤ (∑ j, ∑ k, |(g x)⁻¹ j k|) * ‖ξ‖ * ‖η‖ := by
  have h := abs_sum_sum_mul_le (fun j k => (g x)⁻¹ j k) (fun j k => ξ j * η k)
    (M := ‖ξ‖ * ‖η‖) fun j k => by
      rw [abs_mul]
      exact mul_le_mul (norm_le_pi_norm ξ j) (norm_le_pi_norm η k) (abs_nonneg _)
        (norm_nonneg _)
  simp only [coform_def]
  calc |∑ j, ∑ k, (g x)⁻¹ j k * ξ j * η k| = |∑ j, ∑ k, (g x)⁻¹ j k * (ξ j * η k)| := by
        simp only [mul_assoc]
    _ ≤ _ := h
    _ = _ := by ring

theorem sum_abs_le_card_mul_norm (v : Fin (n + 1) → ℝ) : ∑ k, |v k| ≤ (n + 1) * ‖v‖ := by
  calc ∑ k, |v k| ≤ ∑ _k : Fin (n + 1), ‖v‖ :=
        Finset.sum_le_sum fun k _ => norm_le_pi_norm v k
    _ = _ := by simp

theorem sq_add5_le (a b c d e : ℝ) :
    (a + b + c + d + e) ^ 2 ≤ 5 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (a - e),
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (b - e), sq_nonneg (c - d),
    sq_nonneg (c - e), sq_nonneg (d - e)]

theorem abs_six_le (a b c d e f : ℝ) :
    |a + b - c - d - e + f| ≤ |a| + |b| + |c| + |d| + |e| + |f| := by
  rw [abs_le]
  constructor <;> linarith [le_abs_self a, neg_abs_le a, le_abs_self b, neg_abs_le b,
    le_abs_self c, neg_abs_le c, le_abs_self d, neg_abs_le d, le_abs_self e, neg_abs_le e,
    le_abs_self f, neg_abs_le f]

theorem sq_add3_le (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]

end Elementary

namespace StepData

variable {S : StepData n ι} (hS : S.Hyp)
include hS

theorem Hyp.gb_symm (x : E n) (α β : Fin (n + 1)) : S.gb x α β = S.gb x β α := by
  have h1 := (hS.lorentzian_g x).inv_symm
  have h2 := (hS.lorentzian_g' (S.Ψ x)).inv_symm
  have e1 : (S.g' (S.Ψ x))⁻¹ α β = (S.g' (S.Ψ x))⁻¹ β α := by
    have := congrFun (congrFun h2 β) α; rwa [transpose_apply] at this
  simp only [gb_def, gbar_def, e1]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  have : (S.g x)⁻¹ k j = (S.g x)⁻¹ j k := by
    have := congrFun (congrFun h1 j) k; rwa [transpose_apply] at this
  rw [this]; ring

variable {K : Set (E n)} (hK : IsCompact K) (hKV : K ⊆ S.V)
include hK hKV

/-- Steps 1, 2 on `D_{a,s}`. -/
theorem bound_box (a : ι) {s₁ s₂ : ℝ} (hJ : Icc s₁ s₂ ⊆ S.J) :
    ∃ C, 0 ≤ C ∧ ∀ s ∈ Icc s₁ s₂, ∀ x ∈ K, s ≤ S.φ a x →
      box S.g (S.wb a s) x ^ 2 ≤ C * (S.Gq x + S.Θq x + S.Pq a x) := by
  set F : ℝ × E n → ℝ := fun p => |S.κ p.2 * S.A' a p.1 (S.Ψ p.2)| +
    ∑ α, ∑ β, |d2 (S.u' a p.1) (S.Ψ p.2) α β| + ∑ k, |d (S.u' a p.1) (S.Ψ p.2) k|
  have hF : ContinuousOn F (S.J ×ˢ S.V) := by
    have hκ := hS.contDiffOn_κ.continuousOn.comp continuousOn_snd fun p (hp : p ∈ S.J ×ˢ S.V) => hp.2
    refine ((hκ.mul ((hS.continuous_A' a).comp hS.continuousOn_pidΨ hS.mapsTo_idΨ)).abs.add
      (continuousOn_finsetSum _ fun α _ => continuousOn_finsetSum _ fun β _ => ?_)).add
      (continuousOn_finsetSum _ fun k _ => ?_)
    · exact ((contDiffOn_param_d2 hS.isOpen_JV' (hS.smooth_u' a) α β).continuousOn.comp
        hS.continuousOn_pidΨ hS.mapsTo_idΨ).abs
    · exact ((contDiffOn_param_d hS.isOpen_JV' (hS.smooth_u' a) k).continuousOn.comp
        hS.continuousOn_pidΨ hS.mapsTo_idΨ).abs
  obtain ⟨M, hM0, hM⟩ := exists_abs_le_of_continuousOn (isCompact_Icc.prod hK)
    (hF.mono (prod_mono hJ hKV))
  refine ⟨3 * M ^ 2, by positivity, fun s hs x hx hsx => ?_⟩
  have hFx := (le_abs_self _).trans (hM (s, x) ⟨hs, hx⟩)
  simp only [F] at hFx
  have hb1 : |S.κ x * S.A' a s (S.Ψ x)| ≤ M := by
    have := Finset.sum_nonneg fun α (_ : α ∈ Finset.univ) => Finset.sum_nonneg
      fun β (_ : β ∈ Finset.univ) => abs_nonneg (d2 (S.u' a s) (S.Ψ x) α β)
    have := Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => abs_nonneg (d (S.u' a s) (S.Ψ x) k)
    linarith
  have hb2 : ∀ α β, |d2 (S.u' a s) (S.Ψ x) α β| ≤ M := fun α β => by
    have h1 : |d2 (S.u' a s) (S.Ψ x) α β| ≤ ∑ α, ∑ β, |d2 (S.u' a s) (S.Ψ x) α β| :=
      (Finset.single_le_sum (f := fun β => |d2 (S.u' a s) (S.Ψ x) α β|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ β)).trans
        (Finset.single_le_sum (f := fun α => ∑ β, |d2 (S.u' a s) (S.Ψ x) α β|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ α))
    have := Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => abs_nonneg (d (S.u' a s) (S.Ψ x) k)
    linarith [abs_nonneg (S.κ x * S.A' a s (S.Ψ x))]
  have hb3 : ∀ k, |d (S.u' a s) (S.Ψ x) k| ≤ M := fun k => by
    have h1 := Finset.single_le_sum (f := fun k => |d (S.u' a s) (S.Ψ x) k|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
    have := Finset.sum_nonneg fun α (_ : α ∈ Finset.univ) => Finset.sum_nonneg
      fun β (_ : β ∈ Finset.univ) => abs_nonneg (d2 (S.u' a s) (S.Ψ x) α β)
    linarith [abs_nonneg (S.κ x * S.A' a s (S.Ψ x))]
  have hsJ : s ∈ S.J := hJ hs
  have hxV := hKV hx
  rw [box_wb hS a hsJ hxV]
  have t1 : (S.φ a x - s) * S.A a s x = 0 := by
    rcases hsx.lt_or_eq with h | h
    · rw [hS.wave_zero a s hsJ x hxV h, mul_zero]
    · rw [h, sub_self, zero_mul]
  have t2 : |S.κ x * ((S.φ' a (S.Ψ x) - s) * S.A' a s (S.Ψ x))| ≤ M * |S.φb a x| := by
    by_cases h : s < S.φ' a (S.Ψ x)
    · rw [hS.wave_zero' a s hsJ _ (hS.mapsTo_Ψ hxV) h]; simp; positivity
    · push Not at h
      have e : S.κ x * ((S.φ' a (S.Ψ x) - s) * S.A' a s (S.Ψ x)) =
          (S.κ x * S.A' a s (S.Ψ x)) * (S.φ' a (S.Ψ x) - s) := by ring
      rw [e, abs_mul]
      have : |S.φ' a (S.Ψ x) - s| ≤ |S.φb a x| := by
        rw [abs_of_nonpos (by linarith), StepData.φb_def]
        exact (le_abs_self _).trans' (by linarith)
      exact mul_le_mul hb1 this (abs_nonneg _) hM0.le
  have t3 := abs_sum_sum_mul_le (fun α β => S.gb x α β) _ hb2
  have t4 := abs_sum_mul_le Finset.univ (fun k => S.θb x k) _ fun k _ => hb3 k
  rw [t1, zero_sub]
  set g1 := ∑ α, ∑ β, |S.gb x α β|
  set θ1 := ∑ k, |S.θb x k|
  have hle : |-(S.κ x * ((S.φ' a (S.Ψ x) - s) * S.A' a s (S.Ψ x))) +
      (∑ α, ∑ β, S.gb x α β * d2 (S.u' a s) (S.Ψ x) α β +
        ∑ k, S.θb x k * d (S.u' a s) (S.Ψ x) k)| ≤ M * g1 + M * θ1 + M * |S.φb a x| := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg]
    refine (add_le_add t2 (abs_add_le _ _)).trans ?_
    nlinarith [t3, t4]
  have hsq := sq_le_sq' (neg_le_of_abs_le hle) (le_of_abs_le hle)
  refine hsq.trans ?_
  have := sq_add3_le (M * g1) (M * θ1) (M * |S.φb a x|)
  simp only [Gq_def, Θq_def, Pq_def]
  rw [← sq_abs (S.φb a x)]
  nlinarith

/-- Steps 1, 2 on the fronts `Γ_{a,s}`, `s = φ_a(x)`. -/
theorem bound_transport (a : ι) : ∃ C, 0 ≤ C ∧ ∀ x ∈ K,
    S.Mq a x ≤ C * (S.Zq a x ^ 2 + S.wb a (S.φ a x) x ^ 2 + S.Gq x + S.Pq a x + S.Qq a x) := by
  obtain ⟨c₀, hc₀, hc₀u⟩ := exists_pos_le_of_continuousOn hK
    ((hS.continuousOn_param (hS.smooth_u a) a).mono hKV)
    fun x hx => hS.pos a _ (hS.mem_J a x (hKV hx)) x (hKV hx) rfl
  set F : E n → ℝ := fun x => |S.κ x * box S.g' (S.φ' a) (S.Ψ x)| +
    |S.u a (S.φ a x) x| * ∑ α, ∑ β, |d2 (S.φ' a) (S.Ψ x) α β| +
    (∑ α, |d (S.φ' a) (S.Ψ x) α|) * (∑ β, |d (S.u' a (S.φ a x)) (S.Ψ x) β|) +
    (∑ j, ∑ k, |(S.g x)⁻¹ j k|) * ‖d (fun y => S.u' a (S.φ a x) (S.Ψ y)) x‖ +
    |S.κ x * S.B' a (S.φ a x) (S.Ψ x)|
  have hF : ContinuousOn F S.V := by
    have hκ := hS.contDiffOn_κ.continuousOn
    refine ((((hκ.mul (hS.continuousOn_comp_Ψ
      (hS.continuousOn_box' (hS.eikonal' a).smooth))).abs.add
      ((hS.continuousOn_param (hS.smooth_u a) a).abs.mul (continuousOn_finsetSum _ fun α _ =>
        continuousOn_finsetSum _ fun β _ => (hS.continuousOn_comp_Ψ
          (contDiffOn_d2_of_isOpen hS.isOpen_V' (hS.eikonal' a).smooth α β).continuousOn).abs))).add
      ((continuousOn_finsetSum _ fun α _ => (hS.continuousOn_comp_Ψ
        (hS.continuousOn_d' (hS.eikonal' a).smooth α)).abs).mul
        (continuousOn_finsetSum _ fun β _ =>
          (hS.continuousOn_param'_d_Ψ (hS.smooth_u' a) a β).abs))).add
      ((continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun k _ =>
        (hS.contDiffOn_g_inv j k).continuousOn.abs).mul
        (continuousOn_pi.2 fun k => hS.continuousOn_param_d (U := fun s y => S.u' a s (S.Ψ y))
          (hS.contDiffOn_u'Ψ a) a k).norm)).add
      (hκ.mul (hS.continuousOn_param'_Ψ (hS.continuous_B' a) a)).abs
  obtain ⟨M, hM0, hM⟩ := exists_abs_le_of_continuousOn hK (hF.mono hKV)
  refine ⟨5 * ((2 + 3 * M) / c₀) ^ 2, by positivity, fun x hx => ?_⟩
  have hxV := hKV hx
  have hsJ := hS.mem_J a x hxV
  set s := S.φ a x with hs
  have hFx : F x ≤ M := (le_abs_self _).trans (hM x hx)
  set D2 := ∑ α, ∑ β, |d2 (S.φ' a) (S.Ψ x) α β|
  set D1 := ∑ α, |d (S.φ' a) (S.Ψ x) α|
  set U1 := ∑ β, |d (S.u' a s) (S.Ψ x) β|
  set Mg := ∑ j, ∑ k, |(S.g x)⁻¹ j k|
  set du := ‖d (fun y => S.u' a s (S.Ψ y)) x‖
  have hD2 : 0 ≤ D2 := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hD1 : 0 ≤ D1 := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hU1 : 0 ≤ U1 := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hMg : 0 ≤ Mg := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hdu : 0 ≤ du := norm_nonneg _
  have hF1 : 0 ≤ |S.u a s x| * D2 := by positivity
  have hF2 : 0 ≤ D1 * U1 := by positivity
  have hF3 : 0 ≤ Mg * du := by positivity
  have hb1 : |S.κ x * box S.g' (S.φ' a) (S.Ψ x)| ≤ M := by
    simp only [F] at hFx; linarith [abs_nonneg (S.κ x * S.B' a s (S.Ψ x))]
  have hb2 : |S.u a s x| * D2 ≤ M := by
    simp only [F] at hFx; linarith [abs_nonneg (S.κ x * S.B' a s (S.Ψ x)),
      abs_nonneg (S.κ x * box S.g' (S.φ' a) (S.Ψ x))]
  have hb3 : D1 * U1 ≤ M := by
    simp only [F] at hFx; linarith [abs_nonneg (S.κ x * S.B' a s (S.Ψ x)),
      abs_nonneg (S.κ x * box S.g' (S.φ' a) (S.Ψ x))]
  have hb4 : Mg * du ≤ M := by
    simp only [F] at hFx; linarith [abs_nonneg (S.κ x * S.B' a s (S.Ψ x)),
      abs_nonneg (S.κ x * box S.g' (S.φ' a) (S.Ψ x))]
  have hb5 : |S.κ x * S.B' a s (S.Ψ x)| ≤ M := by
    simp only [F] at hFx; linarith [abs_nonneg (S.κ x * box S.g' (S.φ' a) (S.Ψ x))]
  set g1 := ∑ α, ∑ β, |S.gb x α β|
  have hg1 : 0 ≤ g1 := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have t2 : |S.κ x * S.wb a s x * box S.g' (S.φ' a) (S.Ψ x)| ≤ M * |S.wb a s x| := by
    rw [show S.κ x * S.wb a s x * box S.g' (S.φ' a) (S.Ψ x) =
      (S.κ x * box S.g' (S.φ' a) (S.Ψ x)) * S.wb a s x by ring, abs_mul]
    exact mul_le_mul_of_nonneg_right hb1 (abs_nonneg _)
  have t3 : |S.u a s x * ∑ α, ∑ β, S.gb x α β * d2 (S.φ' a) (S.Ψ x) α β| ≤ M * g1 := by
    have h := abs_sum_sum_mul_le (fun α β => S.gb x α β) (fun α β => d2 (S.φ' a) (S.Ψ x) α β)
      (M := D2) fun α β =>
        (Finset.single_le_sum (f := fun β => |d2 (S.φ' a) (S.Ψ x) α β|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ β)).trans
          (Finset.single_le_sum (f := fun α => ∑ β, |d2 (S.φ' a) (S.Ψ x) α β|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ α))
    rw [abs_mul]
    calc |S.u a s x| * |∑ α, ∑ β, S.gb x α β * d2 (S.φ' a) (S.Ψ x) α β|
        ≤ |S.u a s x| * (g1 * D2) := mul_le_mul_of_nonneg_left h (abs_nonneg _)
      _ = (|S.u a s x| * D2) * g1 := by ring
      _ ≤ M * g1 := mul_le_mul_of_nonneg_right hb2 hg1
  have t4 : |∑ α, ∑ β, S.gb x α β * d (S.φ' a) (S.Ψ x) α * d (S.u' a s) (S.Ψ x) β| ≤
      M * g1 := by
    have h := abs_sum_sum_mul_le (fun α β => S.gb x α β)
      (fun α β => d (S.φ' a) (S.Ψ x) α * d (S.u' a s) (S.Ψ x) β) (M := D1 * U1) fun α β => by
        rw [abs_mul]
        exact mul_le_mul (Finset.single_le_sum (f := fun α => |d (S.φ' a) (S.Ψ x) α|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ α))
          (Finset.single_le_sum (f := fun β => |d (S.u' a s) (S.Ψ x) β|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ β)) (abs_nonneg _) hD1
    simp only [mul_assoc] at h ⊢
    calc _ ≤ g1 * (D1 * U1) := h
      _ ≤ g1 * M := mul_le_mul_of_nonneg_left hb3 hg1
      _ = M * g1 := by ring
  have t5 : |coform S.g x (d (S.φb a) x) (d (fun y => S.u' a s (S.Ψ y)) x)| ≤
      M * ‖d (S.φb a) x‖ := by
    refine (abs_coform_le _ _ _ _).trans ?_
    calc Mg * ‖d (S.φb a) x‖ * du = (Mg * du) * ‖d (S.φb a) x‖ := by ring
      _ ≤ M * ‖d (S.φb a) x‖ := mul_le_mul_of_nonneg_right hb4 (norm_nonneg _)
  have t6 : |S.κ x * ((S.φ' a (S.Ψ x) - s) * S.B' a s (S.Ψ x))| ≤ M * |S.φb a x| := by
    rw [show S.κ x * ((S.φ' a (S.Ψ x) - s) * S.B' a s (S.Ψ x)) =
      (S.κ x * S.B' a s (S.Ψ x)) * (-S.φb a x) by simp only [φb_def, hs]; ring, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_right hb5 (abs_nonneg _)
  have hid := transport_wb hS a hsJ hxV
  rw [hs, sub_self, zero_mul, sub_zero, ← hs] at hid
  set Y := S.T a x - box S.g (S.φb a) x
  rw [← T_def S a x] at hid
  have hY : S.u a s x * Y = _ := hid
  have habs : |S.u a s x| * |Y| ≤ (2 + 3 * M) * (|S.Zq a x| + |S.wb a s x| + g1 +
      ‖d (S.φb a) x‖ + |S.φb a x|) := by
    rw [← abs_mul, hY]
    have hZ : |2 * -coform S.g x (d (S.φ a) x) (d (S.wb a s) x)| = 2 * |S.Zq a x| := by
      rw [abs_mul, abs_neg, abs_two, Zq_def]
    have h4' : |2 * ∑ α, ∑ β, S.gb x α β * d (S.φ' a) (S.Ψ x) α * d (S.u' a s) (S.Ψ x) β| =
        2 * |∑ α, ∑ β, S.gb x α β * d (S.φ' a) (S.Ψ x) α * d (S.u' a s) (S.Ψ x) β| := by
      rw [abs_mul, abs_two]
    have h5' : |2 * coform S.g x (d (S.φb a) x) (d (fun y => S.u' a s (S.Ψ y)) x)| =
        2 * |coform S.g x (d (S.φb a) x) (d (fun y => S.u' a s (S.Ψ y)) x)| := by
      rw [abs_mul, abs_two]
    refine (abs_six_le _ _ _ _ _ _).trans ?_
    rw [hZ, h4', h5']
    have := mul_nonneg hM0.le (abs_nonneg (S.Zq a x))
    have := mul_nonneg hM0.le (abs_nonneg (S.wb a s x))
    have := mul_nonneg hM0.le (abs_nonneg (S.φb a x))
    have := mul_nonneg hM0.le (norm_nonneg (d (S.φb a) x))
    have := mul_nonneg hM0.le hg1
    have := abs_nonneg (S.wb a s x)
    have := abs_nonneg (S.φb a x)
    have := norm_nonneg (d (S.φb a) x)
    nlinarith [t2, t3, t4, t5, t6]
  have hu : c₀ ≤ |S.u a s x| := (hc₀u x hx).trans (le_abs_self _)
  have hY2 : |Y| ≤ (2 + 3 * M) / c₀ * (|S.Zq a x| + |S.wb a s x| + g1 +
      ‖d (S.φb a) x‖ + |S.φb a x|) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc₀]
    calc |Y| * c₀ ≤ |Y| * |S.u a s x| := mul_le_mul_of_nonneg_left hu (abs_nonneg _)
      _ = |S.u a s x| * |Y| := by ring
      _ ≤ _ := habs
  have hsq := pow_le_pow_left₀ (abs_nonneg Y) hY2 2
  rw [sq_abs, mul_pow] at hsq
  have h5 := sq_add5_le (|S.Zq a x|) (|S.wb a s x|) g1 (‖d (S.φb a) x‖) (|S.φb a x|)
  simp only [sq_abs] at h5
  have hk : 0 ≤ ((2 + 3 * M) / c₀) ^ 2 := sq_nonneg _
  simp only [Mq_def, Gq_def, Pq_def, Qq_def]
  calc Y ^ 2 ≤ _ := hsq
    _ ≤ ((2 + 3 * M) / c₀) ^ 2 * (5 * (S.Zq a x ^ 2 + S.wb a s x ^ 2 + g1 ^ 2 +
        ‖d (S.φb a) x‖ ^ 2 + S.φb a x ^ 2)) := mul_le_mul_of_nonneg_left h5 hk
    _ = _ := by ring

/-- `T_a² ≤ C |θ̄|²`. -/
theorem bound_T (a : ι) : ∃ C, 0 ≤ C ∧ ∀ x ∈ K, S.Tq a x ≤ C * S.Θq x := by
  have hF : ContinuousOn (fun x => ∑ k, |d (S.φ' a) (S.Ψ x) k|) S.V :=
    continuousOn_finsetSum _ fun k _ =>
      (hS.continuousOn_comp_Ψ (hS.continuousOn_d' (hS.eikonal' a).smooth k)).abs
  obtain ⟨M, hM0, hM⟩ := exists_abs_le_of_continuousOn hK (hF.mono hKV)
  refine ⟨M ^ 2, by positivity, fun x hx => ?_⟩
  have hb : ∀ k ∈ Finset.univ, |d (S.φ' a) (S.Ψ x) k| ≤ M := fun k _ =>
    (Finset.single_le_sum (f := fun k => |d (S.φ' a) (S.Ψ x) k|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ k)).trans ((le_abs_self _).trans (hM x hx))
  have h := abs_sum_mul_le Finset.univ (fun k => S.θb x k) _ hb
  have h2 := sq_le_sq' (neg_le_of_abs_le h) (le_of_abs_le h)
  simp only [Tq_def, T_def, Θq_def]
  nlinarith

/-- The basis property (L3): `|θ̄|² ≤ C Σ_i T_{e i}²`. -/
theorem bound_basis : ∃ C, 0 ≤ C ∧ ∀ x ∈ K, S.Θq x ≤ C * ∑ i, S.Tq (S.e i) x := by
  set F : E n → (Fin (n + 1) → ℝ) → ℝ := fun x θ =>
    ∑ i, (∑ k, θ k * d (S.φ' (S.e i)) (S.Ψ x) k) ^ 2
  have hF : ContinuousOn (fun p : E n × (Fin (n + 1) → ℝ) => F p.1 p.2) (K ×ˢ univ) := by
    refine continuousOn_finsetSum _ fun i _ => (continuousOn_finsetSum _ fun k _ => ?_).pow 2
    exact ((continuous_apply k).comp continuous_snd).continuousOn.mul
      ((hS.continuousOn_comp_Ψ (hS.continuousOn_d' (hS.eikonal' (S.e i)).smooth k)).comp
        continuousOn_fst fun p hp => hKV hp.1)
  have hhom : ∀ x (t : ℝ) θ, F x (t • θ) = t ^ 2 * F x θ := by
    intro x t θ
    simp only [F, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_pow, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  have hpos : ∀ x ∈ K, ∀ θ, θ ≠ 0 → 0 < F x θ := fun x hx θ hθ =>
    sum_sq_dotProduct_pos (hS.basis _ (hS.mapsTo_Ψ (hKV hx))) hθ
  obtain ⟨c, hc, hcF⟩ := exists_coercive_on hK hF hhom hpos
  refine ⟨((n : ℝ) + 1) ^ 2 / c, by positivity, fun x hx => ?_⟩
  have h1 := hcF x hx (S.θb x)
  have h2 := sum_abs_le_card_mul_norm (S.θb x)
  have h3 : S.Θq x ≤ ((n : ℝ) + 1) ^ 2 * ‖S.θb x‖ ^ 2 := by
    simp only [Θq_def]
    rw [← mul_pow]
    exact pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _) h2 2
  have h4 : F x (S.θb x) = ∑ i, S.Tq (S.e i) x := by simp only [F, Tq_def, T_def]
  rw [h4] at h1
  calc S.Θq x ≤ ((n : ℝ) + 1) ^ 2 * ‖S.θb x‖ ^ 2 := h3
    _ ≤ ((n : ℝ) + 1) ^ 2 * ((∑ i, S.Tq (S.e i) x) / c) := by
        gcongr; rw [le_div_iff₀ hc]; linarith
    _ = _ := by ring

/-- The spanning property (L4) and Step 3: `|ḡ|² ≤ C Σ_a |dφ̄_a|²`. -/
theorem bound_span [Fintype ι] : ∃ C, 0 ≤ C ∧ ∀ x ∈ K, S.Gq x ≤ C * ∑ a, S.Qq a x := by
  set F : E n → (Fin (n + 1) → Fin (n + 1) → ℝ) → ℝ := fun x M =>
    (∑ α, ∑ β, S.g' (S.Ψ x) α β * M α β) ^ 2 +
      ∑ a, (∑ α, ∑ β, M α β * d (S.φ' a) (S.Ψ x) α * d (S.φ' a) (S.Ψ x) β) ^ 2 +
      ∑ α, ∑ β, (M α β - M β α) ^ 2
  have hM : ∀ α β, Continuous fun p : E n × (Fin (n + 1) → Fin (n + 1) → ℝ) => p.2 α β :=
    fun α β => (continuous_apply β).comp ((continuous_apply α).comp continuous_snd)
  have hx : ∀ {f : E n → ℝ}, ContinuousOn f S.V →
      ContinuousOn (fun p : E n × (Fin (n + 1) → Fin (n + 1) → ℝ) => f p.1) (K ×ˢ univ) :=
    fun hf => hf.comp continuousOn_fst fun p hp => hKV hp.1
  have hF : ContinuousOn (fun p => F p.1 p.2) (K ×ˢ univ) := by
    refine (((continuousOn_finsetSum _ fun α _ => continuousOn_finsetSum _ fun β _ =>
      (hx (hS.contDiffOn_g'Ψ α β).continuousOn).mul (hM α β).continuousOn).pow 2).add
      (continuousOn_finsetSum _ fun a _ => (continuousOn_finsetSum _ fun α _ =>
        continuousOn_finsetSum _ fun β _ => ?_).pow 2)).add
      (continuousOn_finsetSum _ fun α _ => continuousOn_finsetSum _ fun β _ =>
        ((hM α β).sub (hM β α)).continuousOn.pow 2)
    exact ((hM α β).continuousOn.mul (hx (hS.continuousOn_comp_Ψ
      (hS.continuousOn_d' (hS.eikonal' a).smooth α)))).mul
      (hx (hS.continuousOn_comp_Ψ (hS.continuousOn_d' (hS.eikonal' a).smooth β)))
  have hhom : ∀ x (t : ℝ) M, F x (t • M) = t ^ 2 * F x M := by
    intro x t M
    simp only [F, Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum]
    congr 1
    congr 1
    · rw [← mul_pow, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun α _ => by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun β _ => by ring
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [← mul_pow, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun α _ => by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun β _ => by ring
    · exact Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => by ring
  have hpos : ∀ x ∈ K, ∀ M, M ≠ 0 → 0 < F x M := by
    intro x hxK M hM0
    have hA : 0 ≤ (∑ α, ∑ β, S.g' (S.Ψ x) α β * M α β) ^ 2 := sq_nonneg _
    have hB : 0 ≤ ∑ a, (∑ α, ∑ β, M α β * d (S.φ' a) (S.Ψ x) α * d (S.φ' a) (S.Ψ x) β) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hC : 0 ≤ ∑ α, ∑ β, (M α β - M β α) ^ 2 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    refine lt_of_le_of_ne (by simp only [F]; positivity) fun hF0 => hM0 ?_
    have hF0' := hF0.symm
    simp only [F] at hF0'
    have eA : (∑ α, ∑ β, S.g' (S.Ψ x) α β * M α β) ^ 2 = 0 := by linarith
    have eB : ∑ a, (∑ α, ∑ β, M α β * d (S.φ' a) (S.Ψ x) α * d (S.φ' a) (S.Ψ x) β) ^ 2 = 0 := by
      linarith
    have eC : ∑ α, ∑ β, (M α β - M β α) ^ 2 = 0 := by linarith
    refine eq_zero_of_span (hS.span _ (hS.mapsTo_Ψ (hKV hxK))) (fun α β => ?_)
      (pow_eq_zero_iff two_ne_zero |>.1 eA) fun a => ?_
    · have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun α _ => Finset.sum_nonneg
        fun β _ => sq_nonneg (M α β - M β α)).1 eC α (Finset.mem_univ _)
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun β _ => sq_nonneg (M α β - M β α)).1 h1 β
        (Finset.mem_univ _)
      exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)
    · have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun a _ => sq_nonneg
        (∑ α, ∑ β, M α β * d (S.φ' a) (S.Ψ x) α * d (S.φ' a) (S.Ψ x) β)).1 eB a
        (Finset.mem_univ _)
      exact pow_eq_zero_iff two_ne_zero |>.1 h1
  obtain ⟨c, hc, hcF⟩ := exists_coercive_on hK hF hhom hpos
  have hG : ContinuousOn (fun x => ∑ j, ∑ k, |(S.g x)⁻¹ j k|) S.V :=
    continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun k _ =>
      (hS.contDiffOn_g_inv j k).continuousOn.abs
  obtain ⟨Mg, hMg0, hMg⟩ := exists_abs_le_of_continuousOn hK (hG.mono hKV)
  have hD : ContinuousOn (fun x => ∑ a, (‖d (S.φ a) x‖ + ‖d (S.φb a) x‖)) S.V :=
    continuousOn_finsetSum _ fun a _ => (hS.continuousOn_norm_d (hS.eikonal a).smooth).add
      (hS.continuousOn_norm_d (hS.contDiffOn_φb a))
  obtain ⟨M₁, hM₁0, hM₁⟩ := exists_abs_le_of_continuousOn hK (hD.mono hKV)
  refine ⟨((n : ℝ) + 1) ^ 4 / c * (9 * Mg ^ 2 * M₁ ^ 2), by positivity, fun x hxK => ?_⟩
  have hxV := hKV hxK
  have hMgx : ∑ j, ∑ k, |(S.g x)⁻¹ j k| ≤ Mg := (le_abs_self _).trans (hMg x hxK)
  have hM₁x : ∀ a, ‖d (S.φ a) x‖ + ‖d (S.φb a) x‖ ≤ M₁ := fun a =>
    (Finset.single_le_sum (f := fun a => ‖d (S.φ a) x‖ + ‖d (S.φb a) x‖)
      (fun _ _ => by positivity) (Finset.mem_univ a)).trans ((le_abs_self _).trans (hM₁ x hxK))
  have hnull : ∀ a, (∑ α, ∑ β, S.gb x α β * d (S.φ' a) (S.Ψ x) α * d (S.φ' a) (S.Ψ x) β) ^ 2 ≤
      9 * Mg ^ 2 * M₁ ^ 2 * S.Qq a x := by
    intro a
    rw [gb_null hS a hxV, coform_sub_left, coform_sub_right, coform_sub_right,
      (hS.eikonal a).null x hxV, coform_symm (hS.lorentzian_g x) (d (S.φb a) x) (d (S.φ a) x)]
    set p := ‖d (S.φ a) x‖
    set q := ‖d (S.φb a) x‖
    have h1 := abs_coform_le S.g x (d (S.φ a) x) (d (S.φb a) x)
    have h2 := abs_coform_le S.g x (d (S.φb a) x) (d (S.φb a) x)
    have hp : 0 ≤ p := norm_nonneg _
    have hq : 0 ≤ q := norm_nonneg _
    have hpq := hM₁x a
    have h3 : |0 - coform S.g x (d (S.φ a) x) (d (S.φb a) x) -
        (coform S.g x (d (S.φ a) x) (d (S.φb a) x) -
          coform S.g x (d (S.φb a) x) (d (S.φb a) x))| ≤ 3 * Mg * M₁ * q := by
      have e : 0 - coform S.g x (d (S.φ a) x) (d (S.φb a) x) -
          (coform S.g x (d (S.φ a) x) (d (S.φb a) x) -
            coform S.g x (d (S.φb a) x) (d (S.φb a) x)) =
          -(2 * coform S.g x (d (S.φ a) x) (d (S.φb a) x)) +
            coform S.g x (d (S.φb a) x) (d (S.φb a) x) := by ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      rw [abs_neg, abs_mul, abs_two]
      have h4 : (∑ j, ∑ k, |(S.g x)⁻¹ j k|) * p * q ≤ Mg * M₁ * q := by
        have : (∑ j, ∑ k, |(S.g x)⁻¹ j k|) * p ≤ Mg * M₁ :=
          mul_le_mul hMgx (by linarith) hp hMg0.le
        exact mul_le_mul_of_nonneg_right this hq
      have h5 : (∑ j, ∑ k, |(S.g x)⁻¹ j k|) * q * q ≤ Mg * M₁ * q := by
        have : (∑ j, ∑ k, |(S.g x)⁻¹ j k|) * q ≤ Mg * M₁ :=
          mul_le_mul hMgx (by linarith) hq hMg0.le
        exact mul_le_mul_of_nonneg_right this hq
      linarith
    have := sq_le_sq' (neg_le_of_abs_le h3) (le_of_abs_le h3)
    simp only [Qq_def]
    nlinarith
  have hFg : F x (fun α β => S.gb x α β) =
      ∑ a, (∑ α, ∑ β, S.gb x α β * d (S.φ' a) (S.Ψ x) α * d (S.φ' a) (S.Ψ x) β) ^ 2 := by
    simp only [F, sum_g'_mul_gb hS x, hS.gb_symm x]
    simp
  have h1 := hcF x hxK fun α β => S.gb x α β
  rw [hFg] at h1
  have h2 : ∑ α, ∑ β, |S.gb x α β| ≤ ((n : ℝ) + 1) ^ 2 * ‖fun α β => S.gb x α β‖ := by
    calc ∑ α, ∑ β, |S.gb x α β| ≤ ∑ _α : Fin (n + 1), ∑ _β : Fin (n + 1),
          ‖fun α β => S.gb x α β‖ := Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun β _ =>
            (norm_le_pi_norm (fun β => S.gb x α β) β).trans
              (norm_le_pi_norm (fun α β => S.gb x α β) α)
      _ = _ := by simp; ring
  have h3 : S.Gq x ≤ ((n : ℝ) + 1) ^ 4 * ‖fun α β => S.gb x α β‖ ^ 2 := by
    simp only [Gq_def]
    calc (∑ α, ∑ β, |S.gb x α β|) ^ 2 ≤ (((n : ℝ) + 1) ^ 2 * ‖fun α β => S.gb x α β‖) ^ 2 :=
          pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
            abs_nonneg _) h2 2
      _ = _ := by ring
  have h4 : ∑ a, (∑ α, ∑ β, S.gb x α β * d (S.φ' a) (S.Ψ x) α * d (S.φ' a) (S.Ψ x) β) ^ 2 ≤
      9 * Mg ^ 2 * M₁ ^ 2 * ∑ a, S.Qq a x := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun a _ => hnull a
  calc S.Gq x ≤ ((n : ℝ) + 1) ^ 4 * ‖fun α β => S.gb x α β‖ ^ 2 := h3
    _ ≤ ((n : ℝ) + 1) ^ 4 * ((9 * Mg ^ 2 * M₁ ^ 2 * ∑ a, S.Qq a x) / c) := by
        gcongr; rw [le_div_iff₀ hc]; linarith
    _ = _ := by ring

end StepData

end

end LorentzianCalderon
