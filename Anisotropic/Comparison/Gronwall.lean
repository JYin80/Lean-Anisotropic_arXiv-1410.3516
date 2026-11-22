module

public import Mathlib

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

/-! # Grönwall closures -/

/-- Mathlib's Grönwall bound with start value `a`, source `K a` and horizon `1` equals
`(2 e^K − 1) a`. -/
private lemma gronwall_const_eq (K a : ℝ) :
    gronwallBound a K (K * a) 1 = (2 * Real.exp K - 1) * a := by
  unfold gronwallBound
  by_cases hK : K = 0
  · subst hK; simp; ring
  · simp only [hK, ite_false, mul_one]
    field_simp
    ring

/-- A right derivative below `r` gives slopes below `r` at points arbitrarily close on the right. -/
private lemma gronwall_liminf_of_hasDerivAt {f : ℝ → ℝ} {d x r : ℝ} (h : HasDerivAt f d x)
    (hr : d < r) : ∃ᶠ z in 𝓝[>] x, (z - x)⁻¹ * (f z - f x) < r := by
  have h1 : Tendsto (slope f x) (𝓝[Set.Ioi x] x) (𝓝 d) :=
    (hasDerivWithinAt_iff_tendsto_slope' (s := Set.Ioi x) (by simp)).1 h.hasDerivWithinAt
  have h2 : ∀ᶠ z in 𝓝[>] x, slope f x z < r := h1.eventually_lt_const hr
  refine h2.frequently.mono fun z hz => ?_
  simpa [slope_def_field, div_eq_inv_mul] using hz

/-- Grönwall on `[0, 1]`: `Φ' ≤ K (a + Φ)`, `Φ(0) ≤ a` give `Φ(1) ≤ (2e^K − 1) a`. -/
theorem gronwall_affine {Φ Φ' : ℝ → ℝ} {K a : ℝ} (hK : 0 ≤ K) (ha : 0 ≤ a)
    (hcont : ContinuousOn Φ (Set.Icc 0 1))
    (hderiv : ∀ θ ∈ Set.Ico (0 : ℝ) 1, HasDerivAt Φ (Φ' θ) θ)
    (hbound : ∀ θ ∈ Set.Ico (0 : ℝ) 1, Φ' θ ≤ K * (a + Φ θ)) (h0 : Φ 0 ≤ a) :
    Φ 1 ≤ (2 * Real.exp K - 1) * a := by
  have key := le_gronwallBound_of_liminf_deriv_right_le (f := Φ) (f' := Φ') (δ := a) (K := K)
    (ε := K * a) (a := 0) (b := 1) hcont
    (fun x hx r hr => gronwall_liminf_of_hasDerivAt (hderiv x hx) hr) h0
    (fun x hx => by have := hbound x hx; linarith)
    1 ⟨zero_le_one, le_rfl⟩
  rw [sub_zero, gronwall_const_eq] at key
  exact key

/-- Core of `gronwall_sup`, with the uniform bound only on `[0, 1]`. -/
private lemma gronwall_sup_core {ι : Type*} [Nonempty ι] {Φ Φ' : ι → ℝ → ℝ} {K a B : ℝ}
    (hK : 0 ≤ K) (ha : 0 ≤ a) (hB : ∀ w, ∀ θ ∈ Set.Icc (0 : ℝ) 1, |Φ w θ| ≤ B)
    (hderiv : ∀ w, ∀ θ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (Φ w) (Φ' w θ) θ)
    (hbound : ∀ w, ∀ θ ∈ Set.Icc (0 : ℝ) 1, |Φ' w θ| ≤ K * (a + ⨆ w', Φ w' θ))
    (h0 : ∀ w, Φ w 0 ≤ a) : ∀ w, Φ w 1 ≤ (2 * Real.exp K - 1) * a := by
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ → ℝ, ∀ θ, Q θ = ⨆ w', Φ w' θ := ⟨_, fun _ => rfl⟩
  have hbdd : ∀ θ ∈ Set.Icc (0 : ℝ) 1, BddAbove (Set.range fun w => Φ w θ) := fun θ hθ =>
    ⟨B, by rintro _ ⟨w, rfl⟩; exact (le_abs_self _).trans (hB w θ hθ)⟩
  have hleQ : ∀ w, ∀ θ ∈ Set.Icc (0 : ℝ) 1, Φ w θ ≤ Q θ := fun w θ hθ => by
    rw [hQ]; exact le_ciSup (hbdd θ hθ) w
  have hQle : ∀ θ c, (∀ w, Φ w θ ≤ c) → Q θ ≤ c := fun θ c h => by
    rw [hQ]; exact ciSup_le h
  have hQB : ∀ θ ∈ Set.Icc (0 : ℝ) 1, Q θ ≤ B := fun θ hθ =>
    hQle θ B fun w => (le_abs_self _).trans (hB w θ hθ)
  have hB0 : 0 ≤ B := by
    obtain ⟨w⟩ := ‹Nonempty ι›
    exact (abs_nonneg _).trans (hB w 0 ⟨le_rfl, zero_le_one⟩)
  have hbound' : ∀ w, ∀ θ ∈ Set.Icc (0 : ℝ) 1, |Φ' w θ| ≤ K * (a + Q θ) := fun w θ hθ => by
    rw [hQ]; exact hbound w θ hθ
  -- uniform Lipschitz constant
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = K * (a + B) := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := hL ▸ mul_nonneg hK (add_nonneg ha hB0)
  have hderivL : ∀ w, ∀ θ ∈ Set.Icc (0 : ℝ) 1, |Φ' w θ| ≤ L := fun w θ hθ =>
    (hbound' w θ hθ).trans
      (hL ▸ mul_le_mul_of_nonneg_left (by linarith [hQB θ hθ]) hK)
  -- mean value inequality on a subinterval of `[0, 1]`
  have mvt : ∀ w, ∀ x z C : ℝ, x ∈ Set.Icc (0 : ℝ) 1 → z ∈ Set.Icc (0 : ℝ) 1 → x ≤ z →
      (∀ ξ ∈ Set.Ico x z, |Φ' w ξ| ≤ C) → |Φ w z - Φ w x| ≤ C * (z - x) := by
    intro w x z C hx hz hxz hC
    have hsub : Set.Icc x z ⊆ Set.Icc (0 : ℝ) 1 := Set.Icc_subset_Icc hx.1 hz.2
    have := norm_image_sub_le_of_norm_deriv_le_segment' (f := Φ w) (f' := Φ' w) (a := x)
      (b := z) (C := C) (fun ξ hξ => (hderiv w ξ (hsub hξ)).hasDerivWithinAt) hC z ⟨hxz, le_rfl⟩
    rwa [Real.norm_eq_abs] at this
  have hΦlip : ∀ w, ∀ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 → s ≤ t →
      |Φ w t - Φ w s| ≤ L * (t - s) := fun w s t hs ht hst =>
    mvt w s t L hs ht hst fun ξ hξ => hderivL w ξ ⟨hs.1.trans hξ.1, hξ.2.le.trans ht.2⟩
  -- `Q` is Lipschitz on `[0, 1]`
  have hQlip : ∀ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 → s ≤ t →
      Q t ≤ Q s + L * (t - s) ∧ Q s ≤ Q t + L * (t - s) := by
    intro s t hs ht hst
    constructor
    · refine hQle t _ fun w => ?_
      linarith [(abs_le.1 (hΦlip w s t hs ht hst)).2, hleQ w s hs]
    · refine hQle s _ fun w => ?_
      linarith [(abs_le.1 (hΦlip w s t hs ht hst)).1, hleQ w t ht]
  have hQcont : ContinuousOn Q (Set.Icc (0 : ℝ) 1) := by
    refine (LipschitzOnWith.of_dist_le' (K := L) ?_).continuousOn
    intro s hs t ht
    rw [Real.dist_eq, Real.dist_eq]
    have key : ∀ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 → s ≤ t →
        |Q s - Q t| ≤ L * |s - t| := fun s t hs ht hst => by
      obtain ⟨h1, h2⟩ := hQlip s t hs ht hst
      rw [abs_sub_comm s t, abs_of_nonneg (sub_nonneg.2 hst), abs_le]
      exact ⟨by linarith, by linarith⟩
    rcases le_total s t with h | h
    · exact key s t hs ht h
    · rw [abs_sub_comm (Q s), abs_sub_comm s]; exact key t s ht hs h
  -- the liminf condition for `Q`
  have hliminf : ∀ x ∈ Set.Ico (0 : ℝ) 1, ∀ r : ℝ, K * (a + Q x) < r →
      ∃ᶠ z in 𝓝[>] x, (z - x)⁻¹ * (Q z - Q x) < r := by
    intro x hx r hr
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1, hx.2.le⟩
    obtain ⟨M, hM⟩ : ∃ M : ℝ, M = K * L := ⟨_, rfl⟩
    have hM0 : 0 ≤ M := hM ▸ mul_nonneg hK hL0
    obtain ⟨c, hc⟩ : ∃ c : ℝ, c = K * (a + Q x) := ⟨_, rfl⟩
    obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (r - c) / (M + 1) := ⟨_, rfl⟩
    have hδpos : 0 < δ := hδ ▸ div_pos (by linarith) (by linarith)
    have hmem : Set.Ioo x (min 1 (x + δ)) ∈ 𝓝[>] x :=
      Ioo_mem_nhdsGT (lt_min hx.2 (by linarith))
    refine (Filter.Eventually.frequently (Filter.mem_of_superset hmem fun z hz => ?_))
    obtain ⟨hz1, hz2⟩ := hz
    have hzle : z ≤ 1 := (hz2.trans_le (min_le_left _ _)).le
    have hzδ : z < x + δ := hz2.trans_le (min_le_right _ _)
    have hz' : z ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1.trans hz1.le, hzle⟩
    have hzx : 0 < z - x := by linarith
    have hC : ∀ w, ∀ ξ ∈ Set.Ico x z, |Φ' w ξ| ≤ c + M * (z - x) := by
      intro w ξ hξ
      have hξ' : ξ ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1.trans hξ.1, hξ.2.le.trans hzle⟩
      have h1 := (hQlip x ξ hx' hξ' hξ.1).1
      have h2 : K * (a + Q ξ) ≤ K * (a + Q x + L * (ξ - x)) :=
        mul_le_mul_of_nonneg_left (by linarith) hK
      have h3 : K * (L * (ξ - x)) ≤ K * (L * (z - x)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith [hξ.2]) hL0) hK
      calc |Φ' w ξ| ≤ K * (a + Q ξ) := hbound' w ξ hξ'
        _ ≤ K * (a + Q x + L * (ξ - x)) := h2
        _ = c + K * (L * (ξ - x)) := by rw [hc]; ring
        _ ≤ c + K * (L * (z - x)) := by linarith
        _ = c + M * (z - x) := by rw [hM]; ring
    have hQz : Q z ≤ Q x + (c + M * (z - x)) * (z - x) := by
      refine hQle z _ fun w => ?_
      have := (abs_le.1 (mvt w x z _ hx' hz' hz1.le (hC w))).2
      linarith [hleQ w x hx']
    have h4 : (z - x)⁻¹ * (Q z - Q x) ≤ c + M * (z - x) := by
      rw [inv_mul_le_iff₀ hzx]; linarith
    have h5 : (M + 1) * (z - x) < r - c := by
      have := mul_lt_mul_of_pos_left (show z - x < δ by linarith) (show 0 < M + 1 by linarith)
      rwa [hδ, mul_div_cancel₀ _ (by linarith : M + 1 ≠ 0)] at this
    change (z - x)⁻¹ * (Q z - Q x) < r
    nlinarith
  have hQ0 : Q 0 ≤ a := hQle 0 a h0
  have key := le_gronwallBound_of_liminf_deriv_right_le (f := Q) (f' := fun x => K * (a + Q x))
    (δ := a) (K := K) (ε := K * a) (a := 0) (b := 1) hQcont
    (fun x hx r hr => hliminf x hx r hr) hQ0 (fun x _ => le_of_eq (by ring)) 1
    ⟨zero_le_one, le_rfl⟩
  rw [sub_zero, gronwall_const_eq] at key
  intro w
  exact (hleQ w 1 ⟨zero_le_one, le_rfl⟩).trans key

/-- Grönwall for `Q(θ) = sup_w Φ_w(θ)` (the form needed for Lemma 7.10 in Section 8). -/
theorem gronwall_sup {ι : Type*} [Nonempty ι] {Φ Φ' : ι → ℝ → ℝ} {K a B : ℝ} (hK : 0 ≤ K)
    (ha : 0 ≤ a) (hB : ∀ w θ, |Φ w θ| ≤ B)
    (hderiv : ∀ w, ∀ θ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (Φ w) (Φ' w θ) θ)
    (hbound : ∀ w, ∀ θ ∈ Set.Icc (0 : ℝ) 1, |Φ' w θ| ≤ K * (a + ⨆ w', Φ w' θ))
    (h0 : ∀ w, Φ w 0 ≤ a) : ∀ w, Φ w 1 ≤ (2 * Real.exp K - 1) * a :=
  gronwall_sup_core hK ha (fun w θ _ => hB w θ) hderiv hbound h0

/-- Instance of `gronwall_affine` at `Φ θ = θ`, `K = a = 1`: `1 ≤ 2e − 1`. -/
example : (1 : ℝ) ≤ (2 * Real.exp 1 - 1) * 1 :=
  gronwall_affine (Φ := fun θ : ℝ => θ) (Φ' := fun _ => 1) (K := 1) (a := 1) zero_le_one
    zero_le_one continuousOn_id (fun θ _ => hasDerivAt_id θ)
    (fun θ hθ => by change (1 : ℝ) ≤ 1 * (1 + θ); linarith [hθ.1]) (by norm_num)

/-- Instance of `gronwall_sup` at `ι = Unit`, `Φ θ = sin θ`, `K = a = B = 1`:
`sin 1 ≤ 2e − 1`. -/
example : Real.sin 1 ≤ (2 * Real.exp 1 - 1) * 1 :=
  gronwall_sup (ι := Unit) (Φ := fun _ θ => Real.sin θ) (Φ' := fun _ θ => Real.cos θ)
    (K := 1) (a := 1) (B := 1) zero_le_one zero_le_one (fun _ θ => Real.abs_sin_le_one θ)
    (fun _ θ _ => Real.hasDerivAt_sin θ)
    (fun _ θ hθ => by
      rw [ciSup_const, one_mul]
      have := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (hθ.2.trans (by linarith [Real.pi_gt_three]))
      linarith [Real.abs_cos_le_one θ])
    (fun _ => by simp) ()

end Anisotropic
