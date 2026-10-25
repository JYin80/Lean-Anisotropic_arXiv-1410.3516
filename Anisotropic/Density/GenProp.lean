import Anisotropic.Density.SelfConsistent

/-!
# Asymptotics of `m` and Lemma 4.10

For `σ ≥ 0` and `z ∈ ℂ₊`, the solution `m(z)` of `f(m) = z` satisfies `m(z) = -1/z + O(|z|⁻²)`
for large `|z|`. Under (phi_bounded), (bound_Sigma) and (Sigma_gap), Lemma 4.10 (`lem:gen_prop_m`)
gives `|m| ≍ 1` and `Im m ≳ Im z` on `τ ≤ |z| ≤ τ⁻¹`, with the explicit constant
`C(τ) = (2 + τ)² / τ⁴`.
-/

open MeasureTheory Polynomial Filter Topology
open scoped ENNReal

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! ## A bound on the sum in `f` -/

private lemma gp_term_le (N : ℕ) {a : ℝ} (ha : 0 ≤ a) {w : ℂ} (hw : a * ‖w‖ ≤ 1 / 2) :
    ‖(a : ℂ) / (N * (1 + a * w))‖ ≤ 2 * (a / N) := by
  have h1 : 1 / 2 ≤ ‖1 + (a : ℂ) * w‖ := by
    have h := norm_sub_le (1 + (a : ℂ) * w) ((a : ℂ) * w)
    have h2 : ‖(a : ℂ) * w‖ = a * ‖w‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha]
    rw [add_sub_cancel_right, norm_one] at h
    linarith
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp
  · have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha, Complex.norm_natCast,
      div_le_iff₀ (by positivity)]
    have : 2 * (a / N) * (N * ‖1 + (a : ℂ) * w‖) = a * (2 * ‖1 + (a : ℂ) * w‖) := by
      field_simp
    rw [this]
    nlinarith

private lemma gp_sum_le (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {w : ℂ}
    (hw : ∀ i, σ i * ‖w‖ ≤ 1 / 2) :
    ‖∑ i, (σ i : ℂ) / (N * (1 + σ i * w))‖ ≤ 2 * ∑ i, σ i / N := by
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => gp_term_le N (hσ i) (hw i)

private lemma gp_sum_nonneg_le (N : ℕ) (σ : Fin M → ℝ) {b : ℝ}
    (hb : ∀ i, σ i ≤ b) : ∑ i, σ i / N ≤ M * b / N := by
  rw [← Finset.sum_div]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  · have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    refine div_le_div_of_nonneg_right ?_ hNr.le
    calc ∑ i, σ i ≤ ∑ _i : Fin M, b := Finset.sum_le_sum fun i _ => hb i
      _ = M * b := by simp

private lemma gp_sum_nonneg (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) :
    0 ≤ ∑ i, σ i / N :=
  Finset.sum_nonneg fun i _ => div_nonneg (hσ i) (Nat.cast_nonneg N)

/-- The asymptotics `m(z) = -1/z + O(|z|⁻²)`, with any upper bound `s₁` of the `σ i`. -/
theorem norm_mFun_add_inv_le (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {s₁ : ℝ}
    (hs₁ : ∀ i, σ i ≤ s₁) {z : ℂ} (hz : 0 < z.im)
    (hzl : 2 * (1 + √(massRatio N σ)) * s₁ ≤ ‖z‖) :
    ‖mFun N σ z + z⁻¹‖ ≤ 2 * (1 + √(massRatio N σ)) * (∑ i, σ i / N) / ‖z‖ ^ 2 := by
  obtain ⟨hm, hfm⟩ := mFun_spec N σ hσ hz
  set m := mFun N σ z with hmdef
  have hzn : 0 < ‖z‖ := lt_of_lt_of_le hz (Complex.im_le_norm z)
  have hz0 : z ≠ 0 := norm_pos_iff.mp hzn
  have hm0 : m ≠ 0 := fun h => by simp [h] at hm
  have hmb : ‖m‖ ≤ (1 + √(massRatio N σ)) / ‖z‖ := norm_mFun_le N σ hσ hz
  set K := 1 + √(massRatio N σ) with hK
  have hK0 : 0 ≤ K := by positivity
  have hsm : ∀ i, σ i * ‖m‖ ≤ 1 / 2 := by
    intro i
    have hs : 0 ≤ s₁ := (hσ i).trans (hs₁ i)
    calc σ i * ‖m‖ ≤ σ i * (K / ‖z‖) := mul_le_mul_of_nonneg_left hmb (hσ i)
      _ ≤ s₁ * (K / ‖z‖) := mul_le_mul_of_nonneg_right (hs₁ i) (by positivity)
      _ = (K * s₁) / ‖z‖ := by ring
      _ ≤ 1 / 2 := by
        rw [div_le_iff₀ hzn]
        linarith
  have hS := gp_sum_le N σ hσ hsm
  set S := ∑ i, (σ i : ℂ) / (N * (1 + σ i * m)) with hSdef
  have hfz : -m⁻¹ + S = z := hfm
  have key : m + z⁻¹ = z⁻¹ * m * S := by
    have : S = z + m⁻¹ := by rw [← hfz]; ring
    rw [this]
    field_simp
  rw [key, norm_mul, norm_mul, norm_inv]
  have hc := gp_sum_nonneg N σ hσ
  have h1 : ‖m‖ * ‖S‖ ≤ K / ‖z‖ * (2 * ∑ i, σ i / N) :=
    mul_le_mul hmb hS (norm_nonneg _) (by positivity)
  calc ‖z‖⁻¹ * ‖m‖ * ‖S‖ = ‖z‖⁻¹ * (‖m‖ * ‖S‖) := by ring
    _ ≤ ‖z‖⁻¹ * (K / ‖z‖ * (2 * ∑ i, σ i / N)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 2 * K * (∑ i, σ i / N) / ‖z‖ ^ 2 := by field_simp

/-! ## Lemma 4.10 (`lem:gen_prop_m`) -/

/-- (phi_bounded), (bound_Sigma), (Sigma_gap) for the spectral data `σ`, with `σ ≥ 0`. -/
structure DensityAssumptions (τ : ℝ) (N : ℕ) (σ : Fin M → ℝ) : Prop where
  pos : 0 < τ
  nonneg : ∀ i, 0 ≤ σ i
  phi_lower : τ ≤ phiRatio M N
  phi_upper : phiRatio M N ≤ τ⁻¹
  bound_Sigma : ∀ i, σ i ≤ τ⁻¹
  Sigma_gap : (empMeasure σ (Set.Icc 0 τ)).toReal ≤ 1 - τ

/-- The constant `C(τ) = (2 + τ)² / τ⁴` of Lemma 4.10. -/
def genPropConst (τ : ℝ) : ℝ := (2 + τ) ^ 2 / τ ^ 4

/-- Lemma 4.10: (m_sim_1) and (Im_m_geq_c) for `τ ≤ |z| ≤ τ⁻¹`. -/
theorem gen_prop_m {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) {z : ℂ}
    (hz : 0 < z.im) (hz₁ : τ ≤ ‖z‖) (hz₂ : ‖z‖ ≤ τ⁻¹) :
    (genPropConst τ)⁻¹ ≤ ‖mFun N σ z‖ ∧ ‖mFun N σ z‖ ≤ genPropConst τ ∧
      (genPropConst τ)⁻¹ * z.im ≤ (mFun N σ z).im := by
  obtain ⟨hτ, hσ, hφl, hφu, hb, -⟩ := h
  obtain ⟨hm, hfm⟩ := mFun_spec N σ hσ hz
  set m := mFun N σ z with hmdef
  have hτi : 0 < τ⁻¹ := inv_pos.mpr hτ
  have hτ1 : τ ≤ 1 := by
    have h1 : τ ≤ τ⁻¹ := hφl.trans hφu
    by_contra hc
    exact absurd h1 (not_le.mpr ((inv_lt_one_of_one_lt₀ (not_le.mp hc)).trans (not_le.mp hc)))
  have hτi1 : 1 ≤ τ⁻¹ := one_le_inv₀ hτ |>.mpr hτ1
  have hzn : 0 < ‖z‖ := lt_of_lt_of_le hτ hz₁
  have hm0 : m ≠ 0 := fun h0 => by simp [h0] at hm
  have hmn : 0 < ‖m‖ := norm_pos_iff.mpr hm0
  -- `L = (2 + τ) / τ²` and `C = L²`
  set L : ℝ := (2 + τ) / τ ^ 2 with hL
  have hLτ : L = 2 * τ⁻¹ ^ 2 + τ⁻¹ := by
    rw [hL]; field_simp
  have hL2 : 2 * τ⁻¹ ^ 2 ≤ L := by rw [hLτ]; linarith
  have hτi2 : 1 ≤ τ⁻¹ ^ 2 := by nlinarith
  have hL1 : 1 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hC : genPropConst τ = L ^ 2 := by
    rw [genPropConst, hL]; field_simp
  have hLi : L⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL1
  have hLi0 : 0 ≤ L⁻¹ := inv_nonneg.mpr hLpos.le
  have hR : massRatio N σ ≤ τ⁻¹ := (massRatio_le_phiRatio N σ).trans hφu
  have hmb : ‖m‖ ≤ (1 + √(massRatio N σ)) / ‖z‖ := norm_mFun_le N σ hσ hz
  -- the lower bound `1 ≤ L ‖m‖`
  have hlow : 1 ≤ L * ‖m‖ := by
    by_cases hbig : τ / 2 < ‖m‖
    · calc (1 : ℝ) ≤ L * (τ / 2) := by
            rw [hL]
            rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
            nlinarith
        _ ≤ L * ‖m‖ := mul_le_mul_of_nonneg_left hbig.le hLpos.le
    · replace hbig := not_lt.mp hbig
      have hsm : ∀ i, σ i * ‖m‖ ≤ 1 / 2 := by
        intro i
        calc σ i * ‖m‖ ≤ τ⁻¹ * (τ / 2) :=
              mul_le_mul (hb i) hbig (norm_nonneg _) hτi.le
          _ = 1 / 2 := by field_simp
      have hS := gp_sum_le N σ hσ hsm
      set S := ∑ i, (σ i : ℂ) / (N * (1 + σ i * m)) with hSdef
      have hfz : -m⁻¹ + S = z := hfm
      have hmS : m⁻¹ = S - z := by rw [← hfz]; ring
      have hsum : ∑ i, σ i / N ≤ τ⁻¹ ^ 2 := by
        refine (gp_sum_nonneg_le N σ hb).trans ?_
        have : (M : ℝ) * τ⁻¹ / N = phiRatio M N * τ⁻¹ := by
          unfold phiRatio; ring
        rw [this, sq]
        exact mul_le_mul_of_nonneg_right hφu hτi.le
      have h1 : ‖m‖⁻¹ ≤ L := by
        rw [← norm_inv, hmS, hLτ]
        calc ‖S - z‖ ≤ ‖S‖ + ‖z‖ := norm_sub_le _ _
          _ ≤ 2 * τ⁻¹ ^ 2 + τ⁻¹ := by linarith
      calc (1 : ℝ) = ‖m‖⁻¹ * ‖m‖ := (inv_mul_cancel₀ hmn.ne').symm
        _ ≤ L * ‖m‖ := mul_le_mul_of_nonneg_right h1 hmn.le
  have hlow' : L⁻¹ ≤ ‖m‖ := by
    calc L⁻¹ = L⁻¹ * 1 := (mul_one _).symm
      _ ≤ L⁻¹ * (L * ‖m‖) := mul_le_mul_of_nonneg_left hlow hLi0
      _ = ‖m‖ := by field_simp
  have hCi : (genPropConst τ)⁻¹ = L⁻¹ ^ 2 := by rw [hC, inv_pow]
  refine ⟨?_, ?_, ?_⟩
  · rw [hCi]
    calc L⁻¹ ^ 2 ≤ L⁻¹ * 1 := by rw [sq]; exact mul_le_mul_of_nonneg_left hLi hLi0
      _ ≤ ‖m‖ := by rw [mul_one]; exact hlow'
  · have hK : 1 + √(massRatio N σ) ≤ 2 * τ⁻¹ := by
      have : √(massRatio N σ) ≤ τ⁻¹ := by
        exact Real.sqrt_le_iff.mpr ⟨hτi.le, by nlinarith⟩
      linarith
    calc ‖m‖ ≤ (1 + √(massRatio N σ)) / ‖z‖ := hmb
      _ ≤ (2 * τ⁻¹) / τ := by
          refine div_le_div₀ (by positivity) hK hτ hz₁
      _ = 2 * τ⁻¹ ^ 2 := by field_simp
      _ ≤ L := hL2
      _ ≤ genPropConst τ := by rw [hC, sq]; nlinarith
  · have him := im_fC N σ m
    rw [hfm] at him
    have hsum0 : 0 ≤ ∑ i, σ i ^ 2 / (N * ‖1 + (σ i : ℂ) * m‖ ^ 2) :=
      Finset.sum_nonneg fun i _ => by positivity
    have h1 : z.im ≤ m.im * (‖m‖ ^ 2)⁻¹ := by
      rw [him]
      exact mul_le_mul_of_nonneg_left (by linarith) hm.le
    have h2 : ‖m‖ ^ 2 * z.im ≤ m.im := by
      have hm2 : 0 < ‖m‖ ^ 2 := by positivity
      calc ‖m‖ ^ 2 * z.im ≤ ‖m‖ ^ 2 * (m.im * (‖m‖ ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left h1 hm2.le
        _ = m.im := by field_simp
    rw [hCi]
    calc L⁻¹ ^ 2 * z.im ≤ ‖m‖ ^ 2 * z.im :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hLi0 hlow' 2) hz.le
      _ ≤ m.im := h2

/-! ## Concrete instances -/

/-- Marchenko–Pastur: `M = 1`, `N = 2`, `σ = 1`, `φ = 1/2`, `τ = 1/20`. -/
example : DensityAssumptions (1 / 20) 2 (fun _ : Fin 1 => (1 : ℝ)) := by
  refine ⟨by norm_num, fun _ => by norm_num, ?_, ?_, fun _ => by norm_num, ?_⟩
  · simp only [phiRatio]; norm_num
  · simp only [phiRatio]; norm_num
  · have h1 : (1 : ℝ) ∉ Set.Icc 0 20⁻¹ := by norm_num
    simp [empMeasure, Set.indicator_of_notMem h1]
    norm_num


/-- Two components: `M = 2`, `N = 20`, `σ = (10, 1)`, `φ = 1/10`, `τ = 1/100`. -/
example : DensityAssumptions (1 / 100) 20 ![(10 : ℝ), 1] := by
  refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> norm_num
  · simp only [phiRatio]; norm_num
  · simp only [phiRatio]; norm_num
  · intro i; fin_cases i <;> norm_num
  · have h10 : (10 : ℝ) ∉ Set.Icc 0 100⁻¹ := by norm_num
    have h1 : (1 : ℝ) ∉ Set.Icc 0 100⁻¹ := by norm_num
    simp [empMeasure, Fin.sum_univ_two, Set.indicator_of_notMem h10, Set.indicator_of_notMem h1]
    norm_num

/-- MP, `s₁ = 1`, `z = 5 i`: the asymptotics of `m`. -/
example : ‖mFun 2 (fun _ : Fin 1 => (1 : ℝ)) (5 * Complex.I) + (5 * Complex.I)⁻¹‖ ≤
    2 * (1 + √(massRatio 2 (fun _ : Fin 1 => (1 : ℝ)))) *
      (∑ i : Fin 1, (fun _ : Fin 1 => (1 : ℝ)) i / (2 : ℕ)) / ‖(5 * Complex.I)‖ ^ 2 := by
  refine norm_mFun_add_inv_le 2 (fun _ : Fin 1 => (1 : ℝ)) (fun _ => by norm_num)
    (s₁ := 1) (fun _ => le_rfl) (by simp) ?_
  have hR : massRatio 2 (fun _ : Fin 1 => (1 : ℝ)) ≤ 1 :=
    (massRatio_le_phiRatio 2 _).trans (by simp only [phiRatio]; norm_num)
  have := Real.sqrt_le_one.mpr hR
  simp only [norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one]
  linarith

/-- MP, `τ = 1/20`, `z = i` (`τ ≤ |z| = 1 ≤ τ⁻¹`): Lemma 4.10. -/
example : (genPropConst (1 / 20))⁻¹ ≤ ‖mFun 2 (fun _ : Fin 1 => (1 : ℝ)) Complex.I‖ ∧
    ‖mFun 2 (fun _ : Fin 1 => (1 : ℝ)) Complex.I‖ ≤ genPropConst (1 / 20) ∧
      (genPropConst (1 / 20))⁻¹ * Complex.I.im ≤ (mFun 2 (fun _ : Fin 1 => (1 : ℝ)) Complex.I).im :=
  gen_prop_m (τ := 1 / 20) (N := 2) (σ := fun _ : Fin 1 => (1 : ℝ))
    (by
      refine ⟨by norm_num, fun _ => by norm_num, ?_, ?_, fun _ => by norm_num, ?_⟩
      · simp only [phiRatio]; norm_num
      · simp only [phiRatio]; norm_num
      · have h1 : (1 : ℝ) ∉ Set.Icc 0 20⁻¹ := by norm_num
        simp [empMeasure, Set.indicator_of_notMem h1]
        norm_num)
    (by simp) (by simp; norm_num) (by simp)

end Anisotropic
