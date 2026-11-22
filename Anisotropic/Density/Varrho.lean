module

public import Anisotropic.MainDefs
public import Anisotropic.Density.Boundary
public import Anisotropic.Density.GenProp

@[expose] public section

/-!
# The measure `ϱ` (second half of Lemma 2.2)

For `σ ≥ 0` and `N > 0`, the measure
`ϱ = (1 - R)₊ δ₀ + 1_{(0,∞)} π⁻¹ Im m(x + i0) dx`, `R = #{i | σ_i > 0} / N`,
is a probability measure supported in `[0, X₀]`, `X₀ = (1 + √R) s₁ max(2, √(8R))` for any
`s₁ ≥ max_i σ_i`, and its Stieltjes transform is `m` on `ℂ₊` (Lemma 2.2, Definition 2.3).

Proof. For `ε > 0`, `h(w) = m(w + iε)` is holomorphic on `Im w > -ε` and `|h(w)| ≤ (1 + √R)/|w|`
for `Im w ≥ 0`. Cauchy's theorem on the rectangles `[-X, X] × [0, X]`, applied to
`(h(w) - h(a))((w - a)⁻¹ - (w - ā)⁻¹)` and `h(w)(w - ā)⁻¹`, gives
`h(a) = π⁻¹ ∫ Im h(x) (x - a)⁻¹ dx` for `a ∈ ℂ₊`, and the asymptotics `m(z) = -1/z + O(|z|⁻²)`
give `π⁻¹ ∫ Im h = 1`. The bound `Im m(w) ≤ 2 Im w (1 + √R)² / |w|²` for `|w| ≥ X₀` controls the
tails, so `ε → 0` and then a cutoff `δ → 0` around `0` give
`m(z) = -c/z + ∫_0^∞ ρ(x)(x - z)⁻¹ dx`, `c = 1 - ∫_0^∞ ρ ∈ [0, 1]`. Finally `c = (1 - R)₊`, from
`-z m(z) = 1 - N⁻¹ Σ_i σ_i m/(1 + σ_i m)` as `z = iy`, `y ↓ 0`.
-/

open MeasureTheory Polynomial Filter Topology
open scoped ENNReal

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! ## The measure `ϱ` (second half of Lemma 2.2) -/

/-! ## Decay of `Im m` -/

private lemma vr_massRatio_nonneg (N : ℕ) (σ : Fin M → ℝ) : 0 ≤ massRatio N σ := by
  unfold massRatio
  positivity

/-- For `|w| ≥ X₀ = (1 + √R) s₁ max(2, √(8R))`: `Im m(w) ≤ 2 Im w (1 + √R)² / |w|²`. -/
private lemma vr_im_mFun_le (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {s₁ : ℝ}
    (hs₁0 : 0 ≤ s₁) (hs₁ : ∀ i, σ i ≤ s₁) {w : ℂ} (hw : 0 < w.im)
    (hwl : (1 + √(massRatio N σ)) * s₁ * max 2 (√(8 * massRatio N σ)) ≤ ‖w‖) :
    (mFun N σ w).im ≤ 2 * w.im * (1 + √(massRatio N σ)) ^ 2 / ‖w‖ ^ 2 := by
  obtain ⟨hm, hfm⟩ := mFun_spec N σ hσ hw
  set μ := mFun N σ w with hμdef
  set R := massRatio N σ with hRdef
  set K := 1 + √R with hK
  have hR0 : 0 ≤ R := vr_massRatio_nonneg N σ
  have hK1 : 1 ≤ K := by have := Real.sqrt_nonneg R; linarith
  have hwn : 0 < ‖w‖ := lt_of_lt_of_le hw (Complex.im_le_norm w)
  have hμ0 : μ ≠ 0 := fun h => by simp [h] at hm
  have hμn : 0 < ‖μ‖ := norm_pos_iff.mpr hμ0
  have hmb : ‖μ‖ ≤ K / ‖w‖ := norm_mFun_le N σ hσ hw
  have hmw : ‖μ‖ * ‖w‖ ≤ K := by rwa [le_div_iff₀ hwn] at hmb
  have h2 : 2 * K * s₁ ≤ ‖w‖ := by
    refine le_trans ?_ hwl
    have : K * s₁ * 2 ≤ K * s₁ * max 2 (√(8 * R)) :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
    linarith
  have h8 : 8 * R * (K * s₁) ^ 2 ≤ ‖w‖ ^ 2 := by
    have h1 : K * s₁ * √(8 * R) ≤ ‖w‖ :=
      le_trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)) hwl
    have h3 : (K * s₁ * √(8 * R)) ^ 2 ≤ ‖w‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    rw [mul_pow, Real.sq_sqrt (by positivity)] at h3
    linarith
  have hsm : ∀ i, σ i * ‖μ‖ ≤ 1 / 2 := by
    intro i
    have h := mul_le_mul (hs₁ i) hmw (by positivity) hs₁0
    have : σ i * ‖μ‖ * (2 * ‖w‖) ≤ 1 * ‖w‖ := by nlinarith [hσ i, norm_nonneg μ]
    nlinarith
  have hden : ∀ i, 1 / 2 ≤ ‖1 + (σ i : ℂ) * μ‖ := by
    intro i
    have h := norm_sub_le (1 + (σ i : ℂ) * μ) ((σ i : ℂ) * μ)
    have h2 : ‖(σ i : ℂ) * μ‖ = σ i * ‖μ‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hσ i)]
    rw [add_sub_cancel_right, norm_one] at h
    linarith [hsm i]
  -- the sum in the key identity
  have hS : ∑ i, σ i ^ 2 / (N * ‖1 + (σ i : ℂ) * μ‖ ^ 2) ≤ 4 * R * s₁ ^ 2 := by
    have hterm : ∀ i, σ i ^ 2 / (N * ‖1 + (σ i : ℂ) * μ‖ ^ 2) ≤
        if 0 < σ i then 4 * s₁ ^ 2 / N else 0 := by
      intro i
      rcases (hσ i).eq_or_lt with h0 | hpos
      · rw [← h0]; simp
      · simp only [hpos, ↓reduceIte]
        have hd : (1 / 4 : ℝ) ≤ ‖1 + (σ i : ℂ) * μ‖ ^ 2 := by
          have := hden i
          nlinarith
        have hsq : σ i ^ 2 ≤ s₁ ^ 2 := pow_le_pow_left₀ (hσ i) (hs₁ i) 2
        rcases Nat.eq_zero_or_pos N with hN | hN
        · subst hN; simp
        · have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
          rw [div_le_div_iff₀ (by positivity) hNr]
          have h4 := mul_le_mul_of_nonneg_left hd (show 0 ≤ 4 * s₁ ^ 2 * N by positivity)
          nlinarith
    refine (Finset.sum_le_sum fun i _ => hterm i).trans ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hRdef, massRatio]
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp
    · have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
      field_simp
      rfl
  have hRm : 8 * R * s₁ ^ 2 * ‖μ‖ ^ 2 ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hmw 2)
      (show 0 ≤ 8 * R * s₁ ^ 2 by positivity)
    have h' : 8 * R * s₁ ^ 2 * ‖μ‖ ^ 2 * ‖w‖ ^ 2 ≤ 1 * ‖w‖ ^ 2 := by
      nlinarith
    exact le_of_mul_le_mul_right h' (by positivity)
  have hkey := im_fC N σ μ
  rw [hfm] at hkey
  -- `Im w ≥ Im μ |μ|⁻² / 2`
  have hbr : (‖μ‖ ^ 2)⁻¹ / 2 ≤
      (‖μ‖ ^ 2)⁻¹ - ∑ i, σ i ^ 2 / (N * ‖1 + (σ i : ℂ) * μ‖ ^ 2) := by
    have : 4 * R * s₁ ^ 2 ≤ (‖μ‖ ^ 2)⁻¹ / 2 := by
      rw [show (‖μ‖ ^ 2)⁻¹ / 2 = 1 / (2 * ‖μ‖ ^ 2) by field_simp,
        le_div_iff₀ (by positivity)]
      linarith
    linarith
  have hwim : μ.im * ((‖μ‖ ^ 2)⁻¹ / 2) ≤ w.im := by
    rw [hkey]; exact mul_le_mul_of_nonneg_left hbr hm.le
  have hμim : μ.im ≤ 2 * w.im * ‖μ‖ ^ 2 := by
    have hp : 0 < ‖μ‖ ^ 2 := by positivity
    have : μ.im = μ.im * ((‖μ‖ ^ 2)⁻¹ / 2) * (2 * ‖μ‖ ^ 2) := by field_simp
    rw [this]
    nlinarith
  have hμ2 : ‖μ‖ ^ 2 ≤ K ^ 2 / ‖w‖ ^ 2 := by
    rw [← div_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hmb 2
  calc μ.im ≤ 2 * w.im * ‖μ‖ ^ 2 := hμim
    _ ≤ 2 * w.im * (K ^ 2 / ‖w‖ ^ 2) := mul_le_mul_of_nonneg_left hμ2 (by positivity)
    _ = 2 * w.im * K ^ 2 / ‖w‖ ^ 2 := by ring

/-- `E + iη → E` within `ℂ₊` as `η ↓ 0`. -/
private lemma vr_tendsto_path (E : ℝ) :
    Tendsto (fun η : ℝ => (E : ℂ) + η * Complex.I) (𝓝[>] 0) (𝓝[upperHalf] (E : ℂ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have hc : Continuous (fun η : ℝ => (E : ℂ) + η * Complex.I) := by fun_prop
    have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using h
  · filter_upwards [self_mem_nhdsWithin] with η hη
    show 0 < ((E : ℂ) + η * Complex.I).im
    simpa using hη

/-- `Im m(E + iη) → Im m(E + i0)` as `η ↓ 0`, for real `E ≠ 0`. -/
private lemma vr_tendsto_im (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {E : ℝ} (hE : E ≠ 0) :
    Tendsto (fun η : ℝ => (mFun N σ ((E : ℂ) + η * Complex.I)).im) (𝓝[>] 0)
      (𝓝 (mExt N σ E).im) :=
  (Complex.continuous_im.tendsto _).comp
    ((tendsto_mFun_of_ne_zero N σ hσ hE).comp (vr_tendsto_path E))

/-- `Im m(E + i0) = 0` for `E > X₀`. -/
private lemma vr_im_mExt_eq_zero (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {s₁ : ℝ}
    (hs₁0 : 0 ≤ s₁) (hs₁ : ∀ i, σ i ≤ s₁) {E : ℝ}
    (hE : (1 + √(massRatio N σ)) * s₁ * max 2 (√(8 * massRatio N σ)) < E) :
    (mExt N σ E).im = 0 := by
  set K := 1 + √(massRatio N σ) with hK
  have hX0 : 0 ≤ K * s₁ * max 2 (√(8 * massRatio N σ)) := by
    have : 0 ≤ max 2 (√(8 * massRatio N σ)) := le_trans (by norm_num) (le_max_left _ _)
    positivity
  have hE0 : 0 < E := lt_of_le_of_lt hX0 hE
  refine le_antisymm ?_ (im_mExt_nonneg N σ hσ hE0.ne')
  have hg : Tendsto (fun η : ℝ => 2 * η * K ^ 2 / E ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun η : ℝ => 2 * η * K ^ 2 / E ^ 2) := by fun_prop
    have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using h
  refine le_of_tendsto_of_tendsto (vr_tendsto_im N σ hσ hE0.ne') hg ?_
  filter_upwards [self_mem_nhdsWithin] with η hη
  have hη' : (0 : ℝ) < η := hη
  have hwim : ((E : ℂ) + η * Complex.I).im = η := by simp
  have hnorm : E ≤ ‖(E : ℂ) + η * Complex.I‖ := by
    have h := Complex.abs_re_le_norm ((E : ℂ) + η * Complex.I)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero] at h
    exact le_trans (le_abs_self E) h
  have hb := vr_im_mFun_le N σ hσ hs₁0 hs₁ (w := (E : ℂ) + η * Complex.I)
    (by rw [hwim]; exact hη') (le_trans hE.le hnorm)
  rw [hwim] at hb
  refine hb.trans ?_
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact pow_le_pow_left₀ hE0.le hnorm 2

/-! ## The Poisson integral and Cauchy's theorem on the half-plane -/

private lemma vr_poisson_eq (c : ℝ) {b : ℝ} (hb : b ≠ 0) (x : ℝ) :
    ((x - c) ^ 2 + b ^ 2)⁻¹ = (b ^ 2)⁻¹ * (1 + ((x - c) / b) ^ 2)⁻¹ := by
  rw [← mul_inv, mul_add, mul_one, div_pow, mul_div_cancel₀ _ (pow_ne_zero 2 hb), add_comm]

private lemma vr_integrable_poisson (c : ℝ) {b : ℝ} (hb : b ≠ 0) :
    Integrable (fun x : ℝ => ((x - c) ^ 2 + b ^ 2)⁻¹) := by
  have h := ((integrable_inv_one_add_sq.comp_div hb).comp_sub_right c).const_mul (b ^ 2)⁻¹
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only
  rw [vr_poisson_eq c hb x]

/-- `∫ ((x - c)² + b²)⁻¹ dx = π / b` for `b > 0`. -/
private lemma vr_integral_poisson (c : ℝ) {b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ, ((x - c) ^ 2 + b ^ 2)⁻¹ = Real.pi / b := by
  simp_rw [vr_poisson_eq c hb.ne']
  rw [integral_const_mul, integral_sub_right_eq_self (fun x => (1 + (x / b) ^ 2)⁻¹) c,
    Measure.integral_comp_div (fun x => (1 + x ^ 2)⁻¹) b, integral_univ_inv_one_add_sq,
    abs_of_pos hb, smul_eq_mul]
  field_simp

/-- Cauchy's theorem on the half-plane: `∫_ℝ G = 0` if `G` is holomorphic on a neighbourhood of
`Im w ≥ 0`, integrable on `ℝ`, and `|G(w)| ≤ C |w|⁻²` for `Im w ≥ 0`, `|w| ≥ X₀`. -/
private lemma vr_integral_eq_zero {G : ℂ → ℂ}
    (hd : ∀ w : ℂ, 0 ≤ w.im → DifferentiableAt ℂ G w) (hi : Integrable (fun x : ℝ => G x))
    {C X₀ : ℝ} (hC : 0 ≤ C)
    (hb : ∀ w : ℂ, 0 ≤ w.im → X₀ ≤ ‖w‖ → ‖G w‖ ≤ C / ‖w‖ ^ 2) :
    ∫ x : ℝ, G x = 0 := by
  have hlim : Tendsto (fun X : ℝ => ∫ x in -X..X, G x) atTop (𝓝 (∫ x : ℝ, G x)) :=
    intervalIntegral_tendsto_integral hi tendsto_neg_atTop_atBot tendsto_id
  have hbound : ∀ X : ℝ, max X₀ 1 ≤ X → ‖∫ x in -X..X, G x‖ ≤ 4 * C / X := by
    intro X hX
    have hX0 : X₀ ≤ X := le_trans (le_max_left _ _) hX
    have hXp : 0 < X := by linarith [le_max_right X₀ 1]
    have hGX : ∀ w : ℂ, 0 ≤ w.im → X ≤ ‖w‖ → ‖G w‖ ≤ C / X ^ 2 := by
      intro w hw hwX
      refine (hb w hw (hX0.trans hwX)).trans ?_
      exact div_le_div_of_nonneg_left hC (by positivity) (pow_le_pow_left₀ hXp.le hwX 2)
    have h1 : (-(X : ℂ)).re = -X := by simp
    have h2 : (-(X : ℂ)).im = 0 := by simp
    have h3 : ((X : ℂ) + X * Complex.I).re = X := by simp
    have h4 : ((X : ℂ) + X * Complex.I).im = X := by simp
    have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn G
      (-(X : ℂ)) ((X : ℂ) + X * Complex.I) (fun w hw => ?_)
    · rw [h1, h2, h3, h4] at hrect
      simp only [Complex.ofReal_zero, zero_mul, add_zero] at hrect
      set T := ∫ x in -X..X, G (x + X * Complex.I)
      set Rt := ∫ y in (0 : ℝ)..X, G (X + y * Complex.I)
      set L := ∫ y in (0 : ℝ)..X, G ((-X : ℝ) + y * Complex.I)
      have heq : ∫ x in -X..X, G x = T - Complex.I • Rt + Complex.I • L := by
        linear_combination hrect
      have hT : ‖T‖ ≤ C / X ^ 2 * |X - -X| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun x _ =>
          hGX _ (by simp; linarith) ?_
        have h := Complex.abs_im_le_norm ((x : ℂ) + X * Complex.I)
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero] at h
        exact le_trans (le_abs_self X) h
      have hR : ‖Rt‖ ≤ C / X ^ 2 * |X - 0| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
        rw [Set.uIoc_of_le hXp.le] at hy
        refine hGX _ (by simp; exact hy.1.le) ?_
        have h := Complex.abs_re_le_norm ((X : ℂ) + y * Complex.I)
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero] at h
        exact le_trans (le_abs_self X) h
      have hL : ‖L‖ ≤ C / X ^ 2 * |X - 0| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
        rw [Set.uIoc_of_le hXp.le] at hy
        refine hGX _ (by simp; exact hy.1.le) ?_
        have h := Complex.abs_re_le_norm (((-X : ℝ) : ℂ) + y * Complex.I)
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, abs_neg] at h
        exact le_trans (le_abs_self X) h
      rw [heq]
      have hn : ‖T - Complex.I • Rt + Complex.I • L‖ ≤ ‖T‖ + ‖Rt‖ + ‖L‖ := by
        refine (norm_add_le _ _).trans ?_
        refine add_le_add ((norm_sub_le _ _).trans ?_) ?_
        · simp
        · simp
      refine hn.trans ?_
      rw [show |X - -X| = 2 * X by rw [sub_neg_eq_add, abs_of_pos (by linarith)]; ring,
        sub_zero, abs_of_pos hXp] at *
      have : C / X ^ 2 * (2 * X) + C / X ^ 2 * X + C / X ^ 2 * X = 4 * C / X := by
        field_simp; ring
      linarith
    · rw [Complex.mem_reProdIm] at hw
      refine (hd w ?_).differentiableWithinAt
      have h := hw.2
      rw [h2, h4, Set.uIcc_of_le hXp.le] at h
      exact h.1
  have h0 : Tendsto (fun X : ℝ => ∫ x in -X..X, G x) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun X => 4 * C / X) ?_ ?_
    · filter_upwards [eventually_ge_atTop (max X₀ 1)] with X hX using hbound X hX
    · exact tendsto_const_nhds.div_atTop tendsto_id
  exact tendsto_nhds_unique hlim h0

/-! ## The Stieltjes representation at height `ε` -/

private lemma vr_norm_ofReal_sub_sq (x : ℝ) (b : ℂ) :
    ‖(x : ℂ) - b‖ ^ 2 = (x - b.re) ^ 2 + b.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, zero_sub]
  ring

private lemma vr_ofReal_sub_ne (x : ℝ) {b : ℂ} (hb : b.im ≠ 0) : (x : ℂ) - b ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hb this

/-- `‖w‖ ≤ ‖w + iε‖` and `ε ≤ ‖w + iε‖` for `Im w ≥ 0`, `ε ≥ 0`. -/
private lemma vr_norm_le_shift {w : ℂ} (hw : 0 ≤ w.im) {ε : ℝ} (hε : 0 ≤ ε) :
    ‖w‖ ≤ ‖w + ε * Complex.I‖ ∧ ε ≤ ‖w + ε * Complex.I‖ := by
  have him : (w + ε * Complex.I).im = w.im + ε := by simp
  constructor
  · have h : ‖w‖ ^ 2 ≤ ‖w + ε * Complex.I‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply, him]
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero]
      nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h
  · have h := Complex.abs_im_le_norm (w + ε * Complex.I)
    rw [him] at h
    linarith [le_abs_self (w.im + ε)]

private lemma vr_differentiableAt_shift (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {ε : ℝ}
    {w : ℂ} (hw : -ε < w.im) :
    DifferentiableAt ℂ (fun w => mFun N σ (w + ε * Complex.I)) w := by
  have h : 0 < (w + ε * Complex.I).im := by simp; linarith
  exact (hasDerivAt_mFun N σ hσ h).differentiableAt.comp w
    (differentiableAt_id.add_const _)

private lemma vr_norm_shift_le (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {ε : ℝ}
    (hε : 0 < ε) {w : ℂ} (hw : 0 ≤ w.im) :
    ‖mFun N σ (w + ε * Complex.I)‖ ≤ (1 + √(massRatio N σ)) / ‖w + ε * Complex.I‖ :=
  norm_mFun_le N σ hσ (by simp; linarith)

private lemma vr_continuous_shift (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {ε : ℝ}
    (hε : 0 < ε) : Continuous (fun x : ℝ => mFun N σ (x + ε * Complex.I)) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  exact (vr_differentiableAt_shift N σ hσ (w := (x : ℂ)) (by simp; linarith)).continuousAt.comp
    Complex.continuous_ofReal.continuousAt

/-- `x ↦ m(x + iε) (x - b)⁻¹` is integrable on `ℝ` for `Im b ≠ 0`. -/
private lemma vr_integrable_shift_mul_inv (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {ε : ℝ}
    (hε : 0 < ε) {b : ℂ} (hb : b.im ≠ 0) :
    Integrable (fun x : ℝ => mFun N σ (x + ε * Complex.I) * ((x : ℂ) - b)⁻¹) := by
  set K := 1 + √(massRatio N σ)
  have hg : Integrable (fun x : ℝ =>
      (K ^ 2 * ((x - 0) ^ 2 + ε ^ 2)⁻¹ + ((x - b.re) ^ 2 + b.im ^ 2)⁻¹) / 2) :=
    (((vr_integrable_poisson 0 hε.ne').const_mul (K ^ 2)).add
      (vr_integrable_poisson b.re hb)).div_const 2
  refine hg.mono' ?_ (ae_of_all _ fun x => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    refine (vr_continuous_shift N σ hσ hε).mul ?_
    exact (Complex.continuous_ofReal.sub continuous_const).inv₀ fun x => vr_ofReal_sub_ne x hb
  · have hx0 : (0 : ℝ) ≤ ((x : ℂ)).im := by simp
    have h1 := vr_norm_shift_le N σ hσ hε hx0
    have hn : ‖(x : ℂ) + ε * Complex.I‖ ^ 2 = (x - 0) ^ 2 + ε ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
    have hpos : 0 < ‖(x : ℂ) + ε * Complex.I‖ :=
      lt_of_lt_of_le hε (vr_norm_le_shift hx0 hε.le).2
    have hsq : ‖mFun N σ (x + ε * Complex.I)‖ ^ 2 ≤ K ^ 2 * ((x - 0) ^ 2 + ε ^ 2)⁻¹ := by
      rw [← hn, ← div_eq_mul_inv, ← div_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    have hk : ‖((x : ℂ) - b)⁻¹‖ ^ 2 = ((x - b.re) ^ 2 + b.im ^ 2)⁻¹ := by
      rw [norm_inv, inv_pow, vr_norm_ofReal_sub_sq]
    rw [norm_mul]
    nlinarith [sq_nonneg (‖mFun N σ (x + ε * Complex.I)‖ - ‖((x : ℂ) - b)⁻¹‖)]

/-- `(x - a)⁻¹ - (x - ā)⁻¹ = 2i Im a / ((x - Re a)² + (Im a)²)`. -/
private lemma vr_kernel_eq (x : ℝ) {a : ℂ} (ha : a.im ≠ 0) :
    ((x : ℂ) - a)⁻¹ - ((x : ℂ) - (starRingEnd ℂ) a)⁻¹ =
      ((2 * a.im * ((x - a.re) ^ 2 + a.im ^ 2)⁻¹ : ℝ) : ℂ) * Complex.I := by
  have h1 : (x : ℂ) - a ≠ 0 := vr_ofReal_sub_ne x ha
  have h2 : (x : ℂ) - (starRingEnd ℂ) a ≠ 0 := vr_ofReal_sub_ne x (by simpa using ha)
  have hprod : ((x : ℂ) - a) * ((x : ℂ) - (starRingEnd ℂ) a) =
      (((x - a.re) ^ 2 + a.im ^ 2 : ℝ) : ℂ) := by
    apply Complex.ext <;>
      simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im] <;> ring
  have hp : ((x - a.re) ^ 2 + a.im ^ 2 : ℝ) ≠ 0 := by positivity
  rw [inv_sub_inv h1 h2, hprod, show (x : ℂ) - (starRingEnd ℂ) a - ((x : ℂ) - a) =
    a - (starRingEnd ℂ) a by ring, Complex.sub_conj]
  push_cast
  field_simp

/-- The Stieltjes representation at height `ε`: for `ε > 0` and `a ∈ ℂ₊`,
`m(a + iε) = ∫ π⁻¹ Im m(x + iε) (x - a)⁻¹ dx`. -/
private lemma vr_stieltjes_shift (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {ε : ℝ}
    (hε : 0 < ε) {a : ℂ} (ha : 0 < a.im) :
    mFun N σ (a + ε * Complex.I) =
      ∫ x : ℝ, (((mFun N σ (x + ε * Complex.I)).im / Real.pi : ℝ) : ℂ) * ((x : ℂ) - a)⁻¹ := by
  set h : ℂ → ℂ := fun w => mFun N σ (w + ε * Complex.I) with hdef
  set K := 1 + √(massRatio N σ) with hK
  have hK0 : 0 ≤ K := by positivity
  set ac := (starRingEnd ℂ) a with hac
  have haci : ac.im = -a.im := by simp [hac]
  have hacre : ac.re = a.re := by simp [hac]
  have hdiff : ∀ w : ℂ, -ε < w.im → DifferentiableAt ℂ h w :=
    fun w hw => vr_differentiableAt_shift N σ hσ hw
  have hnorm : ∀ w : ℂ, 0 ≤ w.im → 0 < ‖w‖ → ‖h w‖ ≤ K / ‖w‖ := by
    intro w hw hwp
    refine (vr_norm_shift_le N σ hσ hε hw).trans ?_
    exact div_le_div_of_nonneg_left hK0 hwp (vr_norm_le_shift hw hε.le).1
  have hne : ∀ w : ℂ, 0 ≤ w.im → w - ac ≠ 0 := by
    intro w hw h0
    have := congrArg Complex.im h0
    simp only [Complex.sub_im, haci, Complex.zero_im] at this
    linarith
  -- large `|w|`: `|w - a|, |w - ā| ≥ |w|/2`
  have hfar : ∀ w : ℂ, 2 * ‖a‖ + 1 ≤ ‖w‖ →
      ‖w‖ / 2 ≤ ‖w - a‖ ∧ ‖w‖ / 2 ≤ ‖w - ac‖ := by
    intro w hw
    have hac' : ‖ac‖ = ‖a‖ := by rw [hac, Complex.norm_conj]
    constructor
    · have := norm_sub_norm_le w a; linarith [norm_nonneg a]
    · have := norm_sub_norm_le w ac; linarith [norm_nonneg a]
  have hI1 : Integrable (fun x : ℝ => h x * ((x : ℂ) - a)⁻¹) :=
    vr_integrable_shift_mul_inv N σ hσ hε (b := a) ha.ne'
  have hI2 : Integrable (fun x : ℝ => h x * ((x : ℂ) - ac)⁻¹) :=
    vr_integrable_shift_mul_inv N σ hσ hε (b := ac) (by rw [haci]; linarith)
  have hk : Integrable (fun x : ℝ => ((x : ℂ) - a)⁻¹ - ((x : ℂ) - ac)⁻¹) := by
    have h0 : Integrable (fun x : ℝ =>
        ((2 * a.im * ((x - a.re) ^ 2 + a.im ^ 2)⁻¹ : ℝ) : ℂ) * Complex.I) :=
      (((vr_integrable_poisson a.re ha.ne').const_mul (2 * a.im)).ofReal).mul_const _
    exact h0.congr (ae_of_all _ fun x => (vr_kernel_eq x ha.ne').symm)
  have hkint : ∫ x : ℝ, (((x : ℂ) - a)⁻¹ - ((x : ℂ) - ac)⁻¹) =
      2 * Real.pi * Complex.I := by
    simp_rw [hac, vr_kernel_eq _ ha.ne']
    rw [integral_mul_const, integral_complex_ofReal, integral_const_mul,
      vr_integral_poisson a.re ha]
    have : (a.im : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    push_cast
    field_simp
  -- `G₂(w) = h(w) (w - ā)⁻¹`
  have hG2 : ∫ x : ℝ, h x * ((x : ℂ) - ac)⁻¹ = 0 := by
    refine vr_integral_eq_zero (G := fun w => h w * (w - ac)⁻¹) (C := 2 * K)
      (X₀ := 2 * ‖a‖ + 1) ?_ hI2 (by positivity) ?_
    · intro w hw
      exact (hdiff w (by linarith)).mul ((differentiableAt_id.sub_const _).inv (hne w hw))
    · intro w hw hwX
      have hwp : 0 < ‖w‖ := by linarith [norm_nonneg a]
      have h2 := (hfar w hwX).2
      rw [norm_mul, norm_inv]
      calc ‖h w‖ * ‖w - ac‖⁻¹ ≤ K / ‖w‖ * (‖w‖ / 2)⁻¹ :=
            mul_le_mul (hnorm w hw hwp) (inv_anti₀ (by positivity) h2) (by positivity)
              (by positivity)
        _ = 2 * K / ‖w‖ ^ 2 := by field_simp
  -- `G₁(w) = dslope h a w · (a - ā)(w - ā)⁻¹`
  have hU : {w : ℂ | -ε < w.im} ∈ 𝓝 a :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds (by simp; linarith)
  have hds : DifferentiableOn ℂ (dslope h a) {w : ℂ | -ε < w.im} :=
    (Complex.differentiableOn_dslope hU).mpr fun w hw => (hdiff w hw).differentiableWithinAt
  have hG1pt : ∀ x : ℝ, dslope h a x * ((a - ac) * ((x : ℂ) - ac)⁻¹) =
      h x * ((x : ℂ) - a)⁻¹ - h x * ((x : ℂ) - ac)⁻¹ -
        h a * (((x : ℂ) - a)⁻¹ - ((x : ℂ) - ac)⁻¹) := by
    intro x
    have h1 : (x : ℂ) - a ≠ 0 := vr_ofReal_sub_ne x ha.ne'
    have h2 : (x : ℂ) - ac ≠ 0 := vr_ofReal_sub_ne x (by rw [haci]; linarith)
    rw [dslope_of_ne _ (sub_ne_zero.mp h1), slope_def_module, smul_eq_mul]
    field_simp
    ring
  have hG1 : ∫ x : ℝ, dslope h a x * ((a - ac) * ((x : ℂ) - ac)⁻¹) = 0 := by
    have hI : Integrable (fun x : ℝ => dslope h a x * ((a - ac) * ((x : ℂ) - ac)⁻¹)) := by
      refine ((hI1.sub hI2).sub (hk.const_mul (h a))).congr (ae_of_all _ fun x => ?_)
      exact (hG1pt x).symm
    refine vr_integral_eq_zero (G := fun w => dslope h a w * ((a - ac) * (w - ac)⁻¹))
      (C := 4 * (K + ‖h a‖) * ‖a - ac‖) (X₀ := 2 * ‖a‖ + 1) ?_ hI (by positivity) ?_
    · intro w hw
      have hwU : {w : ℂ | -ε < w.im} ∈ 𝓝 w :=
        (isOpen_lt continuous_const Complex.continuous_im).mem_nhds (by simp; linarith)
      exact (hds.differentiableAt hwU).mul
        ((differentiableAt_const _).mul ((differentiableAt_id.sub_const _).inv (hne w hw)))
    · intro w hw hwX
      have hwp : 0 < ‖w‖ := by linarith [norm_nonneg a]
      have hw1 : 1 ≤ ‖w‖ := by linarith [norm_nonneg a]
      obtain ⟨h1, h2⟩ := hfar w hwX
      have hwa : w ≠ a := by
        intro e
        have : ‖w - a‖ = 0 := by rw [e, sub_self, norm_zero]
        linarith
      rw [dslope_of_ne _ hwa, slope_def_module, smul_eq_mul, norm_mul, norm_mul, norm_mul,
        norm_inv, norm_inv]
      have hhw : ‖h w - h a‖ ≤ K + ‖h a‖ := by
        have := (hnorm w hw hwp).trans (div_le_self hK0 hw1)
        linarith [norm_sub_le (h w) (h a)]
      calc ‖w - a‖⁻¹ * ‖h w - h a‖ * (‖a - ac‖ * ‖w - ac‖⁻¹)
          ≤ (‖w‖ / 2)⁻¹ * (K + ‖h a‖) * (‖a - ac‖ * (‖w‖ / 2)⁻¹) := by
            gcongr
        _ = 4 * (K + ‖h a‖) * ‖a - ac‖ / ‖w‖ ^ 2 := by field_simp; ring
  -- combine
  have hmain : ∫ x : ℝ, h x * ((x : ℂ) - a)⁻¹ = 2 * Real.pi * Complex.I * h a := by
    simp_rw [hG1pt] at hG1
    rw [integral_sub (f := fun x : ℝ => h x * ((x : ℂ) - a)⁻¹ - h x * ((x : ℂ) - ac)⁻¹)
      (g := fun x : ℝ => h a * (((x : ℂ) - a)⁻¹ - ((x : ℂ) - ac)⁻¹)) (hI1.sub hI2)
      (hk.const_mul _), integral_sub hI1 hI2, integral_const_mul, hG2, hkint] at hG1
    linear_combination hG1
  have hconj : ∫ x : ℝ, (starRingEnd ℂ) (h x) * ((x : ℂ) - a)⁻¹ = 0 := by
    have : ∀ x : ℝ, (starRingEnd ℂ) (h x) * ((x : ℂ) - a)⁻¹ =
        (starRingEnd ℂ) (h x * ((x : ℂ) - ac)⁻¹) := by
      intro x
      simp [hac, map_inv₀]
    simp_rw [this]
    rw [integral_conj, hG2, map_zero]
  have hIc : Integrable (fun x : ℝ => (starRingEnd ℂ) (h x) * ((x : ℂ) - a)⁻¹) := by
    refine hI2.congr' ?_ (ae_of_all _ fun x => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      refine (Complex.continuous_conj.comp (vr_continuous_shift N σ hσ hε)).mul ?_
      exact (Complex.continuous_ofReal.sub continuous_const).inv₀
        fun x => vr_ofReal_sub_ne x ha.ne'
    · simp only [norm_mul, Complex.norm_conj, norm_inv]
      congr 1
      rw [inv_inj, ← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), vr_norm_ofReal_sub_sq,
        vr_norm_ofReal_sub_sq, haci, hacre]
      ring
  have hpt : ∀ x : ℝ, (((h x).im / Real.pi : ℝ) : ℂ) * ((x : ℂ) - a)⁻¹ =
      (2 * Real.pi * Complex.I)⁻¹ * (h x * ((x : ℂ) - a)⁻¹ -
        (starRingEnd ℂ) (h x) * ((x : ℂ) - a)⁻¹) := by
    intro x
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [← sub_mul, Complex.sub_conj]
    push_cast
    field_simp
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hfin : h a = ∫ x : ℝ, (2 * Real.pi * Complex.I)⁻¹ * (h x * ((x : ℂ) - a)⁻¹ -
      (starRingEnd ℂ) (h x) * ((x : ℂ) - a)⁻¹) := by
    rw [integral_const_mul, integral_sub hI1 hIc, hmain, hconj, sub_zero]
    field_simp
  exact hfin.trans (integral_congr_ae (ae_of_all _ hpt)).symm

/-! ## Mass of `π⁻¹ Im m(x + iε) dx` -/

/-- The threshold `X₀` with `s₁ = Σ_i σ_i`. -/
private def vrX (N : ℕ) (σ : Fin M → ℝ) : ℝ :=
  (1 + √(massRatio N σ)) * (∑ i, σ i) * max 2 (√(8 * massRatio N σ))

private lemma vrX_nonneg (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) : 0 ≤ vrX N σ := by
  have h1 : 0 ≤ ∑ i, σ i := Finset.sum_nonneg fun i _ => hσ i
  have h2 : 0 ≤ max 2 (√(8 * massRatio N σ)) := le_trans (by norm_num) (le_max_left _ _)
  unfold vrX
  positivity

/-- `Im m(w) ≤ (2 Im w (1 + √R)² + (1 + √R) X₀) / |w|²` on `ℂ₊`. -/
private lemma vr_im_mFun_le_global (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {w : ℂ}
    (hw : 0 < w.im) :
    (mFun N σ w).im ≤ (2 * w.im * (1 + √(massRatio N σ)) ^ 2 +
      (1 + √(massRatio N σ)) * vrX N σ) / ‖w‖ ^ 2 := by
  set K := 1 + √(massRatio N σ) with hK
  have hK0 : 0 ≤ K := by positivity
  have hX0 := vrX_nonneg N σ hσ
  have hwn : 0 < ‖w‖ := lt_of_lt_of_le hw (Complex.im_le_norm w)
  rcases le_or_gt (vrX N σ) ‖w‖ with hX | hX
  · have h := vr_im_mFun_le N σ hσ (Finset.sum_nonneg fun i _ => hσ i)
      (fun i => Finset.single_le_sum (fun j _ => hσ j) (Finset.mem_univ i)) hw hX
    refine h.trans (div_le_div_of_nonneg_right ?_ (by positivity))
    have : 0 ≤ K * vrX N σ := mul_nonneg hK0 hX0
    linarith
  · have h1 : (mFun N σ w).im ≤ K / ‖w‖ :=
      (Complex.im_le_norm _).trans (norm_mFun_le N σ hσ hw)
    refine h1.trans ?_
    rw [div_le_div_iff₀ hwn (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hX.le (mul_nonneg hK0 hwn.le),
      mul_nonneg (mul_nonneg hw.le (sq_nonneg K)) hwn.le]

private lemma vr_norm_shift_sq (x ε : ℝ) : ‖(x : ℂ) + ε * Complex.I‖ ^ 2 = (x - 0) ^ 2 + ε ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring

/-- `0 < π⁻¹ Im m(x + iε) ≤ (2ε(1 + √R)² + (1 + √R) X₀) π⁻¹ (x² + ε²)⁻¹`. -/
private lemma vr_u_bound (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {ε : ℝ} (hε : 0 < ε)
    (x : ℝ) :
    0 < (mFun N σ (x + ε * Complex.I)).im / Real.pi ∧
    (mFun N σ (x + ε * Complex.I)).im / Real.pi ≤
      (2 * ε * (1 + √(massRatio N σ)) ^ 2 + (1 + √(massRatio N σ)) * vrX N σ) / Real.pi *
        ((x - 0) ^ 2 + ε ^ 2)⁻¹ := by
  have hw : 0 < ((x : ℂ) + ε * Complex.I).im := by simp; exact hε
  have him : ((x : ℂ) + ε * Complex.I).im = ε := by simp
  constructor
  · exact div_pos (mFun_spec N σ hσ hw).1 Real.pi_pos
  · have h := vr_im_mFun_le_global N σ hσ hw
    rw [him, vr_norm_shift_sq] at h
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right Real.pi_pos, ← div_eq_mul_inv]
    exact h

private lemma vr_integrable_u (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {ε : ℝ}
    (hε : 0 < ε) :
    Integrable (fun x : ℝ => (mFun N σ (x + ε * Complex.I)).im / Real.pi) := by
  refine ((vr_integrable_poisson 0 hε.ne').const_mul ((2 * ε * (1 + √(massRatio N σ)) ^ 2 +
    (1 + √(massRatio N σ)) * vrX N σ) / Real.pi)).mono' ?_ (ae_of_all _ fun x => ?_)
  · exact ((Complex.continuous_im.comp (vr_continuous_shift N σ hσ hε)).div_const _)
      |>.aestronglyMeasurable
  · obtain ⟨h0, h1⟩ := vr_u_bound N σ hσ hε x
    rw [Real.norm_of_nonneg h0.le]
    exact h1

private lemma vr_norm_mul_inv_le (r x : ℝ) {z : ℂ} (hz : 0 < z.im) :
    ‖(r : ℂ) * ((x : ℂ) - z)⁻¹‖ ≤ ‖r‖ / z.im := by
  have hle : z.im ≤ ‖(x : ℂ) - z‖ := by
    have h := Complex.abs_im_le_norm ((x : ℂ) - z)
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] at h
    exact (le_abs_self _).trans h
  rw [norm_mul, Complex.norm_real, norm_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (inv_anti₀ hz hle) (norm_nonneg _)

/-- `x ↦ f(x) (x - z)⁻¹` is integrable for integrable `f` and `z ∈ ℂ₊`. -/
private lemma vr_integrable_mul_inv {f : ℝ → ℝ} {μ : Measure ℝ} (hf : Integrable f μ) {z : ℂ}
    (hz : 0 < z.im) : Integrable (fun x : ℝ => ((f x : ℝ) : ℂ) * ((x : ℂ) - z)⁻¹) μ := by
  refine (hf.norm.div_const z.im).mono' ?_ (ae_of_all _ fun x => ?_)
  · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hf.1).mul
      ((Complex.continuous_ofReal.sub continuous_const).inv₀
        (fun x => vr_ofReal_sub_ne x hz.ne')).aestronglyMeasurable
  · exact vr_norm_mul_inv_le (f x) x hz

/-- `-iy (x - iy)⁻¹` has real part `y² / (x² + y²)`. -/
private lemma vr_re_kernel (u x y : ℝ) (hy : 0 < y) :
    (-(y * Complex.I) * ((u : ℂ) * ((x : ℂ) - y * Complex.I)⁻¹)).re =
      u * (y ^ 2 / (x ^ 2 + y ^ 2)) := by
  have hd : x ^ 2 + y ^ 2 ≠ 0 := by positivity
  simp [Complex.mul_re, Complex.mul_im, Complex.inv_re, Complex.inv_im, Complex.normSq]
  field_simp

/-- `∫ π⁻¹ Im m(x + iε) dx = 1` for `ε > 0`. -/
private lemma vr_integral_u (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {ε : ℝ}
    (hε : 0 < ε) :
    ∫ x : ℝ, (mFun N σ (x + ε * Complex.I)).im / Real.pi = 1 := by
  set u : ℝ → ℝ := fun x => (mFun N σ (x + ε * Complex.I)).im / Real.pi with hu
  set K := 1 + √(massRatio N σ) with hK
  have hui : Integrable u := vr_integrable_u N σ hσ hε
  have hu0 : ∀ x, 0 ≤ u x := fun x => (vr_u_bound N σ hσ hε x).1.le
  -- `Re(-iy m(i(y + ε))) = ∫ u(x) y²/(x² + y²) dx`
  have hrep : ∀ y : ℝ, 0 < y → ∫ x : ℝ, u x * (y ^ 2 / (x ^ 2 + y ^ 2)) =
      (-(y * Complex.I) * mFun N σ (y * Complex.I + ε * Complex.I)).re := by
    intro y hy
    have hs := vr_stieltjes_shift N σ hσ hε (a := y * Complex.I) (by simpa using hy)
    have hI : Integrable (fun x : ℝ =>
        -(y * Complex.I) * (((u x : ℝ) : ℂ) * ((x : ℂ) - y * Complex.I)⁻¹)) :=
      (vr_integrable_mul_inv hui (z := y * Complex.I) (by simpa using hy)).const_mul _
    calc ∫ x : ℝ, u x * (y ^ 2 / (x ^ 2 + y ^ 2))
        = ∫ x : ℝ, RCLike.re (-(y * Complex.I) *
            (((u x : ℝ) : ℂ) * ((x : ℂ) - y * Complex.I)⁻¹)) :=
          integral_congr_ae (ae_of_all _ fun x => by
            simp only
            rw [RCLike.re_to_complex, vr_re_kernel (u x) x y hy])
      _ = RCLike.re (∫ x : ℝ, -(y * Complex.I) *
            (((u x : ℝ) : ℂ) * ((x : ℂ) - y * Complex.I)⁻¹)) := integral_re hI
      _ = _ := by
        rw [RCLike.re_to_complex, hs, ← integral_const_mul]
  -- `y → ∞` on the left side
  have hL : Tendsto (fun y : ℝ => ∫ x : ℝ, u x * (y ^ 2 / (x ^ 2 + y ^ 2))) atTop
      (𝓝 (∫ x : ℝ, u x)) := by
    refine tendsto_integral_filter_of_dominated_convergence u ?_ ?_ hui ?_
    · filter_upwards [eventually_gt_atTop 0] with y hy
      exact hui.1.mul (Continuous.aestronglyMeasurable
        (continuous_const.div (by fun_prop) fun x => by positivity))
    · filter_upwards [eventually_gt_atTop 0] with y hy
      refine ae_of_all _ fun x => ?_
      rw [norm_mul, Real.norm_of_nonneg (hu0 x), Real.norm_of_nonneg (by positivity)]
      refine mul_le_of_le_one_right (hu0 x) ?_
      rw [div_le_one (by positivity)]
      nlinarith [sq_nonneg x]
    · refine ae_of_all _ fun x => ?_
      have h1 : Tendsto (fun y : ℝ => (1 + x ^ 2 * (y⁻¹) ^ 2)⁻¹) atTop (𝓝 1) := by
        have h := (((tendsto_inv_atTop_zero (𝕜 := ℝ)).pow 2).const_mul (x ^ 2)).const_add 1
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
          add_zero] at h
        simpa using h.inv₀ (by norm_num)
      have h2 : Tendsto (fun y : ℝ => y ^ 2 / (x ^ 2 + y ^ 2)) atTop (𝓝 1) := by
        refine h1.congr' ?_
        filter_upwards [eventually_gt_atTop 0] with y hy
        field_simp
        ring
      simpa using h2.const_mul (u x)
  -- `y → ∞` on the right side, by the asymptotics `m(z) = -1/z + O(|z|⁻²)`
  have hR : Tendsto (fun y : ℝ => (-(y * Complex.I) *
      mFun N σ (y * Complex.I + ε * Complex.I)).re) atTop (𝓝 1) := by
    set s₁ := ∑ i, σ i
    have hs₁ : ∀ i, σ i ≤ s₁ := fun i => Finset.single_le_sum (fun j _ => hσ j) (Finset.mem_univ i)
    set C' := 2 * K * (∑ i, σ i / N)
    have hC' : 0 ≤ C' := by
      have : 0 ≤ ∑ i, σ i / (N : ℝ) :=
        Finset.sum_nonneg fun i _ => div_nonneg (hσ i) (by positivity)
      positivity
    have hq : Tendsto (fun y : ℝ => y / (y + ε)) atTop (𝓝 1) := by
      have h := (((tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul ε).const_add 1).inv₀
        (by norm_num : (1 : ℝ) + ε * 0 ≠ 0)
      simp only [mul_zero, add_zero, inv_one] at h
      refine h.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with y hy
      field_simp
    have hd : Tendsto (fun y : ℝ => -(y * Complex.I) * mFun N σ (y * Complex.I + ε * Complex.I) -
        ((y / (y + ε) : ℝ) : ℂ)) atTop (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun y => C' / y) ?_
        (tendsto_const_nhds.div_atTop tendsto_id)
      filter_upwards [eventually_gt_atTop 0, eventually_ge_atTop (2 * K * s₁)] with y hy hyl
      set w := (y : ℂ) * Complex.I + ε * Complex.I with hw
      have hwI : w = ((y + ε : ℝ) : ℂ) * Complex.I := by rw [hw]; push_cast; ring
      have hwim : 0 < w.im := by rw [hwI]; simp; linarith
      have hwn : ‖w‖ = y + ε := by
        rw [hwI, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_of_nonneg (by linarith)]
      have hb := norm_mFun_add_inv_le N σ hσ hs₁ hwim (by rw [hwn]; linarith)
      have heq : -(y * Complex.I) * mFun N σ w - ((y / (y + ε) : ℝ) : ℂ) =
          -(y * Complex.I) * (mFun N σ w + w⁻¹) := by
        have hyε : ((y + ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : y + ε ≠ 0)
        rw [hwI]
        push_cast
        field_simp
        ring_nf
      rw [heq, norm_mul, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg hy.le]
      rw [hwn] at hb
      calc y * ‖mFun N σ w + w⁻¹‖ ≤ y * (C' / (y + ε) ^ 2) := mul_le_mul_of_nonneg_left hb hy.le
        _ ≤ C' / y := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hy]
          nlinarith [mul_nonneg hC' (sq_nonneg y), mul_nonneg hC' (mul_nonneg hy.le hε.le),
            mul_nonneg hC' (sq_nonneg ε)]
    have h := (hd.add (Complex.continuous_ofReal.continuousAt.tendsto.comp hq))
    rw [zero_add, Complex.ofReal_one] at h
    have h2 : Tendsto (fun y : ℝ => -(y * Complex.I) *
        mFun N σ (y * Complex.I + ε * Complex.I)) atTop (𝓝 1) :=
      h.congr fun y => by simp only [Function.comp, sub_add_cancel]
    have h3 := (Complex.continuous_re.tendsto 1).comp h2
    rwa [Complex.one_re] at h3
  have hL' : Tendsto (fun y : ℝ => ∫ x : ℝ, u x * (y ^ 2 / (x ^ 2 + y ^ 2))) atTop (𝓝 1) :=
    hR.congr' (by
      filter_upwards [eventually_gt_atTop 0] with y hy
      exact (hrep y hy).symm)
  exact tendsto_nhds_unique hL hL'

/-! ## The limit `ε → 0` away from `0` -/

/-- The set `|x| ≥ δ`. -/
private def vrS (δ : ℝ) : Set ℝ := {x | δ ≤ |x|}

private lemma vrS_measurable (δ : ℝ) : MeasurableSet (vrS δ) :=
  (isClosed_le continuous_const continuous_abs).measurableSet

/-- The constant `B_δ = (2(1 + √R)² + (1 + √R) X₀) π⁻¹ (1 + δ⁻²)`. -/
private def vrB (N : ℕ) (σ : Fin M → ℝ) (δ : ℝ) : ℝ :=
  (2 * (1 + √(massRatio N σ)) ^ 2 + (1 + √(massRatio N σ)) * vrX N σ) / Real.pi *
    (1 + (δ ^ 2)⁻¹)

private lemma vr_inv_sq_le {δ x : ℝ} (hδ : 0 < δ) (hx : δ ≤ |x|) :
    (x ^ 2)⁻¹ ≤ (1 + (δ ^ 2)⁻¹) * ((x - 0) ^ 2 + 1 ^ 2)⁻¹ := by
  have hx2 : δ ^ 2 ≤ x ^ 2 := by
    rw [← sq_abs x]; exact pow_le_pow_left₀ hδ.le hx 2
  have hx0 : 0 < x ^ 2 := lt_of_lt_of_le (by positivity) hx2
  rw [sub_zero, one_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have : (x ^ 2)⁻¹ ≤ (δ ^ 2)⁻¹ := inv_anti₀ (by positivity) hx2
  have h1 : (x ^ 2)⁻¹ * (x ^ 2 + 1) = 1 + (x ^ 2)⁻¹ := by
    rw [mul_add, inv_mul_cancel₀ hx0.ne', mul_one]
  linarith

/-- `π⁻¹ Im m(x + iε) ≤ B_δ ((x - 0)² + 1)⁻¹` for `0 < ε ≤ 1` and `|x| ≥ δ > 0`. -/
private lemma vr_u_le_S (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {ε δ x : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hδ : 0 < δ) (hx : x ∈ vrS δ) :
    (mFun N σ (x + ε * Complex.I)).im / Real.pi ≤ vrB N σ δ * ((x - 0) ^ 2 + 1 ^ 2)⁻¹ := by
  have hx' : δ ≤ |x| := hx
  set K := 1 + √(massRatio N σ)
  have hK0 : 0 ≤ K := by positivity
  have hX := vrX_nonneg N σ hσ
  have hx2 : 0 < x ^ 2 := by
    have : δ ^ 2 ≤ x ^ 2 := by rw [← sq_abs x]; exact pow_le_pow_left₀ hδ.le hx' 2
    exact lt_of_lt_of_le (by positivity) this
  refine (vr_u_bound N σ hσ hε x).2.trans ?_
  unfold vrB
  have h1 : (2 * ε * K ^ 2 + K * vrX N σ) / Real.pi ≤ (2 * K ^ 2 + K * vrX N σ) / Real.pi := by
    refine div_le_div_of_nonneg_right ?_ Real.pi_pos.le
    nlinarith [sq_nonneg K]
  have h2 : ((x - 0) ^ 2 + ε ^ 2)⁻¹ ≤ (x ^ 2)⁻¹ :=
    inv_anti₀ hx2 (by rw [sub_zero]; nlinarith [sq_nonneg ε])
  have h3 := vr_inv_sq_le hδ hx'
  calc (2 * ε * K ^ 2 + K * vrX N σ) / Real.pi * ((x - 0) ^ 2 + ε ^ 2)⁻¹
      ≤ (2 * K ^ 2 + K * vrX N σ) / Real.pi * (x ^ 2)⁻¹ :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ ≤ (2 * K ^ 2 + K * vrX N σ) / Real.pi * ((1 + (δ ^ 2)⁻¹) * ((x - 0) ^ 2 + 1 ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by ring

/-- `π⁻¹ Im m(x + iε) → ρ(x)` as `ε ↓ 0`, for `x ≠ 0`. -/
private lemma vr_tendsto_u (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {x : ℝ} (hx : x ≠ 0) :
    Tendsto (fun ε : ℝ => (mFun N σ (x + ε * Complex.I)).im / Real.pi) (𝓝[>] 0)
      (𝓝 (rhoDens N σ x)) :=
  (vr_tendsto_im N σ hσ hx).div_const _

private lemma vr_rhoDens_nonneg (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {x : ℝ}
    (hx : x ≠ 0) : 0 ≤ rhoDens N σ x :=
  div_nonneg (im_mExt_nonneg N σ hσ hx) Real.pi_pos.le

private lemma vr_rhoDens_le_S (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {δ x : ℝ}
    (hδ : 0 < δ) (hx : x ∈ vrS δ) : rhoDens N σ x ≤ vrB N σ δ * ((x - 0) ^ 2 + 1 ^ 2)⁻¹ := by
  have hx0 : x ≠ 0 := by
    intro h; have : δ ≤ |x| := hx; rw [h, abs_zero] at this; linarith
  refine le_of_tendsto (vr_tendsto_u N σ hσ hx0) ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
  exact vr_u_le_S N σ hσ hε.1 hε.2.le hδ hx

private lemma vr_continuousOn_rhoDens (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) :
    ContinuousOn (rhoDens N σ) {x | x ≠ 0} := by
  have h : ContinuousOn (fun x : ℝ => mExt N σ x) {x | x ≠ 0} :=
    (continuousOn_mExt N σ hσ).comp Complex.continuous_ofReal.continuousOn fun x hx =>
      Or.inr ⟨by simp, by simpa using hx⟩
  exact (Complex.continuous_im.comp_continuousOn h).div_const _

private lemma vrS_subset {δ : ℝ} (hδ : 0 < δ) : vrS δ ⊆ {x | x ≠ 0} := by
  intro x hx h
  have : δ ≤ |x| := hx
  rw [show x = 0 from h, abs_zero] at this
  linarith

private lemma vr_integrableOn_rhoDens_S (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {δ : ℝ}
    (hδ : 0 < δ) : IntegrableOn (rhoDens N σ) (vrS δ) := by
  refine (((vr_integrable_poisson 0 one_ne_zero).const_mul (vrB N σ δ)).integrableOn).mono' ?_ ?_
  · exact ((vr_continuousOn_rhoDens N σ hσ).mono (vrS_subset hδ)).aestronglyMeasurable
      (vrS_measurable δ)
  · refine (ae_restrict_iff' (vrS_measurable δ)).mpr (ae_of_all _ fun x hx => ?_)
    rw [Real.norm_of_nonneg (vr_rhoDens_nonneg N σ hσ (vrS_subset hδ hx))]
    exact vr_rhoDens_le_S N σ hσ hδ hx

/-- `|(x - z)⁻¹ + z⁻¹| ≤ 2δ/|z|²` for `|x| < δ ≤ |z|/2`. -/
private lemma vr_kernel_near {z : ℂ} (hz : 0 < z.im) {δ x : ℝ} (hδz : δ ≤ ‖z‖ / 2)
    (hx : |x| < δ) : ‖((x : ℂ) - z)⁻¹ + z⁻¹‖ ≤ 2 * δ / ‖z‖ ^ 2 := by
  have hzn : 0 < ‖z‖ := lt_of_lt_of_le hz (Complex.im_le_norm z)
  have hz0 : z ≠ 0 := norm_pos_iff.mp hzn
  have hxz : (x : ℂ) - z ≠ 0 := vr_ofReal_sub_ne x hz.ne'
  have heq : ((x : ℂ) - z)⁻¹ + z⁻¹ = x / (((x : ℂ) - z) * z) := by
    field_simp
    ring
  have hn : ‖z‖ / 2 ≤ ‖(x : ℂ) - z‖ := by
    have h := norm_sub_norm_le z (x : ℂ)
    rw [norm_sub_rev, Complex.norm_real, Real.norm_eq_abs] at h
    linarith
  rw [heq, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |x| / (‖(x : ℂ) - z‖ * ‖z‖) ≤ δ / (‖z‖ / 2 * ‖z‖) :=
        div_le_div₀ (by linarith [abs_nonneg x]) hx.le (by positivity)
          (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
    _ = 2 * δ / ‖z‖ ^ 2 := by field_simp

/-- The splitting at height `ε`: with `u_ε(x) = π⁻¹ Im m(x + iε)` and `S = {|x| ≥ δ}`,
`|m(z + iε) - ∫_S u_ε(x)(x - z)⁻¹ dx + z⁻¹(1 - ∫_S u_ε)| ≤ 2δ/|z|²` for `δ ≤ |z|/2`. -/
private lemma vr_step_eps (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {z : ℂ} (hz : 0 < z.im)
    {δ : ℝ} (hδ : 0 < δ) (hδz : δ ≤ ‖z‖ / 2) {ε : ℝ} (hε : 0 < ε) :
    ‖mFun N σ (z + ε * Complex.I) -
        (∫ x in vrS δ, (((mFun N σ (x + ε * Complex.I)).im / Real.pi : ℝ) : ℂ) * ((x : ℂ) - z)⁻¹) +
        z⁻¹ * ((1 - ∫ x in vrS δ, (mFun N σ (x + ε * Complex.I)).im / Real.pi : ℝ) : ℂ)‖ ≤
      2 * δ / ‖z‖ ^ 2 := by
  set u : ℝ → ℝ := fun x => (mFun N σ (x + ε * Complex.I)).im / Real.pi with hu
  have hui : Integrable u := vr_integrable_u N σ hσ hε
  have hu0 : ∀ x, 0 ≤ u x := fun x => (vr_u_bound N σ hσ hε x).1.le
  have htot : ∫ x, u x = 1 := vr_integral_u N σ hσ hε
  have hS := vrS_measurable δ
  have hF : Integrable (fun x : ℝ => ((u x : ℝ) : ℂ) * ((x : ℂ) - z)⁻¹) :=
    vr_integrable_mul_inv hui hz
  have hs : mFun N σ (z + ε * Complex.I) = ∫ x : ℝ, ((u x : ℝ) : ℂ) * ((x : ℂ) - z)⁻¹ :=
    vr_stieltjes_shift N σ hσ hε hz
  have hsplit : (∫ x in vrS δ, ((u x : ℝ) : ℂ) * ((x : ℂ) - z)⁻¹) +
      (∫ x in (vrS δ)ᶜ, ((u x : ℝ) : ℂ) * ((x : ℂ) - z)⁻¹) =
      ∫ x : ℝ, ((u x : ℝ) : ℂ) * ((x : ℂ) - z)⁻¹ := integral_add_compl hS hF
  have hsplit_u : (∫ x in vrS δ, u x) + (∫ x in (vrS δ)ᶜ, u x) = 1 := by
    rw [← htot]; exact integral_add_compl hS hui
  have hG : Integrable (fun x : ℝ => ((u x : ℝ) : ℂ) * z⁻¹) := hui.ofReal.mul_const _
  have hcomb : (∫ x in (vrS δ)ᶜ, ((u x : ℝ) : ℂ) * ((x : ℂ) - z)⁻¹) +
      z⁻¹ * ((∫ x in (vrS δ)ᶜ, u x : ℝ) : ℂ) =
      ∫ x in (vrS δ)ᶜ, ((u x : ℝ) : ℂ) * (((x : ℂ) - z)⁻¹ + z⁻¹) := by
    have h1 : ∫ x in (vrS δ)ᶜ, (((u x : ℝ) : ℂ) * ((x : ℂ) - z)⁻¹ + ((u x : ℝ) : ℂ) * z⁻¹) =
        (∫ x in (vrS δ)ᶜ, ((u x : ℝ) : ℂ) * ((x : ℂ) - z)⁻¹) +
          ∫ x in (vrS δ)ᶜ, ((u x : ℝ) : ℂ) * z⁻¹ :=
      integral_add hF.integrableOn hG.integrableOn
    have h2 : ∫ x in (vrS δ)ᶜ, ((u x : ℝ) : ℂ) * z⁻¹ = z⁻¹ * ((∫ x in (vrS δ)ᶜ, u x : ℝ) : ℂ) := by
      rw [integral_mul_const, integral_complex_ofReal, mul_comm]
    rw [← h2, ← h1]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only
    ring
  have hexpr : mFun N σ (z + ε * Complex.I) -
      (∫ x in vrS δ, ((u x : ℝ) : ℂ) * ((x : ℂ) - z)⁻¹) +
      z⁻¹ * ((1 - ∫ x in vrS δ, u x : ℝ) : ℂ) =
      ∫ x in (vrS δ)ᶜ, ((u x : ℝ) : ℂ) * (((x : ℂ) - z)⁻¹ + z⁻¹) := by
    rw [← hcomb, hs, ← hsplit, show (1 - ∫ x in vrS δ, u x : ℝ) = ∫ x in (vrS δ)ᶜ, u x by
      linarith]
    ring
  show ‖mFun N σ (z + ε * Complex.I) -
      (∫ x in vrS δ, ((u x : ℝ) : ℂ) * ((x : ℂ) - z)⁻¹) +
      z⁻¹ * ((1 - ∫ x in vrS δ, u x : ℝ) : ℂ)‖ ≤ 2 * δ / ‖z‖ ^ 2
  rw [hexpr]
  have hSc := hS.compl
  have hb : ∀ᵐ x ∂(volume.restrict (vrS δ)ᶜ),
      ‖((u x : ℝ) : ℂ) * (((x : ℂ) - z)⁻¹ + z⁻¹)‖ ≤ u x * (2 * δ / ‖z‖ ^ 2) := by
    refine (ae_restrict_iff' hSc).mpr (ae_of_all _ fun x hx => ?_)
    have hx' : |x| < δ := by
      simp only [vrS, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hx
      exact hx
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hu0 x)]
    exact mul_le_mul_of_nonneg_left (vr_kernel_near hz hδz hx') (hu0 x)
  refine (norm_integral_le_of_norm_le (hui.integrableOn.mul_const _) hb).trans ?_
  rw [integral_mul_const]
  have h1 : ∫ x in (vrS δ)ᶜ, u x ≤ 1 := by
    have : 0 ≤ ∫ x in vrS δ, u x := setIntegral_nonneg hS fun x _ => hu0 x
    linarith
  have hc : 0 ≤ 2 * δ / ‖z‖ ^ 2 := by positivity
  nlinarith

/-- `∫_S π⁻¹ Im m(x + iε) dx → ∫_S ρ` as `ε ↓ 0`, `S = {|x| ≥ δ}`. -/
private lemma vr_tendsto_int_S (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {δ : ℝ}
    (hδ : 0 < δ) :
    Tendsto (fun ε : ℝ => ∫ x in vrS δ, (mFun N σ (x + ε * Complex.I)).im / Real.pi) (𝓝[>] 0)
      (𝓝 (∫ x in vrS δ, rhoDens N σ x)) := by
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x => vrB N σ δ * ((x - 0) ^ 2 + 1 ^ 2)⁻¹) ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ((Complex.continuous_im.comp (vr_continuous_shift N σ hσ hε)).div_const _)
      |>.aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    refine (ae_restrict_iff' (vrS_measurable δ)).mpr (ae_of_all _ fun x hx => ?_)
    rw [Real.norm_of_nonneg (vr_u_bound N σ hσ hε.1 x).1.le]
    exact vr_u_le_S N σ hσ hε.1 hε.2.le hδ hx
  · exact ((vr_integrable_poisson 0 one_ne_zero).const_mul _).integrableOn
  · exact (ae_restrict_iff' (vrS_measurable δ)).mpr
      (ae_of_all _ fun x hx => vr_tendsto_u N σ hσ (vrS_subset hδ hx))

/-- `∫_S π⁻¹ Im m(x + iε)(x - z)⁻¹ dx → ∫_S ρ(x)(x - z)⁻¹ dx` as `ε ↓ 0`. -/
private lemma vr_tendsto_int_S_kernel (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {δ : ℝ}
    (hδ : 0 < δ) {z : ℂ} (hz : 0 < z.im) :
    Tendsto (fun ε : ℝ => ∫ x in vrS δ,
        (((mFun N σ (x + ε * Complex.I)).im / Real.pi : ℝ) : ℂ) * ((x : ℂ) - z)⁻¹) (𝓝[>] 0)
      (𝓝 (∫ x in vrS δ, ((rhoDens N σ x : ℝ) : ℂ) * ((x : ℂ) - z)⁻¹)) := by
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x => vrB N σ δ * ((x - 0) ^ 2 + 1 ^ 2)⁻¹ / z.im) ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    refine Continuous.aestronglyMeasurable ?_
    exact (Complex.continuous_ofReal.comp ((Complex.continuous_im.comp
      (vr_continuous_shift N σ hσ hε)).div_const _)).mul
      ((Complex.continuous_ofReal.sub continuous_const).inv₀ fun x => vr_ofReal_sub_ne x hz.ne')
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    refine (ae_restrict_iff' (vrS_measurable δ)).mpr (ae_of_all _ fun x hx => ?_)
    refine (vr_norm_mul_inv_le _ x hz).trans (div_le_div_of_nonneg_right ?_ hz.le)
    rw [Real.norm_of_nonneg (vr_u_bound N σ hσ hε.1 x).1.le]
    exact vr_u_le_S N σ hσ hε.1 hε.2.le hδ hx
  · exact (((vr_integrable_poisson 0 one_ne_zero).const_mul _).div_const _).integrableOn
  · refine (ae_restrict_iff' (vrS_measurable δ)).mpr (ae_of_all _ fun x hx => ?_)
    exact ((Complex.continuous_ofReal.tendsto _).comp
      (vr_tendsto_u N σ hσ (vrS_subset hδ hx))).mul_const _

private lemma vr_integral_rhoDens_S_le (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {δ : ℝ}
    (hδ : 0 < δ) : ∫ x in vrS δ, rhoDens N σ x ≤ 1 := by
  refine le_of_tendsto (vr_tendsto_int_S N σ hσ hδ) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [← vr_integral_u N σ hσ hε]
  exact setIntegral_le_integral (vr_integrable_u N σ hσ hε)
    (ae_of_all _ fun x => (vr_u_bound N σ hσ hε x).1.le)

/-- `|m(z) - ∫_S ρ(x)(x - z)⁻¹ dx + z⁻¹(1 - ∫_S ρ)| ≤ 2δ/|z|²` for `0 < δ ≤ |z|/2`. -/
private lemma vr_limit_eps (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {z : ℂ} (hz : 0 < z.im)
    {δ : ℝ} (hδ : 0 < δ) (hδz : δ ≤ ‖z‖ / 2) :
    ‖mFun N σ z - (∫ x in vrS δ, ((rhoDens N σ x : ℝ) : ℂ) * ((x : ℂ) - z)⁻¹) +
        z⁻¹ * ((1 - ∫ x in vrS δ, rhoDens N σ x : ℝ) : ℂ)‖ ≤ 2 * δ / ‖z‖ ^ 2 := by
  have hm : Tendsto (fun ε : ℝ => mFun N σ (z + ε * Complex.I)) (𝓝[>] 0)
      (𝓝 (mFun N σ z)) := by
    have hc : ContinuousAt (mFun N σ) z := (hasDerivAt_mFun N σ hσ hz).continuousAt
    have hp : Tendsto (fun ε : ℝ => z + ε * Complex.I) (𝓝[>] 0) (𝓝 z) := by
      have : Continuous (fun ε : ℝ => z + ε * Complex.I) := by fun_prop
      simpa using (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    exact hc.tendsto.comp hp
  have hT := (hm.sub (vr_tendsto_int_S_kernel N σ hσ hδ hz)).add
    ((tendsto_const_nhds (x := z⁻¹)).mul ((Complex.continuous_ofReal.tendsto _).comp
      ((tendsto_const_nhds (x := (1 : ℝ))).sub (vr_tendsto_int_S N σ hσ hδ))))
  refine le_of_tendsto hT.norm ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact vr_step_eps N σ hσ hz hδ hδz hε

/-! ## The limit `δ → 0` -/

private lemma vr_rhoDens_of_neg (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    {x : ℝ} (hx : x < 0) : rhoDens N σ x = 0 := by
  rw [rhoDens, im_mExt_of_neg N σ hσ hN hx, zero_div]

private lemma vr_setIntegral_S_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} (hg : ∀ x : ℝ, x < 0 → g x = 0) {δ : ℝ} (hδ : 0 < δ) :
    ∫ x in vrS δ, g x = ∫ x in Set.Ici δ, g x := by
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (vrS_measurable δ) ?_ ?_
  · intro x hx
    have : δ ≤ x := hx
    show δ ≤ |x|
    exact this.trans (le_abs_self x)
  · intro x ⟨hx1, hx2⟩
    have h1 : δ ≤ |x| := hx1
    have h2 : ¬ δ ≤ x := hx2
    apply hg
    rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩ <;> [exact absurd (h ▸ h1) h2; linarith]

/-- The cutoffs `δ_n = 1/(n + 1)`. -/
private lemma vr_iUnion_Ici : (⋃ n : ℕ, Set.Ici (1 / ((n : ℝ) + 1))) = Set.Ioi 0 := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_Ici, Set.mem_Ioi]
  constructor
  · rintro ⟨n, hn⟩
    exact lt_of_lt_of_le (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity) hn
  · intro hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx
    exact ⟨n, hn.le⟩

private lemma vr_mono_Ici : Monotone (fun n : ℕ => Set.Ici (1 / ((n : ℝ) + 1))) := by
  intro m n hmn
  refine Set.Ici_subset_Ici.mpr ?_
  exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)

private lemma vr_integrableOn_rhoDens (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) :
    IntegrableOn (rhoDens N σ) (Set.Ioi 0) := by
  have hcov : AECover (volume.restrict (Set.Ioi (0 : ℝ))) atTop
      (fun n : ℕ => Set.Ici (1 / ((n : ℝ) + 1))) := by
    refine ⟨(ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx => ?_),
      fun n => measurableSet_Ici⟩
    have hx' : (0 : ℝ) < x := hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx'
    filter_upwards [eventually_ge_atTop n] with k hk
    exact vr_mono_Ici hk (show 1 / ((n : ℝ) + 1) ≤ x from hn.le)
  have hsub : ∀ n : ℕ, Set.Ici (1 / ((n : ℝ) + 1)) ⊆ Set.Ioi (0 : ℝ) := fun n x hx =>
    lt_of_lt_of_le (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity) hx
  have hres : ∀ n : ℕ, (volume.restrict (Set.Ioi (0 : ℝ))).restrict (Set.Ici (1 / ((n : ℝ) + 1)))
      = volume.restrict (Set.Ici (1 / ((n : ℝ) + 1))) := by
    intro n
    rw [Measure.restrict_restrict measurableSet_Ici, Set.inter_eq_self_of_subset_left (hsub n)]
  refine hcov.integrable_of_integral_norm_bounded 1 (fun n => ?_) (Eventually.of_forall fun n => ?_)
  · have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    rw [IntegrableOn, hres]
    exact (vr_integrableOn_rhoDens_S N σ hσ hδ).mono_set fun x hx =>
      (show 1 / ((n : ℝ) + 1) ≤ x from hx).trans (le_abs_self x)
  · have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    rw [hres]
    have h := vr_integral_rhoDens_S_le N σ hσ hδ
    rw [vr_setIntegral_S_eq (fun x hx => vr_rhoDens_of_neg N σ hσ hN hx) hδ] at h
    refine le_of_eq_of_le (setIntegral_congr_fun measurableSet_Ici fun x hx => ?_) h
    exact Real.norm_of_nonneg (vr_rhoDens_nonneg N σ hσ (hsub n hx).ne')

private lemma vr_integral_rhoDens_le_one (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i)
    (hN : 0 < N) : ∫ x in Set.Ioi 0, rhoDens N σ x ≤ 1 := by
  have hT := tendsto_setIntegral_of_monotone (μ := volume) (fun n => measurableSet_Ici)
    vr_mono_Ici (f := rhoDens N σ) (by rw [vr_iUnion_Ici]; exact vr_integrableOn_rhoDens N σ hσ hN)
  rw [vr_iUnion_Ici] at hT
  refine le_of_tendsto' hT fun n => ?_
  have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  rw [← vr_setIntegral_S_eq (fun x hx => vr_rhoDens_of_neg N σ hσ hN hx) hδ]
  exact vr_integral_rhoDens_S_le N σ hσ hδ

/-- The representation `m(z) = ∫_0^∞ ρ(x)(x - z)⁻¹ dx - z⁻¹(1 - ∫_0^∞ ρ)` on `ℂ₊`. -/
private lemma vr_rep (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {z : ℂ}
    (hz : 0 < z.im) :
    mFun N σ z = (∫ x in Set.Ioi 0, ((rhoDens N σ x : ℝ) : ℂ) * ((x : ℂ) - z)⁻¹) -
      z⁻¹ * ((1 - ∫ x in Set.Ioi 0, rhoDens N σ x : ℝ) : ℂ) := by
  have hI := vr_integrableOn_rhoDens N σ hσ hN
  have hIk : IntegrableOn (fun x : ℝ => ((rhoDens N σ x : ℝ) : ℂ) * ((x : ℂ) - z)⁻¹)
      (Set.Ioi 0) := vr_integrable_mul_inv hI hz
  have hA := tendsto_setIntegral_of_monotone (μ := volume) (fun n => measurableSet_Ici)
    vr_mono_Ici (f := rhoDens N σ) (by rw [vr_iUnion_Ici]; exact hI)
  have hB := tendsto_setIntegral_of_monotone (μ := volume) (fun n => measurableSet_Ici)
    vr_mono_Ici (f := fun x : ℝ => ((rhoDens N σ x : ℝ) : ℂ) * ((x : ℂ) - z)⁻¹)
    (by rw [vr_iUnion_Ici]; exact hIk)
  rw [vr_iUnion_Ici] at hA hB
  have hzn : 0 < ‖z‖ := lt_of_lt_of_le hz (Complex.im_le_norm z)
  have hδ0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hδ' : Tendsto (fun n : ℕ => 2 * (1 / ((n : ℝ) + 1)) / ‖z‖ ^ 2) atTop (𝓝 0) := by
    simpa using (hδ0.const_mul 2).div_const (‖z‖ ^ 2)
  have hE := (tendsto_const_nhds (x := mFun N σ z)).sub hB |>.add
    ((tendsto_const_nhds (x := z⁻¹)).mul ((Complex.continuous_ofReal.tendsto _).comp
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hA)))
  have hle := le_of_tendsto_of_tendsto hE.norm hδ' (by
    filter_upwards [(tendsto_order.1 hδ0).2 _ (half_pos hzn)] with n hn
    have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have h := vr_limit_eps N σ hσ hz hδ hn.le
    rw [vr_setIntegral_S_eq (fun x hx => by rw [vr_rhoDens_of_neg N σ hσ hN hx]; simp) hδ,
      vr_setIntegral_S_eq (fun x hx => vr_rhoDens_of_neg N σ hσ hN hx) hδ] at h
    exact h)
  have h0 := norm_le_zero_iff.mp hle
  linear_combination h0

/-! ## The atom: `1 - ∫_0^∞ ρ = (1 - R)₊` -/

/-- `z m(z) = N⁻¹ Σ_i σ_i m/(1 + σ_i m) - 1`, from `f(m) = z`. -/
private lemma vr_zm (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {z : ℂ} (hz : 0 < z.im) :
    z * mFun N σ z =
      (∑ i, (σ i : ℂ) * mFun N σ z / (N * (1 + σ i * mFun N σ z))) - 1 := by
  obtain ⟨hm, hfm⟩ := mFun_spec N σ hσ hz
  set m := mFun N σ z
  have hm0 : m ≠ 0 := fun h => by simp [h] at hm
  have hterm : ∀ i, (σ i : ℂ) * m / (N * (1 + σ i * m)) =
      (σ i : ℂ) / (N * (1 + σ i * m)) * m := fun i => by ring
  rw [← hfm, fC, add_mul, Finset.sum_mul, neg_mul, inv_mul_cancel₀ hm0,
    Finset.sum_congr rfl fun i _ => hterm i]
  ring

private lemma vr_massRatio_eq_sum (N : ℕ) (σ : Fin M → ℝ) :
    massRatio N σ = ∑ i, if 0 < σ i then (1 / N : ℝ) else 0 := by
  rw [massRatio, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul]
  ring

/-- `|N⁻¹ Σ_i σ_i w/(1 + σ_i w)| ≤ R` for `Re w ≥ 0`. -/
private lemma vr_norm_h_le (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {w : ℂ}
    (hw : 0 ≤ w.re) :
    ‖∑ i, (σ i : ℂ) * w / (N * (1 + σ i * w))‖ ≤ massRatio N σ := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [vr_massRatio_eq_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rcases (hσ i).eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · simp only [hpos, ↓reduceIte]
    have hv : 0 ≤ ((σ i : ℂ) * w).re := by simp; positivity
    have hle : ‖(σ i : ℂ) * w‖ ≤ ‖1 + (σ i : ℂ) * w‖ := by
      rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
        Complex.normSq_apply, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, zero_add]
      nlinarith
    have hpos' : 0 < ‖1 + (σ i : ℂ) * w‖ := by
      refine lt_of_lt_of_le ?_ (Complex.abs_re_le_norm _)
      simp only [Complex.add_re, Complex.one_re]
      rw [abs_of_pos (by linarith)]
      linarith
    rw [norm_div, norm_mul (N : ℂ), Complex.norm_natCast, div_le_div_iff₀ (by positivity) hNr]
    nlinarith

/-- `|N⁻¹ Σ_i σ_i w/(1 + σ_i w) - R| ≤ Σ_{σ_i > 0} (N σ_i Im w)⁻¹` for `Im w > 0`. -/
private lemma vr_norm_h_sub_le (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    {w : ℂ} (hw : 0 < w.im) :
    ‖(∑ i, (σ i : ℂ) * w / (N * (1 + σ i * w))) - (massRatio N σ : ℂ)‖ ≤
      ∑ i, if 0 < σ i then 1 / (N * σ i * w.im) else 0 := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [vr_massRatio_eq_sum, Complex.ofReal_sum, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rcases (hσ i).eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · simp only [hpos, ↓reduceIte]
    have hne : 1 + (σ i : ℂ) * w ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      rcases this with h1 | h1 <;> linarith
    have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have heq : (σ i : ℂ) * w / (N * (1 + σ i * w)) - (((1 / N : ℝ)) : ℂ) =
        -(1 / (N * (1 + σ i * w))) := by
      push_cast
      field_simp
      ring
    rw [heq, norm_neg, norm_div, norm_one, norm_mul, Complex.norm_natCast]
    have him : σ i * w.im ≤ ‖1 + (σ i : ℂ) * w‖ := by
      refine le_trans ?_ (Complex.abs_im_le_norm _)
      simp only [Complex.add_im, Complex.one_im, zero_add, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero]
      exact le_abs_self _
    rw [mul_assoc]
    exact one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_left him hNr.le)

/-- `Re` and `Im` of `∫_0^∞ ρ(x)(x - iy)⁻¹ dx` are nonnegative for `y > 0`. -/
private lemma vr_re_im_nonneg (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    {y : ℝ} (hy : 0 < y) :
    0 ≤ (∫ x in Set.Ioi 0, ((rhoDens N σ x : ℝ) : ℂ) * ((x : ℂ) - y * Complex.I)⁻¹).re ∧
    0 ≤ (∫ x in Set.Ioi 0, ((rhoDens N σ x : ℝ) : ℂ) * ((x : ℂ) - y * Complex.I)⁻¹).im := by
  have hIk : IntegrableOn (fun x : ℝ => ((rhoDens N σ x : ℝ) : ℂ) * ((x : ℂ) - y * Complex.I)⁻¹)
      (Set.Ioi 0) := vr_integrable_mul_inv (vr_integrableOn_rhoDens N σ hσ hN) (by simpa using hy)
  have hpt : ∀ x : ℝ, 0 < x →
      0 ≤ (((rhoDens N σ x : ℝ) : ℂ) * ((x : ℂ) - y * Complex.I)⁻¹).re ∧
      0 ≤ (((rhoDens N σ x : ℝ) : ℂ) * ((x : ℂ) - y * Complex.I)⁻¹).im := by
    intro x hx
    have hr := vr_rhoDens_nonneg N σ hσ hx.ne'
    have hd : x ^ 2 + y ^ 2 ≠ 0 := by positivity
    have hre : (((rhoDens N σ x : ℝ) : ℂ) * ((x : ℂ) - y * Complex.I)⁻¹).re =
        rhoDens N σ x * (x / (x ^ 2 + y ^ 2)) := by
      simp [Complex.mul_re, Complex.inv_re, Complex.inv_im, Complex.normSq]
      field_simp
      simp
    have him : (((rhoDens N σ x : ℝ) : ℂ) * ((x : ℂ) - y * Complex.I)⁻¹).im =
        rhoDens N σ x * (y / (x ^ 2 + y ^ 2)) := by
      simp [Complex.mul_im, Complex.inv_re, Complex.inv_im, Complex.normSq]
      field_simp
      simp
    rw [hre, him]
    exact ⟨mul_nonneg hr (by positivity), mul_nonneg hr (by positivity)⟩
  constructor
  · rw [← RCLike.re_to_complex, ← integral_re hIk]
    exact setIntegral_nonneg measurableSet_Ioi fun x hx => by
      rw [RCLike.re_to_complex]; exact (hpt x hx).1
  · rw [← RCLike.im_to_complex, ← integral_im hIk]
    exact setIntegral_nonneg measurableSet_Ioi fun x hx => by
      rw [RCLike.im_to_complex]; exact (hpt x hx).2

/-- `∫_0^∞ ρ(x) iy (x - iy)⁻¹ dx → 0` as `y ↓ 0`. -/
private lemma vr_tendsto_T (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) :
    Tendsto (fun y : ℝ => ∫ x in Set.Ioi 0, ((rhoDens N σ x : ℝ) : ℂ) *
      (y * Complex.I * ((x : ℂ) - y * Complex.I)⁻¹)) (𝓝[>] 0) (𝓝 0) := by
  have hI := vr_integrableOn_rhoDens N σ hσ hN
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Set.Ioi 0))
    (l := 𝓝[>] (0 : ℝ)) (f := fun _ => (0 : ℂ))
    (F := fun (y : ℝ) (x : ℝ) => ((rhoDens N σ x : ℝ) : ℂ) *
      (y * Complex.I * ((x : ℂ) - y * Complex.I)⁻¹))
    (fun x => ‖rhoDens N σ x‖) ?_ ?_ hI.norm ?_
  · simpa using h
  · filter_upwards [self_mem_nhdsWithin] with y hy
    have hy' : (0 : ℝ) < y := hy
    refine (Complex.continuous_ofReal.comp_aestronglyMeasurable hI.1).mul ?_
    refine Continuous.aestronglyMeasurable ?_
    exact continuous_const.mul ((Complex.continuous_ofReal.sub continuous_const).inv₀
      fun x => vr_ofReal_sub_ne x (by simpa using hy'.ne'))
  · filter_upwards [self_mem_nhdsWithin] with y hy
    have hy' : (0 : ℝ) < y := hy
    refine ae_of_all _ fun x => ?_
    have hle : y ≤ ‖(x : ℂ) - y * Complex.I‖ := by
      have h := Complex.abs_im_le_norm ((x : ℂ) - y * Complex.I)
      simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_sub, abs_neg] at h
      exact (le_abs_self y).trans h
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, norm_inv, Complex.norm_real,
      Complex.norm_real, Real.norm_of_nonneg hy'.le]
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    rw [← div_eq_mul_inv, div_le_one (lt_of_lt_of_le hy' hle)]
    exact hle
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx => ?_)
    have hx' : (0 : ℝ) < x := hx
    have hc : ContinuousAt (fun y : ℝ => ((rhoDens N σ x : ℝ) : ℂ) *
        (y * Complex.I * ((x : ℂ) - y * Complex.I)⁻¹)) 0 := by
      refine continuousAt_const.mul (ContinuousAt.mul (by fun_prop) ?_)
      refine ContinuousAt.inv₀ (by fun_prop) ?_
      simpa using hx'.ne'
    have h0 := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using h0

/-- The atom: `1 - ∫_0^∞ ρ = (1 - R)₊`. -/
private lemma vr_atom (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) :
    1 - ∫ x in Set.Ioi 0, rhoDens N σ x = max (1 - massRatio N σ) 0 := by
  set A := ∫ x in Set.Ioi 0, rhoDens N σ x with hA
  set R := massRatio N σ with hR
  have hA1 : A ≤ 1 := vr_integral_rhoDens_le_one N σ hσ hN
  have hA0 : 0 ≤ A := setIntegral_nonneg measurableSet_Ioi fun x hx =>
    vr_rhoDens_nonneg N σ hσ (ne_of_gt hx)
  set T : ℝ → ℂ := fun y => ∫ x in Set.Ioi 0, ((rhoDens N σ x : ℝ) : ℂ) *
    (y * Complex.I * ((x : ℂ) - y * Complex.I)⁻¹) with hT
  set B : ℝ → ℂ := fun y => ∫ x in Set.Ioi 0, ((rhoDens N σ x : ℝ) : ℂ) *
    ((x : ℂ) - y * Complex.I)⁻¹ with hB
  set H : ℂ → ℂ := fun w => ∑ i, (σ i : ℂ) * w / (N * (1 + σ i * w)) with hH
  have hyz : ∀ y : ℝ, 0 < y → 0 < ((y : ℂ) * Complex.I).im := fun y hy => by simpa using hy
  have hm : ∀ y : ℝ, 0 < y → mFun N σ (y * Complex.I) =
      B y - (y * Complex.I)⁻¹ * ((1 - A : ℝ) : ℂ) := fun y hy => vr_rep N σ hσ hN (hyz y hy)
  have hTB : ∀ y : ℝ, T y = (y * Complex.I) * B y := by
    intro y
    simp only [hT, hB]
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only
    ring
  have hinv : ∀ y : ℝ, 0 < y → (y * Complex.I)⁻¹ * ((1 - A : ℝ) : ℂ) =
      ((-((1 - A) / y) : ℝ) : ℂ) * Complex.I := by
    intro y hy
    have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    rw [mul_inv, Complex.inv_I]
    push_cast
    field_simp
  have hkey : ∀ y : ℝ, 0 < y → H (mFun N σ (y * Complex.I)) = (A : ℂ) + T y := by
    intro y hy
    have h1 := vr_zm N σ hσ (hyz y hy)
    have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    calc H (mFun N σ (y * Complex.I)) = y * Complex.I * mFun N σ (y * Complex.I) + 1 := by
          simp only [hH]; rw [h1]; ring
      _ = y * Complex.I * (B y - (y * Complex.I)⁻¹ * ((1 - A : ℝ) : ℂ)) + 1 := by rw [hm y hy]
      _ = (A : ℂ) + T y := by
          rw [hTB]
          push_cast
          field_simp
          ring
  have hre : ∀ y : ℝ, 0 < y → 0 ≤ (mFun N σ (y * Complex.I)).re := by
    intro y hy
    rw [hm y hy, hinv y hy, Complex.sub_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero,
      sub_zero]
    exact (vr_re_im_nonneg N σ hσ hN hy).1
  have him : ∀ y : ℝ, 0 < y → (1 - A) / y ≤ (mFun N σ (y * Complex.I)).im := by
    intro y hy
    rw [hm y hy, hinv y hy, Complex.sub_im, Complex.im_ofReal_mul, Complex.I_im, mul_one]
    linarith [(vr_re_im_nonneg N σ hσ hN hy).2]
  have hTt := vr_tendsto_T N σ hσ hN
  -- `A ≤ R`
  have step1 : A ≤ R := by
    have hlim : Tendsto (fun y : ℝ => ‖(A : ℂ) + T y‖) (𝓝[>] 0) (𝓝 ‖(A : ℂ) + 0‖) :=
      ((tendsto_const_nhds.add hTt).norm)
    rw [add_zero, Complex.norm_real, Real.norm_of_nonneg hA0] at hlim
    refine le_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [← hkey y hy]
    exact vr_norm_h_le N σ hσ hN (hre y hy)
  -- `A < 1 → A = R`
  have step2 : A < 1 → A = R := by
    intro hc
    have hc' : 0 < 1 - A := by linarith
    set Q := ∑ i, if 0 < σ i then 1 / (N * σ i * (1 - A)) else 0 with hQ
    have hlim : Tendsto (fun y : ℝ => ‖((A - R : ℝ) : ℂ) + T y‖) (𝓝[>] 0)
        (𝓝 ‖((A - R : ℝ) : ℂ) + 0‖) := (tendsto_const_nhds.add hTt).norm
    have hlim2 : Tendsto (fun y : ℝ => y * Q) (𝓝[>] 0) (𝓝 (0 * Q)) :=
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).mul_const _
    have hle := le_of_tendsto_of_tendsto hlim hlim2 (by
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hy' : (0 : ℝ) < y := hy
      have hmi : 0 < (mFun N σ (y * Complex.I)).im := (mFun_spec N σ hσ (hyz y hy')).1
      have h1 := vr_norm_h_sub_le N σ hσ hN hmi
      have heq : ((A - R : ℝ) : ℂ) + T y = H (mFun N σ (y * Complex.I)) - (R : ℂ) := by
        rw [hkey y hy']; push_cast; ring
      rw [heq]
      refine h1.trans ?_
      rw [hQ, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      split_ifs with hpos
      · have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
        have hlow := him y hy'
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
        calc N * σ i * (1 - A) = N * σ i * ((1 - A) / y * y) := by field_simp
          _ ≤ N * σ i * ((mFun N σ (y * Complex.I)).im * y) := by
              gcongr
          _ = y * (N * σ i * (mFun N σ (y * Complex.I)).im) := by ring
      · simp)
    rw [add_zero, zero_mul, norm_le_zero_iff, Complex.ofReal_eq_zero] at hle
    linarith
  rcases lt_or_ge A 1 with hc | hc
  · have := step2 hc
    rw [max_eq_left (by linarith)]
    linarith
  · have hA : A = 1 := le_antisymm hA1 hc
    rw [max_eq_right (by linarith), hA, sub_self]

/-! ## Second half of Lemma 2.2 -/

/-- `ϱ` is a probability measure (Lemma 2.2). -/
theorem isProbabilityMeasure_varrho (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i)
    (hN : 0 < N) : IsProbabilityMeasure (varrho N σ) := by
  constructor
  have hI := vr_integrableOn_rhoDens N σ hσ hN
  have h0 : 0 ≤ᵐ[volume.restrict (Set.Ioi 0)] rhoDens N σ :=
    (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx =>
      vr_rhoDens_nonneg N σ hσ (ne_of_gt hx))
  have hA : ∫ x in Set.Ioi 0, rhoDens N σ x = 1 - max (1 - massRatio N σ) 0 := by
    linarith [vr_atom N σ hσ hN]
  have hA0 : 0 ≤ 1 - max (1 - massRatio N σ) 0 := by
    rw [← hA]; exact setIntegral_nonneg_of_ae_restrict h0
  rw [varrho, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hI h0, hA,
    ← ENNReal.ofReal_add (le_max_right _ _) hA0, add_sub_cancel, ENNReal.ofReal_one]

/-- `m` is the Stieltjes transform of `ϱ` on `ℂ₊` (Lemma 2.2, Definition 2.3). -/
theorem resolventTransform_varrho (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    {z : ℂ} (hz : 0 < z.im) : resolventTransform (varrho N σ) z = mFun N σ z := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  have hI := vr_integrableOn_rhoDens N σ hσ hN
  have hres : ∀ x : ℝ, resolvent z x = ((x : ℂ) - z)⁻¹ := by
    intro x
    simp [resolvent, Ring.inverse_eq_inv']
  rw [resolventTransform_apply]
  simp_rw [hres]
  have hint : Integrable (fun x : ℝ => ((x : ℂ) - z)⁻¹) (varrho N σ) := by
    refine Integrable.of_bound ?_ (z.im)⁻¹ (ae_of_all _ fun x => ?_)
    · exact ((Complex.continuous_ofReal.sub continuous_const).inv₀
        fun x => vr_ofReal_sub_ne x hz.ne').aestronglyMeasurable
    · have h := vr_norm_mul_inv_le 1 x hz
      simpa using h
  rw [varrho] at hint ⊢
  rw [integral_add_measure (hint.mono_measure (Measure.le_add_right le_rfl))
    (hint.mono_measure (Measure.le_add_left le_rfl)), integral_smul_measure, integral_dirac,
    integral_withDensity_eq_integral_toReal_smul₀ hI.1.aemeasurable.ennreal_ofReal
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  have hw : ∫ x in Set.Ioi 0, (ENNReal.ofReal (rhoDens N σ x)).toReal • ((x : ℂ) - z)⁻¹ =
      ∫ x in Set.Ioi 0, ((rhoDens N σ x : ℝ) : ℂ) * ((x : ℂ) - z)⁻¹ := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [ENNReal.toReal_ofReal (vr_rhoDens_nonneg N σ hσ (ne_of_gt hx)), Complex.real_smul]
  rw [hw, vr_rep N σ hσ hN hz, vr_atom N σ hσ hN,
    ENNReal.toReal_ofReal (le_max_right _ _), Complex.real_smul, Complex.ofReal_zero, zero_sub,
    inv_neg]
  ring

/-- `ϱ` is supported in `[0, X₀]`, `X₀ = (1 + √R) s₁ max(2, √(8R))`, for any `s₁ ≥ max_i σ_i`. -/
theorem varrho_compl_Icc (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {s₁ : ℝ}
    (hs₁0 : 0 ≤ s₁) (hs₁ : ∀ i, σ i ≤ s₁) :
    varrho N σ (Set.Icc 0 ((1 + √(massRatio N σ)) * s₁ *
      max 2 (√(8 * massRatio N σ))))ᶜ = 0 := by
  set X₀ := (1 + √(massRatio N σ)) * s₁ * max 2 (√(8 * massRatio N σ)) with hX₀
  have hX0 : 0 ≤ X₀ := by
    have : 0 ≤ max 2 (√(8 * massRatio N σ)) := le_trans (by norm_num) (le_max_left _ _)
    positivity
  have hs : MeasurableSet (Set.Icc 0 X₀)ᶜ := measurableSet_Icc.compl
  have h0 : (0 : ℝ) ∉ (Set.Icc 0 X₀)ᶜ := fun h => h ⟨le_rfl, hX0⟩
  rw [varrho, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hs,
    Set.indicator_of_notMem h0, smul_zero, zero_add, withDensity_apply _ hs,
    Measure.restrict_restrict hs]
  refine setLIntegral_eq_zero (hs.inter measurableSet_Ioi) fun x ⟨hx1, hx2⟩ => ?_
  have hx2' : (0 : ℝ) < x := hx2
  have hxX : X₀ < x := by
    by_contra h
    exact hx1 ⟨hx2'.le, not_lt.mp h⟩
  simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero]
  rw [rhoDens, vr_im_mExt_eq_zero N σ hσ hs₁0 hs₁ hxX, zero_div]

/-! ## Concrete instance (Marchenko–Pastur: `M = 1`, `N = 2`, `σ = 1`, `R = 1/2`) -/

/-- MP: `ϱ` is a probability measure. -/
example : IsProbabilityMeasure (varrho 2 (fun _ : Fin 1 => (1 : ℝ))) :=
  isProbabilityMeasure_varrho 2 _ (fun _ => by norm_num) (by norm_num)

/-- MP, `z = i`: the Stieltjes transform of `ϱ` is `m`. -/
example : resolventTransform (varrho 2 (fun _ : Fin 1 => (1 : ℝ))) Complex.I =
    mFun 2 (fun _ : Fin 1 => (1 : ℝ)) Complex.I :=
  resolventTransform_varrho 2 _ (fun _ => by norm_num) (by norm_num) (by simp)

example : max (1 - massRatio 2 (fun _ : Fin 1 => (1 : ℝ))) 0 = 1 / 2 := by
  norm_num [massRatio]

/-- MP, `s₁ = 1`: `ϱ` vanishes outside `[0, X₀]`, `X₀ = (1 + √(1/2)) max(2, √4)`. -/
example : varrho 2 (fun _ : Fin 1 => (1 : ℝ)) (Set.Icc 0 ((1 + √(massRatio 2
    (fun _ : Fin 1 => (1 : ℝ)))) * 1 * max 2 (√(8 * massRatio 2 (fun _ : Fin 1 => (1 : ℝ))))))ᶜ
    = 0 :=
  varrho_compl_Icc 2 _ (fun _ => by norm_num) (by norm_num) (by norm_num) (fun _ => le_rfl)

end Anisotropic
