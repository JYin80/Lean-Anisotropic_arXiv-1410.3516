module

public import Anisotropic.Density.Stability.Domains

@[expose] public section

open MeasureTheory Polynomial Filter Topology
open scoped ENNReal

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-- The control functions of Definition 5.4 on `S`: `N⁻² ≤ δ ≤ (log N)⁻¹`, `N²`-Lipschitz,
nonincreasing in `η` at fixed `E`. -/
structure AdmissibleDelta (N : ℕ) (S : Set ℂ) (δ : ℂ → ℝ) : Prop where
  lower : ∀ z ∈ S, ((N : ℝ) ^ 2)⁻¹ ≤ δ z
  upper : ∀ z ∈ S, δ z ≤ (Real.log N)⁻¹
  lipschitz : ∀ z ∈ S, ∀ w ∈ S, |δ z - δ w| ≤ (N : ℝ) ^ 2 * ‖z - w‖
  antitone : ∀ z ∈ S, ∀ w ∈ S, w.re = z.re → z.im ≤ w.im → δ w ≤ δ z

/-- The two-regime bound `C d / (D + √d)`, with `C = C₀` if `κ + η > K₀ d` and `C = C₁`
otherwise. -/
def twoRegime (C₀ C₁ K₀ κ η d D : ℝ) : ℝ :=
  (if K₀ * d < κ + η then C₀ else C₁) * (d / (D + √d))

/-- The bound of (strong_stab): denominator `√(κ + η) + √δ`. -/
def strongBound (C₀ C₁ K₀ : ℝ) (N : ℕ) (σ : Fin M → ℝ) (δ : ℂ → ℝ) (z : ℂ) : ℝ :=
  twoRegime C₀ C₁ K₀ (kappa N σ z.re) z.im (δ z) √(kappa N σ z.re + z.im)

/-- The bound of (u-m_stability): denominator `Im m + √δ`. -/
def weakBound (C₀ C₁ K₀ : ℝ) (N : ℕ) (σ : Fin M → ℝ) (δ : ℂ → ℝ) (z : ℂ) : ℝ :=
  twoRegime C₀ C₁ K₀ (kappa N σ z.re) z.im (δ z) (mFun N σ z).im

/-- The one-step implication of Definition 5.4 with the bound `B δ`: for every admissible `δ`,
every Stieltjes transform `u` of a probability measure and every `z ∈ S` with
`|f(u(z)) - z| ≤ δ(z)`, the bound at `z + i N⁻⁵` (required when `Im z < 1`) gives the bound
at `z`. -/
def StableWith (B : (ℂ → ℝ) → ℂ → ℝ) (N : ℕ) (σ : Fin M → ℝ) (S : Set ℂ) : Prop :=
  ∀ δ : ℂ → ℝ, AdmissibleDelta N S δ →
  ∀ μ : Measure ℝ, IsProbabilityMeasure μ →
  ∀ z ∈ S, ‖fC N σ (resolventTransform μ z) - z‖ ≤ δ z →
    (z.im < 1 → ‖resolventTransform μ (shiftUp N z) - mFun N σ (shiftUp N z)‖ ≤
      B δ (shiftUp N z)) →
    ‖resolventTransform μ z - mFun N σ z‖ ≤ B δ z

/-- Definition 5.4 (stability), with the two-regime constants. -/
def StableOn (C₀ C₁ K₀ : ℝ) (N : ℕ) (σ : Fin M → ℝ) (S : Set ℂ) : Prop :=
  StableWith (weakBound C₀ C₁ K₀ N σ) N σ S

/-- Definition A.2 (strong stability), with the two-regime constants. -/
def StronglyStableOn (C₀ C₁ K₀ : ℝ) (N : ℕ) (σ : Fin M → ℝ) (S : Set ℂ) : Prop :=
  StableWith (strongBound C₀ C₁ K₀ N σ) N σ S

/-- The quotient `d / (D + √d)` is nonnegative. -/
private theorem twoRegime_quot_nonneg {d D : ℝ} (hd : 0 ≤ d) (hD : 0 ≤ D) :
    0 ≤ d / (D + √d) :=
  div_nonneg hd (add_nonneg hD (Real.sqrt_nonneg d))

/-- The quotient `d / (D + √d)` is nondecreasing in `d` and nonincreasing in `D`. -/
private theorem twoRegime_quot_mono {d d' D D' : ℝ} (hd' : 0 < d') (hdd' : d' ≤ d)
    (hD : 0 ≤ D) (hDD' : D ≤ D') : d' / (D' + √d') ≤ d / (D + √d) := by
  have hd : 0 < d := lt_of_lt_of_le hd' hdd'
  have ha : 0 < √d := Real.sqrt_pos.2 hd
  have hb : 0 < √d' := Real.sqrt_pos.2 hd'
  have hba : √d' ≤ √d := Real.sqrt_le_sqrt hdd'
  rw [div_le_div_iff₀ (add_pos_of_nonneg_of_pos (hD.trans hDD') hb)
    (add_pos_of_nonneg_of_pos hD ha)]
  have h1 : d' * D ≤ d * D' := mul_le_mul hdd' hDD' hD hd.le
  have h2 : d' * √d ≤ d * √d' := by
    have e1 := Real.sq_sqrt hd'.le
    have e2 := Real.sq_sqrt hd.le
    have h3 := mul_nonneg (mul_nonneg ha.le hb.le) (sub_nonneg.2 hba)
    have h4 : √d' ^ 2 * √d ≤ √d ^ 2 * √d' := by nlinarith [h3]
    rwa [e1, e2] at h4
  rw [mul_add, mul_add]
  linarith

/-- Kernel bound: `Im z ≤ ‖x - z‖` for real `x` and `Im z > 0`. -/
private theorem twoRegime_im_le_norm (z : ℂ) (x : ℝ) : z.im ≤ ‖(x : ℂ) - z‖ := by
  have h := Complex.abs_im_le_norm ((x : ℂ) - z)
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] at h
  exact le_trans (le_abs_self _) h

private theorem twoRegime_resolvent_eq (z : ℂ) (x : ℝ) : resolvent z x = ((x : ℂ) - z)⁻¹ := by
  simp [resolvent, Ring.inverse_eq_inv']

private theorem twoRegime_ofReal_sub_ne {z : ℂ} (hz : 0 < z.im) (x : ℝ) : (x : ℂ) - z ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

/-- The kernel `x ↦ (x - z)⁻¹` is integrable for a probability measure when `Im z > 0`. -/
private theorem twoRegime_integrable_kernel (μ : Measure ℝ) [IsProbabilityMeasure μ] {z : ℂ}
    (hz : 0 < z.im) : Integrable (fun x : ℝ => ((x : ℂ) - z)⁻¹) μ := by
  refine Integrable.of_bound ?_ (z.im)⁻¹ (ae_of_all _ fun x => ?_)
  · exact ((Complex.continuous_ofReal.sub continuous_const).inv₀
      fun x => twoRegime_ofReal_sub_ne hz x).aestronglyMeasurable
  · rw [norm_inv]
    exact inv_anti₀ hz (twoRegime_im_le_norm z x)

/-- The bound does not increase from `z` to `z + i N⁻⁵`: the thin regime `κ + η ≤ K₀ δ` is
closed under decreasing `η` when `δ` is nonincreasing in `η`. -/
theorem twoRegime_mono {C₀ C₁ K₀ κ η η' d d' : ℝ} (hC₀ : 0 ≤ C₀) (hC : C₀ ≤ C₁)
    (hK₀ : 0 ≤ K₀) (hκ : 0 ≤ κ) (hη : 0 < η) (hηη' : η ≤ η') (hd' : 0 < d') (hdd' : d' ≤ d) :
    twoRegime C₀ C₁ K₀ κ η' d' √(κ + η') ≤ twoRegime C₀ C₁ K₀ κ η d √(κ + η) := by
  have hd : 0 < d := lt_of_lt_of_le hd' hdd'
  have hD : 0 ≤ √(κ + η) := Real.sqrt_nonneg _
  have hDD' : √(κ + η) ≤ √(κ + η') := Real.sqrt_le_sqrt (by linarith)
  have hq := twoRegime_quot_mono hd' hdd' hD hDD'
  have hq0 : 0 ≤ d / (√(κ + η) + √d) := twoRegime_quot_nonneg hd.le hD
  have hq0' : 0 ≤ d' / (√(κ + η') + √d') := twoRegime_quot_nonneg hd'.le (Real.sqrt_nonneg _)
  have hC₁ : 0 ≤ C₁ := le_trans hC₀ hC
  unfold twoRegime
  by_cases h' : K₀ * d' < κ + η'
  · by_cases h : K₀ * d < κ + η
    · simp only [h', h, ↓reduceIte]
      exact mul_le_mul_of_nonneg_left hq hC₀
    · simp only [h', h, ↓reduceIte]
      calc C₀ * (d' / (√(κ + η') + √d')) ≤ C₀ * (d / (√(κ + η) + √d)) :=
            mul_le_mul_of_nonneg_left hq hC₀
        _ ≤ C₁ * (d / (√(κ + η) + √d)) := mul_le_mul_of_nonneg_right hC hq0
  · have h : ¬ K₀ * d < κ + η := by
      intro h
      apply h'
      have h' := not_lt.1 h'
      have : K₀ * d' ≤ K₀ * d := mul_le_mul_of_nonneg_left hdd' hK₀
      linarith
    simp only [h', h, ↓reduceIte]
    exact mul_le_mul_of_nonneg_left hq hC₁

/-- With `C₀ ≤ C₁`, the two-regime bound is at most the bound with the larger constant,
`C₁ d / (D + √d)`. -/
theorem twoRegime_le {C₀ C₁ K₀ κ η d D : ℝ} (hC : C₀ ≤ C₁) (hd : 0 ≤ d) (hD : 0 ≤ D) :
    twoRegime C₀ C₁ K₀ κ η d D ≤ C₁ * (d / (D + √d)) := by
  unfold twoRegime
  split_ifs
  · exact mul_le_mul_of_nonneg_right hC (twoRegime_quot_nonneg hd hD)
  · exact le_rfl

theorem im_resolventTransform_pos (μ : Measure ℝ) [IsProbabilityMeasure μ] {z : ℂ}
    (hz : 0 < z.im) : 0 < (resolventTransform μ z : ℂ).im := by
  have hint := twoRegime_integrable_kernel μ hz
  rw [resolventTransform_apply]
  simp_rw [twoRegime_resolvent_eq]
  have him : (∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂μ).im = ∫ x : ℝ, (((x : ℂ) - z)⁻¹).im ∂μ := by
    have := integral_im (𝕜 := ℂ) hint
    simpa using this.symm
  rw [him]
  have hpos : ∀ x : ℝ, 0 < (((x : ℂ) - z)⁻¹).im := by
    intro x
    rw [Complex.inv_im, Complex.sub_im, Complex.ofReal_im, zero_sub, neg_neg]
    exact div_pos hz (Complex.normSq_pos.2 (twoRegime_ofReal_sub_ne hz x))
  have hint' : Integrable (fun x : ℝ => (((x : ℂ) - z)⁻¹).im) μ := by
    simpa using hint.im
  rw [integral_pos_iff_support_of_nonneg (fun x => (hpos x).le) hint']
  have : Function.support (fun x : ℝ => (((x : ℂ) - z)⁻¹).im) = Set.univ :=
    Set.eq_univ_of_forall fun x => (hpos x).ne'
  rw [this]
  simp

/-- `|u(z) - u(w)| ≤ |z - w| / (Im z Im w)` for a Stieltjes transform `u`. -/
theorem norm_resolventTransform_sub_le (μ : Measure ℝ) [IsProbabilityMeasure μ] {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    ‖(resolventTransform μ z : ℂ) - resolventTransform μ w‖ ≤ ‖z - w‖ / (z.im * w.im) := by
  have h1 := twoRegime_integrable_kernel μ hz
  have h2 := twoRegime_integrable_kernel μ hw
  rw [resolventTransform_apply, resolventTransform_apply]
  simp_rw [twoRegime_resolvent_eq]
  rw [← integral_sub h1 h2]
  have hb : ∀ x : ℝ, ‖((x : ℂ) - z)⁻¹ - ((x : ℂ) - w)⁻¹‖ ≤ ‖z - w‖ / (z.im * w.im) := by
    intro x
    have hz0 := twoRegime_ofReal_sub_ne hz x
    have hw0 := twoRegime_ofReal_sub_ne hw x
    have e : ((x : ℂ) - z)⁻¹ - ((x : ℂ) - w)⁻¹ = (z - w) / (((x : ℂ) - z) * ((x : ℂ) - w)) := by
      field_simp
      ring
    rw [e, norm_div, norm_mul]
    apply div_le_div_of_nonneg_left (norm_nonneg _) (mul_pos hz hw)
    exact mul_le_mul (twoRegime_im_le_norm z x) (twoRegime_im_le_norm w x) hw.le
      (norm_nonneg _)
  have := norm_integral_le_of_norm_le_const (μ := μ) (ae_of_all _ hb)
  simpa using this

/-- The case `Im z ≥ h` of Lemma A.5: `u = m(f(u))` and `|u - m| ≤ 2 |f(u) - z| / h²`. -/
theorem norm_sub_mFun_le_of_im_ge {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    {h : ℝ} (hh : 0 < h) {z u : ℂ} (hz : h ≤ z.im) (hu : 0 < u.im)
    (hw : ‖fC N σ u - z‖ ≤ h / 2) : ‖u - mFun N σ z‖ ≤ 2 * ‖fC N σ u - z‖ / h ^ 2 := by
  have hwim : h / 2 ≤ (fC N σ u).im := by
    have h1 := Complex.abs_im_le_norm (fC N σ u - z)
    rw [Complex.sub_im] at h1
    have h2 := neg_abs_le ((fC N σ u).im - z.im)
    linarith
  have hw0 : 0 < (fC N σ u).im := lt_of_lt_of_le (by linarith) hwim
  have hz0 : 0 < z.im := lt_of_lt_of_le hh hz
  have hmu : mFun N σ (fC N σ u) = u := mFun_eq_of_fC_eq N σ hσ hw0 hu rfl
  have := isProbabilityMeasure_varrho N σ hσ hN
  have hL := norm_resolventTransform_sub_le (varrho N σ) hw0 hz0
  rw [resolventTransform_varrho N σ hσ hN hw0, resolventTransform_varrho N σ hσ hN hz0,
    hmu] at hL
  have hden : h ^ 2 / 2 ≤ (fC N σ u).im * z.im := by nlinarith
  refine hL.trans ?_
  rw [mul_div_assoc, show 2 * (‖fC N σ u - z‖ / h ^ 2) = ‖fC N σ u - z‖ / (h ^ 2 / 2) by
    field_simp]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hden

/-! ## Instances -/

/-- A nondegenerate admissible `δ`: the constant `(log 3)⁻¹` at `N = 3`, on any `S`. -/
example (S : Set ℂ) : AdmissibleDelta 3 S (fun _ => (Real.log 3)⁻¹) := by
  have hl : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hl2 : Real.log 3 ≤ 3 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  refine ⟨fun z _ => ?_, fun z _ => ?_, fun z _ w _ => ?_, fun z _ w _ _ _ => le_rfl⟩
  · push_cast
    exact inv_anti₀ hl (by linarith)
  · push_cast; exact le_rfl
  · simp only [sub_self, abs_zero]; positivity

/-- Both regimes are inhabited: `δ = 10⁻³`, `η = 10⁻⁴`, `K₀ = 36`; `κ = 0.1` is thick. -/
example (D : ℝ) : twoRegime 10 50 36 (1 / 10) (1 / 10000) (1 / 1000) D =
    10 * ((1 / 1000) / (D + √(1 / 1000))) := by
  rw [twoRegime]
  split_ifs with h
  · rfl
  · exact absurd h (by norm_num)

/-- `κ = 0.01` is thin. -/
example (D : ℝ) : twoRegime 10 50 36 (1 / 100) (1 / 10000) (1 / 1000) D =
    50 * ((1 / 1000) / (D + √(1 / 1000))) := by
  rw [twoRegime]
  split_ifs with h
  · exact absurd h (by norm_num)
  · rfl

/-- `twoRegime_mono` at a mixed pair: `z` thin (`K₀ d = 0.036 ≥ κ + η = 0.0101`), `z + iN⁻⁵`
thick (`K₀ d' = 0.009 < κ + η' = 0.0102`). -/
example : twoRegime 10 50 36 (1 / 100) (2 / 10000) (1 / 4000) √(1 / 100 + 2 / 10000) ≤
    twoRegime 10 50 36 (1 / 100) (1 / 10000) (1 / 1000) √(1 / 100 + 1 / 10000) :=
  twoRegime_mono (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- `twoRegime_le` at the thick instance. -/
example : twoRegime 10 50 36 (1 / 10) (1 / 10000) (1 / 1000) √(1 / 10 + 1 / 10000) ≤
    50 * ((1 / 1000) / (√(1 / 10 + 1 / 10000) + √(1 / 1000))) :=
  twoRegime_le (by norm_num) (by norm_num) (Real.sqrt_nonneg _)

/-- `im_resolventTransform_pos` at `μ = δ₀`, `z = i`. -/
example : 0 < (resolventTransform (Measure.dirac (0 : ℝ)) Complex.I : ℂ).im :=
  im_resolventTransform_pos _ (by simp)

/-- `norm_resolventTransform_sub_le` at `μ = δ₀`, `z = i`, `w = 2i`: equality `1/2 ≤ 1/2`. -/
example : ‖(resolventTransform (Measure.dirac (0 : ℝ)) Complex.I : ℂ) -
    resolventTransform (Measure.dirac (0 : ℝ)) (2 * Complex.I)‖ ≤
    ‖Complex.I - 2 * Complex.I‖ / (Complex.I.im * (2 * Complex.I).im) :=
  norm_resolventTransform_sub_le _ (by simp) (by simp)

/-- `norm_sub_mFun_le_of_im_ge` for the Marchenko–Pastur parameters `M = 1`, `N = 2`, `σ = 1`
with `h = 1/2`, `u = i`, `z = 3/8 + 3i/4`: `f(i) = 1/4 + 3i/4`, `‖f(i) - z‖ = 1/8 ≤ h/2`. -/
example :
    ‖Complex.I - mFun 2 (fun _ : Fin 1 => (1 : ℝ)) (⟨3 / 8, 3 / 4⟩ : ℂ)‖ ≤
      2 * ‖fC 2 (fun _ : Fin 1 => (1 : ℝ)) Complex.I - ⟨3 / 8, 3 / 4⟩‖ / (1 / 2 : ℝ) ^ 2 := by
  have hf : fC 2 (fun _ : Fin 1 => (1 : ℝ)) Complex.I = ⟨1 / 4, 3 / 4⟩ := by
    have hn : Complex.normSq (1 + Complex.I) = 2 := by
      simp [Complex.normSq_apply]; norm_num
    apply Complex.ext <;> simp [fC, hn] <;> norm_num
  refine norm_sub_mFun_le_of_im_ge (fun _ => by norm_num) (by norm_num) (by norm_num)
    (z := (⟨3 / 8, 3 / 4⟩ : ℂ)) (by simp; norm_num) (by simp) ?_
  rw [hf]
  have : ((⟨1 / 4, 3 / 4⟩ : ℂ) - ⟨3 / 8, 3 / 4⟩) = ((-1 / 8 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp <;> norm_num
  rw [this, Complex.norm_real]
  norm_num

end Anisotropic
