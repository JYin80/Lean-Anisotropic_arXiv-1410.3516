module

public import Anisotropic.Density.Count
public import Anisotropic.Density.Critical
public import Anisotropic.Density.Stability.EdgeTools
public import Anisotropic.Endpoints.Main
public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.Framework.Domination
public import Anisotropic.Framework.Model
public import Anisotropic.Probability.NormBound.Main
public import Anisotropic.Rigidity.Defs
public import Anisotropic.Rigidity.EdgeLow
public import Anisotropic.Rigidity.Exclusion
public import Anisotropic.Rigidity.GaussCount
public import Anisotropic.Rigidity.Segment

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # `|n_N(E) − n(E)| ≺ 1`: `count_edgeWin`, `count_edge`, `count_bulk` -/

/-! ## Deterministic estimates for the Stieltjes transforms -/

private lemma cnt_sub_ne {z : ℂ} (hz : 0 < z.im) (x : ℝ) : (x : ℂ) - z ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

private lemma cnt_im_le_norm (z : ℂ) (x : ℝ) : z.im ≤ ‖(x : ℂ) - z‖ := by
  have h := Complex.abs_im_le_norm ((x : ℂ) - z)
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] at h
  exact (le_abs_self _).trans h

/-- `|(x − z)⁻¹ − (x − w)⁻¹| ≤ |z − w| / (Im z Im w)`. -/
private lemma cnt_inv_sub_le {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) (x : ℝ) :
    ‖((x : ℂ) - z)⁻¹ - ((x : ℂ) - w)⁻¹‖ ≤ ‖z - w‖ / (z.im * w.im) := by
  have hz0 := cnt_sub_ne hz x
  have hw0 := cnt_sub_ne hw x
  have e : ((x : ℂ) - z)⁻¹ - ((x : ℂ) - w)⁻¹ = (z - w) / (((x : ℂ) - z) * ((x : ℂ) - w)) := by
    field_simp
    ring
  rw [e, norm_div, norm_mul]
  apply div_le_div_of_nonneg_left (norm_nonneg _) (mul_pos hz hw)
  exact mul_le_mul (cnt_im_le_norm z x) (cnt_im_le_norm w x) hw.le (norm_nonneg _)

/-- `|s(z) − s(w)| ≤ |z − w| / (Im z Im w)` for the empirical Stieltjes transform. -/
private lemma cnt_emp_lip {K : ℕ} (lam : Fin K → ℝ) {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    ‖empStieltjes lam z - empStieltjes lam w‖ ≤ ‖z - w‖ / (z.im * w.im) := by
  have hq : 0 ≤ ‖z - w‖ / (z.im * w.im) := by positivity
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simpa [empStieltjes] using hq
  unfold empStieltjes
  rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul, norm_inv, Complex.norm_natCast]
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hsum : ‖∑ j, (((lam j : ℂ) - z)⁻¹ - ((lam j : ℂ) - w)⁻¹)‖ ≤
      K * (‖z - w‖ / (z.im * w.im)) := by
    refine (norm_sum_le _ _).trans ?_
    have := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => cnt_inv_sub_le hz hw (lam j)
    simpa using this
  calc (K : ℝ)⁻¹ * ‖∑ j, (((lam j : ℂ) - z)⁻¹ - ((lam j : ℂ) - w)⁻¹)‖
      ≤ (K : ℝ)⁻¹ * (K * (‖z - w‖ / (z.im * w.im))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ‖z - w‖ / (z.im * w.im) := by field_simp

/-- `|m(z) − m(w)| ≤ |z − w| / (Im z Im w)`. -/
private lemma cnt_m_lip (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    ‖mFun N σ z - mFun N σ w‖ ≤ ‖z - w‖ / (z.im * w.im) := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  have h := norm_resolventTransform_sub_le (varrho N σ) hz hw
  rwa [resolventTransform_varrho N σ hσ hN hz, resolventTransform_varrho N σ hσ hN hw] at h

/-- `s` is continuous on `ℂ₊`. -/
private lemma cnt_cont_emp {K : ℕ} (lam : Fin K → ℝ) :
    ContinuousOn (empStieltjes lam) {z : ℂ | 0 < z.im} := by
  unfold empStieltjes
  refine continuousOn_const.mul (continuousOn_finsetSum _ fun j _ => ?_)
  exact ((continuous_const.sub continuous_id).continuousOn).inv₀ fun z hz => cnt_sub_ne hz _

/-- Along a horizontal line `x ↦ x + iy`, `y > 0`, a function continuous on `ℂ₊` is
continuous. -/
private lemma cnt_cont_hor {f : ℂ → ℂ} (hf : ContinuousOn f {z : ℂ | 0 < z.im}) {y : ℝ}
    (hy : 0 < y) : Continuous fun x : ℝ => f (↑x + ↑y * Complex.I) :=
  hf.comp_continuous (by fun_prop) fun x => by simpa using hy

/-- Along a vertical segment `y ↦ E + iy`, `y ∈ [η, η₀]`, `η > 0`, a function continuous on
`ℂ₊` is continuous. -/
private lemma cnt_cont_ver {f : ℂ → ℂ} (hf : ContinuousOn f {z : ℂ | 0 < z.im}) (E : ℝ)
    {η η₀ : ℝ} (hη : 0 < η) (hηη₀ : η ≤ η₀) :
    ContinuousOn (fun y : ℝ => f (↑E + ↑y * Complex.I)) (Set.uIcc η η₀) := by
  refine hf.comp (by fun_prop) fun y hy => ?_
  rw [Set.uIcc_of_le hηη₀] at hy
  simpa using lt_of_lt_of_le hη hy.1

/-- On `ℂ₊`, `m(z) = ∫ (t − z)⁻¹ dϱ(t)`. -/
private lemma cnt_m_eq_integral (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {z : ℂ}
    (hz : 0 < z.im) : mFun N σ z = ∫ t : ℝ, ((t : ℂ) - z)⁻¹ ∂(varrho N σ) := by
  rw [← resolventTransform_varrho N σ hσ hN hz, resolventTransform_apply]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp [resolvent, Ring.inverse_eq_inv']

private lemma cnt_integrable_inv (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {z : ℂ}
    (hz : 0 < z.im) : Integrable (fun t : ℝ => ((t : ℂ) - z)⁻¹) (varrho N σ) := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  refine Integrable.of_bound ?_ (z.im)⁻¹ (ae_of_all _ fun t => ?_)
  · exact ((Complex.continuous_ofReal.sub continuous_const).inv₀
      (cnt_sub_ne hz)).aestronglyMeasurable
  · rw [norm_inv]
    exact inv_anti₀ hz (cnt_im_le_norm z t)

private lemma cnt_inv_im (t x y : ℝ) :
    (((t : ℂ) - (↑x + ↑y * Complex.I))⁻¹).im = y / ((t - x) ^ 2 + y ^ 2) := by
  rw [Complex.inv_im, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.add_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, Complex.sub_im, Complex.add_im, Complex.mul_im]
  ring

/-- `Im m(x + iy) = ∫ y / ((t − x)² + y²) dϱ(t)` for `y > 0`. -/
private lemma cnt_im_m (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) (x : ℝ) {y : ℝ}
    (hy : 0 < y) :
    (mFun N σ (↑x + ↑y * Complex.I)).im = ∫ t, y / ((t - x) ^ 2 + y ^ 2) ∂(varrho N σ) := by
  have hz : 0 < ((x : ℂ) + ↑y * Complex.I).im := by simpa using hy
  rw [cnt_m_eq_integral σ hσ hN hz]
  have := integral_im (𝕜 := ℂ) (cnt_integrable_inv σ hσ hN hz)
  simp only [RCLike.im_to_complex] at this
  rw [← this]
  simp_rw [cnt_inv_im]

/-- `ϱ([c − δ, c + δ]) ≤ 2δ Im m(c + iδ)`. -/
private lemma cnt_varrho_Icc_le (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) (c : ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    (varrho N σ).real (Set.Icc (c - δ) (c + δ)) ≤
      2 * δ * (mFun N σ (↑c + ↑δ * Complex.I)).im := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  rw [cnt_im_m σ hσ hN c hδ]
  have hint : Integrable (fun t : ℝ => δ / ((t - c) ^ 2 + δ ^ 2)) (varrho N σ) := by
    refine Integrable.of_bound ?_ (1 / δ) (ae_of_all _ fun t => ?_)
    · exact (continuous_const.div (by fun_prop) fun t => by positivity).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_le_div_iff₀ (by positivity) hδ]
      nlinarith [sq_nonneg (t - c)]
  have hm := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun t => by positivity) hint
    (1 / (2 * δ))
  have hsub : Set.Icc (c - δ) (c + δ) ⊆
      {t | 1 / (2 * δ) ≤ δ / ((t - c) ^ 2 + δ ^ 2)} := by
    intro t ht
    simp only [Set.mem_ofPred_eq]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (t - c) ^ 2 ≤ δ ^ 2 := by
      have : |t - c| ≤ δ := abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩
      nlinarith [abs_nonneg (t - c), sq_abs (t - c)]
    nlinarith
  have h2 := measureReal_mono (μ := varrho N σ) hsub
  have h3 : (1 / (2 * δ)) * (varrho N σ).real (Set.Icc (c - δ) (c + δ)) ≤
      ∫ t, δ / ((t - c) ^ 2 + δ ^ 2) ∂(varrho N σ) :=
    (mul_le_mul_of_nonneg_left h2 (by positivity)).trans hm
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)] at h3
  linarith

/-- `n` is nonincreasing and nonnegative. -/
private lemma cnt_nClass_anti (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {E E' : ℝ}
    (h : E ≤ E') : nClass N σ E' ≤ nClass N σ E := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  unfold nClass
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg N)
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Ici_subset_Ici.2 h))

private lemma cnt_nClass_nonneg (σ : Fin M → ℝ) (E : ℝ) : 0 ≤ nClass N σ E := by
  unfold nClass
  positivity

/-- `n(E) − n(E') ≤ N ϱ([E, E'])`. -/
private lemma cnt_nClass_sub_le (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) (E E' : ℝ) :
    nClass N σ E - nClass N σ E' ≤ N * (varrho N σ).real (Set.Icc E E') := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  unfold nClass
  have h : varrho N σ (Set.Ici E) ≤ varrho N σ (Set.Icc E E') + varrho N σ (Set.Ici E') := by
    refine (measure_mono fun t ht => ?_).trans (measure_union_le _ _)
    by_cases htE : t ≤ E'
    · exact Or.inl ⟨ht, htE⟩
    · exact Or.inr (le_of_lt (not_le.1 htE))
  have h2 := ENNReal.toReal_mono (by finiteness) h
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at h2
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [Measure.real]
  nlinarith

private lemma cnt_integrable_decay (μ : Measure ℝ) [IsFiniteMeasure μ] (E η : ℝ) (hη : 0 < η) :
    Integrable (fun x : ℝ => η / (|x - E| + η)) μ := by
  refine Integrable.of_bound ?_ 1 (ae_of_all _ fun t => ?_)
  · exact (continuous_const.div (by fun_prop) fun t => by positivity).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_le_one (by positivity)]
    linarith [abs_nonneg (t - E)]

/-- The counting comparison with `s − m` controlled on the two vertical segments `E_i + iy`,
`y ∈ [η, 1]`, and on the top segment `[E₁, E₂] + i`, and `|m| ≤ C_m` on the vertical
segments. -/
private lemma cnt_core (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) (lam : Fin N → ℝ)
    {E₁ E₂ η B Cm : ℝ} (L : ℕ) (hη : 0 < η) (hL : 2 ^ L * η ≤ 1) (hB : 0 ≤ B)
    (h12 : E₁ ≤ E₂) (hE₁ : 0 < E₁)
    (hline : ∀ E, (E = E₁ ∨ E = E₂) → ∀ y ∈ Set.Icc η 1,
      ‖empStieltjes lam (↑E + ↑y * Complex.I) - mFun N σ (↑E + ↑y * Complex.I)‖ ≤ B / (N * y) ∧
        ‖mFun N σ (↑E + ↑y * Complex.I)‖ ≤ Cm)
    (htop : ∀ x ∈ Set.Icc E₁ E₂,
      ‖empStieltjes lam (↑x + ↑(1 : ℝ) * Complex.I) - mFun N σ (↑x + ↑(1 : ℝ) * Complex.I)‖ ≤
        B / N) :
    |((Finset.univ.filter fun j => E₁ ≤ lam j).card : ℝ) -
        (Finset.univ.filter fun j => E₂ ≤ lam j).card - (nClass N σ E₁ - nClass N σ E₂)| ≤
      B * (E₂ - E₁ + 2 * Real.log (1 / η) + 48) + 40 * N * η * (L + 1) * Cm +
        10 * N / 2 ^ L := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h2L : (1 : ℝ) ≤ 2 ^ L := one_le_pow₀ (by norm_num)
  have hη1 : η ≤ 1 := by nlinarith
  have hpi := Real.pi_gt_three
  have hlog : 0 ≤ Real.log (1 / η) := Real.log_nonneg (by rw [le_div_iff₀ hη]; linarith)
  have hCm : 0 ≤ Cm := (norm_nonneg _).trans (hline E₁ (Or.inl rfl) η ⟨le_rfl, hη1⟩).2
  have hS := cnt_cont_emp lam
  have hM : ContinuousOn (mFun N σ) {z : ℂ | 0 < z.im} :=
    (analyticOnNhd_mFun N σ hσ).continuousOn
  -- the integral term
  have hT1 : N * |∫ x in E₁..E₂,
      (empStieltjes lam (↑x + ↑η * Complex.I) - mFun N σ (↑x + ↑η * Complex.I)).im| /
        Real.pi ≤ B * (E₂ - E₁ + 2 * Real.log (1 / η)) := by
    have iS : ∀ y : ℝ, 0 < y → IntervalIntegrable
        (fun x : ℝ => (empStieltjes lam (↑x + ↑y * Complex.I)).im) volume E₁ E₂ :=
      fun y hy => (Complex.continuous_im.comp (cnt_cont_hor hS hy)).intervalIntegrable _ _
    have iM : ∀ y : ℝ, 0 < y → IntervalIntegrable
        (fun x : ℝ => (mFun N σ (↑x + ↑y * Complex.I)).im) volume E₁ E₂ :=
      fun y hy => (Complex.continuous_im.comp (cnt_cont_hor hM hy)).intervalIntegrable _ _
    have rS : ∀ E : ℝ, IntervalIntegrable
        (fun y : ℝ => (empStieltjes lam (↑E + ↑y * Complex.I)).re) volume η 1 :=
      fun E => (Complex.continuous_re.comp_continuousOn
        (cnt_cont_ver hS E hη hη1)).intervalIntegrable
    have rM : ∀ E : ℝ, IntervalIntegrable
        (fun y : ℝ => (mFun N σ (↑E + ↑y * Complex.I)).re) volume η 1 :=
      fun E => (Complex.continuous_re.comp_continuousOn
        (cnt_cont_ver hM E hη hη1)).intervalIntegrable
    have hId : ∫ x in E₁..E₂,
        (empStieltjes lam (↑x + ↑η * Complex.I) - mFun N σ (↑x + ↑η * Complex.I)).im =
        (∫ x in E₁..E₂, (empStieltjes lam (↑x + ↑(1 : ℝ) * Complex.I) -
            mFun N σ (↑x + ↑(1 : ℝ) * Complex.I)).im) -
          ((∫ y in η..1, (empStieltjes lam (↑E₂ + ↑y * Complex.I) -
              mFun N σ (↑E₂ + ↑y * Complex.I)).re) -
            ∫ y in η..1, (empStieltjes lam (↑E₁ + ↑y * Complex.I) -
              mFun N σ (↑E₁ + ↑y * Complex.I)).re) := by
      simp only [Complex.sub_im, Complex.sub_re]
      rw [intervalIntegral.integral_sub (iS η hη) (iM η hη),
        intervalIntegral.integral_sub (iS 1 one_pos) (iM 1 one_pos),
        intervalIntegral.integral_sub (rS E₂) (rM E₂),
        intervalIntegral.integral_sub (rS E₁) (rM E₁),
        segment_identity lam E₁ E₂ η 1 hη hη1, segment_identity_m σ hσ hN E₁ E₂ η 1 hη hη1,
        intervalIntegral.integral_sub (rS E₂) (rS E₁),
        intervalIntegral.integral_sub (rM E₂) (rM E₁)]
      ring
    have hb1 : |∫ x in E₁..E₂, (empStieltjes lam (↑x + ↑(1 : ℝ) * Complex.I) -
        mFun N σ (↑x + ↑(1 : ℝ) * Complex.I)).im| ≤ B / N * (E₂ - E₁) := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := E₁) (b := E₂) (C := B / N)
        (f := fun x : ℝ => (empStieltjes lam (↑x + ↑(1 : ℝ) * Complex.I) -
          mFun N σ (↑x + ↑(1 : ℝ) * Complex.I)).im) (fun x hx => by
            rw [Set.uIoc_of_le h12] at hx
            exact (Real.norm_eq_abs _ ▸ Complex.abs_im_le_norm _).trans
              (htop x ⟨hx.1.le, hx.2⟩))
      rwa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 h12)] at this
    have hb2 : ∀ E, (E = E₁ ∨ E = E₂) → |∫ y in η..1, (empStieltjes lam (↑E + ↑y * Complex.I) -
        mFun N σ (↑E + ↑y * Complex.I)).re| ≤ B / N * Real.log (1 / η) := by
      intro E hE
      have hg : IntervalIntegrable (fun y : ℝ => B / N * y⁻¹) volume η 1 := by
        refine (continuousOn_const.mul (continuousOn_inv₀.mono fun y hy => ?_)).intervalIntegrable
        rw [Set.uIcc_of_le hη1] at hy
        exact (lt_of_lt_of_le hη hy.1).ne'
      have := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
        (f := fun y : ℝ => (empStieltjes lam (↑E + ↑y * Complex.I) -
          mFun N σ (↑E + ↑y * Complex.I)).re) hη1 (ae_of_all _ fun y hy => by
        have hy0 : 0 < y := lt_trans hη hy.1
        refine (Real.norm_eq_abs _ ▸ Complex.abs_re_le_norm _).trans ?_
        refine ((hline E hE y ⟨hy.1.le, hy.2⟩).1).trans (le_of_eq ?_)
        field_simp) hg
      rwa [Real.norm_eq_abs, intervalIntegral.integral_const_mul,
        integral_inv_of_pos hη one_pos] at this
    rw [hId]
    have hsum : |(∫ x in E₁..E₂, (empStieltjes lam (↑x + ↑(1 : ℝ) * Complex.I) -
            mFun N σ (↑x + ↑(1 : ℝ) * Complex.I)).im) -
          ((∫ y in η..1, (empStieltjes lam (↑E₂ + ↑y * Complex.I) -
              mFun N σ (↑E₂ + ↑y * Complex.I)).re) -
            ∫ y in η..1, (empStieltjes lam (↑E₁ + ↑y * Complex.I) -
              mFun N σ (↑E₁ + ↑y * Complex.I)).re)| ≤
        B / N * (E₂ - E₁) + 2 * (B / N * Real.log (1 / η)) := by
      have h1 := hb2 E₁ (Or.inl rfl)
      have h2 := hb2 E₂ (Or.inr rfl)
      refine (abs_sub _ _).trans ?_
      have := abs_sub (∫ y in η..1, (empStieltjes lam (↑E₂ + ↑y * Complex.I) -
              mFun N σ (↑E₂ + ↑y * Complex.I)).re)
            (∫ y in η..1, (empStieltjes lam (↑E₁ + ↑y * Complex.I) -
              mFun N σ (↑E₁ + ↑y * Complex.I)).re)
      linarith
    have hX : 0 ≤ B / N * (E₂ - E₁) + 2 * (B / N * Real.log (1 / η)) := by
      have : 0 ≤ E₂ - E₁ := sub_nonneg.2 h12
      positivity
    calc (N : ℝ) * |_| / Real.pi
        ≤ N * (B / N * (E₂ - E₁) + 2 * (B / N * Real.log (1 / η))) / 1 := by
          gcongr
          linarith
      _ = B * (E₂ - E₁ + 2 * Real.log (1 / η)) := by field_simp
  -- the smoothing of the eigenvalues
  have hT2 : ∀ E, (E = E₁ ∨ E = E₂) → ∑ j, η / (|lam j - E| + η) ≤
      4 * N * η * (L + 1) * Cm + 8 * B + N / 2 ^ L := by
    intro E hE
    have h := smooth_sum_le lam E η hη L
    have hl : ∀ l ∈ Finset.range (L + 1),
        (empStieltjes lam (↑E + ↑(2 ^ l * η) * Complex.I)).im ≤
          Cm + B / (N * η) * (1 / 2) ^ l := by
      intro l hl
      have hlL : l ≤ L := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
      have h2l : (1 : ℝ) ≤ 2 ^ l := one_le_pow₀ (by norm_num)
      have h2lL : (2 : ℝ) ^ l ≤ 2 ^ L := pow_le_pow_right₀ (by norm_num) hlL
      have hyl : 2 ^ l * η ∈ Set.Icc η 1 := ⟨by nlinarith, by nlinarith⟩
      obtain ⟨h1, h2⟩ := hline E hE _ hyl
      have he : (empStieltjes lam (↑E + ↑(2 ^ l * η) * Complex.I)).im =
          (empStieltjes lam (↑E + ↑(2 ^ l * η) * Complex.I) -
            mFun N σ (↑E + ↑(2 ^ l * η) * Complex.I)).im +
          (mFun N σ (↑E + ↑(2 ^ l * η) * Complex.I)).im := by
        rw [Complex.sub_im]; ring
      have hq : B / (N * (2 ^ l * η)) = B / (N * η) * (1 / 2) ^ l := by
        rw [_root_.one_div_pow]
        field_simp
      rw [he]
      have := Complex.im_le_norm (empStieltjes lam (↑E + ↑(2 ^ l * η) * Complex.I) -
            mFun N σ (↑E + ↑(2 ^ l * η) * Complex.I))
      have := Complex.im_le_norm (mFun N σ (↑E + ↑(2 ^ l * η) * Complex.I))
      linarith
    have hsum : ∑ l ∈ Finset.range (L + 1),
        (empStieltjes lam (↑E + ↑(2 ^ l * η) * Complex.I)).im ≤
          (L + 1) * Cm + B / (N * η) * 2 := by
      refine (Finset.sum_le_sum hl).trans ?_
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
      push_cast
      have := sum_geometric_two_le (L + 1)
      have : 0 ≤ B / (N * η) := by positivity
      nlinarith
    calc ∑ j, η / (|lam j - E| + η)
        ≤ 4 * N * η * ∑ l ∈ Finset.range (L + 1),
            (empStieltjes lam (↑E + ↑(2 ^ l * η) * Complex.I)).im + N / 2 ^ L := h
      _ ≤ 4 * N * η * ((L + 1) * Cm + B / (N * η) * 2) + N / 2 ^ L := by gcongr
      _ = 4 * N * η * (L + 1) * Cm + 8 * B + N / 2 ^ L := by field_simp; ring
  -- the smoothing of `ϱ`
  have hT3 : ∀ E, (E = E₁ ∨ E = E₂) → ∫ x, η / (|x - E| + η) ∂(varrho N σ) ≤
      4 * η * (L + 1) * Cm + 1 / 2 ^ L := by
    intro E hE
    have h := smooth_int_le σ hσ hN E η hη L
    have hl : ∀ l ∈ Finset.range (L + 1), (mFun N σ (↑E + ↑(2 ^ l * η) * Complex.I)).im ≤ Cm := by
      intro l hl
      have hlL : l ≤ L := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
      have h2l : (1 : ℝ) ≤ 2 ^ l := one_le_pow₀ (by norm_num)
      have h2lL : (2 : ℝ) ^ l ≤ 2 ^ L := pow_le_pow_right₀ (by norm_num) hlL
      have hyl : 2 ^ l * η ∈ Set.Icc η 1 := ⟨by nlinarith, by nlinarith⟩
      exact (Complex.im_le_norm _).trans (hline E hE _ hyl).2
    have hsum := Finset.sum_le_sum hl
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hsum
    calc ∫ x, η / (|x - E| + η) ∂(varrho N σ)
        ≤ 4 * η * ∑ l ∈ Finset.range (L + 1), (mFun N σ (↑E + ↑(2 ^ l * η) * Complex.I)).im +
            1 / 2 ^ L := h
      _ ≤ 4 * η * ((L + 1) * Cm) + 1 / 2 ^ L := by
          have := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ 4 * η)
          linarith
      _ = 4 * η * (L + 1) * Cm + 1 / 2 ^ L := by ring
  have hcc := count_compare σ hσ hN lam hη h12 hE₁
  have := isProbabilityMeasure_varrho N σ hσ hN
  rw [Finset.sum_add_distrib, integral_add (cnt_integrable_decay _ E₁ η hη)
    (cnt_integrable_decay _ E₂ η hη)] at hcc
  have a1 := hT2 E₁ (Or.inl rfl)
  have a2 := hT2 E₂ (Or.inr rfl)
  have b1 := hT3 E₁ (Or.inl rfl)
  have b2 := hT3 E₂ (Or.inr rfl)
  have hN0 : (0 : ℝ) ≤ N := hNr.le
  have hb1' := mul_le_mul_of_nonneg_left b1 hN0
  have hb2' := mul_le_mul_of_nonneg_left b2 hN0
  refine hcc.trans ?_
  calc _ ≤ B * (E₂ - E₁ + 2 * Real.log (1 / η)) +
        3 * ((4 * N * η * (L + 1) * Cm + 8 * B + N / 2 ^ L) +
          (4 * N * η * (L + 1) * Cm + 8 * B + N / 2 ^ L)) +
        2 * (N * (4 * η * (L + 1) * Cm + 1 / 2 ^ L) + N * (4 * η * (L + 1) * Cm + 1 / 2 ^ L)) := by
        have e : 2 * (N : ℝ) * (∫ x, η / (|x - E₁| + η) ∂(varrho N σ) +
            ∫ x, η / (|x - E₂| + η) ∂(varrho N σ)) =
            2 * (N * ∫ x, η / (|x - E₁| + η) ∂(varrho N σ) +
              N * ∫ x, η / (|x - E₂| + η) ∂(varrho N σ)) := by ring
        rw [e]
        refine add_le_add (add_le_add hT1 ?_) ?_
        · linarith
        · linarith
    _ = B * (E₂ - E₁ + 2 * Real.log (1 / η) + 48) + 40 * N * η * (L + 1) * Cm +
        10 * N / 2 ^ L := by ring

/-! ## Grids -/

/-- Transfer along a vertical segment from the grid `j/N⁴` to all heights `y ∈ [η, 1]`. -/
private lemma cnt_line_transfer (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 2 ≤ N)
    (lam : Fin N → ℝ) (e : ℝ) {η A : ℝ} (hη0 : 0 < η) (hη : 2 / (N : ℝ) ^ 3 ≤ η) (hA : 0 ≤ A)
    (hgrid : ∀ j : ℕ, j ∈ Finset.Icc 1 (2 * N ^ 4) → η ≤ (j : ℝ) / N ^ 4 →
      ‖empStieltjes lam (↑e + ↑((j : ℝ) / N ^ 4) * Complex.I) -
          mFun N σ (↑e + ↑((j : ℝ) / N ^ 4) * Complex.I)‖ ≤ A * (1 / (N * ((j : ℝ) / N ^ 4)))) :
    ∀ y ∈ Set.Icc η 1, ‖empStieltjes lam (↑e + ↑y * Complex.I) -
      mFun N σ (↑e + ↑y * Complex.I)‖ ≤ (A + 1) / (N * y) := by
  intro y hy
  have hN0 : 0 < N := by omega
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN4 : (0 : ℝ) < (N : ℝ) ^ 4 := by positivity
  have hy0 : 0 < y := lt_of_lt_of_le hη0 hy.1
  set j := ⌈y * (N : ℝ) ^ 4⌉₊ with hj
  have hj1 : y * (N : ℝ) ^ 4 ≤ j := Nat.le_ceil _
  have hj2 : (j : ℝ) < y * (N : ℝ) ^ 4 + 1 := Nat.ceil_lt_add_one (by positivity)
  set y' := (j : ℝ) / N ^ 4 with hy'
  have hyy' : y ≤ y' := by rw [hy', le_div_iff₀ hN4]; exact hj1
  have hy'y : y' - y ≤ 1 / (N : ℝ) ^ 4 := by
    rw [hy', div_sub' (by positivity), div_le_div_iff_of_pos_right hN4]
    linarith
  have hjpos : 1 ≤ j := Nat.one_le_iff_ne_zero.2 (by
    intro h0
    rw [h0] at hj1
    simp at hj1
    nlinarith)
  have hjle : j ≤ 2 * N ^ 4 := by
    have : (j : ℝ) < (N : ℝ) ^ 4 + 1 := by nlinarith [hy.2]
    have h' : j < N ^ 4 + 1 := by exact_mod_cast this
    have : 1 ≤ N ^ 4 := Nat.one_le_pow _ _ hN0
    omega
  have hy'0 : 0 < y' := lt_of_lt_of_le hy0 hyy'
  have hg : ‖empStieltjes lam (↑e + ↑y' * Complex.I) - mFun N σ (↑e + ↑y' * Complex.I)‖ ≤
      A * (1 / (N * y')) := hgrid j (Finset.mem_Icc.2 ⟨hjpos, hjle⟩) (hy.1.trans hyy')
  have hz : 0 < ((e : ℂ) + ↑y * Complex.I).im := by simpa using hy0
  have hz' : 0 < ((e : ℂ) + ↑y' * Complex.I).im := by simpa using hy'0
  have hs := cnt_emp_lip lam hz hz'
  have hm := cnt_m_lip σ hσ hN0 hz hz'
  have hdist : ‖((e : ℂ) + ↑y * Complex.I) - (↑e + ↑y' * Complex.I)‖ = y' - y := by
    have : ((e : ℂ) + ↑y * Complex.I) - (↑e + ↑y' * Complex.I) =
        ((y - y' : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    ring
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, mul_zero, zero_add, mul_one, add_zero] at hs hm
  rw [hdist] at hs hm
  have htri : ‖empStieltjes lam (↑e + ↑y * Complex.I) - mFun N σ (↑e + ↑y * Complex.I)‖ ≤
      ‖empStieltjes lam (↑e + ↑y' * Complex.I) - mFun N σ (↑e + ↑y' * Complex.I)‖ +
        ‖empStieltjes lam (↑e + ↑y * Complex.I) - empStieltjes lam (↑e + ↑y' * Complex.I)‖ +
        ‖mFun N σ (↑e + ↑y * Complex.I) - mFun N σ (↑e + ↑y' * Complex.I)‖ := by
    have := norm_add₃_le
      (a := empStieltjes lam (↑e + ↑y' * Complex.I) - mFun N σ (↑e + ↑y' * Complex.I))
      (b := empStieltjes lam (↑e + ↑y * Complex.I) - empStieltjes lam (↑e + ↑y' * Complex.I))
      (c := -(mFun N σ (↑e + ↑y * Complex.I) - mFun N σ (↑e + ↑y' * Complex.I)))
    rw [norm_neg] at this
    convert this using 2
    ring
  -- the three terms
  have h1 : A * (1 / (N * y')) ≤ A / (N * y) := by
    rw [mul_one_div]
    exact div_le_div_of_nonneg_left hA (by positivity) (by gcongr)
  have h2 : (y' - y) / (y * y') ≤ 1 / (2 * (N * y)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hy'η : η ≤ y' := hy.1.trans hyy'
    -- `(y' − y) · 2N y ≤ (2/N⁴) N y ≤ η y ≤ y y'`
    have k1 : (y' - y) * (2 * (N * y)) ≤ 1 / (N : ℝ) ^ 4 * (2 * (N * y)) :=
      mul_le_mul_of_nonneg_right hy'y (by positivity)
    have k2 : 1 / (N : ℝ) ^ 4 * (2 * (N * y)) = 2 / (N : ℝ) ^ 3 * y := by
      field_simp
    have k3 : 2 / (N : ℝ) ^ 3 * y ≤ y * y' := by nlinarith
    linarith
  have hfin : A / (N * y) + 1 / (2 * (N * y)) + 1 / (2 * (N * y)) = (A + 1) / (N * y) := by
    field_simp
    ring
  linarith

/-- Transfer along the top segment `x + i` from the grid `j/N²` to all `x ∈ [0, X]`. -/
private lemma cnt_top_transfer (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 2 ≤ N)
    (lam : Fin N → ℝ) {X A : ℝ}
    (hgrid : ∀ j : ℕ, j ∈ Finset.range (⌈X * (N : ℝ) ^ 2⌉₊ + 2) →
      ‖empStieltjes lam (↑((j : ℝ) / N ^ 2) + ↑(1 : ℝ) * Complex.I) -
          mFun N σ (↑((j : ℝ) / N ^ 2) + ↑(1 : ℝ) * Complex.I)‖ ≤ A * (1 / (N * 1))) :
    ∀ x ∈ Set.Icc 0 X, ‖empStieltjes lam (↑x + ↑(1 : ℝ) * Complex.I) -
      mFun N σ (↑x + ↑(1 : ℝ) * Complex.I)‖ ≤ (A + 1) / N := by
  intro x hx
  have hN0 : 0 < N := by omega
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  set j := ⌈x * (N : ℝ) ^ 2⌉₊ with hj
  have hj1 : x * (N : ℝ) ^ 2 ≤ j := Nat.le_ceil _
  have hj2 : (j : ℝ) < x * (N : ℝ) ^ 2 + 1 := Nat.ceil_lt_add_one (by nlinarith [hx.1])
  have hjK : j < ⌈X * (N : ℝ) ^ 2⌉₊ + 2 := by
    have : j ≤ ⌈X * (N : ℝ) ^ 2⌉₊ := Nat.ceil_mono (by nlinarith [hx.2])
    omega
  set x' := (j : ℝ) / N ^ 2 with hx'
  have hxx' : x ≤ x' := by rw [hx', le_div_iff₀ hN2]; exact hj1
  have hx'x : x' - x ≤ 1 / (N : ℝ) ^ 2 := by
    rw [hx', div_sub' (by positivity), div_le_div_iff_of_pos_right hN2]
    linarith
  have hg : ‖empStieltjes lam (↑x' + ↑(1 : ℝ) * Complex.I) -
      mFun N σ (↑x' + ↑(1 : ℝ) * Complex.I)‖ ≤ A * (1 / (N * 1)) :=
    hgrid j (Finset.mem_range.2 hjK)
  have hz : 0 < ((x : ℂ) + ↑(1 : ℝ) * Complex.I).im := by simp
  have hz' : 0 < ((x' : ℂ) + ↑(1 : ℝ) * Complex.I).im := by simp
  have hs := cnt_emp_lip lam hz hz'
  have hm := cnt_m_lip σ hσ hN0 hz hz'
  have hdist : ‖((x : ℂ) + ↑(1 : ℝ) * Complex.I) - (↑x' + ↑(1 : ℝ) * Complex.I)‖ = x' - x := by
    have : ((x : ℂ) + ↑(1 : ℝ) * Complex.I) - (↑x' + ↑(1 : ℝ) * Complex.I) =
        ((x - x' : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, mul_zero, zero_add, mul_one, add_zero] at hs hm
  rw [hdist] at hs hm
  have htri : ‖empStieltjes lam (↑x + ↑(1 : ℝ) * Complex.I) -
      mFun N σ (↑x + ↑(1 : ℝ) * Complex.I)‖ ≤
      ‖empStieltjes lam (↑x' + ↑(1 : ℝ) * Complex.I) - mFun N σ (↑x' + ↑(1 : ℝ) * Complex.I)‖ +
        ‖empStieltjes lam (↑x + ↑(1 : ℝ) * Complex.I) -
          empStieltjes lam (↑x' + ↑(1 : ℝ) * Complex.I)‖ +
        ‖mFun N σ (↑x + ↑(1 : ℝ) * Complex.I) - mFun N σ (↑x' + ↑(1 : ℝ) * Complex.I)‖ := by
    have := norm_add₃_le
      (a := empStieltjes lam (↑x' + ↑(1 : ℝ) * Complex.I) - mFun N σ (↑x' + ↑(1 : ℝ) * Complex.I))
      (b := empStieltjes lam (↑x + ↑(1 : ℝ) * Complex.I) -
        empStieltjes lam (↑x' + ↑(1 : ℝ) * Complex.I))
      (c := -(mFun N σ (↑x + ↑(1 : ℝ) * Complex.I) - mFun N σ (↑x' + ↑(1 : ℝ) * Complex.I)))
    rw [norm_neg] at this
    convert this using 2
    ring
  have h2 : (x' - x) / (1 * 1) ≤ 1 / (2 * N) := by
    rw [mul_one, div_one]
    refine hx'x.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hfin : A * (1 / (N * 1)) + 1 / (2 * N) + 1 / (2 * N) = (A + 1) / N := by
    field_simp
    ring
  linarith

/-- Lower and upper neighbours in a closed `W ⊆ [0, X]`, at distance `≤ N⁻²`, from a finite set
of at most `2(⌈X N²⌉ + 1)` points of `W`. -/
private lemma cnt_interp {W : Set ℝ} (hW : IsClosed W) {X : ℝ} (hWX : W ⊆ Set.Icc 0 X)
    (hN : 0 < N) :
    ∃ Λ : Finset ℝ, Λ.card ≤ 2 * (⌈X * (N : ℝ) ^ 2⌉₊ + 1) ∧ (∀ e ∈ Λ, e ∈ W) ∧
      ∀ E ∈ W, ∃ lo ∈ Λ, ∃ hi ∈ Λ, lo ≤ E ∧ E ≤ hi ∧ hi - lo ≤ 1 / (N : ℝ) ^ 2 := by
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  let cell : ℕ → Set ℝ := fun j => W ∩ Set.Icc ((j : ℝ) / N ^ 2) ((j + 1 : ℝ) / N ^ 2)
  have hcl : ∀ j, IsClosed (cell j) := fun j => hW.inter isClosed_Icc
  have hbb : ∀ j, BddBelow (cell j) := fun j => ⟨(j : ℝ) / N ^ 2, fun x hx => hx.2.1⟩
  have hba : ∀ j, BddAbove (cell j) := fun j => ⟨(j + 1 : ℝ) / N ^ 2, fun x hx => hx.2.2⟩
  refine ⟨(Finset.range (⌈X * (N : ℝ) ^ 2⌉₊ + 1)).biUnion fun j =>
    if (cell j).Nonempty then {sInf (cell j), sSup (cell j)} else ∅, ?_, ?_, ?_⟩
  · refine (Finset.card_biUnion_le).trans ?_
    calc ∑ j ∈ Finset.range (⌈X * (N : ℝ) ^ 2⌉₊ + 1),
          (if (cell j).Nonempty then ({sInf (cell j), sSup (cell j)} : Finset ℝ) else ∅).card
        ≤ ∑ j ∈ Finset.range (⌈X * (N : ℝ) ^ 2⌉₊ + 1), 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          split_ifs
          · exact Finset.card_le_two
          · simp
      _ = 2 * (⌈X * (N : ℝ) ^ 2⌉₊ + 1) := by simp [mul_comm]
  · intro e he
    rw [Finset.mem_biUnion] at he
    obtain ⟨j, -, hj⟩ := he
    split_ifs at hj with hne
    · rcases Finset.mem_insert.1 hj with h | h
      · rw [h]; exact ((hcl j).csInf_mem hne (hbb j)).1
      · rw [Finset.mem_singleton.1 h]; exact ((hcl j).csSup_mem hne (hba j)).1
    · simp at hj
  · intro E hE
    have hE0 : 0 ≤ E := (hWX hE).1
    set j := ⌊E * (N : ℝ) ^ 2⌋₊ with hj
    have hj1 : (j : ℝ) ≤ E * (N : ℝ) ^ 2 := Nat.floor_le (by positivity)
    have hj2 : E * (N : ℝ) ^ 2 < j + 1 := Nat.lt_floor_add_one _
    have hEc : E ∈ cell j := ⟨hE, by rw [div_le_iff₀ hN2]; linarith,
      by rw [le_div_iff₀ hN2]; linarith⟩
    have hne : (cell j).Nonempty := ⟨E, hEc⟩
    have hjr : j ∈ Finset.range (⌈X * (N : ℝ) ^ 2⌉₊ + 1) := by
      rw [Finset.mem_range, Nat.lt_succ_iff]
      exact (Nat.floor_le_ceil _).trans (Nat.ceil_mono (by nlinarith [(hWX hE).2]))
    have hmem : ∀ e ∈ ({sInf (cell j), sSup (cell j)} : Finset ℝ),
        e ∈ (Finset.range (⌈X * (N : ℝ) ^ 2⌉₊ + 1)).biUnion fun j =>
          if (cell j).Nonempty then {sInf (cell j), sSup (cell j)} else ∅ := by
      intro e he
      rw [Finset.mem_biUnion]
      exact ⟨j, hjr, by simpa [hne] using he⟩
    have hlo := (hcl j).csInf_mem hne (hbb j)
    have hhi := (hcl j).csSup_mem hne (hba j)
    refine ⟨sInf (cell j), hmem _ (by simp), sSup (cell j), hmem _ (by simp),
      csInf_le (hbb j) hEc, le_csSup (hba j) hEc, ?_⟩
    have h1 := hhi.2.2
    have h2 := hlo.2.1
    have : ((j + 1 : ℝ) / N ^ 2) - (j : ℝ) / N ^ 2 = 1 / (N : ℝ) ^ 2 := by
      field_simp
      ring
    linarith

/-- Union bound over a finite family. -/
private lemma cnt_union {Ω : Type*} [MeasureSpace Ω] {ι : Type*} (I : Finset ι) (f : ι → Set Ω)
    (p : ℝ≥0∞) (h : ∀ i ∈ I, ℙ (f i) ≤ p) : ℙ (⋃ i ∈ I, f i) ≤ I.card * p := by
  refine (measure_biUnion_finset_le I f).trans ?_
  refine (Finset.sum_le_sum h).trans ?_
  simp

/-! ## Exponents -/

/-- With `η = N^{−1+a}` and `L = ⌊log₂ ⌊1/η⌋⌋`: `2^L η ≤ 1`, `η ≥ 2N^{−3}`, and the bound of
the counting comparison (at `B = N^a + 1`, `|E₂ − E₁| ≤ X`, `C_m = G`) plus one is at most
`N^{4a}`, for `N` large. -/
private lemma cnt_num {a X G : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hX : 0 ≤ X) (hG : 0 ≤ G) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      2 ≤ N ∧ 2 ^ Nat.log 2 ⌊1 / (N : ℝ) ^ (-1 + a)⌋₊ * (N : ℝ) ^ (-1 + a) ≤ 1 ∧
      2 / (N : ℝ) ^ 3 ≤ (N : ℝ) ^ (-1 + a) ∧
      ((N : ℝ) ^ a + 1) * (X + 2 * Real.log (1 / (N : ℝ) ^ (-1 + a)) + 48) +
        40 * N * (N : ℝ) ^ (-1 + a) * (Nat.log 2 ⌊1 / (N : ℝ) ^ (-1 + a)⌋₊ + 1) * G +
        10 * N / 2 ^ Nat.log 2 ⌊1 / (N : ℝ) ^ (-1 + a)⌋₊ + 1 ≤ (N : ℝ) ^ (4 * a) := by
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : ℝ, A₀ = 2 * X + 117 + 40 * G := ⟨_, rfl⟩
  obtain ⟨A₁, hA₁⟩ : ∃ A₁ : ℝ, A₁ = 4 + 80 * G := ⟨_, rfl⟩
  have hA₀0 : 0 ≤ A₀ := by rw [hA₀]; positivity
  have hA₁0 : 0 ≤ A₁ := by rw [hA₁]; positivity
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = A₀ + A₁ / a := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  refine ⟨⌈T ^ (1 / (2 * a))⌉₊ + 2, fun N hN => ?_⟩
  have hN2 : 2 ≤ N := by omega
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have hNT : T ^ (1 / (2 * a)) ≤ N := by
    have := Nat.le_ceil (T ^ (1 / (2 * a)))
    have h' : (⌈T ^ (1 / (2 * a))⌉₊ : ℝ) ≤ N := by
      exact_mod_cast (by omega : ⌈T ^ (1 / (2 * a))⌉₊ ≤ N)
    linarith
  have hNa1 : 1 ≤ (N : ℝ) ^ a := Real.one_le_rpow (by linarith) ha.le
  have hNη : (N : ℝ) * (N : ℝ) ^ (-1 + a) = (N : ℝ) ^ a := by
    rw [← Real.rpow_one_add' hNpos.le (by linarith)]
    ring_nf
  have hT2 : T ≤ (N : ℝ) ^ (2 * a) := by
    have h1 := Real.rpow_le_rpow (by positivity) hNT (by positivity : (0 : ℝ) ≤ 2 * a)
    rwa [← Real.rpow_mul hT0, one_div, inv_mul_cancel₀ (by positivity), Real.rpow_one] at h1
  have hsq : (N : ℝ) ^ (2 * a) = (N : ℝ) ^ a * (N : ℝ) ^ a := by
    rw [← Real.rpow_add hNpos]; ring_nf
  have hsq4 : (N : ℝ) ^ (4 * a) = (N : ℝ) ^ (2 * a) * (N : ℝ) ^ (2 * a) := by
    rw [← Real.rpow_add hNpos]; ring_nf
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hlogr : Real.log N ≤ (N : ℝ) ^ a / a := Real.log_le_rpow_div hNpos.le ha
  have hη1 : (N : ℝ) ^ (-1 + a) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  generalize hηdef : (N : ℝ) ^ (-1 + a) = η at hNη hη1 ⊢
  generalize hPa : (N : ℝ) ^ a = Pa at hNη hNa1 hsq hlogr ⊢
  have hη0 : 0 < η := by
    rw [← hηdef]; exact Real.rpow_pos_of_pos hNpos _
  have hηN : 1 / (N : ℝ) ≤ η := by
    rw [div_le_iff₀ hNpos]
    linarith
  have hiη1 : 1 ≤ 1 / η := by rw [le_div_iff₀ hη0]; linarith
  have hiηN : 1 / η ≤ N := by
    rw [div_le_iff₀ hη0]
    have := (div_le_iff₀ hNpos).1 hηN
    linarith
  have hn1 : (⌊1 / η⌋₊ : ℝ) ≤ 1 / η := Nat.floor_le (by linarith)
  have hn2 : 1 / η < ⌊1 / η⌋₊ + 1 := Nat.lt_floor_add_one _
  generalize hndef : ⌊1 / η⌋₊ = n at hn1 hn2 ⊢
  have hn0 : n ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero, zero_add] at hn2
    linarith
  have hL1 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn0
  have hL2 : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  generalize hLdef : Nat.log 2 n = L at hL1 hL2 ⊢
  have hL1r : (2 : ℝ) ^ L ≤ n := by exact_mod_cast hL1
  have hL2r : (n : ℝ) + 1 ≤ 2 ^ (L + 1) := by exact_mod_cast hL2
  have h2L : (0 : ℝ) < 2 ^ L := by positivity
  have hLη : (2 : ℝ) ^ L * η ≤ 1 := by
    have := hL1r.trans hn1
    rwa [le_div_iff₀ hη0] at this
  have hsmall : 1 < 2 * 2 ^ L * η := by
    have h1 : 1 / η < 2 ^ (L + 1) := lt_of_lt_of_le hn2 hL2r
    rw [div_lt_iff₀ hη0, pow_succ] at h1
    linarith
  have hNL : 10 * (N : ℝ) / 2 ^ L ≤ 20 * Pa := by
    rw [div_le_iff₀ h2L]
    have : 10 * (N : ℝ) * 1 ≤ 10 * N * (2 * 2 ^ L * η) :=
      mul_le_mul_of_nonneg_left hsmall.le (by positivity)
    have e : 10 * (N : ℝ) * (2 * 2 ^ L * η) = 20 * (N * η) * 2 ^ L := by ring
    rw [e, hNη] at this
    linarith
  have hlogη : Real.log (1 / η) ≤ Real.log N := Real.log_le_log (by linarith) hiηN
  have hlogη0 : 0 ≤ Real.log (1 / η) := Real.log_nonneg hiη1
  have hLlog : (L : ℝ) ≤ 2 * Real.log N := by
    have h1 : (2 : ℝ) ^ L ≤ N := hL1r.trans (hn1.trans hiηN)
    have h2 := Real.log_le_log h2L h1
    rw [Real.log_pow] at h2
    have h3 := Real.log_two_gt_d9
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    nlinarith
  refine ⟨hN2, hLη, ?_, ?_⟩
  · refine le_trans ?_ hηN
    rw [div_le_div_iff₀ (by positivity) hNpos]
    have h4 : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have : (N : ℝ) ^ 3 = (N : ℝ) ^ 2 * N := by ring
    nlinarith
  · have e1 : 40 * (N : ℝ) * η * (L + 1) * G = 40 * Pa * (L + 1) * G := by
      rw [← hNη]; ring
    rw [e1]
    have hNa0 : 0 ≤ Pa := by linarith
    have k1 : (Pa + 1) * (X + 2 * Real.log (1 / η) + 48) ≤
        2 * Pa * (X + 2 * Real.log N + 48) := by
      have h1 : X + 2 * Real.log (1 / η) + 48 ≤ X + 2 * Real.log N + 48 := by linarith
      have h0 : 0 ≤ X + 2 * Real.log (1 / η) + 48 := by linarith
      calc (Pa + 1) * (X + 2 * Real.log (1 / η) + 48)
          ≤ (2 * Pa) * (X + 2 * Real.log (1 / η) + 48) :=
            mul_le_mul_of_nonneg_right (by linarith) h0
        _ ≤ 2 * Pa * (X + 2 * Real.log N + 48) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
    have k2 : 40 * Pa * (L + 1) * G ≤ 40 * Pa * (2 * Real.log N + 1) * G := by
      have h1 : (L : ℝ) + 1 ≤ 2 * Real.log N + 1 := by linarith
      have h40 : 0 ≤ 40 * Pa := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h40) hG
    have k3 : 2 * Pa * (X + 2 * Real.log N + 48) + 40 * Pa * (2 * Real.log N + 1) * G +
        20 * Pa + 1 ≤ Pa * (A₀ + A₁ * Real.log N) := by
      have e : Pa * (A₀ + A₁ * Real.log N) - (2 * Pa * (X + 2 * Real.log N + 48) +
          40 * Pa * (2 * Real.log N + 1) * G + 20 * Pa + 1) = Pa - 1 := by
        rw [hA₀, hA₁]; ring
      linarith
    have k4 : Pa * (A₀ + A₁ * Real.log N) ≤ (N : ℝ) ^ (2 * a) * T := by
      rw [hsq, hT]
      have m1 : A₁ * Real.log N ≤ A₁ * (Pa / a) := mul_le_mul_of_nonneg_left hlogr hA₁0
      have m2 : A₀ ≤ A₀ * Pa := le_mul_of_one_le_right hA₀0 hNa1
      have e : Pa * (A₀ + A₁ / a) = A₀ * Pa + A₁ * (Pa / a) := by ring
      have : A₀ + A₁ * Real.log N ≤ Pa * (A₀ + A₁ / a) := by linarith
      calc Pa * (A₀ + A₁ * Real.log N) ≤ Pa * (Pa * (A₀ + A₁ / a)) :=
            mul_le_mul_of_nonneg_left this hNa0
        _ = _ := by ring
    have k5 : (N : ℝ) ^ (2 * a) * T ≤ (N : ℝ) ^ (4 * a) := by
      rw [hsq4]
      exact mul_le_mul_of_nonneg_left hT2 (by positivity)
    linarith only [k1, k2, hNL, k3, k4, k5]

/-! ## The count on a closed window from the law on the lines and one exact count -/

/-- Deterministic part: if `|s − m| ≤ N^a/(N Im z)` on the grids of the vertical lines at the
points of `Λ ∪ {P}` and of the top segment, and `n_N(P) = n(P)`, then
`|n_N(E) − n(E)| ≤ N^ε` on `W`. -/
private lemma cnt_det {τ₂ ε X a : ℝ} (hτ₂ : 0 < τ₂) (hX : X + 2 ≤ τ₂⁻¹)
    (h4a : 4 * a ≤ ε) {N : ℕ} (hN2 : 2 ≤ N) (hNG : 2 * genPropConst τ₂ ≤ N)
    (hLη : 2 ^ Nat.log 2 ⌊1 / (N : ℝ) ^ (-1 + a)⌋₊ * (N : ℝ) ^ (-1 + a) ≤ 1)
    (hη3 : 2 / (N : ℝ) ^ 3 ≤ (N : ℝ) ^ (-1 + a))
    (hnum : ((N : ℝ) ^ a + 1) * (X + 2 * Real.log (1 / (N : ℝ) ^ (-1 + a)) + 48) +
        40 * N * (N : ℝ) ^ (-1 + a) * (Nat.log 2 ⌊1 / (N : ℝ) ^ (-1 + a)⌋₊ + 1) *
          genPropConst τ₂ + 10 * N / 2 ^ Nat.log 2 ⌊1 / (N : ℝ) ^ (-1 + a)⌋₊ + 1 ≤
          (N : ℝ) ^ (4 * a))
    {σ : Fin M → ℝ} (hda : DensityAssumptions τ₂ N σ) (lam : Fin N → ℝ)
    {W : Set ℝ} (hWX : W ⊆ Set.Icc τ₂ X) {P : ℝ} (hP : P ∈ Set.Icc τ₂ X) (Λ : Finset ℝ)
    (hΛW : ∀ e ∈ Λ, e ∈ W)
    (hΛint : ∀ E ∈ W, ∃ lo ∈ Λ, ∃ hi ∈ Λ, lo ≤ E ∧ E ≤ hi ∧ hi - lo ≤ 1 / (N : ℝ) ^ 2)
    (hline : ∀ e ∈ insert P Λ, ∀ j : ℕ, j ∈ Finset.Icc 1 (2 * N ^ 4) →
      (N : ℝ) ^ (-1 + a) ≤ (j : ℝ) / N ^ 4 →
      ‖empStieltjes lam (↑e + ↑((j : ℝ) / N ^ 4) * Complex.I) -
          mFun N σ (↑e + ↑((j : ℝ) / N ^ 4) * Complex.I)‖ ≤
        (N : ℝ) ^ a * (1 / (N * ((j : ℝ) / N ^ 4))))
    (htop : ∀ j : ℕ, j ∈ Finset.range (⌈X * (N : ℝ) ^ 2⌉₊ + 2) →
      ‖empStieltjes lam (↑((j : ℝ) / N ^ 2) + ↑(1 : ℝ) * Complex.I) -
          mFun N σ (↑((j : ℝ) / N ^ 2) + ↑(1 : ℝ) * Complex.I)‖ ≤ (N : ℝ) ^ a * (1 / (N * 1)))
    (hexact : ((Finset.univ.filter fun j => P ≤ lam j).card : ℝ) = nClass N σ P) :
    ∀ E ∈ W, |((Finset.univ.filter fun j => E ≤ lam j).card : ℝ) - nClass N σ E| ≤
      (N : ℝ) ^ ε := by
  have hN0 : 0 < N := by omega
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hσ := hda.nonneg
  set G := genPropConst τ₂ with hGdef
  have hG : 0 ≤ G := by rw [hGdef]; unfold genPropConst; positivity
  set η := (N : ℝ) ^ (-1 + a) with hη
  have hη0 : 0 < η := Real.rpow_pos_of_pos (by linarith) _
  set L := Nat.log 2 ⌊1 / η⌋₊ with hL
  have hNa : 0 ≤ (N : ℝ) ^ a := by positivity
  -- the bounds on the lines, the top segment and `|m|`
  have hL1 : ∀ e ∈ insert P Λ, ∀ y ∈ Set.Icc η 1, ‖empStieltjes lam (↑e + ↑y * Complex.I) -
      mFun N σ (↑e + ↑y * Complex.I)‖ ≤ ((N : ℝ) ^ a + 1) / (N * y) :=
    fun e he => cnt_line_transfer σ hσ hN2 lam e hη0 hη3 hNa (hline e he)
  have hT1 : ∀ x ∈ Set.Icc 0 X, ‖empStieltjes lam (↑x + ↑(1 : ℝ) * Complex.I) -
      mFun N σ (↑x + ↑(1 : ℝ) * Complex.I)‖ ≤ ((N : ℝ) ^ a + 1) / N :=
    cnt_top_transfer σ hσ hN2 lam htop
  have hmb : ∀ e ∈ Set.Icc τ₂ X, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖mFun N σ (↑e + ↑y * Complex.I)‖ ≤ G := by
    intro e he y hy0 hy1
    have hz : 0 < ((e : ℂ) + ↑y * Complex.I).im := by simpa using hy0
    have h1 : τ₂ ≤ ‖(e : ℂ) + ↑y * Complex.I‖ := by
      have := Complex.abs_re_le_norm ((e : ℂ) + ↑y * Complex.I)
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero] at this
      linarith [he.1, le_abs_self e]
    have h2 : ‖(e : ℂ) + ↑y * Complex.I‖ ≤ τ₂⁻¹ := by
      have := Complex.norm_le_abs_re_add_abs_im ((e : ℂ) + ↑y * Complex.I)
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, Complex.add_im,
        Complex.mul_im, zero_add] at this
      rw [abs_of_nonneg (by linarith [he.1]), abs_of_pos hy0] at this
      linarith [he.2]
    exact (gen_prop_m hda hz h1 h2).2.1
  -- the comparison at the points of `Λ ∪ {P}`
  set Bnd := ((N : ℝ) ^ a + 1) * (X + 2 * Real.log (1 / η) + 48) +
      40 * N * η * (L + 1) * G + 10 * N / 2 ^ L with hBnd
  have hcore : ∀ E₁ E₂, E₁ ∈ insert P Λ → E₂ ∈ insert P Λ → E₁ ≤ E₂ →
      |((Finset.univ.filter fun j => E₁ ≤ lam j).card : ℝ) -
        (Finset.univ.filter fun j => E₂ ≤ lam j).card - (nClass N σ E₁ - nClass N σ E₂)| ≤
        Bnd := by
    intro E₁ E₂ h1 h2 h12
    have hmem : ∀ e ∈ insert P Λ, e ∈ Set.Icc τ₂ X := by
      intro e he
      rcases Finset.mem_insert.1 he with h | h
      · rw [h]; exact hP
      · exact hWX (hΛW e h)
    have m1 := hmem E₁ h1
    have m2 := hmem E₂ h2
    have hc := cnt_core σ hσ hN0 lam (B := (N : ℝ) ^ a + 1) (Cm := G) L hη0 hLη (by positivity)
      h12 (lt_of_lt_of_le hτ₂ m1.1)
      (fun E hE y hy => by
        rcases hE with rfl | rfl
        · exact ⟨hL1 _ h1 y hy, hmb _ m1 y (lt_of_lt_of_le hη0 hy.1) hy.2⟩
        · exact ⟨hL1 _ h2 y hy, hmb _ m2 y (lt_of_lt_of_le hη0 hy.1) hy.2⟩)
      (fun x hx => hT1 x ⟨by linarith [hx.1, m1.1], by linarith [hx.2, m2.2]⟩)
    refine hc.trans ?_
    have hlog : 0 ≤ Real.log (1 / η) := Real.log_nonneg (by
      rw [le_div_iff₀ hη0]
      have h2L : (1 : ℝ) ≤ 2 ^ L := one_le_pow₀ (by norm_num)
      nlinarith)
    have : E₂ - E₁ ≤ X := by linarith [m1.1, m2.2]
    have hB : 0 ≤ (N : ℝ) ^ a + 1 := by positivity
    rw [hBnd]
    gcongr
  have hpt : ∀ e ∈ insert P Λ,
      |((Finset.univ.filter fun j => e ≤ lam j).card : ℝ) - nClass N σ e| ≤ Bnd := by
    intro e he
    rcases le_total e P with h | h
    · have := hcore e P he (Finset.mem_insert_self _ _) h
      rw [hexact] at this
      convert this using 2
      ring
    · have := hcore P e (Finset.mem_insert_self _ _) he h
      rw [hexact] at this
      rw [abs_sub_comm] at this
      convert this using 2
      ring
  -- the density between neighbours
  have hgap : ∀ lo hi, lo ∈ Set.Icc τ₂ X → hi ∈ Set.Icc τ₂ X → lo ≤ hi →
      hi - lo ≤ 1 / (N : ℝ) ^ 2 → nClass N σ lo - nClass N σ hi ≤ 1 := by
    intro lo hi hlo hhi hlh hd
    have hN2' : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
    set δ := 1 / (N : ℝ) ^ 2 with hδ
    have hδ0 : 0 < δ := by positivity
    have hδ1 : δ ≤ 1 := by rw [hδ, div_le_one hN2']; nlinarith
    set c := (lo + hi) / 2 with hc
    have hsub : Set.Icc lo hi ⊆ Set.Icc (c - δ) (c + δ) := fun t ht =>
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have := isProbabilityMeasure_varrho N σ hσ hN0
    have h1 := cnt_nClass_sub_le σ hσ hN0 lo hi
    have h2 := measureReal_mono (μ := varrho N σ) hsub
    have h3 := cnt_varrho_Icc_le σ hσ hN0 c hδ0
    have h4 : (mFun N σ (↑c + ↑δ * Complex.I)).im ≤ G :=
      (Complex.im_le_norm _).trans
        (hmb c ⟨by linarith [hlo.1, hhi.1], by linarith [hlo.2, hhi.2]⟩ δ hδ0 hδ1)
    have h5 : (N : ℝ) * (2 * δ * G) ≤ 1 := by
      rw [hδ]
      have : (N : ℝ) * (2 * (1 / (N : ℝ) ^ 2) * G) = 2 * G / N := by field_simp
      rw [this, div_le_one (by linarith)]
      linarith
    have hN0r : (0 : ℝ) ≤ N := by linarith
    have h6 : (varrho N σ).real (Set.Icc lo hi) ≤ 2 * δ * G := by
      have : 2 * δ * (mFun N σ (↑c + ↑δ * Complex.I)).im ≤ 2 * δ * G :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
      linarith
    have h7 := mul_le_mul_of_nonneg_left h6 hN0r
    linarith
  have hfin : Bnd + 1 ≤ (N : ℝ) ^ ε := by
    refine le_trans ?_ (Real.rpow_le_rpow_of_exponent_le (by linarith) h4a)
    rw [hBnd]
    exact hnum
  intro E hE
  obtain ⟨lo, hlo, hi, hhi, hloE, hEhi, hd⟩ := hΛint E hE
  have hloW := hWX (hΛW lo hlo)
  have hhiW := hWX (hΛW hi hhi)
  have hlo' := hpt lo (Finset.mem_insert_of_mem hlo)
  have hhi' := hpt hi (Finset.mem_insert_of_mem hhi)
  have hg := hgap lo hi hloW hhiW (hloE.trans hEhi) hd
  have c1 : ((Finset.univ.filter fun j => E ≤ lam j).card : ℝ) ≤
      (Finset.univ.filter fun j => lo ≤ lam j).card := by
    exact_mod_cast Finset.card_le_card fun j hj => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      linarith
  have c2 : ((Finset.univ.filter fun j => hi ≤ lam j).card : ℝ) ≤
      (Finset.univ.filter fun j => E ≤ lam j).card := by
    exact_mod_cast Finset.card_le_card fun j hj => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      linarith
  have n1 := cnt_nClass_anti σ hσ hN0 hloE
  have n2 := cnt_nClass_anti σ hσ hN0 hEhi
  rw [abs_le] at hlo' hhi' ⊢
  constructor <;> linarith

private lemma cnt_re_pt (x y : ℝ) : ((x : ℂ) + (y : ℂ) * Complex.I).re = x := by simp

private lemma cnt_im_pt (x y : ℝ) : ((x : ℂ) + (y : ℂ) * Complex.I).im = y := by simp

/-- The count on a closed window `W ⊆ [τ₂, X]`: if the averaged law (level `a = min(ε,1)/4`,
`D + 8`) holds on the vertical lines over `W ∪ {P}` for heights `[N^{−1+a}, 2]` and on the
segment `[0, X + 1] + i`, and `n_N(P) = n(P)` with high probability, then
`|n_N(E) − n(E)| ≤ N^ε` for all `E ∈ W` with high probability. -/
private lemma cnt_window (τ₂ ε D X : ℝ) (hτ₂ : 0 < τ₂) (hε : 0 < ε) (hX0 : 0 ≤ X)
    (hX : X + 2 ≤ τ₂⁻¹) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (Xm : Ω → Matrix (Fin M) (Fin N) ℝ)
      (W : Set ℝ) (P : ℝ),
      Sig.PosDef → DensityAssumptions τ₂ N (specOf Sig) → IsClosed W → W ⊆ Set.Icc τ₂ X →
      P ∈ Set.Icc τ₂ X →
      (∀ z : ℂ, ((z.re ∈ W ∨ z.re = P) ∧ z.im ∈ Set.Icc ((N : ℝ) ^ (-1 + min ε 1 / 4)) 2) ∨
          (z.re ∈ Set.Icc 0 (X + 1) ∧ z.im = 1) →
        ODomAt N (min ε 1 / 4) (D + 8) (fun ω => mN Sig (Xm ω) z - mFun N (specOf Sig) z)
          (fun _ => 1 / (N * z.im))) →
      HighProbAt N (D + 1) {ω | (eigCount (QN Sig (Xm ω)) P : ℝ) = nClass N (specOf Sig) P} →
      HighProbAt N D {ω | (eigCount (QN Sig (Xm ω)) P : ℝ) = nClass N (specOf Sig) P ∧
        ∀ E ∈ W, |(eigCount (QN Sig (Xm ω)) E : ℝ) - nClass N (specOf Sig) E| ≤ (N : ℝ) ^ ε} := by
  set a := min ε 1 / 4 with ha_def
  have ha : 0 < a := by rw [ha_def]; have := lt_min hε one_pos; linarith
  have ha1 : a ≤ 1 := by rw [ha_def]; have := min_le_right ε 1; linarith
  have h4a : 4 * a ≤ ε := by rw [ha_def]; have := min_le_left ε 1; linarith
  have hG : 0 ≤ genPropConst τ₂ := by unfold genPropConst; positivity
  obtain ⟨N₁, hN₁⟩ := cnt_num ha ha1 hX0 hG
  refine ⟨max N₁ (max ⌈5 * X + 13⌉₊ ⌈2 * genPropConst τ₂⌉₊), ?_⟩
  intro N hN Ω _ _ M Sig Xm W P hSig hda hWc hWX hP hlaw hexact
  obtain ⟨hN2, hLη, hη3, hnum⟩ := hN₁ N (le_of_max_le_left hN)
  have hN0 : 0 < N := by omega
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have hNX : 5 * X + 13 ≤ (N : ℝ) := by
    have := Nat.le_ceil (5 * X + 13)
    have h' : (⌈5 * X + 13⌉₊ : ℝ) ≤ N := by
      exact_mod_cast le_of_max_le_left (le_of_max_le_right hN)
    linarith
  have hNG : 2 * genPropConst τ₂ ≤ (N : ℝ) := by
    have := Nat.le_ceil (2 * genPropConst τ₂)
    have h' : (⌈2 * genPropConst τ₂⌉₊ : ℝ) ≤ N := by
      exact_mod_cast le_of_max_le_right (le_of_max_le_right hN)
    linarith
  set σ := specOf Sig with hσdef
  set η := (N : ℝ) ^ (-1 + a) with hη
  have hη0 : 0 < η := Real.rpow_pos_of_pos hNpos _
  obtain ⟨Λ, hΛc, hΛW, hΛint⟩ := cnt_interp hWc (X := X)
    (fun e he => ⟨hτ₂.le.trans (hWX he).1, (hWX he).2⟩) hN0
  set K := ⌈X * (N : ℝ) ^ 2⌉₊ with hK
  set Yg := (Finset.Icc 1 (2 * N ^ 4)).filter (fun j : ℕ => η ≤ (j : ℝ) / N ^ 4) with hYg
  let bad : ℂ → Set Ω := fun z =>
    {ω | (N : ℝ) ^ a * (1 / (N * z.im)) < ‖mN Sig (Xm ω) z - mFun N σ z‖}
  let zl : ℝ × ℕ → ℂ := fun p => ↑p.1 + ↑((p.2 : ℝ) / N ^ 4) * Complex.I
  let zt : ℕ → ℂ := fun j => ↑((j : ℝ) / N ^ 2) + ↑(1 : ℝ) * Complex.I
  set B₁ := ⋃ p ∈ (insert P Λ) ×ˢ Yg, bad (zl p) with hB₁
  set B₂ := ⋃ j ∈ Finset.range (K + 2), bad (zt j) with hB₂
  set B₃ := {ω | (eigCount (QN Sig (Xm ω)) P : ℝ) = nClass N σ P}ᶜ with hB₃
  -- the probability of the bad events
  have hq : ∀ z, (∃ p ∈ (insert P Λ) ×ˢ Yg, z = zl p) ∨ (∃ j ∈ Finset.range (K + 2), z = zt j) →
      ℙ (bad z) ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 8))) := by
    intro z hz
    refine hlaw z ?_
    rcases hz with ⟨p, hp, rfl⟩ | ⟨j, hj, rfl⟩
    · obtain ⟨hp1, hp2⟩ := Finset.mem_product.1 hp
      rw [hYg, Finset.mem_filter, Finset.mem_Icc] at hp2
      left
      simp only [zl, cnt_re_pt, cnt_im_pt]
      refine ⟨?_, ?_⟩
      · rcases Finset.mem_insert.1 hp1 with h | h
        · exact Or.inr h
        · exact Or.inl (hΛW _ h)
      · have hj2 : (p.2 : ℝ) ≤ 2 * (N : ℝ) ^ 4 := by exact_mod_cast hp2.1.2
        have hN4 : (0 : ℝ) < (N : ℝ) ^ 4 := by positivity
        exact ⟨hp2.2, by rw [div_le_iff₀ hN4]; linarith⟩
    · right
      have hjK : (j : ℝ) ≤ K + 1 := by
        have := Finset.mem_range.1 hj
        have : j ≤ K + 1 := by omega
        exact_mod_cast this
      have hK1 : (K : ℝ) < X * (N : ℝ) ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
      have hN2' : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
      simp only [zt, cnt_re_pt, cnt_im_pt]
      refine ⟨⟨by positivity, ?_⟩, trivial⟩
      rw [div_le_iff₀ (by positivity)]
      nlinarith
  have hP₁ : ℙ B₁ ≤ ((insert P Λ) ×ˢ Yg).card * ENNReal.ofReal ((N : ℝ) ^ (-(D + 8))) :=
    cnt_union _ _ _ fun p hp => hq _ (Or.inl ⟨p, hp, rfl⟩)
  have hP₂ : ℙ B₂ ≤ (Finset.range (K + 2)).card * ENNReal.ofReal ((N : ℝ) ^ (-(D + 8))) :=
    cnt_union _ _ _ fun j hj => hq _ (Or.inr ⟨j, hj, rfl⟩)
  have hP₃ : ℙ B₃ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) := hexact
  -- the cardinalities
  have hcard : (((insert P Λ) ×ˢ Yg).card : ℝ) + (Finset.range (K + 2)).card ≤ (N : ℝ) ^ 7 := by
    have c1 : ((insert P Λ) ×ˢ Yg).card ≤ (2 * (K + 1) + 1) * (2 * N ^ 4) := by
      rw [Finset.card_product]
      refine Nat.mul_le_mul ((Finset.card_insert_le _ _).trans (by omega)) ?_
      refine (Finset.card_filter_le _ _).trans ?_
      simp
    have c1r : (((insert P Λ) ×ˢ Yg).card : ℝ) ≤ (2 * (K + 1) + 1) * (2 * (N : ℝ) ^ 4) := by
      exact_mod_cast c1
    rw [Finset.card_range]
    push_cast
    have hK1 : (K : ℝ) < X * (N : ℝ) ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have hN1 : (1 : ℝ) ≤ N := by linarith
    have p2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := one_le_pow₀ hN1
    have p4 : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 4 := pow_le_pow_right₀ hN1 (by norm_num)
    have p6 : (N : ℝ) ^ 4 ≤ (N : ℝ) ^ 6 := pow_le_pow_right₀ hN1 (by norm_num)
    have e7 : (N : ℝ) ^ 7 = (N : ℝ) ^ 6 * N := by ring
    have e6 : (N : ℝ) ^ 6 = (N : ℝ) ^ 2 * (N : ℝ) ^ 4 := by ring
    have hXN : (2 * (K + 1) + 1) * (2 * (N : ℝ) ^ 4) + (K + 2) ≤
        (2 * X * (N : ℝ) ^ 2 + 5) * (2 * (N : ℝ) ^ 4) + (X * (N : ℝ) ^ 2 + 3) := by
      have : (2 * (K + 1) + 1 : ℝ) ≤ 2 * X * (N : ℝ) ^ 2 + 5 := by linarith
      have := mul_le_mul_of_nonneg_right this (by positivity : (0 : ℝ) ≤ 2 * (N : ℝ) ^ 4)
      linarith
    have h6 : (2 * X * (N : ℝ) ^ 2 + 5) * (2 * (N : ℝ) ^ 4) + (X * (N : ℝ) ^ 2 + 3) ≤
        (5 * X + 13) * (N : ℝ) ^ 6 := by
      rw [e6]
      have hX4 : X * (N : ℝ) ^ 2 ≤ X * ((N : ℝ) ^ 2 * (N : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by positivity)
          (one_le_pow₀ hN1)) hX0
      have h1 : (N : ℝ) ^ 4 ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ 4 :=
        le_mul_of_one_le_left (by positivity) p2
      nlinarith
    have h7 : (5 * X + 13) * (N : ℝ) ^ 6 ≤ (N : ℝ) ^ 7 := by
      rw [e7]
      exact mul_le_mul_of_nonneg_left hNX (by positivity) |>.trans_eq' (by ring)
    linarith
  have hprob : ℙ (B₁ ∪ B₂ ∪ B₃) ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
    refine (measure_union_le _ _).trans ?_
    refine (add_le_add (measure_union_le _ _) hP₃).trans ?_
    refine (add_le_add (add_le_add hP₁ hP₂) le_rfl).trans ?_
    have hq0 : (0 : ℝ) ≤ (N : ℝ) ^ (-(D + 8)) := by positivity
    rw [← add_mul, ← Nat.cast_add, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have e8 : (N : ℝ) ^ (-(D + 8)) * (N : ℝ) ^ 7 = (N : ℝ) ^ (-(D + 1)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hNpos]
      congr 1
      push_cast
      ring
    have e1 : (N : ℝ) ^ (-D) = (N : ℝ) ^ (-(D + 1)) * N := by
      rw [← Real.rpow_add_one hNpos.ne']
      congr 1
      ring
    have hq1 : (0 : ℝ) ≤ (N : ℝ) ^ (-(D + 1)) := by positivity
    push_cast
    have := mul_le_mul_of_nonneg_left hcard hq0
    nlinarith
  -- on the complement
  refine le_trans (measure_mono ?_) hprob
  intro ω hω
  by_contra hn
  apply hω
  simp only [Set.mem_union, not_or] at hn
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hn
  rw [hB₃, Set.mem_compl_iff, not_not] at h₃
  set lam := specOf (QN Sig (Xm ω)) with hlam
  have hsF : ∀ z : ℂ, 0 < z.im → mN Sig (Xm ω) z = empStieltjes lam z :=
    fun z hz => mN_eq_empStieltjes hSig (Xm ω) hz
  have hgood' : ∀ z, (∃ p ∈ (insert P Λ) ×ˢ Yg, z = zl p) ∨
      (∃ j ∈ Finset.range (K + 2), z = zt j) →
      ‖mN Sig (Xm ω) z - mFun N σ z‖ ≤ (N : ℝ) ^ a * (1 / (N * z.im)) := by
    intro z hz
    rcases hz with ⟨p, hp, rfl⟩ | ⟨j, hj, rfl⟩
    · have : ω ∉ bad (zl p) := fun hb => h₁ (Set.mem_biUnion hp hb)
      simpa [bad] using this
    · have : ω ∉ bad (zt j) := fun hb => h₂ (Set.mem_biUnion hj hb)
      simpa [bad] using this
  refine ⟨h₃, ?_⟩
  have hdet := cnt_det hτ₂ hX h4a hN2 hNG hLη hη3 hnum hda lam hWX hP Λ hΛW hΛint
    (fun e he j hj hjη => by
      have hpos : 0 < (j : ℝ) / N ^ 4 := lt_of_lt_of_le hη0 hjη
      have h := hgood' (zl (e, j)) (Or.inl ⟨(e, j), Finset.mem_product.2
        ⟨he, by rw [hYg, Finset.mem_filter]; exact ⟨hj, hjη⟩⟩, rfl⟩)
      have him : (zl (e, j)).im = (j : ℝ) / N ^ 4 := cnt_im_pt _ _
      rw [him, hsF _ (by rw [him]; exact hpos)] at h
      exact h)
    (fun j hj => by
      have h := hgood' (zt j) (Or.inr ⟨j, hj, rfl⟩)
      have him : (zt j).im = 1 := cnt_im_pt _ _
      rw [him, hsF _ (by rw [him]; exact one_pos)] at h
      exact h)
    h₃
  exact hdet

/-! ## The edges, the classical counting function at the exact-count points -/

/-- (phi_bounded) and (Sigma_gap) give `N > 0`, `M > 0` and some positive `σ i`. -/
private lemma cnt_facts {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) :
    0 < N ∧ 0 < M ∧ (posVals σ).Nonempty := by
  have hτ := h.pos
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · exfalso
      have := h.phi_lower
      simp [phiRatio, h0] at this
      linarith
    · exact h0
  have hM : M ≠ 0 := by
    rintro rfl
    have := h.phi_lower
    simp [phiRatio] at this
    linarith
  refine ⟨hN, Nat.pos_of_ne_zero hM, ?_⟩
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have hall : ∀ i, σ i = 0 := by
    intro i
    by_contra hi
    have hpos : 0 < σ i := lt_of_le_of_ne (h.nonneg i) (Ne.symm hi)
    have : σ i ∈ posVals σ := by
      simp only [posVals, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨i, rfl⟩, hpos⟩
    rw [hne] at this
    simp at this
  have hgap := h.Sigma_gap
  have happ : empMeasure σ (Set.Icc 0 τ) = (M : ℝ≥0∞)⁻¹ * (M : ℝ≥0∞) := by
    simp only [empMeasure, Measure.smul_apply, Measure.finsetSum_apply,
      Measure.dirac_apply' _ measurableSet_Icc, smul_eq_mul, hall]
    have h0 : (0 : ℝ) ∈ Set.Icc 0 τ := ⟨le_rfl, hτ.le⟩
    simp [Set.indicator_of_mem h0]
  have hM' : (M : ℝ≥0∞)⁻¹ * (M : ℝ≥0∞) = 1 :=
    ENNReal.inv_mul_cancel (by exact_mod_cast hM) (ENNReal.natCast_ne_top _)
  rw [happ, hM', ENNReal.toReal_one] at hgap
  linarith

/-- `a_j ≤ a_i` for `1 ≤ i ≤ j ≤ 2p`. -/
private lemma cnt_anti {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) {i j : ℕ}
    (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ 2 * numBands N σ) : edgeVal N σ j ≤ edgeVal N σ i := by
  obtain ⟨hN, -, hS⟩ := cnt_facts h
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ k hik ih =>
    exact (edgeVal_succ_le N σ h.nonneg hN hS (by omega) (by omega)).trans (ih (by omega))

/-- `0 ≤ a_k ≤ 2τ⁻¹(1 + τ⁻¹)` for `1 ≤ k ≤ 2p`. -/
private lemma cnt_edge_bd {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) {k : ℕ}
    (hk : 1 ≤ k) (hkp : k ≤ 2 * numBands N σ) :
    0 ≤ edgeVal N σ k ∧ edgeVal N σ k ≤ 2 * τ⁻¹ * (1 + τ⁻¹) := by
  obtain ⟨hN, -, hS⟩ := cnt_facts h
  exact edgeVal_mem_Icc N σ h.nonneg hN hS h.pos h.phi_lower h.phi_upper h.bound_Sigma hk hkp

/-- `n(E) = 0` for `E ≥ a_1`. -/
private lemma cnt_nClass_top {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ)
    {E : ℝ} (hE : edgeVal N σ 1 ≤ E) : nClass N σ E = 0 := by
  obtain ⟨hN, -, hS⟩ := cnt_facts h
  have hp := (card_innerCrit N σ h.nonneg hN hS).2
  have h1 := (nClass_edgeVal h (k := 1) le_rfl hp).1
  have h0 : cumCount N σ (1 - 1) = 0 := by simp [cumCount]
  rw [show 2 * 1 - 1 = 1 by norm_num, h0, Nat.cast_zero] at h1
  have := cnt_nClass_anti σ h.nonneg hN hE
  have := cnt_nClass_nonneg (N := N) σ E
  linarith

/-- A positive point of `supp ϱ` lies in a band `[a_{2k}, a_{2k−1}]`, `1 ≤ k ≤ p`. -/
private lemma cnt_supp {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) {y : ℝ}
    (hy : y ∈ (varrho N σ).support) (hy0 : 0 < y) :
    ∃ k, 1 ≤ k ∧ k ≤ numBands N σ ∧ edgeVal N σ (2 * k) ≤ y ∧ y ≤ edgeVal N σ (2 * k - 1) := by
  obtain ⟨hN, -, hS⟩ := cnt_facts h
  obtain ⟨k, hk1, hk2, hyk⟩ := (mem_support_varrho_iff N σ h.nonneg hN hS hy0).1 hy
  exact ⟨k, hk1, hk2, hyk.1, hyk.2⟩

/-- `a_1 ∈ supp ϱ` when `a_1 > 0`. -/
private lemma cnt_supp_ne {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ)
    (h1 : 0 < edgeVal N σ 1) : (varrho N σ).support.Nonempty := by
  obtain ⟨hN, -, hS⟩ := cnt_facts h
  have hp := (card_innerCrit N σ h.nonneg hN hS).2
  refine ⟨edgeVal N σ 1, (mem_support_varrho_iff N σ h.nonneg hN hS h1).2 ⟨1, le_rfl, hp, ?_⟩⟩
  have := cnt_anti h (i := 1) (j := 2) le_rfl (by norm_num) (by omega)
  exact ⟨by simpa using this, by simp⟩

/-- At the midpoint of a gap `(a_{2j+1}, a_{2j})` of width `≥ τ` with `a_{2j} ≥ τ`:
`n = d_j`, the distance to `supp ϱ` is `≥ τ/2`, and `τ/2 ≤ gapMid ≤ a_1`. -/
private lemma cnt_gapMid {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) {j : ℕ}
    (hj : 1 ≤ j) (hjp : j < numBands N σ) (ha : τ ≤ edgeVal N σ (2 * j))
    (hw : τ ≤ edgeVal N σ (2 * j) - edgeVal N σ (2 * j + 1)) :
    nClass N σ (gapMid N σ j) = cumCount N σ j ∧
      τ / 2 ≤ Metric.infDist (gapMid N σ j) (varrho N σ).support ∧
      τ / 2 ≤ gapMid N σ j ∧ gapMid N σ j ≤ edgeVal N σ 1 := by
  obtain ⟨hN, -, hS⟩ := cnt_facts h
  have hτ := h.pos
  have hb0 := (cnt_edge_bd h (k := 2 * j + 1) (by omega) (by omega)).1
  have hm1 : edgeVal N σ (2 * j + 1) ≤ gapMid N σ j := by unfold gapMid; linarith
  have hm2 : gapMid N σ j ≤ edgeVal N σ (2 * j) := by unfold gapMid; linarith
  have hlow : τ / 2 ≤ gapMid N σ j := by unfold gapMid; linarith
  obtain ⟨-, e2⟩ := nClass_edgeVal h (k := j) hj (by omega)
  have e2' := e2 (by linarith)
  have e3 := (nClass_edgeVal h (k := j + 1) (by omega) (by omega)).1
  rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega, show j + 1 - 1 = j by omega] at e3
  have n1 := cnt_nClass_anti σ h.nonneg hN hm1
  have n2 := cnt_nClass_anti σ h.nonneg hN hm2
  refine ⟨by linarith, ?_, hlow, hm2.trans (cnt_anti h le_rfl (by omega) (by omega))⟩
  have hne : (varrho N σ).support.Nonempty :=
    cnt_supp_ne h (by linarith [cnt_anti h (i := 1) (j := 2 * j) le_rfl (by omega) (by omega)])
  refine (Metric.le_infDist hne).2 fun y hy => ?_
  rw [Real.dist_eq]
  rcases le_or_gt y 0 with hy0 | hy0
  · rw [abs_of_pos (by linarith)]; linarith
  obtain ⟨k, hk1, hk2, hyk1, hyk2⟩ := cnt_supp h hy hy0
  rcases le_or_gt k j with hkj | hkj
  · have := cnt_anti h (i := 2 * k) (j := 2 * j) (by omega) (by omega) (by omega)
    rw [abs_sub_comm, abs_of_nonneg (by unfold gapMid at *; linarith)]
    unfold gapMid at *
    linarith
  · have := cnt_anti h (i := 2 * j + 1) (j := 2 * k - 1) (by omega) (by omega) (by omega)
    rw [abs_of_nonneg (by unfold gapMid at *; linarith)]
    unfold gapMid at *
    linarith

/-- At `a_{2p}/2` with `a_{2p} ≥ τ`: `n = M ∧ N` and the distance to `supp ϱ` is `≥ τ/2`. -/
private lemma cnt_bottom {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ)
    (hσ : ∀ j, 0 < σ j) (ha : τ ≤ edgeVal N σ (2 * numBands N σ)) :
    nClass N σ (edgeVal N σ (2 * numBands N σ) / 2) = (min M N : ℕ) ∧
      τ / 2 ≤ Metric.infDist (edgeVal N σ (2 * numBands N σ) / 2) (varrho N σ).support := by
  obtain ⟨hN, hM, hS⟩ := cnt_facts h
  have hτ := h.pos
  have hp := (card_innerCrit N σ h.nonneg hN hS).2
  set p := numBands N σ with hpdef
  set a := edgeVal N σ (2 * p) with hadef
  have ha0 : 0 < a := lt_of_lt_of_le hτ ha
  have hoff : ∀ y ∈ (varrho N σ).support, 0 < y → a ≤ y := by
    intro y hy hy0
    obtain ⟨k, hk1, hk2, hyk1, -⟩ := cnt_supp h hy hy0
    exact (cnt_anti h (i := 2 * k) (j := 2 * p) (by omega) (by omega) le_rfl).trans hyk1
  refine ⟨?_, ?_⟩
  · have e1 := (nClass_edgeVal h (k := p) hp le_rfl).2 ha0
    obtain ⟨hc1, -, -⟩ := cumCount_spec h (k := p) hp le_rfl
    have hsum := (Ni_sum N σ hσ hN hM).2
    have hcm : (cumCount N σ p : ℝ) = ((min M N : ℕ) : ℝ) := by
      rw [hc1, hsum, Nat.cast_min, min_comm]
    have := isProbabilityMeasure_varrho N σ h.nonneg hN
    have hnull : varrho N σ (Set.Ico (a / 2) a) = 0 := by
      refine measure_mono_null (fun y hy => ?_) Measure.measure_compl_support
      intro hys
      have := hoff y hys (by linarith [hy.1])
      linarith [hy.2]
    have hle : nClass N σ (a / 2) ≤ nClass N σ a := by
      unfold nClass
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg N)
      have : varrho N σ (Set.Ici (a / 2)) ≤ varrho N σ (Set.Ico (a / 2) a) +
          varrho N σ (Set.Ici a) := by
        refine (measure_mono fun t ht => ?_).trans (measure_union_le _ _)
        by_cases hta : t < a
        · exact Or.inl ⟨ht, hta⟩
        · exact Or.inr (not_lt.1 hta)
      rw [hnull, zero_add] at this
      exact ENNReal.toReal_mono (measure_ne_top _ _) this
    have hge := cnt_nClass_anti σ h.nonneg hN (show a / 2 ≤ a by linarith)
    rw [← hcm, ← e1]
    linarith
  · have hne : (varrho N σ).support.Nonempty :=
      cnt_supp_ne h (by linarith [cnt_anti h (i := 1) (j := 2 * p) le_rfl (by omega) le_rfl])
    refine (Metric.le_infDist hne).2 fun y hy => ?_
    rw [Real.dist_eq]
    rcases le_or_gt y 0 with hy0 | hy0
    · rw [abs_of_pos (by linarith)]; linarith
    have := hoff y hy hy0
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith

/-! ## The exact-count points -/

/-- `‖Σ‖ ≤ τ⁻¹` under (bound_Sigma) (L2 operator norm). -/
private lemma cnt_norm_sig {τ : ℝ} (hτ : 0 < τ) {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hS : SigmaAssumption τ Sig) : ‖Sig‖ ≤ τ⁻¹ := by
  have hH := hS.posDef.isHermitian
  set U := hH.eigenvectorUnitary with hU
  have hUm : (U : Matrix (Fin M) (Fin M) ℝ) ∈ unitaryGroup (Fin M) ℝ := U.2
  have hUn : ‖(U : Matrix (Fin M) (Fin M) ℝ)‖ ≤ 1 := by
    have h1 : ‖(U : Matrix (Fin M) (Fin M) ℝ)ᴴ * (U : Matrix (Fin M) (Fin M) ℝ)‖ =
        ‖(U : Matrix (Fin M) (Fin M) ℝ)‖ * ‖(U : Matrix (Fin M) (Fin M) ℝ)‖ :=
      l2_opNorm_conjTranspose_mul_self _
    have h2 : (U : Matrix (Fin M) (Fin M) ℝ)ᴴ * (U : Matrix (Fin M) (Fin M) ℝ) = 1 := by
      rw [← star_eq_conjTranspose]; exact (mem_unitaryGroup_iff'.1 hUm)
    have h3 : ‖(1 : Matrix (Fin M) (Fin M) ℝ)‖ ≤ 1 := by
      rw [← diagonal_one, l2_opNorm_diagonal]
      exact pi_norm_le_iff_of_nonneg zero_le_one |>.2 fun _ => by simp
    rw [h2] at h1
    nlinarith [norm_nonneg (U : Matrix (Fin M) (Fin M) ℝ)]
  have hspec := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  rw [hspec]
  have hD : ‖(diagonal (RCLike.ofReal ∘ hH.eigenvalues) : Matrix (Fin M) (Fin M) ℝ)‖ ≤ τ⁻¹ := by
    rw [l2_opNorm_diagonal]
    refine pi_norm_le_iff_of_nonneg (inv_pos.2 hτ).le |>.2 fun i => ?_
    simp only [Function.comp_apply, RCLike.ofReal_real_eq_id, id, Real.norm_eq_abs]
    rw [abs_of_pos (hS.posDef.eigenvalues_pos i)]
    exact hS.eigenvalues_le i
  have hUs : ‖star (U : Matrix (Fin M) (Fin M) ℝ)‖ ≤ 1 := by
    rw [star_eq_conjTranspose, l2_opNorm_conjTranspose]; exact hUn
  calc _ ≤ ‖(U : Matrix (Fin M) (Fin M) ℝ) * diagonal (RCLike.ofReal ∘ hH.eigenvalues)‖ *
        ‖star (U : Matrix (Fin M) (Fin M) ℝ)‖ := l2_opNorm_mul _ _
    _ ≤ (‖(U : Matrix (Fin M) (Fin M) ℝ)‖ * ‖(diagonal (RCLike.ofReal ∘ hH.eigenvalues) :
          Matrix (Fin M) (Fin M) ℝ)‖) * ‖star (U : Matrix (Fin M) (Fin M) ℝ)‖ :=
        mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _)
    _ ≤ (1 * τ⁻¹) * 1 := by gcongr
    _ = τ⁻¹ := by ring

/-- No eigenvalue of `Q_N` is `≥ E` when `E > τ⁻¹ ‖XᵀX‖`. -/
private lemma cnt_eig_top {τ : ℝ} (hτ : 0 < τ) {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hS : SigmaAssumption τ Sig) (Xm : Matrix (Fin M) (Fin N) ℝ) {C₀ E : ℝ}
    (hX : ‖Xmᵀ * Xm‖ ≤ C₀) (hE : τ⁻¹ * C₀ < E) : eigCount (QN Sig Xm) E = 0 := by
  have hH : (QN Sig Xm).IsHermitian := by
    have := isHermitian_conjTranspose_mul_mul Xm hS.posDef.isHermitian
    simpa [QN, conjTranspose_eq_transpose_of_trivial] using this
  refine eigCount_eq_zero_of_norm_lt hH (lt_of_le_of_lt ?_ hE)
  have hT : ‖Xmᵀ‖ = ‖Xm‖ := by
    rw [← conjTranspose_eq_transpose_of_trivial, l2_opNorm_conjTranspose]
  have hTT : ‖Xmᵀ * Xm‖ = ‖Xm‖ * ‖Xm‖ := by
    rw [← conjTranspose_eq_transpose_of_trivial, l2_opNorm_conjTranspose_mul_self]
  calc ‖QN Sig Xm‖ = ‖Xmᵀ * Sig * Xm‖ := rfl
    _ ≤ ‖Xmᵀ‖ * ‖Sig‖ * ‖Xm‖ :=
        (l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _))
    _ = ‖Sig‖ * ‖Xmᵀ * Xm‖ := by rw [hT, hTT]; ring
    _ ≤ τ⁻¹ * C₀ := mul_le_mul (cnt_norm_sig hτ hS) hX (norm_nonneg _) (inv_nonneg.2 hτ.le)

private lemma cnt_hp_mono {Ω : Type*} [MeasureSpace Ω] {N : ℕ} {D : ℝ} {A B : Set Ω}
    (h : HighProbAt N D A) (hAB : A ⊆ B) : HighProbAt N D B :=
  (measure_mono (Set.compl_subset_compl.2 hAB)).trans h

/-- The exact-count point next to a regular edge `a_l`: `E_top` for `l = 1`, the midpoint of the
adjacent gap, or `a_{2p}/2` for `l = 2p`. It lies in `[τ/2, X]` at distance `≥ τ/4` from
`supp ϱ`, and `n_N = n` there with high probability. -/
private lemma cnt_exact (τ : ℝ) (C : ℕ → ℝ) (D Xt : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hXt : 2 * τ⁻¹ * (1 + τ⁻¹) + 1 ≤ Xt)
    (htop : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)] (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (X : Ω → Matrix (Fin M) (Fin N) ℝ), IsModel τ C M N Sig X →
      HighProbAt N D {ω | eigCount (QN Sig (X ω)) Xt = 0}) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (l : ℕ),
      IsModel τ C M N Sig X → RegularEdge τ N (specOf Sig) l →
      ∃ P, P ∈ Set.Icc (τ / 2) Xt ∧
        τ / 4 ≤ Metric.infDist P (varrho N (specOf Sig)).support ∧
        HighProbAt N D {ω | (eigCount (QN Sig (X ω)) P : ℝ) = nClass N (specOf Sig) P} := by
  obtain ⟨N₁, h₁⟩ := htop
  obtain ⟨N₂, h₂⟩ := prop_counting τ C τ D hτ hτ
  obtain ⟨N₃, h₃⟩ := bottom_count τ C τ D hτ hτ
  refine ⟨max N₁ (max N₂ N₃), fun N hN Ω _ _ M Sig X l hm hreg => ?_⟩
  have hda : DensityAssumptions τ N (specOf Sig) := hm.diagModel_specOf.densityAssumptions hτ
  obtain ⟨hN0, -, hS⟩ := cnt_facts hda
  set σ := specOf Sig with hσdef
  have hp := (card_innerCrit N σ hda.nonneg hN0 hS).2
  obtain ⟨hl1, hl2, hla, hsep, -⟩ := hreg
  have hτ8 : τ ≤ 2 * τ⁻¹ * (1 + τ⁻¹) := by
    have : 1 ≤ τ⁻¹ := one_le_inv₀ hτ |>.2 hτ1
    nlinarith
  -- the gap case
  have hgap : ∀ j, 1 ≤ j → j < numBands N σ → τ ≤ edgeVal N σ (2 * j) →
      τ ≤ edgeVal N σ (2 * j) - edgeVal N σ (2 * j + 1) →
      ∃ P, P ∈ Set.Icc (τ / 2) Xt ∧ τ / 4 ≤ Metric.infDist P (varrho N σ).support ∧
        HighProbAt N D {ω | (eigCount (QN Sig (X ω)) P : ℝ) = nClass N σ P} := by
    intro j hj hjp ha hw
    obtain ⟨hn, hd, hlo, hhi⟩ := cnt_gapMid hda hj hjp ha hw
    have hb := (cnt_edge_bd hda (k := 1) le_rfl (by omega)).2
    refine ⟨gapMid N σ j, ⟨hlo, by linarith⟩, by linarith, ?_⟩
    refine cnt_hp_mono (h₂ N (le_of_max_le_left (le_of_max_le_right hN)) M Sig X j hm hj hjp
      ha hw) fun ω hω => ?_
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [hω, hn]
  rcases Nat.even_or_odd' l with ⟨j, rfl | rfl⟩
  · -- `l = 2j`
    rcases lt_or_eq_of_le (show j ≤ numBands N σ by omega) with hjp | hjp
    · refine hgap j (by omega) hjp hla ?_
      have := hsep (2 * j + 1) (by omega) (by omega) (by omega)
      have hle := cnt_anti hda (i := 2 * j) (j := 2 * j + 1) (by omega) (by omega) (by omega)
      rw [abs_of_nonneg (by linarith)] at this
      exact this
    · subst hjp
      have hσpos : ∀ i, 0 < σ i := fun i => by
        rw [hσdef, specOf_eq hm.sigma.posDef.isHermitian]
        exact hm.sigma.posDef.eigenvalues_pos i
      obtain ⟨hn, hd⟩ := cnt_bottom hda hσpos hla
      have hb := cnt_edge_bd hda (k := 2 * numBands N σ) (by omega) le_rfl
      refine ⟨edgeVal N σ (2 * numBands N σ) / 2, ⟨by linarith, by linarith⟩, by linarith, ?_⟩
      refine cnt_hp_mono (h₃ N (le_of_max_le_right (le_of_max_le_right hN)) M Sig X hm hla)
        fun ω hω => ?_
      simp only [Set.mem_ofPred_eq] at hω ⊢
      rw [hω, hn]
  · -- `l = 2j + 1`
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · subst hj0
      refine ⟨Xt, ⟨by linarith, le_rfl⟩, ?_, ?_⟩
      · have hb := cnt_edge_bd hda (k := 1) le_rfl (by omega)
        have hne : (varrho N σ).support.Nonempty := cnt_supp_ne hda (by linarith)
        refine (Metric.le_infDist hne).2 fun y hy => ?_
        rw [Real.dist_eq]
        rcases le_or_gt y 0 with hy0 | hy0
        · rw [abs_of_pos (by linarith)]; linarith
        obtain ⟨k, hk1, hk2, -, hyk⟩ := cnt_supp hda hy hy0
        have := cnt_anti hda (i := 1) (j := 2 * k - 1) le_rfl (by omega) (by omega)
        rw [abs_of_pos (by linarith)]
        linarith
      · have hn := cnt_nClass_top hda (E := Xt)
          (by linarith [(cnt_edge_bd hda (k := 1) le_rfl (by omega)).2])
        refine cnt_hp_mono (h₁ N (le_of_max_le_left hN) M Sig X hm) fun ω hω => ?_
        simp only [Set.mem_ofPred_eq] at hω ⊢
        rw [hω, hn, Nat.cast_zero]
    · have hle := cnt_anti hda (i := 2 * j) (j := 2 * j + 1) (by omega) (by omega) (by omega)
      have hsj := hsep (2 * j) (by omega) (by omega) (by omega)
      rw [abs_of_nonpos (by linarith)] at hsj
      exact hgap j hj0 (by omega) (by linarith) (by linarith)

/-- The top point `E_top = τ⁻¹|C₀| + 2τ⁻¹(1 + τ⁻¹) + 1` (`C₀` of Lemma 4.8): with high
probability no eigenvalue of `Q_N` is `≥ E_top`. -/
private lemma cnt_top_event (τ : ℝ) (C : ℕ → ℝ) (D : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ∃ Xt : ℝ, 2 * τ⁻¹ * (1 + τ⁻¹) + 1 ≤ Xt ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)] (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (X : Ω → Matrix (Fin M) (Fin N) ℝ), IsModel τ C M N Sig X →
      HighProbAt N D {ω | eigCount (QN Sig (X ω)) Xt = 0} := by
  obtain ⟨C₀, hC₀⟩ := norm_XtX_le hτ hτ1
  obtain ⟨N₀, h₀⟩ := hC₀ C D
  refine ⟨τ⁻¹ * |C₀| + 2 * τ⁻¹ * (1 + τ⁻¹) + 1, by
    have : 0 ≤ τ⁻¹ * |C₀| := by positivity
    linarith, max N₀ 1, fun N hN Ω _ _ M Sig X hm => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast le_of_max_le_right hN
  have hMN : (M : ℝ) ≤ τ⁻¹ * N := by
    have := hm.ratio_le
    rwa [div_le_iff₀ (by linarith)] at this
  refine cnt_hp_mono (h₀ N (le_of_max_le_left hN) M X hm.entries hMN) fun ω hω => ?_
  refine cnt_eig_top hτ hm.sigma (X ω) hω ?_
  have h1 : τ⁻¹ * C₀ ≤ τ⁻¹ * |C₀| := mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
  have : 0 ≤ 2 * τ⁻¹ * (1 + τ⁻¹) := by positivity
  linarith

/-- `edgeWin τ` is closed. -/
private lemma cnt_edgeWin_closed (τ : ℝ) (N : ℕ) (σ : Fin M → ℝ) :
    IsClosed (edgeWin τ N σ) := by
  unfold edgeWin
  refine isClosed_Ici.union ?_
  have e : {E | ∃ l, 1 ≤ l ∧ l ≤ 2 * numBands N σ ∧ τ / 2 ≤ edgeVal N σ l ∧
      |E - edgeVal N σ l| ≤ τ / 8} = ⋃ l ∈ Finset.range (2 * numBands N σ + 1),
        {E | 1 ≤ l ∧ l ≤ 2 * numBands N σ ∧ τ / 2 ≤ edgeVal N σ l ∧
          |E - edgeVal N σ l| ≤ τ / 8} := by
    ext E
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range]
    constructor
    · rintro ⟨l, h⟩
      exact ⟨l, by omega, h⟩
    · rintro ⟨l, -, h⟩
      exact ⟨l, h⟩
  rw [e]
  refine isClosed_biUnion_finset fun l _ => ?_
  by_cases hl : 1 ≤ l ∧ l ≤ 2 * numBands N σ ∧ τ / 2 ≤ edgeVal N σ l
  · have e2 : {E | 1 ≤ l ∧ l ≤ 2 * numBands N σ ∧ τ / 2 ≤ edgeVal N σ l ∧
        |E - edgeVal N σ l| ≤ τ / 8} = {E | |E - edgeVal N σ l| ≤ τ / 8} := by
      ext E
      simp only [Set.mem_ofPred_eq]
      exact ⟨fun h => h.2.2.2, fun h => ⟨hl.1, hl.2.1, hl.2.2, h⟩⟩
    rw [e2]
    exact isClosed_le (by fun_prop) continuous_const
  · have e2 : {E | 1 ≤ l ∧ l ≤ 2 * numBands N σ ∧ τ / 2 ≤ edgeVal N σ l ∧
        |E - edgeVal N σ l| ≤ τ / 8} = ∅ := by
      ext E
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hl ⟨h.1, h.2.1, h.2.2.1⟩
    rw [e2]
    exact isClosed_empty

/-- Every `E ∈ edgeWin τ` satisfies `E ≥ 3τ/8`. -/
private lemma cnt_edgeWin_ge {τ : ℝ} (hτ : 0 < τ) {N : ℕ} {σ : Fin M → ℝ} {E : ℝ}
    (hE : E ∈ edgeWin τ N σ) : 3 * τ / 8 ≤ E := by
  rcases hE with h | ⟨l, -, -, hl, hd⟩
  · have : 3 * τ / 4 ≤ E := h
    linarith
  · have := (abs_le.1 hd).1
    linarith

/-- A point `E + iy` with `τ₂ ≤ E ≤ τ₂⁻¹` and `N^{−1+τ₂} ≤ y ≤ τ₂⁻¹` lies in `𝐃(τ₂, N)`. -/
private lemma cnt_mem_spec {τ₂ : ℝ} (hτ₂ : 0 < τ₂) {N : ℕ} (hN : 0 < N) {z : ℂ}
    (h1 : τ₂ ≤ z.re) (h2 : z.re ≤ τ₂⁻¹) (h3 : (N : ℝ) ^ (-1 + τ₂) ≤ z.im) (h4 : z.im ≤ τ₂⁻¹) :
    z ∈ specDomain τ₂ N := by
  have h0 : 0 < z.im := lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast hN) _) h3
  refine ⟨h0, ?_, ?_, h3, h4⟩
  · exact h1.trans ((le_abs_self _).trans (Complex.abs_re_le_norm z))
  · rw [abs_of_pos (lt_of_lt_of_le hτ₂ h1)]; exact h2

/-- The point `x + i`, `0 ≤ x ≤ τ₂⁻¹`, `τ₂ ≤ 1`, lies in the high domain at `τ₂`. -/
private lemma cnt_mem_high {τ₂ : ℝ} (hτ₂ : 0 < τ₂) (hτ₂1 : τ₂ ≤ 1) {N : ℕ} (hN : 1 ≤ N)
    {z : ℂ} (h1 : 0 ≤ z.re) (h2 : z.re ≤ τ₂⁻¹) (h3 : z.im = 1) : z ∈ highDomain τ₂ N := by
  have hi : 1 ≤ τ₂⁻¹ := one_le_inv₀ hτ₂ |>.2 hτ₂1
  refine ⟨⟨by rw [h3]; exact one_pos, ?_, by rw [abs_of_nonneg h1]; exact h2, ?_,
    by rw [h3]; exact hi⟩, by rw [h3]; linarith⟩
  · have := Complex.abs_im_le_norm z
    rw [h3, abs_one] at this
    linarith
  · rw [h3]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by linarith)

/-- `τ'(τ) ≤ τ/2` for `τ ∈ (0, 1]`. -/
private lemma cnt_edgeTau'_le {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) : edgeTau' τ ≤ τ / 2 := by
  have hs := Real.sqrt_pos.2 hτ
  have hcx : 0 < edgecx τ := by unfold edgecx; positivity
  have h2 : 0 < edgec2 τ := by unfold edgec2 edgeCx; positivity
  have h3 : 0 < edgeC3 τ := by unfold edgeC3; positivity
  have h0 : 0 < edgeRho0 τ := by unfold edgeRho0; positivity
  have h1 : 0 < edgeRho1 τ := by unfold edgeRho1; positivity
  have h10 : edgeRho1 τ ≤ edgeRho0 τ := min_le_left _ _
  have h1τ : edgeRho1 τ ≤ τ / 2 := by
    refine h10.trans ?_
    unfold edgeRho0; linarith [min_le_right (edgecx τ) τ]
  have hc2τ : edgec2 τ ≤ τ ^ 3 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have heq : edgeTau' τ = edgec2 τ * edgeRho1 τ ^ 2 / 32 := by
    unfold edgeTau' edgeTau0; ring
  rw [heq]
  have hsq : edgeRho1 τ ^ 2 ≤ (τ / 2) ^ 2 := pow_le_pow_left₀ h1.le h1τ 2
  have hmul : edgec2 τ * edgeRho1 τ ^ 2 ≤ τ ^ 3 / 4 * (τ / 2) ^ 2 :=
    mul_le_mul hc2τ hsq (sq_nonneg _) (by positivity)
  have hτ4 : τ ^ 4 ≤ 1 := pow_le_one₀ hτ.le hτ1
  nlinarith

/-! ## The counting estimates -/

/-- Under the hypotheses of Theorem 3.12 (every edge with `a_k ≥ τ/2` regular at `τ/2`): `|n_N(E) − n(E)| ≤ N^ε` for all
`E ∈ edgeWin τ`. -/
theorem count_edgeWin (τ : ℝ) (C : ℕ → ℝ) (c : ℝ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ),
      IsModel τ C M N Sig X →
      (∀ k, 1 ≤ k → k ≤ 2 * numBands N (specOf Sig) → τ / 2 ≤ edgeVal N (specOf Sig) k →
        RegularEdge (τ / 2) N (specOf Sig) k) →
      (∀ k, 1 ≤ k → k ≤ numBands N (specOf Sig) → RegularBulk c N (specOf Sig) k) →
      HighProbAt N D {ω | ∀ E ∈ edgeWin τ N (specOf Sig),
        |(eigCount (QN Sig (X ω)) E : ℝ) - nClass N (specOf Sig) E| ≤ (N : ℝ) ^ ε} := by
  by_cases hτ1 : τ ≤ 1
  swap
  · exact ⟨0, fun N _ Ω _ _ M Sig X hm _ _ => absurd hm.tau_le_one hτ1⟩
  obtain ⟨Xt, hXt, N₃, h₃⟩ := cnt_top_event τ C (D + 1) hτ hτ1
  have hXt1 : 1 ≤ Xt := by
    have : 0 ≤ 2 * τ⁻¹ * (1 + τ⁻¹) := by positivity
    linarith
  have hXt0 : 0 ≤ Xt := by linarith
  set a := min ε 1 / 4 with ha_def
  have ha : 0 < a := by rw [ha_def]; have := lt_min hε one_pos; linarith
  set τ₂ := min (min (τ / 4) a) (1 / (Xt + 2)) with hτ₂_def
  have hτ₂0 : 0 < τ₂ := lt_min (lt_min (by linarith) ha) (by positivity)
  have hτ₂τ : τ₂ ≤ τ / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have hτ₂a : τ₂ ≤ a := (min_le_left _ _).trans (min_le_right _ _)
  have hτ₂X : Xt + 2 ≤ τ₂⁻¹ := by
    have h := min_le_right (min (τ / 4) a) (1 / (Xt + 2))
    rw [← hτ₂_def] at h
    rw [le_inv_comm₀ (by positivity) hτ₂0]
    simpa using h
  have hτ₂1 : τ₂ ≤ 1 := by linarith
  obtain ⟨N₁, h₁⟩ := LL_G_low τ τ₂ C c a (D + 8) hτ₂0 (by linarith) ha
  obtain ⟨N₂, h₂⟩ := high_law τ₂ C a (D + 8) hτ₂0 ha
  obtain ⟨N₄, h₄⟩ := cnt_window τ₂ ε D Xt hτ₂0 hε hXt0 hτ₂X
  refine ⟨max (max N₁ N₂) (max N₃ (max N₄ 1)), fun N hN Ω _ _ M Sig X hm hedge hbulk => ?_⟩
  have hNA : max N₁ N₂ ≤ N := le_of_max_le_left hN
  have hNB : max N₃ (max N₄ 1) ≤ N := le_of_max_le_right hN
  have hN1 : 1 ≤ N := le_of_max_le_right (le_of_max_le_right hNB)
  have hN0 : 0 < N := hN1
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  set σ := specOf Sig with hσdef
  have hdaτ : DensityAssumptions τ N σ := hm.diagModel_specOf.densityAssumptions hτ
  have hm2 : IsModel τ₂ C M N Sig X := hm.mono hτ₂0 (by linarith)
  have hda2 : DensityAssumptions τ₂ N σ := hm2.diagModel_specOf.densityAssumptions hτ₂0
  obtain ⟨hNf, -, hSf⟩ := cnt_facts hdaτ
  have hp := (card_innerCrit N σ hdaτ.nonneg hNf hSf).2
  have ha1 := (cnt_edge_bd hdaτ (k := 1) le_rfl (by omega)).2
  have hnXt : nClass N σ Xt = 0 := cnt_nClass_top hdaτ (by linarith)
  have hηle : (N : ℝ) ^ (-1 + τ₂) ≤ (N : ℝ) ^ (-1 + a) :=
    Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
  set W := edgeWin τ N σ ∩ Set.Icc (3 * τ / 8) Xt with hW
  have hWc : IsClosed W := (cnt_edgeWin_closed τ N σ).inter isClosed_Icc
  have hWX : W ⊆ Set.Icc τ₂ Xt := fun e he => ⟨by linarith [he.2.1], he.2.2⟩
  have hP : Xt ∈ Set.Icc τ₂ Xt := ⟨by linarith, le_rfl⟩
  have hlaw : ∀ z : ℂ, ((z.re ∈ W ∨ z.re = Xt) ∧
        z.im ∈ Set.Icc ((N : ℝ) ^ (-1 + min ε 1 / 4)) 2) ∨
        (z.re ∈ Set.Icc 0 (Xt + 1) ∧ z.im = 1) →
      ODomAt N (min ε 1 / 4) (D + 8) (fun ω => mN Sig (X ω) z - mFun N σ z)
        (fun _ => 1 / (N * z.im)) := by
    intro z hz
    rcases hz with ⟨hre, him⟩ | ⟨hre, him⟩
    · have hwin : z.re ∈ edgeWin τ N σ ∧ 3 * τ / 8 ≤ z.re ∧ z.re ≤ Xt := by
        rcases hre with h | h
        · exact ⟨h.1, h.2.1, h.2.2⟩
        · rw [h]
          refine ⟨Or.inl (?_ : 3 * τ / 4 ≤ Xt), by linarith, le_rfl⟩
          linarith
      have hz : z ∈ lowDomain τ τ₂ N σ :=
        ⟨cnt_mem_spec hτ₂0 hN0 (by linarith [hwin.2.1]) (by linarith [hwin.2.2])
          (hηle.trans him.1) (by linarith [him.2]), hwin.1⟩
      exact h₁ N (le_of_max_le_left hNA) M Sig X hm hedge hbulk z hz
    · have hz : z ∈ highDomain τ₂ N :=
        cnt_mem_high hτ₂0 hτ₂1 hN1 hre.1 (by linarith [hre.2]) him
      exact (h₂ N (le_of_max_le_right hNA) M Sig X hm2).2 z hz
  have hexact : HighProbAt N (D + 1)
      {ω | (eigCount (QN Sig (X ω)) Xt : ℝ) = nClass N σ Xt} := by
    refine cnt_hp_mono (h₃ N (le_of_max_le_left hNB) M Sig X hm) fun ω hω => ?_
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [hω, hnXt, Nat.cast_zero]
  have hwin := h₄ N (le_of_max_le_left (le_of_max_le_right hNB)) M Sig X W Xt
    hm.sigma.posDef hda2 hWc hWX hP hlaw hexact
  refine cnt_hp_mono hwin fun ω hω => ?_
  simp only [Set.mem_ofPred_eq] at hω ⊢
  intro E hE
  rcases le_or_gt E Xt with hEX | hEX
  · exact hω.2 E ⟨hE, cnt_edgeWin_ge hτ hE, hEX⟩
  · have h1 := eigCount_antitone (QN Sig (X ω)) hEX.le
    have h2 : (eigCount (QN Sig (X ω)) Xt : ℝ) = 0 := by rw [hω.1, hnXt]
    have h3 : (eigCount (QN Sig (X ω)) E : ℝ) = 0 := by
      have : eigCount (QN Sig (X ω)) Xt = 0 := by exact_mod_cast h2
      rw [this] at h1
      exact_mod_cast Nat.le_zero.1 h1
    rw [h3, cnt_nClass_top hdaτ (by linarith), sub_zero, abs_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg N) _

/-- Near a regular edge `k` (window `τ'(τ) = edgeTau' τ`): `|n_N(E) − n(E)| ≤ N^ε`. -/
theorem count_edge (τ : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (k : ℕ),
      IsModel τ C M N Sig X → RegularEdge τ N (specOf Sig) k →
      HighProbAt N D {ω | ∀ E ∈ Set.Icc (edgeVal N (specOf Sig) k - edgeTau' τ)
          (edgeVal N (specOf Sig) k + edgeTau' τ),
        |(eigCount (QN Sig (X ω)) E : ℝ) - nClass N (specOf Sig) E| ≤ (N : ℝ) ^ ε} := by
  by_cases hτ1 : τ ≤ 1
  swap
  · exact ⟨0, fun N _ Ω _ _ M Sig X k hm _ => absurd hm.tau_le_one hτ1⟩
  obtain ⟨Xt, hXt, htop⟩ := cnt_top_event τ C (D + 1) hτ hτ1
  have hτi : 0 ≤ 2 * τ⁻¹ * (1 + τ⁻¹) := by positivity
  have hXt0 : 0 ≤ Xt := by linarith
  set a := min ε 1 / 4 with ha_def
  have ha : 0 < a := by rw [ha_def]; have := lt_min hε one_pos; linarith
  set τ₂ := min (min (τ / 4) a) (1 / (Xt + 2)) with hτ₂_def
  have hτ₂0 : 0 < τ₂ := lt_min (lt_min (by linarith) ha) (by positivity)
  have hτ₂τ : τ₂ ≤ τ / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have hτ₂a : τ₂ ≤ a := (min_le_left _ _).trans (min_le_right _ _)
  have hτ₂X : Xt + 2 ≤ τ₂⁻¹ := by
    have h := min_le_right (min (τ / 4) a) (1 / (Xt + 2))
    rw [← hτ₂_def] at h
    rw [le_inv_comm₀ (by positivity) hτ₂0]
    simpa using h
  have hτ₂1 : τ₂ ≤ 1 := by linarith
  have hw0 := edgeTau'_pos hτ
  have hw := cnt_edgeTau'_le hτ hτ1
  obtain ⟨N₁, h₁⟩ := edge_law' τ τ₂ (edgeTau' τ) C a (D + 8) hτ₂0 (by linarith) hw0 le_rfl ha
  obtain ⟨N₂, h₂⟩ := outside_law τ₂ (τ / 4) C a (D + 8) hτ₂0 (by linarith) ha
  obtain ⟨N₃, h₃⟩ := high_law τ₂ C a (D + 8) hτ₂0 ha
  obtain ⟨N₄, h₄⟩ := cnt_window τ₂ ε D Xt hτ₂0 hε hXt0 hτ₂X
  obtain ⟨N₅, h₅⟩ := cnt_exact τ C (D + 1) Xt hτ hτ1 hXt htop
  refine ⟨max (max N₁ N₂) (max (max N₃ N₄) (max N₅ 1)),
    fun N hN Ω _ _ M Sig X k hm hk => ?_⟩
  have hNA : max N₁ N₂ ≤ N := le_of_max_le_left hN
  have hNB : max N₃ N₄ ≤ N := le_of_max_le_left (le_of_max_le_right hN)
  have hNC : max N₅ 1 ≤ N := le_of_max_le_right (le_of_max_le_right hN)
  have hN1 : 1 ≤ N := le_of_max_le_right hNC
  have hN0 : 0 < N := hN1
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  set σ := specOf Sig with hσdef
  have hdaτ : DensityAssumptions τ N σ := hm.diagModel_specOf.densityAssumptions hτ
  have hm2 : IsModel τ₂ C M N Sig X := hm.mono hτ₂0 (by linarith)
  have hda2 : DensityAssumptions τ₂ N σ := hm2.diagModel_specOf.densityAssumptions hτ₂0
  obtain ⟨P, hP, hPd, hPex⟩ := h₅ N (le_of_max_le_left hNC) M Sig X k hm hk
  have hak := hk.2.2.1
  have hakb := (cnt_edge_bd hdaτ hk.1 hk.2.1).2
  have hηle : (N : ℝ) ^ (-1 + τ₂) ≤ (N : ℝ) ^ (-1 + a) :=
    Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
  set W := Set.Icc (edgeVal N σ k - edgeTau' τ) (edgeVal N σ k + edgeTau' τ) with hW
  have hWX : W ⊆ Set.Icc τ₂ Xt := fun e he => ⟨by linarith [he.1], by linarith [he.2]⟩
  have hP' : P ∈ Set.Icc τ₂ Xt := ⟨by linarith [hP.1], hP.2⟩
  have hlaw : ∀ z : ℂ, ((z.re ∈ W ∨ z.re = P) ∧
        z.im ∈ Set.Icc ((N : ℝ) ^ (-1 + min ε 1 / 4)) 2) ∨
        (z.re ∈ Set.Icc 0 (Xt + 1) ∧ z.im = 1) →
      ODomAt N (min ε 1 / 4) (D + 8) (fun ω => mN Sig (X ω) z - mFun N σ z)
        (fun _ => 1 / (N * z.im)) := by
    intro z hz
    rcases hz with ⟨hre, him⟩ | ⟨hre, him⟩
    · rcases hre with hre | hre
      · have hz : z ∈ edgeDomain τ₂ (edgeTau' τ) N σ k :=
          ⟨cnt_mem_spec hτ₂0 hN0 (hWX hre).1 (by linarith [(hWX hre).2]) (hηle.trans him.1)
            (by linarith [him.2]), hre⟩
        exact (h₁ N (le_of_max_le_left hNA) M Sig X k hm hk).2 z hz
      · have hz : z ∈ outsideDomain τ₂ (τ / 4) N σ :=
          ⟨cnt_mem_spec hτ₂0 hN0 (by rw [hre]; exact hP'.1) (by rw [hre]; linarith [hP'.2])
            (hηle.trans him.1) (by linarith [him.2]), by rw [hre]; exact hPd⟩
        exact (h₂ N (le_of_max_le_right hNA) M Sig X hm2).2 z hz
    · have hz : z ∈ highDomain τ₂ N :=
        cnt_mem_high hτ₂0 hτ₂1 hN1 hre.1 (by linarith [hre.2]) him
      exact (h₃ N (le_of_max_le_left hNB) M Sig X hm2).2 z hz
  have hwin := h₄ N (le_of_max_le_right hNB) M Sig X W P hm.sigma.posDef hda2 isClosed_Icc
    hWX hP' hlaw hPex
  exact cnt_hp_mono hwin fun ω hω => hω.2

/-- In a regular bulk component `k` with one regular edge: `|n_N(E) − n(E)| ≤ N^ε`. -/
theorem count_bulk (τ τ' : ℝ) (c : ℝ → ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hτ' : 0 < τ')
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (k : ℕ),
      IsModel τ C M N Sig X → RegularBulk c N (specOf Sig) k →
      (RegularEdge τ N (specOf Sig) (2 * k) ∨ RegularEdge τ N (specOf Sig) (2 * k - 1)) →
      HighProbAt N D {ω | ∀ E ∈ Set.Icc (edgeVal N (specOf Sig) (2 * k) + τ')
          (edgeVal N (specOf Sig) (2 * k - 1) - τ'),
        |(eigCount (QN Sig (X ω)) E : ℝ) - nClass N (specOf Sig) E| ≤ (N : ℝ) ^ ε} := by
  by_cases hτ1 : τ ≤ 1
  swap
  · exact ⟨0, fun N _ Ω _ _ M Sig X k hm _ _ => absurd hm.tau_le_one hτ1⟩
  obtain ⟨Xt, hXt, htop⟩ := cnt_top_event τ C (D + 1) hτ hτ1
  have hτi : 0 ≤ 2 * τ⁻¹ * (1 + τ⁻¹) := by positivity
  have hXt0 : 0 ≤ Xt := by linarith
  set a := min ε 1 / 4 with ha_def
  have ha : 0 < a := by rw [ha_def]; have := lt_min hε one_pos; linarith
  set τ₂ := min (min (min (τ / 4) a) (1 / (Xt + 2))) τ' with hτ₂_def
  have hτ₂0 : 0 < τ₂ := lt_min (lt_min (lt_min (by linarith) ha) (by positivity)) hτ'
  have hτ₂τ : τ₂ ≤ τ / 4 := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hτ₂a : τ₂ ≤ a := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hτ₂τ' : τ₂ ≤ τ' := min_le_right _ _
  have hτ₂X : Xt + 2 ≤ τ₂⁻¹ := by
    have h : τ₂ ≤ 1 / (Xt + 2) := (min_le_left _ _).trans (min_le_right _ _)
    rw [le_inv_comm₀ (by positivity) hτ₂0]
    simpa using h
  have hτ₂1 : τ₂ ≤ 1 := by linarith
  obtain ⟨N₁, h₁⟩ := bulk_law τ₂ τ' c C a (D + 8) hτ₂0 hτ' ha
  obtain ⟨N₂, h₂⟩ := outside_law τ₂ (τ / 4) C a (D + 8) hτ₂0 (by linarith) ha
  obtain ⟨N₃, h₃⟩ := high_law τ₂ C a (D + 8) hτ₂0 ha
  obtain ⟨N₄, h₄⟩ := cnt_window τ₂ ε D Xt hτ₂0 hε hXt0 hτ₂X
  obtain ⟨N₅, h₅⟩ := cnt_exact τ C (D + 1) Xt hτ hτ1 hXt htop
  refine ⟨max (max N₁ N₂) (max (max N₃ N₄) (max N₅ 1)),
    fun N hN Ω _ _ M Sig X k hm hb hreg => ?_⟩
  have hNA : max N₁ N₂ ≤ N := le_of_max_le_left hN
  have hNB : max N₃ N₄ ≤ N := le_of_max_le_left (le_of_max_le_right hN)
  have hNC : max N₅ 1 ≤ N := le_of_max_le_right (le_of_max_le_right hN)
  have hN1 : 1 ≤ N := le_of_max_le_right hNC
  have hN0 : 0 < N := hN1
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  set σ := specOf Sig with hσdef
  have hdaτ : DensityAssumptions τ N σ := hm.diagModel_specOf.densityAssumptions hτ
  have hm2 : IsModel τ₂ C M N Sig X := hm.mono hτ₂0 (by linarith)
  have hda2 : DensityAssumptions τ₂ N σ := hm2.diagModel_specOf.densityAssumptions hτ₂0
  obtain ⟨l, hl⟩ : ∃ l, RegularEdge τ N σ l := by
    rcases hreg with h | h
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩
  obtain ⟨P, hP, hPd, hPex⟩ := h₅ N (le_of_max_le_left hNC) M Sig X l hm hl
  have hk1 := hb.1
  have hkp := hb.2.1
  have hlow := (cnt_edge_bd hdaτ (k := 2 * k) (by omega) (by omega)).1
  have hupp := (cnt_edge_bd hdaτ (k := 2 * k - 1) (by omega) (by omega)).2
  have hηle : (N : ℝ) ^ (-1 + τ₂) ≤ (N : ℝ) ^ (-1 + a) :=
    Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
  set W := Set.Icc (edgeVal N σ (2 * k) + τ') (edgeVal N σ (2 * k - 1) - τ') with hW
  have hWX : W ⊆ Set.Icc τ₂ Xt := fun e he => ⟨by linarith [he.1], by linarith [he.2]⟩
  have hP' : P ∈ Set.Icc τ₂ Xt := ⟨by linarith [hP.1], hP.2⟩
  have hlaw : ∀ z : ℂ, ((z.re ∈ W ∨ z.re = P) ∧
        z.im ∈ Set.Icc ((N : ℝ) ^ (-1 + min ε 1 / 4)) 2) ∨
        (z.re ∈ Set.Icc 0 (Xt + 1) ∧ z.im = 1) →
      ODomAt N (min ε 1 / 4) (D + 8) (fun ω => mN Sig (X ω) z - mFun N σ z)
        (fun _ => 1 / (N * z.im)) := by
    intro z hz
    rcases hz with ⟨hre, him⟩ | ⟨hre, him⟩
    · rcases hre with hre | hre
      · have hz : z ∈ bulkDomain τ₂ τ' N σ k :=
          ⟨cnt_mem_spec hτ₂0 hN0 (hWX hre).1 (by linarith [(hWX hre).2]) (hηle.trans him.1)
            (by linarith [him.2]), hre⟩
        exact (h₁ N (le_of_max_le_left hNA) M Sig X k hm2 hb).2 z hz
      · have hz : z ∈ outsideDomain τ₂ (τ / 4) N σ :=
          ⟨cnt_mem_spec hτ₂0 hN0 (by rw [hre]; exact hP'.1) (by rw [hre]; linarith [hP'.2])
            (hηle.trans him.1) (by linarith [him.2]), by rw [hre]; exact hPd⟩
        exact (h₂ N (le_of_max_le_right hNA) M Sig X hm2).2 z hz
    · have hz : z ∈ highDomain τ₂ N :=
        cnt_mem_high hτ₂0 hτ₂1 hN1 hre.1 (by linarith [hre.2]) him
      exact (h₃ N (le_of_max_le_left hNB) M Sig X hm2).2 z hz
  have hwin := h₄ N (le_of_max_le_right hNB) M Sig X W P hm.sigma.posDef hda2 isClosed_Icc
    hWX hP' hlaw hPex
  exact cnt_hp_mono hwin fun ω hω => hω.2

/-! ## Instances

The Marchenko–Pastur model: Gaussian `X`, `Σ = I_n`, `M = n`, `N = 2n` (`φ = 1/2`), `τ = 1/5`,
`C = gaussMoment`; the model hypothesis is discharged for every `n ≥ 1`. The edge and bulk
regularity hypotheses are kept as binders (conditional instances). They hold together at this
model: `p = 1`, `a_1 = (1 + √(1/2))² ≈ 2.914`, `a_2 = (1 − √(1/2))² ≈ 0.086`, `x_1 = √2 − 2`,
so `a_1 ≥ 1/5`, `a_1 − a_2 ≈ 2.83` and `|x_1 + 1| ≈ 0.414`; the density
`ρ(x) = √((a_1 − x)(x − a_2))/(2πx)` satisfies `ρ ≥ √(min(t, 1))/20` on `[a_2 + t, a_1 − t]`
(for instance `min ρ ≈ 0.0092` at `t = 0.01` and `≈ 0.112` at `t = 1`). -/

end Anisotropic

#print axioms Anisotropic.count_edgeWin
#print axioms Anisotropic.count_edge
#print axioms Anisotropic.count_bulk
