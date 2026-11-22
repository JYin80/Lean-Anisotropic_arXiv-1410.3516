module

public import Anisotropic.Density.Boundary
public import Anisotropic.Density.GenProp
public import Anisotropic.Density.Ordering
public import Anisotropic.Density.Structure
public import Anisotropic.Density.Varrho
public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.GeneralT.Limit
public import Anisotropic.GeneralT.Spectra
public import Anisotropic.Rigidity.Defs
public import Anisotropic.Rigidity.Segment

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # Support, masses and classical locations of `Ŝ + κ P₀` as `κ ↓ 0` -/

/-! ## The measure `ϱ` and the counting function `n` -/

/-- `ϱ(A) = ∫_A ρ` for measurable `A ⊆ (0, ∞)`. -/
private lemma masses_varrho_apply (N : ℕ) (σ : Fin M → ℝ) {A : Set ℝ} (hA : MeasurableSet A)
    (hsub : A ⊆ Set.Ioi 0) :
    varrho N σ A = ∫⁻ x in A, ENNReal.ofReal (rhoDens N σ x) := by
  have h0 : (0 : ℝ) ∉ A := fun h => lt_irrefl (0 : ℝ) (Set.mem_Ioi.mp (hsub h))
  rw [varrho, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hA,
    Set.indicator_of_notMem h0, smul_zero, zero_add, withDensity_apply _ hA,
    Measure.restrict_restrict hA, Set.inter_eq_left.mpr hsub]

/-- `ϱ((−∞, 0)) = 0`. -/
private lemma masses_varrho_Iio (N : ℕ) (σ : Fin M → ℝ) : varrho N σ (Set.Iio 0) = 0 := by
  have h0 : (0 : ℝ) ∉ Set.Iio 0 := fun h => lt_irrefl (0 : ℝ) h
  rw [varrho, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ measurableSet_Iio,
    Set.indicator_of_notMem h0, smul_zero, zero_add, withDensity_apply _ measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio]
  have he : Set.Iio (0 : ℝ) ∩ Set.Ioi 0 = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi, Set.mem_empty_iff_false, iff_false,
      not_and, not_lt]
    intro h
    exact h.le
  rw [he, Measure.restrict_empty, lintegral_zero_measure]

private lemma masses_continuousOn_rhoDens (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) :
    ContinuousOn (rhoDens N σ) (Set.Ioi 0) := by
  have h1 : ContinuousOn (fun x : ℝ => mExt N σ x) (Set.Ioi 0) :=
    (continuousOn_mExt N σ hσ).comp Complex.continuous_ofReal.continuousOn
      (fun x hx => Or.inr ⟨Complex.ofReal_im x, Complex.ofReal_ne_zero.mpr (ne_of_gt hx)⟩)
  exact (Complex.continuous_im.comp_continuousOn h1).div_const _

/-- `n` is nonincreasing. -/
private lemma masses_nClass_anti {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) :
    Antitone (nClass N σ) := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  intro x y hxy
  exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono (Set.Ici_subset_Ici.mpr hxy))) (Nat.cast_nonneg N)

private lemma masses_nClass_lip {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {a b : ℝ}
    (ha : 0 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, x ≤ y →
      nClass N σ x - nClass N σ y ≤ K * (y - x) := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun x hx => lt_of_lt_of_le ha hx.1
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image
    ((masses_continuousOn_rhoDens N σ hσ).mono hsub)
  refine ⟨N * max B 0, by positivity, fun x hx y hy hxy => ?_⟩
  have hsplit : varrho N σ (Set.Ici x) = varrho N σ (Set.Ico x y) + varrho N σ (Set.Ici y) := by
    rw [← measure_union _ measurableSet_Ici, Set.Ico_union_Ici_eq_Ici hxy]
    rw [Set.disjoint_left]
    intro z hz1 hz2
    exact absurd hz1.2 (not_lt.mpr hz2)
  have hIco : varrho N σ (Set.Ico x y) ≤ ENNReal.ofReal (max B 0 * (y - x)) := by
    have hsub' : Set.Ico x y ⊆ Set.Icc a b := fun z hz => ⟨hx.1.trans hz.1, hz.2.le.trans hy.2⟩
    rw [masses_varrho_apply N σ measurableSet_Ico (hsub'.trans hsub)]
    calc ∫⁻ z in Set.Ico x y, ENNReal.ofReal (rhoDens N σ z)
        ≤ ∫⁻ z in Set.Ico x y, ENNReal.ofReal (max B 0) := by
          refine setLIntegral_mono' measurableSet_Ico fun z hz => ?_
          exact ENNReal.ofReal_le_ofReal
            ((hB ⟨z, hsub' hz, rfl⟩).trans (le_max_left _ _))
      _ = ENNReal.ofReal (max B 0 * (y - x)) := by
          rw [setLIntegral_const, Real.volume_Ico, ← ENNReal.ofReal_mul (le_max_right _ _)]
  have hc : 0 ≤ max B 0 * (y - x) := mul_nonneg (le_max_right _ _) (by linarith)
  have h1 : (varrho N σ (Set.Ico x y)).toReal ≤ max B 0 * (y - x) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hIco
    rwa [ENNReal.toReal_ofReal hc] at this
  have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (α := ℝ) N)
  unfold nClass
  rw [hsplit, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  linarith

/-- `n` is continuous on `(0, ∞)`. -/
private lemma masses_nClass_continuousOn {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) :
    ContinuousOn (nClass N σ) (Set.Ioi 0) := by
  intro E0 hE0
  have hE0' : (0 : ℝ) < E0 := hE0
  have hmem : Set.Icc (E0 / 2) (2 * E0) ∈ 𝓝 E0 :=
    Icc_mem_nhds (by linarith) (by linarith)
  obtain ⟨K, hK0, hK⟩ := masses_nClass_lip (σ := σ) hσ hN (a := E0 / 2) (b := 2 * E0)
    (by linarith)
  have hanti := masses_nClass_anti (σ := σ) hσ hN
  have hlip : LipschitzOnWith K.toNNReal (nClass N σ) (Set.Icc (E0 / 2) (2 * E0)) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hK0]
    rcases le_total x y with hxy | hxy
    · have h1 := hK x hx y hy hxy
      have h2 := hanti hxy
      rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
      linarith
    · have h1 := hK y hy x hx hxy
      have h2 := hanti hxy
      rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
      linarith
  exact (hlip.continuousOn.continuousAt hmem).continuousWithinAt

/-- `n(x) − n(y) = N ϱ([x, y))` for `x ≤ y`. -/
private lemma masses_nClass_sub {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {x y : ℝ}
    (hxy : x ≤ y) :
    nClass N σ x - nClass N σ y = N * (varrho N σ (Set.Ico x y)).toReal := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  have hsplit : varrho N σ (Set.Ici x) = varrho N σ (Set.Ico x y) + varrho N σ (Set.Ici y) := by
    rw [← measure_union _ measurableSet_Ici, Set.Ico_union_Ici_eq_Ici hxy]
    rw [Set.disjoint_left]
    intro z hz1 hz2
    exact absurd hz1.2 (not_lt.mpr hz2)
  unfold nClass
  rw [hsplit, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  ring

/-! ## `m` on the real line away from `supp ϱ` -/

private lemma masses_inv_im (t x y : ℝ) :
    (((t : ℂ) - (↑x + ↑y * Complex.I))⁻¹).im = y / ((t - x) ^ 2 + y ^ 2) := by
  rw [Complex.inv_im, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.add_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, Complex.sub_im, Complex.add_im, Complex.mul_im]
  ring

private lemma masses_integrable_inv (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {z : ℂ}
    (hz : 0 < z.im) : Integrable (fun t : ℝ => ((t : ℂ) - z)⁻¹) (varrho N σ) := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  have hne : ∀ t : ℝ, (t : ℂ) - z ≠ 0 := fun t h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  refine Integrable.of_bound ?_ (z.im)⁻¹ (ae_of_all _ fun t => ?_)
  · exact ((Complex.continuous_ofReal.sub continuous_const).inv₀ hne).aestronglyMeasurable
  · rw [norm_inv]
    refine inv_anti₀ hz ?_
    have h := Complex.abs_im_le_norm ((t : ℂ) - z)
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] at h
    exact le_trans (le_abs_self _) h

/-- `Im m(x + iy) = ∫ y / ((t − x)² + y²) dϱ(t)` for `y > 0`. -/
private lemma masses_im_mFun_eq (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) (x : ℝ)
    {y : ℝ} (hy : 0 < y) :
    (mFun N σ (↑x + ↑y * Complex.I)).im = ∫ t, y / ((t - x) ^ 2 + y ^ 2) ∂(varrho N σ) := by
  have hz : 0 < ((x : ℂ) + ↑y * Complex.I).im := by simpa using hy
  have hrep : mFun N σ (↑x + ↑y * Complex.I) =
      ∫ t : ℝ, ((t : ℂ) - (↑x + ↑y * Complex.I))⁻¹ ∂(varrho N σ) := by
    rw [← resolventTransform_varrho N σ hσ hN hz, resolventTransform_apply]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp [resolvent, Ring.inverse_eq_inv']
  rw [hrep]
  have := integral_im (𝕜 := ℂ) (masses_integrable_inv σ hσ hN hz)
  simp only [RCLike.im_to_complex] at this
  rw [← this]
  simp_rw [masses_inv_im]

/-- `Im m(y + iη) ≤ η / d²` when `y` is at distance `≥ d` from `supp ϱ`. -/
private lemma masses_im_mFun_le {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {y d : ℝ}
    (hd : 0 < d) (hs : ∀ s ∈ (varrho N σ).support, d ≤ |s - y|) {η : ℝ} (hη : 0 < η) :
    (mFun N σ (↑y + ↑η * Complex.I)).im ≤ η / d ^ 2 := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  rw [masses_im_mFun_eq σ hσ hN y hη]
  calc ∫ t, η / ((t - y) ^ 2 + η ^ 2) ∂(varrho N σ) ≤ ∫ _t, η / d ^ 2 ∂(varrho N σ) := by
        refine integral_mono_of_nonneg (ae_of_all _ fun t => by positivity) (integrable_const _)
          ?_
        filter_upwards [Measure.support_mem_ae (μ := varrho N σ)] with t ht
        have h1 := hs t ht
        have h2 : d ^ 2 ≤ (t - y) ^ 2 := by
          rw [← sq_abs (t - y)]
          exact pow_le_pow_left₀ hd.le h1 2
        exact div_le_div_of_nonneg_left hη.le (by positivity) (by nlinarith)
    _ = η / d ^ 2 := by simp

private lemma masses_tendsto_line (y : ℝ) :
    Tendsto (fun η : ℝ => (y : ℂ) + η * Complex.I) (𝓝[>] 0) (𝓝[upperHalf] (y : ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have : Tendsto (fun η : ℝ => (y : ℂ) + η * Complex.I) (𝓝 0)
        (𝓝 ((y : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)) :=
      ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).tendsto 0)
    simpa using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with η hη
    change 0 < ((y : ℂ) + η * Complex.I).im
    simpa using hη

private lemma masses_norm_real_sq (r : ℝ) : ‖(r : ℂ)‖ ^ 2 = r ^ 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- `f(w) w = −1 + N⁻¹ Σ_i σ_i w / (1 + σ_i w)` for `w ≠ 0`. -/
private lemma masses_fC_mul {σ : Fin M → ℝ} {w : ℂ} (hw : w ≠ 0) :
    fC N σ w * w = -1 + ∑ i, (σ i : ℂ) * w / (N * (1 + σ i * w)) := by
  unfold fC
  rw [add_mul, Finset.sum_mul, neg_mul, inv_mul_cancel₀ hw]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [div_mul_eq_mul_div]

/-- At a point `y ≠ 0` at distance `≥ d > 0` from `supp ϱ`, `m(y)` is a real number `x`, with
`x ≠ 0`, `1 + σ_i x ≠ 0`, `f(x) = y` and `f'(x) ≥ d²`. -/
private lemma masses_outside_real {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {y d : ℝ}
    (hy : y ≠ 0) (hd : 0 < d) (hs : ∀ s ∈ (varrho N σ).support, d ≤ |s - y|) :
    mExt N σ y = ((mExt N σ y).re : ℂ) ∧ (mExt N σ y).re ≠ 0 ∧
      (∀ i, 1 + σ i * (mExt N σ y).re ≠ 0) ∧ fR N σ (mExt N σ y).re = y ∧
      d ^ 2 ≤ fR1 N σ (mExt N σ y).re := by
  set x := (mExt N σ y).re with hx
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set z : ℝ → ℂ := fun η => (y : ℂ) + η * Complex.I with hz
  have hzt : Tendsto z (𝓝[>] 0) (𝓝[upperHalf] (y : ℂ)) := masses_tendsto_line y
  have hzt' : Tendsto z (𝓝[>] 0) (𝓝 (y : ℂ)) := (tendsto_nhdsWithin_iff.mp hzt).1
  have hm : Tendsto (fun η => mFun N σ (z η)) (𝓝[>] 0) (𝓝 (mExt N σ y)) :=
    (tendsto_mFun_of_ne_zero N σ hσ hy).comp hzt
  have him0 : (mExt N σ y).im = 0 := by
    have h1 : Tendsto (fun η => (mFun N σ (z η)).im) (𝓝[>] 0) (𝓝 (mExt N σ y).im) :=
      (Complex.continuous_im.tendsto _).comp hm
    have h2 : Tendsto (fun η => (mFun N σ (z η)).im) (𝓝[>] 0) (𝓝 0) := by
      have hup : Tendsto (fun η : ℝ => η / d ^ 2) (𝓝[>] 0) (𝓝 0) := by
        have : Tendsto (fun η : ℝ => η / d ^ 2) (𝓝 0) (𝓝 (0 / d ^ 2)) :=
          (continuous_id.div_const _).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with η hη
        exact (mFun_spec N σ hσ (show 0 < (z η).im by simpa [hz] using hη)).1.le
      · filter_upwards [self_mem_nhdsWithin] with η hη
        exact masses_im_mFun_le hσ hN hd hs hη
    exact tendsto_nhds_unique h1 h2
  have hmx : mExt N σ y = (x : ℂ) := Complex.ext (by simp [hx]) (by simp [him0])
  rw [hmx] at hm
  set Bf : ℂ → ℝ := fun w => (‖w‖ ^ 2)⁻¹ - ∑ i, σ i ^ 2 / (N * ‖1 + (σ i : ℂ) * w‖ ^ 2)
    with hBf
  -- the facts along the vertical line
  have hev : ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 < (mFun N σ (z η)).im ∧
      fC N σ (mFun N σ (z η)) = z η ∧ d ^ 2 ≤ Bf (mFun N σ (z η)) := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    have hη' : (0 : ℝ) < η := hη
    have hzi : 0 < (z η).im := by simpa [hz] using hη'
    obtain ⟨h1, h2⟩ := mFun_spec N σ hσ hzi
    refine ⟨h1, h2, ?_⟩
    have hle := masses_im_mFun_le hσ hN hd hs hη'
    have hid := im_fC N σ (mFun N σ (z η))
    rw [h2] at hid
    have hzim : (z η).im = η := by simp [hz]
    rw [hzim] at hid
    change d ^ 2 ≤ (‖mFun N σ (z η)‖ ^ 2)⁻¹ -
      ∑ i, σ i ^ 2 / (N * ‖1 + (σ i : ℂ) * mFun N σ (z η)‖ ^ 2)
    set B := (‖mFun N σ (z η)‖ ^ 2)⁻¹ -
      ∑ i, σ i ^ 2 / (N * ‖1 + (σ i : ℂ) * mFun N σ (z η)‖ ^ 2)
    set u := (mFun N σ (z η)).im
    have hle' : u * d ^ 2 ≤ η := by
      rw [le_div_iff₀ (by positivity)] at hle
      exact hle
    by_contra hlt
    rw [not_le] at hlt
    have := mul_lt_mul_of_pos_left hlt h1
    linarith
  -- `σ_i² |m|² ≤ N |1 + σ_i m|²` along the line
  have hterm : ∀ i, ∀ᶠ η in 𝓝[>] (0 : ℝ),
      σ i ^ 2 * ‖mFun N σ (z η)‖ ^ 2 ≤ N * ‖1 + (σ i : ℂ) * mFun N σ (z η)‖ ^ 2 := by
    intro i
    filter_upwards [hev] with η ⟨him, _, hB⟩
    set w := mFun N σ (z η)
    have hw0 : 0 < ‖w‖ := lt_of_lt_of_le him (Complex.im_le_norm w)
    rcases (hσ i).eq_or_lt with h0 | hpos
    · rw [← h0]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
        Complex.ofReal_zero, add_zero, norm_one, one_pow, mul_one]
      positivity
    · have h1w : 0 < ‖1 + (σ i : ℂ) * w‖ := by
        refine lt_of_lt_of_le ?_ (Complex.abs_im_le_norm _)
        simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, add_zero, zero_add]
        rw [abs_of_pos (mul_pos hpos him)]
        exact mul_pos hpos him
      have hsum_nonneg : ∀ j ∈ Finset.univ, 0 ≤ σ j ^ 2 / (N * ‖1 + (σ j : ℂ) * w‖ ^ 2) :=
        fun j _ => by positivity
      have hsingle := Finset.single_le_sum hsum_nonneg (Finset.mem_univ i)
      have hBpos : 0 ≤ Bf w := le_trans (by positivity) hB
      have hle : σ i ^ 2 / (N * ‖1 + (σ i : ℂ) * w‖ ^ 2) ≤ (‖w‖ ^ 2)⁻¹ := by
        simp only [hBf] at hBpos
        linarith
      rw [div_le_iff₀ (by positivity)] at hle
      have h3 := mul_le_mul_of_nonneg_left hle (sq_nonneg ‖w‖)
      rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul] at h3
      linarith
  have hL1 : ∀ i, σ i ^ 2 * x ^ 2 ≤ N * (1 + σ i * x) ^ 2 := by
    intro i
    have hc : Continuous (fun w : ℂ => (N : ℝ) * ‖1 + (σ i : ℂ) * w‖ ^ 2 - σ i ^ 2 * ‖w‖ ^ 2) := by
      fun_prop
    have hlim := (hc.tendsto (x : ℂ)).comp hm
    have hge : 0 ≤ (N : ℝ) * ‖1 + (σ i : ℂ) * (x : ℂ)‖ ^ 2 - σ i ^ 2 * ‖(x : ℂ)‖ ^ 2 := by
      refine ge_of_tendsto hlim ?_
      filter_upwards [hterm i] with η hη
      simp only [Function.comp_apply]
      linarith
    have e1 : (1 : ℂ) + (σ i : ℂ) * (x : ℂ) = ((1 + σ i * x : ℝ) : ℂ) := by push_cast; ring
    rw [e1, masses_norm_real_sq, masses_norm_real_sq] at hge
    linarith
  have hpole : ∀ i, 1 + σ i * x ≠ 0 := by
    intro i
    rcases (hσ i).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    by_cases hx0 : x = 0
    · rw [hx0]; simp
    · intro h
      have := hL1 i
      rw [h] at this
      have : 0 < σ i ^ 2 * x ^ 2 := by positivity
      linarith
  have hpoleC : ∀ i, (N : ℂ) * (1 + (σ i : ℂ) * (x : ℂ)) ≠ 0 := by
    intro i
    have e1 : (N : ℂ) * (1 + (σ i : ℂ) * (x : ℂ)) = (((N : ℝ) * (1 + σ i * x) : ℝ) : ℂ) := by
      push_cast; ring
    rw [e1, Complex.ofReal_ne_zero]
    exact mul_ne_zero hNr.ne' (hpole i)
  -- the identity `z m = G(m)` in the limit
  set G : ℂ → ℂ := fun w => -1 + ∑ i, (σ i : ℂ) * w / (N * (1 + σ i * w)) with hG
  have hGc : ContinuousAt G (x : ℂ) := by
    refine continuousAt_const.add (tendsto_finsetSum _ fun i _ => ?_)
    exact (continuousAt_const.mul continuousAt_id).div
      (continuousAt_const.mul (continuousAt_const.add (continuousAt_const.mul continuousAt_id)))
      (hpoleC i)
  have hlimG : Tendsto (fun η => G (mFun N σ (z η))) (𝓝[>] 0) (𝓝 (G x)) := hGc.tendsto.comp hm
  have hlimZ : Tendsto (fun η => z η * mFun N σ (z η)) (𝓝[>] 0) (𝓝 ((y : ℂ) * x)) :=
    hzt'.mul hm
  have heqG : (y : ℂ) * x = G x := by
    refine tendsto_nhds_unique hlimZ (hlimG.congr' ?_)
    filter_upwards [hev] with η ⟨him, hfc, _⟩
    have hw0 : mFun N σ (z η) ≠ 0 := fun h => by rw [h] at him; simp at him
    simp only [hG]
    rw [← masses_fC_mul hw0, hfc]
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0] at heqG
    simp [hG] at heqG
  have hfx : fR N σ x = y := by
    have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0
    have h1 : fC N σ x * x = G x := masses_fC_mul hxC
    rw [← heqG, fC_ofReal] at h1
    have h2 := mul_right_cancel₀ hxC h1
    exact_mod_cast h2
  -- `f'(x) ≥ d²` in the limit
  have hBc : ContinuousAt Bf (x : ℂ) := by
    have hxn : ‖(x : ℂ)‖ ^ 2 ≠ 0 := by
      rw [masses_norm_real_sq]; positivity
    refine ((continuous_norm.pow 2).continuousAt.inv₀ hxn).sub
      (tendsto_finsetSum _ fun i _ => ?_)
    refine continuousAt_const.div (continuousAt_const.mul
      ((continuous_norm.comp (continuous_const.add
        (continuous_const.mul continuous_id))).pow 2).continuousAt) ?_
    have e1 : (1 : ℂ) + (σ i : ℂ) * (x : ℂ) = ((1 + σ i * x : ℝ) : ℂ) := by push_cast; ring
    change (N : ℝ) * ‖1 + (σ i : ℂ) * (x : ℂ)‖ ^ 2 ≠ 0
    rw [e1, masses_norm_real_sq]
    exact mul_ne_zero hNr.ne' (pow_ne_zero 2 (hpole i))
  have hBx : Bf x = fR1 N σ x := by
    simp only [hBf, fR1, masses_norm_real_sq]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 : (1 : ℂ) + (σ i : ℂ) * (x : ℂ) = ((1 + σ i * x : ℝ) : ℂ) := by push_cast; ring
    rw [e1, masses_norm_real_sq]
  have hd2 : d ^ 2 ≤ fR1 N σ x := by
    rw [← hBx]
    refine ge_of_tendsto (hBc.tendsto.comp hm) ?_
    filter_upwards [hev] with η ⟨_, _, hB⟩
    exact hB
  exact ⟨hmx, hx0, hpole, hfx, hd2⟩

/-! ## The spectra of `Σ = T Tᵀ` and `Ŝ + κ P₀` -/

/-- The eigenvalues of `T Tᵀ` are nonnegative. -/
private lemma masses_specOf_nonneg {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ) :
    ∀ i, 0 ≤ specOf (T * Tᵀ) i := by
  have hP : (T * Tᵀ).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose T
  intro i
  rw [specOf_eq hP.isHermitian]
  exact hP.eigenvalues_nonneg i

/-- The eigenvalues of `Ŝ + κ P₀` are nonnegative for `κ > 0`. -/
private lemma masses_specOf_regS_nonneg {K : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (T : Matrix (Fin M) (Fin K) ℝ) : ∀ i, 0 ≤ specOf (regS κ (Tᵀ * T)) i := by
  have hP := regS_posDef hκ T
  intro i
  rw [specOf_eq hP.isHermitian]
  exact (hP.eigenvalues_pos i).le

private lemma masses_regS_isHermitian {K : ℕ} (κ : ℝ) (S : Matrix (Fin K) (Fin K) ℝ) :
    (regS κ S).IsHermitian :=
  Matrix.isHermitian_iff_isSelfAdjoint.mpr (cfc_predicate _ S)

/-- The eigenvalue multiset of `regS κ S` is the image of that of `S` under
`x ↦ if 0 < x then x else κ`. -/
private lemma masses_regS_eig_multiset {K : ℕ} (κ : ℝ) {S : Matrix (Fin K) (Fin K) ℝ}
    (hS : S.IsHermitian) :
    Finset.univ.val.map (specOf (regS κ S)) =
      Finset.univ.val.map (fun j => if 0 < specOf S j then specOf S j else κ) := by
  have h1 := (masses_regS_isHermitian κ S).roots_charpoly_eq_eigenvalues
  have h2 : (regS κ S).charpoly = ∏ i, (Polynomial.X - Polynomial.C
      (if 0 < hS.eigenvalues i then hS.eigenvalues i else κ)) :=
    hS.charpoly_cfc_eq _
  rw [h2, Polynomial.roots_prod] at h1
  · rw [specOf_eq (masses_regS_isHermitian κ S), specOf_eq hS]
    simp only [Polynomial.roots_X_sub_C] at h1
    simpa [Function.comp_def, RCLike.ofReal_real_eq_id] using h1.symm
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

/-- Every eigenvalue of `Ŝ + κ P₀` is an eigenvalue of `Σ = T Tᵀ` or equals `κ`. -/
private lemma masses_regS_eig {K : ℕ} (κ : ℝ) (T : Matrix (Fin M) (Fin K) ℝ) (i : Fin K) :
    (∃ l, specOf (regS κ (Tᵀ * T)) i = specOf (T * Tᵀ) l) ∨
      specOf (regS κ (Tᵀ * T)) i = κ := by
  have hS : (Tᵀ * T).IsHermitian := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.posSemidef_conjTranspose_mul_self T).isHermitian
  have hmem : specOf (regS κ (Tᵀ * T)) i ∈ Finset.univ.val.map
      (fun j => if 0 < specOf (Tᵀ * T) j then specOf (Tᵀ * T) j else κ) := by
    rw [← masses_regS_eig_multiset κ hS]
    exact Multiset.mem_map_of_mem _ (Finset.mem_univ i)
  obtain ⟨j, -, hj⟩ := Multiset.mem_map.mp hmem
  split_ifs at hj with hpos
  · left
    have hc := nzEq_specOf_mul_transpose T (specOf (Tᵀ * T) j) hpos.ne'
    have hne : (Finset.univ.filter fun l => specOf (T * Tᵀ) l = specOf (Tᵀ * T) j).Nonempty := by
      rw [← Finset.card_pos, hc]
      exact Finset.card_pos.mpr ⟨j, by simp⟩
    obtain ⟨l, hl⟩ := hne
    exact ⟨l, by rw [← hj]; exact ((Finset.mem_filter.mp hl).2).symm⟩
  · right
    exact hj.symm

/-- `f` of `Ŝ + κ P₀` on `ℝ`: `f_κ(x) = f(x) + (K − rank T) κ / (N (1 + κ x))`. -/
private lemma masses_fR_regS {K : ℕ} (N : ℕ) {κ : ℝ} (hκ : 0 < κ)
    (T : Matrix (Fin M) (Fin K) ℝ) (x : ℝ) :
    fR N (specOf (regS κ (Tᵀ * T))) x = fR N (specOf (T * Tᵀ)) x +
      ((K - T.rank : ℕ) : ℝ) * κ / (N * (1 + κ * x)) := by
  apply Complex.ofReal_injective
  rw [← fC_ofReal, fC_regS N hκ T, fC_ofReal]
  push_cast
  ring

/-- `f'` of `Ŝ + κ P₀` on `ℝ`: `f_κ'(x) = f'(x) − (K − rank T) κ² / (N (1 + κ x)²)`. -/
private lemma masses_fR1_regS {K : ℕ} (hN : 0 < N) {κ : ℝ} (hκ : 0 < κ)
    (T : Matrix (Fin M) (Fin K) ℝ) {x : ℝ} (hx : x ≠ 0)
    (hx' : ∀ i, 1 + specOf (T * Tᵀ) i * x ≠ 0)
    (hx'' : ∀ i, 1 + specOf (regS κ (Tᵀ * T)) i * x ≠ 0) (hκx : 1 + κ * x ≠ 0) :
    fR1 N (specOf (regS κ (Tᵀ * T))) x = fR1 N (specOf (T * Tᵀ)) x -
      ((K - T.rank : ℕ) : ℝ) * κ ^ 2 / (N * (1 + κ * x) ^ 2) := by
  set a : ℝ := ((K - T.rank : ℕ) : ℝ) with ha
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := hasDerivAt_fR N (specOf (regS κ (Tᵀ * T))) hx hx''
  have hfun : fR N (specOf (regS κ (Tᵀ * T))) =
      fun u => fR N (specOf (T * Tᵀ)) u + a * κ / (N * (1 + κ * u)) :=
    funext (masses_fR_regS N hκ T)
  rw [hfun] at h1
  have hd : HasDerivAt (fun u : ℝ => (N : ℝ) * (1 + κ * u)) ((N : ℝ) * (κ * 1)) x :=
    (((hasDerivAt_id x).const_mul κ).const_add 1).const_mul (N : ℝ)
  have hq : HasDerivAt (fun u : ℝ => a * κ / (N * (1 + κ * u)))
      ((0 * ((N : ℝ) * (1 + κ * x)) - a * κ * ((N : ℝ) * (κ * 1))) / ((N : ℝ) * (1 + κ * x)) ^ 2)
      x :=
    (hasDerivAt_const x (a * κ)).div hd (mul_ne_zero hNr.ne' hκx)
  have h2 := (hasDerivAt_fR N (specOf (T * Tᵀ)) hx hx').add hq
  rw [h1.unique h2]
  field_simp
  ring

/-! ## A support bound uniform in `κ` -/

private lemma masses_massRatio_le {L : ℕ} (N : ℕ) (σ : Fin L → ℝ) :
    massRatio N σ ≤ (L : ℝ) / N := by
  unfold massRatio
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)

/-- `ϱ((X, ∞)) = 0` for `X = (1 + √R) s₁ max(2, √(8R))`, `σ ≤ s₁`, `R ≥ φ π((0, ∞))`. -/
private lemma masses_varrho_Ioi {L : ℕ} {σ : Fin L → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    {s₁ R : ℝ} (hs₁ : ∀ i, σ i ≤ s₁) (hs₁0 : 0 ≤ s₁) (hR : massRatio N σ ≤ R) :
    varrho N σ (Set.Ioi ((1 + √R) * s₁ * max 2 √(8 * R))) = 0 := by
  refine measure_mono_null ?_ (varrho_compl_Icc N σ hσ hN hs₁0 hs₁)
  intro x hx hmem
  have hle : (1 + √(massRatio N σ)) * s₁ * max 2 (√(8 * massRatio N σ)) ≤
      (1 + √R) * s₁ * max 2 √(8 * R) := by
    gcongr
  exact absurd (lt_of_le_of_lt hle hx) (not_lt.mpr hmem.2)

/-! ## The arctan sandwich -/

private lemma masses_arctan_ge {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    Real.pi / 2 - η / δ ≤ Real.arctan (δ / η) := by
  have h := Real.arctan_inv_of_pos (show 0 < η / δ by positivity)
  rw [inv_div] at h
  rw [h]
  linarith [Real.arctan_le_self (show 0 ≤ η / δ by positivity)]

private lemma masses_kernel_lower {a E₂ B δ η x : ℝ} (hδ : 0 < δ) (hη : 0 < η) (haE : a ≤ E₂)
    (hB : B + δ ≤ E₂) (hx : x ≤ B) :
    Real.pi * (Set.Ici (a + δ)).indicator 1 x - 2 * (η / δ) ≤
      Real.arctan ((E₂ - x) / η) - Real.arctan ((a - x) / η) := by
  by_cases h : x ∈ Set.Ici (a + δ)
  · rw [Set.indicator_of_mem h, Pi.one_apply, mul_one]
    have hxa : a + δ ≤ x := h
    have h1 : Real.arctan (δ / η) ≤ Real.arctan ((E₂ - x) / η) :=
      Real.arctan_mono (div_le_div_of_nonneg_right (by linarith) hη.le)
    have h2 : Real.arctan ((a - x) / η) ≤ Real.arctan (-δ / η) :=
      Real.arctan_mono (div_le_div_of_nonneg_right (by linarith) hη.le)
    rw [neg_div, Real.arctan_neg] at h2
    linarith [masses_arctan_ge hδ hη]
  · rw [Set.indicator_of_notMem h, mul_zero, zero_sub]
    have h1 : Real.arctan ((a - x) / η) ≤ Real.arctan ((E₂ - x) / η) :=
      Real.arctan_mono (div_le_div_of_nonneg_right (by linarith) hη.le)
    have : 0 ≤ 2 * (η / δ) := by positivity
    linarith

private lemma masses_kernel_upper {a E₂ δ η x : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    Real.arctan ((E₂ - x) / η) - Real.arctan ((a - x) / η) ≤
      Real.pi * (Set.Ici (a - δ)).indicator 1 x + η / δ := by
  have hA := Real.arctan_lt_pi_div_two ((E₂ - x) / η)
  by_cases h : x ∈ Set.Ici (a - δ)
  · rw [Set.indicator_of_mem h, Pi.one_apply, mul_one]
    have hB := Real.neg_pi_div_two_lt_arctan ((a - x) / η)
    have : 0 ≤ η / δ := by positivity
    linarith
  · rw [Set.indicator_of_notMem h, mul_zero, zero_add]
    have hx : x < a - δ := not_le.mp h
    have h2 : Real.arctan (δ / η) ≤ Real.arctan ((a - x) / η) :=
      Real.arctan_mono (div_le_div_of_nonneg_right (by linarith) hη.le)
    linarith [masses_arctan_ge hδ hη]

private lemma masses_kernel_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] (a E₂ η : ℝ) :
    Integrable (fun x => Real.arctan ((E₂ - x) / η) - Real.arctan ((a - x) / η)) μ := by
  refine Integrable.of_bound ?_ Real.pi (ae_of_all _ fun x => ?_)
  · exact ((Real.continuous_arctan.comp ((continuous_const.sub continuous_id).div_const η)).sub
      (Real.continuous_arctan.comp
        ((continuous_const.sub continuous_id).div_const η))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_le]
    have := Real.arctan_lt_pi_div_two ((E₂ - x) / η)
    have := Real.neg_pi_div_two_lt_arctan ((E₂ - x) / η)
    have := Real.arctan_lt_pi_div_two ((a - x) / η)
    have := Real.neg_pi_div_two_lt_arctan ((a - x) / η)
    constructor <;> linarith

private lemma masses_integral_lower {μ : Measure ℝ} [IsProbabilityMeasure μ] {a E₂ B δ η : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (haE : a ≤ E₂) (hB : B + δ ≤ E₂) (hμB : μ (Set.Ioi B) = 0) :
    Real.pi * (μ (Set.Ici (a + δ))).toReal - 2 * (η / δ) ≤
      ∫ x, Real.arctan ((E₂ - x) / η) - Real.arctan ((a - x) / η) ∂μ := by
  have hint := masses_kernel_integrable μ a E₂ η
  have hi1 : Integrable (fun x => Real.pi * (Set.Ici (a + δ)).indicator (1 : ℝ → ℝ) x) μ :=
    ((integrable_const (1 : ℝ)).indicator measurableSet_Ici).const_mul _
  have hint2 : Integrable
      (fun x => Real.pi * (Set.Ici (a + δ)).indicator (1 : ℝ → ℝ) x - 2 * (η / δ)) μ :=
    hi1.sub (integrable_const _)
  have hae : ∀ᵐ x ∂μ, x ≤ B := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hμB] with x hx
    exact not_lt.mp hx
  calc Real.pi * (μ (Set.Ici (a + δ))).toReal - 2 * (η / δ)
      = ∫ x, Real.pi * (Set.Ici (a + δ)).indicator (1 : ℝ → ℝ) x - 2 * (η / δ) ∂μ := by
        rw [integral_sub hi1 (integrable_const _), integral_const_mul,
          integral_indicator_one measurableSet_Ici, integral_const]
        simp [measureReal_def]
    _ ≤ _ := by
        refine integral_mono_ae hint2 hint ?_
        filter_upwards [hae] with x hx
        exact masses_kernel_lower hδ hη haE hB hx

private lemma masses_integral_upper {μ : Measure ℝ} [IsProbabilityMeasure μ] {a E₂ δ η : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) :
    ∫ x, Real.arctan ((E₂ - x) / η) - Real.arctan ((a - x) / η) ∂μ ≤
      Real.pi * (μ (Set.Ici (a - δ))).toReal + η / δ := by
  have hint := masses_kernel_integrable μ a E₂ η
  have hi1 : Integrable (fun x => Real.pi * (Set.Ici (a - δ)).indicator (1 : ℝ → ℝ) x) μ :=
    ((integrable_const (1 : ℝ)).indicator measurableSet_Ici).const_mul _
  have hint2 : Integrable
      (fun x => Real.pi * (Set.Ici (a - δ)).indicator (1 : ℝ → ℝ) x + η / δ) μ :=
    hi1.add (integrable_const _)
  calc _ ≤ ∫ x, Real.pi * (Set.Ici (a - δ)).indicator (1 : ℝ → ℝ) x + η / δ ∂μ :=
        integral_mono hint hint2 fun x => masses_kernel_upper hδ hη
    _ = Real.pi * (μ (Set.Ici (a - δ))).toReal + η / δ := by
        rw [integral_add hi1 (integrable_const _), integral_const_mul,
          integral_indicator_one measurableSet_Ici, integral_const]
        simp [measureReal_def]

/-! ## Convergence of `∫ Im m` along horizontal segments -/

private lemma masses_continuous_im_line {L : ℕ} (N : ℕ) {σ : Fin L → ℝ} (hσ : ∀ i, 0 ≤ σ i)
    {η : ℝ} (hη : 0 < η) :
    Continuous (fun x : ℝ => (mFun N σ (↑x + ↑η * Complex.I)).im) := by
  refine Complex.continuous_im.comp (continuous_iff_continuousAt.mpr fun x => ?_)
  have hz : 0 < ((x : ℂ) + ↑η * Complex.I).im := by simpa using hη
  exact ContinuousAt.comp (g := mFun N σ) (f := fun x : ℝ => (x : ℂ) + ↑η * Complex.I)
    (analyticOnNhd_mFun N σ hσ _ hz).continuousAt
    (Complex.continuous_ofReal.add continuous_const).continuousAt

private lemma masses_tendsto_segment {K : ℕ} (hN : 1 ≤ N) (T : Matrix (Fin M) (Fin K) ℝ)
    {a b η : ℝ} (hab : a ≤ b) (hη : 0 < η) :
    Tendsto (fun κ => ∫ x in a..b, (mFun N (specOf (regS κ (Tᵀ * T))) (↑x + ↑η * Complex.I)).im)
      (𝓝[>] 0) (𝓝 (∫ x in a..b, (mFun N (specOf (T * Tᵀ)) (↑x + ↑η * Complex.I)).im)) := by
  set L : Set ℂ := (fun x : ℝ => (x : ℂ) + η * Complex.I) '' Set.Icc a b with hL
  have hLc : IsCompact L :=
    isCompact_Icc.image (Complex.continuous_ofReal.add continuous_const)
  have hL0 : ∀ z ∈ L, 0 < z.im := by
    rintro _ ⟨x, -, rfl⟩
    simpa using hη
  have hU := tendstoUniformlyOn_mFun_regS hN T hLc hL0
  rw [Metric.tendstoUniformlyOn_iff] at hU
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hc : 0 < ε / (b - a + 1) := div_pos hε (by linarith)
  filter_upwards [hU _ hc, self_mem_nhdsWithin] with κ hκ hκ0
  have hσ := masses_specOf_nonneg T
  have hσκ := masses_specOf_regS_nonneg (show (0 : ℝ) < κ from hκ0) T
  rw [Real.dist_eq, ← intervalIntegral.integral_sub
    ((masses_continuous_im_line N hσκ hη).intervalIntegrable _ _)
    ((masses_continuous_im_line N hσ hη).intervalIntegrable _ _)]
  have hb : ∀ x ∈ Set.uIoc a b,
      ‖(mFun N (specOf (regS κ (Tᵀ * T))) (↑x + ↑η * Complex.I)).im -
        (mFun N (specOf (T * Tᵀ)) (↑x + ↑η * Complex.I)).im‖ ≤ ε / (b - a + 1) := by
    intro x hx
    have hxI : x ∈ Set.Icc a b := by
      rw [Set.uIoc_of_le hab] at hx
      exact ⟨hx.1.le, hx.2⟩
    have := hκ _ ⟨x, hxI, rfl⟩
    rw [Real.norm_eq_abs, ← Complex.sub_im]
    refine (Complex.abs_im_le_norm _).trans ?_
    rw [← dist_eq_norm, dist_comm]
    exact this.le
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [Real.norm_eq_abs] at h
  refine lt_of_le_of_lt h ?_
  rw [abs_of_nonneg (by linarith), div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
  nlinarith

/-- `γ_j > 0` forces the defining set of `γ_j` to be nonempty and bounded above. -/
private lemma masses_gammaLoc_set {σ : Fin M → ℝ} {j : ℕ} (hj : 0 < gammaLoc N σ j) :
    {E | 0 < E ∧ (j : ℝ) - 1 / 2 ≤ nClass N σ E}.Nonempty ∧
      BddAbove {E | 0 < E ∧ (j : ℝ) - 1 / 2 ≤ nClass N σ E} := by
  unfold gammaLoc at hj
  constructor
  · by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Real.sSup_empty] at hj
    exact lt_irrefl _ hj
  · by_contra h
    rw [Real.sSup_of_not_bddAbove h] at hj
    exact lt_irrefl _ hj

/-- `n(γ_j) = j − 1/2` wherever `γ_j > 0` (`σ ≥ 0`). -/
theorem nClass_gammaLoc_of_pos {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {j : ℕ}
    (hj : 0 < gammaLoc N σ j) : nClass N σ (gammaLoc N σ j) = (j : ℝ) - 1 / 2 := by
  obtain ⟨⟨E0, hE0S⟩, hbdd⟩ := masses_gammaLoc_set hj
  set S : Set ℝ := {E | 0 < E ∧ (j : ℝ) - 1 / 2 ≤ nClass N σ E} with hSdef
  have hgam : gammaLoc N σ j = sSup S := rfl
  rw [hgam] at hj ⊢
  have hcont : ContinuousAt (nClass N σ) (sSup S) :=
    (masses_nClass_continuousOn hσ hN).continuousAt (Ioi_mem_nhds hj)
  refine le_antisymm ?_ ?_
  · by_contra hlt
    rw [not_le] at hlt
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp hcont
      ((nClass N σ (sSup S)) - ((j : ℝ) - 1 / 2)) (by linarith)
    have hlt2 : sSup S < sSup S + δ / 2 := by linarith
    have hmem : sSup S + δ / 2 ∈ S := by
      refine ⟨by linarith, ?_⟩
      have := hδ' (x := sSup S + δ / 2)
        (by rw [Real.dist_eq]; rw [abs_of_pos (by linarith)]; linarith)
      rw [Real.dist_eq, abs_lt] at this
      linarith [this.1]
    exact absurd (le_csSup hbdd hmem) (not_le.mpr hlt2)
  · by_contra hlt
    rw [not_le] at hlt
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp hcont
      (((j : ℝ) - 1 / 2) - nClass N σ (sSup S)) (by linarith)
    obtain ⟨E, hES, hE⟩ := exists_lt_of_lt_csSup ⟨E0, hE0S⟩ (show sSup S - δ < sSup S by linarith)
    have hEle : E ≤ sSup S := le_csSup hbdd hES
    have := hδ' (x := E) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    rw [Real.dist_eq, abs_lt] at this
    linarith [hES.2, this.2]

/-- `ν(B(E, r)) = 0` for a nonzero measure `ν` gives `dist(E, supp ν) ≥ r`. -/
private lemma masses_le_infDist {μ : Measure ℝ} (hμ : μ ≠ 0) {E r : ℝ}
    (h : μ (Metric.ball E r) = 0) : r ≤ Metric.infDist E μ.support := by
  rw [Metric.le_infDist (Measure.nonempty_support hμ)]
  intro y hy
  by_contra hlt
  have hyb : y ∈ Metric.ball E r := by
    rw [Metric.mem_ball, dist_comm]
    exact not_le.mp hlt
  exact (Measure.notMem_support_iff_exists.mpr
    ⟨_, Metric.isOpen_ball.mem_nhds hyb, h⟩) hy

/-- A point at distance `t ≤ |E|` from `supp ϱ` is at distance `t/2` from `supp ϱ_κ`, for all
small `κ`. -/
theorem outside_regS {τ : ℝ} (hτ : 0 < τ) {K : ℕ} (hN : 1 ≤ N) {T : Matrix (Fin M) (Fin K) ℝ}
    (hda : DensityAssumptions τ N (specOf (T * Tᵀ))) {E t : ℝ} (ht : 0 < t) (htE : t ≤ |E|)
    (hd : t ≤ Metric.infDist E (varrho N (specOf (T * Tᵀ))).support) :
    ∀ᶠ κ in 𝓝[>] (0 : ℝ),
      t / 2 ≤ Metric.infDist E (varrho N (specOf (regS κ (Tᵀ * T)))).support := by
  have _ := hτ
  have _ := hda
  have hN0 : 0 < N := hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set σ := specOf (T * Tᵀ) with hσdef
  have hσ : ∀ i, 0 ≤ σ i := masses_specOf_nonneg T
  have hne : ∀ κ : ℝ, 0 < κ → varrho N (specOf (regS κ (Tᵀ * T))) ≠ 0 := fun κ hκ => by
    have := isProbabilityMeasure_varrho N _ (masses_specOf_regS_nonneg hκ T) hN0
    exact IsProbabilityMeasure.ne_zero _
  rcases lt_trichotomy E 0 with hE | hE | hE
  · -- `E < 0`: `ϱ_κ` does not charge `(−∞, 0)`
    filter_upwards [self_mem_nhdsWithin] with κ hκ
    refine masses_le_infDist (hne κ hκ) (measure_mono_null (fun x hx => ?_) (masses_varrho_Iio N _))
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx
    rw [abs_of_neg hE] at htE
    change x < 0
    linarith [hx.2]
  · rw [hE, abs_zero] at htE
    linarith
  rw [abs_of_pos hE] at htE
  -- distances to `supp ϱ` on `[E − 3t/4, E + 3t/4]`
  have hsupp : ∀ y, |y - E| ≤ 3 * t / 4 → ∀ s ∈ (varrho N σ).support, t / 4 ≤ |s - y| := by
    intro y hy s hs
    have h1 : t ≤ dist E s := hd.trans (Metric.infDist_le_dist_of_mem hs)
    rw [Real.dist_eq] at h1
    have h2 := abs_sub_le E y s
    rw [abs_sub_comm E y, abs_sub_comm y s] at h2
    linarith
  set y₁ := E - 3 * t / 4 with hy₁def
  set y₂ := E + 3 * t / 4 with hy₂def
  have hy₁ : 0 < y₁ := by linarith
  have hreal : ∀ y ∈ Set.Icc y₁ y₂, (mExt N σ y).re ≠ 0 ∧ (∀ i, 1 + σ i * (mExt N σ y).re ≠ 0) ∧
      fR N σ (mExt N σ y).re = y ∧ (t / 4) ^ 2 ≤ fR1 N σ (mExt N σ y).re := by
    intro y hy
    have hy0 : y ≠ 0 := by linarith [hy.1]
    obtain ⟨-, h1, h2, h3, h4⟩ := masses_outside_real hσ hN0 hy0 (by positivity)
      (hsupp y (by rw [abs_le]; constructor <;> linarith [hy.1, hy.2]))
    exact ⟨h1, h2, h3, h4⟩
  set X : ℝ → ℝ := fun y => (mExt N σ y).re with hX
  have hIcc : Set.uIcc y₁ y₂ = Set.Icc y₁ y₂ := Set.uIcc_of_le (by linarith)
  have hXc : ContinuousOn X (Set.uIcc y₁ y₂) := by
    rw [hIcc]
    have h1 : ContinuousOn (fun y : ℝ => mExt N σ y) (Set.Icc y₁ y₂) :=
      (continuousOn_mExt N σ hσ).comp Complex.continuous_ofReal.continuousOn
        (fun y hy => Or.inr ⟨Complex.ofReal_im y,
          Complex.ofReal_ne_zero.mpr (by linarith [hy.1] : y ≠ 0)⟩)
    exact Complex.continuous_re.comp_continuousOn h1
  set α := X y₁ with hα
  set β := X y₂ with hβ
  have hgood : ∀ w ∈ Set.uIcc α β, w ≠ 0 ∧ (∀ i, 1 + σ i * w ≠ 0) ∧
      (t / 4) ^ 2 ≤ fR1 N σ w := by
    intro w hw
    obtain ⟨y, hy, rfl⟩ := intermediate_value_uIcc hXc hw
    rw [hIcc] at hy
    obtain ⟨h1, h2, -, h4⟩ := hreal y hy
    exact ⟨h1, h2, h4⟩
  have hfα : fR N σ α = y₁ := (hreal y₁ ⟨le_rfl, by linarith⟩).2.2.1
  have hfβ : fR N σ β = y₂ := (hreal y₂ ⟨by linarith, le_rfl⟩).2.2.1
  set ρ := |α| + |β| + 1 with hρ
  have hρ1 : 1 ≤ ρ := by have := abs_nonneg α; have := abs_nonneg β; linarith
  have hwρ : ∀ w ∈ Set.uIcc α β, |w| ≤ ρ := by
    intro w hw
    have h1 := Set.mem_uIcc.mp hw
    rw [abs_le]
    constructor
    · rcases h1 with h | h <;>
        linarith [neg_abs_le α, neg_abs_le β, abs_nonneg α, abs_nonneg β, h.1]
    · rcases h1 with h | h <;>
        linarith [le_abs_self α, le_abs_self β, abs_nonneg α, abs_nonneg β, h.2]
  set A : ℝ := ((K - T.rank : ℕ) : ℝ) with hA
  have hA0 : 0 ≤ A := Nat.cast_nonneg _
  set κ₀ := min (1 / (2 * ρ)) (min (t * N / (8 * (A + 1))) (min 1 (N * t ^ 2 / (128 * (A + 1)))))
    with hκ₀def
  have hκ₀ : 0 < κ₀ := lt_min (by positivity) (lt_min (by positivity)
    (lt_min one_pos (by positivity)))
  filter_upwards [Ioo_mem_nhdsGT hκ₀] with κ hκ
  obtain ⟨hκ0, hκ1⟩ := hκ
  have hκa : κ ≤ 1 / (2 * ρ) := hκ1.le.trans (min_le_left _ _)
  have hκb : κ ≤ t * N / (8 * (A + 1)) := hκ1.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hκc : κ ≤ 1 :=
    hκ1.le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hκd : κ ≤ N * t ^ 2 / (128 * (A + 1)) :=
    hκ1.le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  set σκ := specOf (regS κ (Tᵀ * T)) with hσκdef
  have hσκ : ∀ i, 0 ≤ σκ i := masses_specOf_regS_nonneg hκ0 T
  have hκw : ∀ w ∈ Set.uIcc α β, 1 / 2 ≤ 1 + κ * w := by
    intro w hw
    have h1 := hwρ w hw
    have h2 : κ * ρ ≤ 1 / 2 := by
      rw [le_div_iff₀ (by positivity)] at hκa
      linarith
    have h3 : κ * |w| ≤ κ * ρ := mul_le_mul_of_nonneg_left h1 hκ0.le
    have h4 : -(κ * |w|) ≤ κ * w := by
      have := neg_abs_le w
      nlinarith
    linarith
  have hpoleκ : ∀ w ∈ Set.uIcc α β, ∀ i, 1 + σκ i * w ≠ 0 := by
    intro w hw i
    rcases masses_regS_eig κ T i with ⟨l, hl⟩ | hl
    · rw [hσκdef, hl]
      exact (hgood w hw).2.1 l
    · rw [hσκdef, hl]
      have := hκw w hw
      linarith
  have hg : ∀ w ∈ Set.uIcc α β, 0 ≤ A * κ / (N * (1 + κ * w)) ∧
      A * κ / (N * (1 + κ * w)) ≤ t / 4 := by
    intro w hw
    have h1 := hκw w hw
    have hden : (N : ℝ) / 2 ≤ N * (1 + κ * w) := by nlinarith
    refine ⟨by positivity, ?_⟩
    calc A * κ / (N * (1 + κ * w)) ≤ A * κ / (N / 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ ≤ t / 4 := by
          rw [div_le_iff₀ (by positivity)]
          have h2 : A * κ ≤ A * (t * N / (8 * (A + 1))) := mul_le_mul_of_nonneg_left hκb hA0
          have h3 : A * (t * N / (8 * (A + 1))) ≤ t * N / 8 := by
            rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith [mul_pos ht hNr]
          linarith
  have hfκα : fR N σκ α ≤ E - t / 2 := by
    rw [masses_fR_regS N hκ0 T α, hfα]
    have := (hg α Set.left_mem_uIcc).2
    linarith
  have hfκβ : E + t / 2 ≤ fR N σκ β := by
    rw [masses_fR_regS N hκ0 T β, hfβ]
    have := (hg β Set.right_mem_uIcc).1
    linarith
  have hcont : ContinuousOn (fR N σκ) (Set.uIcc α β) := fun w hw =>
    (hasDerivAt_fR N σκ (hgood w hw).1 (hpoleκ w hw)).continuousAt.continuousWithinAt
  have hball : varrho N σκ (Metric.ball E (t / 2)) = 0 := by
    have hsub : Metric.ball E (t / 2) ⊆ Set.Ioi 0 := fun x hx => by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx
      change 0 < x
      linarith [hx.1]
    rw [masses_varrho_apply N σκ measurableSet_ball hsub]
    refine setLIntegral_eq_zero measurableSet_ball fun x hx => ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx
    have hxI : x ∈ Set.uIcc (fR N σκ α) (fR N σκ β) :=
      Set.mem_uIcc.mpr (Or.inl ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    obtain ⟨w, hw, hwx⟩ := intermediate_value_uIcc hcont hxI
    obtain ⟨hw0, hwp, hw1⟩ := hgood w hw
    have h1 := hκw w hw
    have hf1 : 0 < fR1 N σκ w := by
      rw [masses_fR1_regS hN0 hκ0 T hw0 hwp (hpoleκ w hw) (by linarith : (0 : ℝ) < 1 + κ * w).ne']
      have hsq : (1 / 2 : ℝ) ^ 2 ≤ (1 + κ * w) ^ 2 := pow_le_pow_left₀ (by norm_num) h1 2
      have hden : (N : ℝ) / 4 ≤ N * (1 + κ * w) ^ 2 := by
        have := mul_le_mul_of_nonneg_left hsq hNr.le
        linarith
      have hb1 : A * κ ^ 2 / (N * (1 + κ * w) ^ 2) ≤ A * κ ^ 2 / (N / 4) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      have h2 : κ ^ 2 ≤ N * t ^ 2 / (128 * (A + 1)) := by
        calc κ ^ 2 = κ * κ := sq κ
          _ ≤ 1 * κ := mul_le_mul_of_nonneg_right hκc hκ0.le
          _ ≤ _ := by linarith
      have h3 : A * κ ^ 2 ≤ A * (N * t ^ 2 / (128 * (A + 1))) := mul_le_mul_of_nonneg_left h2 hA0
      have h4 : A * (N * t ^ 2 / (128 * (A + 1))) ≤ N * t ^ 2 / 128 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
        have := mul_pos hNr (pow_pos ht 2)
        nlinarith
      have hb2 : A * κ ^ 2 / (N / 4) ≤ t ^ 2 / 32 := by
        rw [div_le_iff₀ (by positivity)]
        have e : t ^ 2 / 32 * (N / 4) = N * t ^ 2 / 128 := by ring
        linarith
      have e2 : (t / 4) ^ 2 = t ^ 2 / 16 := by ring
      have := pow_pos ht 2
      linarith
    have hx0 : fR N σκ w ≠ 0 := by rw [hwx]; linarith [hx.1]
    have hm := mExt_fR_of_pos N σκ hσκ hN0 hw0 (hpoleκ w hw) hx0 hf1
    rw [hwx] at hm
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero]
    rw [rhoDens, hm, Complex.ofReal_im, zero_div]
  exact masses_le_infDist (hne κ hκ0) hball

/-- The classical counting function of `Ŝ + κ P₀` tends to that of `Σ = T Tᵀ` at every `E > 0`. -/
theorem tendsto_nClass_regS {K : ℕ} (hN : 1 ≤ N) (T : Matrix (Fin M) (Fin K) ℝ) {E : ℝ}
    (hE : 0 < E) :
    Tendsto (fun κ => nClass N (specOf (regS κ (Tᵀ * T))) E) (𝓝[>] 0)
      (𝓝 (nClass N (specOf (T * Tᵀ)) E)) := by
  have hN0 : 0 < N := hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set σ := specOf (T * Tᵀ) with hσdef
  have hσ : ∀ i, 0 ≤ σ i := masses_specOf_nonneg T
  -- a support bound uniform in `κ ∈ (0, 1]`
  have hsum0 : 0 ≤ ∑ i, σ i := Finset.sum_nonneg fun i _ => hσ i
  set S₁ : ℝ := ∑ i, σ i + 1 with hS₁
  have hσS : ∀ i, σ i ≤ S₁ := fun i => by
    have := Finset.single_le_sum (fun j _ => hσ j) (Finset.mem_univ i)
    linarith
  have hS₁0 : 0 ≤ S₁ := by linarith
  set R : ℝ := ((M : ℝ) + K) / N with hR
  set B : ℝ := (1 + √R) * S₁ * max 2 √(8 * R) with hBdef
  have hB0 : 0 ≤ B := by
    have : 0 ≤ max 2 √(8 * R) := le_trans (by norm_num) (le_max_left _ _)
    positivity
  have hBσ : varrho N σ (Set.Ioi B) = 0 :=
    masses_varrho_Ioi hσ hN0 hσS hS₁0 ((masses_massRatio_le N σ).trans
      (div_le_div_of_nonneg_right (by linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]) hNr.le))
  have hBκ : ∀ κ : ℝ, 0 < κ → κ ≤ 1 → varrho N (specOf (regS κ (Tᵀ * T))) (Set.Ioi B) = 0 := by
    intro κ hκ hκ1
    refine masses_varrho_Ioi (masses_specOf_regS_nonneg hκ T) hN0 (fun i => ?_) hS₁0 ?_
    · rcases masses_regS_eig κ T i with ⟨l, hl⟩ | hl
      · rw [hl]
        exact hσS l
      · rw [hl]
        linarith
    · exact (masses_massRatio_le N _).trans (div_le_div_of_nonneg_right
        (by linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]) hNr.le)
  set E₂ : ℝ := B + E + 2 with hE₂
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hcont := (masses_nClass_continuousOn hσ hN0).continuousAt (Ioi_mem_nhds hE)
  obtain ⟨δ₀, hδ₀, hδ₀'⟩ := Metric.continuousAt_iff.mp hcont (ε / 4) (by positivity)
  set δ : ℝ := min (δ₀ / 3) 1 with hδdef
  have hδ : 0 < δ := lt_min (by positivity) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδ3 : δ ≤ δ₀ / 3 := min_le_left _ _
  set η : ℝ := δ * ε / (12 * N) with hηdef
  have hη : 0 < η := by positivity
  have hηδ : η / δ = ε / (12 * N) := by
    rw [hηdef]
    field_simp
  set θ : ℝ := ε / (4 * N) with hθdef
  have hθ : 0 < θ := by positivity
  have hlo := masses_tendsto_segment hN T (a := E - δ) (b := E₂) (by linarith) hη
  have hhi := masses_tendsto_segment hN T (a := E + δ) (b := E₂) (by linarith) hη
  filter_upwards [(Metric.tendsto_nhds.mp hlo) θ hθ, (Metric.tendsto_nhds.mp hhi) θ hθ,
    Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with κ h1 h2 hκ
  obtain ⟨hκ0, hκ1⟩ := hκ
  set σκ := specOf (regS κ (Tᵀ * T)) with hσκdef
  have hσκ : ∀ i, 0 ≤ σκ i := masses_specOf_regS_nonneg hκ0 T
  have := isProbabilityMeasure_varrho N σ hσ hN0
  have := isProbabilityMeasure_varrho N σκ hσκ hN0
  rw [arctan_count_varrho σκ hσκ hN0 _ _ _ hη, arctan_count_varrho σ hσ hN0 _ _ _ hη,
    Real.dist_eq, abs_lt] at h1 h2
  have A1 := masses_integral_lower (μ := varrho N σκ) (a := E - δ) (E₂ := E₂) (B := B) hδ hη
    (by linarith) (by linarith) (hBκ κ hκ0 hκ1.le)
  have A2 := masses_integral_upper (μ := varrho N σ) (a := E - δ) (E₂ := E₂) hδ hη
  have A3 := masses_integral_upper (μ := varrho N σκ) (a := E + δ) (E₂ := E₂) hδ hη
  have A4 := masses_integral_lower (μ := varrho N σ) (a := E + δ) (E₂ := E₂) (B := B) hδ hη
    (by linarith) (by linarith) hBσ
  rw [sub_add_cancel] at A1
  rw [add_sub_cancel_right] at A3
  have c1 := hδ₀' (x := E - δ - δ) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
  have c2 := hδ₀' (x := E + δ + δ) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
  rw [Real.dist_eq, abs_lt] at c1 c2
  unfold nClass at c1 c2 ⊢
  rw [Real.dist_eq, abs_lt]
  set p := (varrho N σκ (Set.Ici E)).toReal
  set q₁ := (varrho N σ (Set.Ici (E - δ - δ))).toReal
  set q₂ := (varrho N σ (Set.Ici (E + δ + δ))).toReal
  set q := (varrho N σ (Set.Ici E)).toReal
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hc : 3 * (η / δ) + θ = ε / (2 * N) := by
    rw [hηδ, hθdef]
    field_simp
    ring
  have hpos : 0 < ε / (2 * N) := by positivity
  have k1 : Real.pi * (p - q₁) < ε / (2 * N) := by linarith [h1.2]
  have k2 : Real.pi * (q₂ - p) < ε / (2 * N) := by linarith [h2.1]
  have k1' : p - q₁ < ε / (2 * N) := by
    by_cases hpq : p - q₁ ≤ 0
    · linarith
    · have hpq' := not_le.mp hpq
      nlinarith
  have k2' : q₂ - p < ε / (2 * N) := by
    by_cases hpq : q₂ - p ≤ 0
    · linarith
    · have hpq' := not_le.mp hpq
      nlinarith
  have e1 : (N : ℝ) * (p - q₁) < ε / 2 := by
    calc (N : ℝ) * (p - q₁) < N * (ε / (2 * N)) := mul_lt_mul_of_pos_left k1' hNr
      _ = ε / 2 := by field_simp
  have e2 : (N : ℝ) * (q₂ - p) < ε / 2 := by
    calc (N : ℝ) * (q₂ - p) < N * (ε / (2 * N)) := mul_lt_mul_of_pos_left k2' hNr
      _ = ε / 2 := by field_simp
  have m1 := mul_sub (N : ℝ) p q₁
  have m2 := mul_sub (N : ℝ) q₂ p
  constructor
  · linarith [c2.1]
  · linarith [c1.2]

/-! ## Integer masses at points outside `supp ϱ` -/

private lemma masses_empMeasure_apply_card (σ : Fin M → ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    empMeasure σ s = (M : ℝ≥0∞)⁻¹ * ((Finset.univ.filter fun i => σ i ∈ s).card : ℝ≥0∞) := by
  simp only [empMeasure, Measure.smul_apply, Measure.finsetSum_apply,
    Measure.dirac_apply' _ hs, smul_eq_mul]
  congr 1
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Set.indicator]

/-- Any `σ ≥ 0` with a positive entry satisfies (phi_bounded), (bound_Sigma) and (Sigma_gap) at
some `τ > 0`. -/
private lemma masses_densityAssumptions {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    {i₀ : Fin M} (hi₀ : 0 < σ i₀) : ∃ τ, DensityAssumptions τ N σ := by
  have hM : 0 < M := i₀.pos
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set S := ∑ i, σ i with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hσ i
  set τ : ℝ := min (min ((M : ℝ) / N) ((N : ℝ) / M))
    (min (1 / (S + 1)) (min (σ i₀ / 2) (1 / (M : ℝ)))) with hτdef
  have hτ : 0 < τ := by
    refine lt_min (lt_min (by positivity) (by positivity))
      (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hτ1 : τ ≤ (M : ℝ) / N := (min_le_left _ _).trans (min_le_left _ _)
  have hτ2 : τ ≤ (N : ℝ) / M := (min_le_left _ _).trans (min_le_right _ _)
  have hτ3 : τ ≤ 1 / (S + 1) := (min_le_right _ _).trans (min_le_left _ _)
  have hτ4 : τ ≤ σ i₀ / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hτ5 : τ ≤ 1 / (M : ℝ) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨τ, hτ, hσ, hτ1, ?_, ?_, ?_⟩
  · unfold phiRatio
    calc (M : ℝ) / N = ((N : ℝ) / M)⁻¹ := by rw [inv_div]
      _ ≤ τ⁻¹ := inv_anti₀ hτ hτ2
  · intro i
    have h1 : σ i ≤ S := Finset.single_le_sum (fun j _ => hσ j) (Finset.mem_univ i)
    have h3 : S + 1 ≤ τ⁻¹ := by
      have := inv_anti₀ hτ hτ3
      rwa [one_div, inv_inv] at this
    linarith
  · rw [masses_empMeasure_apply_card σ measurableSet_Icc, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, ENNReal.toReal_natCast]
    have hMτ : (M : ℝ) * τ ≤ 1 := by
      rw [le_div_iff₀ hMr] at hτ5
      linarith
    rw [inv_mul_le_iff₀ hMr]
    refine le_trans ?_ (show (M : ℝ) - 1 ≤ M * (1 - τ) by nlinarith)
    rw [le_sub_iff_add_le]
    norm_cast
    refine Nat.succ_le_of_lt (lt_of_lt_of_eq (Finset.card_lt_card (Finset.filter_ssubset.mpr
      ⟨i₀, Finset.mem_univ _, fun h => ?_⟩)) (by simp))
    have := h.2
    linarith

/-- `n(E) ∈ ℕ` at every `E > 0` outside `supp ϱ` (Lemma `lem:N_i`). -/
private lemma masses_nClass_int {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {E : ℝ} (hE : 0 < E) (hEs : E ∉ (varrho N σ).support) :
    ∃ d : ℕ, nClass N σ E = d := by
  obtain ⟨s₀, hs₀⟩ := hS
  have hs₀' := Finset.mem_filter.mp hs₀
  obtain ⟨i₀, -, hi₀⟩ := Finset.mem_image.mp hs₀'.1
  obtain ⟨τ, hda⟩ := masses_densityAssumptions hσ hN (i₀ := i₀) (by rw [hi₀]; exact hs₀'.2)
  have := isProbabilityMeasure_varrho N σ hσ hN
  set A := (varrho N σ).support ∩ Set.Ici E with hAdef
  rcases A.eq_empty_or_nonempty with hA | hA
  · refine ⟨0, ?_⟩
    have h0 : varrho N σ (Set.Ici E) = 0 := by
      refine measure_mono_null (show Set.Ici E ⊆ (varrho N σ).supportᶜ from
        fun x hx hxs => ?_) Measure.measure_compl_support
      have hxA : x ∈ A := ⟨hxs, hx⟩
      rw [hA] at hxA
      exact hxA
    simp [nClass, h0]
  · have hAc : IsClosed A := Measure.isClosed_support.inter isClosed_Ici
    have hAb : BddBelow A := ⟨E, fun x hx => hx.2⟩
    have hsA := hAc.csInf_mem hA hAb
    set s := sInf A with hsdef
    have hsE : E < s := lt_of_le_of_ne hsA.2 (fun h => hEs (h ▸ hsA.1))
    have hlow : ∀ x ∈ A, s ≤ x := fun x hx => csInf_le hAb hx
    have hIco : varrho N σ (Set.Ico E s) = 0 := by
      refine measure_mono_null (show Set.Ico E s ⊆ (varrho N σ).supportᶜ from
        fun x hx hxs => ?_) Measure.measure_compl_support
      exact absurd (hlow x ⟨hxs, hx.1⟩) (not_le.mpr hx.2)
    have hn : nClass N σ E = nClass N σ s := by
      have h := masses_nClass_sub hσ hN hsE.le
      rw [hIco, ENNReal.toReal_zero, mul_zero] at h
      linarith
    have hs0 : 0 < s := hE.trans hsE
    obtain ⟨k, hk1, hkp, hks⟩ :=
      (mem_support_varrho_iff N σ hσ hN ⟨s₀, hs₀⟩ hs0).mp hsA.1
    have hse : s = edgeVal N σ (2 * k) := by
      by_contra hne
      have hlt : edgeVal N σ (2 * k) < s := lt_of_le_of_ne hks.1 (Ne.symm hne)
      set y := max (edgeVal N σ (2 * k)) ((E + s) / 2) with hy
      have hy1 : y < s := max_lt hlt (by linarith)
      have hyE : E ≤ y := le_trans (by linarith) (le_max_right _ _)
      have hy0 : 0 < y := lt_of_lt_of_le hE hyE
      have hyband : y ∈ Set.Icc (edgeVal N σ (2 * k)) (edgeVal N σ (2 * k - 1)) :=
        ⟨le_max_left _ _, hy1.le.trans hks.2⟩
      have hysupp :=
        (mem_support_varrho_iff N σ hσ hN ⟨s₀, hs₀⟩ hy0).mpr ⟨k, hk1, hkp, hyband⟩
      exact absurd (hlow y ⟨hysupp, hyE⟩) (not_le.mpr hy1)
    have hcnt := (nClass_edgeVal hda hk1 hkp).2 (hse ▸ hs0)
    exact ⟨cumCount N σ k, by rw [hn, hse, hcnt]⟩

/-- If `n(E) > 0` for some `E > 0`, then `σ` has a positive entry. -/
private lemma masses_posVals_nonempty {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {E : ℝ}
    (hE : 0 < E) (hn : 0 < nClass N σ E) : (posVals σ).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have hcard : (Finset.univ.filter fun i => 0 < σ i).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _ hi
    have hmem : σ i ∈ posVals σ :=
      Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), hi⟩
    rw [hne] at hmem
    simp at hmem
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h0 := varrho_singleton_zero N σ hσ hN
  rw [hcard, Nat.cast_zero, sub_zero, max_eq_left (Nat.cast_nonneg _)] at h0
  have h1 : (varrho N σ {0}).toReal = 1 :=
    mul_left_cancel₀ hNr.ne' (h0.trans (mul_one _).symm)
  have := isProbabilityMeasure_varrho N σ hσ hN
  have h2 : Set.Ici E ⊆ ({0} : Set ℝ)ᶜ := fun x hx h => by
    rw [Set.mem_singleton_iff] at h
    rw [h, Set.mem_Ici] at hx
    linarith
  have h3 : varrho N σ ({0} : Set ℝ)ᶜ = 0 := by
    rw [prob_compl_eq_one_sub (measurableSet_singleton 0),
      (ENNReal.toReal_eq_one_iff _).mp h1, tsub_self]
  have h4 : nClass N σ E = 0 := by
    unfold nClass
    rw [measure_mono_null h2 h3]
    simp
  linarith

/-- The classical locations converge where they are positive. -/
theorem tendsto_gammaLoc_regS {K : ℕ} (hN : 1 ≤ N) (T : Matrix (Fin M) (Fin K) ℝ) {j : ℕ}
    (hj : 0 < gammaLoc N (specOf (T * Tᵀ)) j) :
    Tendsto (fun κ => gammaLoc N (specOf (regS κ (Tᵀ * T))) j) (𝓝[>] 0)
      (𝓝 (gammaLoc N (specOf (T * Tᵀ)) j)) := by
  have hN0 : 0 < N := hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set σ := specOf (T * Tᵀ) with hσdef
  have hσ : ∀ i, 0 ≤ σ i := masses_specOf_nonneg T
  set γ := gammaLoc N σ j with hγ
  obtain ⟨-, hbdd⟩ := masses_gammaLoc_set hj
  have hnγ : nClass N σ γ = (j : ℝ) - 1 / 2 := nClass_gammaLoc_of_pos hσ hN0 hj
  have hanti := masses_nClass_anti hσ hN0
  have := isProbabilityMeasure_varrho N σ hσ hN0
  have hj1 : (1 : ℝ) ≤ j := by
    have h0 : 0 ≤ nClass N σ γ := by unfold nClass; positivity
    rw [hnγ] at h0
    have : (0 : ℝ) < j := by linarith
    have : 0 < j := by exact_mod_cast this
    exact_mod_cast this
  have hS : (posVals σ).Nonempty := masses_posVals_nonempty hσ hN0 hj (by rw [hnγ]; linarith)
  -- `n < j − 1/2` to the right of `γ_j`
  have hright : ∀ δ, 0 < δ → nClass N σ (γ + δ) < (j : ℝ) - 1 / 2 := by
    intro δ hδ
    by_contra h
    have : γ + δ ≤ γ := le_csSup hbdd ⟨by linarith, not_lt.mp h⟩
    linarith
  -- `n > j − 1/2` to the left of `γ_j`
  have hleft : ∀ δ, 0 < δ → δ < γ → (j : ℝ) - 1 / 2 < nClass N σ (γ - δ) := by
    intro δ hδ hδγ
    have hge : (j : ℝ) - 1 / 2 ≤ nClass N σ (γ - δ) := hnγ ▸ hanti (by linarith)
    rcases hge.lt_or_eq with h | h
    · exact h
    · exfalso
      have hsub := masses_nClass_sub hσ hN0 (show γ - δ ≤ γ by linarith)
      rw [← h, hnγ, sub_self] at hsub
      have hnull : varrho N σ (Set.Ico (γ - δ) γ) = 0 := by
        have h0 : (varrho N σ (Set.Ico (γ - δ) γ)).toReal = 0 := by
          rcases mul_eq_zero.mp hsub.symm with h' | h'
          · exact absurd h' hNr.ne'
          · exact h'
        exact ((ENNReal.toReal_eq_zero_iff _).mp h0).resolve_right (measure_ne_top _ _)
      set E' := γ - δ / 2 with hE'
      have hE'0 : 0 < E' := by linarith
      have hE's : E' ∉ (varrho N σ).support := by
        rw [Measure.notMem_support_iff_exists]
        exact ⟨Set.Ioo (γ - δ) γ, Ioo_mem_nhds (by linarith) (by linarith),
          measure_mono_null Set.Ioo_subset_Ico_self hnull⟩
      obtain ⟨d, hd⟩ := masses_nClass_int hσ hN0 hS hE'0 hE's
      have hE'n : nClass N σ E' = (j : ℝ) - 1 / 2 :=
        le_antisymm (h ▸ hanti (by linarith)) (hnγ ▸ hanti (by linarith))
      rw [hd] at hE'n
      have h2 : ((2 * d : ℕ) : ℝ) + 1 = ((2 * j : ℕ) : ℝ) := by
        push_cast
        linarith
      have h3 : 2 * d + 1 = 2 * j := by exact_mod_cast h2
      omega
  rw [Metric.tendsto_nhds]
  intro ε hε
  set δ := min (ε / 2) (γ / 2) with hδdef
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδγ : δ < γ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have t1 := tendsto_nClass_regS hN T (E := γ + δ) (by linarith)
  have t2 := tendsto_nClass_regS hN T (E := γ - δ) (by linarith)
  have hr := hright δ hδ
  have hl := hleft δ hδ hδγ
  filter_upwards [t1.eventually (gt_mem_nhds hr), t2.eventually (lt_mem_nhds hl),
    self_mem_nhdsWithin] with κ h1 h2 hκ
  have hκ0 : (0 : ℝ) < κ := hκ
  have hσκ := masses_specOf_regS_nonneg hκ0 T
  have hantiκ := masses_nClass_anti hσκ hN0
  set Sκ : Set ℝ := {E | 0 < E ∧ (j : ℝ) - 1 / 2 ≤ nClass N (specOf (regS κ (Tᵀ * T))) E}
    with hSκ
  have hmem : γ - δ ∈ Sκ := ⟨by linarith, h2.le⟩
  have hub : ∀ E ∈ Sκ, E ≤ γ + δ := by
    intro E hE
    by_contra hlt
    have := hantiκ (not_le.mp hlt).le
    linarith [hE.2]
  have hlo : γ - δ ≤ gammaLoc N (specOf (regS κ (Tᵀ * T))) j := le_csSup ⟨γ + δ, hub⟩ hmem
  have hhi : gammaLoc N (specOf (regS κ (Tᵀ * T))) j ≤ γ + δ := csSup_le ⟨_, hmem⟩ hub
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-! ## Instances -/

/-- `T = (1; 0)`, `Σ = T Tᵀ = diag(1, 0)`. -/
local notation "masses_Ta" => (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)

/-- `T = (1 1)`, `Σ = T Tᵀ = (2)`, `Tᵀ T = ((1, 1), (1, 1))`. -/
local notation "masses_Tb" => (!![1, 1] : Matrix (Fin 1) (Fin 2) ℝ)

/-- `tendsto_nClass_regS` at `T = (1 1)`, `N = 2`, `E = 1`. -/
example : Tendsto (fun κ => nClass 2 (specOf (regS κ (masses_Tbᵀ * masses_Tb))) 1) (𝓝[>] 0)
    (𝓝 (nClass 2 (specOf (masses_Tb * masses_Tbᵀ)) 1)) :=
  tendsto_nClass_regS (by norm_num) _ (by norm_num)

#print axioms Anisotropic.nClass_gammaLoc_of_pos
#print axioms Anisotropic.outside_regS
#print axioms Anisotropic.tendsto_nClass_regS
#print axioms Anisotropic.tendsto_gammaLoc_regS

end Anisotropic
