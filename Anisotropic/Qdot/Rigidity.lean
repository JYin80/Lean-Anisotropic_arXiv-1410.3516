import Anisotropic.Density.Count
import Anisotropic.Density.Critical
import Anisotropic.Entrywise.DiagModel
import Anisotropic.Framework.Domination
import Anisotropic.Framework.Model
import Anisotropic.GeneralT.Edges
import Anisotropic.GeneralT.Model
import Anisotropic.GeneralT.Rigidity
import Anisotropic.Instances.MarchenkoPasturTwo
import Anisotropic.Instances.Models
import Anisotropic.Probability.NormBound.GaussianLower
import Anisotropic.Qdot.Defs
import Anisotropic.Qdot.RigidityLocal
import Anisotropic.Rigidity.Defs

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # Theorem 11.3 with the classical quantities of `N − 1` samples, under (T_diag) and for general `T`, and the reading with the quantities of `N` -/

/-! ## The density assumptions at `N − 1`, and boundary values of `m` off the support -/

private lemma rd_cast_pred (hN : 2 ≤ N) : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
  rw [Nat.cast_sub (by omega)]; simp

/-- (phi_bounded), (bound_Sigma), (Sigma_gap) at `N − 1` with `τ/2`, from those at `N` with `τ`. -/
private lemma rd_da_pred {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) (hN : 2 ≤ N) :
    DensityAssumptions (τ / 2) (N - 1) σ := by
  have hτ := h.pos
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hc := rd_cast_pred hN
  have hφl := h.phi_lower
  have hφu := h.phi_upper
  unfold phiRatio at hφl hφu
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  refine ⟨by positivity, h.nonneg, ?_, ?_, ?_, ?_⟩
  · unfold phiRatio
    rw [hc, le_div_iff₀ hN1]
    rw [le_div_iff₀ (by linarith)] at hφl
    nlinarith
  · unfold phiRatio
    rw [hc, div_le_iff₀ hN1]
    rw [div_le_iff₀ (by linarith)] at hφu
    have : (τ / 2)⁻¹ = 2 * τ⁻¹ := by field_simp
    rw [this]
    have hτi : 0 < τ⁻¹ := inv_pos.mpr hτ
    nlinarith
  · intro i
    have := h.bound_Sigma i
    have : τ⁻¹ ≤ (τ / 2)⁻¹ := inv_anti₀ (by positivity) (by linarith)
    linarith
  · have := (h.mono (show 0 < τ / 2 by positivity) (by linarith)).Sigma_gap
    linarith

private lemma rd_posVals_nonempty {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) :
    (posVals σ).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have hall : ∀ i, σ i = 0 := by
    intro i
    rcases (h.nonneg i).eq_or_lt with h0 | hpos
    · exact h0.symm
    · have : σ i ∈ posVals σ :=
        Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hpos⟩
      rw [hne] at this
      exact absurd this (Finset.notMem_empty _)
  have hτ := h.pos
  have hM : 0 < M := by
    by_contra h0
    have hM0 : M = 0 := by omega
    have := h.phi_lower
    unfold phiRatio at this
    rw [hM0] at this
    simp at this
    linarith
  have hgap := h.Sigma_gap
  have hfull : empMeasure σ (Set.Icc 0 τ) = 1 := by
    simp only [empMeasure, Measure.smul_apply, Measure.finsetSum_apply,
      Measure.dirac_apply' _ measurableSet_Icc, smul_eq_mul]
    have : ∀ i, (Set.Icc 0 τ).indicator (1 : ℝ → ℝ≥0∞) (σ i) = 1 := by
      intro i
      rw [hall i]
      simp [Set.indicator, hτ.le]
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast hM.ne') (ENNReal.natCast_ne_top _)
  rw [hfull, ENNReal.toReal_one] at hgap
  linarith
private lemma rd_im_mFun_eq (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hK : 0 < K) {z : ℂ}
    (hz : 0 < z.im) :
    (mFun K σ z).im = ∫ t, z.im / ((t - z.re) ^ 2 + z.im ^ 2) ∂(varrho K σ) := by
  have := isProbabilityMeasure_varrho K σ hσ hK
  have hne : ∀ t : ℝ, (t : ℂ) - z ≠ 0 := fun t h => by
    have := congrArg Complex.im h; simp at this; linarith
  have hint : Integrable (fun t : ℝ => ((t : ℂ) - z)⁻¹) (varrho K σ) := by
    refine Integrable.of_bound ?_ (z.im)⁻¹ (ae_of_all _ fun t => ?_)
    · exact ((Complex.continuous_ofReal.sub continuous_const).inv₀ hne).aestronglyMeasurable
    · rw [norm_inv]
      refine inv_anti₀ hz ?_
      have h := Complex.abs_im_le_norm ((t : ℂ) - z)
      simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] at h
      exact (le_abs_self _).trans h
  have hm : mFun K σ z = ∫ t : ℝ, ((t : ℂ) - z)⁻¹ ∂(varrho K σ) := by
    rw [← resolventTransform_varrho K σ hσ hK hz, resolventTransform_apply]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp [resolvent, Ring.inverse_eq_inv']
  rw [hm]
  have := integral_im (𝕜 := ℂ) hint
  simp only [RCLike.im_to_complex] at this
  rw [← this]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  dsimp only
  rw [Complex.inv_im, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im]
  ring

/-- `Im m(z) ≤ Im z / d²` when the support of `ϱ` is at distance `≥ d` from `Re z`. -/
private lemma rd_im_le_of_dist (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hK : 0 < K) {z : ℂ}
    (hz : 0 < z.im) {d : ℝ} (hd : 0 < d)
    (hsupp : ∀ t ∈ (varrho K σ).support, d ≤ |t - z.re|) :
    (mFun K σ z).im ≤ z.im / d ^ 2 := by
  have := isProbabilityMeasure_varrho K σ hσ hK
  rw [rd_im_mFun_eq K σ hσ hK hz]
  have hb : ∀ᵐ t ∂(varrho K σ), z.im / ((t - z.re) ^ 2 + z.im ^ 2) ≤ z.im / d ^ 2 := by
    filter_upwards [Measure.support_mem_ae (μ := varrho K σ)] with t ht
    have h1 := hsupp t ht
    have h2 : d ^ 2 ≤ (t - z.re) ^ 2 := by
      have := pow_le_pow_left₀ hd.le h1 2
      rwa [sq_abs] at this
    exact div_le_div_of_nonneg_left hz.le (by positivity) (by nlinarith)
  calc ∫ t, z.im / ((t - z.re) ^ 2 + z.im ^ 2) ∂(varrho K σ)
      ≤ ∫ _t, z.im / d ^ 2 ∂(varrho K σ) := integral_mono_ae (by
        refine Integrable.of_bound ?_ (1 / z.im) (ae_of_all _ fun t => ?_)
        · exact (continuous_const.div (by fun_prop) fun t => by positivity).aestronglyMeasurable
        · rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_le_div_iff₀ (by positivity) hz]
          nlinarith [sq_nonneg (t - z.re)]) (integrable_const _) hb
    _ = z.im / d ^ 2 := by simp

/-- The path `y ↦ E + i y`, `y ↓ 0`, tends to `E` within `ℂ₊`. -/
private lemma rd_tendsto_path (E : ℝ) :
    Tendsto (fun y : ℝ => (E : ℂ) + (y : ℂ) * Complex.I) (𝓝[>] 0) (𝓝[upperHalf] (E : ℂ)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : Tendsto (fun y : ℝ => (E : ℂ) + (y : ℂ) * Complex.I) (𝓝 0) (𝓝 ((E : ℂ) + 0)) := by
      have := ((Complex.continuous_ofReal.tendsto 0).mul_const Complex.I).const_add (E : ℂ)
      simpa using this
    simpa using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy
    simp [upperHalf]
    exact hy

private lemma rd_tendsto_mFun_path (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {E : ℝ}
    (hE : E ≠ 0) :
    Tendsto (fun y : ℝ => mFun K σ ((E : ℂ) + (y : ℂ) * Complex.I)) (𝓝[>] 0)
      (𝓝 (mExt K σ E)) :=
  (tendsto_mFun_of_ne_zero K σ hσ hE).comp (rd_tendsto_path E)

private lemma rd_path_im {E y : ℝ} : ((E : ℂ) + (y : ℂ) * Complex.I).im = y := by simp

private lemma rd_path_re {E y : ℝ} : ((E : ℂ) + (y : ℂ) * Complex.I).re = E := by simp

/-- Off the support, `m(E + i0)` is real. -/
private lemma rd_mExt_im_eq_zero (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hK : 0 < K) {E : ℝ}
    (hE : E ≠ 0) {d : ℝ} (hd : 0 < d) (hsupp : ∀ t ∈ (varrho K σ).support, d ≤ |t - E|) :
    (mExt K σ E).im = 0 := by
  have ht := (Complex.continuous_im.tendsto _).comp (rd_tendsto_mFun_path K σ hσ hE)
  refine le_antisymm ?_ (im_mExt_nonneg K σ hσ hE)
  have hup : Tendsto (fun y : ℝ => y / d ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun y : ℝ => y / d ^ 2) (𝓝 0) (𝓝 (0 / d ^ 2)) :=
      (continuous_id.div_const _).tendsto 0
    rw [zero_div] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto_of_tendsto ht hup ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy' : 0 < ((E : ℂ) + (y : ℂ) * Complex.I).im := by rw [rd_path_im]; exact hy
  have := rd_im_le_of_dist K σ hσ hK hy' hd (by rw [rd_path_re]; exact hsupp)
  simpa [rd_path_im] using this

/-- A real boundary value `x = m(E + i0)`, `E ≠ 0`: `x ≠ 0`, `x` is not a pole, `f(x) = E`. -/
private lemma rd_real_facts (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hK : 0 < K) {E : ℝ}
    (hE : E ≠ 0) (him : (mExt K σ E).im = 0) :
    mExt K σ E = ((mExt K σ E).re : ℂ) ∧ (mExt K σ E).re ≠ 0 ∧
      (∀ i, 1 + σ i * (mExt K σ E).re ≠ 0) ∧ fR K σ (mExt K σ E).re = E := by
  set w := mExt K σ E with hw
  have hwx : w = (w.re : ℂ) := by
    apply Complex.ext <;> simp [him]
  have hev := scPoly_eval_mExt K σ hσ hE
  rw [← hw] at hev
  have hw0 : w ≠ 0 := by
    intro h; rw [h, scPoly_eval_zero] at hev; norm_num at hev
  have hx0 : w.re ≠ 0 := by
    intro h; apply hw0; rw [hwx, h]; simp
  have hpole : ∀ i, 1 + σ i * w.re ≠ 0 := by
    intro i h
    rcases (hσ i).eq_or_lt with h0 | hpos
    · rw [← h0] at h; simp at h
    · have hs : σ i ∈ posVals σ :=
        Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hpos⟩
      have hx : w = -((σ i : ℂ))⁻¹ := by
        rw [hwx]
        have : w.re = -(σ i)⁻¹ := by field_simp; linarith
        rw [this]; push_cast; ring
      exact scPoly_eval_pole K σ hK (E : ℂ) hs (hx ▸ hev)
  have hpole' : ∀ s ∈ posVals σ, 1 + (s : ℂ) * w ≠ 0 := by
    intro s hs h
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hs).1
    apply hpole i
    have := congrArg Complex.re h
    rw [hwx] at this
    simp at this
    rw [hi]; linarith
  have hev2 := scPoly_eval K σ hσ (E : ℂ) hw0 hpole'
  rw [hev] at hev2
  have hprod : ∏ s ∈ posVals σ, (1 + (s : ℂ) * w) ≠ 0 := Finset.prod_ne_zero_iff.mpr hpole'
  have hf : fC K σ w = E := by
    have := mul_eq_zero.mp hev2.symm
    rcases this with h | h
    · exact absurd h (mul_ne_zero hw0 hprod)
    · exact sub_eq_zero.mp h
  refine ⟨hwx, hx0, hpole, ?_⟩
  have := hf
  rw [hwx, fC_ofReal] at this
  exact_mod_cast this

/-- Off the support, `f'(m(E)) ≥ dist(E, supp ϱ)²`. -/
private lemma rd_fR1_ge_dist (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hK : 0 < K) {E : ℝ}
    (hE : E ≠ 0) {d : ℝ} (hd : 0 < d) (hsupp : ∀ t ∈ (varrho K σ).support, d ≤ |t - E|) :
    d ^ 2 ≤ fR1 K σ (mExt K σ E).re := by
  have him := rd_mExt_im_eq_zero K σ hσ hK hE hd hsupp
  obtain ⟨hwx, hx0, hpole, -⟩ := rd_real_facts K σ hσ hK hE him
  set x := (mExt K σ E).re
  set g : ℂ → ℝ := fun w => (‖w‖ ^ 2)⁻¹ - ∑ i, σ i ^ 2 / (K * ‖1 + (σ i : ℂ) * w‖ ^ 2) with hg
  have hgx : g x = fR1 K σ x := by
    simp only [hg, fR1]
    congr 1
    · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    · refine Finset.sum_congr rfl fun i _ => ?_
      congr 2
      have : (1 + (σ i : ℂ) * (x : ℂ)) = ((1 + σ i * x : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hcont : ContinuousAt g (x : ℂ) := by
    have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx0
    refine ContinuousAt.sub ?_ ?_
    · exact ((continuous_norm.pow 2).continuousAt).inv₀
        (pow_pos (norm_pos_iff.mpr hxc) 2).ne'
    · refine tendsto_finsetSum _ fun i _ => ?_
      refine continuousAt_const.div (continuousAt_const.mul
        ((continuous_norm.comp (continuous_const.add (continuous_const.mul continuous_id))).pow 2
          |>.continuousAt)) ?_
      have h1 : (1 + (σ i : ℂ) * (x : ℂ)) ≠ 0 := by
        have : (1 + (σ i : ℂ) * (x : ℂ)) = ((1 + σ i * x : ℝ) : ℂ) := by push_cast; ring
        rw [this]; exact_mod_cast hpole i
      have : (0 : ℝ) < K := by exact_mod_cast hK
      have h2 : 0 < ‖1 + (σ i : ℂ) * (x : ℂ)‖ := norm_pos_iff.mpr h1
      positivity
  have ht : Tendsto (fun y : ℝ => g (mFun K σ ((E : ℂ) + (y : ℂ) * Complex.I))) (𝓝[>] 0)
      (𝓝 (g x)) := by
    have := rd_tendsto_mFun_path K σ hσ hE
    rw [hwx] at this
    exact hcont.tendsto.comp this
  rw [← hgx]
  refine ge_of_tendsto ht ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy' : 0 < ((E : ℂ) + (y : ℂ) * Complex.I).im := by rw [rd_path_im]; exact hy
  obtain ⟨hm, hfm⟩ := mFun_spec K σ hσ hy'
  have hi := im_fC K σ (mFun K σ ((E : ℂ) + (y : ℂ) * Complex.I))
  rw [hfm, rd_path_im] at hi
  have hb := rd_im_le_of_dist K σ hσ hK hy' hd (by rw [rd_path_re]; exact hsupp)
  rw [rd_path_im] at hb
  change d ^ 2 ≤ (‖mFun K σ ((E : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2)⁻¹ -
    ∑ i, σ i ^ 2 / (K * ‖1 + (σ i : ℂ) * mFun K σ ((E : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2)
  set G := (‖mFun K σ ((E : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2)⁻¹ -
    ∑ i, σ i ^ 2 / (K * ‖1 + (σ i : ℂ) * mFun K σ ((E : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2)
  set q := (mFun K σ ((E : ℂ) + (y : ℂ) * Complex.I)).im
  have hq : y = q * G := hi
  rw [le_div_iff₀ (by positivity)] at hb
  have hd2 : 0 < d ^ 2 := by positivity
  nlinarith

/-- `ϱ` does not charge an interval of `(0, ∞)` on which `m(E + i0)` is real. -/
private lemma rd_varrho_Ioo_eq_zero (K : ℕ) (σ : Fin M → ℝ) {α β : ℝ} (hα : 0 ≤ α)
    (h : ∀ E ∈ Set.Ioo α β, (mExt K σ E).im = 0) : varrho K σ (Set.Ioo α β) = 0 := by
  have hA : MeasurableSet (Set.Ioo α β) := measurableSet_Ioo
  have h0 : (0 : ℝ) ∉ Set.Ioo α β := fun h0 => by linarith [h0.1]
  rw [varrho, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hA,
    Set.indicator_of_notMem h0, smul_zero, zero_add, withDensity_apply _ hA,
    Measure.restrict_restrict hA]
  have : ∫⁻ x in Set.Ioo α β ∩ Set.Ioi 0, ENNReal.ofReal (rhoDens K σ x) =
      ∫⁻ _x in Set.Ioo α β ∩ Set.Ioi 0, 0 :=
    setLIntegral_congr_fun (hA.inter measurableSet_Ioi) fun x hx => by
      simp only [rhoDens]
      rw [h x hx.1, zero_div, ENNReal.ofReal_zero]
  rw [this, lintegral_zero]

private lemma rd_not_mem_support_of_Ioo (K : ℕ) (σ : Fin M → ℝ) {α β E : ℝ} (hα : 0 ≤ α)
    (h : ∀ E ∈ Set.Ioo α β, (mExt K σ E).im = 0) (hE : E ∈ Set.Ioo α β) :
    E ∉ (varrho K σ).support :=
  Measure.notMem_support_iff_exists.2 ⟨_, Ioo_mem_nhds hE.1 hE.2, rd_varrho_Ioo_eq_zero K σ hα h⟩

/-- Near a point with `f' > 0`, `f` has a local inverse given by `m(· + i0)`. -/
private lemma rd_local_inv (K : ℕ) (σ : Fin M → ℝ) {y : ℝ}
    (hy : y ≠ 0) (hy' : ∀ i, 1 + σ i * y ≠ 0) (hd : 0 < fR1 K σ y) :
    ∃ r > 0, (∀ y' ∈ Set.Icc (y - r) (y + r), y' ≠ 0 ∧ (∀ i, 1 + σ i * y' ≠ 0) ∧
      0 < fR1 K σ y') ∧ StrictMonoOn (fR K σ) (Set.Icc (y - r) (y + r)) := by
  have hev : ∀ᶠ y' in 𝓝 y, y' ≠ 0 ∧ (∀ i, 1 + σ i * y' ≠ 0) ∧ 0 < fR1 K σ y' := by
    refine (eventually_ne_nhds hy).and ((?_ : ∀ᶠ y' in 𝓝 y, ∀ i, 1 + σ i * y' ≠ 0).and ?_)
    · refine Filter.eventually_all.2 fun i => ?_
      exact (continuous_const.add (continuous_const.mul continuous_id)).continuousAt.eventually_ne
        (hy' i)
    · exact (hasDerivAt_fR1 K σ hy hy').continuousAt.eventually (lt_mem_nhds hd)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hgood : ∀ y' ∈ Set.Icc (y - ε / 2) (y + ε / 2), y' ≠ 0 ∧ (∀ i, 1 + σ i * y' ≠ 0) ∧
      0 < fR1 K σ y' := fun y' hy'' => hball (by
    rw [Real.dist_eq]
    have : |y' - y| ≤ ε / 2 := abs_le.2 ⟨by linarith [hy''.1], by linarith [hy''.2]⟩
    linarith)
  refine ⟨ε / 2, by positivity, hgood, ?_⟩
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _) ?_ fun x hx => ?_
  · intro x hx
    obtain ⟨h0, h1, -⟩ := hgood x hx
    exact (hasDerivAt_fR K σ h0 h1).continuousAt.continuousWithinAt
  · have hx' := interior_subset hx
    obtain ⟨h0, h1, h2⟩ := hgood x hx'
    rw [(hasDerivAt_fR K σ h0 h1).deriv]
    exact h2

/-- `f' > 0` at `y`: then `m(f(y) + i0) = y`, and `f(y) > 0` is not in the support of `ϱ`. -/
private lemma rd_not_mem_support (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hK : 0 < K) {y : ℝ}
    (hy : y ≠ 0) (hy' : ∀ i, 1 + σ i * y ≠ 0) (hd : 0 < fR1 K σ y) (hf : 0 < fR K σ y) :
    fR K σ y ∉ (varrho K σ).support := by
  obtain ⟨r, hr, hgood, hmono⟩ := rd_local_inv K σ hy hy' hd
  have hlo : fR K σ (y - r) < fR K σ y :=
    hmono ⟨le_rfl, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
  have hhi : fR K σ y < fR K σ (y + r) :=
    hmono ⟨by linarith, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
  have hcont : ContinuousOn (fR K σ) (Set.Icc (y - r) (y + r)) := fun x hx => by
    obtain ⟨h0, h1, -⟩ := hgood x hx
    exact (hasDerivAt_fR K σ h0 h1).continuousAt.continuousWithinAt
  refine rd_not_mem_support_of_Ioo K σ (le_max_left 0 (fR K σ (y - r)))
    (β := fR K σ (y + r)) (fun E hE => ?_) ⟨max_lt hf hlo, hhi⟩
  have hE0 : 0 < E := lt_of_le_of_lt (le_max_left _ _) hE.1
  obtain ⟨y', hy'm, hy'E⟩ := intermediate_value_Icc (show y - r ≤ y + r by linarith) hcont
    ⟨(le_max_right _ _).trans hE.1.le, hE.2.le⟩
  obtain ⟨h0, h1, h2⟩ := hgood y' hy'm
  have := mExt_fR_of_pos K σ hσ hK h0 h1 (by rw [hy'E]; exact hE0.ne') h2
  rw [hy'E] at this
  rw [this]
  simp

/-- `t ↦ m(t + i0)` is continuous on `[a, b] ⊂ (0, ∞)`. -/
private lemma rd_cont_mExt (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun t : ℝ => mExt K σ t) (Set.Icc a b) := by
  refine (continuousOn_mExt K σ hσ).comp Complex.continuous_ofReal.continuousOn fun t ht => ?_
  right
  refine ⟨by simp, ?_⟩
  have : (t : ℂ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by linarith [ht.1])
  exact this


private lemma rd_fR_mul (K : ℕ) (σ : Fin M → ℝ) (hK : 0 < K) (x : ℝ) :
    (K : ℝ) * fR K σ x = -(K : ℝ) * x⁻¹ + ∑ i, σ i / (1 + σ i * x) := by
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  unfold fR
  rw [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : 1 + σ i * x = 0
    · simp [h]
    · field_simp

private lemma rd_fR1_mul (K : ℕ) (σ : Fin M → ℝ) (hK : 0 < K) (x : ℝ) :
    (K : ℝ) * fR1 K σ x = (K : ℝ) * (x ^ 2)⁻¹ - ∑ i, σ i ^ 2 / (1 + σ i * x) ^ 2 := by
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  unfold fR1
  rw [mul_sub, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : 1 + σ i * x = 0
  · simp [h]
  · field_simp

/-- `(N − 1) f_{N−1} = N f_N + x⁻¹`. -/
private lemma rd_fR_pred (σ : Fin M → ℝ) (hN : 2 ≤ N) (x : ℝ) :
    ((N : ℝ) - 1) * fR (N - 1) σ x = N * fR N σ x + x⁻¹ := by
  have h1 := rd_fR_mul (N - 1) σ (by omega) x
  have h2 := rd_fR_mul N σ (by omega) x
  rw [rd_cast_pred hN] at h1
  linear_combination h1 - h2

/-- `(N − 1) f'_{N−1} = N f'_N − x⁻²`. -/
private lemma rd_fR1_pred (σ : Fin M → ℝ) (hN : 2 ≤ N) (x : ℝ) :
    ((N : ℝ) - 1) * fR1 (N - 1) σ x = N * fR1 N σ x - (x ^ 2)⁻¹ := by
  have h1 := rd_fR1_mul (N - 1) σ (by omega) x
  have h2 := rd_fR1_mul N σ (by omega) x
  rw [rd_cast_pred hN] at h1
  linear_combination h1 - h2

/-- `C(τ/2)⁻¹ ≤ |m(E + i0)| ≤ C(τ/2)` for `τ ≤ E ≤ τ⁻¹`. -/
private lemma rd_mExt_norm_bounds {τ : ℝ} {K : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ K σ)
    {E : ℝ} (h1 : τ ≤ E) (h2 : E ≤ τ⁻¹) :
    (genPropConst (τ / 2))⁻¹ ≤ ‖mExt K σ E‖ ∧ ‖mExt K σ E‖ ≤ genPropConst (τ / 2) := by
  have hτ := h.pos
  have hσ := h.nonneg
  have h2' := h.mono (show 0 < τ / 2 by positivity) (by linarith)
  have hE : E ≠ 0 := by linarith
  have ht := (continuous_norm.tendsto _).comp (rd_tendsto_mFun_path K σ hσ hE)
  have hev : ∀ᶠ y : ℝ in 𝓝[>] 0, (genPropConst (τ / 2))⁻¹ ≤
      ‖mFun K σ ((E : ℂ) + (y : ℂ) * Complex.I)‖ ∧
        ‖mFun K σ ((E : ℂ) + (y : ℂ) * Complex.I)‖ ≤ genPropConst (τ / 2) := by
    have hτi : 0 < τ⁻¹ := inv_pos.mpr hτ
    filter_upwards [Ioo_mem_nhdsGT hτi] with y hy
    have hy' : 0 < ((E : ℂ) + (y : ℂ) * Complex.I).im := by rw [rd_path_im]; exact hy.1
    have hn1 : τ / 2 ≤ ‖(E : ℂ) + (y : ℂ) * Complex.I‖ := by
      have := Complex.abs_re_le_norm ((E : ℂ) + (y : ℂ) * Complex.I)
      rw [rd_path_re, abs_of_pos (by linarith)] at this
      linarith
    have hn2 : ‖(E : ℂ) + (y : ℂ) * Complex.I‖ ≤ (τ / 2)⁻¹ := by
      have e : (τ / 2)⁻¹ = 2 * τ⁻¹ := by field_simp
      rw [e]
      calc ‖(E : ℂ) + (y : ℂ) * Complex.I‖ ≤ ‖(E : ℂ)‖ + ‖(y : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = |E| + |y| := by simp
        _ ≤ 2 * τ⁻¹ := by
            rw [abs_of_pos (by linarith), abs_of_pos hy.1]; linarith [hy.2]
    obtain ⟨a, b, -⟩ := gen_prop_m h2' hy' hn1 hn2
    exact ⟨a, b⟩
  exact ⟨ge_of_tendsto ht (hev.mono fun y hy => hy.1), le_of_tendsto ht (hev.mono fun y hy => hy.2)⟩


/-- `ϱ` is a probability measure, so its support is nonempty. -/
private lemma rd_supp_nonempty {τ : ℝ} {K : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ K σ)
    (hK : 0 < K) : (varrho K σ).support.Nonempty := by
  have := isProbabilityMeasure_varrho K σ h.nonneg hK
  exact Measure.nonempty_support (IsProbabilityMeasure.ne_zero _)

/-- `0 ≤ a_k ≤ 2τ⁻¹(1 + τ⁻¹)` for `1 ≤ k ≤ 2p`. -/
private lemma rd_edge_mem {τ : ℝ} {K : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ K σ)
    (hK : 0 < K) {k : ℕ} (hk : 1 ≤ k) (hkp : k ≤ 2 * numBands K σ) :
    0 ≤ edgeVal K σ k ∧ edgeVal K σ k ≤ 2 * τ⁻¹ * (1 + τ⁻¹) :=
  edgeVal_mem_Icc K σ h.nonneg hK (rd_posVals_nonempty h) h.pos h.phi_lower h.phi_upper
    h.bound_Sigma hk hkp

/-- A positive point of `supp ϱ` lies in a band `[a_{2k}, a_{2k−1}]`, `1 ≤ k ≤ p`. -/
private lemma rd_supp {τ : ℝ} {K : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ K σ)
    (hK : 0 < K) {y : ℝ} (hy : y ∈ (varrho K σ).support) (hy0 : 0 < y) :
    ∃ k, 1 ≤ k ∧ k ≤ numBands K σ ∧ edgeVal K σ (2 * k) ≤ y ∧ y ≤ edgeVal K σ (2 * k - 1) := by
  obtain ⟨k, hk1, hk2, hyk⟩ :=
    (mem_support_varrho_iff K σ h.nonneg hK (rd_posVals_nonempty h) hy0).1 hy
  exact ⟨k, hk1, hk2, hyk.1, hyk.2⟩

/-- A positive point of a band `[a_{2k}, a_{2k−1}]` lies in `supp ϱ`. -/
private lemma rd_mem_supp {τ : ℝ} {K : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ K σ)
    (hK : 0 < K) {k : ℕ} (hk : 1 ≤ k) (hkp : k ≤ numBands K σ) {y : ℝ} (hy0 : 0 < y)
    (hy1 : edgeVal K σ (2 * k) ≤ y) (hy2 : y ≤ edgeVal K σ (2 * k - 1)) :
    y ∈ (varrho K σ).support :=
  (mem_support_varrho_iff K σ h.nonneg hK (rd_posVals_nonempty h) hy0).2 ⟨k, hk, hkp, hy1, hy2⟩

/-- Off the support of `ϱ_N` at `N` (at distance `≥ τ/4`, above `τ/2`), the point is off the
support of `ϱ_{N−1}`: through `m_{N−1}(f_{N−1}(x)) = x = m_N(E)` with `f'_{N−1}(x) > 0`. -/
private lemma rd_off_pred (τ : ℝ) (hτ : 0 < τ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (σ : Fin M → ℝ), DensityAssumptions τ N σ →
      ∀ E : ℝ, τ / 2 ≤ E → τ / 4 ≤ Metric.infDist E (varrho N σ).support →
        E ∉ (varrho (N - 1) σ).support := by
  have hτi : 0 < τ⁻¹ := inv_pos.mpr hτ
  set Emax := 4 * τ⁻¹ * (1 + 2 * τ⁻¹) with hEmax
  have hEmax0 : 0 < Emax := by positivity
  set τ₁ := min (τ / 4) (Emax + 1)⁻¹ with hτ₁
  have hτ₁0 : 0 < τ₁ := lt_min (by positivity) (by positivity)
  set c := (genPropConst (τ₁ / 2))⁻¹ with hc
  have hc0 : 0 < c := by rw [hc, genPropConst]; positivity
  set d := τ / 8 with hd
  have hd0 : 0 < d := by positivity
  set B := Emax + 1 + c⁻¹ with hB
  have hB0 : 0 < B := by positivity
  refine ⟨⌈(d ^ 2 * c ^ 2)⁻¹ + 4 * B / d + 3⌉₊, ?_⟩
  intro N hN M σ h E hE hdist
  have hNc : (d ^ 2 * c ^ 2)⁻¹ + 4 * B / d + 3 ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hNr : (3 : ℝ) ≤ N := by
    have : 0 ≤ (d ^ 2 * c ^ 2)⁻¹ + 4 * B / d := by positivity
    linarith
  have hN2 : 2 ≤ N := by
    have : (2 : ℝ) < N := by linarith
    exact_mod_cast this.le
  have hK : 0 < N := by omega
  have hK1 : 0 < N - 1 := by omega
  have hσ := h.nonneg
  have h1 := rd_da_pred h hN2
  have hbd2 : 2 * (τ / 2)⁻¹ * (1 + (τ / 2)⁻¹) = Emax := by rw [hEmax]; field_simp; ring
  have hτ1 : τ ≤ 1 := by
    have h' : τ ≤ τ⁻¹ := h.phi_lower.trans h.phi_upper
    by_contra hc
    push Not at hc
    have : τ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hc
    linarith
  have hd1 : d ≤ 1 := by rw [hd]; linarith
  by_cases hbig : Emax < E
  · intro hs
    obtain ⟨k, hk1, hkp, -, hk2⟩ := rd_supp h1 hK1 hs (by linarith)
    have := (rd_edge_mem h1 hK1 (k := 2 * k - 1) (by omega) (by omega)).2
    rw [hbd2] at this
    linarith
  push Not at hbig
  have hdist' : ∀ E' ∈ Set.Icc (E - d) (E + d), ∀ u ∈ (varrho N σ).support, d ≤ |u - E'| := by
    intro E' hE' u hu
    have h1' := Metric.infDist_le_dist_of_mem hu (x := E)
    rw [Real.dist_eq] at h1'
    have : |E - u| ≤ |u - E'| + |E' - E| := by
      calc |E - u| = |(E' - u) + (E - E')| := by ring_nf
        _ ≤ |E' - u| + |E - E'| := abs_add_le _ _
        _ = |u - E'| + |E' - E| := by rw [abs_sub_comm E' u, abs_sub_comm E E']
    have : |E' - E| ≤ d := abs_le.2 ⟨by linarith [hE'.1], by linarith [hE'.2]⟩
    linarith
  set X : ℝ → ℝ := fun E' => (mExt N σ E').re with hX
  set T : ℝ → ℝ := fun E' => fR (N - 1) σ (X E') with hT
  have hfacts : ∀ E' ∈ Set.Icc (E - d) (E + d),
      0 < E' ∧ mExt N σ E' = (X E' : ℂ) ∧ X E' ≠ 0 ∧ (∀ i, 1 + σ i * X E' ≠ 0) ∧
        fR N σ (X E') = E' ∧ c ≤ |X E'| ∧ 0 < fR1 (N - 1) σ (X E') ∧
        |T E' - E'| ≤ d / 4 := by
    intro E' hE'
    have hE'0 : 0 < E' := by linarith [hE'.1]
    have him := rd_mExt_im_eq_zero N σ hσ hK hE'0.ne' hd0 (hdist' E' hE')
    obtain ⟨hwx, hx0, hpole, hf⟩ := rd_real_facts N σ hσ hK hE'0.ne' him
    have hge := rd_fR1_ge_dist N σ hσ hK hE'0.ne' hd0 (hdist' E' hE')
    have hlo : c ≤ |X E'| := by
      have hτ₁E : τ₁ ≤ E' := (min_le_left _ _).trans (by linarith [hE'.1])
      have hEτ₁ : E' ≤ τ₁⁻¹ := by
        have : E' ≤ Emax + 1 := by linarith [hE'.2]
        refine this.trans ?_
        rw [hτ₁]
        exact le_inv_of_le_inv₀ (by positivity) (min_le_right _ _)
      have := (rd_mExt_norm_bounds (h.mono hτ₁0 ((min_le_left _ _).trans (by linarith)))
        hτ₁E hEτ₁).1
      rw [hwx, Complex.norm_real, Real.norm_eq_abs] at this
      exact this
    have hx2 : (X E' ^ 2)⁻¹ ≤ (c ^ 2)⁻¹ := by
      refine inv_anti₀ (by positivity) ?_
      have := pow_le_pow_left₀ hc0.le hlo 2
      rwa [sq_abs] at this
    have hd' : 0 < fR1 (N - 1) σ (X E') := by
      have e := rd_fR1_pred σ hN2 (X E')
      have hN1 : (0 : ℝ) < N - 1 := by linarith
      have : (c ^ 2)⁻¹ < N * d ^ 2 := by
        have h3 : (d ^ 2 * c ^ 2)⁻¹ < N := by
          have : 0 ≤ 4 * B / d := by positivity
          linarith
        rw [inv_lt_iff_one_lt_mul₀ (by positivity)] at h3
        rw [inv_lt_iff_one_lt_mul₀ (by positivity)]
        nlinarith
      have : 0 < ((N : ℝ) - 1) * fR1 (N - 1) σ (X E') := by
        rw [e]; nlinarith
      exact pos_of_mul_pos_right this hN1.le
    have hTE : |T E' - E'| ≤ d / 4 := by
      have e := rd_fR_pred σ hN2 (X E')
      have hN1 : (0 : ℝ) < N - 1 := by linarith
      have e2 : T E' - E' = (E' + (X E')⁻¹) / (N - 1) := by
        simp only [hT]
        rw [eq_div_iff hN1.ne', sub_mul, mul_comm, e, hf]
        ring
      rw [e2, abs_div, abs_of_pos hN1, div_le_iff₀ hN1]
      have hinv : |(X E')⁻¹| ≤ c⁻¹ := by
        rw [abs_inv]; exact inv_anti₀ hc0 hlo
      have h5 : |E' + (X E')⁻¹| ≤ B := by
        calc |E' + (X E')⁻¹| ≤ |E'| + |(X E')⁻¹| := abs_add_le _ _
          _ ≤ (Emax + 1) + c⁻¹ := by
              rw [abs_of_pos hE'0]; linarith [hE'.2]
          _ = B := rfl
      have h6 : 4 * B / d ≤ N - 1 := by
        have : 0 ≤ (d ^ 2 * c ^ 2)⁻¹ := by positivity
        linarith
      rw [div_le_iff₀ hd0] at h6
      linarith
    exact ⟨hE'0, hwx, hx0, hpole, hf, hlo, hd', hTE⟩
  have hcont : ContinuousOn T (Set.Icc (E - d) (E + d)) := by
    have hXc : ContinuousOn X (Set.Icc (E - d) (E + d)) :=
      Complex.continuous_re.comp_continuousOn (rd_cont_mExt N σ hσ (by linarith))
    intro E' hE'
    obtain ⟨-, -, hx0, hpole, -⟩ := hfacts E' hE'
    exact (hasDerivAt_fR (N - 1) σ hx0 hpole).continuousAt.comp_continuousWithinAt (hXc E' hE')
  have hoff : ∀ t ∈ Set.Icc (T (E - d)) (T (E + d)), t ∉ (varrho (N - 1) σ).support := by
    intro t ht
    obtain ⟨E', hE', hTt⟩ := intermediate_value_Icc (show E - d ≤ E + d by linarith) hcont ht
    obtain ⟨-, -, hx0, hpole, -, -, hd', hTE⟩ := hfacts E' hE'
    have hT0 : 0 < T E' := by
      have := (abs_le.1 hTE).1
      linarith [hE'.1]
    rw [← hTt]
    exact rd_not_mem_support (N - 1) σ hσ hK1 hx0 hpole hd' hT0
  have hm := hfacts (E - d) ⟨le_rfl, by linarith⟩
  have hp := hfacts (E + d) ⟨by linarith, le_rfl⟩
  have hTm := (abs_le.1 hm.2.2.2.2.2.2.2).2
  have hTp := (abs_le.1 hp.2.2.2.2.2.2.2).1
  exact hoff E ⟨by linarith, by linarith⟩

/-! ## Counts, bands and high-probability events -/

/-- `n` is nonincreasing (`σ ≥ 0`). -/
private lemma rd_nClass_anti {K : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hK : 0 < K) {x y : ℝ}
    (hxy : x ≤ y) : nClass K σ y ≤ nClass K σ x := by
  have := isProbabilityMeasure_varrho K σ hσ hK
  exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono (Set.Ici_subset_Ici.mpr hxy))) (Nat.cast_nonneg K)

/-- `n ≤ K`. -/
private lemma rd_nClass_le {K : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hK : 0 < K) (E : ℝ) :
    nClass K σ E ≤ K := by
  have := isProbabilityMeasure_varrho K σ hσ hK
  unfold nClass
  have h1 : (varrho K σ (Set.Ici E)).toReal ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)
  have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (α := ℝ) K)
  linarith

/-- A positive classical location `γ_j` has `j ≤ K`. -/
private lemma rd_index_le {K : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hK : 0 < K) {j : ℕ}
    (hj : 0 < gammaLoc K σ j) : j ≤ K := by
  have h1 := nClass_gammaLoc_of_pos hσ hK hj
  have h2 := rd_nClass_le hσ hK (gammaLoc K σ j)
  have : (j : ℝ) < K + 1 := by linarith
  exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)

/-- `γ_{k,i} ∈ [a_{2k}, a_{2k−1}]` for `1 ≤ i ≤ N_k` when `γ_{k,i} > 0` (`σ ≥ 0`). -/
private lemma rd_band_mem {τ : ℝ} {K : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ K σ)
    (hK : 0 < K) {k i : ℕ} (hk : 1 ≤ k) (hkp : k ≤ numBands K σ) (hi : 1 ≤ i)
    (hiN : i ≤ bandNat K σ k) (hγ : 0 < gammaBand K σ k i) :
    edgeVal K σ (2 * k) ≤ gammaBand K σ k i ∧ gammaBand K σ k i ≤ edgeVal K σ (2 * k - 1) := by
  have hσ := h.nonneg
  have hanti : ∀ {x y : ℝ}, x ≤ y → nClass K σ y ≤ nClass K σ x := rd_nClass_anti hσ hK
  have hn := nClass_gammaLoc_of_pos hσ hK hγ
  obtain ⟨he1, he2⟩ := nClass_edgeVal h hk hkp
  obtain ⟨-, -, hc3⟩ := cumCount_spec h hk hkp
  have hg : gammaBand K σ k i = gammaLoc K σ (cumCount K σ (k - 1) + i) := rfl
  rw [hg] at hγ ⊢
  have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hjk : ((cumCount K σ (k - 1) + i : ℕ) : ℝ) ≤ cumCount K σ k := by
    exact_mod_cast (by omega : cumCount K σ (k - 1) + i ≤ cumCount K σ k)
  push_cast at hn hjk
  constructor
  · by_contra hlt
    rw [not_le] at hlt
    have := hanti hlt.le
    rw [hn, he2 (hγ.trans hlt)] at this
    linarith
  · by_contra hlt
    rw [not_le] at hlt
    have := hanti hlt.le
    rw [hn, he1] at this
    linarith

/-- Every band carries at least one classical location: `N_k ≥ 1`. -/
private lemma rd_bandNat_pos {τ : ℝ} {K : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ K σ)
    (hK : 0 < K) {k : ℕ} (hk : 1 ≤ k) (hkp : k ≤ numBands K σ) : 1 ≤ bandNat K σ k := by
  have hσ := h.nonneg
  have hS := rd_posVals_nonempty h
  have := isProbabilityMeasure_varrho K σ hσ hK
  have hlt := edgeVal_band_lt K σ hσ hK hS hk hkp
  have h0 := (rd_edge_mem h hK (k := 2 * k) (by omega) (by omega)).1
  set a := edgeVal K σ (2 * k)
  set b := edgeVal K σ (2 * k - 1)
  have hmid : (a + b) / 2 ∈ (varrho K σ).support :=
    rd_mem_supp h hK hk hkp (by linarith) (by linarith) (by linarith)
  have hpos : 0 < varrho K σ (Set.Ioo a b) :=
    (Measure.mem_support_iff_forall _).1 hmid _ (Ioo_mem_nhds (by linarith) (by linarith))
  have hpos' : 0 < varrho K σ (Set.Icc a b) :=
    lt_of_lt_of_le hpos (measure_mono Set.Ioo_subset_Icc_self)
  have hr : 0 < (varrho K σ (Set.Icc a b)).toReal :=
    ENNReal.toReal_pos hpos'.ne' (measure_ne_top _ _)
  have hbc : 0 < bandCount K σ k := by
    unfold bandCount
    have : (0 : ℝ) < K := by exact_mod_cast hK
    positivity
  have e := (cumCount_spec h hk hkp).2.1
  have : (0 : ℝ) < bandNat K σ k := by rw [e]; exact hbc
  exact_mod_cast this

/-- `k ≤ d_k` for `k ≤ p`. -/
private lemma rd_le_cum {τ : ℝ} {K : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ K σ)
    (hK : 0 < K) : ∀ k, k ≤ numBands K σ → k ≤ cumCount K σ k := by
  intro k
  induction k with
  | zero => intro _; exact Nat.zero_le _
  | succ k ih =>
    intro hk
    have h1 := rd_bandNat_pos h hK (k := k + 1) (by omega) hk
    have h2 := (cumCount_spec h (k := k + 1) (by omega) hk).2.2
    rw [Nat.add_sub_cancel] at h2
    have := ih (by omega)
    omega

/-- `d_k ≤ K ∧ #{σ_i > 0}` for `k ≤ p`. -/
private lemma rd_cum_le {τ : ℝ} {K : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ K σ)
    (hK : 0 < K) {k : ℕ} (hk : 1 ≤ k) (hkp : k ≤ numBands K σ) :
    (cumCount K σ k : ℝ) ≤ min (K : ℝ) (Finset.univ.filter fun i => 0 < σ i).card := by
  have hsum := sum_bandCount K σ h.nonneg hK (rd_posVals_nonempty h)
  have hle : ∑ l ∈ Finset.Icc 1 k, bandCount K σ l ≤
      ∑ l ∈ Finset.Icc 1 (numBands K σ), bandCount K σ l :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl hkp)
      (fun l _ _ => by unfold bandCount; positivity)
  rw [hsum, ← (cumCount_spec h hk hkp).1] at hle
  exact hle

/-- `p ≤ K`. -/
private lemma rd_numBands_le {τ : ℝ} {K : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ K σ)
    (hK : 0 < K) : numBands K σ ≤ K := by
  have hp := (card_innerCrit K σ h.nonneg hK (rd_posVals_nonempty h)).2
  have h1 := rd_le_cum h hK (numBands K σ) le_rfl
  have h2 := rd_cum_le h hK hp le_rfl
  have h3 : (cumCount K σ (numBands K σ) : ℝ) ≤ K := h2.trans (min_le_left _ _)
  have : cumCount K σ (numBands K σ) ≤ K := by exact_mod_cast h3
  omega

/-- For `1 ≤ i` with `γ_{l,i} > 0` (`K` samples), the index `j = d_{l−1} + i` satisfies
`1 ≤ j ≤ K`. -/
private lemma rd_dot_index {K : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hK : 0 < K) {l i : ℕ}
    (hi : 1 ≤ i) (hγ : 0 < gammaBand K σ l i) :
    1 ≤ cumCount K σ (l - 1) + i ∧ cumCount K σ (l - 1) + i ≤ K :=
  ⟨by omega, rd_index_le hσ hK hγ⟩

/-- `A ⊆ B` and `A` holds with high probability: so does `B`. -/
private lemma rd_hp_mono {Ω : Type*} [MeasureSpace Ω] {N : ℕ} {D : ℝ} {A B : Set Ω}
    (h : HighProbAt N D A) (hAB : A ⊆ B) : HighProbAt N D B :=
  (measure_mono (Set.compl_subset_compl.2 hAB)).trans h

/-- The bound of (rigidity) decreases when `min(i, N_k + 1 − i)` increases. -/
private lemma rd_rigBound_mono {N Nk Nk' i i' : ℕ} {ε : ℝ}
    (h1 : 1 ≤ min i (Nk + 1 - i)) (h : min i (Nk + 1 - i) ≤ min i' (Nk' + 1 - i')) :
    rigBound N Nk' i' ε ≤ rigBound N Nk i ε := by
  unfold rigBound
  have hp : (0 : ℝ) < ((min i (Nk + 1 - i) : ℕ) : ℝ) := by exact_mod_cast h1
  have hle : ((min i (Nk + 1 - i) : ℕ) : ℝ) ≤ ((min i' (Nk' + 1 - i') : ℕ) : ℝ) := by
    exact_mod_cast h
  have hr := Real.rpow_le_rpow_of_nonpos hp hle (show -(1 / 3 : ℝ) ≤ 0 by norm_num)
  have h0 : (0 : ℝ) ≤ (N : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have h0' : (0 : ℝ) ≤ (N : ℝ) ^ (-(2 / 3 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr h0) h0'

/-- `N^ε N⁻¹ ≤ N^ε (i ∧ (N_k + 1 − i))^{−1/3} N^{−2/3}` when `1 ≤ i ∧ (N_k + 1 − i) ≤ N`. -/
private lemma rd_bulk_le_rigBound {N Nk i : ℕ} {ε : ℝ} (h1 : 1 ≤ min i (Nk + 1 - i))
    (hN : min i (Nk + 1 - i) ≤ N) : (N : ℝ) ^ ε * (N : ℝ)⁻¹ ≤ rigBound N Nk i ε := by
  unfold rigBound
  have hp : (0 : ℝ) < ((min i (Nk + 1 - i) : ℕ) : ℝ) := by exact_mod_cast h1
  have hNr : (0 : ℝ) < N := hp.trans_le (by exact_mod_cast hN)
  have hle : ((min i (Nk + 1 - i) : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
  have hr := Real.rpow_le_rpow_of_nonpos hp hle (show -(1 / 3 : ℝ) ≤ 0 by norm_num)
  have hinv : (N : ℝ)⁻¹ = (N : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) := by
    rw [← Real.rpow_add hNr, ← Real.rpow_neg_one]
    norm_num
  rw [hinv, ← mul_assoc]
  have h0 : (0 : ℝ) ≤ (N : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have h0' : (0 : ℝ) ≤ (N : ℝ) ^ (-(2 / 3 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr h0) h0'

/-! ## The covering: every `γ̇ ≥ τ` lies near an edge or in the bulk of a band of `N` -/

/-- Every classical location `γ̇_{l,i} ≥ τ` of `N − 1` samples lies within `w` of an edge
`a_k ≥ τ/2` of `N`, or in `[a_{2m} + w, a_{2m−1} − w]` for a band `m` of `N` with
`a_{2m−1} ≥ τ/2`, given that the points above `2w` at distance `≥ w` from `supp ϱ_N` are off
`supp ϱ_{N−1}`. -/
private lemma rd_cover {τ w : ℝ} {K : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ K σ)
    (hK2 : 2 ≤ K) (hw0 : 0 < w) (hwτ : w ≤ τ / 4)
    (hoff : ∀ E : ℝ, 2 * w ≤ E → w ≤ Metric.infDist E (varrho K σ).support →
      E ∉ (varrho (K - 1) σ).support)
    {l i : ℕ} (hl1 : 1 ≤ l) (hlp : l ≤ numBands (K - 1) σ) (hi : 1 ≤ i)
    (hiN : i ≤ bandNat (K - 1) σ l) (hγ : τ ≤ gammaBand (K - 1) σ l i) :
    (∃ k, 1 ≤ k ∧ k ≤ 2 * numBands K σ ∧ τ / 2 ≤ edgeVal K σ k ∧
      gammaBand (K - 1) σ l i ∈ Set.Icc (edgeVal K σ k - w) (edgeVal K σ k + w)) ∨
    (∃ m, 1 ≤ m ∧ m ≤ numBands K σ ∧ τ / 2 ≤ edgeVal K σ (2 * m - 1) ∧
      gammaBand (K - 1) σ l i ∈
        Set.Icc (edgeVal K σ (2 * m) + w) (edgeVal K σ (2 * m - 1) - w)) := by
  have hτ := h.pos
  have hK : 0 < K := by omega
  have hK1 : 0 < K - 1 := by omega
  have h1 := rd_da_pred h hK2
  set x := gammaBand (K - 1) σ l i with hx
  have hx0 : 0 < x := by linarith
  obtain ⟨hxl, hxu⟩ := rd_band_mem h1 hK1 hl1 hlp hi hiN hx0
  have hxs : x ∈ (varrho (K - 1) σ).support := rd_mem_supp h1 hK1 hl1 hlp hx0 hxl hxu
  have hdist : Metric.infDist x (varrho K σ).support < w := by
    by_contra hc
    push Not at hc
    exact hoff x (by linarith) hc hxs
  obtain ⟨u, hu, hxu'⟩ := (Metric.infDist_lt_iff (rd_supp_nonempty h hK)).1 hdist
  rw [Real.dist_eq] at hxu'
  have hu' := abs_lt.1 hxu'
  have hu0 : 0 < u := by linarith [hu'.2]
  obtain ⟨m, hm1, hmp, hm2, hm3⟩ := rd_supp h hK hu hu0
  by_cases hA : |x - edgeVal K σ (2 * m - 1)| ≤ w
  · left
    have h' := abs_le.1 hA
    exact ⟨2 * m - 1, by omega, by omega, by linarith [h'.1], by constructor <;> linarith⟩
  by_cases hB : |x - edgeVal K σ (2 * m)| ≤ w
  · left
    have h' := abs_le.1 hB
    exact ⟨2 * m, by omega, by omega, by linarith [h'.2], by constructor <;> linarith⟩
  · right
    refine ⟨m, hm1, hmp, by linarith [hu'.1], ?_⟩
    rw [not_le] at hA hB
    constructor
    · rcases lt_abs.1 hB with h' | h'
      · linarith
      · linarith [hu'.1]
    · rcases lt_abs.1 hA with h' | h'
      · linarith [hu'.2]
      · linarith

/-- The assembly: the window-local events at the edges `a_k ≥ τ/2` and in the bulk of the bands
with `a_{2m−1} ≥ τ/2` give the event at every classical location `γ̇ ≥ τ`, with high
probability (at most `3N` events at `D + 2`). -/
private lemma rd_assemble {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {τ w ε D : ℝ} {N : ℕ} {σ : Fin M → ℝ}
    (hN3 : 3 ≤ N) (hp : numBands N σ ≤ N) (lam : Ω → ℕ → ℕ → ℝ)
    (hcov : ∀ l i, 1 ≤ l → l ≤ numBands (N - 1) σ → 1 ≤ i → i ≤ bandNat (N - 1) σ l →
      τ ≤ gammaBand (N - 1) σ l i →
      (∃ k, 1 ≤ k ∧ k ≤ 2 * numBands N σ ∧ τ / 2 ≤ edgeVal N σ k ∧
        gammaBand (N - 1) σ l i ∈ Set.Icc (edgeVal N σ k - w) (edgeVal N σ k + w)) ∨
      (∃ m, 1 ≤ m ∧ m ≤ numBands N σ ∧ τ / 2 ≤ edgeVal N σ (2 * m - 1) ∧
        gammaBand (N - 1) σ l i ∈
          Set.Icc (edgeVal N σ (2 * m) + w) (edgeVal N σ (2 * m - 1) - w)))
    (hidx : ∀ l i, 1 ≤ i → τ ≤ gammaBand (N - 1) σ l i → i ≤ N)
    (hE : ∀ k, 1 ≤ k → k ≤ 2 * numBands N σ → τ / 2 ≤ edgeVal N σ k →
      HighProbAt N (D + 2) {ω | ∀ l, 1 ≤ l → l ≤ numBands (N - 1) σ →
        ∀ i, 1 ≤ i → i ≤ bandNat (N - 1) σ l →
        gammaBand (N - 1) σ l i ∈ Set.Icc (edgeVal N σ k - w) (edgeVal N σ k + w) →
        |lam ω l i - gammaBand (N - 1) σ l i| ≤ rigBound N (bandNat (N - 1) σ l) i ε})
    (hB : ∀ m, 1 ≤ m → m ≤ numBands N σ → τ / 2 ≤ edgeVal N σ (2 * m - 1) →
      HighProbAt N (D + 2) {ω | ∀ l, 1 ≤ l → l ≤ numBands (N - 1) σ →
        ∀ i, 1 ≤ i → i ≤ bandNat (N - 1) σ l →
        gammaBand (N - 1) σ l i ∈
          Set.Icc (edgeVal N σ (2 * m) + w) (edgeVal N σ (2 * m - 1) - w) →
        |lam ω l i - gammaBand (N - 1) σ l i| ≤ (N : ℝ) ^ ε * (N : ℝ)⁻¹}) :
    HighProbAt N D {ω | ∀ l, 1 ≤ l → l ≤ numBands (N - 1) σ →
      ∀ i, 1 ≤ i → i ≤ bandNat (N - 1) σ l → τ ≤ gammaBand (N - 1) σ l i →
        |lam ω l i - gammaBand (N - 1) σ l i| ≤ rigBound N (bandNat (N - 1) σ l) i ε} := by
  set p := numBands N σ with hpdef
  set Sb : Finset ℕ := (Finset.Icc 1 p).filter (fun m => τ / 2 ≤ edgeVal N σ (2 * m - 1))
    with hSb
  set Se : Finset ℕ := (Finset.Icc 1 (2 * p)).filter (fun k => τ / 2 ≤ edgeVal N σ k) with hSe
  have hcard : ((Sb.disjSum Se).card : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) := by
    rw [Finset.card_disjSum, Real.rpow_two]
    have h1 : Sb.card ≤ p := by
      have := Finset.card_filter_le (Finset.Icc 1 p) (fun m => τ / 2 ≤ edgeVal N σ (2 * m - 1))
      simpa using this
    have h2 : Se.card ≤ 2 * p := by
      have := Finset.card_filter_le (Finset.Icc 1 (2 * p)) (fun k => τ / 2 ≤ edgeVal N σ k)
      simpa using this
    have h : Sb.card + Se.card ≤ N ^ 2 := by nlinarith
    exact_mod_cast h
  set Eb : ℕ → Set Ω := fun m => {ω | ∀ l, 1 ≤ l → l ≤ numBands (N - 1) σ →
    ∀ i, 1 ≤ i → i ≤ bandNat (N - 1) σ l →
    gammaBand (N - 1) σ l i ∈ Set.Icc (edgeVal N σ (2 * m) + w) (edgeVal N σ (2 * m - 1) - w) →
    |lam ω l i - gammaBand (N - 1) σ l i| ≤ (N : ℝ) ^ ε * (N : ℝ)⁻¹} with hEb
  set Ee : ℕ → Set Ω := fun k => {ω | ∀ l, 1 ≤ l → l ≤ numBands (N - 1) σ →
    ∀ i, 1 ≤ i → i ≤ bandNat (N - 1) σ l →
    gammaBand (N - 1) σ l i ∈ Set.Icc (edgeVal N σ k - w) (edgeVal N σ k + w) →
    |lam ω l i - gammaBand (N - 1) σ l i| ≤ rigBound N (bandNat (N - 1) σ l) i ε} with hEe
  have hev : ∀ x ∈ Sb.disjSum Se, HighProbAt N (D + 2) (Sum.elim Eb Ee x) := by
    rintro (m | k) hx
    · have hm := Finset.inl_mem_disjSum.1 hx
      simp only [hSb, Finset.mem_filter, Finset.mem_Icc] at hm
      exact hB m hm.1.1 hm.1.2 hm.2
    · have hk := Finset.inr_mem_disjSum.1 hx
      simp only [hSe, Finset.mem_filter, Finset.mem_Icc] at hk
      exact hE k hk.1.1 hk.1.2 hk.2
  have hI := HighProbAt.biInter (Sb.disjSum Se) (by omega) hcard hev
  unfold HighProbAt at hI ⊢
  refine le_trans (measure_mono (Set.compl_subset_compl.2 ?_)) hI
  intro ω hω
  simp only [Set.mem_ofPred_eq]
  intro l hl1 hlp i hi1 hiN hγ
  rcases hcov l i hl1 hlp hi1 hiN hγ with ⟨k, hk1, hk2, hka, hwin⟩ | ⟨m, hm1, hm2, hma, hwin⟩
  · have hkS : k ∈ Se := by
      simp only [hSe, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hk1, hk2⟩, hka⟩
    have hE' : ω ∈ Ee k := Set.mem_iInter₂.1 hω (Sum.inr k) (Finset.inr_mem_disjSum.2 hkS)
    exact hE' l hl1 hlp i hi1 hiN hwin
  · have hmS : m ∈ Sb := by
      simp only [hSb, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hm1, hm2⟩, hma⟩
    have hB' : ω ∈ Eb m := Set.mem_iInter₂.1 hω (Sum.inl m) (Finset.inl_mem_disjSum.2 hmS)
    have hiN' := hidx l i hi1 hγ
    exact (hB' l hl1 hlp i hi1 hiN hwin).trans
      (rd_bulk_le_rigBound (le_min hi1 (by omega)) ((min_le_left _ _).trans hiN'))

/-! ## The classical count `n` at one `N` -/

/-- (phi_bounded) and (Sigma_gap) give `N > 0`, `M > 0` and some positive `σ i`. -/
private lemma rd_facts {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) :
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

/-- `ϱ(A) = ∫_A ρ` for measurable `A ⊆ (0, ∞)`. -/
private lemma rd_varrho_apply (σ : Fin M → ℝ) {A : Set ℝ} (hA : MeasurableSet A)
    (hsub : A ⊆ Set.Ioi 0) :
    varrho N σ A = ∫⁻ x in A, ENNReal.ofReal (rhoDens N σ x) := by
  have h0 : (0 : ℝ) ∉ A := fun h => lt_irrefl (0 : ℝ) (Set.mem_Ioi.mp (hsub h))
  rw [varrho, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hA,
    Set.indicator_of_notMem h0, smul_zero, zero_add, withDensity_apply _ hA,
    Measure.restrict_restrict hA, Set.inter_eq_left.mpr hsub]

/-- `n(x) − n(y) = N ϱ([x, y))` for `x ≤ y`. -/
private lemma rd_nClass_sub {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {x y : ℝ}
    (hxy : x ≤ y) :
    nClass N σ x - nClass N σ y = N * (varrho N σ (Set.Ico x y)).toReal := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  have hsplit : varrho N σ (Set.Ici x) =
      varrho N σ (Set.Ico x y) + varrho N σ (Set.Ici y) := by
    rw [← measure_union _ measurableSet_Ici, Set.Ico_union_Ici_eq_Ici hxy]
    rw [Set.disjoint_left]
    intro z hz1 hz2
    exact absurd hz1.2 (not_lt.mpr hz2)
  unfold nClass
  rw [hsplit, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  ring

/-- If `ρ ≥ c₀` on `[x, y)` with `0 < x ≤ y`, then `n(x) − n(y) ≥ N c₀ (y − x)`. -/
private lemma rd_nClass_sub_ge {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {x y c₀ : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (hc₀ : 0 ≤ c₀)
    (hρ : ∀ u ∈ Set.Ico x y, c₀ ≤ rhoDens N σ u) :
    N * c₀ * (y - x) ≤ nClass N σ x - nClass N σ y := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  rw [rd_nClass_sub hσ hN hxy]
  have hsub : Set.Ico x y ⊆ Set.Ioi 0 := fun u hu => lt_of_lt_of_le hx hu.1
  have hge : ENNReal.ofReal (c₀ * (y - x)) ≤ varrho N σ (Set.Ico x y) := by
    rw [rd_varrho_apply σ measurableSet_Ico hsub]
    calc ENNReal.ofReal (c₀ * (y - x))
        = ∫⁻ u in Set.Ico x y, ENNReal.ofReal c₀ := by
          rw [setLIntegral_const, Real.volume_Ico, ENNReal.ofReal_mul hc₀]
      _ ≤ ∫⁻ u in Set.Ico x y, ENNReal.ofReal (rhoDens N σ u) :=
          setLIntegral_mono' measurableSet_Ico fun u hu =>
            ENNReal.ofReal_le_ofReal (hρ u hu)
  have h1 : c₀ * (y - x) ≤ (varrho N σ (Set.Ico x y)).toReal := by
    have := ENNReal.toReal_mono (measure_ne_top _ _) hge
    rwa [ENNReal.toReal_ofReal (mul_nonneg hc₀ (by linarith))] at this
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  calc (N : ℝ) * c₀ * (y - x) = N * (c₀ * (y - x)) := by ring
    _ ≤ N * (varrho N σ (Set.Ico x y)).toReal := mul_le_mul_of_nonneg_left h1 hN0

/-- If `ρ ≤ c₀` on `[x, y)` with `0 < x ≤ y`, then `n(x) − n(y) ≤ N c₀ (y − x)`. -/
private lemma rd_nClass_sub_le {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {x y c₀ : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (hc₀ : 0 ≤ c₀)
    (hρ : ∀ u ∈ Set.Ico x y, rhoDens N σ u ≤ c₀) :
    nClass N σ x - nClass N σ y ≤ N * c₀ * (y - x) := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  rw [rd_nClass_sub hσ hN hxy]
  have hsub : Set.Ico x y ⊆ Set.Ioi 0 := fun u hu => lt_of_lt_of_le hx hu.1
  have hle : varrho N σ (Set.Ico x y) ≤ ENNReal.ofReal (c₀ * (y - x)) := by
    rw [rd_varrho_apply σ measurableSet_Ico hsub]
    calc ∫⁻ u in Set.Ico x y, ENNReal.ofReal (rhoDens N σ u)
        ≤ ∫⁻ u in Set.Ico x y, ENNReal.ofReal c₀ :=
          setLIntegral_mono' measurableSet_Ico fun u hu =>
            ENNReal.ofReal_le_ofReal (hρ u hu)
      _ = ENNReal.ofReal (c₀ * (y - x)) := by
          rw [setLIntegral_const, Real.volume_Ico, ENNReal.ofReal_mul hc₀]
  have h1 : (varrho N σ (Set.Ico x y)).toReal ≤ c₀ * (y - x) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    rwa [ENNReal.toReal_ofReal (mul_nonneg hc₀ (by linarith))] at this
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  calc (N : ℝ) * (varrho N σ (Set.Ico x y)).toReal ≤ N * (c₀ * (y - x)) :=
        mul_le_mul_of_nonneg_left h1 hN0
    _ = N * c₀ * (y - x) := by ring

/-- `n(x) ≤ d_k` for `a_{2k} < x`, `1 ≤ k ≤ p`. -/
private lemma rd_n_le_cum {τ : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ) {k : ℕ}
    (hk : 1 ≤ k) (hkp : k ≤ numBands N σ) {x : ℝ} (hx : edgeVal N σ (2 * k) < x) :
    nClass N σ x ≤ cumCount N σ k := by
  obtain ⟨hN, -, hS⟩ := rd_facts hda
  have hσ := hda.nonneg
  obtain ⟨-, hbn, hcs⟩ := cumCount_spec hda hk hkp
  have hna := (nClass_edgeVal hda hk hkp).1
  have hcr : (cumCount N σ k : ℝ) = cumCount N σ (k - 1) + bandCount N σ k := by
    rw [← hcs]; push_cast; rw [hbn]
  rcases le_or_gt (edgeVal N σ (2 * k - 1)) x with h1 | h1
  · have := rd_nClass_anti hσ hN h1
    have h0 : 0 ≤ bandCount N σ k := by unfold bandCount; positivity
    linarith
  · have := isProbabilityMeasure_varrho N σ hσ hN
    have hs := rd_nClass_sub hσ hN h1.le
    have hmono : (varrho N σ (Set.Ico x (edgeVal N σ (2 * k - 1)))).toReal ≤
        (varrho N σ (Set.Icc (edgeVal N σ (2 * k)) (edgeVal N σ (2 * k - 1)))).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _)
        (measure_mono fun t ht => ⟨le_trans hx.le ht.1, ht.2.le⟩)
    have hb : bandCount N σ k =
        N * (varrho N σ (Set.Icc (edgeVal N σ (2 * k)) (edgeVal N σ (2 * k - 1)))).toReal := rfl
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have := mul_le_mul_of_nonneg_left hmono hN0
    linarith

/-- (def:gamma_alpha): `n(x) ≥ j − 1/2` at `x > 0` gives `x ≤ γ_j`. -/
private lemma rd_le_gamma {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) {j : ℕ}
    (hj : 1 ≤ j) {x : ℝ} (hx : 0 < x) (hn : (j : ℝ) - 1 / 2 ≤ nClass N σ x) :
    x ≤ gammaLoc N σ j := by
  obtain ⟨hN, -, hS⟩ := rd_facts h
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hbdd : BddAbove {E | 0 < E ∧ (j : ℝ) - 1 / 2 ≤ nClass N σ E} := by
    refine ⟨edgeVal N σ 1, fun E hE => ?_⟩
    by_contra hlt
    push Not at hlt
    have hsub : Set.Ici E ⊆ (Set.Icc 0 (edgeVal N σ 1))ᶜ := fun t ht hmem =>
      absurd (le_trans (Set.mem_Ici.mp ht) hmem.2) (not_le.mpr hlt)
    have h0 : varrho N σ (Set.Ici E) = 0 :=
      measure_mono_null hsub (varrho_compl_Icc_edgeVal N σ h.nonneg hN hS)
    have : nClass N σ E = 0 := by simp [nClass, h0]
    linarith [hE.2]
  exact le_csSup hbdd ⟨hx, hn⟩

/-- The eigenvalues `σ` of `Σ` are positive under Assumption 2.1. -/
private lemma rd_sigma_pos {Ω : Type*} [MeasureSpace Ω] {τ : ℝ} {C : ℕ → ℝ}
    {Sig : Matrix (Fin M) (Fin M) ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ}
    (hm : IsModel τ C M N Sig X) : ∀ i, 0 < specOf Sig i := fun i => by
  rw [specOf_eq hm.sigma.posDef.isHermitian]
  exact hm.sigma.posDef.eigenvalues_pos i

/-- `C N^a ≤ N^b` for `a < b` and `N` large. -/
private lemma rd_ev (C : ℝ) {a b : ℝ} (hab : a < b) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → C * (N : ℝ) ^ a ≤ (N : ℝ) ^ b := by
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) ^ (b - a)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1
    ((h1.eventually_ge_atTop C).and (Filter.eventually_ge_atTop 1))
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨h2, h3⟩ := hN₀ N hN
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc C * (N : ℝ) ^ a ≤ (N : ℝ) ^ (b - a) * (N : ℝ) ^ a :=
        mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hN.le _)
    _ = (N : ℝ) ^ b := by rw [← Real.rpow_add hN]; ring_nf



/-! ## Scaling and interlacing of sorted eigenvalues -/

section SpecSub

variable {K : ℕ} {A : Matrix (Fin K) (Fin K) ℝ}

/-- The orthogonal matrix whose columns are the eigenvectors of `A`. -/
private def rdU (hA : A.IsHermitian) : Matrix (Fin K) (Fin K) ℝ :=
  (hA.eigenvectorUnitary : Matrix (Fin K) (Fin K) ℝ)

/-- The coordinates of `w` in the eigenbasis of `A`. -/
private def rdC (hA : A.IsHermitian) (w : Fin K → ℝ) : Fin K → ℝ :=
  star (rdU hA) *ᵥ w

private lemma rdU_star_mul (hA : A.IsHermitian) : star (rdU hA) * rdU hA = 1 :=
  Unitary.coe_star_mul_self _

private lemma rdU_mul_star (hA : A.IsHermitian) : rdU hA * star (rdU hA) = 1 :=
  Unitary.coe_mul_star_self _

private lemma rdU_mulVec_rdC (hA : A.IsHermitian) (w : Fin K → ℝ) : rdU hA *ᵥ rdC hA w = w := by
  unfold rdC
  rw [mulVec_mulVec, rdU_mul_star, one_mulVec]

private lemma rdU_orth_dot (hA : A.IsHermitian) (x y : Fin K → ℝ) :
    (rdU hA *ᵥ x) ⬝ᵥ (rdU hA *ᵥ y) = x ⬝ᵥ y := by
  rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, mulVec_mulVec]
  have : (rdU hA)ᵀ * rdU hA = 1 := by
    have h := rdU_star_mul hA
    rwa [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h
  rw [this, one_mulVec]

private lemma rdU_decomp (hA : A.IsHermitian) :
    A = rdU hA * diagonal hA.eigenvalues * star (rdU hA) := by
  have := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at this
  simpa [rdU] using this

private lemma rd_dot_eq_sum (hA : A.IsHermitian) (w : Fin K → ℝ) :
    w ⬝ᵥ w = ∑ j, (rdC hA w j) ^ 2 := by
  conv_lhs => rw [← rdU_mulVec_rdC hA w]
  rw [rdU_orth_dot]
  simp [dotProduct, sq]

private lemma rd_quad_eq_sum (hA : A.IsHermitian) (w : Fin K → ℝ) :
    w ⬝ᵥ (A *ᵥ w) = ∑ j, hA.eigenvalues j * (rdC hA w j) ^ 2 := by
  have h1 : A *ᵥ w = rdU hA *ᵥ (diagonal hA.eigenvalues *ᵥ rdC hA w) := by
    conv_lhs => rw [rdU_decomp hA]
    unfold rdC
    rw [← mulVec_mulVec, ← mulVec_mulVec]
  rw [h1]
  nth_rewrite 1 [← rdU_mulVec_rdC hA w]
  rw [rdU_orth_dot]
  simp only [dotProduct, mulVec_diagonal, sq]
  refine Finset.sum_congr rfl fun j _ => by ring

/-- The linear map recording the eigencoordinates of `w` indexed by `s`. -/
private def rdMap (hA : A.IsHermitian) (s : Finset (Fin K)) : (Fin K → ℝ) →ₗ[ℝ] (s → ℝ) :=
  (LinearMap.funLeft ℝ ℝ (Subtype.val : s → Fin K)) ∘ₗ Matrix.mulVecLin (star (rdU hA))

private lemma rd_mem_ker_rdMap (hA : A.IsHermitian) (s : Finset (Fin K)) (w : Fin K → ℝ) :
    w ∈ LinearMap.ker (rdMap hA s) ↔ ∀ j ∈ s, rdC hA w j = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h j hj
    exact congrFun h ⟨j, hj⟩
  · intro h
    funext j
    exact h j.1 j.2

private lemma rd_le_finrank_ker (hA : A.IsHermitian) (s : Finset (Fin K)) :
    K ≤ Module.finrank ℝ (LinearMap.ker (rdMap hA s)) + s.card := by
  have h := LinearMap.finrank_range_add_finrank_ker (rdMap hA s)
  have h1 : Module.finrank ℝ (LinearMap.range (rdMap hA s)) ≤ s.card := by
    calc Module.finrank ℝ (LinearMap.range (rdMap hA s)) ≤ Module.finrank ℝ (s → ℝ) :=
          Submodule.finrank_le _
      _ = s.card := by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  have h2 : Module.finrank ℝ (Fin K → ℝ) = K := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  omega

private lemma rd_eigCount_add_card (hA : A.IsHermitian) (E : ℝ) :
    eigCount A E + (Finset.univ.filter fun j => ¬ E ≤ hA.eigenvalues j).card = K := by
  have : eigCount A E = (Finset.univ.filter fun j => E ≤ hA.eigenvalues j).card := by
    unfold eigCount
    rw [specOf_eq hA]
  rw [this, Finset.card_filter_add_card_filter_not]
  simp

/-- A spectral subspace: dimension at least `n_A(E)`, and `⟨w, A w⟩ ≥ E |w|²` on it. -/
private lemma rd_spectral_subspace (hA : A.IsHermitian) (E : ℝ) :
    ∃ W : Submodule ℝ (Fin K → ℝ), eigCount A E ≤ Module.finrank ℝ W ∧
      ∀ w ∈ W, E * (w ⬝ᵥ w) ≤ w ⬝ᵥ (A *ᵥ w) := by
  set s := Finset.univ.filter fun j => ¬ E ≤ hA.eigenvalues j with hs
  have hz : ∀ w ∈ LinearMap.ker (rdMap hA s), ∀ j, hA.eigenvalues j < E → rdC hA w j = 0 := by
    intro w hw j hj
    exact (rd_mem_ker_rdMap hA s w).mp hw j (by simpa [hs] using hj)
  refine ⟨LinearMap.ker (rdMap hA s), ?_, ?_⟩
  · have h1 := rd_le_finrank_ker hA s
    have h2 : eigCount A E + s.card = K := rd_eigCount_add_card hA E
    omega
  · intro w hw
    rw [rd_quad_eq_sum hA, rd_dot_eq_sum hA, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hj : hA.eigenvalues j < E
    · rw [hz w hw j hj]; simp
    · exact mul_le_mul_of_nonneg_right (not_lt.mp hj) (sq_nonneg _)

/-- `n_A(E) ≤ n_{cA}(cE)` for `c > 0`. -/
private lemma rd_eigCount_le_smul (hA : A.IsHermitian) {c : ℝ} (hc : 0 < c) (E : ℝ) :
    eigCount A E ≤ eigCount (c • A) (c * E) := by
  obtain ⟨W, hW1, hW2⟩ := rd_spectral_subspace hA E
  have hcA : (c • A).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_smul, hA.eq, star_trivial]
  refine hW1.trans (eigCount_ge_of_subspace hcA W fun w hw => ?_)
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hW2 w hw) hc.le

/-- `n_{cA}(cE) = n_A(E)` for `c > 0`. -/
private lemma rd_eigCount_smul (hA : A.IsHermitian) {c : ℝ} (hc : 0 < c) (E : ℝ) :
    eigCount (c • A) (c * E) = eigCount A E := by
  have hcA : (c • A).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_smul, hA.eq, star_trivial]
  refine le_antisymm ?_ (rd_eigCount_le_smul hA hc E)
  have := rd_eigCount_le_smul hcA (inv_pos.mpr hc) (c * E)
  rwa [smul_smul, inv_mul_cancel₀ hc.ne', one_smul, ← mul_assoc, inv_mul_cancel₀ hc.ne',
    one_mul] at this

/-- `λ_j(cA) = c λ_j(A)` for `c > 0`, `1 ≤ j ≤ K`. -/
private lemma rd_sortedEig_smul (hA : A.IsHermitian) {c : ℝ} (hc : 0 < c) {j : ℕ} (hj : 1 ≤ j)
    (hjK : j ≤ K) : sortedEig (c • A) j = c * sortedEig A j := by
  have hcA : (c • A).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_smul, hA.eq, star_trivial]
  have key : ∀ x, x ≤ sortedEig (c • A) j ↔ x ≤ c * sortedEig A j := by
    intro x
    rw [sortedEig_ge_iff hcA hj hjK, show x = c * (x / c) by field_simp, rd_eigCount_smul hA hc,
      ← sortedEig_ge_iff hA hj hjK, mul_le_mul_iff_of_pos_left hc]
  exact le_antisymm ((key _).1 le_rfl) ((key _).2 le_rfl)

end SpecSub

/-- Cauchy interlacing for `π̄ B π̄`: `λ_{j+1}(B) ≤ λ_j(π̄ B π̄)`. -/
private lemma rd_interlace_lo {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.IsHermitian)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {j : ℕ} (hj : 1 ≤ j) (hjN : j + 1 ≤ N) :
    sortedEig (QN Sig Xm) (j + 1) ≤ sortedEig (QN Sig (Xdot Xm)) j := by
  have hB : (QN Sig Xm).IsHermitian := XSX_isHermitian hSig Xm
  have hB' : (QN Sig (Xdot Xm)).IsHermitian := XSX_isHermitian hSig (Xdot Xm)
  set x := sortedEig (QN Sig Xm) (j + 1)
  have h1 := (sortedEig_ge_iff hB (by omega) hjN x).1 le_rfl
  have h2 := eigCount_le_compress_add_one hSig Xm x
  exact (sortedEig_ge_iff hB' hj (by omega) x).2 (by omega)

/-- Cauchy interlacing for `π̄ B π̄`: `λ_j(π̄ B π̄) ≤ λ_j(B)` when `λ_j(π̄ B π̄) > 0`. -/
private lemma rd_interlace_hi {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.IsHermitian)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {j : ℕ} (hj : 1 ≤ j) (hjN : j ≤ N)
    (hpos : 0 < sortedEig (QN Sig (Xdot Xm)) j) :
    sortedEig (QN Sig (Xdot Xm)) j ≤ sortedEig (QN Sig Xm) j := by
  have hB : (QN Sig Xm).IsHermitian := XSX_isHermitian hSig Xm
  have hB' : (QN Sig (Xdot Xm)).IsHermitian := XSX_isHermitian hSig (Xdot Xm)
  set x := sortedEig (QN Sig (Xdot Xm)) j
  have h1 := (sortedEig_ge_iff hB' hj hjN x).1 le_rfl
  have h2 := eigCount_compress_le hSig Xm hpos
  exact (sortedEig_ge_iff hB hj hjN x).2 (h1.trans h2)

/-- If `0 < L ≤ λ_j(π̄ B π̄)` and `λ_j(B) ≤ U`, then
`L ≤ (N/(N−1)) λ_j(π̄ B π̄) ≤ U + U/(N − 1)`. -/
private lemma rd_dot_bounds {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.IsHermitian)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (hN : 2 ≤ N) {j : ℕ} (hj : 1 ≤ j) (hjN : j ≤ N) {L U : ℝ}
    (hL : 0 < L) (hLj : L ≤ sortedEig (QN Sig (Xdot Xm)) j) (hU : sortedEig (QN Sig Xm) j ≤ U) :
    L ≤ (N : ℝ) / (N - 1) * sortedEig (QN Sig (Xdot Xm)) j ∧
      (N : ℝ) / (N - 1) * sortedEig (QN Sig (Xdot Xm)) j ≤ U + U / (N - 1) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : 0 < sortedEig (QN Sig (Xdot Xm)) j := lt_of_lt_of_le hL hLj
  have hle := rd_interlace_hi hSig Xm hj hjN hpos
  set x := sortedEig (QN Sig (Xdot Xm)) j
  have hN1 : (0 : ℝ) < N - 1 := by linarith
  have e : (N : ℝ) / (N - 1) = 1 + 1 / (N - 1) := by field_simp; ring
  have hU0 : 0 ≤ U := by linarith
  rw [e]
  constructor
  · have : 0 ≤ 1 / ((N : ℝ) - 1) * x := by positivity
    nlinarith
  · have h1 : 1 / ((N : ℝ) - 1) * x ≤ 1 / ((N : ℝ) - 1) * U :=
      mul_le_mul_of_nonneg_left (hle.trans hU) (by positivity)
    have e2 : U / ((N : ℝ) - 1) = 1 / ((N : ℝ) - 1) * U := by ring
    nlinarith

/-! ## The factor `N/(N − 1)` -/

/-- `U/(N − 1) ≤ 2U/N` for `U ≥ 0`, `N ≥ 2`. -/
private lemma rd_div_pred {U : ℝ} (hU : 0 ≤ U) (hN : 2 ≤ N) :
    U / ((N : ℝ) - 1) ≤ 2 * U * (N : ℝ)⁻¹ := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  rw [div_le_iff₀ (by linarith)]
  have e : 2 * U * (N : ℝ)⁻¹ * ((N : ℝ) - 1) = U * (2 - 2 / N) := by
    field_simp
  rw [e]
  have : 2 / (N : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  nlinarith


/-- `τ'(τ) ≤ τ/2` for `τ ∈ (0, 1]`. -/
private lemma rd_edgeTau'_le {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) : edgeTau' τ ≤ τ / 2 := by
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


/-! ## The regularisation `Ŝ + κ P₀` (§11.1) -/

/-- `τ ≤ 1` under Assumption 2.1 for a general `T`. -/
private lemma rd_tau_le_one {Ω : Type*} [MeasureSpace Ω] {τ : ℝ} {C : ℕ → ℝ} {K : ℕ}
    {T : Matrix (Fin M) (Fin K) ℝ} {X : Ω → Matrix (Fin K) (Fin N) ℝ}
    (hm : IsModelT τ C M K N T X) : τ ≤ 1 := by
  have h1 := hm.ratio_ge
  have h2 := hm.ratio_le
  by_contra hc
  push Not at hc
  have : τ⁻¹ < τ := lt_trans (inv_lt_one_of_one_lt₀ hc) hc
  linarith


/-- `0 < τ'_gen(τ) ≤ τ/32` for `0 < τ ≤ 1`. -/
private lemma rd_tauGen {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    0 < tauGen τ ∧ tauGen τ ≤ τ / 32 := by
  have he := tauE_pos hτ
  have he4 : tauE τ ≤ τ / 4 := min_le_right _ _
  have h := rd_edgeTau'_le he (by linarith)
  refine ⟨by unfold tauGen; have := edgeTau'_pos he; positivity, ?_⟩
  unfold tauGen
  linarith

/-- Weyl's inequality for the sorted eigenvalues, one side: `λ_j(A) ≤ λ_j(B) + ‖A − B‖`. -/
private lemma rd_sortedEig_le {K : ℕ} {A B : Matrix (Fin K) (Fin K) ℝ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (j : ℕ) : sortedEig A j ≤ sortedEig B j + ‖A - B‖ := by
  by_cases hj : 1 ≤ j ∧ j ≤ K
  · have h1 : sortedEig A j - ‖A - B‖ ≤ sortedEig B j := by
      rw [sortedEig_ge_iff hB hj.1 hj.2]
      have hw := eigCount_weyl hA hB le_rfl (sortedEig A j - ‖A - B‖)
      rw [sub_add_cancel] at hw
      exact le_trans ((sortedEig_ge_iff hA hj.1 hj.2 _).1 le_rfl) hw
    linarith
  · have hA0 : sortedEig A j = 0 := by
      unfold sortedEig
      split_ifs with h'
      · exact absurd ⟨h'.2.1, by simpa using h'.2.2⟩ hj
      · rfl
    have hB0 : sortedEig B j = 0 := by
      unfold sortedEig
      split_ifs with h'
      · exact absurd ⟨h'.2.1, by simpa using h'.2.2⟩ hj
      · rfl
    rw [hA0, hB0]
    simp

/-- Weyl's inequality for the sorted eigenvalues: `|λ_j(A) − λ_j(B)| ≤ ‖A − B‖`. -/
private lemma rd_abs_sortedEig_sub {K : ℕ} {A B : Matrix (Fin K) (Fin K) ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (j : ℕ) :
    |sortedEig A j - sortedEig B j| ≤ ‖A - B‖ := by
  rw [abs_le]
  have h1 := rd_sortedEig_le hA hB j
  have h2 := rd_sortedEig_le hB hA j
  rw [norm_sub_rev] at h2
  constructor <;> linarith

/-- The projection `P₀` on `ker S`, by spectral calculus. -/
private def rdP0 {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  cfc (fun x : ℝ => if 0 < x then (0 : ℝ) else 1) S

/-- `Ŝ + κ P₀ = Ŝ + κ • P₀` for `Ŝ = Tᵀ T`. -/
private lemma rd_regS_eq {K : ℕ} (κ : ℝ) (T : Matrix (Fin M) (Fin K) ℝ) :
    regS κ (Tᵀ * T) = Tᵀ * T + κ • rdP0 (Tᵀ * T) := by
  have hS : (Tᵀ * T).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self T
  have hcont : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ (Tᵀ * T)) := fun f => by
    rw [hS.1.spectrum_real_eq_range_eigenvalues]
    exact (Set.finite_range _).continuousOn f
  unfold regS rdP0
  have h1 : cfc (fun x : ℝ => if 0 < x then x else κ) (Tᵀ * T) =
      cfc (fun x : ℝ => (if 0 < x then x else 0) + κ * (if 0 < x then (0 : ℝ) else 1))
        (Tᵀ * T) :=
    cfc_congr fun x _ => by split_ifs <;> ring
  have hid : cfc (id : ℝ → ℝ) (Tᵀ * T) = Tᵀ * T := cfc_id ℝ (Tᵀ * T) hS.1
  rw [h1, cfc_add (a := Tᵀ * T) (fun x : ℝ => if 0 < x then x else 0)
      (fun x : ℝ => κ * (if 0 < x then (0 : ℝ) else 1)) (hcont _) (hcont _),
    cfc_const_mul κ (fun x : ℝ => if 0 < x then (0 : ℝ) else 1) (Tᵀ * T) (hcont _)]
  congr 1
  rw [cfc_congr (g := id) fun x hx => ?_]
  · exact hid
  · have : 0 ≤ x := by
      rw [hS.1.spectrum_real_eq_range_eigenvalues] at hx
      obtain ⟨i, rfl⟩ := hx
      exact hS.eigenvalues_nonneg i
    split_ifs with h
    · rfl
    · simp only [id]
      linarith

/-- `‖Q_N(Ŝ + κ P₀) − Q_N(Ŝ)‖ → 0` as `κ ↓ 0`. -/
private lemma rd_norm_QN_regS {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ)
    (Xm : Matrix (Fin K) (Fin N) ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ κ in 𝓝[>] (0 : ℝ), ‖QN (regS κ (Tᵀ * T)) Xm - QN (Tᵀ * T) Xm‖ < δ := by
  set B := Xmᵀ * rdP0 (Tᵀ * T) * Xm with hB
  have heq : ∀ κ : ℝ, QN (regS κ (Tᵀ * T)) Xm - QN (Tᵀ * T) Xm = κ • B := fun κ => by
    unfold QN
    rw [rd_regS_eq, Matrix.mul_add, Matrix.add_mul, hB, Matrix.mul_smul, Matrix.smul_mul]
    abel
  have hpos : 0 < δ / (‖B‖ + 1) := by positivity
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℝ) hpos)] with κ hκ
  rw [heq, norm_smul]
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hκ
  rw [Real.norm_eq_abs]
  have hB0 : 0 ≤ ‖B‖ := norm_nonneg _
  calc |κ| * ‖B‖ ≤ δ / (‖B‖ + 1) * ‖B‖ := mul_le_mul_of_nonneg_right hκ.le hB0
    _ < δ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith

/-- `a_j ≤ a_i` for `1 ≤ i ≤ j ≤ 2p`. -/
private lemma rd_anti {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) {i j : ℕ}
    (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ 2 * numBands N σ) : edgeVal N σ j ≤ edgeVal N σ i := by
  obtain ⟨hN, -, hS⟩ := rd_facts h
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ k hik ih =>
    exact (edgeVal_succ_le N σ h.nonneg hN hS (by omega) (by omega)).trans (ih (by omega))

/-! ## The counts up to a band, and the scale `i^{−1/3} N^{−2/3}` -/

/-- `d_k ≤ M ∧ N` for `1 ≤ k ≤ p`, and `d_p = M ∧ N`. -/
private lemma rd_cum {τ : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ)
    (hσ : ∀ j, 0 < σ j) {k : ℕ} (hk : 1 ≤ k) (hkp : k ≤ numBands N σ) :
    cumCount N σ k ≤ min M N ∧ cumCount N σ (numBands N σ) = min M N := by
  obtain ⟨hN, hM, hS⟩ := rd_facts hda
  have hp := (card_innerCrit N σ hda.nonneg hN hS).2
  have hsum := (Ni_sum N σ hσ hN hM).2
  have hnn : ∀ l ∈ Finset.Icc 1 (numBands N σ), l ∉ Finset.Icc 1 k →
      0 ≤ bandCount N σ l := fun l _ _ => by unfold bandCount; positivity
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := fun l => bandCount N σ l)
    (Finset.Icc_subset_Icc le_rfl hkp) hnn
  obtain ⟨hc1, -, -⟩ := cumCount_spec hda hk hkp
  obtain ⟨hcp, -, -⟩ := cumCount_spec hda hp le_rfl
  rw [hsum] at hle hcp
  rw [← hc1] at hle
  constructor
  · have : (cumCount N σ k : ℝ) ≤ ((min M N : ℕ) : ℝ) := by
      rw [Nat.cast_min, min_comm]; exact hle
    exact_mod_cast this
  · have : (cumCount N σ (numBands N σ) : ℝ) = ((min M N : ℕ) : ℝ) := by
      rw [Nat.cast_min, min_comm]; exact hcp
    exact_mod_cast this

/-- `β = i^{−1/3} N^{−2/3}` satisfies `β > 0` and `β³ i N² = 1`. -/
private lemma rd_beta {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < a ^ (-(1 / 3 : ℝ)) * b ^ (-(2 / 3 : ℝ)) ∧
      (a ^ (-(1 / 3 : ℝ)) * b ^ (-(2 / 3 : ℝ))) ^ 3 * a * b ^ 2 = 1 := by
  refine ⟨by positivity, ?_⟩
  have e1 : (a ^ (-(1 / 3 : ℝ))) ^ 3 = a⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    norm_num
    exact Real.rpow_neg_one a
  have e2 : (b ^ (-(2 / 3 : ℝ))) ^ 3 = (b ^ 2)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb.le]
    norm_num
  rw [mul_pow, e1, e2]
  field_simp

/-! ## The density near a regular edge, and the counts in the gaps -/

/-- The lower constant `1/(π √C₂(τ))` of the square-root density. -/
private def rdC1 (τ : ℝ) : ℝ := 1 / (Real.pi * √(edgeC2 τ))

/-- The upper constant `2/(π √c₂(τ))` of the square-root density. -/
private def rdC2 (τ : ℝ) : ℝ := 2 / (Real.pi * √(edgec2 τ))

private lemma rd_C_pos {τ : ℝ} (hτ : 0 < τ) : 0 < edgeC2 τ ∧ 0 < edgec2 τ := by
  have hs := Real.sqrt_pos.2 hτ
  have hcx : 0 < edgecx τ := by unfold edgecx; positivity
  refine ⟨by unfold edgeC2 edgeCx; positivity, by unfold edgec2 edgeCx; positivity⟩

private lemma rd_C1_pos {τ : ℝ} (hτ : 0 < τ) : 0 < rdC1 τ := by
  have := (rd_C_pos hτ).1; unfold rdC1; positivity

private lemma rd_C2_pos {τ : ℝ} (hτ : 0 < τ) : 0 < rdC2 τ := by
  have := (rd_C_pos hτ).2; unfold rdC2; positivity

/-- `c₁ √d ≤ ρ ≤ c₂ √d` on the band side of a regular edge, `d` the distance to the edge
(proof of Lemma A.4). -/
private lemma rd_rho_edge {τ : ℝ} {σ : Fin M → ℝ} {l : ℕ} (hda : DensityAssumptions τ N σ)
    (hl : RegularEdge τ N σ l) {x : ℝ} (hx : |x - edgeVal N σ l| ≤ edgeTau0 τ)
    (hside : (-1 : ℝ) ^ (l + 1) * (x - edgeVal N σ l) ≤ 0) :
    rdC1 τ * √|x - edgeVal N σ l| ≤ rhoDens N σ x ∧
      rhoDens N σ x ≤ rdC2 τ * √|x - edgeVal N σ l| := by
  obtain ⟨h1, h2⟩ := (rhoDens_edge hda hl hx).1 hside
  obtain ⟨hC2, hc2⟩ := rd_C_pos hda.pos
  rw [Real.sqrt_div' _ hC2.le] at h1
  rw [Real.sqrt_div' _ hc2.le] at h2
  have hπ := Real.pi_pos
  have hsC := Real.sqrt_pos.2 hC2
  have hsc := Real.sqrt_pos.2 hc2
  set d := √|x - edgeVal N σ l|
  constructor
  · have e : rdC1 τ * d = d / √(edgeC2 τ) / Real.pi := by unfold rdC1; field_simp
    rw [e, div_le_iff₀ hπ]
    linarith
  · have e : rdC2 τ * d = 2 * (d / √(edgec2 τ)) / Real.pi := by unfold rdC2; field_simp
    rw [e, le_div_iff₀ hπ]
    linarith

/-- A point `x ≥ r` at distance `≥ r` from every band is at distance `≥ r` from `supp ϱ`. -/
private lemma rd_dist {τ : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ) {x r : ℝ}
    (hr : 0 ≤ r) (hx : r ≤ x) (hne : (varrho N σ).support.Nonempty)
    (h : ∀ l, 1 ≤ l → l ≤ numBands N σ →
      x + r ≤ edgeVal N σ (2 * l) ∨ edgeVal N σ (2 * l - 1) + r ≤ x) :
    r ≤ Metric.infDist x (varrho N σ).support := by
  refine (Metric.le_infDist hne).2 fun y hy => ?_
  rw [Real.dist_eq]
  rcases le_or_gt y 0 with hy0 | hy0
  · rw [abs_of_nonneg (by linarith)]; linarith
  obtain ⟨l, hl1, hl2, hyl1, hyl2⟩ := rd_supp hda (rd_facts hda).1 hy hy0
  rcases h l hl1 hl2 with h' | h'
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith)]; linarith

/-- `τ₀(τ) ≤ τ/16` for `τ ∈ (0, 1]`. -/
private lemma rd_tau0_le {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) : edgeTau0 τ ≤ τ / 16 := by
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
  have hsq : edgeRho1 τ ^ 2 ≤ (τ / 2) ^ 2 := pow_le_pow_left₀ h1.le h1τ 2
  have hmul : edgec2 τ * edgeRho1 τ ^ 2 ≤ τ ^ 3 / 4 * (τ / 2) ^ 2 :=
    mul_le_mul hc2τ hsq (sq_nonneg _) (by positivity)
  have hτ4 : τ ^ 4 ≤ 1 := pow_le_one₀ hτ.le hτ1
  unfold edgeTau0
  nlinarith

/-- `a_{2k+1} + τ ≤ a_{2k}` when the edge `2k` is regular at `τ`, `k < p`. -/
private lemma rd_sep_dn {τ : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ) {k : ℕ}
    (hk : 1 ≤ k) (hkp : k < numBands N σ) (hreg : RegularEdge τ N σ (2 * k)) :
    edgeVal N σ (2 * k + 1) + τ ≤ edgeVal N σ (2 * k) := by
  have h1 := hreg.2.2.2.1 (2 * k + 1) (by omega) (by omega) (by omega)
  have h2 := rd_anti hda (i := 2 * k) (j := 2 * k + 1) (by omega) (by omega) (by omega)
  rw [abs_of_nonneg (by linarith)] at h1
  linarith

/-- In the gap below the band `k` (between `a_{2k+1}` and `a_{2k}`, or in `(0, a_{2p}]`):
`n(x) = d_k`. -/
private lemma rd_n_gap_dn {τ : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ)
    (hσp : ∀ j, 0 < σ j) {k : ℕ} (hk : 1 ≤ k) (hkp : k ≤ numBands N σ) {x : ℝ} (hx0 : 0 < x)
    (hx1 : x ≤ edgeVal N σ (2 * k)) (hx2 : k < numBands N σ → edgeVal N σ (2 * k + 1) ≤ x) :
    nClass N σ x = cumCount N σ k := by
  obtain ⟨hN, hM, hS⟩ := rd_facts hda
  have hσ := hda.nonneg
  have hna := (nClass_edgeVal hda hk hkp).2 (by linarith)
  have hlo := rd_nClass_anti hσ hN hx1
  rcases lt_or_eq_of_le hkp with hlt | heq
  · have hnb := (nClass_edgeVal hda (k := k + 1) (by omega) (by omega)).1
    rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega, show k + 1 - 1 = k by omega] at hnb
    have hup := rd_nClass_anti hσ hN (hx2 hlt)
    linarith
  · have hcp := (rd_cum hda hσp hk hkp).2
    rw [← heq] at hcp
    have hz := (Ni_sum N σ hσp hN hM).1
    have := isProbabilityMeasure_varrho N σ hσ hN
    have hdisj : Disjoint ({0} : Set ℝ) (Set.Ici x) := by
      rw [Set.disjoint_left]
      intro t ht1 ht2
      rw [Set.mem_singleton_iff] at ht1
      rw [ht1, Set.mem_Ici] at ht2
      linarith
    have hsum : varrho N σ {0} + varrho N σ (Set.Ici x) ≤ 1 := by
      rw [← measure_union hdisj measurableSet_Ici]
      exact prob_le_one
    have hsum' : (varrho N σ {0}).toReal + (varrho N σ (Set.Ici x)).toReal ≤ 1 := by
      rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
      have := ENNReal.toReal_mono ENNReal.one_ne_top hsum
      simpa using this
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hmul := mul_le_mul_of_nonneg_left hsum' hN0
    have hle : nClass N σ x ≤ (min M N : ℕ) := by
      unfold nClass
      rw [Nat.cast_min]
      rcases le_total M N with hMN | hMN
      · rw [min_eq_left (by exact_mod_cast hMN)]
        rw [max_eq_left (by have : (M : ℝ) ≤ N := by exact_mod_cast hMN
                            linarith)] at hz
        nlinarith
      · rw [min_eq_right (by exact_mod_cast hMN)]
        have : 0 ≤ (varrho N σ {0}).toReal := ENNReal.toReal_nonneg
        nlinarith
    rw [hcp] at hna ⊢
    linarith

/-! ## The scale `ι^{−1/3} N^{−2/3}`, and the atom at `0` -/

/-- `N⁻¹ ≤ β ≤ N^{−2/3}` for `β = ι^{−1/3} N^{−2/3}`, `1 ≤ ι ≤ N`. -/
private lemma rd_beta_bounds {ι : ℕ} (hι : 1 ≤ ι) (hιN : ι ≤ N) :
    0 < (ι : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) ∧
      (ι : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) ≤ (N : ℝ) ^ (-(2 / 3 : ℝ)) ∧
      (N : ℝ)⁻¹ ≤ (ι : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) := by
  have hι1 : (1 : ℝ) ≤ ι := by exact_mod_cast hι
  have hNι : (ι : ℝ) ≤ N := by exact_mod_cast hιN
  have hN0 : (0 : ℝ) < N := by linarith
  have h2 : (0 : ℝ) < (N : ℝ) ^ (-(2 / 3 : ℝ)) := by positivity
  refine ⟨by positivity, ?_, ?_⟩
  · have : (ι : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hι1 (by norm_num)
    nlinarith
  · have e : (N : ℝ)⁻¹ = (N : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) := by
      rw [← Real.rpow_add hN0, show -(1 / 3 : ℝ) + -(2 / 3) = -1 by norm_num, Real.rpow_neg_one]
    rw [e]
    have := Real.rpow_le_rpow_of_nonpos (by linarith : (0 : ℝ) < ι) hNι
      (by norm_num : -(1 / 3 : ℝ) ≤ 0)
    exact mul_le_mul_of_nonneg_right this h2.le

/-- `0 ∈ supp ϱ` when `M < N` (the atom `(1 − M/N) δ₀`). -/
private lemma rd_zero_mem_supp {τ : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ)
    (hσ : ∀ j, 0 < σ j) (hMN : M < N) : (0 : ℝ) ∈ (varrho N σ).support := by
  obtain ⟨hN, hM, -⟩ := rd_facts hda
  have hz := (Ni_sum N σ hσ hN hM).1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hMNr : (M : ℝ) < N := by exact_mod_cast hMN
  have hpos : 0 < (varrho N σ {0}).toReal := by
    have h1 : (0 : ℝ) < max ((N : ℝ) - M) 0 := lt_max_of_lt_left (by linarith)
    rw [← hz] at h1
    exact (mul_pos_iff_of_pos_left hN0).1 h1
  rw [Measure.mem_support_iff_forall]
  intro U hU
  have h0 : ({0} : Set ℝ) ⊆ U := Set.singleton_subset_iff.2 (mem_of_mem_nhds hU)
  exact lt_of_lt_of_le (ENNReal.toReal_pos_iff.1 hpos).1 (measure_mono h0)

/-- `Tᵀ T` is symmetric. -/
private lemma rd_TtT_herm {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ) : (Tᵀ * T).IsHermitian := by
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.posSemidef_conjTranspose_mul_self T).isHermitian

/-- `λ̇_{k,i} = (N/(N−1)) λ_j(π̄ B π̄)` for a general `T`, `B = Xᵀ Tᵀ T X`,
`j = Ṅ_1 + ⋯ + Ṅ_{k−1} + i`. -/
private lemma rd_lamDotT_eq {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ)
    (Xm : Matrix (Fin K) (Fin N) ℝ) (hN : 2 ≤ N) {l i : ℕ}
    (hj : 1 ≤ cumCount (N - 1) (specOf (T * Tᵀ)) (l - 1) + i)
    (hjN : cumCount (N - 1) (specOf (T * Tᵀ)) (l - 1) + i ≤ N) :
    lamDotBandT T Xm l i = (N : ℝ) / (N - 1) *
      sortedEig (QN (Tᵀ * T) (Xdot Xm)) (cumCount (N - 1) (specOf (T * Tᵀ)) (l - 1) + i) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hc : 0 < (N : ℝ) / (N - 1) := div_pos (by linarith) (by linarith)
  unfold lamDotBandT QdotNT
  exact rd_sortedEig_smul (XSX_isHermitian (rd_TtT_herm T) (Xdot Xm)) hc hj hjN

set_option maxHeartbeats 1000000 in
-- many linear-arithmetic steps over a large context
/-- The bulk step at one index, on the rigidity event of Theorem 3.15 (iii) at `N`, for the
companion `B = Xᵀ S X` of any symmetric `S` and classical data `σ ≥ 0`: interlacing of `π̄ B π̄`
against `B`, `|n_{N−1} − n_N| ≤ N^{ε₁}` and the density bound `c₀`. -/
private lemma rd_bulk_det {τ τ' c₀ ε ε₁ : ℝ} {K : ℕ} {S : Matrix (Fin K) (Fin K) ℝ}
    {Xm : Matrix (Fin K) (Fin N) ℝ} {σ : Fin M → ℝ} {k : ℕ} (hda : DensityAssumptions τ N σ)
    (hS : S.IsHermitian) (hN2 : 2 ≤ N) (hk1 : 1 ≤ k)
    (hkp : k ≤ numBands N σ) (hτ' : 0 < τ') (hc0 : 0 < c₀) (hε₁0 : 0 < ε₁)
    (hρ : ∀ E ∈ Set.Icc (edgeVal N σ (2 * k) + τ' / 2) (edgeVal N σ (2 * k - 1) - τ' / 2),
      c₀ ≤ rhoDens N σ E)
    (hsub : ∀ E, min τ τ' ≤ E → |nClass (N - 1) σ E - nClass N σ E| ≤ (N : ℝ) ^ ε₁)
    (hω : ∀ i, 1 ≤ i → i ≤ bandNat N σ k →
      gammaBand N σ k i ∈ Set.Icc (edgeVal N σ (2 * k) + τ' / 2)
        (edgeVal N σ (2 * k - 1) - τ' / 2) →
      |sortedEig (QN S Xm) (cumCount N σ (k - 1) + i) - gammaBand N σ k i| ≤
        (N : ℝ) ^ ε₁ * (N : ℝ)⁻¹)
    (f3 : (2 / c₀ + 1 + 2 * (2 * τ⁻¹ * (1 + τ⁻¹))) * (N : ℝ) ^ ε₁ ≤ (N : ℝ) ^ ε)
    (f4 : 4 / (c₀ * τ') * (N : ℝ) ^ ε₁ ≤ N) (f5 : 4 / τ' * (N : ℝ) ^ ε₁ ≤ N)
    {l i : ℕ} (hi : 1 ≤ i)
    (hE : gammaBand (N - 1) σ l i ∈
      Set.Icc (edgeVal N σ (2 * k) + τ') (edgeVal N σ (2 * k - 1) - τ')) :
    |(N : ℝ) / (N - 1) * sortedEig (QN S (Xdot Xm)) (cumCount (N - 1) σ (l - 1) + i) -
      gammaBand (N - 1) σ l i| ≤ (N : ℝ) ^ ε * (N : ℝ)⁻¹ := by
  have hτ := hda.pos
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  set Ca := 2 * τ⁻¹ * (1 + τ⁻¹) with hCa
  have hCa0 : 0 ≤ Ca := by rw [hCa]; positivity
  set K' := 2 / c₀ + 1 + 2 * Ca with hK'
  have hσ := hda.nonneg
  have hdaN1 := rd_da_pred hda hN2
  obtain ⟨hN0, -, -⟩ := rd_facts hda
  have hN10 : 0 < N - 1 := by omega
  -- the index `j` at `N − 1`
  set a₂ := edgeVal N σ (2 * k) with ha₂
  set a₁ := edgeVal N σ (2 * k - 1) with ha₁
  have ha₂0 := (rd_edge_mem hda hN0 (k := 2 * k) (by omega) (by omega)).1
  have ha₁C := (rd_edge_mem hda hN0 (k := 2 * k - 1) (by omega) (by omega)).2
  rw [← ha₁, ← hCa] at ha₁C
  rw [← ha₂] at ha₂0
  have hEdef : gammaBand (N - 1) σ l i = gammaLoc (N - 1) σ (cumCount (N - 1) σ (l - 1) + i) :=
    rfl
  rw [hEdef] at hE ⊢
  set j := cumCount (N - 1) σ (l - 1) + i with hj
  set E := gammaLoc (N - 1) σ j with hEd
  have hE0 : 0 < E := by linarith [hE.1]
  have hj1 : 1 ≤ j := by omega
  have hnE := nClass_gammaLoc_of_pos hσ hN10 hE0
  have hEτ : min τ τ' ≤ E := le_trans (min_le_right _ _) (by linarith [hE.1])
  have hsub := hsub E hEτ
  rw [abs_le] at hsub
  -- the window of half-width `r`
  set s := (N : ℝ) ^ ε₁ with hs
  have hs1 : 1 ≤ s := Real.one_le_rpow (by linarith) hε₁0.le
  set r := (s + 1) / (c₀ * N) with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  have hNcr : (N : ℝ) * c₀ * r = s + 1 := by rw [hr]; field_simp
  have hrτ : r ≤ τ' / 2 := by
    rw [hr, div_le_iff₀ (by positivity)]
    have e : 4 / (c₀ * τ') * s * (c₀ * τ' / 8) = s / 2 := by field_simp; ring
    have := mul_le_mul_of_nonneg_right f4 (by positivity : (0 : ℝ) ≤ c₀ * τ' / 8)
    rw [e] at this
    linarith
  have hsN : s * (N : ℝ)⁻¹ ≤ τ' / 4 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hNpos]
    have e : 4 / τ' * s * (τ' / 4) = s := by field_simp
    have := mul_le_mul_of_nonneg_right f5 (by positivity : (0 : ℝ) ≤ τ' / 4)
    rw [e] at this
    linarith
  have hwin : ∀ x, E - r ≤ x → x ≤ E + r →
      x ∈ Set.Icc (a₂ + τ' / 2) (a₁ - τ' / 2) :=
    fun x h1 h2 => ⟨by linarith [hE.1], by linarith [hE.2]⟩
  have hm1 := rd_nClass_sub_ge hσ hN0 (x := E - r) (y := E) (c₀ := c₀)
    (by linarith [hE.1]) (by linarith) hc0.le
    (fun u hu => hρ u (hwin u hu.1 (by linarith [hu.2])))
  have hm2 := rd_nClass_sub_ge hσ hN0 (x := E) (y := E + r) (c₀ := c₀)
    (by linarith [hE.1]) (by linarith) hc0.le
    (fun u hu => hρ u (hwin u (by linarith [hu.1]) (by linarith [hu.2])))
  rw [show E - (E - r) = r by ring, hNcr] at hm1
  rw [show E + r - E = r by ring, hNcr] at hm2
  have hjr : (j : ℝ) - 1 / 2 = nClass (N - 1) σ E := hnE.symm
  have hlo : (j : ℝ) + 1 / 2 ≤ nClass N σ (E - r) := by linarith
  have hhi : nClass N σ (E + r) ≤ (j : ℝ) - 3 / 2 := by linarith
  -- `j` and `j + 1` lie in the band `k` at `N`
  obtain ⟨-, -, hcs⟩ := cumCount_spec hda hk1 hkp
  have hna := (nClass_edgeVal hda hk1 hkp).1
  have hcm : cumCount N σ k ≤ N := by
    have := (rd_cum_le hda hN0 hk1 hkp).trans (min_le_left _ _)
    exact_mod_cast this
  have hc1 : (cumCount N σ (k - 1) : ℝ) ≤ (j : ℝ) - 3 / 2 := by
    rw [← hna]
    exact le_trans (rd_nClass_anti hσ hN0 (by linarith [hE.2])) hhi
  have hc2 : (j : ℝ) + 1 / 2 ≤ cumCount N σ k :=
    hlo.trans (rd_n_le_cum hda hk1 hkp (by linarith [hE.1]))
  have hc1' : cumCount N σ (k - 1) + 1 ≤ j := by
    have : (cumCount N σ (k - 1) : ℝ) + 1 ≤ j := by linarith
    exact_mod_cast this
  have hc2' : j + 1 ≤ cumCount N σ k := by
    have : (j : ℝ) + 1 ≤ cumCount N σ k := by
      have h := hc2
      have : ((j + 1 : ℕ) : ℝ) < (cumCount N σ k : ℝ) + 1 := by push_cast; linarith
      have := Nat.lt_succ_iff.mp (by exact_mod_cast this)
      exact_mod_cast this
    exact_mod_cast this
  have hjN : j + 1 ≤ N := hc2'.trans hcm
  -- the classical locations `γ_j`, `γ_{j+1}` at `N` near `E`
  have hγ2 : E - r ≤ gammaLoc N σ j :=
    rd_le_gamma hda hj1 (by linarith [hE.1]) (by linarith)
  have hγ4 : E - r ≤ gammaLoc N σ (j + 1) :=
    rd_le_gamma hda (by omega) (by linarith [hE.1]) (by push_cast; linarith)
  have hnγ := nClass_gammaLoc_of_pos hσ hN0 (show 0 < gammaLoc N σ j by linarith [hE.1])
  have hnγ' := nClass_gammaLoc_of_pos hσ hN0 (show 0 < gammaLoc N σ (j + 1) by linarith [hE.1])
  push_cast at hnγ'
  have hγ1 : gammaLoc N σ j ≤ E + r := by
    by_contra hc
    have := rd_nClass_anti hσ hN0 (le_of_lt (not_le.mp hc))
    linarith
  have hγ3 : gammaLoc N σ (j + 1) ≤ E + r := by
    by_contra hc
    have := rd_nClass_anti hσ hN0 (le_of_lt (not_le.mp hc))
    linarith
  -- rigidity at `N` for `j` and `j + 1`
  set i₁ := j - cumCount N σ (k - 1) with hi₁
  have hi₁j : cumCount N σ (k - 1) + i₁ = j := by omega
  have hi₁j' : cumCount N σ (k - 1) + (i₁ + 1) = j + 1 := by omega
  have hr1 := hω i₁ (by omega) (by omega)
    (by rw [gammaBand, hi₁j]; exact hwin _ hγ2 hγ1)
  have hr2 := hω (i₁ + 1) (by omega) (by omega)
    (by rw [gammaBand, hi₁j']; exact hwin _ hγ4 hγ3)
  rw [gammaBand, hi₁j] at hr1
  rw [gammaBand, hi₁j'] at hr2
  rw [abs_le] at hr1 hr2
  -- interlacing and the factor `N/(N − 1)`
  set L := sortedEig (QN S Xm) (j + 1) with hL
  set U := sortedEig (QN S Xm) j with hU
  have hL0 : 0 < L := by linarith [hE.1]
  have hLj := rd_interlace_lo hS Xm hj1 hjN
  obtain ⟨hb1, hb2⟩ := rd_dot_bounds hS Xm hN2 hj1 (by omega) hL0 hLj le_rfl
  have hU0 : 0 ≤ U := by linarith [hE.1, hr1.1]
  have hUle : U ≤ Ca := by linarith [hE.2, hr1.2]
  have hdiv := rd_div_pred hU0 hN2
  have hfin : (s + 1) / c₀ + s + 2 * Ca ≤ (N : ℝ) ^ ε := by
    refine le_trans ?_ f3
    have h1 : (s + 1) / c₀ ≤ 2 / c₀ * s := by
      rw [div_le_iff₀ hc0]; field_simp; linarith
    have h2 : 2 * Ca ≤ 2 * Ca * s := by nlinarith
    linarith
  have hNi : 0 < (N : ℝ)⁻¹ := inv_pos.mpr hNpos
  have hfin' : r + s * (N : ℝ)⁻¹ + 2 * Ca * (N : ℝ)⁻¹ ≤ (N : ℝ) ^ ε * (N : ℝ)⁻¹ := by
    have e : r = (s + 1) / c₀ * (N : ℝ)⁻¹ := by rw [hr]; field_simp
    rw [e]
    have := mul_le_mul_of_nonneg_right hfin hNi.le
    linarith
  have h2U : 2 * U * (N : ℝ)⁻¹ ≤ 2 * Ca * (N : ℝ)⁻¹ :=
    mul_le_mul_of_nonneg_right (by linarith) hNi.le
  have hCN : 0 ≤ 2 * Ca * (N : ℝ)⁻¹ := by positivity
  rw [abs_le]
  constructor <;> linarith


/-- The band of `K` samples containing a point `E` near a point `a`: if the edge `l'` lies within
`r'` of `a`, is regular at `τ₁`, and `|E − a| ≤ r` with `r + r' < τ₁`, then `l'` is an edge of
that band `l`. -/
private lemma rd_partner {τ₁ : ℝ} {K : ℕ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ₁ K σ)
    {l l' : ℕ} (hl : 1 ≤ l) (hlp : l ≤ numBands K σ) (hreg : RegularEdge τ₁ K σ l')
    {E a r r' : ℝ} (hE1 : edgeVal K σ (2 * l) ≤ E) (hE2 : E ≤ edgeVal K σ (2 * l - 1))
    (hEa : |E - a| ≤ r) (hpa : |edgeVal K σ l' - a| ≤ r') (hsmall : r + r' < τ₁) :
    (l' + 1) / 2 = l := by
  obtain ⟨hl1, hl2, -, hsep, -⟩ := hreg
  have hd : |E - edgeVal K σ l'| < τ₁ := by
    have := abs_sub_le E a (edgeVal K σ l')
    rw [abs_sub_comm a] at this
    linarith
  rw [abs_lt] at hd
  rcases Nat.even_or_odd l' with ⟨q, hq⟩ | ⟨q, hq⟩
  · have hl'e : l' = 2 * l := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have h1 := rd_anti hda (i := l') (j := 2 * l - 1) hl1 (by omega) (by omega)
        have h2 := hsep (2 * l - 1) (by omega) (by omega) (by omega)
        rw [abs_of_nonneg (by linarith)] at h2
        linarith
      · have h1 := rd_anti hda (i := 2 * l) (j := l') (by omega) hgt.le hl2
        have h2 := hsep (2 * l) (by omega) (by omega) (by omega)
        rw [abs_of_nonpos (by linarith)] at h2
        linarith
    omega
  · have hl'e : l' = 2 * l - 1 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have h1 := rd_anti hda (i := l') (j := 2 * l - 1) hl1 hlt.le (by omega)
        have h2 := hsep (2 * l - 1) (by omega) (by omega) (by omega)
        rw [abs_of_nonneg (by linarith)] at h2
        linarith
      · have h1 := rd_anti hda (i := 2 * l) (j := l') (by omega) (by omega) hl2
        have h2 := hsep (2 * l) (by omega) (by omega) (by omega)
        rw [abs_of_nonpos (by linarith)] at h2
        linarith
    omega

/-- `Q̇` is symmetric for symmetric `Σ`. -/
private lemma rd_QdotN_herm {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.IsHermitian)
    (Xm : Matrix (Fin M) (Fin N) ℝ) : (QdotN Sig Xm).IsHermitian := by
  have hA : (QN Sig (Xdot Xm)).IsHermitian := XSX_isHermitian hSig (Xdot Xm)
  unfold QdotN Matrix.IsHermitian
  rw [conjTranspose_smul]
  change star (((N : ℝ) / (N - 1))) • (QN Sig (Xdot Xm))ᴴ = _
  rw [hA.eq, star_trivial]

/-- The edge-local statement for a general `T`. -/
theorem rigidity_dot_edge_gen (τ : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M K : ℕ) (T : Matrix (Fin M) (Fin K) ℝ) (X : Ω → Matrix (Fin K) (Fin N) ℝ) (k : ℕ),
      IsModelT τ C M K N T X → RegularEdge τ N (specOf (T * Tᵀ)) k →
      HighProbAt N D {ω | ∀ l, 1 ≤ l → l ≤ numBands (N - 1) (specOf (T * Tᵀ)) →
        ∀ i, 1 ≤ i → i ≤ bandNat (N - 1) (specOf (T * Tᵀ)) l →
        gammaBand (N - 1) (specOf (T * Tᵀ)) l i ∈
          Set.Icc (edgeVal N (specOf (T * Tᵀ)) k - tauGen τ / 4)
            (edgeVal N (specOf (T * Tᵀ)) k + tauGen τ / 4) →
        |lamDotBandT T (X ω) l i - gammaBand (N - 1) (specOf (T * Tᵀ)) l i| ≤
          rigBound N (bandNat (N - 1) (specOf (T * Tᵀ)) l) i ε} := by
  by_cases hτ1 : τ ≤ 1
  swap
  · exact ⟨0, fun N _ Ω _ _ M K T X k hm _ => absurd (rd_tau_le_one hm) hτ1⟩
  have hτh : 0 < τ / 2 := by positivity
  have hτe : 0 < tauE τ := tauE_pos hτ
  have hτe3 : tauE τ ≤ τ ^ 3 := min_le_left _ _
  obtain ⟨hgen0, hgenτ⟩ := rd_tauGen hτ hτ1
  set e := edgeTau' (tauE τ) with he
  have he0 : 0 < e := edgeTau'_pos hτe
  have hgen : tauGen τ = e / 4 := rfl
  have hδa : deltaA τ ≤ e / 16 := min_le_left _ _
  obtain ⟨N₀, h₀⟩ := rigidity_dot_edge (tauE τ) C ε D hτe hε
  obtain ⟨C₁, Na, hpred⟩ := edge_pred τ hτ
  refine ⟨max (max N₀ Na) (max (⌈4 * |C₁| / τ⌉₊ + 1) 3),
    fun N hN Ω _ _ M K T X k hm hreg => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hN
  obtain ⟨⟨hN0, hNa⟩, hNC, hN3⟩ := hN
  have hN1 : 1 ≤ N := by omega
  have hN2 : 2 ≤ N := by omega
  have hN11 : 1 ≤ N - 1 := by omega
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hNC' : 4 * |C₁| / τ ≤ N := by
    have := Nat.le_ceil (4 * |C₁| / τ)
    have h' : ((⌈4 * |C₁| / τ⌉₊ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hNC
    push_cast at h'
    linarith
  have hC₁N : C₁ / N ≤ τ / 4 := by
    rw [div_le_iff₀ (by linarith)]
    rw [div_le_iff₀ hτ] at hNC'
    have := le_abs_self C₁
    nlinarith
  set σ := specOf (T * Tᵀ) with hσdef
  have hda : DensityAssumptions τ N σ := hm.densityAssumptions hτ
  have hσ : ∀ i, 0 ≤ σ i := hda.nonneg
  have hda1 : DensityAssumptions (τ / 2) (N - 1) σ := rd_da_pred hda hN2
  -- the partner edge `l̃` of `k` for `N − 1` samples, and its regularisation
  obtain ⟨lt, -, hlta, hltreg⟩ := hpred N hNa M σ hda k hreg
  have hK1 : (K : ℝ) / ((N - 1 : ℕ) : ℝ) ≤ (τ / 2)⁻¹ := by
    rw [rd_cast_pred hN2]
    have hK := hm.ratioK_le
    have hNr' : (0 : ℝ) < N - 1 := by linarith
    rw [div_le_iff₀ hNr']
    rw [div_le_iff₀ (by linarith)] at hK
    have e2 : (τ / 2)⁻¹ = 2 * τ⁻¹ := by field_simp
    rw [e2]
    have hτi : 0 < τ⁻¹ := inv_pos.mpr hτ
    nlinarith
  have hreg1 := regularEdge_regS (N := N - 1) hτh (by linarith) hN11 hda1 hK1 hltreg
  -- the admissible edges `l'` of `Ŝ + κ P₀` at `N`, and the event of `rigidity_dot_edge` there
  set P : ℝ → ℕ → Prop := fun κ l' =>
    RegularEdge (tauE τ) N (specOf (regS κ (Tᵀ * T))) l' ∧
      |edgeVal N (specOf (regS κ (Tᵀ * T))) l' - edgeVal N σ k| ≤ deltaA τ with hP
  set Ev : ℝ → ℕ → Set Ω := fun κ l' =>
    {ω | ∀ l, 1 ≤ l → l ≤ numBands (N - 1) (specOf (regS κ (Tᵀ * T))) →
      ∀ i, 1 ≤ i → i ≤ bandNat (N - 1) (specOf (regS κ (Tᵀ * T))) l →
      gammaBand (N - 1) (specOf (regS κ (Tᵀ * T))) l i ∈
        Set.Icc (edgeVal N (specOf (regS κ (Tᵀ * T))) l' - e / 4)
          (edgeVal N (specOf (regS κ (Tᵀ * T))) l' + e / 4) →
      |lamDotBand (regS κ (Tᵀ * T)) (X ω) l i - gammaBand (N - 1) (specOf (regS κ (Tᵀ * T))) l i| ≤
        rigBound N (bandNat (N - 1) (specOf (regS κ (Tᵀ * T))) l) i ε} with hEv
  have hregκ := regularEdge_regS hτ (show τ / 2 ≤ τ by linarith) hN1 hda hm.ratioK_le hreg
  have hκev : ∀ᶠ κ in 𝓝[>] (0 : ℝ), 0 < κ ∧ κ ≤ τ ^ 3 :=
    Filter.mem_of_superset (Ioc_mem_nhdsGT (by positivity)) fun κ hκ => hκ
  have hcN : (0 : ℝ) < (N : ℝ) / (N - 1) := div_pos (by linarith) (by linarith)
  unfold HighProbAt
  refine measure_le_of_eventually (l := 𝓝[>] (0 : ℝ))
    (Bi := fun κ => {ω | ∀ l', P κ l' → ω ∉ Ev κ l'}) ?_ ?_
  · intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall] at hω
    obtain ⟨l, hl1, hlp, i, hi1, hiN, hwin, hbad⟩ := hω
    rw [not_le] at hbad
    obtain ⟨hk1, hk2, hak, -, -⟩ := hreg
    set j := cumCount (N - 1) σ (l - 1) + i with hj
    have hγdef : gammaBand (N - 1) σ l i = gammaLoc (N - 1) σ j := rfl
    have hlamdef : lamDotBandT T (X ω) l i = sortedEig (QdotNT T (X ω)) j := rfl
    rw [hγdef] at hwin hbad
    rw [hlamdef] at hbad
    set γ := gammaLoc (N - 1) σ j with hγ
    set lam := sortedEig (QdotNT T (X ω)) j with hlam
    set β := rigBound N (bandNat (N - 1) σ l) i ε with hβ
    have hγpos : 0 < γ := by
      have := hwin.1
      linarith
    -- the partner `l̃` is an edge of the band `l`
    obtain ⟨hγl, hγu⟩ := rd_band_mem hda1 (by omega) hl1 hlp hi1 hiN hγpos
    have hlt : (lt + 1) / 2 = l := by
      refine rd_partner hda1 hl1 hlp hltreg hγl hγu (a := edgeVal N σ k) (r := e / 16)
        (r' := C₁ / N) ?_ hlta ?_
      · rw [abs_le]; constructor <;> linarith [hwin.1, hwin.2]
      · linarith
    set g := |lam - γ| - β with hg
    have hg0 : 0 < g := by rw [hg]; linarith
    have hγlim := tendsto_gammaLoc_regS hN11 T hγpos
    have hγev : ∀ᶠ κ in 𝓝[>] (0 : ℝ),
        dist (gammaLoc (N - 1) (specOf (regS κ (Tᵀ * T))) j) γ < min (e / 16) (g / 2) :=
      (Metric.tendsto_nhds.1 hγlim) _ (by positivity)
    have hlamev := rd_norm_QN_regS T (Xdot (X ω)) (show 0 < g / 2 / ((N : ℝ) / (N - 1)) by
      positivity)
    filter_upwards [hκev, hγev, hlamev, hreg1] with κ hκ hγκ hlamκ hl''
    obtain ⟨l'', hl''reg, -, hcl1, hcl2⟩ := hl''
    rw [hlt, ← hσdef] at hcl1 hcl2
    intro l' hPl' hω'
    obtain ⟨hregl', hal'⟩ := hPl'
    have hmκ : IsModel (tauE τ) C K N (regS κ (Tᵀ * T)) X :=
      (isModel_regS hτ hm hκ.1 hκ.2).mono hτe hτe3
    have hdaκ : DensityAssumptions (tauE τ) N (specOf (regS κ (Tᵀ * T))) :=
      hmκ.diagModel_specOf.densityAssumptions hτe
    have hdaκ1 := rd_da_pred hdaκ hN2
    set σκ := specOf (regS κ (Tᵀ * T)) with hσκ
    obtain ⟨hl''1, hl''2, -, -, -⟩ := hl''reg
    set ll := (l'' + 1) / 2 with hll
    have hll1 : 1 ≤ ll := by omega
    have hllp : ll ≤ numBands (N - 1) σκ := by omega
    obtain ⟨-, -, hcκ⟩ := cumCount_spec hdaκ1 hll1 hllp
    obtain ⟨-, -, hc⟩ := cumCount_spec hda1 hl1 hlp
    set i'' := j - cumCount (N - 1) σκ (ll - 1) with hi''
    have hji : cumCount (N - 1) σκ (ll - 1) + i'' = j := by omega
    have hi''1 : 1 ≤ i'' := by omega
    have hi''N : i'' ≤ bandNat (N - 1) σκ ll := by omega
    have hγκdef : gammaBand (N - 1) σκ ll i'' = gammaLoc (N - 1) σκ j := by
      unfold gammaBand; rw [hji]
    have hlamκdef : lamDotBand (regS κ (Tᵀ * T)) (X ω) ll i'' =
        sortedEig (QdotN (regS κ (Tᵀ * T)) (X ω)) j := by
      unfold lamDotBand; rw [← hσκ, hji]
    have hγκ' : |gammaLoc (N - 1) σκ j - γ| < min (e / 16) (g / 2) := by
      rw [← Real.dist_eq]; exact hγκ
    have hγκ1 : |gammaLoc (N - 1) σκ j - γ| < e / 16 := hγκ'.trans_le (min_le_left _ _)
    have hγκ2 : |gammaLoc (N - 1) σκ j - γ| < g / 2 := hγκ'.trans_le (min_le_right _ _)
    have hwin' : gammaBand (N - 1) σκ ll i'' ∈ Set.Icc (edgeVal N σκ l' - e / 4)
        (edgeVal N σκ l' + e / 4) := by
      rw [hγκdef]
      have h1 := abs_le.1 hγκ1.le
      have h2 := abs_le.1 hal'
      have h3 := hwin
      rw [hgen] at h3
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
    have hres := hω' ll hll1 hllp i'' hi''1 hi''N hwin'
    rw [hγκdef, hlamκdef] at hres
    have hβ' : rigBound N (bandNat (N - 1) σκ ll) i'' ε ≤ β :=
      rd_rigBound_mono (by omega) (min_le_min (by omega) (by omega))
    -- Weyl for the companions of `Q̇`
    have hdiff : QdotN (regS κ (Tᵀ * T)) (X ω) - QdotNT T (X ω) =
        ((N : ℝ) / (N - 1)) • (QN (regS κ (Tᵀ * T)) (Xdot (X ω)) - QN (Tᵀ * T) (Xdot (X ω))) := by
      unfold QdotN QdotNT; rw [smul_sub]
    have hnorm : ‖QdotN (regS κ (Tᵀ * T)) (X ω) - QdotNT T (X ω)‖ < g / 2 := by
      rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos hcN]
      have := mul_lt_mul_of_pos_left hlamκ hcN
      rwa [mul_div_cancel₀ _ hcN.ne'] at this
    have hherm1 := rd_QdotN_herm (regS_posDef hκ.1 T).isHermitian (X ω)
    have hherm2 : (QdotNT T (X ω)).IsHermitian := rd_QdotN_herm (rd_TtT_herm T) (X ω)
    have hlam' := (rd_abs_sortedEig_sub hherm1 hherm2 j).trans_lt hnorm
    have htri : |lam - γ| ≤ |sortedEig (QdotN (regS κ (Tᵀ * T)) (X ω)) j - gammaLoc (N - 1) σκ j| +
        |sortedEig (QdotN (regS κ (Tᵀ * T)) (X ω)) j - lam| + |gammaLoc (N - 1) σκ j - γ| := by
      have h1 := abs_sub_le lam (sortedEig (QdotN (regS κ (Tᵀ * T)) (X ω)) j) γ
      have h2 := abs_sub_le (sortedEig (QdotN (regS κ (Tᵀ * T)) (X ω)) j) (gammaLoc (N - 1) σκ j) γ
      have h3 := abs_sub_comm lam (sortedEig (QdotN (regS κ (Tᵀ * T)) (X ω)) j)
      linarith
    linarith
  · filter_upwards [hregκ, hκev] with κ hl hκ
    obtain ⟨l', hl'⟩ := hl
    have hmκ : IsModel (tauE τ) C K N (regS κ (Tᵀ * T)) X :=
      (isModel_regS hτ hm hκ.1 hκ.2).mono hτe hτe3
    have hpr := h₀ N hN0 K (regS κ (Tᵀ * T)) X l' hmκ hl'.1
    refine le_trans (measure_mono ?_) hpr
    intro ω hω
    exact hω l' ⟨hl'.1, hl'.2.1⟩

/-- The bulk-local statement for a general `T`. -/
theorem rigidity_dot_bulk_gen (τ τ' : ℝ) (c : ℝ → ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ)
    (hτ' : 0 < τ') (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M K : ℕ) (T : Matrix (Fin M) (Fin K) ℝ) (X : Ω → Matrix (Fin K) (Fin N) ℝ) (k : ℕ),
      IsModelT τ C M K N T X → RegularBulk c N (specOf (T * Tᵀ)) k →
      (RegularEdge τ N (specOf (T * Tᵀ)) (2 * k) ∨
        RegularEdge τ N (specOf (T * Tᵀ)) (2 * k - 1)) →
      HighProbAt N D {ω | ∀ l, 1 ≤ l → l ≤ numBands (N - 1) (specOf (T * Tᵀ)) →
        ∀ i, 1 ≤ i → i ≤ bandNat (N - 1) (specOf (T * Tᵀ)) l →
        gammaBand (N - 1) (specOf (T * Tᵀ)) l i ∈
          Set.Icc (edgeVal N (specOf (T * Tᵀ)) (2 * k) + τ')
            (edgeVal N (specOf (T * Tᵀ)) (2 * k - 1) - τ') →
        |lamDotBandT T (X ω) l i - gammaBand (N - 1) (specOf (T * Tᵀ)) l i| ≤
          (N : ℝ) ^ ε * (N : ℝ)⁻¹} := by
  by_cases hc0 : 0 < c (τ' / 2)
  swap
  · exact ⟨0, fun N _ Ω _ _ M K T X k _ hb _ => absurd ((hb.2.2 (τ' / 2) (by linarith)).1) hc0⟩
  set c₀ := c (τ' / 2) with hc₀
  set ε₁ := min ε 1 / 2 with hε₁
  have hε₁0 : 0 < ε₁ := by have := lt_min hε one_pos; rw [hε₁]; linarith
  have hε₁ε : ε₁ < ε := by have := min_le_left ε 1; rw [hε₁]; linarith
  have hε₁1 : ε₁ < 1 := by have := min_le_right ε 1; rw [hε₁]; linarith
  set Ca := 2 * τ⁻¹ * (1 + τ⁻¹) with hCa
  have hCa0 : 0 ≤ Ca := by rw [hCa]; positivity
  set K₀ := 2 / c₀ + 1 + 2 * Ca with hK₀
  obtain ⟨N₁, h₁⟩ := rigidity_bulk_gen τ (τ' / 2) c C ε₁ D hτ (by linarith) hε₁0
  obtain ⟨N₂, h₂⟩ := nClass_pred_sub (min τ τ') ε₁ (lt_min hτ hτ') hε₁0
  obtain ⟨N₃, h₃⟩ := rd_ev K₀ hε₁ε
  obtain ⟨N₄, h₄⟩ := rd_ev (4 / (c₀ * τ')) (a := ε₁) (b := 1) hε₁1
  obtain ⟨N₅, h₅⟩ := rd_ev (4 / τ') (a := ε₁) (b := 1) hε₁1
  refine ⟨max (max N₁ N₂) (max (max N₃ N₄) (max N₅ 2)),
    fun N hN Ω _ _ M K T X k hm hb hedge => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hN
  obtain ⟨⟨hN1, hN2'⟩, ⟨hN3, hN4⟩, hN5, hN2⟩ := hN
  have f3 := h₃ N hN3
  have f4 := h₄ N hN4
  have f5 := h₅ N hN5
  rw [Real.rpow_one] at f4 f5
  set σ := specOf (T * Tᵀ) with hσdef
  have hda : DensityAssumptions τ N σ := hm.densityAssumptions hτ
  have hσ := hda.nonneg
  have hS := rd_TtT_herm T
  have hda0 : DensityAssumptions (min τ τ') N σ := hda.mono (lt_min hτ hτ') (min_le_left _ _)
  obtain ⟨hk1, hkp, hbk⟩ := hb
  have hρ := (hbk (τ' / 2) (by linarith)).2
  have hN10 : 0 < N - 1 := by omega
  have ha₂0 := (rd_edge_mem hda (by omega) (k := 2 * k) (by omega) (by omega)).1
  refine rd_hp_mono (h₁ N hN1 M K T X k hm ⟨hk1, hkp, hbk⟩ hedge) fun ω hω => ?_
  simp only [Set.mem_ofPred_eq] at hω ⊢
  intro l hl1 hlp i hi hiN hE
  have hγ0 : 0 < gammaBand (N - 1) σ l i := by linarith [hE.1]
  obtain ⟨hj1, hjN⟩ := rd_dot_index hσ hN10 hi hγ0
  rw [rd_lamDotT_eq T (X ω) hN2 hj1 (hjN.trans (Nat.sub_le N 1))]
  exact rd_bulk_det hda hS hN2 hk1 hkp hτ' hc0 hε₁0 hρ
    (fun E hE => h₂ N hN2' M σ hda0 E hE) hω f3 f4 f5 hi hE

/-- Theorem 11.3 at fixed `N`, under (T_diag): under the hypotheses of Theorem 3.12
(edges with `a_k ≥ τ/2` regular at `τ/2`, all bulk components regular), for all `k ≤ ṗ` and
`i ≤ Ṅ_k` with `γ̇_{k,i} ≥ τ`, `|λ̇_{k,i} − γ̇_{k,i}| ≤ N^ε (i ∧ (Ṅ_k + 1 − i))^{−1/3} N^{−2/3}`
simultaneously; the dotted classical quantities are those of `N − 1` samples. -/
theorem rigidity_dot (τ : ℝ) (C : ℕ → ℝ) (c : ℝ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ),
      IsModel τ C M N Sig X →
      (∀ k, 1 ≤ k → k ≤ 2 * numBands N (specOf Sig) → τ / 2 ≤ edgeVal N (specOf Sig) k →
        RegularEdge (τ / 2) N (specOf Sig) k) →
      (∀ k, 1 ≤ k → k ≤ numBands N (specOf Sig) → RegularBulk c N (specOf Sig) k) →
      HighProbAt N D {ω | ∀ k, 1 ≤ k → k ≤ numBands (N - 1) (specOf Sig) →
        ∀ i, 1 ≤ i → i ≤ bandNat (N - 1) (specOf Sig) k →
        τ ≤ gammaBand (N - 1) (specOf Sig) k i →
          |lamDotBand Sig (X ω) k i - gammaBand (N - 1) (specOf Sig) k i| ≤
            rigBound N (bandNat (N - 1) (specOf Sig) k) i ε} := by
  by_cases hτ1 : τ ≤ 1
  swap
  · exact ⟨0, fun N _ Ω _ _ M Sig X hm _ _ => absurd hm.tau_le_one hτ1⟩
  have hτh : 0 < τ / 2 := by positivity
  set w := edgeTau' (τ / 2) / 4 with hw
  have hw0 : 0 < w := by have := edgeTau'_pos hτh; positivity
  have hwτ : w ≤ τ / 4 := by have := rd_edgeTau'_le hτh (by linarith); linarith
  obtain ⟨N₁, h₁⟩ := rigidity_dot_edge (τ / 2) C ε (D + 2) hτh hε
  obtain ⟨N₂, h₂⟩ := rigidity_dot_bulk (τ / 2) w c C ε (D + 2) hτh hw0 hε
  obtain ⟨N₃, h₃⟩ := rd_off_pred (4 * w) (by positivity)
  refine ⟨max (max N₁ N₂) (max N₃ 3), fun N hN Ω _ _ M Sig X hm hedge hbulk => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hN
  obtain ⟨⟨hN₁, hN₂⟩, hN₃, hN3⟩ := hN
  have hNpos : 0 < N := by omega
  have hN1 : 0 < N - 1 := by omega
  set σ := specOf Sig with hσdef
  have hda : DensityAssumptions τ N σ := hm.diagModel_specOf.densityAssumptions hτ
  have hσ := hda.nonneg
  have hmh : IsModel (τ / 2) C M N Sig X := hm.mono hτh (by linarith)
  have hda4 : DensityAssumptions (4 * w) N σ := hda.mono (by positivity) (by linarith)
  refine rd_assemble (lam := fun ω l i => lamDotBand Sig (X ω) l i) (w := w) hN3
    (rd_numBands_le hda hNpos) ?_ ?_ ?_ ?_
  · intro l i hl1 hlp hi hiN hγ
    exact rd_cover hda (by omega) hw0 hwτ
      (fun E hE hd => h₃ N hN₃ M σ hda4 E (by linarith) (by linarith)) hl1 hlp hi hiN hγ
  · intro l i hi hγ
    have := (rd_dot_index hσ hN1 (l := l) hi (by linarith)).2
    omega
  · intro k hk1 hk2 hka
    exact h₁ N hN₁ M Sig X k hmh (hedge k hk1 hk2 hka)
  · intro m hm1 hm2 hma
    exact h₂ N hN₂ M Sig X m hmh (hbulk m hm1 hm2)
      (Or.inr (hedge (2 * m - 1) (by omega) (by omega) hma))

/-- Theorem 11.3 at fixed `N` for a general `T` (§11.1), with the classical quantities of
`N − 1` samples. -/
theorem rigidity_dot_gen (τ : ℝ) (C : ℕ → ℝ) (c : ℝ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M K : ℕ) (T : Matrix (Fin M) (Fin K) ℝ) (X : Ω → Matrix (Fin K) (Fin N) ℝ),
      IsModelT τ C M K N T X →
      (∀ k, 1 ≤ k → k ≤ 2 * numBands N (specOf (T * Tᵀ)) →
        τ / 2 ≤ edgeVal N (specOf (T * Tᵀ)) k → RegularEdge (τ / 2) N (specOf (T * Tᵀ)) k) →
      (∀ k, 1 ≤ k → k ≤ numBands N (specOf (T * Tᵀ)) → RegularBulk c N (specOf (T * Tᵀ)) k) →
      HighProbAt N D {ω | ∀ k, 1 ≤ k → k ≤ numBands (N - 1) (specOf (T * Tᵀ)) →
        ∀ i, 1 ≤ i → i ≤ bandNat (N - 1) (specOf (T * Tᵀ)) k →
        τ ≤ gammaBand (N - 1) (specOf (T * Tᵀ)) k i →
          |lamDotBandT T (X ω) k i - gammaBand (N - 1) (specOf (T * Tᵀ)) k i| ≤
            rigBound N (bandNat (N - 1) (specOf (T * Tᵀ)) k) i ε} := by
  by_cases hτ1 : τ ≤ 1
  swap
  · exact ⟨0, fun N _ Ω _ _ M K T X hm _ _ => absurd (rd_tau_le_one hm) hτ1⟩
  have hτh : 0 < τ / 2 := by positivity
  obtain ⟨hg0, hgτ⟩ := rd_tauGen hτh (by linarith)
  set w := tauGen (τ / 2) / 4 with hw
  have hw0 : 0 < w := by positivity
  have hwτ : w ≤ τ / 4 := by linarith
  obtain ⟨N₁, h₁⟩ := rigidity_dot_edge_gen (τ / 2) C ε (D + 2) hτh hε
  obtain ⟨N₂, h₂⟩ := rigidity_dot_bulk_gen (τ / 2) w c C ε (D + 2) hτh hw0 hε
  obtain ⟨N₃, h₃⟩ := rd_off_pred (4 * w) (by positivity)
  refine ⟨max (max N₁ N₂) (max N₃ 3), fun N hN Ω _ _ M K T X hm hedge hbulk => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hN
  obtain ⟨⟨hN₁, hN₂⟩, hN₃, hN3⟩ := hN
  have hNpos : 0 < N := by omega
  have hN1 : 0 < N - 1 := by omega
  set σ := specOf (T * Tᵀ) with hσdef
  have hda : DensityAssumptions τ N σ := hm.densityAssumptions hτ
  have hσ := hda.nonneg
  have hmh : IsModelT (τ / 2) C M K N T X := hm.mono hτh (by linarith)
  have hda4 : DensityAssumptions (4 * w) N σ := hda.mono (by positivity) (by linarith)
  refine rd_assemble (lam := fun ω l i => lamDotBandT T (X ω) l i) (w := w) hN3
    (rd_numBands_le hda hNpos) ?_ ?_ ?_ ?_
  · intro l i hl1 hlp hi hiN hγ
    exact rd_cover hda (by omega) hw0 hwτ
      (fun E hE hd => h₃ N hN₃ M σ hda4 E (by linarith) (by linarith)) hl1 hlp hi hiN hγ
  · intro l i hi hγ
    have := (rd_dot_index hσ hN1 (l := l) hi (by linarith)).2
    omega
  · intro k hk1 hk2 hka
    exact h₁ N hN₁ M K T X k hmh (hedge k hk1 hk2 hka)
  · intro m hm1 hm2 hma
    exact h₂ N hN₂ M K T X m hmh (hbulk m hm1 hm2)
      (Or.inr (hedge (2 * m - 1) (by omega) (by omega) hma))

/-! ## The spacing of the classical locations near a regular edge and in the bulk -/

/-- `0 < τ₀(τ)`. -/
private lemma rd_tau0_pos {τ : ℝ} (hτ : 0 < τ) : 0 < edgeTau0 τ := by
  have := edgeTau'_pos hτ
  unfold edgeTau' at this
  linarith

/-- `τ ≤ 1` under (phi_bounded). -/
private lemma rd_da_le_one {τ : ℝ} {K : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ K σ) :
    τ ≤ 1 := by
  have hτ := h.pos
  have h' : τ ≤ τ⁻¹ := h.phi_lower.trans h.phi_upper
  by_contra hc
  push Not at hc
  have : τ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hc
  linarith

/-- The cube comparison closing the two spacing estimates: `N c₁ q K β ≤ 1`,
`ι ≤ 2 N c₂ q³` and `θ ≤ β³ ι N²` contradict `2 c₂ < θ c₁³ K³`. -/
private lemma rd_cube {c₁ c₂ q Kc β θ ι n : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hq : 0 < q)
    (hK : 0 ≤ Kc) (hβ : 0 < β) (hn : 0 < n) (hι : ι ≤ 2 * (n * c₂ * q ^ 3))
    (hθ : θ ≤ β ^ 3 * ι * n ^ 2) (h1 : n * c₁ * q * (Kc * β) ≤ 1)
    (hlt : 2 * c₂ < θ * (c₁ ^ 3 * Kc ^ 3)) : False := by
  have hA : θ ≤ 2 * c₂ * (n * q * β) ^ 3 := by
    calc θ ≤ β ^ 3 * ι * n ^ 2 := hθ
      _ ≤ β ^ 3 * (2 * (n * c₂ * q ^ 3)) * n ^ 2 := by
          have : 0 ≤ β ^ 3 := by positivity
          have : 0 ≤ n ^ 2 := by positivity
          gcongr
      _ = 2 * c₂ * (n * q * β) ^ 3 := by ring
  have hB : (c₁ * Kc * (n * q * β)) ^ 3 ≤ 1 := by
    refine pow_le_one₀ (by positivity) ?_
    calc c₁ * Kc * (n * q * β) = n * c₁ * q * (Kc * β) := by ring
      _ ≤ 1 := h1
  have : θ * (c₁ ^ 3 * Kc ^ 3) ≤ 2 * c₂ := by
    calc θ * (c₁ ^ 3 * Kc ^ 3) ≤ 2 * c₂ * (n * q * β) ^ 3 * (c₁ ^ 3 * Kc ^ 3) :=
          mul_le_mul_of_nonneg_right hA (by positivity)
      _ = 2 * c₂ * (c₁ * Kc * (n * q * β)) ^ 3 := by ring
      _ ≤ 2 * c₂ * 1 := mul_le_mul_of_nonneg_left hB (by positivity)
      _ = 2 * c₂ := mul_one _
  linarith

/-- Below a regular upper edge `a = a_{2k−1}`: classical locations `γ' < γ` with
`n(γ) − n(a) = ι − 1/2`, `n(γ') − n(γ) ≤ 1` and `γ ≥ a − τ₀/2` satisfy `γ − γ' ≤ K β`
whenever `θ ≤ β³ ι N²` and `2 c₂ < θ c₁³ K³` (square-root density). -/
private lemma rd_space_top {τ₁ θ Kc β : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ₁ N σ)
    {k : ℕ} (hk : 1 ≤ k) (hreg : RegularEdge τ₁ N σ (2 * k - 1)) {ι : ℕ} (hι : 1 ≤ ι)
    {γ γ' : ℝ} (hγa : γ < edgeVal N σ (2 * k - 1))
    (hγt : edgeVal N σ (2 * k - 1) - edgeTau0 τ₁ / 2 ≤ γ)
    (hn : nClass N σ γ - nClass N σ (edgeVal N σ (2 * k - 1)) = (ι : ℝ) - 1 / 2)
    (hn' : nClass N σ γ' - nClass N σ γ ≤ 1)
    (hβ : 0 < β) (hθ : θ ≤ β ^ 3 * ι * (N : ℝ) ^ 2) (hK0 : 0 ≤ Kc)
    (hK : 2 * rdC2 τ₁ < θ * (rdC1 τ₁ ^ 3 * Kc ^ 3)) (hKβ : Kc * β ≤ edgeTau0 τ₁ / 2) :
    γ - γ' ≤ Kc * β := by
  obtain ⟨hN0, -, -⟩ := rd_facts hda
  have hσ := hda.nonneg
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hτ₁ := hda.pos
  set a := edgeVal N σ (2 * k - 1) with ha
  have haτ : τ₁ ≤ a := hreg.2.2.1
  have hc1 := rd_C1_pos hτ₁
  have hc2 := rd_C2_pos hτ₁
  have ht0 := rd_tau0_pos hτ₁
  have ht0τ := rd_tau0_le hτ₁ (rd_da_le_one hda)
  have hρ : ∀ x, a - edgeTau0 τ₁ ≤ x → x ≤ a →
      rdC1 τ₁ * √(a - x) ≤ rhoDens N σ x ∧ rhoDens N σ x ≤ rdC2 τ₁ * √(a - x) := by
    intro x h1 h2
    have hx : |x - a| ≤ edgeTau0 τ₁ := by rw [abs_le]; constructor <;> linarith
    have hside : (-1 : ℝ) ^ (2 * k - 1 + 1) * (x - a) ≤ 0 := by
      rw [show 2 * k - 1 + 1 = 2 * k by omega, pow_mul]; norm_num; linarith
    have := rd_rho_edge hda hreg hx hside
    rwa [abs_of_nonpos (by linarith), neg_sub] at this
  set u := a - γ with hu
  have hu0 : 0 < u := by linarith
  set q := √u with hq
  have hq0 : 0 < q := Real.sqrt_pos.2 hu0
  have hqq : q * q = u := Real.mul_self_sqrt hu0.le
  have hup := rd_nClass_sub_le hσ hN0 (x := γ) (y := a) (c₀ := rdC2 τ₁ * q)
    (by linarith) hγa.le (by positivity) fun x hx => by
      have h := (hρ x (by linarith [hx.1]) hx.2.le).2
      have : √(a - x) ≤ q := Real.sqrt_le_sqrt (by linarith [hx.1])
      calc rhoDens N σ x ≤ rdC2 τ₁ * √(a - x) := h
        _ ≤ rdC2 τ₁ * q := mul_le_mul_of_nonneg_left this hc2.le
  rw [hn] at hup
  by_contra hcon
  push Not at hcon
  have hKβ0 : 0 ≤ Kc * β := mul_nonneg hK0 hβ.le
  have hlow := rd_nClass_sub_ge hσ hN0 (x := γ - Kc * β) (y := γ) (c₀ := rdC1 τ₁ * q)
    (by linarith) (by linarith) (by positivity) fun x hx => by
      have h := (hρ x (by linarith [hx.1]) (by linarith [hx.2])).1
      have : q ≤ √(a - x) := Real.sqrt_le_sqrt (by linarith [hx.2])
      calc rdC1 τ₁ * q ≤ rdC1 τ₁ * √(a - x) := mul_le_mul_of_nonneg_left this hc1.le
        _ ≤ rhoDens N σ x := h
  have hmono := rd_nClass_anti hσ hN0 (show γ' ≤ γ - Kc * β by linarith)
  rw [show γ - (γ - Kc * β) = Kc * β by ring] at hlow
  have hι1 : (1 : ℝ) ≤ ι := by exact_mod_cast hι
  have hup' : (ι : ℝ) ≤ 2 * ((N : ℝ) * rdC2 τ₁ * q ^ 3) := by
    have e : (N : ℝ) * (rdC2 τ₁ * q) * (a - γ) = N * rdC2 τ₁ * q ^ 3 := by
      rw [← hu, ← hqq]; ring
    rw [e] at hup
    linarith
  exact rd_cube hc1 hc2 hq0 hK0 hβ hNr hup' hθ (by linarith) hK

/-- Above a regular lower edge `a = a_{2k}`: classical locations `γ' < γ` with
`n(a) − n(γ') = ι − 1/2`, `n(γ') − n(γ) ≤ 1` and `γ ≤ a + τ₀/2` satisfy `γ − γ' ≤ K β`
whenever `θ ≤ β³ ι N²` and `2 c₂ < θ c₁³ K³` (square-root density). -/
private lemma rd_space_bot {τ₁ θ Kc β : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ₁ N σ)
    {k : ℕ} (hreg : RegularEdge τ₁ N σ (2 * k)) {ι : ℕ} (hι : 1 ≤ ι)
    {γ γ' : ℝ} (hγγ : γ' < γ) (hγa : edgeVal N σ (2 * k) < γ')
    (hγt : γ ≤ edgeVal N σ (2 * k) + edgeTau0 τ₁ / 2)
    (hn : nClass N σ (edgeVal N σ (2 * k)) - nClass N σ γ' = (ι : ℝ) - 1 / 2)
    (hn' : nClass N σ γ' - nClass N σ γ ≤ 1)
    (hβ : 0 < β) (hθ : θ ≤ β ^ 3 * ι * (N : ℝ) ^ 2) (hK0 : 0 ≤ Kc)
    (hK : 2 * rdC2 τ₁ < θ * (rdC1 τ₁ ^ 3 * Kc ^ 3)) :
    γ - γ' ≤ Kc * β := by
  obtain ⟨hN0, -, -⟩ := rd_facts hda
  have hσ := hda.nonneg
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hτ₁ := hda.pos
  set a := edgeVal N σ (2 * k) with ha
  have haτ : τ₁ ≤ a := hreg.2.2.1
  have hc1 := rd_C1_pos hτ₁
  have hc2 := rd_C2_pos hτ₁
  have ht0 := rd_tau0_pos hτ₁
  have hρ : ∀ x, a ≤ x → x ≤ a + edgeTau0 τ₁ →
      rdC1 τ₁ * √(x - a) ≤ rhoDens N σ x ∧ rhoDens N σ x ≤ rdC2 τ₁ * √(x - a) := by
    intro x h1 h2
    have hx : |x - a| ≤ edgeTau0 τ₁ := by rw [abs_le]; constructor <;> linarith
    have hside : (-1 : ℝ) ^ (2 * k + 1) * (x - a) ≤ 0 := by
      rw [pow_succ, pow_mul]; norm_num; linarith
    have := rd_rho_edge hda hreg hx hside
    rwa [abs_of_nonneg (by linarith)] at this
  set u := γ' - a with hu
  have hu0 : 0 < u := by linarith
  set q := √u with hq
  have hq0 : 0 < q := Real.sqrt_pos.2 hu0
  have hqq : q * q = u := Real.mul_self_sqrt hu0.le
  have hup := rd_nClass_sub_le hσ hN0 (x := a) (y := γ') (c₀ := rdC2 τ₁ * q)
    (by linarith) hγa.le (by positivity) fun x hx => by
      have h := (hρ x hx.1 (by linarith [hx.2])).2
      have : √(x - a) ≤ q := Real.sqrt_le_sqrt (by linarith [hx.2])
      calc rhoDens N σ x ≤ rdC2 τ₁ * √(x - a) := h
        _ ≤ rdC2 τ₁ * q := mul_le_mul_of_nonneg_left this hc2.le
  rw [hn] at hup
  by_contra hcon
  push Not at hcon
  have hKβ0 : 0 ≤ Kc * β := mul_nonneg hK0 hβ.le
  have hlow := rd_nClass_sub_ge hσ hN0 (x := γ') (y := γ' + Kc * β) (c₀ := rdC1 τ₁ * q)
    (by linarith) (by linarith) (by positivity) fun x hx => by
      have h := (hρ x (by linarith [hx.1]) (by linarith [hx.2])).1
      have : q ≤ √(x - a) := Real.sqrt_le_sqrt (by linarith [hx.1])
      calc rdC1 τ₁ * q ≤ rdC1 τ₁ * √(x - a) := mul_le_mul_of_nonneg_left this hc1.le
        _ ≤ rhoDens N σ x := h
  have hmono := rd_nClass_anti hσ hN0 (show γ' + Kc * β ≤ γ by linarith)
  rw [show γ' + Kc * β - γ' = Kc * β by ring] at hlow
  have hι1 : (1 : ℝ) ≤ ι := by exact_mod_cast hι
  have hup' : (ι : ℝ) ≤ 2 * ((N : ℝ) * rdC2 τ₁ * q ^ 3) := by
    have e : (N : ℝ) * (rdC2 τ₁ * q) * (γ' - a) = N * rdC2 τ₁ * q ^ 3 := by
      rw [← hu, ← hqq]; ring
    rw [e] at hup
    linarith
  exact rd_cube hc1 hc2 hq0 hK0 hβ hNr hup' hθ (by linarith) hK

/-- In the bulk: classical locations `γ' < γ` with `n(γ') − n(γ) ≤ 1` and density `≥ c₀` on
`[γ − t, γ]`, `N c₀ t > 1`, satisfy `γ − γ' ≤ t`. -/
private lemma rd_space_bulk {c₀ t : ℝ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    {γ γ' : ℝ} (hc0 : 0 < c₀) (ht : 0 < t) (hγt : 0 < γ - t)
    (hρ : ∀ x ∈ Set.Icc (γ - t) γ, c₀ ≤ rhoDens N σ x)
    (hn' : nClass N σ γ' - nClass N σ γ ≤ 1) (hNt : 1 < N * c₀ * t) : γ - γ' ≤ t := by
  by_contra hcon
  push Not at hcon
  have hlow := rd_nClass_sub_ge hσ hN (x := γ - t) (y := γ) (c₀ := c₀) hγt (by linarith) hc0.le
    fun x hx => hρ x ⟨hx.1, hx.2.le⟩
  have hmono := rd_nClass_anti hσ hN (show γ' ≤ γ - t by linarith)
  rw [show γ - (γ - t) = t by ring] at hlow
  linarith

/-- Above a regular lower edge `a = a_{2k}` of `K` samples: a classical location `γ ≥ a` with
`n(a) − n(γ) ≤ 1/2` lies below `a + t` whenever `K c₁ √(t/2) (t/2) > 1/2`, `t ≤ τ₀`. -/
private lemma rd_loc_dn {τ₁ t : ℝ} {K : ℕ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ₁ K σ)
    {k : ℕ} (hreg : RegularEdge τ₁ K σ (2 * k)) {γ : ℝ}
    (hn : nClass K σ (edgeVal K σ (2 * k)) - nClass K σ γ ≤ 1 / 2) (ht0 : 0 < t)
    (htτ : t ≤ edgeTau0 τ₁) (hmass : 1 / 2 < K * rdC1 τ₁ * √(t / 2) * (t / 2)) :
    γ - edgeVal K σ (2 * k) < t := by
  obtain ⟨hK0, -, -⟩ := rd_facts hda
  have hσ := hda.nonneg
  have hτ₁ := hda.pos
  set a := edgeVal K σ (2 * k) with ha
  have haτ : τ₁ ≤ a := hreg.2.2.1
  have hc1 := rd_C1_pos hτ₁
  by_contra hcon
  push Not at hcon
  have hlow := rd_nClass_sub_ge hσ hK0 (x := a + t / 2) (y := a + t)
    (c₀ := rdC1 τ₁ * √(t / 2)) (by linarith) (by linarith) (by positivity) fun x hx => by
      have hx' : |x - a| ≤ edgeTau0 τ₁ := by
        rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
      have hside : (-1 : ℝ) ^ (2 * k + 1) * (x - a) ≤ 0 := by
        rw [pow_succ, pow_mul]; norm_num; linarith [hx.1]
      have h := (rd_rho_edge hda hreg hx' hside).1
      rw [abs_of_nonneg (by linarith [hx.1])] at h
      have : √(t / 2) ≤ √(x - a) := Real.sqrt_le_sqrt (by linarith [hx.1])
      calc rdC1 τ₁ * √(t / 2) ≤ rdC1 τ₁ * √(x - a) := mul_le_mul_of_nonneg_left this hc1.le
        _ ≤ rhoDens K σ x := h
  have h1 := rd_nClass_anti hσ hK0 (show a ≤ a + t / 2 by linarith)
  have h2 := rd_nClass_anti hσ hK0 (show a + t ≤ γ by linarith)
  rw [show a + t - (a + t / 2) = t / 2 by ring] at hlow
  have e : (K : ℝ) * (rdC1 τ₁ * √(t / 2)) * (t / 2) = K * rdC1 τ₁ * √(t / 2) * (t / 2) := by ring
  linarith

/-! ## Theorem 3.12 at `N` at one index, from the window-local events -/

/-- `rigBound N N_k i ε = N^ε β` with `β = (i ∧ (N_k + 1 − i))^{−1/3} N^{−2/3}`. -/
private lemma rd_rigBound_eq (N Nk i : ℕ) (ε : ℝ) :
    rigBound N Nk i ε = (N : ℝ) ^ ε *
      (((min i (Nk + 1 - i) : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ))) := by
  unfold rigBound; ring

/-- `rigBound N N_k (i + 1) ε ≤ 2 rigBound N N_k i ε` for `1 ≤ i < N_k`. -/
private lemma rd_rigBound_succ {N Nk i : ℕ} {ε : ℝ} (hi : 1 ≤ i) (hiN : i + 1 ≤ Nk) :
    rigBound N Nk (i + 1) ε ≤ 2 * rigBound N Nk i ε := by
  unfold rigBound
  set m := min i (Nk + 1 - i) with hm
  set m' := min (i + 1) (Nk + 1 - (i + 1)) with hm'
  have hm1 : 1 ≤ m := le_min hi (by omega)
  have hm'1 : 1 ≤ m' := le_min (by omega) (by omega)
  have h2 : m ≤ 2 * m' := by omega
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm1
  have hm'r : (0 : ℝ) < m' := by exact_mod_cast hm'1
  have h2r : (m : ℝ) ≤ 2 * m' := by exact_mod_cast h2
  have hr := Real.rpow_le_rpow_of_nonpos hmr h2r (show -(1 / 3 : ℝ) ≤ 0 by norm_num)
  rw [Real.mul_rpow (by norm_num) hm'r.le] at hr
  have h2c : (2 : ℝ) ^ (-(1 / 3 : ℝ)) ≥ 1 / 2 := by
    have : (2 : ℝ) ^ (-(1 / 3 : ℝ)) ≥ (2 : ℝ) ^ (-(1 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    rw [Real.rpow_neg_one] at this
    linarith
  have hpos : 0 ≤ (m' : ℝ) ^ (-(1 / 3 : ℝ)) := by positivity
  have key : (m' : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 2 * (m : ℝ) ^ (-(1 / 3 : ℝ)) := by nlinarith
  have h0 : (0 : ℝ) ≤ (N : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have h0' : (0 : ℝ) ≤ (N : ℝ) ^ (-(2 / 3 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  calc (N : ℝ) ^ ε * (m' : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ))
      ≤ (N : ℝ) ^ ε * (2 * (m : ℝ) ^ (-(1 / 3 : ℝ))) * (N : ℝ) ^ (-(2 / 3 : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left key h0) h0'
    _ = 2 * ((N : ℝ) ^ ε * (m : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ))) := by ring

/-- (rigidity) at `N` at one index with `γ_{k,i} ≥ τ/2 + τ_r`, on the events of Theorems 3.14 (iii)
and 3.15 (iii) at the edges `a_l ≥ τ/2` (window `τ_r`) and in the bulk of the bands with
`a_{2m−1} ≥ τ/2`. -/
private lemma rd_rigN {τ τr ε' : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    {Xm : Matrix (Fin M) (Fin N) ℝ} (hda : DensityAssumptions τ N (specOf Sig)) (hτr : 0 < τr)
    (hE1 : ∀ l, 1 ≤ l → l ≤ 2 * numBands N (specOf Sig) → τ / 2 ≤ edgeVal N (specOf Sig) l →
      ∀ i, 1 ≤ i → i ≤ bandNat N (specOf Sig) ((l + 1) / 2) →
      gammaBand N (specOf Sig) ((l + 1) / 2) i ∈
        Set.Icc (edgeVal N (specOf Sig) l - τr) (edgeVal N (specOf Sig) l + τr) →
      |lamBand Sig Xm ((l + 1) / 2) i - gammaBand N (specOf Sig) ((l + 1) / 2) i| ≤
        rigBound N (bandNat N (specOf Sig) ((l + 1) / 2)) i ε')
    (hE2 : ∀ m, 1 ≤ m → m ≤ numBands N (specOf Sig) → τ / 2 ≤ edgeVal N (specOf Sig) (2 * m - 1) →
      ∀ i, 1 ≤ i → i ≤ bandNat N (specOf Sig) m →
      gammaBand N (specOf Sig) m i ∈ Set.Icc (edgeVal N (specOf Sig) (2 * m) + τr)
        (edgeVal N (specOf Sig) (2 * m - 1) - τr) →
      |lamBand Sig Xm m i - gammaBand N (specOf Sig) m i| ≤ (N : ℝ) ^ ε' * (N : ℝ)⁻¹)
    {k i : ℕ} (hk1 : 1 ≤ k) (hkp : k ≤ numBands N (specOf Sig)) (hi : 1 ≤ i)
    (hiN : i ≤ bandNat N (specOf Sig) k) (hγ : τ / 2 + τr ≤ gammaBand N (specOf Sig) k i) :
    |lamBand Sig Xm k i - gammaBand N (specOf Sig) k i| ≤
      rigBound N (bandNat N (specOf Sig) k) i ε' := by
  have hτ := hda.pos
  obtain ⟨hN0, -, -⟩ := rd_facts hda
  have hσ := hda.nonneg
  have hγ0 : 0 < gammaBand N (specOf Sig) k i := by linarith
  have hmem := rd_band_mem hda hN0 hk1 hkp hi hiN hγ0
  have hjN := rd_index_le hσ hN0 (j := cumCount N (specOf Sig) (k - 1) + i) hγ0
  have hmin1 : 1 ≤ min i (bandNat N (specOf Sig) k + 1 - i) := le_min hi (by omega)
  have hminN : min i (bandNat N (specOf Sig) k + 1 - i) ≤ N := (min_le_left _ _).trans (by omega)
  by_cases hA : |gammaBand N (specOf Sig) k i - edgeVal N (specOf Sig) (2 * k - 1)| ≤ τr
  · have hkk : (2 * k - 1 + 1) / 2 = k := by omega
    have h := abs_le.1 hA
    have := hE1 (2 * k - 1) (by omega) (by omega) (by linarith [hmem.2]) i hi
      (by rw [hkk]; exact hiN) (by rw [hkk]; exact ⟨by linarith [h.1], by linarith [h.2]⟩)
    rwa [hkk] at this
  by_cases hB : τ / 2 ≤ edgeVal N (specOf Sig) (2 * k) ∧
      |gammaBand N (specOf Sig) k i - edgeVal N (specOf Sig) (2 * k)| ≤ τr
  · have hkk : (2 * k + 1) / 2 = k := by omega
    have h := abs_le.1 hB.2
    have := hE1 (2 * k) (by omega) (by omega) hB.1 i hi (by rw [hkk]; exact hiN)
      (by rw [hkk]; exact ⟨by linarith [h.1], by linarith [h.2]⟩)
    rwa [hkk] at this
  · have hup : gammaBand N (specOf Sig) k i ≤ edgeVal N (specOf Sig) (2 * k - 1) - τr := by
      rw [not_le, abs_sub_comm, abs_of_nonneg (by linarith [hmem.2])] at hA
      linarith
    have hlow : edgeVal N (specOf Sig) (2 * k) + τr ≤ gammaBand N (specOf Sig) k i := by
      by_cases h2 : τ / 2 ≤ edgeVal N (specOf Sig) (2 * k)
      · have hB' : ¬ |gammaBand N (specOf Sig) k i - edgeVal N (specOf Sig) (2 * k)| ≤ τr :=
          fun h => hB ⟨h2, h⟩
        rw [not_le, abs_of_nonneg (by linarith [hmem.1])] at hB'
        linarith
      · linarith
    exact (hE2 k hk1 hkp (by linarith [hmem.2]) i hi hiN ⟨hlow, hup⟩).trans
      (rd_bulk_le_rigBound hmin1 hminN)

set_option maxHeartbeats 4000000 in
-- many linear-arithmetic steps over a large context
/-- Theorem 11.3 with the classical quantities of `N` at one index `(k, i)` with `i < N_k`,
`γ_{k,i} ≥ τ`: interlacing `λ_{j+1} ≤ λ_j(π̄ B π̄) ≤ λ_j`, (rigidity) at `N` for `j` and `j + 1`,
and the spacing `γ_j − γ_{j+1} ≤ K (i ∧ (N_k + 1 − i))^{−1/3} N^{−2/3}`. -/
private lemma rd_dotN_A {τ τr ε ε' c₀ Kt Kb : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    {Xm : Matrix (Fin M) (Fin N) ℝ} (hda : DensityAssumptions τ N (specOf Sig))
    (hσp : ∀ j, 0 < specOf Sig j) (hSig : Sig.IsHermitian) (hN2 : 2 ≤ N)
    (hD6 : ∀ l, 1 ≤ l → l ≤ 2 * numBands N (specOf Sig) → τ / 2 ≤ edgeVal N (specOf Sig) l →
      RegularEdge (τ / 2) N (specOf Sig) l)
    (hc0 : 0 < c₀) (hτr0 : 0 < τr)
    (hρ0 : ∀ m, 1 ≤ m → m ≤ numBands N (specOf Sig) → ∀ E ∈ Set.Icc
      (edgeVal N (specOf Sig) (2 * m) + edgeTau0 (τ / 2) / 4)
      (edgeVal N (specOf Sig) (2 * m - 1) - edgeTau0 (τ / 2) / 4), c₀ ≤ rhoDens N (specOf Sig) E)
    (hrig : ∀ k i, 1 ≤ k → k ≤ numBands N (specOf Sig) → 1 ≤ i →
      i ≤ bandNat N (specOf Sig) k → τ / 2 + τr ≤ gammaBand N (specOf Sig) k i →
      |lamBand Sig Xm k i - gammaBand N (specOf Sig) k i| ≤
        rigBound N (bandNat N (specOf Sig) k) i ε')
    (hKt : 0 ≤ Kt) (hKt' : 2 * rdC2 (τ / 2) < 1 * (rdC1 (τ / 2) ^ 3 * Kt ^ 3))
    (hKb : 0 ≤ Kb) (hKb' : 2 * rdC2 (τ / 2) < 1 / 2 * (rdC1 (τ / 2) ^ 3 * Kb ^ 3))
    (f1 : Kt * (N : ℝ) ^ (-(2 / 3 : ℝ)) ≤ edgeTau0 (τ / 2) / 2)
    (f3 : 2 / (N * c₀) ≤ edgeTau0 (τ / 2) / 4)
    (f4 : (Kt + Kb + 2 / c₀) * (N : ℝ) ^ (-(2 / 3 : ℝ)) ≤ τ / 2 - τr)
    (f5 : 2 * (N : ℝ) ^ ε' * (N : ℝ) ^ (-(2 / 3 : ℝ)) < τ / 2)
    (f6 : 2 * (N : ℝ) ^ ε' + (Kt + Kb + 2 / c₀) + 2 * (2 * τ⁻¹ * (1 + τ⁻¹) + 1) ≤ (N : ℝ) ^ ε)
    {k i : ℕ} (hk1 : 1 ≤ k) (hkp : k ≤ numBands N (specOf Sig)) (hi : 1 ≤ i)
    (hiN1 : i + 1 ≤ bandNat N (specOf Sig) k) (hγ : τ ≤ gammaBand N (specOf Sig) k i) :
    |sortedEig (QdotN Sig Xm) (cumCount N (specOf Sig) (k - 1) + i) -
      gammaBand N (specOf Sig) k i| ≤ rigBound N (bandNat N (specOf Sig) k) i ε := by
  have hτ := hda.pos
  have hτ1 := rd_da_le_one hda
  set σ := specOf Sig with hσdef
  have hσ := hda.nonneg
  obtain ⟨hN0, -, -⟩ := rd_facts hda
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have hτh : 0 < τ / 2 := by positivity
  have hda2 : DensityAssumptions (τ / 2) N σ := hda.mono hτh (by linarith)
  set τ₀ := edgeTau0 (τ / 2) with hτ₀
  have ht0 : 0 < τ₀ := rd_tau0_pos hτh
  have ht0τ : τ₀ ≤ τ / 2 / 16 := rd_tau0_le hτh (by linarith)
  set Ca := 2 * τ⁻¹ * (1 + τ⁻¹) with hCa
  -- the indices `j = d_{k−1} + i` and `j + 1`
  obtain ⟨-, -, hcs⟩ := cumCount_spec hda hk1 hkp
  have hcm := (rd_cum hda hσp hk1 hkp).1
  set j := cumCount N σ (k - 1) + i with hj
  have hj1 : 1 ≤ j := by omega
  have hjN : j + 1 ≤ min M N := by omega
  obtain ⟨hγ0, hnγ⟩ := nClass_gammaLoc hda hσp hj1 (by omega)
  obtain ⟨hγ'0, hnγ'⟩ := nClass_gammaLoc hda hσp (show 1 ≤ j + 1 by omega) hjN
  have hmem := gammaBand_mem hda hσp hk1 hkp hi (by omega)
  have hmem' := gammaBand_mem hda hσp hk1 hkp (show 1 ≤ i + 1 by omega) hiN1
  have hgb : gammaBand N σ k i = gammaLoc N σ j := rfl
  have hgb' : gammaBand N σ k (i + 1) = gammaLoc N σ (j + 1) := rfl
  rw [hgb] at hγ hmem ⊢
  rw [hgb'] at hmem'
  set γ := gammaLoc N σ j with hγdef
  set γ' := gammaLoc N σ (j + 1) with hγ'def
  push_cast at hnγ'
  have hγγ : γ' < γ := by
    by_contra hc
    push Not at hc
    have := rd_nClass_anti hσ hN0 hc
    linarith
  have hn1 : nClass N σ γ' - nClass N σ γ ≤ 1 := by rw [hnγ, hnγ']; linarith
  -- the scale `β = (i ∧ (N_k + 1 − i))^{−1/3} N^{−2/3}`
  set m := min i (bandNat N σ k + 1 - i) with hm
  have hm1 : 1 ≤ m := le_min hi (by omega)
  have hmN : m ≤ N := (min_le_left _ _).trans (by omega)
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm1
  obtain ⟨hβ0, hβ3⟩ := rd_beta hmr hNpos
  obtain ⟨-, hβle, hβge⟩ := rd_beta_bounds hm1 hmN
  set β := (m : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) with hβdef
  have hx0 : 0 < (N : ℝ) ^ (-(2 / 3 : ℝ)) := by positivity
  set Ks := Kt + Kb + 2 / c₀ with hKs
  have hc0' : 0 ≤ 2 / c₀ := by positivity
  have hKs0 : 0 ≤ Ks := by positivity
  -- the spacing `γ_j − γ_{j+1} ≤ K_s β`
  have hsp : γ - γ' ≤ Ks * β := by
    have hna := (nClass_edgeVal hda hk1 hkp).1
    by_cases htop : edgeVal N σ (2 * k - 1) - τ₀ / 2 ≤ γ
    · have hreg := hD6 (2 * k - 1) (by omega) (by omega) (by linarith [hmem.2])
      have hθ : (1 : ℝ) ≤ β ^ 3 * (i : ℝ) * (N : ℝ) ^ 2 := by
        have hmi : (m : ℝ) ≤ i := by exact_mod_cast (min_le_left _ _)
        have : β ^ 3 * (m : ℝ) * (N : ℝ) ^ 2 ≤ β ^ 3 * (i : ℝ) * (N : ℝ) ^ 2 := by
          have : 0 ≤ β ^ 3 := by positivity
          gcongr
        linarith
      have h := rd_space_top hda2 hk1 hreg hi hmem.2 htop
        (by rw [hnγ, hna, hj]; push_cast; ring) hn1 hβ0 hθ hKt hKt'
        (le_trans (mul_le_mul_of_nonneg_left hβle hKt) f1)
      have : Kt * β ≤ Ks * β := mul_le_mul_of_nonneg_right (by linarith) hβ0.le
      linarith
    by_cases hbot : τ / 2 ≤ edgeVal N σ (2 * k) ∧ γ ≤ edgeVal N σ (2 * k) + τ₀ / 2
    · have hreg := hD6 (2 * k) (by omega) (by omega) hbot.1
      have hnb := (nClass_edgeVal hda hk1 hkp).2 (by linarith [hbot.1])
      have hι : 1 ≤ bandNat N σ k - i := by omega
      have hθ : (1 / 2 : ℝ) ≤ β ^ 3 * ((bandNat N σ k - i : ℕ) : ℝ) * (N : ℝ) ^ 2 := by
        have hm2 : (m : ℝ) ≤ 2 * ((bandNat N σ k - i : ℕ) : ℝ) := by
          have : m ≤ 2 * (bandNat N σ k - i) := (min_le_right _ _).trans (by omega)
          exact_mod_cast this
        have : β ^ 3 * (m : ℝ) * (N : ℝ) ^ 2 ≤
            β ^ 3 * (2 * ((bandNat N σ k - i : ℕ) : ℝ)) * (N : ℝ) ^ 2 := by
          have : 0 ≤ β ^ 3 := by positivity
          gcongr
        nlinarith
      have hcast : ((bandNat N σ k - i : ℕ) : ℝ) = (bandNat N σ k : ℝ) - i := by
        rw [Nat.cast_sub (by omega)]
      have hcs' : (cumCount N σ k : ℝ) = cumCount N σ (k - 1) + bandNat N σ k := by
        rw [← hcs]; push_cast; ring
      have h := rd_space_bot hda2 hreg hι hγγ hmem'.1 hbot.2
        (by rw [hnb, hnγ', hcast, hcs', hj]; push_cast; ring) hn1 hβ0 hθ hKb hKb'
      have : Kb * β ≤ Ks * β := mul_le_mul_of_nonneg_right (by linarith) hβ0.le
      linarith
    · -- in the bulk of the band `k`
      push Not at htop
      have hlo : edgeVal N σ (2 * k) + τ₀ / 2 ≤ γ := by
        by_cases h2 : τ / 2 ≤ edgeVal N σ (2 * k)
        · have := hbot
          push Not at this
          exact (this h2).le
        · push Not at h2; linarith
      set t := 2 / (N * c₀) with ht
      have htp : 0 < t := by positivity
      have h := rd_space_bulk hσ hN0 (γ' := γ') hc0 htp (by linarith [hmem.1, (rd_edge_mem hda hN0
          (k := 2 * k) (by omega) (by omega)).1])
        (fun x hx => hρ0 k hk1 hkp x ⟨by linarith [hx.1], by linarith [hx.2]⟩) hn1
        (by rw [ht]; field_simp; norm_num)
      have e : t = 2 / c₀ * (N : ℝ)⁻¹ := by rw [ht]; field_simp
      have : 2 / c₀ * (N : ℝ)⁻¹ ≤ 2 / c₀ * β := mul_le_mul_of_nonneg_left hβge hc0'
      have : 2 / c₀ * β ≤ Ks * β := mul_le_mul_of_nonneg_right (by linarith) hβ0.le
      linarith
  have hKsβ : Ks * β ≤ Ks * (N : ℝ) ^ (-(2 / 3 : ℝ)) := mul_le_mul_of_nonneg_left hβle hKs0
  have hτr : τr ≤ τ / 2 := by nlinarith
  have hγ'τ : τ / 2 + τr ≤ γ' := by linarith
  -- (rigidity) at `N` for `j` and `j + 1`
  have hr1 := hrig k i hk1 hkp hi (by omega) (by rw [hgb]; linarith)
  have hr2 := hrig k (i + 1) hk1 hkp (by omega) hiN1 (by rw [hgb']; exact hγ'τ)
  rw [hgb] at hr1
  rw [hgb'] at hr2
  have hl1 : lamBand Sig Xm k i = sortedEig (QN Sig Xm) j := rfl
  have hl2 : lamBand Sig Xm k (i + 1) = sortedEig (QN Sig Xm) (j + 1) := rfl
  rw [hl1] at hr1
  rw [hl2] at hr2
  have hR : rigBound N (bandNat N σ k) i ε' = (N : ℝ) ^ ε' * β := rd_rigBound_eq _ _ _ _
  have hR' := rd_rigBound_succ (N := N) (ε := ε') hi hiN1
  rw [hR] at hr1 hR'
  rw [abs_le] at hr1 hr2
  have hNε' : 0 ≤ (N : ℝ) ^ ε' := by positivity
  have hRβ : (N : ℝ) ^ ε' * β ≤ (N : ℝ) ^ ε' * (N : ℝ) ^ (-(2 / 3 : ℝ)) :=
    mul_le_mul_of_nonneg_left hβle hNε'
  -- interlacing and the factor `N/(N − 1)`
  set L := sortedEig (QN Sig Xm) (j + 1) with hL
  set U := sortedEig (QN Sig Xm) j with hU
  have hL0 : 0 < L := by linarith
  have hjN' : j + 1 ≤ N := hjN.trans (min_le_right _ _)
  have hLj := rd_interlace_lo hSig Xm hj1 hjN'
  obtain ⟨hb1, hb2⟩ := rd_dot_bounds hSig Xm hN2 hj1 (by omega) hL0 hLj le_rfl
  have hc : 0 < (N : ℝ) / (N - 1) := div_pos (by linarith) (by linarith)
  have hq : sortedEig (QdotN Sig Xm) j = (N : ℝ) / (N - 1) * sortedEig (QN Sig (Xdot Xm)) j := by
    unfold QdotN
    exact rd_sortedEig_smul (XSX_isHermitian hSig (Xdot Xm)) hc hj1 (by omega)
  rw [hq]
  have hCa0 : 0 ≤ Ca := by rw [hCa]; positivity
  have hUle : U ≤ Ca + 1 := by
    have := (rd_edge_mem hda hN0 (k := 2 * k - 1) (by omega) (by omega)).2
    linarith [hmem.2]
  have hU0 : 0 ≤ U := by linarith
  have hdiv := rd_div_pred hU0 hN2
  have hdivβ : 2 * U * (N : ℝ)⁻¹ ≤ 2 * (Ca + 1) * β := by
    have h1 : 2 * U * (N : ℝ)⁻¹ ≤ 2 * (Ca + 1) * (N : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h2 : 2 * (Ca + 1) * (N : ℝ)⁻¹ ≤ 2 * (Ca + 1) * β :=
      mul_le_mul_of_nonneg_left hβge (by positivity)
    linarith
  rw [rd_rigBound_eq]
  have hfin : (2 * (N : ℝ) ^ ε' + Ks + 2 * (Ca + 1)) * β ≤ (N : ℝ) ^ ε * β :=
    mul_le_mul_of_nonneg_right f6 hβ0.le
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

set_option maxHeartbeats 4000000 in
-- many linear-arithmetic steps over a large context
/-- Theorem 11.3 with the classical quantities of `N` at the last index `i = N_k` of a band
`k < p` (or `k = p` when `M < N`) with `γ_{k,N_k} ≥ τ`: the edge `a_{2k}` is regular, the counts
`ḋ_k = d_k` agree (a point of the gap below the band), and the window-local statement at the
edge `a_{2k}` applies at the last index `Ṅ_k` of the band `k` of `N − 1`. -/
private lemma rd_dotN_B {τ ε ε' w C₁ Ke Ke' c₈ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    {Xm : Matrix (Fin M) (Fin N) ℝ} (hda : DensityAssumptions τ N (specOf Sig))
    (hσp : ∀ j, 0 < specOf Sig j) (hN3 : 3 ≤ N)
    (hD6 : ∀ l, 1 ≤ l → l ≤ 2 * numBands N (specOf Sig) → τ / 2 ≤ edgeVal N (specOf Sig) l →
      RegularEdge (τ / 2) N (specOf Sig) l)
    (hc8 : 0 < c₈)
    (hρ8 : ∀ m, 1 ≤ m → m ≤ numBands N (specOf Sig) → ∀ E ∈ Set.Icc
      (edgeVal N (specOf Sig) (2 * m) + τ / 8) (edgeVal N (specOf Sig) (2 * m - 1) - τ / 8),
      c₈ ≤ rhoDens N (specOf Sig) E)
    (hpred : ∀ l, 1 ≤ l → l ≤ 2 * numBands N (specOf Sig) → τ / 2 ≤ edgeVal N (specOf Sig) l →
      |edgeVal (N - 1) (specOf Sig) l - edgeVal N (specOf Sig) l| ≤ C₁ / N ∧
        RegularEdge (τ / 4) (N - 1) (specOf Sig) l)
    (hgap : ∀ E : ℝ, τ / 4 ≤ E → τ / 8 ≤ Metric.infDist E (varrho N (specOf Sig)).support →
      (∃ x ∈ (varrho N (specOf Sig)).support, x < E) →
      nClass (N - 1) (specOf Sig) E = nClass N (specOf Sig) E)
    (hdot : ∀ m, 1 ≤ m → m ≤ numBands N (specOf Sig) → τ / 2 ≤ edgeVal N (specOf Sig) (2 * m) →
      ∀ l, 1 ≤ l → l ≤ numBands (N - 1) (specOf Sig) →
      ∀ i, 1 ≤ i → i ≤ bandNat (N - 1) (specOf Sig) l →
      gammaBand (N - 1) (specOf Sig) l i ∈ Set.Icc (edgeVal N (specOf Sig) (2 * m) - w)
        (edgeVal N (specOf Sig) (2 * m) + w) →
      |lamDotBand Sig Xm l i - gammaBand (N - 1) (specOf Sig) l i| ≤
        rigBound N (bandNat (N - 1) (specOf Sig) l) i ε')
    (hKe : 0 < Ke) (hKe' : 0 < Ke')
    (g1 : 1 / 2 < N * c₈ * (τ / 8)) (g2 : |C₁| / N < τ / 8)
    (g3 : 1 / 2 < N * rdC1 (τ / 2) * √(Ke * (N : ℝ) ^ (-(2 / 3 : ℝ)) / 2) *
      (Ke * (N : ℝ) ^ (-(2 / 3 : ℝ)) / 2))
    (g4 : Ke * (N : ℝ) ^ (-(2 / 3 : ℝ)) ≤ edgeTau0 (τ / 2))
    (g5 : 1 / 2 < ((N - 1 : ℕ) : ℝ) * rdC1 (τ / 4) * √(Ke' * (N : ℝ) ^ (-(2 / 3 : ℝ)) / 2) *
      (Ke' * (N : ℝ) ^ (-(2 / 3 : ℝ)) / 2))
    (g6 : Ke' * (N : ℝ) ^ (-(2 / 3 : ℝ)) ≤ edgeTau0 (τ / 4))
    (g7 : |C₁| / N + Ke' * (N : ℝ) ^ (-(2 / 3 : ℝ)) ≤ w)
    (g8 : (N : ℝ) ^ ε' + Ke + Ke' + |C₁| ≤ (N : ℝ) ^ ε)
    {k : ℕ} (hk1 : 1 ≤ k) (hkp : k ≤ numBands N (specOf Sig))
    (hγ : τ ≤ gammaBand N (specOf Sig) k (bandNat N (specOf Sig) k))
    (hex : k < numBands N (specOf Sig) ∨ M < N) :
    |sortedEig (QdotN Sig Xm) (cumCount N (specOf Sig) (k - 1) + bandNat N (specOf Sig) k) -
      gammaBand N (specOf Sig) k (bandNat N (specOf Sig) k)| ≤
        rigBound N (bandNat N (specOf Sig) k) (bandNat N (specOf Sig) k) ε := by
  have hτ := hda.pos
  have hτ1 := rd_da_le_one hda
  set σ := specOf Sig with hσdef
  have hσ := hda.nonneg
  obtain ⟨hN0, -, -⟩ := rd_facts hda
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hNpos : (0 : ℝ) < N := by linarith
  have hN2 : 2 ≤ N := by omega
  have hN10 : 0 < N - 1 := by omega
  have hτh : 0 < τ / 2 := by positivity
  have hda2 : DensityAssumptions (τ / 2) N σ := hda.mono hτh (by linarith)
  have hda1 : DensityAssumptions (τ / 2) (N - 1) σ := rd_da_pred hda hN2
  have hda14 : DensityAssumptions (τ / 4) (N - 1) σ := hda1.mono (by positivity) (by linarith)
  set x := (N : ℝ) ^ (-(2 / 3 : ℝ)) with hx
  have hx0 : 0 < x := by positivity
  have hC1 : |C₁| / N ≤ |C₁| * x := by
    rw [div_eq_mul_inv]
    have : (N : ℝ)⁻¹ ≤ x := by
      rw [hx, ← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
  have hC1N : C₁ / N ≤ |C₁| / N := div_le_div_of_nonneg_right (le_abs_self _) hNpos.le
  -- the last index `j = d_k` of the band `k`
  have hNk := rd_bandNat_pos hda hN0 hk1 hkp
  obtain ⟨-, -, hcs⟩ := cumCount_spec hda hk1 hkp
  have hcm := (rd_cum hda hσp hk1 hkp).1
  set Nk := bandNat N σ k with hNkdef
  set j := cumCount N σ (k - 1) + Nk with hj
  have hjk : j = cumCount N σ k := hcs
  have hj1 : 1 ≤ j := by omega
  obtain ⟨hγ0, hnγ⟩ := nClass_gammaLoc hda hσp hj1 (by omega)
  have hmem := gammaBand_mem hda hσp hk1 hkp hNk le_rfl
  have hgb : gammaBand N σ k Nk = gammaLoc N σ j := rfl
  rw [hgb] at hγ hmem ⊢
  set γ := gammaLoc N σ j with hγdef
  -- the lower edge is at least `τ/2`
  have ha2 : τ / 2 ≤ edgeVal N σ (2 * k) := by
    by_contra hlt
    push Not at hlt
    have hlow := rd_nClass_sub_ge hσ hN0 (x := 3 * τ / 4) (y := 7 * τ / 8) (c₀ := c₈)
      (by positivity) (by linarith) hc8.le fun E hE => hρ8 k hk1 hkp E
        ⟨by linarith [hE.1], by linarith [hE.2, hmem.2]⟩
    have h1 := rd_n_le_cum hda hk1 hkp (x := 3 * τ / 4) (by linarith)
    have h2 := rd_nClass_anti hσ hN0 (show 7 * τ / 8 ≤ γ by linarith)
    rw [hnγ, hjk] at h2
    have e : 7 * τ / 8 - 3 * τ / 4 = τ / 8 := by ring
    rw [e] at hlow
    linarith
  set a := edgeVal N σ (2 * k) with ha
  have hreg := hD6 (2 * k) (by omega) (by omega) ha2
  obtain ⟨hadot, hreg'⟩ := hpred (2 * k) (by omega) (by omega) ha2
  set ad := edgeVal (N - 1) σ (2 * k) with hadef
  have hada := abs_le.1 hadot
  have hkp' : k ≤ numBands (N - 1) σ := by have := hreg'.2.1; omega
  -- the counts below the band agree: `ḋ_k = d_k`
  set E := a - τ / 8 with hE
  have hE0 : 0 < E := by linarith
  have hnE : nClass N σ E = cumCount N σ k :=
    rd_n_gap_dn hda hσp hk1 hkp hE0 (by linarith) fun hlt => by
      have := rd_sep_dn hda2 hk1 hlt hreg
      linarith
  have hgE : nClass (N - 1) σ E = nClass N σ E := by
    refine hgap E (by linarith) ?_ ?_
    · refine rd_dist hda (by positivity) (by linarith) (rd_supp_nonempty hda hN0)
        fun l hl1 hl2 => ?_
      by_cases hlk : l ≤ k
      · left
        have := rd_anti hda (i := 2 * l) (j := 2 * k) (by omega) (by omega) (by omega)
        linarith
      · right
        have hk' : k < numBands N σ := by omega
        have h1 := rd_anti hda (i := 2 * k + 1) (j := 2 * l - 1) (by omega) (by omega) (by omega)
        have h2 := rd_sep_dn hda2 hk1 hk' hreg
        linarith
    · rcases hex with hk' | hMN
      · have hlt := edgeVal_band_lt N σ hσ hN0 (rd_posVals_nonempty hda) (k := k + 1) (by omega) hk'
        have h0 := (rd_edge_mem hda hN0 (k := 2 * (k + 1)) (by omega) (by omega)).1
        refine ⟨edgeVal N σ (2 * (k + 1) - 1), rd_mem_supp hda hN0 (k := k + 1) (by omega) hk'
          (by linarith) hlt.le le_rfl, ?_⟩
        have h2 := rd_sep_dn hda2 hk1 hk' hreg
        rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
        linarith
      · exact ⟨0, rd_zero_mem_supp hda hσp hMN, hE0⟩
  have hnE1 : nClass (N - 1) σ E = cumCount (N - 1) σ k :=
    rd_n_gap_dn hda1 hσp hk1 hkp' hE0 (by linarith) fun hlt => by
      have := rd_sep_dn hda14 hk1 hlt hreg'
      linarith
  have hBA : cumCount (N - 1) σ k = cumCount N σ k := by
    have : (cumCount (N - 1) σ k : ℝ) = cumCount N σ k := by rw [← hnE1, hgE, hnE]
    exact_mod_cast this
  -- the last index `Ṅ_k` of the band `k` of `N − 1`
  have hNk1 := rd_bandNat_pos hda1 hN10 hk1 hkp'
  obtain ⟨-, -, hcs1⟩ := cumCount_spec hda1 hk1 hkp'
  set Nk1 := bandNat (N - 1) σ k with hNk1def
  have hj' : cumCount (N - 1) σ (k - 1) + Nk1 = j := by omega
  have hcm1 := (rd_cum hda1 hσp hk1 hkp').1
  obtain ⟨hγ1pos, hnγ1⟩ := nClass_gammaLoc hda1 hσp hj1 (by omega)
  have hmem1 := gammaBand_mem hda1 hσp hk1 hkp' hNk1 le_rfl
  have hgb1 : gammaBand (N - 1) σ k Nk1 = gammaLoc (N - 1) σ j := by
    unfold gammaBand; rw [hj']
  rw [hgb1] at hmem1
  set γ1 := gammaLoc (N - 1) σ j with hγ1def
  -- the locations: `γ − a < K_e N^{−2/3}`, `γ̇ − ȧ < K_e' N^{−2/3}`
  have hnb := (nClass_edgeVal hda hk1 hkp).2 (by linarith)
  have hlocN := rd_loc_dn hda2 hreg (γ := γ) (by rw [hnb, hnγ, hjk]; norm_num)
    (by positivity) g4 g3
  have hnb1 := (nClass_edgeVal hda1 hk1 hkp').2 (by linarith)
  have hloc1 := rd_loc_dn hda14 hreg' (γ := γ1) (by rw [hnb1, hnγ1, hBA, hjk]; norm_num)
    (by positivity) g6 g5
  -- the window-local statement at the edge `a_{2k}`
  have hwin : gammaBand (N - 1) σ k Nk1 ∈ Set.Icc (a - w) (a + w) := by
    rw [hgb1]
    constructor <;> linarith [hmem1.1]
  have hres := hdot k hk1 hkp ha2 k hk1 hkp' Nk1 hNk1 le_rfl hwin
  have hl : lamDotBand Sig Xm k Nk1 = sortedEig (QdotN Sig Xm) j := by
    unfold lamDotBand; rw [← hσdef, hj']
  rw [hl, hgb1] at hres
  have hrb : ∀ (n : ℕ) (e : ℝ), 1 ≤ n → rigBound N n n e = (N : ℝ) ^ e * x := by
    intro n e hn
    unfold rigBound
    rw [Nat.add_sub_cancel_left, Nat.min_eq_right hn, Nat.cast_one, Real.one_rpow, mul_one]
  rw [hrb _ _ hNk1] at hres
  rw [hrb _ _ hNk]
  have hfin : ((N : ℝ) ^ ε' + Ke + Ke' + |C₁|) * x ≤ (N : ℝ) ^ ε * x :=
    mul_le_mul_of_nonneg_right g8 hx0.le
  rw [abs_le] at hres ⊢
  constructor <;> nlinarith [hmem.1, hmem1.1]

/-- `κ ≤ κ³` for `κ ≥ 1`. -/
private lemma rd_le_cube {κ : ℝ} (h : 1 ≤ κ) : κ ≤ κ ^ 3 := by
  have h2 : 1 ≤ κ ^ 2 := one_le_pow₀ h
  calc κ = κ * 1 := (mul_one κ).symm
    _ ≤ κ * κ ^ 2 := mul_le_mul_of_nonneg_left h2 (by linarith)
    _ = κ ^ 3 := by ring

/-- `n √(κ² n^{−2/3}) (κ² n^{−2/3}) = κ³` for `n > 0`, `κ ≥ 0`. -/
private lemma rd_root {n κ : ℝ} (hn : 0 < n) (hκ : 0 ≤ κ) :
    n * √(2 * κ ^ 2 * n ^ (-(2 / 3 : ℝ)) / 2) * (2 * κ ^ 2 * n ^ (-(2 / 3 : ℝ)) / 2) =
      κ ^ 3 := by
  set s := n ^ (-(1 / 3 : ℝ)) with hsdef
  have hs0 : 0 ≤ s := by positivity
  have hs : n ^ (-(2 / 3 : ℝ)) = s ^ 2 := by
    rw [hsdef, ← Real.rpow_natCast, ← Real.rpow_mul hn.le]; norm_num
  have hs3 : n * s ^ 3 = 1 := by
    rw [hsdef, ← Real.rpow_natCast, ← Real.rpow_mul hn.le]
    norm_num
    rw [Real.rpow_neg_one, mul_inv_cancel₀ hn.ne']
  rw [hs, show 2 * κ ^ 2 * s ^ 2 / 2 = (κ * s) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  calc n * (κ * s) * (κ * s) ^ 2 = κ ^ 3 * (n * s ^ 3) := by ring
    _ = κ ^ 3 := by rw [hs3, mul_one]

set_option maxHeartbeats 4000000 in
-- many linear-arithmetic steps over a large context
/-- Theorem 11.3 under (T_diag) with the classical quantities of `N`, at every index except
`(p, N_p)` when `M ≥ N` (rank `Σ ≥ N`). -/
theorem rigidity_dot_N (τ : ℝ) (C : ℕ → ℝ) (c : ℝ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ),
      IsModel τ C M N Sig X →
      (∀ k, 1 ≤ k → k ≤ 2 * numBands N (specOf Sig) → τ / 2 ≤ edgeVal N (specOf Sig) k →
        RegularEdge (τ / 2) N (specOf Sig) k) →
      (∀ k, 1 ≤ k → k ≤ numBands N (specOf Sig) → RegularBulk c N (specOf Sig) k) →
      HighProbAt N D {ω | ∀ k, 1 ≤ k → k ≤ numBands N (specOf Sig) →
        ∀ i, 1 ≤ i → i ≤ bandNat N (specOf Sig) k → τ ≤ gammaBand N (specOf Sig) k i →
        ¬ (k = numBands N (specOf Sig) ∧ i = bandNat N (specOf Sig) k ∧ N ≤ M) →
          |sortedEig (QdotN Sig (X ω)) (cumCount N (specOf Sig) (k - 1) + i) -
              gammaBand N (specOf Sig) k i| ≤ rigBound N (bandNat N (specOf Sig) k) i ε} := by
  by_cases hτ1 : τ ≤ 1
  swap
  · exact ⟨0, fun N _ Ω _ _ M Sig X hm _ _ => absurd hm.tau_le_one hτ1⟩
  have hτh : 0 < τ / 2 := by positivity
  have hτq : 0 < τ / 4 := by positivity
  set τ₀ := edgeTau0 (τ / 2) with hτ₀
  have ht0 : 0 < τ₀ := rd_tau0_pos hτh
  have ht0τ : τ₀ ≤ τ / 2 / 16 := rd_tau0_le hτh (by linarith)
  have ht0' : 0 < edgeTau0 (τ / 4) := rd_tau0_pos hτq
  by_cases hc : 0 < c (τ₀ / 4) ∧ 0 < c (τ / 8)
  swap
  · refine ⟨0, fun N _ Ω _ _ M Sig X hm _ hbulk => absurd ?_ hc⟩
    have hda : DensityAssumptions τ N (specOf Sig) := hm.diagModel_specOf.densityAssumptions hτ
    obtain ⟨hN, -, hS⟩ := rd_facts hda
    have hp := (card_innerCrit N (specOf Sig) hda.nonneg hN hS).2
    exact ⟨((hbulk 1 le_rfl hp).2.2 (τ₀ / 4) (by positivity)).1,
      ((hbulk 1 le_rfl hp).2.2 (τ / 8) (by positivity)).1⟩
  obtain ⟨hc0, hc8⟩ := hc
  set c₀ := c (τ₀ / 4) with hc₀
  set c₈ := c (τ / 8) with hc₈
  set ε' := min ε 1 / 2 with hε'
  have hε'0 : 0 < ε' := by have := lt_min hε one_pos; rw [hε']; linarith
  have hε'ε : 2 * ε' ≤ ε := by have := min_le_left ε 1; rw [hε']; linarith
  have hε'h : ε' ≤ 1 / 2 := by have := min_le_right ε 1; rw [hε']; linarith
  have hτ'0 := edgeTau'_pos hτh
  have hτ'le := rd_edgeTau'_le hτh (by linarith)
  set τr := edgeTau' (τ / 2) / 2 with hτr
  set w := edgeTau' (τ / 2) / 4 with hw
  have hτr0 : 0 < τr := by positivity
  have hw0 : 0 < w := by positivity
  have hτrτ : τr ≤ τ / 8 := by linarith
  -- the constants
  set c₁ := rdC1 (τ / 2) with hc₁
  set c₂ := rdC2 (τ / 2) with hc₂
  set c₁' := rdC1 (τ / 4) with hc₁'
  have hc₁0 : 0 < c₁ := rd_C1_pos hτh
  have hc₂0 : 0 < c₂ := rd_C2_pos hτh
  have hc₁'0 : 0 < c₁' := rd_C1_pos hτq
  set Kt := max 1 (2 * c₂ / c₁ ^ 3) + 1 with hKt
  set Kb := max 1 (4 * c₂ / c₁ ^ 3) + 1 with hKb
  have hKt1 : 1 ≤ Kt := by have := le_max_left 1 (2 * c₂ / c₁ ^ 3); rw [hKt]; linarith
  have hKb1 : 1 ≤ Kb := by have := le_max_left 1 (4 * c₂ / c₁ ^ 3); rw [hKb]; linarith
  have hc13 : (0 : ℝ) < c₁ ^ 3 := by positivity
  have hKt' : 2 * c₂ < 1 * (c₁ ^ 3 * Kt ^ 3) := by
    have h1 : 2 * c₂ / c₁ ^ 3 < Kt := by
      have := le_max_right 1 (2 * c₂ / c₁ ^ 3); rw [hKt]; linarith
    have h3 := (div_lt_iff₀ hc13).1 h1
    have : c₁ ^ 3 * Kt ≤ c₁ ^ 3 * Kt ^ 3 := mul_le_mul_of_nonneg_left (rd_le_cube hKt1) hc13.le
    linarith [mul_comm Kt (c₁ ^ 3)]
  have hKb' : 2 * c₂ < 1 / 2 * (c₁ ^ 3 * Kb ^ 3) := by
    have h1 : 4 * c₂ / c₁ ^ 3 < Kb := by
      have := le_max_right 1 (4 * c₂ / c₁ ^ 3); rw [hKb]; linarith
    have h3 := (div_lt_iff₀ hc13).1 h1
    have : c₁ ^ 3 * Kb ≤ c₁ ^ 3 * Kb ^ 3 := mul_le_mul_of_nonneg_left (rd_le_cube hKb1) hc13.le
    linarith [mul_comm Kb (c₁ ^ 3)]
  set Ks := Kt + Kb + 2 / c₀ with hKs
  have hKs0 : 0 < Ks := by positivity
  set Ca := 2 * τ⁻¹ * (1 + τ⁻¹) with hCa
  have hCa0 : 0 ≤ Ca := by positivity
  set κ := 1 / c₁ + 1 with hκ
  set κ' := 2 / c₁' + 1 with hκ'
  have hκ1 : 1 ≤ κ := by have : 0 < 1 / c₁ := by positivity
                         linarith
  have hκ'1 : 1 ≤ κ' := by have : 0 < 2 / c₁' := by positivity
                           linarith
  set Ke := 2 * κ ^ 2 with hKe
  set Ke' := 2 * κ' ^ 2 with hKe'
  have hKe0 : 0 < Ke := by positivity
  have hKe'0 : 0 < Ke' := by positivity
  obtain ⟨C₁, Nd, hpredD6⟩ := edge_pred_D6 τ hτ
  set B₁ := 2 + Ks + 2 * (Ca + 1) with hB₁
  set B₂ := 1 + Ke + Ke' + |C₁| with hB₂
  -- the window-local events at `N` and `N − 1`
  obtain ⟨N₁, h₁⟩ := rigidity_edge (τ / 2) C ε' (D + 2) hτh hε'0
  obtain ⟨N₂, h₂⟩ := rigidity_bulk (τ / 2) τr c C ε' (D + 2) hτh hτr0 hε'0
  obtain ⟨N₃, h₃⟩ := rigidity_dot_edge (τ / 2) C ε' (D + 2) hτh hε'0
  obtain ⟨N₄, h₄⟩ := nClass_pred_gap (τ / 2) hτh
  -- the exponent rows, for `N` large
  have hxlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hylim : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(2 / 3 - ε'))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  have hzlim : Tendsto (fun n : ℕ => (n : ℝ) ^ ε') atTop atTop :=
    (tendsto_rpow_atTop hε'0).comp tendsto_natCast_atTop_atTop
  set δ := min (min (τ₀ / 2 / Kt) ((τ / 2 - τr) / Ks))
    (min (τ₀ / Ke) (min (edgeTau0 (τ / 4) / Ke') (w / 2 / Ke'))) with hδ
  have hδ0 : 0 < δ := by
    refine lt_min (lt_min (by positivity) (div_pos (by linarith) hKs0))
      (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hev : ∀ᶠ n : ℕ in atTop, (N₁ ≤ n ∧ N₂ ≤ n ∧ N₃ ≤ n ∧ N₄ ≤ n ∧ Nd ≤ n ∧ 4 ≤ n) ∧
      (n : ℝ) ^ (-(2 / 3 : ℝ)) < δ ∧ (n : ℝ) ^ (-(2 / 3 - ε')) < τ / 4 ∧
      max B₁ B₂ ≤ (n : ℝ) ^ ε' ∧
      8 / (c₀ * τ₀) + 4 / (c₈ * τ) + 8 * |C₁| / τ + 2 * |C₁| / w + 1 ≤ (n : ℝ) := by
    refine Filter.Eventually.and ?_ (Filter.Eventually.and (hxlim.eventually (gt_mem_nhds hδ0))
      (Filter.Eventually.and (hylim.eventually (gt_mem_nhds (by positivity)))
        (Filter.Eventually.and (hzlim.eventually_ge_atTop _)
          ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop _))))
    exact (eventually_ge_atTop N₁).and ((eventually_ge_atTop N₂).and ((eventually_ge_atTop N₃).and
      ((eventually_ge_atTop N₄).and ((eventually_ge_atTop Nd).and (eventually_ge_atTop 4)))))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
  refine ⟨N₀, fun N hN Ω _ _ M Sig X hm hedge hbulk => ?_⟩
  obtain ⟨⟨hN₁, hN₂, hN₃, hN₄, hNd, hN4⟩, hxδ, hyτ, hzB, hNbig⟩ := hN₀ N hN
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN4
  have hNpos : (0 : ℝ) < N := by linarith
  have hN3 : 3 ≤ N := by omega
  have hN2 : 2 ≤ N := by omega
  set x := (N : ℝ) ^ (-(2 / 3 : ℝ)) with hx
  have hx0 : 0 < x := by positivity
  set y := (N : ℝ) ^ ε' with hy
  have hy1 : 1 ≤ y := Real.one_le_rpow (by linarith) hε'0.le
  have hyy : y * y ≤ (N : ℝ) ^ ε := by
    rw [hy, ← Real.rpow_add hNpos]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hB₁y : B₁ ≤ y := (le_max_left _ _).trans hzB
  have hB₂y : B₂ ≤ y := (le_max_right _ _).trans hzB
  -- the numerical facts at this `N`
  have hδ1 : δ ≤ τ₀ / 2 / Kt := (min_le_left _ _).trans (min_le_left _ _)
  have hδ2 : δ ≤ (τ / 2 - τr) / Ks := (min_le_left _ _).trans (min_le_right _ _)
  have hδ3 : δ ≤ τ₀ / Ke := (min_le_right _ _).trans (min_le_left _ _)
  have hδ4 : δ ≤ edgeTau0 (τ / 4) / Ke' :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ5 : δ ≤ w / 2 / Ke' :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have f1 : Kt * x ≤ τ₀ / 2 := by
    have := (lt_div_iff₀ (by linarith : (0 : ℝ) < Kt)).1 (hxδ.trans_le hδ1)
    linarith
  have f4 : Ks * x ≤ τ / 2 - τr := by
    have := (lt_div_iff₀ hKs0).1 (hxδ.trans_le hδ2)
    linarith
  have g4 : Ke * x ≤ τ₀ := by
    have := (lt_div_iff₀ hKe0).1 (hxδ.trans_le hδ3)
    linarith
  have g6 : Ke' * x ≤ edgeTau0 (τ / 4) := by
    have := (lt_div_iff₀ hKe'0).1 (hxδ.trans_le hδ4)
    linarith
  have g6' : Ke' * x ≤ w / 2 := by
    have := (lt_div_iff₀ hKe'0).1 (hxδ.trans_le hδ5)
    linarith
  have hp1 : 0 ≤ 8 / (c₀ * τ₀) := by positivity
  have hp2 : 0 ≤ 4 / (c₈ * τ) := by positivity
  have hp3 : 0 ≤ 8 * |C₁| / τ := by positivity
  have hp4 : 0 ≤ 2 * |C₁| / w := by positivity
  have f3 : 2 / (N * c₀) ≤ τ₀ / 4 := by
    rw [div_le_iff₀ (by positivity)]
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < c₀ * τ₀)).1
      (show 8 / (c₀ * τ₀) ≤ N by linarith)
    have e : τ₀ / 4 * (N * c₀) = N * (c₀ * τ₀) / 4 := by ring
    rw [e]; linarith
  have f5 : 2 * y * x < τ / 2 := by
    have e : y * x = (N : ℝ) ^ (-(2 / 3 - ε')) := by
      rw [hy, hx, ← Real.rpow_add hNpos]; congr 1; ring
    have e2 : 2 * y * x = 2 * (y * x) := by ring
    rw [e2, e]; linarith
  have hyB : B₁ * y ≤ y * y := mul_le_mul_of_nonneg_right hB₁y (by linarith)
  have hyB₂ : B₂ * y ≤ y * y := mul_le_mul_of_nonneg_right hB₂y (by linarith)
  have f6 : 2 * y + Ks + 2 * (Ca + 1) ≤ (N : ℝ) ^ ε := by
    have h0 : 0 ≤ Ks + 2 * (Ca + 1) := by positivity
    have h1 : Ks + 2 * (Ca + 1) ≤ (Ks + 2 * (Ca + 1)) * y := le_mul_of_one_le_right h0 hy1
    have e : B₁ * y = 2 * y + (Ks + 2 * (Ca + 1)) * y := by rw [hB₁]; ring
    linarith
  have g1 : 1 / 2 < N * c₈ * (τ / 8) := by
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < c₈ * τ)).1
      (show 4 / (c₈ * τ) ≤ N - 1 by linarith)
    have e : (N : ℝ) * c₈ * (τ / 8) = ((N : ℝ) - 1) * (c₈ * τ) / 8 + c₈ * τ / 8 := by ring
    have : 0 < c₈ * τ := by positivity
    rw [e]; linarith
  have g2 : |C₁| / N < τ / 8 := by
    rw [div_lt_iff₀ hNpos]
    have h := (div_le_iff₀ hτ).1 (show 8 * |C₁| / τ ≤ N - 1 by linarith)
    have e : τ / 8 * N = ((N : ℝ) - 1) * τ / 8 + τ / 8 := by ring
    rw [e]; linarith
  have g2' : |C₁| / N ≤ w / 2 := by
    rw [div_le_iff₀ hNpos]
    have h := (div_le_iff₀ hw0).1 (show 2 * |C₁| / w ≤ N by linarith)
    have e : w / 2 * N = N * w / 2 := by ring
    rw [e]; linarith
  have g3 : 1 / 2 < N * c₁ * √(Ke * x / 2) * (Ke * x / 2) := by
    have e : (N : ℝ) * c₁ * √(Ke * x / 2) * (Ke * x / 2) =
        c₁ * ((N : ℝ) * √(2 * κ ^ 2 * x / 2) * (2 * κ ^ 2 * x / 2)) := by rw [hKe]; ring
    rw [e, hx, rd_root hNpos (by positivity)]
    have h1 : c₁ * κ ≤ c₁ * κ ^ 3 := mul_le_mul_of_nonneg_left (rd_le_cube hκ1) hc₁0.le
    have h2 : c₁ * κ = 1 + c₁ := by rw [hκ]; field_simp
    linarith
  have g5 : 1 / 2 < ((N - 1 : ℕ) : ℝ) * c₁' * √(Ke' * x / 2) * (Ke' * x / 2) := by
    have hr := rd_root (κ := κ') hNpos (by positivity)
    rw [← hx] at hr
    have e : ((N - 1 : ℕ) : ℝ) * c₁' * √(Ke' * x / 2) * (Ke' * x / 2) =
        c₁' * ((N : ℝ) - 1) / N * ((N : ℝ) * √(2 * κ' ^ 2 * x / 2) * (2 * κ' ^ 2 * x / 2)) := by
      rw [rd_cast_pred hN2, hKe']; field_simp
    rw [e, hr]
    have h0 : c₁' * κ' ≤ c₁' * κ' ^ 3 := mul_le_mul_of_nonneg_left (rd_le_cube hκ'1) hc₁'0.le
    have h0' : c₁' * κ' = 2 + c₁' := by rw [hκ']; field_simp
    have h1 : (1 / 2 : ℝ) ≤ ((N : ℝ) - 1) / N := by
      rw [le_div_iff₀ hNpos]; linarith
    have h2 : 1 < c₁' * κ' ^ 3 := by linarith
    have e2 : c₁' * ((N : ℝ) - 1) / N * κ' ^ 3 = (c₁' * κ' ^ 3) * (((N : ℝ) - 1) / N) := by ring
    rw [e2]
    have : (c₁' * κ' ^ 3) * (1 / 2) ≤ (c₁' * κ' ^ 3) * (((N : ℝ) - 1) / N) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    linarith
  have g7 : |C₁| / N + Ke' * x ≤ w := by linarith
  have g8 : y + Ke + Ke' + |C₁| ≤ (N : ℝ) ^ ε := by
    have h0 : 0 ≤ Ke + Ke' + |C₁| := by positivity
    have h1 : Ke + Ke' + |C₁| ≤ (Ke + Ke' + |C₁|) * y := le_mul_of_one_le_right h0 hy1
    have e : B₂ * y = y + (Ke + Ke' + |C₁|) * y := by rw [hB₂]; ring
    linarith
  -- the model at `N`
  set σ := specOf Sig with hσdef
  have hda : DensityAssumptions τ N σ := hm.diagModel_specOf.densityAssumptions hτ
  have hσp := rd_sigma_pos hm
  have hSig := hm.sigma.posDef.isHermitian
  have hmh : IsModel (τ / 2) C M N Sig X := hm.mono hτh (by linarith)
  have hda2 : DensityAssumptions (τ / 2) N σ := hda.mono hτh (by linarith)
  have hNpos' : 0 < N := by omega
  have hpN := rd_numBands_le hda hNpos'
  set p := numBands N σ with hpdef
  -- the events
  set Se : Finset ℕ := (Finset.Icc 1 (2 * p)).filter (fun l => τ / 2 ≤ edgeVal N σ l) with hSe
  set Sb : Finset ℕ := (Finset.Icc 1 p).filter (fun m => τ / 2 ≤ edgeVal N σ (2 * m - 1))
    with hSb
  set Sd : Finset ℕ := (Finset.Icc 1 p).filter (fun m => τ / 2 ≤ edgeVal N σ (2 * m)) with hSd
  set Ee : ℕ → Set Ω := fun l => {ω | ∀ i, 1 ≤ i → i ≤ bandNat N σ ((l + 1) / 2) →
    gammaBand N σ ((l + 1) / 2) i ∈ Set.Icc (edgeVal N σ l - edgeTau' (τ / 2) / 2)
      (edgeVal N σ l + edgeTau' (τ / 2) / 2) →
    |lamBand Sig (X ω) ((l + 1) / 2) i - gammaBand N σ ((l + 1) / 2) i| ≤
      rigBound N (bandNat N σ ((l + 1) / 2)) i ε'} with hEe
  set Eb : ℕ → Set Ω := fun m => {ω | ∀ i, 1 ≤ i → i ≤ bandNat N σ m →
    gammaBand N σ m i ∈ Set.Icc (edgeVal N σ (2 * m) + τr) (edgeVal N σ (2 * m - 1) - τr) →
    |lamBand Sig (X ω) m i - gammaBand N σ m i| ≤ (N : ℝ) ^ ε' * (N : ℝ)⁻¹} with hEb
  set Ed : ℕ → Set Ω := fun m => {ω | ∀ l, 1 ≤ l → l ≤ numBands (N - 1) σ →
    ∀ i, 1 ≤ i → i ≤ bandNat (N - 1) σ l →
    gammaBand (N - 1) σ l i ∈ Set.Icc (edgeVal N σ (2 * m) - edgeTau' (τ / 2) / 4)
      (edgeVal N σ (2 * m) + edgeTau' (τ / 2) / 4) →
    |lamDotBand Sig (X ω) l i - gammaBand (N - 1) σ l i| ≤
      rigBound N (bandNat (N - 1) σ l) i ε'} with hEd
  have hcard : (((Se.disjSum Sb).disjSum Sd).card : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) := by
    rw [Finset.card_disjSum, Finset.card_disjSum, Real.rpow_two]
    have h1 : Se.card ≤ 2 * p := by
      have := Finset.card_filter_le (Finset.Icc 1 (2 * p)) (fun l => τ / 2 ≤ edgeVal N σ l)
      simpa using this
    have h2 : Sb.card ≤ p := by
      have := Finset.card_filter_le (Finset.Icc 1 p) (fun m => τ / 2 ≤ edgeVal N σ (2 * m - 1))
      simpa using this
    have h3 : Sd.card ≤ p := by
      have := Finset.card_filter_le (Finset.Icc 1 p) (fun m => τ / 2 ≤ edgeVal N σ (2 * m))
      simpa using this
    have h : Se.card + Sb.card + Sd.card ≤ N ^ 2 := by nlinarith
    exact_mod_cast h
  have hev' : ∀ z ∈ (Se.disjSum Sb).disjSum Sd,
      HighProbAt N (D + 2) (Sum.elim (Sum.elim Ee Eb) Ed z) := by
    rintro ((l | m) | m) hz
    · have hl := Finset.inl_mem_disjSum.1 (Finset.inl_mem_disjSum.1 hz)
      simp only [hSe, Finset.mem_filter, Finset.mem_Icc] at hl
      exact h₁ N hN₁ M Sig X l hmh (hedge l hl.1.1 hl.1.2 hl.2)
    · have hm' := Finset.inr_mem_disjSum.1 (Finset.inl_mem_disjSum.1 hz)
      simp only [hSb, Finset.mem_filter, Finset.mem_Icc] at hm'
      exact h₂ N hN₂ M Sig X m hmh (hbulk m hm'.1.1 hm'.1.2)
        (Or.inr (hedge (2 * m - 1) (by omega) (by omega) hm'.2))
    · have hm' := Finset.inr_mem_disjSum.1 hz
      simp only [hSd, Finset.mem_filter, Finset.mem_Icc] at hm'
      exact h₃ N hN₃ M Sig X (2 * m) hmh (hedge (2 * m) (by omega) (by omega) hm'.2)
  have hI := HighProbAt.biInter ((Se.disjSum Sb).disjSum Sd) (by omega) hcard hev'
  unfold HighProbAt at hI ⊢
  refine le_trans (measure_mono (Set.compl_subset_compl.2 ?_)) hI
  intro ω hω
  have hE1 : ∀ l, 1 ≤ l → l ≤ 2 * p → τ / 2 ≤ edgeVal N σ l → ω ∈ Ee l := fun l h1 h2 h3 =>
    Set.mem_iInter₂.1 hω (Sum.inl (Sum.inl l)) (Finset.inl_mem_disjSum.2
      (Finset.inl_mem_disjSum.2 (by
        simp only [hSe, Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨h1, h2⟩, h3⟩)))
  have hE2 : ∀ m, 1 ≤ m → m ≤ p → τ / 2 ≤ edgeVal N σ (2 * m - 1) → ω ∈ Eb m :=
    fun m h1 h2 h3 => Set.mem_iInter₂.1 hω (Sum.inl (Sum.inr m)) (Finset.inl_mem_disjSum.2
      (Finset.inr_mem_disjSum.2 (by
        simp only [hSb, Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨h1, h2⟩, h3⟩)))
  have hE3 : ∀ m, 1 ≤ m → m ≤ p → τ / 2 ≤ edgeVal N σ (2 * m) → ω ∈ Ed m :=
    fun m h1 h2 h3 => Set.mem_iInter₂.1 hω (Sum.inr m) (Finset.inr_mem_disjSum.2
      (by simp only [hSd, Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨h1, h2⟩, h3⟩))
  have hrig : ∀ k i, 1 ≤ k → k ≤ p → 1 ≤ i → i ≤ bandNat N σ k →
      τ / 2 + τr ≤ gammaBand N σ k i →
      |lamBand Sig (X ω) k i - gammaBand N σ k i| ≤ rigBound N (bandNat N σ k) i ε' :=
    fun k i hk1 hkp hi hiN hγ => rd_rigN hda hτr0 (fun l h1 h2 h3 => hE1 l h1 h2 h3)
      (fun m h1 h2 h3 => hE2 m h1 h2 h3) hk1 hkp hi hiN hγ
  simp only [Set.mem_ofPred_eq]
  intro k hk1 hkp i hi hiN hγ hex
  by_cases hiN1 : i + 1 ≤ bandNat N σ k
  · exact rd_dotN_A hda hσp hSig hN2 hedge hc0 hτr0
      (fun m h1 h2 => ((hbulk m h1 h2).2.2 (τ₀ / 4) (by positivity)).2) hrig
      (by linarith) hKt' (by linarith) hKb' f1 f3 f4 f5 f6 hk1 hkp hi hiN1 hγ
  · have hi' : i = bandNat N σ k := by omega
    rw [hi'] at hγ ⊢
    have hex' : k < p ∨ M < N := by
      by_contra hc'
      push Not at hc'
      exact hex ⟨by omega, hi', hc'.2⟩
    exact rd_dotN_B hda hσp hN3 hedge hc8
      (fun m h1 h2 => ((hbulk m h1 h2).2.2 (τ / 8) (by positivity)).2)
      (fun l h1 h2 h3 => hpredD6 N hNd M σ hda hedge l h1 h2 h3)
      (fun E h1 h2 h3 => h₄ N hN₄ M σ hda2 E (by linarith) (by linarith) h3)
      (fun m h1 h2 h3 => hE3 m h1 h2 h3) hKe0 hKe'0 g1 g2 g3 g4 g5 g6 g7 g8 hk1 hkp hγ hex'

/-- Theorem 11.3 at `Σ = I_{2n}`, `N = n` (rank `Σ ≥ N`), Gaussian `X`, `τ = 1/10`:
every hypothesis is discharged; the only binder left is `n ≥ N₀`. For the classical
quantities of `N − 1 = n − 1` samples there is a single band `k = 1`, with the indices
`i ≤ Ṅ_1 = n − 1` (the nontrivial eigenvalues of `Q̇`). -/
example : ∃ N₀ : ℕ, ∀ n : ℕ, 1 ≤ n → N₀ ≤ n →
    HighProbAt (Ω := GaussSpace (2 * n) n) n 1 {ω | ∀ k, 1 ≤ k →
      k ≤ numBands (n - 1) (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) →
      ∀ i, 1 ≤ i → i ≤ bandNat (n - 1) (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) k →
      1 / 10 ≤ gammaBand (n - 1) (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) k i →
        |lamDotBand 1 (gaussX (2 * n) n ω) k i -
            gammaBand (n - 1) (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) k i| ≤
          rigBound n (bandNat (n - 1) (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) k) i
            (1 / 3)} := by
  obtain ⟨N₀, h⟩ := rigidity_dot (1 / 10) gaussMoment (fun t => min t 1 / 50) (1 / 3) 1
    (by norm_num) (by norm_num)
  refine ⟨N₀, fun n hn1 hn => h n hn (2 * n) 1 (gaussX (2 * n) n) (isModel_two hn1) ?_ ?_⟩
  · intro k hk1 hk2 _
    rw [specOf_one_eq] at hk2 ⊢
    rw [numBands_one (by omega) (by omega)] at hk2
    exact regularEdge_two (by omega) hk1 (by omega)
  · intro k hk1 hk2
    rw [specOf_one_eq] at hk2 ⊢
    rw [numBands_one (by omega) (by omega)] at hk2
    obtain rfl : k = 1 := by omega
    exact regularBulk_two (by omega)

/-- Theorem 11.3 for a general `T` at `T = tPad n` (`M = 2n`, `K = n`, `N = 2n`,
`Σ = diag(I_n, 0)` singular), Rademacher `X`, `τ = 1/5`: every hypothesis is discharged. -/
example : ∃ N₀ : ℕ, ∀ n : ℕ, 1 ≤ n → N₀ ≤ 2 * n →
    HighProbAt (Ω := SignSpace (Fin n × Fin (2 * n))) (2 * n) 1 {ω | ∀ k, 1 ≤ k →
      k ≤ numBands (2 * n - 1) (specOf (tPad n * (tPad n)ᵀ)) →
      ∀ i, 1 ≤ i → i ≤ bandNat (2 * n - 1) (specOf (tPad n * (tPad n)ᵀ)) k →
      1 / 5 ≤ gammaBand (2 * n - 1) (specOf (tPad n * (tPad n)ᵀ)) k i →
        |lamDotBandT (tPad n) (radXn n ω) k i -
            gammaBand (2 * n - 1) (specOf (tPad n * (tPad n)ᵀ)) k i| ≤
          rigBound (2 * n) (bandNat (2 * n - 1) (specOf (tPad n * (tPad n)ᵀ)) k) i 1} := by
  obtain ⟨N₀, h⟩ := rigidity_dot_gen (1 / 5) (fun _ => 1) (fun t => min t 1 / 50) 1 1
    (by norm_num) one_pos
  exact ⟨N₀, fun n hn hN => h (2 * n) hN (2 * n) n (tPad n) (radXn n) (isModelT_tPad (by omega))
    (mpT_hyps (by omega)).1 (mpT_hyps (by omega)).2.1⟩


/-- `rigidity_dot_edge_gen` at `T = tPad n` (`M = 2n`, `K = n`, `N = 2n`, `Σ = diag(I_n, 0)`
singular), Rademacher `X`, `τ = 1/5`, at the regular top edge `k = 1`: every hypothesis is
discharged. -/
example : ∃ N₀ : ℕ, ∀ n : ℕ, 1 ≤ n → N₀ ≤ 2 * n →
    HighProbAt (Ω := SignSpace (Fin n × Fin (2 * n))) (2 * n) 1 {ω | ∀ l, 1 ≤ l →
      l ≤ numBands (2 * n - 1) (specOf (tPad n * (tPad n)ᵀ)) →
      ∀ i, 1 ≤ i → i ≤ bandNat (2 * n - 1) (specOf (tPad n * (tPad n)ᵀ)) l →
      gammaBand (2 * n - 1) (specOf (tPad n * (tPad n)ᵀ)) l i ∈
        Set.Icc (edgeVal (2 * n) (specOf (tPad n * (tPad n)ᵀ)) 1 - tauGen (1 / 5) / 4)
          (edgeVal (2 * n) (specOf (tPad n * (tPad n)ᵀ)) 1 + tauGen (1 / 5) / 4) →
        |lamDotBandT (tPad n) (radXn n ω) l i -
            gammaBand (2 * n - 1) (specOf (tPad n * (tPad n)ᵀ)) l i| ≤
          rigBound (2 * n) (bandNat (2 * n - 1) (specOf (tPad n * (tPad n)ᵀ)) l) i 1} := by
  obtain ⟨N₀, h⟩ := rigidity_dot_edge_gen (1 / 5) (fun _ => 1) 1 1 (by norm_num) one_pos
  exact ⟨N₀, fun n hn hN => h (2 * n) hN (2 * n) n (tPad n) (radXn n) 1 (isModelT_tPad (by omega))
    (mpT_hyps (by omega)).2.2.1⟩

/-- `rigidity_dot_bulk_gen` at `T = tPad n` (`M = 2n`, `K = n`, `N = 2n`), Rademacher `X`,
`τ = τ' = 1/5`, `c(t) = min(t, 1)/50`, in the band `k = 1` with its regular upper edge (window
`[a₂ + 1/5, a₁ − 1/5]`, nonempty): every hypothesis is discharged. -/
example : ∃ N₀ : ℕ, ∀ n : ℕ, 1 ≤ n → N₀ ≤ 2 * n →
    HighProbAt (Ω := SignSpace (Fin n × Fin (2 * n))) (2 * n) 1 {ω | ∀ l, 1 ≤ l →
      l ≤ numBands (2 * n - 1) (specOf (tPad n * (tPad n)ᵀ)) →
      ∀ i, 1 ≤ i → i ≤ bandNat (2 * n - 1) (specOf (tPad n * (tPad n)ᵀ)) l →
      gammaBand (2 * n - 1) (specOf (tPad n * (tPad n)ᵀ)) l i ∈
        Set.Icc (edgeVal (2 * n) (specOf (tPad n * (tPad n)ᵀ)) (2 * 1) + 1 / 5)
          (edgeVal (2 * n) (specOf (tPad n * (tPad n)ᵀ)) (2 * 1 - 1) - 1 / 5) →
        |lamDotBandT (tPad n) (radXn n ω) l i -
            gammaBand (2 * n - 1) (specOf (tPad n * (tPad n)ᵀ)) l i| ≤
          ((2 * n : ℕ) : ℝ) ^ (1 : ℝ) * ((2 * n : ℕ) : ℝ)⁻¹} := by
  obtain ⟨N₀, h⟩ := rigidity_dot_bulk_gen (1 / 5) (1 / 5) (fun t => min t 1 / 50) (fun _ => 1) 1 1
    (by norm_num) (by norm_num) one_pos
  exact ⟨N₀, fun n hn hN => h (2 * n) hN (2 * n) n (tPad n) (radXn n) 1 (isModelT_tPad (by omega))
    (mpT_hyps (by omega)).2.2.2 (Or.inr (mpT_hyps (by omega)).2.2.1)⟩

/-- `rigidity_dot_N` at `Σ = I_{2n}`, `N = n` (rank `Σ ≥ N`), Gaussian `X`, `τ = 1/10`: every
hypothesis is discharged; the only binder left is `n ≥ N₀`. The excluded index is
`(1, N_1) = (1, n)`; by `gammaBand_two_gt` every `γ_{1,i}`, `i ≤ n`, exceeds `(√2 − 1)² > 1/10`, so
every index `i ≤ n − 1` is constrained. -/
example : ∃ N₀ : ℕ, ∀ n : ℕ, 1 ≤ n → N₀ ≤ n →
    HighProbAt (Ω := GaussSpace (2 * n) n) n 1 {ω | ∀ k, 1 ≤ k →
      k ≤ numBands n (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) →
      ∀ i, 1 ≤ i → i ≤ bandNat n (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) k →
      1 / 10 ≤ gammaBand n (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) k i →
      ¬ (k = numBands n (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) ∧
        i = bandNat n (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) k ∧ n ≤ 2 * n) →
        |sortedEig (QdotN 1 (gaussX (2 * n) n ω))
            (cumCount n (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) (k - 1) + i) -
          gammaBand n (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) k i| ≤
        rigBound n (bandNat n (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) k) i
          (1 / 3)} := by
  obtain ⟨N₀, h⟩ := rigidity_dot_N (1 / 10) gaussMoment (fun t => min t 1 / 50) (1 / 3) 1
    (by norm_num) (by norm_num)
  refine ⟨N₀, fun n hn1 hn => h n hn (2 * n) 1 (gaussX (2 * n) n) (isModel_two hn1) ?_ ?_⟩
  · intro k hk1 hk2 _
    rw [specOf_one_eq] at hk2 ⊢
    rw [numBands_one (by omega) (by omega)] at hk2
    exact regularEdge_two (by omega) hk1 (by omega)
  · intro k hk1 hk2
    rw [specOf_one_eq] at hk2 ⊢
    rw [numBands_one (by omega) (by omega)] at hk2
    obtain rfl : k = 1 := by omega
    exact regularBulk_two (by omega)

#print axioms rigidity_dot_edge_gen
#print axioms rigidity_dot_bulk_gen
#print axioms rigidity_dot
#print axioms rigidity_dot_gen
#print axioms rigidity_dot_N

end Anisotropic
