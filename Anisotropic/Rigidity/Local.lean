import Anisotropic.Density.Critical
import Anisotropic.Density.SelfConsistent
import Anisotropic.Density.Varrho
import Anisotropic.Endpoints.Local
import Anisotropic.Endpoints.Main
import Anisotropic.Entrywise.DiagModel
import Anisotropic.Framework.Domination
import Anisotropic.Framework.Model
import Anisotropic.GeneralT.Masses
import Anisotropic.Probability.NormBound.Main
import Anisotropic.Rigidity.Defs
import Anisotropic.Rigidity.Exclusion
import Anisotropic.Rigidity.Segment

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # The localized eigenvalue count and the bulk inversion -/

/-! ## The Poisson representation of `Im m` -/

/-- `Im (t − (x + iy))⁻¹ = y / ((t − x)² + y²)`. -/
private lemma cl_inv_im (t x y : ℝ) :
    (((t : ℂ) - (↑x + ↑y * Complex.I))⁻¹).im = y / ((t - x) ^ 2 + y ^ 2) := by
  rw [Complex.inv_im, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.add_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, Complex.sub_im, Complex.add_im, Complex.mul_im]
  ring

/-- On `ℂ₊`, `m(z) = ∫ (t − z)⁻¹ dϱ(t)`. -/
private lemma cl_mFun_eq_integral (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {z : ℂ}
    (hz : 0 < z.im) : mFun N σ z = ∫ t : ℝ, ((t : ℂ) - z)⁻¹ ∂(varrho N σ) := by
  rw [← resolventTransform_varrho N σ hσ hN hz, resolventTransform_apply]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp [resolvent, Ring.inverse_eq_inv']

/-- `t ↦ (t − z)⁻¹` is `ϱ`-integrable for `Im z > 0`. -/
private lemma cl_integrable_inv (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {z : ℂ}
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
private lemma cl_mFun_im_eq (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) (x : ℝ) {y : ℝ}
    (hy : 0 < y) :
    (mFun N σ (↑x + ↑y * Complex.I)).im = ∫ t, y / ((t - x) ^ 2 + y ^ 2) ∂(varrho N σ) := by
  have hz : 0 < ((x : ℂ) + ↑y * Complex.I).im := by simpa using hy
  rw [cl_mFun_eq_integral σ hσ hN hz]
  have := integral_im (𝕜 := ℂ) (cl_integrable_inv σ hσ hN hz)
  simp only [RCLike.im_to_complex] at this
  rw [← this]
  simp_rw [cl_inv_im]

/-- The Lorentzian `t ↦ y / ((t − E)² + y²)` is integrable against a finite measure. -/
private lemma cl_integrable_lorentz (μ : Measure ℝ) [IsFiniteMeasure μ] (E : ℝ) {y : ℝ}
    (hy : 0 < y) : Integrable (fun t : ℝ => y / ((t - E) ^ 2 + y ^ 2)) μ := by
  refine Integrable.of_bound ?_ (1 / y) (ae_of_all _ fun t => ?_)
  · exact (continuous_const.div (by fun_prop) fun t => by positivity).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_le_div_iff₀ (by positivity) hy]
    nlinarith [sq_nonneg (t - E)]

/-- `∫_{a}^{b} η/((c − x)² + η²) dx = arctan((b − c)/η) − arctan((a − c)/η)`. -/
private lemma cl_arctan_term (c a b η : ℝ) (hη : 0 < η) :
    ∫ x in a..b, η / ((c - x) ^ 2 + η ^ 2) =
      Real.arctan ((b - c) / η) - Real.arctan ((a - c) / η) := by
  have hd : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun x : ℝ => Real.arctan ((x - c) / η))
      (η / ((c - x) ^ 2 + η ^ 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => (x - c) / η) (1 / η) x := by
      simpa using ((hasDerivAt_id x).sub_const c).div_const η
    have := h1.arctan
    convert this using 1
    have : (c - x) ^ 2 = (x - c) ^ 2 := by ring
    rw [this]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  exact (continuous_const.div (by fun_prop) fun x => by positivity :
    Continuous fun x : ℝ => η / ((c - x) ^ 2 + η ^ 2)).intervalIntegrable _ _

/-! ## The density part of `ϱ` -/

/-- `ϱ(A) = ∫_A ρ` for measurable `A ⊆ (0, ∞)`. -/
private lemma cl_varrho_apply (N : ℕ) (σ : Fin M → ℝ) {A : Set ℝ} (hA : MeasurableSet A)
    (hsub : A ⊆ Set.Ioi 0) :
    varrho N σ A = ∫⁻ x in A, ENNReal.ofReal (rhoDens N σ x) := by
  have h0 : (0 : ℝ) ∉ A := fun h => lt_irrefl (0 : ℝ) (Set.mem_Ioi.mp (hsub h))
  rw [varrho, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hA,
    Set.indicator_of_notMem h0, smul_zero, zero_add, withDensity_apply _ hA,
    Measure.restrict_restrict hA, Set.inter_eq_left.mpr hsub]

/-- `ρ` is continuous on `(0, ∞)`. -/
private lemma cl_continuousOn_rhoDens (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) :
    ContinuousOn (rhoDens N σ) (Set.Ioi 0) := by
  have h1 : ContinuousOn (fun x : ℝ => mExt N σ x) (Set.Ioi 0) :=
    (continuousOn_mExt N σ hσ).comp Complex.continuous_ofReal.continuousOn
      (fun x hx => Or.inr ⟨Complex.ofReal_im x, Complex.ofReal_ne_zero.mpr (ne_of_gt hx)⟩)
  exact (Complex.continuous_im.comp_continuousOn h1).div_const _

/-- On a compact interval inside `(0, ∞)`, `ϱ` is `ρ dx`. -/
private lemma cl_varrho_restrict (N : ℕ) (σ : Fin M → ℝ) {a b : ℝ} (ha : 0 < a) :
    (varrho N σ).restrict (Set.Icc a b) =
      (volume.restrict (Set.Icc a b)).withDensity (fun x => ENNReal.ofReal (rhoDens N σ x)) := by
  have hsub : ∀ A : Set ℝ, A ∩ Set.Icc a b ⊆ Set.Ioi 0 := fun A x hx =>
    lt_of_lt_of_le ha hx.2.1
  refine Measure.ext fun A hA => ?_
  rw [Measure.restrict_apply hA, withDensity_apply _ hA, Measure.restrict_restrict hA,
    cl_varrho_apply N σ (hA.inter measurableSet_Icc) (hsub A)]

/-- The Poisson lower bound: `Im m(E + iη) ≥ 2 c₀ arctan(t/η)` if `ρ ≥ c₀` on `[E − t, E + t] ⊆ (0, ∞)`. -/
theorem im_mFun_ge_of_density {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {E t c₀ η : ℝ}
    (ht : 0 < t) (hEt : 0 < E - t) (hη : 0 < η) (hc₀ : 0 ≤ c₀)
    (hρ : ∀ x ∈ Set.Icc (E - t) (E + t), c₀ ≤ rhoDens N σ x) :
    2 * c₀ * Real.arctan (t / η) ≤ (mFun N σ ⟨E, η⟩).im := by
  have hprob := isProbabilityMeasure_varrho N σ hσ hN
  have hz : (⟨E, η⟩ : ℂ) = ↑E + ↑η * Complex.I := by apply Complex.ext <;> simp
  rw [hz, cl_mFun_im_eq σ hσ hN E hη]
  set f : ℝ → ℝ := fun u => η / ((u - E) ^ 2 + η ^ 2) with hf
  have hfi : Integrable f (varrho N σ) := cl_integrable_lorentz _ E hη
  have hfc : Continuous f := continuous_const.div (by fun_prop) fun x => by positivity
  have hf0 : ∀ u, 0 ≤ f u := fun u => by positivity
  have hIsub : Set.Icc (E - t) (E + t) ⊆ Set.Ioi 0 := fun x hx => lt_of_lt_of_le hEt hx.1
  have h1 : ∫ u in Set.Icc (E - t) (E + t), f u ∂(varrho N σ) ≤ ∫ u, f u ∂(varrho N σ) :=
    setIntegral_le_integral hfi (ae_of_all _ hf0)
  have hρc : ContinuousOn (rhoDens N σ) (Set.Icc (E - t) (E + t)) :=
    (cl_continuousOn_rhoDens N σ hσ).mono hIsub
  have h2 : ∫ u in Set.Icc (E - t) (E + t), f u ∂(varrho N σ) =
      ∫ u in Set.Icc (E - t) (E + t), rhoDens N σ u * f u := by
    have hint := integral_withDensity_eq_integral_toReal_smul₀
      (μ := volume.restrict (Set.Icc (E - t) (E + t)))
      (f := fun x => ENNReal.ofReal (rhoDens N σ x))
      (ENNReal.measurable_ofReal.comp_aemeasurable (hρc.aemeasurable measurableSet_Icc))
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top) f
    rw [cl_varrho_restrict N σ (b := E + t) hEt, hint]
    refine setIntegral_congr_fun measurableSet_Icc fun x hx => ?_
    rw [ENNReal.toReal_ofReal ((hc₀.trans (hρ x hx))), smul_eq_mul]
  have h3 : ∫ u in Set.Icc (E - t) (E + t), c₀ * f u ≤
      ∫ u in Set.Icc (E - t) (E + t), rhoDens N σ u * f u := by
    refine setIntegral_mono_on ?_ ?_ measurableSet_Icc fun x hx =>
      mul_le_mul_of_nonneg_right (hρ x hx) (hf0 x)
    · exact (continuous_const.mul hfc).continuousOn.integrableOn_Icc
    · exact (hρc.mul hfc.continuousOn).integrableOn_Icc
  have h4 : ∫ u in Set.Icc (E - t) (E + t), c₀ * f u = 2 * c₀ * Real.arctan (t / η) := by
    rw [integral_const_mul, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le
      (by linarith)]
    have : ∫ u in (E - t)..(E + t), f u = ∫ u in (E - t)..(E + t), η / ((E - u) ^ 2 + η ^ 2) := by
      refine intervalIntegral.integral_congr fun u _ => ?_
      simp only [hf]
      rw [show (u - E) ^ 2 = (E - u) ^ 2 by ring]
    rw [this, cl_arctan_term E (E - t) (E + t) η hη]
    rw [show E + t - E = t by ring, show E - t - E = -t by ring, neg_div, Real.arctan_neg]
    ring
  linarith

/-! ## The counting function `n` -/

/-- `n(x) − n(y) = N ϱ([x, y))` for `x ≤ y`. -/
private lemma cl_nClass_sub (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {x y : ℝ}
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

/-- `n` is nonincreasing. -/
private lemma cl_nClass_anti (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) :
    Antitone (nClass N σ) := by
  intro x y hxy
  have := cl_nClass_sub σ hσ hN hxy
  have h0 : 0 ≤ (N : ℝ) * (varrho N σ (Set.Ico x y)).toReal := by positivity
  linarith

/-- `n ≥ 0`. -/
private lemma cl_nClass_nonneg (σ : Fin M → ℝ) (E : ℝ) : 0 ≤ nClass N σ E := by
  unfold nClass
  positivity

/-- If `ρ ≥ c₀` on `[x, y)` with `0 < x ≤ y`, then `n(x) − n(y) ≥ N c₀ (y − x)`. -/
private lemma cl_nClass_sub_ge (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {x y c₀ : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (hc₀ : 0 ≤ c₀)
    (hρ : ∀ u ∈ Set.Ico x y, c₀ ≤ rhoDens N σ u) :
    N * c₀ * (y - x) ≤ nClass N σ x - nClass N σ y := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  rw [cl_nClass_sub σ hσ hN hxy]
  have hsub : Set.Ico x y ⊆ Set.Ioi 0 := fun u hu => lt_of_lt_of_le hx hu.1
  have hge : ENNReal.ofReal (c₀ * (y - x)) ≤ varrho N σ (Set.Ico x y) := by
    rw [cl_varrho_apply N σ measurableSet_Ico hsub]
    calc ENNReal.ofReal (c₀ * (y - x))
        = ∫⁻ u in Set.Ico x y, ENNReal.ofReal c₀ := by
          rw [setLIntegral_const, Real.volume_Ico, ENNReal.ofReal_mul hc₀]
      _ ≤ ∫⁻ u in Set.Ico x y, ENNReal.ofReal (rhoDens N σ u) :=
          setLIntegral_mono' measurableSet_Ico fun u hu =>
            ENNReal.ofReal_le_ofReal (hρ u hu)
  have h1 : c₀ * (y - x) ≤ (varrho N σ (Set.Ico x y)).toReal := by
    have := ENNReal.toReal_mono (measure_ne_top _ _) hge
    rwa [ENNReal.toReal_ofReal (mul_nonneg hc₀ (by linarith))] at this
  nlinarith [h1, (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]

/-- `ϱ([g, g + δ]) ≤ 2 δ Im m(g + iδ)`. -/
private lemma cl_varrho_Icc_le (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) (g : ℝ) {δ : ℝ}
    (hδ : 0 < δ) :
    (varrho N σ (Set.Icc g (g + δ))).toReal ≤ 2 * δ * (mFun N σ (↑g + ↑δ * Complex.I)).im := by
  have hprob := isProbabilityMeasure_varrho N σ hσ hN
  rw [cl_mFun_im_eq σ hσ hN g hδ]
  have hfi := cl_integrable_lorentz (varrho N σ) g hδ
  have h1 : ∫ u in Set.Icc g (g + δ), δ / ((u - g) ^ 2 + δ ^ 2) ∂(varrho N σ) ≤
      ∫ u, δ / ((u - g) ^ 2 + δ ^ 2) ∂(varrho N σ) :=
    setIntegral_le_integral hfi (ae_of_all _ fun u => by positivity)
  have h2 : (varrho N σ (Set.Icc g (g + δ))).toReal * (1 / (2 * δ)) ≤
      ∫ u in Set.Icc g (g + δ), δ / ((u - g) ^ 2 + δ ^ 2) ∂(varrho N σ) := by
    have := setIntegral_mono_on (μ := varrho N σ) (s := Set.Icc g (g + δ))
      (f := fun _ => 1 / (2 * δ)) (g := fun u => δ / ((u - g) ^ 2 + δ ^ 2))
      (integrableOn_const (measure_ne_top _ _) |>.mono_set subset_rfl) hfi.integrableOn
      measurableSet_Icc (fun u hu => by
        have hu1 : 0 ≤ u - g := by linarith [hu.1]
        have hu2 : u - g ≤ δ := by linarith [hu.2]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonneg hu1 (by linarith : 0 ≤ δ - (u - g))])
    simpa [Measure.real, mul_comm] using this
  have h3 : (varrho N σ (Set.Icc g (g + δ))).toReal ≤
      2 * δ * ∫ u, δ / ((u - g) ^ 2 + δ ^ 2) ∂(varrho N σ) := by
    have h4 : (varrho N σ (Set.Icc g (g + δ))).toReal ≤
        (∫ u, δ / ((u - g) ^ 2 + δ ^ 2) ∂(varrho N σ)) * (2 * δ) := by
      have := h2.trans h1
      rw [mul_one_div, div_le_iff₀ (by positivity)] at this
      exact this
    linarith
  exact h3

/-! ## Lipschitz bounds and grids -/

/-- `|s(z) − s(w)| ≤ |z − w| / (Im z · Im w)` for the Stieltjes transform of finitely many
points. -/
private lemma cl_lip_emp {K : ℕ} (lam : Fin K → ℝ) {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    ‖empStieltjes lam z - empStieltjes lam w‖ ≤ ‖z - w‖ / (z.im * w.im) := by
  have hb : ∀ j : Fin K, ‖((lam j : ℂ) - z)⁻¹ - ((lam j : ℂ) - w)⁻¹‖ ≤
      ‖z - w‖ / (z.im * w.im) := by
    intro j
    have hne : ∀ u : ℂ, 0 < u.im → (lam j : ℂ) - u ≠ 0 := fun u hu h => by
      have := congrArg Complex.im h
      simp at this
      linarith
    have hge : ∀ u : ℂ, 0 < u.im → u.im ≤ ‖(lam j : ℂ) - u‖ := fun u hu => by
      have h := Complex.abs_im_le_norm ((lam j : ℂ) - u)
      simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] at h
      exact le_trans (le_abs_self _) h
    have hz0 := hne z hz
    have hw0 := hne w hw
    have e : ((lam j : ℂ) - z)⁻¹ - ((lam j : ℂ) - w)⁻¹ =
        (z - w) / (((lam j : ℂ) - z) * ((lam j : ℂ) - w)) := by
      field_simp
      ring
    rw [e, norm_div, norm_mul]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (mul_pos hz hw)
      (mul_le_mul (hge z hz) (hge w hw) hw.le (norm_nonneg _))
  unfold empStieltjes
  rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul]
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp only [Finset.univ_eq_empty, Finset.sum_empty, norm_zero, mul_zero]
    positivity
  · have hsum : ‖∑ j : Fin K, (((lam j : ℂ) - z)⁻¹ - ((lam j : ℂ) - w)⁻¹)‖ ≤
        K * (‖z - w‖ / (z.im * w.im)) := by
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun j _ => hb j).trans ?_
      simp
    have hK' : ‖(K : ℂ)⁻¹‖ = (K : ℝ)⁻¹ := by simp
    rw [hK']
    calc (K : ℝ)⁻¹ * ‖∑ j : Fin K, (((lam j : ℂ) - z)⁻¹ - ((lam j : ℂ) - w)⁻¹)‖
        ≤ (K : ℝ)⁻¹ * (K * (‖z - w‖ / (z.im * w.im))) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = ‖z - w‖ / (z.im * w.im) := by
          have : (K : ℝ) ≠ 0 := by positivity
          field_simp

/-- The difference `s − m` is Lipschitz in `z` with constant `2 / (Im z · Im w)`. -/
private lemma cl_lip_d (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {K : ℕ}
    (lam : Fin K → ℝ) {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    ‖(empStieltjes lam z - mFun N σ z) - (empStieltjes lam w - mFun N σ w)‖ ≤
      2 * ‖z - w‖ / (z.im * w.im) := by
  have hprob := isProbabilityMeasure_varrho N σ hσ hN
  have h1 := cl_lip_emp lam hz hw
  have h2 := norm_resolventTransform_sub_le (varrho N σ) hz hw
  rw [resolventTransform_varrho N σ hσ hN hz, resolventTransform_varrho N σ hσ hN hw] at h2
  have e : (empStieltjes lam z - mFun N σ z) - (empStieltjes lam w - mFun N σ w) =
      (empStieltjes lam z - empStieltjes lam w) - (mFun N σ z - mFun N σ w) := by ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have : 2 * ‖z - w‖ / (z.im * w.im) = ‖z - w‖ / (z.im * w.im) + ‖z - w‖ / (z.im * w.im) := by
    ring
  rw [this]
  exact add_le_add h1 h2

/-- A finite grid on `[a, b]` with spacing `δ`: every point lies between two grid points at
distance at most `δ`. -/
private lemma cl_exists_grid {a b δ : ℝ} (hδ : 0 < δ) (hab : a ≤ b) :
    ∃ G : Finset ℝ, (∀ g ∈ G, g ∈ Set.Icc a b) ∧
      (∀ t ∈ Set.Icc a b, ∃ g ∈ G, ∃ g' ∈ G, g ≤ t ∧ t ≤ g' ∧ g' - g ≤ δ) ∧
      (G.card : ℝ) ≤ (b - a) / δ + 3 := by
  set J : ℕ := ⌈(b - a) / δ⌉₊ with hJ
  have hba : 0 ≤ (b - a) / δ := div_nonneg (by linarith) hδ.le
  have hJ1 : (b - a) / δ ≤ J := Nat.le_ceil _
  have hJ2 : (J : ℝ) < (b - a) / δ + 1 := Nat.ceil_lt_add_one hba
  let f : ℕ → ℝ := fun j => min (a + j * δ) b
  refine ⟨(Finset.range (J + 2)).image f, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hg
    refine ⟨le_min ?_ hab, min_le_right _ _⟩
    have : (0 : ℝ) ≤ j * δ := by positivity
    linarith
  · intro t ht
    set j : ℕ := ⌊(t - a) / δ⌋₊ with hjdef
    have hta : 0 ≤ (t - a) / δ := div_nonneg (by linarith [ht.1]) hδ.le
    have h1 : (j : ℝ) ≤ (t - a) / δ := Nat.floor_le hta
    have h2 : (t - a) / δ < j + 1 := Nat.lt_floor_add_one _
    have h1' : (j : ℝ) * δ ≤ t - a := by
      have := mul_le_mul_of_nonneg_right h1 hδ.le
      rwa [div_mul_cancel₀ _ hδ.ne'] at this
    have h2' : t - a < ((j : ℝ) + 1) * δ := by
      have := mul_lt_mul_of_pos_right h2 hδ
      rwa [div_mul_cancel₀ _ hδ.ne'] at this
    have hjJ : (j : ℝ) ≤ J := by
      refine h1.trans (le_trans ?_ hJ1)
      exact div_le_div_of_nonneg_right (by linarith [ht.2]) hδ.le
    have hjJ' : j ≤ J := by exact_mod_cast hjJ
    refine ⟨f j, Finset.mem_image.2 ⟨j, by simp; omega, rfl⟩, f (j + 1),
      Finset.mem_image.2 ⟨j + 1, by simp; omega, rfl⟩, ?_, ?_, ?_⟩
    · simp only [f]
      exact (min_le_left _ _).trans (by linarith)
    · simp only [f]
      refine le_min ?_ ht.2
      push_cast
      linarith
    · simp only [f]
      have h3 : min (a + ((j : ℝ) + 1) * δ) b ≤ a + ((j : ℝ) + 1) * δ := min_le_left _ _
      have h4 : a + (j : ℝ) * δ ≤ b := by linarith [ht.2]
      have h5 : min (a + (j : ℝ) * δ) b = a + (j : ℝ) * δ := min_eq_left h4
      push_cast
      rw [h5]
      linarith
  · have hc : ((Finset.range (J + 2)).image f).card ≤ J + 2 :=
      Finset.card_image_le.trans (by simp)
    have : (((Finset.range (J + 2)).image f).card : ℝ) ≤ (J : ℝ) + 2 := by exact_mod_cast hc
    linarith

/-- From the grid `Gy` (spacing `N⁻⁴`) to every height in `[η, 1]`. -/
private lemma cl_ext_y {F : ℝ → ℝ} {N η Λ : ℝ} {Gy : Finset ℝ} (hN : 2 ≤ N) (hη : 1 / N ≤ η)
    (hΛ : 1 ≤ Λ)
    (hlip : ∀ y y' : ℝ, 0 < y → 0 < y' → F y ≤ F y' + 2 * |y - y'| / (y * y'))
    (hcov : ∀ y ∈ Set.Icc η 1, ∃ y' ∈ Gy, |y - y'| ≤ (N ^ 4)⁻¹)
    (hev : ∀ y' ∈ Gy, F y' ≤ Λ / (N * y')) :
    ∀ y ∈ Set.Icc η 1, F y ≤ 3 * Λ / (N * y) := by
  intro y hy
  have hNpos : (0 : ℝ) < N := by linarith
  have hηpos : 0 < η := lt_of_lt_of_le (by positivity) hη
  have hy0 : 0 < y := lt_of_lt_of_le hηpos hy.1
  obtain ⟨y', hy'G, hyy'⟩ := hcov y hy
  have hδ0 : 0 < (N ^ 4)⁻¹ := by positivity
  have hyN : 1 / N ≤ y := hη.trans hy.1
  have hN3 : (8 : ℝ) ≤ N ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hN 3
    norm_num at this
    exact this
  have hδ1 : (N ^ 4)⁻¹ ≤ 1 / (2 * N) := by
    rw [inv_eq_one_div]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hδy : (N ^ 4)⁻¹ ≤ y / 2 := by
    refine hδ1.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : 1 ≤ y * N := by
      have := mul_le_mul_of_nonneg_right hyN hNpos.le
      rwa [one_div, inv_mul_cancel₀ hNpos.ne'] at this
    nlinarith
  have hy'1 : y / 2 ≤ y' := by
    have := (abs_le.1 hyy').2
    linarith
  have hy'0 : 0 < y' := by linarith
  have h1 := hlip y y' hy0 hy'0
  have h2 := hev y' hy'G
  have hΛ0 : 0 ≤ Λ := by linarith
  -- the two terms
  have ha : Λ / (N * y') ≤ 2 * Λ / (N * y) := by
    calc Λ / (N * y') ≤ Λ / (N * (y / 2)) :=
          div_le_div_of_nonneg_left hΛ0 (by positivity) (by nlinarith)
      _ = 2 * Λ / (N * y) := by field_simp
  have hb : 2 * |y - y'| / (y * y') ≤ Λ / (N * y) := by
    have hnum : 2 * |y - y'| ≤ 2 * (N ^ 4)⁻¹ := by linarith
    calc 2 * |y - y'| / (y * y') ≤ 2 * (N ^ 4)⁻¹ / (y * (y / 2)) :=
          div_le_div₀ (by positivity) hnum (by positivity) (by nlinarith)
      _ ≤ Λ / (N * y) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have h4 : (N ^ 4)⁻¹ * N ^ 4 = 1 := inv_mul_cancel₀ (by positivity)
          have hyN' : 1 ≤ y * N := by
            have := mul_le_mul_of_nonneg_right hyN hNpos.le
            rwa [one_div, inv_mul_cancel₀ hNpos.ne'] at this
          have hN2 : (4 : ℝ) ≤ N ^ 2 := by nlinarith
          have h5 : (N ^ 4)⁻¹ * N ^ 3 = (N : ℝ)⁻¹ := by
            field_simp
          have h6 : 4 * (N ^ 4)⁻¹ * N ≤ 1 / N := by
            calc 4 * (N ^ 4)⁻¹ * N = 4 * (N ^ 4)⁻¹ * N ^ 3 / N ^ 2 := by field_simp
              _ = 4 * (N : ℝ)⁻¹ / N ^ 2 := by rw [mul_assoc, h5]
              _ ≤ 1 / N := by
                  rw [div_le_div_iff₀ (by positivity) hNpos]
                  field_simp
                  nlinarith
          nlinarith [mul_nonneg hy0.le hΛ0]
  calc F y ≤ F y' + 2 * |y - y'| / (y * y') := h1
    _ ≤ Λ / (N * y') + Λ / (N * y) := add_le_add h2 hb
    _ ≤ 2 * Λ / (N * y) + Λ / (N * y) := by linarith
    _ = 3 * Λ / (N * y) := by ring

/-- From the grid `Gx` (spacing `N⁻²`) to every real part in `[a, b]`, at height `1`. -/
private lemma cl_ext_x {F : ℝ → ℝ} {N Λ a b : ℝ} {Gx : Finset ℝ} (hN : 2 ≤ N) (hΛ : 1 ≤ Λ)
    (hlip : ∀ x x' : ℝ, F x ≤ F x' + 2 * |x - x'|)
    (hcov : ∀ x ∈ Set.Icc a b, ∃ x' ∈ Gx, |x - x'| ≤ (N ^ 2)⁻¹)
    (hev : ∀ x' ∈ Gx, F x' ≤ Λ / N) :
    ∀ x ∈ Set.Icc a b, F x ≤ 2 * Λ / N := by
  intro x hx
  have hNpos : (0 : ℝ) < N := by linarith
  obtain ⟨x', hx'G, hxx'⟩ := hcov x hx
  have h1 := hlip x x'
  have h2 := hev x' hx'G
  have h3 : 2 * |x - x'| ≤ Λ / N := by
    have h4 : 2 * |x - x'| ≤ 2 * (N ^ 2)⁻¹ := by linarith
    refine h4.trans ?_
    rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) hNpos]
    nlinarith [mul_nonneg hNpos.le (sub_nonneg.2 hΛ), mul_nonneg hNpos.le (sub_nonneg.2 hN)]
  calc F x ≤ F x' + 2 * |x - x'| := h1
    _ ≤ Λ / N + Λ / N := add_le_add h2 h3
    _ = 2 * Λ / N := by ring

/-! ## The segment identity for `s − m` -/

/-- `s` is continuous on `ℂ₊`. -/
private lemma cl_continuousOn_emp {K : ℕ} (lam : Fin K → ℝ) :
    ContinuousOn (empStieltjes lam) {z : ℂ | 0 < z.im} := by
  unfold empStieltjes
  refine continuousOn_const.mul (continuousOn_finsetSum _ fun j _ => ?_)
  refine ContinuousOn.inv₀ (continuousOn_const.sub continuousOn_id) fun z hz h => ?_
  have := congrArg Complex.im h
  simp at this
  have hz' : 0 < z.im := hz
  linarith

/-- `m` is continuous on `ℂ₊`. -/
private lemma cl_continuousOn_mFun (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) :
    ContinuousOn (mFun N σ) {z : ℂ | 0 < z.im} :=
  (analyticOnNhd_mFun N σ hσ).continuousOn

/-- `x ↦ F(x + iη)` is continuous for a function continuous on `ℂ₊` and `η > 0`. -/
private lemma cl_cont_horiz {F : ℂ → ℂ} (hF : ContinuousOn F {z : ℂ | 0 < z.im}) {η : ℝ}
    (hη : 0 < η) : Continuous fun x : ℝ => F (↑x + ↑η * Complex.I) :=
  hF.comp_continuous (Complex.continuous_ofReal.add continuous_const) fun x => by simpa using hη

/-- `y ↦ F(E + iy)` is continuous on `y > 0` for a function continuous on `ℂ₊`. -/
private lemma cl_cont_vert {F : ℂ → ℂ} (hF : ContinuousOn F {z : ℂ | 0 < z.im}) (E : ℝ) :
    ContinuousOn (fun y : ℝ => F (↑E + ↑y * Complex.I)) (Set.Ioi 0) :=
  hF.comp (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
    fun y hy => by simpa using hy

/-- The vertical-segment identity for `s − m`. -/
private lemma cl_d_segment (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) (lam : Fin N → ℝ)
    (E₁ E₂ η η₀ : ℝ) (hη : 0 < η) (hηη₀ : η ≤ η₀) :
    (∫ x in E₁..E₂, (empStieltjes lam (↑x + ↑η * Complex.I) -
        mFun N σ (↑x + ↑η * Complex.I)).im) =
      (∫ x in E₁..E₂, (empStieltjes lam (↑x + ↑η₀ * Complex.I) -
          mFun N σ (↑x + ↑η₀ * Complex.I)).im) -
        ∫ y in η..η₀, ((empStieltjes lam (↑E₂ + ↑y * Complex.I) -
            mFun N σ (↑E₂ + ↑y * Complex.I)).re -
          (empStieltjes lam (↑E₁ + ↑y * Complex.I) - mFun N σ (↑E₁ + ↑y * Complex.I)).re) := by
  have hη₀ : 0 < η₀ := hη.trans_le hηη₀
  have hS := cl_continuousOn_emp lam
  have hm := cl_continuousOn_mFun (N := N) σ hσ
  have hSi : ∀ h : ℝ, 0 < h → IntervalIntegrable
      (fun x : ℝ => (empStieltjes lam (↑x + ↑h * Complex.I)).im) volume E₁ E₂ := fun h hh =>
    (Complex.continuous_im.comp (cl_cont_horiz hS hh)).intervalIntegrable _ _
  have hmi : ∀ h : ℝ, 0 < h → IntervalIntegrable
      (fun x : ℝ => (mFun N σ (↑x + ↑h * Complex.I)).im) volume E₁ E₂ := fun h hh =>
    (Complex.continuous_im.comp (cl_cont_horiz hm hh)).intervalIntegrable _ _
  have hre : ∀ (F : ℂ → ℂ), ContinuousOn F {z : ℂ | 0 < z.im} → ∀ E : ℝ,
      IntervalIntegrable (fun y : ℝ => (F (↑E + ↑y * Complex.I)).re) volume η η₀ := by
    intro F hF E
    refine ContinuousOn.intervalIntegrable_of_Icc hηη₀ ?_
    exact (Complex.continuous_re.comp_continuousOn (cl_cont_vert hF E)).mono fun y hy =>
      lt_of_lt_of_le hη hy.1
  simp_rw [Complex.sub_im, Complex.sub_re]
  rw [intervalIntegral.integral_sub (hSi η hη) (hmi η hη),
    intervalIntegral.integral_sub (hSi η₀ hη₀) (hmi η₀ hη₀)]
  have hy : ∫ y in η..η₀, (((empStieltjes lam (↑E₂ + ↑y * Complex.I)).re -
        (mFun N σ (↑E₂ + ↑y * Complex.I)).re) -
        ((empStieltjes lam (↑E₁ + ↑y * Complex.I)).re -
          (mFun N σ (↑E₁ + ↑y * Complex.I)).re)) =
      (∫ y in η..η₀, ((empStieltjes lam (↑E₂ + ↑y * Complex.I)).re -
          (empStieltjes lam (↑E₁ + ↑y * Complex.I)).re)) -
        ∫ y in η..η₀, ((mFun N σ (↑E₂ + ↑y * Complex.I)).re -
          (mFun N σ (↑E₁ + ↑y * Complex.I)).re) := by
    rw [← intervalIntegral.integral_sub ((hre _ hS E₂).sub (hre _ hS E₁))
      ((hre _ hm E₂).sub (hre _ hm E₁))]
    refine intervalIntegral.integral_congr fun y _ => ?_
    ring
  rw [hy, segment_identity lam E₁ E₂ η η₀ hη hηη₀, segment_identity_m σ hσ hN E₁ E₂ η η₀ hη hηη₀]
  ring

/-! ## The count at a grid point -/

/-- `t ↦ η / (|t − E| + η)` is integrable against a finite measure. -/
private lemma cl_integrable_decay (μ : Measure ℝ) [IsFiniteMeasure μ] (E η : ℝ) (hη : 0 < η) :
    Integrable (fun x : ℝ => η / (|x - E| + η)) μ := by
  refine Integrable.of_bound ?_ 1 (ae_of_all _ fun t => ?_)
  · exact (continuous_const.div (by fun_prop) fun t => by positivity).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_le_one (by positivity)]
    linarith [abs_nonneg (t - E)]

/-- The dyadic bounds at one energy `E`: with `Im s ≤ C_m + 3Λ/(N y)` on the heights `2^l η ≤ 1`,
the smoothed counts are `O(Λ (L + 1))`. -/
private lemma cl_smooth_at (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) (lam : Fin N → ℝ)
    {E η Λ Cm : ℝ} (L : ℕ) (hη : 0 < η) (hΛ : Λ = N * η)
    (hB1 : ∀ y ∈ Set.Icc η 1,
        ‖empStieltjes lam (↑E + ↑y * Complex.I) - mFun N σ (↑E + ↑y * Complex.I)‖ ≤
          3 * Λ / (N * y))
    (hCm : ∀ y ∈ Set.Icc η 1, (mFun N σ (↑E + ↑y * Complex.I)).im ≤ Cm)
    (hL1 : 2 ^ L * η ≤ 1) (hL2 : 1 < 2 ^ (L + 1) * η) :
    ∑ j, η / (|lam j - E| + η) ≤ Λ * (4 * Cm * (L + 1) + 26) ∧
    ∫ x, η / (|x - E| + η) ∂(varrho N σ) ≤ η * (4 * Cm * (L + 1) + 2) := by
  have hprob := isProbabilityMeasure_varrho N σ hσ hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hΛ0 : 0 ≤ Λ := by rw [hΛ]; positivity
  have h2L : (0 : ℝ) < 2 ^ L := by positivity
  have hyl : ∀ l ∈ Finset.range (L + 1), 2 ^ l * η ∈ Set.Icc η 1 := by
    intro l hl
    have hl' : l ≤ L := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
    refine ⟨?_, ?_⟩
    · exact le_mul_of_one_le_left hη.le (one_le_pow₀ (by norm_num))
    · exact (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hl') hη.le).trans hL1
  have hone : 1 / 2 ^ L < 2 * η := by
    rw [div_lt_iff₀ h2L]
    nlinarith [pow_succ (2 : ℝ) L]
  -- the sum of the imaginary parts of `s`
  have hsum_s : ∑ l ∈ Finset.range (L + 1), (empStieltjes lam (↑E + ↑(2 ^ l * η) * Complex.I)).im ≤
      (L + 1) * Cm + 6 := by
    have hterm : ∀ l ∈ Finset.range (L + 1),
        (empStieltjes lam (↑E + ↑(2 ^ l * η) * Complex.I)).im ≤ Cm + 3 * (1 / 2) ^ l := by
      intro l hl
      have h1 := hB1 _ (hyl l hl)
      have h2 := hCm _ (hyl l hl)
      have h3 : (empStieltjes lam (↑E + ↑(2 ^ l * η) * Complex.I) -
          mFun N σ (↑E + ↑(2 ^ l * η) * Complex.I)).im ≤ 3 * Λ / (N * (2 ^ l * η)) :=
        (Complex.im_le_norm _).trans h1
      rw [Complex.sub_im] at h3
      have h4 : 3 * Λ / (N * (2 ^ l * η)) = 3 * (1 / 2) ^ l := by
        rw [hΛ, one_div, inv_pow]
        field_simp
      linarith
    calc ∑ l ∈ Finset.range (L + 1), (empStieltjes lam (↑E + ↑(2 ^ l * η) * Complex.I)).im
        ≤ ∑ l ∈ Finset.range (L + 1), (Cm + 3 * (1 / 2) ^ l) := Finset.sum_le_sum hterm
      _ = (L + 1) * Cm + 3 * ∑ l ∈ Finset.range (L + 1), (1 / 2 : ℝ) ^ l := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          simp
      _ ≤ (L + 1) * Cm + 3 * 2 := by
          have := sum_geometric_two_le (L + 1)
          linarith
      _ = (L + 1) * Cm + 6 := by ring
  have hsum_m : ∑ l ∈ Finset.range (L + 1), (mFun N σ (↑E + ↑(2 ^ l * η) * Complex.I)).im ≤
      (L + 1) * Cm := by
    calc ∑ l ∈ Finset.range (L + 1), (mFun N σ (↑E + ↑(2 ^ l * η) * Complex.I)).im
        ≤ ∑ l ∈ Finset.range (L + 1), Cm :=
          Finset.sum_le_sum fun l hl => hCm _ (hyl l hl)
      _ = (L + 1) * Cm := by simp
  constructor
  · have h1 := smooth_sum_le lam E η hη L
    have h4 : 4 * (N : ℝ) * η = 4 * Λ := by rw [hΛ]; ring
    have h5 : (N : ℝ) / 2 ^ L ≤ 2 * Λ := by
      rw [div_le_iff₀ h2L]
      have := mul_lt_mul_of_pos_left hone hNpos
      rw [mul_one_div] at this
      rw [hΛ]
      have h6 : (N : ℝ) / 2 ^ L * 2 ^ L = N := div_mul_cancel₀ _ h2L.ne'
      nlinarith
    calc ∑ j, η / (|lam j - E| + η)
        ≤ 4 * (N : ℝ) * η * ∑ l ∈ Finset.range (L + 1),
          (empStieltjes lam (↑E + ↑(2 ^ l * η) * Complex.I)).im + N / 2 ^ L := by
          simpa using h1
      _ ≤ 4 * Λ * ((L + 1) * Cm + 6) + 2 * Λ := by
          rw [h4]
          exact add_le_add (mul_le_mul_of_nonneg_left hsum_s (by positivity)) h5
      _ = Λ * (4 * Cm * (L + 1) + 26) := by ring
  · have h1 := smooth_int_le σ hσ hN E η hη L
    have hm' : (4 : ℝ) * η * ∑ l ∈ Finset.range (L + 1),
        (mFun N σ (↑E + ↑(2 ^ l * η) * Complex.I)).im ≤ 4 * η * ((L + 1) * Cm) :=
      mul_le_mul_of_nonneg_left hsum_m (by positivity)
    calc ∫ x, η / (|x - E| + η) ∂(varrho N σ)
        ≤ 4 * η * ∑ l ∈ Finset.range (L + 1),
          (mFun N σ (↑E + ↑(2 ^ l * η) * Complex.I)).im + 1 / 2 ^ L := h1
      _ ≤ 4 * η * ((L + 1) * Cm) + 2 * η := add_le_add hm' hone.le
      _ = η * (4 * Cm * (L + 1) + 2) := by ring

/-- The count at a grid point `E'`, from the bounds on `s − m` along the vertical lines over `E'`
and `E_top` and along the top segment (`count_compare` with `E₂ = E_top`, `η = N^{-1+ε'}`). -/
private lemma cl_count_grid (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) (lam : Fin N → ℝ)
    {E' Et η Λ Cm : ℝ} (L : ℕ) (hE' : 0 < E') (hE't : E' ≤ Et) (hη : 0 < η) (hη1 : η ≤ 1)
    (hΛ : Λ = N * η) (hΛ1 : 1 ≤ Λ) (hηN : 1 / (N : ℝ) ≤ η)
    (hanc : ∀ j, lam j < Et) (hnEt : nClass N σ Et = 0)
    (hB1 : ∀ E, (E = E' ∨ E = Et) → ∀ y ∈ Set.Icc η 1,
        ‖empStieltjes lam (↑E + ↑y * Complex.I) - mFun N σ (↑E + ↑y * Complex.I)‖ ≤
          3 * Λ / (N * y))
    (hB2 : ∀ x ∈ Set.Icc E' Et,
        ‖empStieltjes lam (↑x + ↑(1 : ℝ) * Complex.I) -
          mFun N σ (↑x + ↑(1 : ℝ) * Complex.I)‖ ≤ 2 * Λ / N)
    (hCm : ∀ E, (E = E' ∨ E = Et) → ∀ y ∈ Set.Icc η 1,
        (mFun N σ (↑E + ↑y * Complex.I)).im ≤ Cm)
    (hL1 : 2 ^ L * η ≤ 1) (hL2 : 1 < 2 ^ (L + 1) * η) :
    |((Finset.univ.filter fun j => E' ≤ lam j).card : ℝ) - nClass N σ E'| ≤
      (2 * Et + 6 * Real.log N) * Λ + (40 * Cm * (L + 1) + 164) * Λ := by
  have hprob := isProbabilityMeasure_varrho N σ hσ hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hΛ0 : 0 ≤ Λ := by linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hpi := Real.pi_gt_three
  -- the anchor
  have hcard : (Finset.univ.filter fun j => Et ≤ lam j).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro j _
    exact not_le.2 (hanc j)
  have hcc := count_compare σ hσ hN lam hη hE't hE'
  rw [hcard, hnEt] at hcc
  simp only [Nat.cast_zero, sub_zero] at hcc
  -- the segment term
  have hA : (N : ℝ) * |∫ x in E'..Et, (empStieltjes lam (↑x + ↑η * Complex.I) -
        mFun N σ (↑x + ↑η * Complex.I)).im| / Real.pi ≤ (2 * Et + 6 * Real.log N) * Λ := by
    rw [cl_d_segment σ hσ hN lam E' Et η 1 hη hη1]
    have h1 : |∫ x in E'..Et, (empStieltjes lam (↑x + ↑(1 : ℝ) * Complex.I) -
        mFun N σ (↑x + ↑(1 : ℝ) * Complex.I)).im| ≤ 2 * Λ / N * (Et - E') := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := E') (b := Et)
        (C := 2 * Λ / N) (f := fun x : ℝ => (empStieltjes lam (↑x + ↑(1 : ℝ) * Complex.I) -
          mFun N σ (↑x + ↑(1 : ℝ) * Complex.I)).im) (fun x hx => by
        rw [Set.uIoc_of_le hE't] at hx
        rw [Real.norm_eq_abs]
        exact (Complex.abs_im_le_norm _).trans (hB2 x ⟨hx.1.le, hx.2⟩))
      rwa [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ Et - E') ] at this
    have h2 : |∫ y in η..1, ((empStieltjes lam (↑Et + ↑y * Complex.I) -
          mFun N σ (↑Et + ↑y * Complex.I)).re -
        (empStieltjes lam (↑E' + ↑y * Complex.I) - mFun N σ (↑E' + ↑y * Complex.I)).re)| ≤
        6 * Λ / N * Real.log (1 / η) := by
      have hint : IntervalIntegrable (fun y : ℝ => 6 * Λ / N * y⁻¹) volume η 1 := by
        refine ContinuousOn.intervalIntegrable ?_
        exact continuousOn_const.mul (continuousOn_inv₀.mono fun y hy => by
          have := hy.1
          have h0 : 0 < η := hη
          rw [Set.uIcc_of_le hη1] at hy
          exact (lt_of_lt_of_le hη hy.1).ne')
      have := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hη1
        (f := fun y : ℝ => ((empStieltjes lam (↑Et + ↑y * Complex.I) -
          mFun N σ (↑Et + ↑y * Complex.I)).re -
        (empStieltjes lam (↑E' + ↑y * Complex.I) - mFun N σ (↑E' + ↑y * Complex.I)).re))
        (g := fun y : ℝ => 6 * Λ / N * y⁻¹) (ae_of_all _ fun y hy => by
          have hy' : y ∈ Set.Icc η 1 := ⟨hy.1.le, hy.2⟩
          have hy0 : 0 < y := lt_of_lt_of_le hη hy'.1
          have h3 := hB1 Et (Or.inr rfl) y hy'
          have h4 := hB1 E' (Or.inl rfl) y hy'
          have h5 := (Complex.abs_re_le_norm _).trans h3
          have h6 := (Complex.abs_re_le_norm _).trans h4
          rw [Real.norm_eq_abs]
          refine (abs_sub _ _).trans ?_
          have : 6 * Λ / N * y⁻¹ = 3 * Λ / (N * y) + 3 * Λ / (N * y) := by
            field_simp
            ring
          rw [this]
          exact add_le_add h5 h6) hint
      rw [Real.norm_eq_abs] at this
      refine this.trans (le_of_eq ?_)
      rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hη one_pos]
    have hlog : Real.log (1 / η) ≤ Real.log N := by
      refine Real.log_le_log (by positivity) ?_
      rw [div_le_iff₀ hη]
      have := mul_le_mul_of_nonneg_right hηN hNpos.le
      rw [one_div, inv_mul_cancel₀ hNpos.ne'] at this
      linarith
    have hb : |(∫ x in E'..Et, (empStieltjes lam (↑x + ↑(1 : ℝ) * Complex.I) -
        mFun N σ (↑x + ↑(1 : ℝ) * Complex.I)).im) -
        ∫ y in η..1, ((empStieltjes lam (↑Et + ↑y * Complex.I) -
          mFun N σ (↑Et + ↑y * Complex.I)).re -
        (empStieltjes lam (↑E' + ↑y * Complex.I) - mFun N σ (↑E' + ↑y * Complex.I)).re)| ≤
        2 * Λ / N * Et + 6 * Λ / N * Real.log N := by
      refine (abs_sub _ _).trans ?_
      have h7 : 2 * Λ / N * (Et - E') ≤ 2 * Λ / N * Et := by
        have : 0 ≤ 2 * Λ / N := by positivity
        nlinarith
      have h8 : 6 * Λ / N * Real.log (1 / η) ≤ 6 * Λ / N * Real.log N :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      linarith
    have hgen : ∀ a B : ℝ, |a| ≤ B → (N : ℝ) * |a| / Real.pi ≤ N * B := fun a B h =>
      (div_le_self (by positivity) (by linarith)).trans (mul_le_mul_of_nonneg_left h hNpos.le)
    refine (hgen _ _ hb).trans (le_of_eq ?_)
    field_simp
  -- the smoothing terms
  have hs1 := cl_smooth_at σ hσ hN lam (E := E') L hη hΛ (hB1 E' (Or.inl rfl))
    (hCm E' (Or.inl rfl)) hL1 hL2
  have hs2 := cl_smooth_at σ hσ hN lam (E := Et) L hη hΛ (hB1 Et (Or.inr rfl))
    (hCm Et (Or.inr rfl)) hL1 hL2
  have hB : 3 * ∑ j, (η / (|lam j - E'| + η) + η / (|lam j - Et| + η)) ≤
      Λ * (24 * Cm * (L + 1) + 156) := by
    rw [Finset.sum_add_distrib]
    nlinarith [hs1.1, hs2.1]
  have hC : 2 * (N : ℝ) * ∫ x, (η / (|x - E'| + η) + η / (|x - Et| + η)) ∂(varrho N σ) ≤
      Λ * (16 * Cm * (L + 1) + 8) := by
    rw [integral_add (cl_integrable_decay _ E' η hη) (cl_integrable_decay _ Et η hη)]
    have h1 := hs1.2
    have h2 := hs2.2
    have h4 := mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity : (0 : ℝ) ≤ 2 * N)
    refine h4.trans (le_of_eq ?_)
    rw [hΛ]
    ring
  calc |((Finset.univ.filter fun j => E' ≤ lam j).card : ℝ) - nClass N σ E'|
      ≤ _ := hcc
    _ ≤ (2 * Et + 6 * Real.log N) * Λ + Λ * (24 * Cm * (L + 1) + 156) +
        Λ * (16 * Cm * (L + 1) + 8) := add_le_add (add_le_add hA hB) hC
    _ = (2 * Et + 6 * Real.log N) * Λ + (40 * Cm * (L + 1) + 164) * Λ := by ring

/-! ## From the grid to every energy -/

/-- A dyadic exponent `L` with `2^L η ≤ 1 < 2^{L+1} η`, and `L ≤ 2 log N`. -/
private lemma cl_exists_L {η N : ℝ} (hN : 1 ≤ N) (hη : 0 < η) (hη1 : η ≤ 1) (hηN : 1 / N ≤ η) :
    ∃ L : ℕ, 2 ^ L * η ≤ 1 ∧ 1 < 2 ^ (L + 1) * η ∧ (L : ℝ) ≤ 2 * Real.log N := by
  obtain ⟨L, h1, h2⟩ := exists_nat_pow_near (x := 1 / η) (y := (2 : ℝ)) (one_le_one_div hη hη1)
    (by norm_num)
  have hNpos : 0 < N := by linarith
  refine ⟨L, ?_, ?_, ?_⟩
  · rwa [le_div_iff₀ hη] at h1
  · rwa [div_lt_iff₀ hη] at h2
  · have h3 : (2 : ℝ) ^ L ≤ N := by
      refine h1.trans ?_
      rw [div_le_iff₀ hη]
      have := mul_le_mul_of_nonneg_left hηN hNpos.le
      rw [mul_one_div, div_self hNpos.ne'] at this
      linarith
    have h4 := Real.log_le_log (by positivity) h3
    rw [Real.log_pow] at h4
    have h5 := Real.log_two_gt_d9
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    nlinarith

/-- `‖d(E + iy)‖ ≤ ‖d(E + iy')‖ + 2|y − y'|/(y y')`. -/
private lemma cl_lip_y (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) (lam : Fin N → ℝ)
    (E : ℝ) {y y' : ℝ} (hy : 0 < y) (hy' : 0 < y') :
    ‖empStieltjes lam (↑E + ↑y * Complex.I) - mFun N σ (↑E + ↑y * Complex.I)‖ ≤
      ‖empStieltjes lam (↑E + ↑y' * Complex.I) - mFun N σ (↑E + ↑y' * Complex.I)‖ +
        2 * |y - y'| / (y * y') := by
  have h := cl_lip_d σ hσ hN lam (z := ↑E + ↑y * Complex.I) (w := ↑E + ↑y' * Complex.I)
    (by simpa using hy) (by simpa using hy')
  have e1 : ‖(↑E + ↑y * Complex.I) - (↑E + ↑y' * Complex.I)‖ = |y - y'| := by
    have : (↑E + ↑y * Complex.I) - (↑E + ↑y' * Complex.I) = ((y - y' : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add] at h
  rw [e1] at h
  have := norm_le_norm_add_norm_sub' (empStieltjes lam (↑E + ↑y * Complex.I) -
    mFun N σ (↑E + ↑y * Complex.I)) (empStieltjes lam (↑E + ↑y' * Complex.I) -
    mFun N σ (↑E + ↑y' * Complex.I))
  linarith

/-- `‖d(x + i)‖ ≤ ‖d(x' + i)‖ + 2|x − x'|`. -/
private lemma cl_lip_x (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) (lam : Fin N → ℝ)
    (x x' : ℝ) :
    ‖empStieltjes lam (↑x + ↑(1 : ℝ) * Complex.I) - mFun N σ (↑x + ↑(1 : ℝ) * Complex.I)‖ ≤
      ‖empStieltjes lam (↑x' + ↑(1 : ℝ) * Complex.I) -
        mFun N σ (↑x' + ↑(1 : ℝ) * Complex.I)‖ + 2 * |x - x'| := by
  have h := cl_lip_d σ hσ hN lam (z := ↑x + ↑(1 : ℝ) * Complex.I)
    (w := ↑x' + ↑(1 : ℝ) * Complex.I) (by simp) (by simp)
  have e1 : ‖(↑x + ↑(1 : ℝ) * Complex.I) - (↑x' + ↑(1 : ℝ) * Complex.I)‖ = |x - x'| := by
    have : (↑x + ↑(1 : ℝ) * Complex.I) - (↑x' + ↑(1 : ℝ) * Complex.I) = ((x - x' : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add] at h
  rw [e1] at h
  have := norm_le_norm_add_norm_sub' (empStieltjes lam (↑x + ↑(1 : ℝ) * Complex.I) -
    mFun N σ (↑x + ↑(1 : ℝ) * Complex.I)) (empStieltjes lam (↑x' + ↑(1 : ℝ) * Complex.I) -
    mFun N σ (↑x' + ↑(1 : ℝ) * Complex.I))
  linarith

/-- The deterministic count: bounds on `s − m` on the grid points give `|n_N(E) − n(E)|` for every
`E ∈ [E₁, E₂]` (monotonicity of `n_N` and `n`, and `n(g) − n(g') ≤ 2 C_m / N` for
`g' − g ≤ N⁻²`). -/
private lemma cl_det (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 2 ≤ N) (lam : Fin N → ℝ)
    {τ E₁ E₂ Et η Λ Cm : ℝ} (hτ : 0 < τ) (hE₁ : τ ≤ E₁) (hE₂t : E₂ ≤ Et)
    (hη : 0 < η) (hη1 : η ≤ 1) (hΛ : Λ = N * η) (hΛ1 : 1 ≤ Λ) (hηN : 1 / (N : ℝ) ≤ η)
    (hCm0 : 0 ≤ Cm) (GE Gy Gx : Finset ℝ)
    (hGE : ∀ g ∈ GE, g ∈ Set.Icc E₁ E₂)
    (hGEc : ∀ E ∈ Set.Icc E₁ E₂, ∃ g ∈ GE, ∃ g' ∈ GE, g ≤ E ∧ E ≤ g' ∧
      g' - g ≤ ((N : ℝ) ^ 2)⁻¹)
    (hGyc : ∀ y ∈ Set.Icc η 1, ∃ y' ∈ Gy, |y - y'| ≤ ((N : ℝ) ^ 4)⁻¹)
    (hGxc : ∀ x ∈ Set.Icc E₁ Et, ∃ x' ∈ Gx, |x - x'| ≤ ((N : ℝ) ^ 2)⁻¹)
    (hanc : ∀ j, lam j < Et) (hnEt : nClass N σ Et = 0)
    (hCm : ∀ x y : ℝ, τ ≤ x → x ≤ Et → 0 < y → y ≤ 1 →
      (mFun N σ (↑x + ↑y * Complex.I)).im ≤ Cm)
    (hev1 : ∀ E ∈ GE, ∀ y ∈ Gy,
      ‖empStieltjes lam (↑E + ↑y * Complex.I) - mFun N σ (↑E + ↑y * Complex.I)‖ ≤
        Λ / (N * y))
    (hev2 : ∀ y ∈ Gy,
      ‖empStieltjes lam (↑Et + ↑y * Complex.I) - mFun N σ (↑Et + ↑y * Complex.I)‖ ≤
        Λ / (N * y))
    (hev3 : ∀ x ∈ Gx,
      ‖empStieltjes lam (↑x + ↑(1 : ℝ) * Complex.I) -
        mFun N σ (↑x + ↑(1 : ℝ) * Complex.I)‖ ≤ Λ / N) :
    ∀ E ∈ Set.Icc E₁ E₂, |((Finset.univ.filter fun j => E ≤ lam j).card : ℝ) - nClass N σ E| ≤
      (2 * Et + 170 + 120 * Cm) * (1 + Real.log N) * Λ + 2 * Cm / N := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : 0 < N := by omega
  have hNpos : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hΛ0 : 0 ≤ Λ := by linarith
  have := isProbabilityMeasure_varrho N σ hσ hN0
  -- the bounds along every vertical line and along the whole top segment
  have hB1 : ∀ E, (E ∈ GE ∨ E = Et) → ∀ y ∈ Set.Icc η 1,
      ‖empStieltjes lam (↑E + ↑y * Complex.I) - mFun N σ (↑E + ↑y * Complex.I)‖ ≤
        3 * Λ / (N * y) := by
    intro E hE
    refine cl_ext_y (F := fun y => ‖empStieltjes lam (↑E + ↑y * Complex.I) -
      mFun N σ (↑E + ↑y * Complex.I)‖) (Gy := Gy) hN2 hηN hΛ1
      (fun y y' hy hy' => cl_lip_y σ hσ hN0 lam E hy hy') hGyc ?_
    intro y' hy'
    rcases hE with hE | rfl
    · exact hev1 E hE y' hy'
    · exact hev2 y' hy'
  have hB2 : ∀ x ∈ Set.Icc E₁ Et, ‖empStieltjes lam (↑x + ↑(1 : ℝ) * Complex.I) -
      mFun N σ (↑x + ↑(1 : ℝ) * Complex.I)‖ ≤ 2 * Λ / N :=
    cl_ext_x (F := fun x => ‖empStieltjes lam (↑x + ↑(1 : ℝ) * Complex.I) -
      mFun N σ (↑x + ↑(1 : ℝ) * Complex.I)‖) (Gx := Gx) hN2 hΛ1
      (fun x x' => cl_lip_x σ hσ hN0 lam x x') hGxc hev3
  obtain ⟨L, hL1, hL2, hLlog⟩ := cl_exists_L hN1 hη hη1 hηN
  -- the count at the grid points
  have hgrid : ∀ g ∈ GE, |((Finset.univ.filter fun j => g ≤ lam j).card : ℝ) - nClass N σ g| ≤
      (2 * Et + 170 + 120 * Cm) * (1 + Real.log N) * Λ := by
    intro g hg
    have hg' := hGE g hg
    have hτg : τ ≤ g := hE₁.trans hg'.1
    have hgEt : g ≤ Et := hg'.2.trans hE₂t
    have h := cl_count_grid σ hσ hN0 lam (E' := g) (Et := Et) (η := η) (Λ := Λ) (Cm := Cm) L
      (lt_of_lt_of_le hτ hτg) hgEt hη hη1 hΛ hΛ1 hηN hanc hnEt
      (fun E hE y hy => hB1 E (by rcases hE with rfl | rfl; exacts [Or.inl hg, Or.inr rfl]) y hy)
      (fun x hx => hB2 x ⟨hg'.1.trans hx.1, hx.2⟩)
      (fun E hE y hy => hCm E y
        (by rcases hE with rfl | rfl; exacts [hτg, hτg.trans hgEt]) 
        (by rcases hE with rfl | rfl; exacts [hgEt, le_rfl]) (lt_of_lt_of_le hη hy.1) hy.2)
      hL1 hL2
    refine h.trans ?_
    have hEt0 : 0 ≤ Et := by linarith [hτg, hgEt]
    have h1 : 40 * Cm * ((L : ℝ) + 1) ≤ 40 * Cm * (2 * Real.log N + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : (2 * Et + 6 * Real.log N) + (40 * Cm * ((L : ℝ) + 1) + 164) ≤
        (2 * Et + 170 + 120 * Cm) * (1 + Real.log N) := by
      nlinarith [mul_nonneg hCm0 hlogN, mul_nonneg hEt0 hlogN]
    calc (2 * Et + 6 * Real.log N) * Λ + (40 * Cm * ((L : ℝ) + 1) + 164) * Λ
        = ((2 * Et + 6 * Real.log N) + (40 * Cm * ((L : ℝ) + 1) + 164)) * Λ := by ring
      _ ≤ (2 * Et + 170 + 120 * Cm) * (1 + Real.log N) * Λ :=
          mul_le_mul_of_nonneg_right h2 hΛ0
  -- from the grid to every energy
  intro E hE
  obtain ⟨g, hg, g', hg', hgE, hEg', hgg'⟩ := hGEc E hE
  have hgg'le : g ≤ g' := hgE.trans hEg'
  have hc1 : ((Finset.univ.filter fun j => g' ≤ lam j).card : ℝ) ≤
      (Finset.univ.filter fun j => E ≤ lam j).card := by
    exact_mod_cast Finset.card_le_card fun j hj => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact hEg'.trans hj
  have hc2 : ((Finset.univ.filter fun j => E ≤ lam j).card : ℝ) ≤
      (Finset.univ.filter fun j => g ≤ lam j).card := by
    exact_mod_cast Finset.card_le_card fun j hj => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact hgE.trans hj
  have hn1 : nClass N σ g' ≤ nClass N σ E := cl_nClass_anti σ hσ hN0 hEg'
  have hn2 : nClass N σ E ≤ nClass N σ g := cl_nClass_anti σ hσ hN0 hgE
  have hdrop : nClass N σ g - nClass N σ g' ≤ 2 * Cm / N := by
    rw [cl_nClass_sub σ hσ hN0 hgg'le]
    have hδ0 : 0 < ((N : ℝ) ^ 2)⁻¹ := by positivity
    have hδ1 : ((N : ℝ) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hN1)
    have hg1 := hGE g hg
    have h1 : (varrho N σ (Set.Ico g g')).toReal ≤
        (varrho N σ (Set.Icc g (g + ((N : ℝ) ^ 2)⁻¹))).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _)
        (measure_mono fun u hu => ⟨hu.1, by linarith [hu.2]⟩)
    have h2 := cl_varrho_Icc_le σ hσ hN0 g hδ0
    have h3 := hCm g ((N : ℝ) ^ 2)⁻¹ (hE₁.trans hg1.1) (hg1.2.trans hE₂t) hδ0 hδ1
    calc (N : ℝ) * (varrho N σ (Set.Ico g g')).toReal
        ≤ N * (2 * ((N : ℝ) ^ 2)⁻¹ * Cm) :=
          mul_le_mul_of_nonneg_left (h1.trans (h2.trans
            (mul_le_mul_of_nonneg_left h3 (by positivity)))) hNpos.le
      _ = 2 * Cm / N := by field_simp
  have hgb := hgrid g hg
  have hgb' := hgrid g' hg'
  rw [abs_le] at hgb hgb' ⊢
  constructor <;> linarith [hgb.1, hgb.2, hgb'.1, hgb'.2]

/-! ## The anchor: `‖Σ‖`, the top of the spectrum, `n(E_top) = 0` -/

/-- (phi_bounded) and (Sigma_gap) give `N > 0`, `M > 0` and some positive `σ i`. -/
private lemma cl_facts {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) :
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

/-- `n(E) = 0` for `E` above the bound `2τ⁻¹(1 + τ⁻¹)` of the edges. -/
private lemma cl_nClass_top {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) {E : ℝ}
    (hE : 2 * τ⁻¹ * (1 + τ⁻¹) < E) : nClass N σ E = 0 := by
  obtain ⟨hN, -, hS⟩ := cl_facts h
  have hnb := (card_innerCrit N σ h.nonneg hN hS).2
  have ha := (edgeVal_mem_Icc N σ h.nonneg hN hS h.pos h.phi_lower h.phi_upper h.bound_Sigma
    (k := 1) le_rfl (by omega)).2
  have h0 : varrho N σ (Set.Ici E) = 0 :=
    measure_mono_null (t := (Set.Icc 0 (edgeVal N σ 1))ᶜ)
      (fun x hx h => absurd (lt_of_lt_of_le (ha.trans_lt hE) hx) (not_lt.mpr h.2))
      (varrho_compl_Icc_edgeVal N σ h.nonneg hN hS)
  unfold nClass
  rw [h0]
  simp

/-- `‖Σ‖ ≤ τ⁻¹` under (bound_Sigma) (L2 operator norm). -/
private lemma cl_norm_sig_le {τ : ℝ} (hτ : 0 < τ) {Sig : Matrix (Fin M) (Fin M) ℝ}
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

/-- Every eigenvalue of `Q_N = XᵀΣX` is at most `τ⁻¹ ‖XᵀX‖` under (bound_Sigma). -/
private lemma cl_eig_le {τ : ℝ} (hτ : 0 < τ) {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hS : SigmaAssumption τ Sig) (Xm : Matrix (Fin M) (Fin N) ℝ) (j : Fin N) :
    specOf (QN Sig Xm) j ≤ τ⁻¹ * ‖Xmᵀ * Xm‖ := by
  have hQ : (QN Sig Xm).IsHermitian := by
    have := isHermitian_conjTranspose_mul_mul Xm hS.posDef.isHermitian
    simpa [QN, conjTranspose_eq_transpose_of_trivial] using this
  rw [specOf_eq hQ]
  have : Nonempty (Fin N) := ⟨j⟩
  have : NormOneClass (Matrix (Fin N) (Fin N) ℝ) :=
    ⟨by rw [← diagonal_one, l2_opNorm_diagonal]; exact norm_one⟩
  have : CompleteSpace (Matrix (Fin N) (Fin N) ℝ) := FiniteDimensional.complete ℝ _
  have h1 : hQ.eigenvalues j ≤ ‖QN Sig Xm‖ := by
    have := spectrum.norm_le_norm_of_mem (hQ.eigenvalues_mem_spectrum_real j)
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using this)
  refine h1.trans ?_
  have hT : ‖Xmᵀ‖ = ‖Xm‖ := by
    rw [← conjTranspose_eq_transpose_of_trivial, l2_opNorm_conjTranspose]
  have hXX : ‖Xmᵀ * Xm‖ = ‖Xm‖ * ‖Xm‖ := by
    rw [← conjTranspose_eq_transpose_of_trivial, l2_opNorm_conjTranspose_mul_self]
  have hSn := cl_norm_sig_le hτ hS
  calc ‖QN Sig Xm‖ ≤ ‖Xmᵀ * Sig‖ * ‖Xm‖ := l2_opNorm_mul _ _
    _ ≤ (‖Xmᵀ‖ * ‖Sig‖) * ‖Xm‖ := mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _)
    _ ≤ (‖Xm‖ * τ⁻¹) * ‖Xm‖ := by rw [hT]; gcongr
    _ = τ⁻¹ * ‖Xmᵀ * Xm‖ := by rw [hXX]; ring

/-- The probability bookkeeping: `c` events of probability `N^{-(D+8)}`, `c ≤ N⁷`, and one of
probability `N^{-(D+1)}` have union of probability at most `N^{-D}`. -/
private lemma cl_ofReal_arith {N : ℕ} (hN : 2 ≤ N) (D : ℝ) {c : ℕ} (hc : (c : ℝ) ≤ (N : ℝ) ^ 7) :
    (c : ℝ≥0∞) * ENNReal.ofReal ((N : ℝ) ^ (-(D + 8))) + ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) ≤
      ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have h1 : (N : ℝ) ^ (-(D + 1)) = (N : ℝ) ^ (7 : ℕ) * (N : ℝ) ^ (-(D + 8)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hNpos]
    congr 1
    push_cast
    ring
  have h2 : (N : ℝ) ^ (-D) = (N : ℝ) ^ (-(D + 1)) * N := by
    have := Real.rpow_add hNpos (-(D + 1)) 1
    rw [Real.rpow_one] at this
    rw [← this]
    congr 1
    ring
  have hp : 0 ≤ (N : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg hNpos.le _
  calc (c : ℝ≥0∞) * ENNReal.ofReal ((N : ℝ) ^ (-(D + 8))) +
        ENNReal.ofReal ((N : ℝ) ^ (-(D + 1)))
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) := by
        refine add_le_add ?_ le_rfl
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        rw [h1]
        exact mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hNpos.le _)
    _ = ENNReal.ofReal (2 * (N : ℝ) ^ (-(D + 1))) := by
        rw [← ENNReal.ofReal_add hp hp]
        ring_nf
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [h2]
        nlinarith

/-! ## The probabilistic count -/

/-- The count at fixed `N`, given the averaged law at the points of the three families
(the vertical lines over `[E₁, E₂]`, the vertical line over `E_top`, the top segment) and the norm
event: a union bound over grids of spacing `N⁻⁴` and `N⁻²`. -/
private lemma cl_count_main {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (hN : 2 ≤ N) {M : ℕ} (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ)
    {τ : ℝ} {C : ℕ → ℝ} (hm : IsModel τ C M N Sig X) (hτ : 0 < τ)
    {E₁ E₂ Et η Λ Cm C₀ ε D : ℝ} (hE₁ : τ ≤ E₁) (hE₂ : E₂ ≤ τ⁻¹) (hE₂t : E₂ ≤ Et)
    (hEt1 : 2 * τ⁻¹ * (1 + τ⁻¹) < Et) (hEt2 : τ⁻¹ * C₀ < Et)
    (hη : 0 < η) (hη1 : η ≤ 1) (hΛ : Λ = N * η) (hΛ1 : 1 ≤ Λ) (hηN : 1 / (N : ℝ) ≤ η)
    (hCm0 : 0 ≤ Cm)
    (hCm : ∀ x y : ℝ, τ ≤ x → x ≤ Et → 0 < y → y ≤ 1 →
      (mFun N (specOf Sig) (↑x + ↑y * Complex.I)).im ≤ Cm)
    (hlaw1 : ∀ E ∈ Set.Icc E₁ E₂, ∀ y ∈ Set.Icc η 1, ℙ {ω | Λ * (1 / (N * y)) <
      ‖mN Sig (X ω) (↑E + ↑y * Complex.I) - mFun N (specOf Sig) (↑E + ↑y * Complex.I)‖} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-(D + 8))))
    (hlaw2 : ∀ y ∈ Set.Icc η 1, ℙ {ω | Λ * (1 / (N * y)) <
      ‖mN Sig (X ω) (↑Et + ↑y * Complex.I) - mFun N (specOf Sig) (↑Et + ↑y * Complex.I)‖} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-(D + 8))))
    (hlaw3 : ∀ x ∈ Set.Icc E₁ Et, ℙ {ω | Λ * (1 / (N * (1 : ℝ))) <
      ‖mN Sig (X ω) (↑x + ↑(1 : ℝ) * Complex.I) -
        mFun N (specOf Sig) (↑x + ↑(1 : ℝ) * Complex.I)‖} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-(D + 8))))
    (hnorm : ℙ {ω | ¬ ‖(X ω)ᵀ * X ω‖ ≤ C₀} ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))))
    (hcnt : (τ⁻¹ * (N : ℝ) ^ 2 + 3) * ((N : ℝ) ^ 4 + 3) + ((N : ℝ) ^ 4 + 3) +
      (Et * (N : ℝ) ^ 2 + 3) ≤ (N : ℝ) ^ 7)
    (hfin : (2 * Et + 170 + 120 * Cm) * (1 + Real.log N) * Λ + 2 * Cm / N ≤ (N : ℝ) ^ ε) :
    HighProbAt N D {ω | ∀ E ∈ Set.Icc E₁ E₂,
      |(eigCount (QN Sig (X ω)) E : ℝ) - nClass N (specOf Sig) E| ≤ (N : ℝ) ^ ε} := by
  by_cases h12 : E₁ ≤ E₂
  swap
  · have : {ω | ∀ E ∈ Set.Icc E₁ E₂,
        |(eigCount (QN Sig (X ω)) E : ℝ) - nClass N (specOf Sig) E| ≤ (N : ℝ) ^ ε}ᶜ = ∅ := by
      ext ω
      simp [Set.Icc_eq_empty h12]
    unfold HighProbAt
    rw [this]
    simp
  have hN0 : 0 < N := by omega
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hda : DensityAssumptions τ N (specOf Sig) := hm.diagModel_specOf.densityAssumptions hτ
  have hσ := hda.nonneg
  have hnEt : nClass N (specOf Sig) Et = 0 := cl_nClass_top hda hEt1
  -- the grids
  have hδ2 : (0 : ℝ) < ((N : ℝ) ^ 2)⁻¹ := by positivity
  have hδ4 : (0 : ℝ) < ((N : ℝ) ^ 4)⁻¹ := by positivity
  have hExt : E₁ ≤ Et := h12.trans hE₂t
  obtain ⟨GE, hGE, hGEc, hGEcard⟩ := cl_exists_grid hδ2 h12
  obtain ⟨Gy, hGy, hGyc', hGycard⟩ := cl_exists_grid hδ4 hη1
  obtain ⟨Gx, hGx, hGxc', hGxcard⟩ := cl_exists_grid hδ2 hExt
  have hGyc : ∀ y ∈ Set.Icc η 1, ∃ y' ∈ Gy, |y - y'| ≤ ((N : ℝ) ^ 4)⁻¹ := fun y hy => by
    obtain ⟨g, hg, g', hg', h1, h2, h3⟩ := hGyc' y hy
    exact ⟨g, hg, by rw [abs_of_nonneg (by linarith)]; linarith⟩
  have hGxc : ∀ x ∈ Set.Icc E₁ Et, ∃ x' ∈ Gx, |x - x'| ≤ ((N : ℝ) ^ 2)⁻¹ := fun x hx => by
    obtain ⟨g, hg, g', hg', h1, h2, h3⟩ := hGxc' x hx
    exact ⟨g, hg, by rw [abs_of_nonneg (by linarith)]; linarith⟩
  -- the number of grid points
  have hGEc' : (GE.card : ℝ) ≤ τ⁻¹ * (N : ℝ) ^ 2 + 3 := by
    refine hGEcard.trans ?_
    rw [div_inv_eq_mul]
    have : E₂ - E₁ ≤ τ⁻¹ := by linarith [hτ]
    nlinarith [sq_nonneg (N : ℝ)]
  have hGyc2 : (Gy.card : ℝ) ≤ (N : ℝ) ^ 4 + 3 := by
    refine hGycard.trans ?_
    rw [div_inv_eq_mul]
    nlinarith [pow_nonneg hNpos.le 4]
  have hGxc2 : (Gx.card : ℝ) ≤ Et * (N : ℝ) ^ 2 + 3 := by
    refine hGxcard.trans ?_
    rw [div_inv_eq_mul]
    have : Et - E₁ ≤ Et := by linarith [hτ]
    nlinarith [sq_nonneg (N : ℝ)]
  have hc : ((((GE ×ˢ Gy).card + Gy.card + Gx.card : ℕ)) : ℝ) ≤ (N : ℝ) ^ 7 := by
    refine le_trans ?_ hcnt
    push_cast
    rw [Finset.card_product]
    push_cast
    have h1 : (GE.card : ℝ) * Gy.card ≤ (τ⁻¹ * (N : ℝ) ^ 2 + 3) * ((N : ℝ) ^ 4 + 3) :=
      mul_le_mul hGEc' hGyc2 (Nat.cast_nonneg _) (by positivity)
    linarith
  -- the bad events
  set δ' : ℝ≥0∞ := ENNReal.ofReal ((N : ℝ) ^ (-(D + 8))) with hδ'
  let B1 : ℝ × ℝ → Set Ω := fun p => {ω | Λ * (1 / (N * p.2)) <
    ‖mN Sig (X ω) (↑p.1 + ↑p.2 * Complex.I) - mFun N (specOf Sig) (↑p.1 + ↑p.2 * Complex.I)‖}
  let B2 : ℝ → Set Ω := fun y => {ω | Λ * (1 / (N * y)) <
    ‖mN Sig (X ω) (↑Et + ↑y * Complex.I) - mFun N (specOf Sig) (↑Et + ↑y * Complex.I)‖}
  let B3 : ℝ → Set Ω := fun x => {ω | Λ * (1 / (N * (1 : ℝ))) <
    ‖mN Sig (X ω) (↑x + ↑(1 : ℝ) * Complex.I) -
      mFun N (specOf Sig) (↑x + ↑(1 : ℝ) * Complex.I)‖}
  have hU1 : ℙ (⋃ p ∈ GE ×ˢ Gy, B1 p) ≤ ((GE ×ˢ Gy).card : ℝ≥0∞) * δ' := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ δ' fun p hp => ?_).trans (by rw [nsmul_eq_mul])
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.1 hp
    exact hlaw1 p.1 (hGE p.1 hp1) p.2 (hGy p.2 hp2)
  have hU2 : ℙ (⋃ y ∈ Gy, B2 y) ≤ (Gy.card : ℝ≥0∞) * δ' := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ δ' fun y hy => ?_).trans (by rw [nsmul_eq_mul])
    exact hlaw2 y (hGy y hy)
  have hU3 : ℙ (⋃ x ∈ Gx, B3 x) ≤ (Gx.card : ℝ≥0∞) * δ' := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ δ' fun x hx => ?_).trans (by rw [nsmul_eq_mul])
    exact hlaw3 x (hGx x hx)
  -- the good event
  have hgood : ∀ ω, ω ∉ ((⋃ p ∈ GE ×ˢ Gy, B1 p) ∪ (⋃ y ∈ Gy, B2 y) ∪ (⋃ x ∈ Gx, B3 x)) ∪
      {ω | ¬ ‖(X ω)ᵀ * X ω‖ ≤ C₀} → ω ∈ {ω | ∀ E ∈ Set.Icc E₁ E₂,
      |(eigCount (QN Sig (X ω)) E : ℝ) - nClass N (specOf Sig) E| ≤ (N : ℝ) ^ ε} := by
    intro ω hω
    have hnb : ‖(X ω)ᵀ * X ω‖ ≤ C₀ := by
      by_contra h
      exact hω (Or.inr h)
    have h1 : ∀ p ∈ GE ×ˢ Gy, ω ∉ B1 p := fun p hp hB =>
      hω (Or.inl (Or.inl (Or.inl (Set.mem_biUnion hp hB))))
    have h2 : ∀ y ∈ Gy, ω ∉ B2 y := fun y hy hB =>
      hω (Or.inl (Or.inl (Or.inr (Set.mem_biUnion hy hB))))
    have h3 : ∀ x ∈ Gx, ω ∉ B3 x := fun x hx hB =>
      hω (Or.inl (Or.inr (Set.mem_biUnion hx hB)))
    have hmN : ∀ z : ℂ, 0 < z.im → mN Sig (X ω) z = empStieltjes (specOf (QN Sig (X ω))) z :=
      fun z hz => mN_eq_empStieltjes hm.sigma.posDef (X ω) hz
    have hev1 : ∀ E ∈ GE, ∀ y ∈ Gy, ‖empStieltjes (specOf (QN Sig (X ω)))
        (↑E + ↑y * Complex.I) - mFun N (specOf Sig) (↑E + ↑y * Complex.I)‖ ≤ Λ / (N * y) := by
      intro E hE y hy
      have h : ¬ (Λ * (1 / (N * y)) <
          ‖mN Sig (X ω) (↑E + ↑y * Complex.I) -
            mFun N (specOf Sig) (↑E + ↑y * Complex.I)‖) := h1 (E, y) (Finset.mem_product.2 ⟨hE, hy⟩)
      rw [hmN _ (by simpa using (lt_of_lt_of_le hη (hGy y hy).1))] at h
      exact not_lt.1 h |>.trans (le_of_eq (by rw [mul_one_div]))
    have hev2 : ∀ y ∈ Gy, ‖empStieltjes (specOf (QN Sig (X ω)))
        (↑Et + ↑y * Complex.I) - mFun N (specOf Sig) (↑Et + ↑y * Complex.I)‖ ≤ Λ / (N * y) := by
      intro y hy
      have h : ¬ (Λ * (1 / (N * y)) <
          ‖mN Sig (X ω) (↑Et + ↑y * Complex.I) -
            mFun N (specOf Sig) (↑Et + ↑y * Complex.I)‖) := h2 y hy
      rw [hmN _ (by simpa using (lt_of_lt_of_le hη (hGy y hy).1))] at h
      exact not_lt.1 h |>.trans (le_of_eq (by rw [mul_one_div]))
    have hev3 : ∀ x ∈ Gx, ‖empStieltjes (specOf (QN Sig (X ω)))
        (↑x + ↑(1 : ℝ) * Complex.I) - mFun N (specOf Sig) (↑x + ↑(1 : ℝ) * Complex.I)‖ ≤
          Λ / N := by
      intro x hx
      have h : ¬ (Λ * (1 / (N * (1 : ℝ))) <
          ‖mN Sig (X ω) (↑x + ↑(1 : ℝ) * Complex.I) -
            mFun N (specOf Sig) (↑x + ↑(1 : ℝ) * Complex.I)‖) := h3 x hx
      rw [hmN _ (by simp)] at h
      exact not_lt.1 h |>.trans (le_of_eq (by rw [mul_one, mul_one_div]))
    have hanc : ∀ j, specOf (QN Sig (X ω)) j < Et := fun j =>
      lt_of_le_of_lt ((cl_eig_le hτ hm.sigma (X ω) j).trans
        (mul_le_mul_of_nonneg_left hnb (by positivity))) hEt2
    intro E hE
    have := cl_det (specOf Sig) hσ hN (specOf (QN Sig (X ω))) hτ hE₁ hE₂t hη hη1 hΛ hΛ1 hηN
      hCm0 GE Gy Gx hGE hGEc hGyc hGxc hanc hnEt hCm hev1 hev2 hev3 E hE
    exact this.trans hfin
  -- the probability
  have hU : ℙ ((⋃ p ∈ GE ×ˢ Gy, B1 p) ∪ (⋃ y ∈ Gy, B2 y) ∪ (⋃ x ∈ Gx, B3 x)) ≤
      (((GE ×ˢ Gy).card + Gy.card + Gx.card : ℕ) : ℝ≥0∞) * δ' := by
    refine (measure_union_le _ _).trans ?_
    refine (add_le_add ((measure_union_le _ _).trans (add_le_add hU1 hU2)) hU3).trans (le_of_eq ?_)
    push_cast
    ring
  unfold HighProbAt
  calc ℙ {ω | ∀ E ∈ Set.Icc E₁ E₂,
        |(eigCount (QN Sig (X ω)) E : ℝ) - nClass N (specOf Sig) E| ≤ (N : ℝ) ^ ε}ᶜ
      ≤ ℙ (((⋃ p ∈ GE ×ˢ Gy, B1 p) ∪ (⋃ y ∈ Gy, B2 y) ∪ (⋃ x ∈ Gx, B3 x)) ∪
          {ω | ¬ ‖(X ω)ᵀ * X ω‖ ≤ C₀}) :=
        measure_mono fun ω hω => by
          by_contra hcon
          exact hω (hgood ω hcon)
    _ ≤ ℙ ((⋃ p ∈ GE ×ˢ Gy, B1 p) ∪ (⋃ y ∈ Gy, B2 y) ∪ (⋃ x ∈ Gx, B3 x)) +
          ℙ {ω | ¬ ‖(X ω)ᵀ * X ω‖ ≤ C₀} := measure_union_le _ _
    _ ≤ (((GE ×ˢ Gy).card + Gy.card + Gx.card : ℕ) : ℝ≥0∞) * δ' +
          ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) := add_le_add hU hnorm
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := cl_ofReal_arith hN D hc

/-! ## The localized count -/

/-- `supp ϱ ⊆ [0, a₁]`, so `E` at distance `1/2` above `2τ⁻¹(1 + τ⁻¹)` is at distance `1/2` from
`supp ϱ`. -/
private lemma cl_infDist_top {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) {E : ℝ}
    (hE : 2 * τ⁻¹ * (1 + τ⁻¹) + 1 / 2 ≤ E) :
    1 / 2 ≤ Metric.infDist E (varrho N σ).support := by
  obtain ⟨hN, -, hS⟩ := cl_facts h
  have hnb := (card_innerCrit N σ h.nonneg hN hS).2
  have ha := (edgeVal_mem_Icc N σ h.nonneg hN hS h.pos h.phi_lower h.phi_upper h.bound_Sigma
    (k := 1) le_rfl (by omega)).2
  have hsub : (varrho N σ).support ⊆ Set.Icc 0 (edgeVal N σ 1) :=
    Measure.support_subset_of_isClosed isClosed_Icc
      (mem_ae_iff.mpr (varrho_compl_Icc_edgeVal N σ h.nonneg hN hS))
  have := isProbabilityMeasure_varrho N σ h.nonneg hN
  have hne : (varrho N σ).support.Nonempty :=
    Measure.nonempty_support (IsProbabilityMeasure.ne_zero _)
  refine (Metric.le_infDist hne).2 fun y hy => ?_
  have hy2 := (hsub hy).2
  rw [Real.dist_eq]
  exact le_trans (by linarith) (le_abs_self _)

/-- The polynomial count of grid points is below `N⁷`. -/
private lemma cl_count_numeric {a b N : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hN : 1 ≤ N)
    (h : 4 * a + b + 19 ≤ N) :
    (a * N ^ 2 + 3) * (N ^ 4 + 3) + (N ^ 4 + 3) + (b * N ^ 2 + 3) ≤ N ^ 7 := by
  have h2 : 1 ≤ N ^ 2 := one_le_pow₀ hN
  have h4 : 1 ≤ N ^ 4 := one_le_pow₀ hN
  have h24 : N ^ 2 ≤ N ^ 4 := pow_le_pow_right₀ hN (by norm_num)
  have h46 : N ^ 4 ≤ N ^ 6 := pow_le_pow_right₀ hN (by norm_num)
  have e1 : a * N ^ 2 + 3 ≤ (a + 3) * N ^ 2 := by nlinarith
  have e2 : N ^ 4 + 3 ≤ 4 * N ^ 4 := by nlinarith
  have e3 : (a * N ^ 2 + 3) * (N ^ 4 + 3) ≤ (a + 3) * N ^ 2 * (4 * N ^ 4) :=
    mul_le_mul e1 e2 (by positivity) (by positivity)
  have e4 : b * N ^ 2 + 3 ≤ (b + 3) * N ^ 6 := by nlinarith
  have e5 : N ^ 4 + 3 ≤ 4 * N ^ 6 := by nlinarith
  calc (a * N ^ 2 + 3) * (N ^ 4 + 3) + (N ^ 4 + 3) + (b * N ^ 2 + 3)
      ≤ (a + 3) * N ^ 2 * (4 * N ^ 4) + 4 * N ^ 6 + (b + 3) * N ^ 6 :=
        add_le_add (add_le_add e3 e5) e4
    _ = (4 * a + 12) * N ^ 6 + 4 * N ^ 6 + (b + 3) * N ^ 6 := by ring
    _ = (4 * a + b + 19) * N ^ 6 := by ring
    _ ≤ N * N ^ 6 := mul_le_mul_of_nonneg_right h (by positivity)
    _ = N ^ 7 := by ring

/-- The final inequality `K (1 + log N) N^{ε'} + 2 C_m/N ≤ N^ε` for large `N`. -/
private lemma cl_final_ineq {K' Cm ε ε' : ℝ} {N : ℕ} (hN : 1 ≤ N) (hK : 0 ≤ K') (hCm : 0 ≤ Cm)
    (hε' : 0 < ε') (hεε : 4 * ε' ≤ ε)
    (h : K' + 2 * Cm + K' / ε' ≤ (N : ℝ) ^ (2 * ε')) :
    K' * (1 + Real.log N) * (N : ℝ) ^ ε' + 2 * Cm / N ≤ (N : ℝ) ^ ε := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set x : ℝ := (N : ℝ) ^ ε' with hx
  have hx1 : 1 ≤ x := Real.one_le_rpow hN1 hε'.le
  have hx2 : (N : ℝ) ^ (2 * ε') = x ^ 2 := by
    rw [mul_comm, Real.rpow_mul hN0.le, Real.rpow_two]
  have hx4 : (N : ℝ) ^ (4 * ε') = x ^ 4 := by
    have : (4 : ℝ) * ε' = ε' * (4 : ℕ) := by push_cast; ring
    rw [this, Real.rpow_mul hN0.le, Real.rpow_natCast]
  have hlog : Real.log N ≤ x / ε' := Real.log_le_rpow_div hN0.le hε'
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  rw [hx2] at h
  have hinv : 2 * Cm / N ≤ 2 * Cm * x := by
    rw [div_le_iff₀ hN0]
    have : 1 ≤ x * N := by nlinarith
    nlinarith [mul_nonneg hCm (by linarith : (0 : ℝ) ≤ x * N - 1)]
  have h1 : K' * (1 + Real.log N) * x ≤ K' * (1 + x / ε') * x :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hK) (by linarith)
  have h2 : K' * (1 + x / ε') * x + 2 * Cm * x ≤ (K' + 2 * Cm + K' / ε') * x ^ 2 := by
    have hx0 : 0 ≤ x := by linarith
    have e : K' * (1 + x / ε') * x + 2 * Cm * x = (K' + 2 * Cm) * x + (K' / ε') * x ^ 2 := by
      field_simp
      ring
    rw [e]
    have : (K' + 2 * Cm) * x ≤ (K' + 2 * Cm) * x ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    nlinarith [this]
  have h3 : (K' + 2 * Cm + K' / ε') * x ^ 2 ≤ x ^ 2 * x ^ 2 :=
    mul_le_mul_of_nonneg_right h (by positivity)
  have h4 : (N : ℝ) ^ (4 * ε') ≤ (N : ℝ) ^ ε := Real.rpow_le_rpow_of_exponent_le hN1 hεε
  rw [hx4] at h4
  nlinarith [h1, h2, h3, h4, hinv]

/-- The eigenvalue count under (T_diag) on `[E₁, E₂] ⊆ [τ, τ⁻¹]` when `Im m ≥ c_b` on the vertical
lines over `[E₁, E₂]`, `N⁻¹ ≤ η ≤ 1` (the counting step of Theorem 3.15 (iii) with
Definition 2.7 (ii) replaced by this bound). -/
theorem count_loc (τ cb : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hcb : 0 < cb) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (E₁ E₂ : ℝ),
      IsModel τ C M N Sig X → τ ≤ E₁ → E₂ ≤ τ⁻¹ →
      (∀ E ∈ Set.Icc E₁ E₂, ∀ η : ℝ, (N : ℝ)⁻¹ ≤ η → η ≤ 1 →
        cb ≤ (mFun N (specOf Sig) ⟨E, η⟩).im) →
      HighProbAt N D {ω | ∀ E ∈ Set.Icc E₁ E₂,
        |(eigCount (QN Sig (X ω)) E : ℝ) - nClass N (specOf Sig) E| ≤ (N : ℝ) ^ ε} := by
  by_cases hτ1 : τ ≤ 1
  swap
  · exact ⟨0, fun N _ Ω _ _ M Sig X E₁ E₂ hm => absurd hm.tau_le_one hτ1⟩
  obtain ⟨C₀, hC₀⟩ := norm_XtX_le hτ hτ1
  -- the constants, fixed before `N₀`
  set ε₀ : ℝ := min ε 1 with hε₀
  have hε₀0 : 0 < ε₀ := lt_min hε one_pos
  have hε₀1 : ε₀ ≤ 1 := min_le_right _ _
  have hε₀ε : ε₀ ≤ ε := min_le_left _ _
  set ε' : ℝ := ε₀ / 4 with hε'
  have hε'0 : 0 < ε' := by positivity
  have hε'1 : ε' ≤ 1 := by linarith
  have hτinv : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  set Et : ℝ := max (τ⁻¹ * C₀) (2 * τ⁻¹ * (1 + τ⁻¹)) + 1 / 2 with hEt
  have hEt1 : 2 * τ⁻¹ * (1 + τ⁻¹) + 1 / 2 ≤ Et := by
    rw [hEt]; linarith [le_max_right (τ⁻¹ * C₀) (2 * τ⁻¹ * (1 + τ⁻¹))]
  have hEt2 : τ⁻¹ * C₀ + 1 / 2 ≤ Et := by
    rw [hEt]; linarith [le_max_left (τ⁻¹ * C₀) (2 * τ⁻¹ * (1 + τ⁻¹))]
  have hEt3 : τ⁻¹ ≤ Et := by nlinarith
  have hEtpos : 0 < Et := by linarith
  set τ₂ : ℝ := min (min τ ε') Et⁻¹ with hτ₂
  have hτ₂0 : 0 < τ₂ := lt_min (lt_min hτ hε'0) (inv_pos.2 hEtpos)
  have hτ₂τ : τ₂ ≤ τ := (min_le_left _ _).trans (min_le_left _ _)
  have hτ₂ε : τ₂ ≤ ε' := (min_le_left _ _).trans (min_le_right _ _)
  have hτ₂E : τ₂ ≤ Et⁻¹ := min_le_right _ _
  have hτ₂1 : τ₂ ≤ 1 := hτ₂τ.trans hτ1
  have hEtτ₂ : Et ≤ τ₂⁻¹ := (le_inv_comm₀ hτ₂0 hEtpos).1 hτ₂E
  have h1τ₂ : 1 ≤ τ₂⁻¹ := (one_le_inv₀ hτ₂0).2 hτ₂1
  set Cm : ℝ := genPropConst (τ₂ / 2) with hCm
  have hCm0 : 0 < Cm := by rw [hCm]; unfold genPropConst; positivity
  set cb' : ℝ := min cb Cm⁻¹ with hcb'
  have hcb'0 : 0 < cb' := lt_min hcb (inv_pos.2 hCm0)
  obtain ⟨N₁, h₁⟩ := loc_law τ₂ cb' C ε' (D + 8) hτ₂0 hcb'0 hε'0
  obtain ⟨N₂, h₂⟩ := outside_law τ₂ (1 / 2) C ε' (D + 8) hτ₂0 (by norm_num) hε'0
  obtain ⟨N₃, h₃⟩ := high_law τ₂ C ε' (D + 8) hτ₂0 hε'0
  obtain ⟨N₄, h₄⟩ := hC₀ C (D + 1)
  obtain ⟨N₅, h₅⟩ : ∃ N₅ : ℕ, ∀ N ≥ N₅, (2 * Et + 170 + 120 * Cm) + 2 * Cm +
      (2 * Et + 170 + 120 * Cm) / ε' ≤ (N : ℝ) ^ (2 * ε') :=
    Filter.eventually_atTop.1 (((tendsto_rpow_atTop (by positivity : 0 < 2 * ε')).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop _)
  refine ⟨max (max (max N₁ N₂) (max N₃ N₄)) (max (max N₅ ⌈4 * τ⁻¹ + Et + 19⌉₊) 2),
    fun N hN Ω _ _ M Sig X E₁ E₂ hm hE₁ hE₂ hcb => ?_⟩
  have hN₁ : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_trans (le_max_left _ _) hN)
  have hN₂ : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_trans (le_max_left _ _) hN)
  have hN₃ : N₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_trans (le_max_left _ _) hN)
  have hN₄ : N₄ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_trans (le_max_left _ _) hN)
  have hN5 : N₅ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_trans (le_max_right _ _) hN)
  have hN6 : ⌈4 * τ⁻¹ + Et + 19⌉₊ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_trans (le_max_right _ _) hN)
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN)
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hN0 : (0 : ℝ) < N := by linarith
  have hNc : 4 * τ⁻¹ + Et + 19 ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN6)
  -- the height `η = N^{-1+ε'}` and `Λ = N η = N^{ε'}`
  have hη : 0 < (N : ℝ) ^ (-1 + ε') := Real.rpow_pos_of_pos hN0 _
  have hη1 : (N : ℝ) ^ (-1 + ε') ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hNr (by linarith)
  have hΛ : (N : ℝ) ^ ε' = N * (N : ℝ) ^ (-1 + ε') := by
    rw [← Real.rpow_one_add' hN0.le (by linarith : (1 + (-1 + ε')) ≠ 0)]
    congr 1
    ring
  have hΛ1 : 1 ≤ (N : ℝ) ^ ε' := Real.one_le_rpow hNr hε'0.le
  have hηN : 1 / (N : ℝ) ≤ (N : ℝ) ^ (-1 + ε') := by
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
  have hητ₂ : (N : ℝ) ^ (-1 + τ₂) ≤ (N : ℝ) ^ (-1 + ε') :=
    Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
  have hNτ₂ : (N : ℝ)⁻¹ ≤ (N : ℝ) ^ (-1 + τ₂) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
  have hone : (N : ℝ) ^ (-1 + τ₂) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hNr (by linarith)
  -- the models and the density assumptions
  have hm₂ : IsModel τ₂ C M N Sig X := hm.mono hτ₂0 hτ₂τ
  have hda : DensityAssumptions τ N (specOf Sig) := hm.diagModel_specOf.densityAssumptions hτ
  have hda₂ : DensityAssumptions (τ₂ / 2) N (specOf Sig) :=
    (hm.mono (half_pos hτ₂0) ((half_le_self hτ₂0.le).trans hτ₂τ)).diagModel_specOf
      |>.densityAssumptions (half_pos hτ₂0)
  -- the points of the three families lie in `𝐃(τ₂, N)`
  have hdom : ∀ x y : ℝ, τ₂ ≤ x → x ≤ τ₂⁻¹ → (N : ℝ) ^ (-1 + τ₂) ≤ y → y ≤ 1 →
      ((x : ℂ) + y * Complex.I) ∈ specDomain τ₂ N := by
    intro x y hx hxu hy hy1
    have hy0 : 0 < y := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hy
    refine ⟨by simpa using hy0, ?_, ?_, by simpa using hy, by simpa using hy1.trans h1τ₂⟩
    · have := Complex.abs_re_le_norm ((x : ℂ) + y * Complex.I)
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero] at this
      rw [abs_of_pos (by linarith)] at this
      linarith
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
      rw [abs_of_pos (by linarith)]
      exact hxu
  -- `‖z‖` on the strip
  have hnorm_le : ∀ z : ℂ, 0 < z.im → |z.re| ≤ τ₂⁻¹ → z.im ≤ τ₂⁻¹ → ‖z‖ ≤ (τ₂ / 2)⁻¹ := by
    intro z hz1 h1 h2
    have h3 := Complex.norm_le_abs_re_add_abs_im z
    have e : (τ₂ / 2)⁻¹ = τ₂⁻¹ + τ₂⁻¹ := by field_simp; ring
    rw [e, abs_of_pos hz1] at *
    linarith
  -- `Im m ≤ C_m` on the strip `τ ≤ Re z ≤ E_top`, `0 < Im z ≤ 1`
  have hCmb : ∀ x y : ℝ, τ ≤ x → x ≤ Et → 0 < y → y ≤ 1 →
      (mFun N (specOf Sig) (↑x + ↑y * Complex.I)).im ≤ Cm := by
    intro x y hx hxE hy0 hy1
    have hz : 0 < ((x : ℂ) + ↑y * Complex.I).im := by simpa using hy0
    have hre : ((x : ℂ) + ↑y * Complex.I).re = x := by simp
    have him : ((x : ℂ) + ↑y * Complex.I).im = y := by simp
    have hn1 : τ₂ / 2 ≤ ‖(x : ℂ) + ↑y * Complex.I‖ := by
      have := Complex.abs_re_le_norm ((x : ℂ) + ↑y * Complex.I)
      rw [hre, abs_of_pos (by linarith)] at this
      linarith
    have hn2 : ‖(x : ℂ) + ↑y * Complex.I‖ ≤ (τ₂ / 2)⁻¹ :=
      hnorm_le _ hz (by rw [hre, abs_of_pos (by linarith)]; linarith) (by rw [him]; linarith)
    exact (Complex.im_le_norm _).trans (gen_prop_m hda₂ hz hn1 hn2).2.1
  -- the averaged law at the points of the three families
  have hlaw1 : ∀ E ∈ Set.Icc E₁ E₂, ∀ y ∈ Set.Icc ((N : ℝ) ^ (-1 + ε')) 1,
      ℙ {ω | (N : ℝ) ^ ε' * (1 / (N * y)) <
        ‖mN Sig (X ω) (↑E + ↑y * Complex.I) - mFun N (specOf Sig) (↑E + ↑y * Complex.I)‖} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-(D + 8))) := by
    intro E hE y hy
    have hSd : SpectralDomain τ₂ N {z : ℂ | z ∈ specDomain τ₂ N ∧ z.re = E} :=
      ⟨fun z hz => hz.1, fun z hz w hw hre _ => ⟨hw, by rw [hre]; exact hz.2⟩⟩
    have hcbS : ∀ z ∈ {z : ℂ | z ∈ specDomain τ₂ N ∧ z.re = E},
        cb' ≤ (mFun N (specOf Sig) z).im := by
      rintro z ⟨hz, hzE⟩
      by_cases hz1 : z.im ≤ 1
      · have hzeq : (⟨E, z.im⟩ : ℂ) = z := Complex.ext (by simp [hzE]) (by simp)
        have := hcb E hE z.im (hNτ₂.trans hz.2.2.2.1) hz1
        rw [hzeq] at this
        exact (min_le_left _ _).trans this
      · push Not at hz1
        have hn1 : τ₂ / 2 ≤ ‖z‖ := (half_le_self hτ₂0.le).trans hz.2.1
        have hn2 : ‖z‖ ≤ (τ₂ / 2)⁻¹ := hnorm_le z hz.1 hz.2.2.1 hz.2.2.2.2
        have h3 := (gen_prop_m hda₂ hz.1 hn1 hn2).2.2
        have h2 : Cm⁻¹ ≤ Cm⁻¹ * z.im := le_mul_of_one_le_right (inv_nonneg.2 hCm0.le) hz1.le
        exact (min_le_right _ _).trans (h2.trans h3)
    have hE₁' : τ₂ ≤ E := hτ₂τ.trans (hE₁.trans hE.1)
    have hEu : E ≤ τ₂⁻¹ := hE.2.trans (hE₂.trans (hEt3.trans hEtτ₂))
    have hzS : ((E : ℂ) + y * Complex.I) ∈ {z : ℂ | z ∈ specDomain τ₂ N ∧ z.re = E} :=
      ⟨hdom E y hE₁' hEu (hητ₂.trans hy.1) hy.2, by simp⟩
    have h := ((h₁ N hN₁ M Sig X _ hm₂ hSd hcbS).2) _ hzS
    have him : ((E : ℂ) + ↑y * Complex.I).im = y := by simp
    rw [him] at h
    exact h
  have hlaw2 : ∀ y ∈ Set.Icc ((N : ℝ) ^ (-1 + ε')) 1,
      ℙ {ω | (N : ℝ) ^ ε' * (1 / (N * y)) <
        ‖mN Sig (X ω) (↑Et + ↑y * Complex.I) - mFun N (specOf Sig) (↑Et + ↑y * Complex.I)‖} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-(D + 8))) := by
    intro y hy
    have hzS : ((Et : ℂ) + y * Complex.I) ∈ outsideDomain τ₂ (1 / 2) N (specOf Sig) := by
      refine ⟨hdom Et y (hτ₂1.trans (hτinv.trans hEt3)) hEtτ₂ (hητ₂.trans hy.1) hy.2, ?_⟩
      have hre : ((Et : ℂ) + ↑y * Complex.I).re = Et := by simp
      rw [hre]
      exact cl_infDist_top hda hEt1
    have h := ((h₂ N hN₂ M Sig X hm₂).2) _ hzS
    have him : ((Et : ℂ) + ↑y * Complex.I).im = y := by simp
    rw [him] at h
    exact h
  have hlaw3 : ∀ x ∈ Set.Icc E₁ Et,
      ℙ {ω | (N : ℝ) ^ ε' * (1 / (N * (1 : ℝ))) <
        ‖mN Sig (X ω) (↑x + ↑(1 : ℝ) * Complex.I) -
          mFun N (specOf Sig) (↑x + ↑(1 : ℝ) * Complex.I)‖} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-(D + 8))) := by
    intro x hx
    have hx' : τ₂ ≤ x := hτ₂τ.trans (hE₁.trans hx.1)
    have hzS : ((x : ℂ) + ↑(1 : ℝ) * Complex.I) ∈ highDomain τ₂ N :=
      ⟨hdom x 1 hx' (hx.2.trans hEtτ₂) hone le_rfl, by simp; linarith⟩
    have h := ((h₃ N hN₃ M Sig X hm₂).2) _ hzS
    have him : ((x : ℂ) + ↑(1 : ℝ) * Complex.I).im = 1 := by simp
    rw [him] at h
    exact h
  have hK : (M : ℝ) ≤ τ⁻¹ * N := by
    have := hm.ratio_le
    rw [div_le_iff₀ hN0] at this
    linarith
  have hnorm : ℙ {ω | ¬ ‖(X ω)ᵀ * X ω‖ ≤ C₀} ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) :=
    h₄ N hN₄ M X hm.entries hK
  have hcnt := cl_count_numeric (a := τ⁻¹) (b := Et) (by positivity) hEtpos.le hNr hNc
  have hfin := cl_final_ineq (K' := 2 * Et + 170 + 120 * Cm) (Cm := Cm) (ε := ε) (ε' := ε')
    (N := N) (by omega) (by positivity) hCm0.le hε'0 (by rw [hε']; linarith) (h₅ N hN5)
  exact cl_count_main hN2 Sig X hm hτ hE₁ hE₂ (hE₂.trans hEt3) (by linarith) (by linarith)
    hη hη1 hΛ hΛ1 hηN hCm0.le hCmb hlaw1 hlaw2 hlaw3 hnorm hcnt hfin

/-! ## The bulk inversion -/

/-- The bulk inversion: a count within `s` on the window `[a_{2k} + t/2, a_{2k−1} − t/2]` and the
density bound `c₀` there place `λ_{d_{k−1}+i}` within `(s+1)/(c₀N)` of `γ_{k,i}`. -/
theorem bulk_inversion {K : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    {A : Matrix (Fin K) (Fin K) ℝ} (hA : A.IsHermitian) {k : ℕ} {t c₀ s : ℝ} (ht : 0 < t)
    (hc₀ : 0 < c₀) (hs0 : 0 ≤ s)
    (hρ : ∀ E ∈ Set.Icc (edgeVal N σ (2 * k) + t / 2) (edgeVal N σ (2 * k - 1) - t / 2),
      c₀ ≤ rhoDens N σ E)
    (hcount : ∀ E ∈ Set.Icc (edgeVal N σ (2 * k) + t / 2) (edgeVal N σ (2 * k - 1) - t / 2),
      |(eigCount A E : ℝ) - nClass N σ E| ≤ s)
    (hs : (s + 1) / (c₀ * N) ≤ t / 2) {i : ℕ}
    (hγ : gammaBand N σ k i ∈
      Set.Icc (edgeVal N σ (2 * k) + t) (edgeVal N σ (2 * k - 1) - t))
    (hpos : 0 ≤ edgeVal N σ (2 * k)) :
    |sortedEig A (cumCount N σ (k - 1) + i) - gammaBand N σ k i| ≤ (s + 1) / (c₀ * N) := by
  have _ht : 0 < t := ht
  have hγdef : gammaBand N σ k i = gammaLoc N σ (cumCount N σ (k - 1) + i) := rfl
  generalize hj : cumCount N σ (k - 1) + i = j at hγdef ⊢
  rw [hγdef] at hγ ⊢
  generalize hγ' : gammaLoc N σ j = γ at hγ ⊢
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  generalize hr : (s + 1) / (c₀ * N) = r at hs ⊢
  have hr0 : 0 < r := by rw [← hr]; positivity
  have hNcr : N * c₀ * r = s + 1 := by rw [← hr]; field_simp
  have hγ0 : 0 < γ := by linarith [hγ.1, hpos]
  have hn : nClass N σ γ = (j : ℝ) - 1 / 2 := by
    rw [← hγ']; exact nClass_gammaLoc_of_pos hσ hN (by rw [hγ']; exact hγ0)
  have hj1 : 1 ≤ j := by
    by_contra h
    have h0 : j = 0 := by omega
    have := cl_nClass_nonneg σ (N := N) γ
    rw [hn, h0] at this
    norm_num at this
  have hmem : ∀ u, γ - r ≤ u → u ≤ γ + r →
      u ∈ Set.Icc (edgeVal N σ (2 * k) + t / 2) (edgeVal N σ (2 * k - 1) - t / 2) := fun u h1 h2 =>
    ⟨by linarith [hγ.1], by linarith [hγ.2]⟩
  have hγr : 0 < γ - r := by linarith [hγ.1, hpos]
  -- the drops of `n` on `[γ − r, γ)` and `[γ, γ + r)`
  have hdl : N * c₀ * r ≤ nClass N σ (γ - r) - nClass N σ γ := by
    have := cl_nClass_sub_ge σ hσ hN (x := γ - r) (y := γ) hγr (by linarith) hc₀.le
      (fun u hu => hρ u (hmem u hu.1 (by linarith [hu.2])))
    simpa using this
  have hdr : N * c₀ * r ≤ nClass N σ γ - nClass N σ (γ + r) := by
    have := cl_nClass_sub_ge σ hσ hN (x := γ) (y := γ + r) hγ0 (by linarith) hc₀.le
      (fun u hu => hρ u (hmem u (by linarith [hu.1]) (by linarith [hu.2])))
    simpa using this
  have hcl := hcount (γ - r) (hmem _ le_rfl (by linarith))
  have hcr := hcount (γ + r) (hmem _ (by linarith) le_rfl)
  rw [abs_le] at hcl hcr
  have hle : ∀ E, eigCount A E ≤ K := fun E => by
    unfold eigCount
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hlow : (j : ℝ) < eigCount A (γ - r) := by linarith [hcl.1]
  have hlowN : j < eigCount A (γ - r) := by exact_mod_cast hlow
  have hjK : j ≤ K := by have := hle (γ - r); omega
  have hup : (eigCount A (γ + r) : ℝ) < j := by linarith [hcr.2]
  have hupN : eigCount A (γ + r) < j := by exact_mod_cast hup
  have h1 : γ - r ≤ sortedEig A j := (sortedEig_ge_iff hA hj1 hjK (γ - r)).2 hlowN.le
  have h2 : sortedEig A j < γ + r := by
    by_contra h
    have := (sortedEig_ge_iff hA hj1 hjK (γ + r)).1 (not_lt.mp h)
    omega
  rw [abs_le]
  constructor <;> linarith

/-! ## Instances -/

/-- `bulk_inversion` at Marchenko–Pastur data `M = 100`, `N = 200`, `σ = 1`, `k = 1`, `t = 1/2`,
`s = 1/2`, `c₀ = 1/25`. The arithmetic hypothesis `(s + 1)/(c₀ N) = 3/16 ≤ t/2` is discharged; the
hypotheses on `ρ`, on the count, and on `γ_{1,i}` depend on the explicit density and are binders. -/
example {A : Matrix (Fin 200) (Fin 200) ℝ} (hA : A.IsHermitian) {i : ℕ}
    (hρ : ∀ E ∈ Set.Icc (edgeVal 200 (fun _ : Fin 100 => (1 : ℝ)) (2 * 1) + 1 / 2 / 2)
        (edgeVal 200 (fun _ : Fin 100 => (1 : ℝ)) (2 * 1 - 1) - 1 / 2 / 2),
      (1 / 25 : ℝ) ≤ rhoDens 200 (fun _ : Fin 100 => (1 : ℝ)) E)
    (hcount : ∀ E ∈ Set.Icc (edgeVal 200 (fun _ : Fin 100 => (1 : ℝ)) (2 * 1) + 1 / 2 / 2)
        (edgeVal 200 (fun _ : Fin 100 => (1 : ℝ)) (2 * 1 - 1) - 1 / 2 / 2),
      |(eigCount A E : ℝ) - nClass 200 (fun _ : Fin 100 => (1 : ℝ)) E| ≤ 1 / 2)
    (hγ : gammaBand 200 (fun _ : Fin 100 => (1 : ℝ)) 1 i ∈
      Set.Icc (edgeVal 200 (fun _ : Fin 100 => (1 : ℝ)) (2 * 1) + 1 / 2)
        (edgeVal 200 (fun _ : Fin 100 => (1 : ℝ)) (2 * 1 - 1) - 1 / 2))
    (hpos : 0 ≤ edgeVal 200 (fun _ : Fin 100 => (1 : ℝ)) (2 * 1)) :
    |sortedEig A (cumCount 200 (fun _ : Fin 100 => (1 : ℝ)) (1 - 1) + i) -
        gammaBand 200 (fun _ : Fin 100 => (1 : ℝ)) 1 i| ≤
      ((1 / 2 : ℝ) + 1) / ((1 / 25 : ℝ) * ((200 : ℕ) : ℝ)) :=
  bulk_inversion (N := 200) (fun _ => by norm_num) (by norm_num) hA (by norm_num) (by norm_num)
    (by norm_num) hρ hcount (by norm_num) hγ hpos

end Anisotropic

#print axioms Anisotropic.im_mFun_ge_of_density
#print axioms Anisotropic.count_loc
#print axioms Anisotropic.bulk_inversion
