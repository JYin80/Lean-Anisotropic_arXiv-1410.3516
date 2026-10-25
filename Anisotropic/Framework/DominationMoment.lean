import Anisotropic.Framework.Domination

open MeasureTheory ProbabilityTheory Matrix
open scoped ProbabilityTheory ENNReal

noncomputable section

namespace Anisotropic

section Calculus

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Markov's inequality with one moment `p` and `(ε' - ε) p ≥ D`. -/
theorem DomAt.of_moment {N : ℕ} {ε ε' D ζ : ℝ} {ξ : Ω → ℝ} (p : ℕ) (hN : 1 ≤ N)
    (hp : D ≤ (ε' - ε) * p) (hξ : ∀ ω, 0 ≤ ξ ω) (hζ : 0 < ζ)
    (hint : Integrable fun ω => ξ ω ^ p)
    (hmom : ∫ ω, ξ ω ^ p ≤ ((N : ℝ) ^ ε * ζ) ^ p) :
    DomAt N ε' D ξ (fun _ => ζ) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  unfold DomAt
  rcases Nat.eq_zero_or_pos p with h0 | hp1
  · subst h0
    have hD : D ≤ 0 := by simpa using hp
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (-D) := Real.one_le_rpow hN' (by linarith)
    calc ℙ {ω | (N : ℝ) ^ ε' * ζ < ξ ω} ≤ 1 := prob_le_one
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
        rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal h1
  · set a : ℝ := (N : ℝ) ^ ε' * ζ with ha
    have hapos : 0 < a := mul_pos (Real.rpow_pos_of_pos hNpos _) hζ
    have hsub : {ω | a < ξ ω} ⊆ {ω | a ^ p ≤ ξ ω ^ p} := by
      intro ω hω
      exact pow_le_pow_left₀ hapos.le (le_of_lt hω) p
    have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := (ℙ : Measure Ω))
      (f := fun ω => ξ ω ^ p) (ae_of_all _ fun ω => pow_nonneg (hξ ω) p) hint (a ^ p)
    have hreal : (ℙ : Measure Ω).real {ω | a ^ p ≤ ξ ω ^ p} ≤ (N : ℝ) ^ (-D) := by
      have hap : 0 < a ^ p := pow_pos hapos p
      have h1 : (ℙ : Measure Ω).real {ω | a ^ p ≤ ξ ω ^ p} ≤ ((N : ℝ) ^ ε * ζ) ^ p / a ^ p := by
        rw [le_div_iff₀ hap]; linarith
      refine h1.trans ?_
      have h2 : ((N : ℝ) ^ ε * ζ) ^ p / a ^ p = (N : ℝ) ^ ((ε - ε') * p) := by
        rw [ha, mul_pow, mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast ((N : ℝ) ^ ε')]
        rw [← Real.rpow_mul hNpos.le, ← Real.rpow_mul hNpos.le, sub_mul,
          Real.rpow_sub hNpos]
        have : (ζ ^ p) ≠ 0 := (pow_pos hζ p).ne'
        exact mul_div_mul_right _ _ this
      rw [h2]
      apply Real.rpow_le_rpow_of_exponent_le hN'
      nlinarith
    calc ℙ {ω | a < ξ ω} ≤ ℙ {ω | a ^ p ≤ ξ ω ^ p} := measure_mono hsub
      _ = ENNReal.ofReal ((ℙ : Measure Ω).real {ω | a ^ p ≤ ξ ω ^ p}) :=
        (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal hreal

/-- Lemma 7.7 at fixed `N`: `ξ ≺ Γ`, `Γ ≥ N^{-C}`, `E ξ² ≤ N^C` give
`E ξ ≤ 2 N^ε Γ` once `D ≥ 3C`. -/
theorem integral_le_of_domAt {N : ℕ} {ε D C Γ : ℝ} {ξ : Ω → ℝ} (hN : 1 ≤ N)
    (hε : 0 ≤ ε) (hD : 3 * C ≤ D) (hΓ : (N : ℝ) ^ (-C) ≤ Γ) (hξ : ∀ ω, 0 ≤ ξ ω)
    (hint : Integrable fun ω => ξ ω ^ 2) (h2 : ∫ ω, ξ ω ^ 2 ≤ (N : ℝ) ^ C)
    (h : DomAt N ε D ξ (fun _ => Γ)) :
    ∫ ω, ξ ω ≤ 2 * (N : ℝ) ^ ε * Γ := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hΓpos : 0 < Γ := lt_of_lt_of_le (Real.rpow_pos_of_pos hNpos _) hΓ
  set c : ℝ := (N : ℝ) ^ ε * Γ with hc
  have hcpos : 0 < c := mul_pos (Real.rpow_pos_of_pos hNpos _) hΓpos
  -- measurable representative of `ξ`
  have hξm : AEStronglyMeasurable ξ (ℙ : Measure Ω) := by
    have := Real.continuous_sqrt.comp_aestronglyMeasurable hint.aestronglyMeasurable
    refine this.congr (ae_of_all _ fun ω => ?_)
    simp [Real.sqrt_sq (hξ ω)]
  set ξ' : Ω → ℝ := hξm.mk ξ with hξ'
  have hae : ξ =ᵐ[(ℙ : Measure Ω)] ξ' := hξm.ae_eq_mk
  set B : Set Ω := {ω | c < ξ' ω} with hB
  have hBm : MeasurableSet B :=
    measurableSet_lt measurable_const hξm.stronglyMeasurable_mk.measurable
  have hBP : ℙ B ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
    refine le_trans (le_of_eq ?_) h
    refine measure_congr ?_
    rw [Filter.eventuallyEqSet_iff]
    filter_upwards [hae] with ω hω
    simp [hB, hω, hc]
  have hPreal : (ℙ : Measure Ω).real B ≤ (N : ℝ) ^ (-D) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hBP
    rwa [ENNReal.toReal_ofReal (Real.rpow_nonneg hNpos.le _)] at this
  -- exponents
  set t : ℝ := (N : ℝ) ^ (-(C + D) / 2) with ht
  have htpos : 0 < t := Real.rpow_pos_of_pos hNpos _
  have hsmall : (N : ℝ) ^ ((C - D) / 2) ≤ (N : ℝ) ^ (-C) :=
    Real.rpow_le_rpow_of_exponent_le hN' (by linarith)
  have hA : t * (N : ℝ) ^ C = (N : ℝ) ^ ((C - D) / 2) := by
    rw [ht, ← Real.rpow_add hNpos]; congr 1; ring
  have hA' : t⁻¹ * (N : ℝ) ^ (-D) = (N : ℝ) ^ ((C - D) / 2) := by
    rw [ht, ← Real.rpow_neg hNpos.le, ← Real.rpow_add hNpos]; congr 1; ring
  -- pointwise bound
  let g : Ω → ℝ := fun ω => c + (1 / 2) * (t * ξ ω ^ 2 + t⁻¹ * B.indicator (fun _ => (1 : ℝ)) ω)
  have hgint : Integrable g := by
    refine (integrable_const c).add ?_
    refine Integrable.const_mul (Integrable.add (hint.const_mul t) ?_) _
    exact (integrable_const (1 : ℝ)).indicator hBm |>.const_mul _
  have hpt : ∀ᵐ ω ∂(ℙ : Measure Ω), ξ ω ≤ g ω := by
    filter_upwards [hae] with ω hω
    simp only [g]
    by_cases hb : ω ∈ B
    · have hind : B.indicator (fun _ => (1 : ℝ)) ω = 1 := Set.indicator_of_mem hb _
      rw [hind]
      have h0 : 0 ≤ (t * ξ ω - 1) ^ 2 := sq_nonneg _
      have : ξ ω ≤ (1 / 2) * (t * ξ ω ^ 2 + t⁻¹ * 1) := by
        rw [← sub_nonneg]
        have e : (1 / 2) * (t * ξ ω ^ 2 + t⁻¹ * 1) - ξ ω = (t * ξ ω - 1) ^ 2 / (2 * t) := by
          field_simp; ring
        rw [e]; positivity
      have hc0 : 0 ≤ c := hcpos.le
      linarith
    · have hind : B.indicator (fun _ => (1 : ℝ)) ω = 0 := Set.indicator_of_notMem hb _
      rw [hind]
      have : ξ ω ≤ c := by
        have : ¬ c < ξ' ω := hb
        rw [← hω] at this; exact not_lt.mp this
      have : 0 ≤ t * ξ ω ^ 2 + t⁻¹ * 0 := by rw [mul_zero, add_zero]; positivity
      linarith
  have hξint : Integrable ξ := by
    refine Integrable.mono' hgint hξm ?_
    filter_upwards [hpt] with ω hω
    rw [Real.norm_of_nonneg (hξ ω)]; exact hω
  have hmono : ∫ ω, ξ ω ≤ ∫ ω, g ω := integral_mono_ae hξint hgint hpt
  have hgval : ∫ ω, g ω = c + (1 / 2) * (t * (∫ ω, ξ ω ^ 2) + t⁻¹ * (ℙ : Measure Ω).real B) := by
    simp only [g]
    rw [integral_add (integrable_const c) _, integral_const, integral_const_mul,
      integral_add (hint.const_mul t) _, integral_const_mul, integral_const_mul,
      integral_indicator_const _ hBm]
    · simp
    · exact (integrable_const (1 : ℝ)).indicator hBm |>.const_mul _
    · exact Integrable.const_mul (Integrable.add (hint.const_mul t)
        ((integrable_const (1 : ℝ)).indicator hBm |>.const_mul _)) _
  have hfin : c + (1 / 2) * (t * (∫ ω, ξ ω ^ 2) + t⁻¹ * (ℙ : Measure Ω).real B) ≤
      c + (N : ℝ) ^ ((C - D) / 2) := by
    have e1 : t * ∫ ω, ξ ω ^ 2 ≤ t * (N : ℝ) ^ C := mul_le_mul_of_nonneg_left h2 htpos.le
    have e2 : t⁻¹ * (ℙ : Measure Ω).real B ≤ t⁻¹ * (N : ℝ) ^ (-D) :=
      mul_le_mul_of_nonneg_left hPreal (inv_nonneg.mpr htpos.le)
    rw [hA] at e1
    rw [hA'] at e2
    linarith
  have hΓc : Γ ≤ c := by
    have : (1 : ℝ) ≤ (N : ℝ) ^ ε := Real.one_le_rpow hN' hε
    rw [hc]; nlinarith
  calc ∫ ω, ξ ω ≤ ∫ ω, g ω := hmono
    _ ≤ c + (N : ℝ) ^ ((C - D) / 2) := hgval ▸ hfin
    _ ≤ 2 * (N : ℝ) ^ ε * Γ := by
      have : 2 * (N : ℝ) ^ ε * Γ = c + c := by rw [hc]; ring
      rw [this]; linarith

end Calculus

end Anisotropic

#print axioms Anisotropic.DomAt.of_moment
#print axioms Anisotropic.integral_le_of_domAt
