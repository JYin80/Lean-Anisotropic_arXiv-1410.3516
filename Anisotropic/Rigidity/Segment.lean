module

public import Anisotropic.Density.SelfConsistent
public import Anisotropic.Density.Stability.Defs
public import Anisotropic.Density.Varrho
public import Anisotropic.Rigidity.Defs
public import Anisotropic.Rigidity.Exclusion

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # The counting identities (deterministic): arctan counts, smoothing, the segment identities, the comparison -/

/-! ## Real and imaginary parts of the transforms -/

/-- `Im (t − (x + iy))⁻¹ = y / ((t − x)² + y²)`. -/
private lemma seg_inv_im (t x y : ℝ) :
    (((t : ℂ) - (↑x + ↑y * Complex.I))⁻¹).im = y / ((t - x) ^ 2 + y ^ 2) := by
  rw [Complex.inv_im, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.add_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, Complex.sub_im, Complex.add_im, Complex.mul_im]
  ring

/-- `Re (t − (x + iy))⁻¹ = (t − x) / ((t − x)² + y²)`. -/
private lemma seg_inv_re (t x y : ℝ) :
    (((t : ℂ) - (↑x + ↑y * Complex.I))⁻¹).re = (t - x) / ((t - x) ^ 2 + y ^ 2) := by
  rw [Complex.inv_re, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.add_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, Complex.sub_im, Complex.add_im, Complex.mul_im]
  ring

/-- `Im s(x + iy) = K⁻¹ ∑_j y / ((λ_j − x)² + y²)`. -/
private lemma emp_im {K : ℕ} (lam : Fin K → ℝ) (x y : ℝ) :
    (empStieltjes lam (↑x + ↑y * Complex.I)).im =
      (K : ℝ)⁻¹ * ∑ j, y / ((lam j - x) ^ 2 + y ^ 2) := by
  have hK : (K : ℂ)⁻¹ = (((K : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  unfold empStieltjes
  rw [hK, Complex.im_ofReal_mul, Complex.im_sum]
  simp_rw [seg_inv_im]

/-- `Re s(x + iy) = K⁻¹ ∑_j (λ_j − x) / ((λ_j − x)² + y²)`. -/
private lemma emp_re {K : ℕ} (lam : Fin K → ℝ) (x y : ℝ) :
    (empStieltjes lam (↑x + ↑y * Complex.I)).re =
      (K : ℝ)⁻¹ * ∑ j, (lam j - x) / ((lam j - x) ^ 2 + y ^ 2) := by
  have hK : (K : ℂ)⁻¹ = (((K : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  unfold empStieltjes
  rw [hK, Complex.re_ofReal_mul, Complex.re_sum]
  simp_rw [seg_inv_re]

/-- On `ℂ₊`, `m(z) = ∫ (t − z)⁻¹ dϱ(t)`. -/
private lemma mFun_eq_integral (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {z : ℂ}
    (hz : 0 < z.im) : mFun N σ z = ∫ t : ℝ, ((t : ℂ) - z)⁻¹ ∂(varrho N σ) := by
  rw [← resolventTransform_varrho N σ hσ hN hz, resolventTransform_apply]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp [resolvent, Ring.inverse_eq_inv']

/-- `t ↦ (t − z)⁻¹` is `ϱ`-integrable for `Im z > 0`. -/
private lemma integrable_inv_varrho (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {z : ℂ}
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
private lemma mFun_im_eq (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) (x : ℝ) {y : ℝ}
    (hy : 0 < y) :
    (mFun N σ (↑x + ↑y * Complex.I)).im = ∫ t, y / ((t - x) ^ 2 + y ^ 2) ∂(varrho N σ) := by
  have hz : 0 < ((x : ℂ) + ↑y * Complex.I).im := by simpa using hy
  rw [mFun_eq_integral σ hσ hN hz]
  have := integral_im (𝕜 := ℂ) (integrable_inv_varrho σ hσ hN hz)
  simp only [RCLike.im_to_complex] at this
  rw [← this]
  simp_rw [seg_inv_im]

/-- `Re m(x + iy) = ∫ (t − x) / ((t − x)² + y²) dϱ(t)` for `y > 0`. -/
private lemma mFun_re_eq (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) (x : ℝ) {y : ℝ}
    (hy : 0 < y) :
    (mFun N σ (↑x + ↑y * Complex.I)).re =
      ∫ t, (t - x) / ((t - x) ^ 2 + y ^ 2) ∂(varrho N σ) := by
  have hz : 0 < ((x : ℂ) + ↑y * Complex.I).im := by simpa using hy
  rw [mFun_eq_integral σ hσ hN hz]
  have := integral_re (𝕜 := ℂ) (integrable_inv_varrho σ hσ hN hz)
  simp only [RCLike.re_to_complex] at this
  rw [← this]
  simp_rw [seg_inv_re]

/-! ## Arctan counts -/

/-- The Lorentzian `x ↦ η / ((c − x)² + η²)` is continuous for `η > 0`. -/
private lemma cont_lorentz (c η : ℝ) (hη : 0 < η) :
    Continuous fun x : ℝ => η / ((c - x) ^ 2 + η ^ 2) :=
  continuous_const.div (by fun_prop) fun x => by positivity

/-- `∫_{E₁}^{E₂} η/((c − x)² + η²) dx = arctan((E₂ − c)/η) − arctan((E₁ − c)/η)`. -/
private lemma arctan_term (c E₁ E₂ η : ℝ) (hη : 0 < η) :
    ∫ x in E₁..E₂, η / ((c - x) ^ 2 + η ^ 2) =
      Real.arctan ((E₂ - c) / η) - Real.arctan ((E₁ - c) / η) := by
  have hd : ∀ x ∈ Set.uIcc E₁ E₂, HasDerivAt (fun x : ℝ => Real.arctan ((x - c) / η))
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
  exact (cont_lorentz c η hη).intervalIntegrable _ _

/-- Exchange of the order of integration for an interval integral and a finite measure. -/
private lemma swap_ivl {μ : Measure ℝ} [IsFiniteMeasure μ] (f : ℝ → ℝ → ℝ)
    (hf : Measurable (Function.uncurry f)) {a b C : ℝ}
    (hb : ∀ x ∈ Set.uIoc a b, ∀ t, |f x t| ≤ C) :
    ∫ x in a..b, ∫ t, f x t ∂μ = ∫ t, (∫ x in a..b, f x t) ∂μ := by
  have key : ∀ s : Set ℝ, MeasurableSet s → volume s < ⊤ → (∀ x ∈ s, ∀ t, |f x t| ≤ C) →
      ∫ x in s, ∫ t, f x t ∂μ = ∫ t, (∫ x in s, f x t) ∂μ := by
    intro s hs hfin hbd
    have : IsFiniteMeasure (volume.restrict s) :=
      ⟨by simpa [Measure.restrict_apply_univ] using hfin⟩
    refine integral_integral_swap (μ := volume.restrict s) (ν := μ) (f := f) ?_
    refine Integrable.of_bound hf.aestronglyMeasurable C ?_
    have hprod := Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := μ) s Set.univ
    rw [Measure.restrict_univ] at hprod
    rw [hprod]
    refine (ae_restrict_iff' (hs.prod MeasurableSet.univ)).2 (ae_of_all _ fun p hp => ?_)
    simpa [Function.uncurry] using hbd p.1 hp.1 p.2
  rcases le_total a b with h | h
  · simp only [intervalIntegral.integral_of_le h]
    exact key _ measurableSet_Ioc (by simp) fun x hx => hb x (by rwa [Set.uIoc_of_le h])
  · simp only [intervalIntegral.integral_of_ge h, integral_neg]
    rw [key _ measurableSet_Ioc (by simp) fun x hx => hb x (by rwa [Set.uIoc_of_ge h])]

/-- `K ∫_{E₁}^{E₂} Im s(x + iη) dx = ∑_j (arctan((E₂ − λ_j)/η) − arctan((E₁ − λ_j)/η))`. -/
theorem arctan_count {K : ℕ} (lam : Fin K → ℝ) (E₁ E₂ η : ℝ) (hη : 0 < η) :
    (K : ℝ) * ∫ x in E₁..E₂, (empStieltjes lam (↑x + ↑η * Complex.I)).im =
      ∑ j, (Real.arctan ((E₂ - lam j) / η) - Real.arctan ((E₁ - lam j) / η)) := by
  simp_rw [emp_im]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
  · simp_rw [arctan_term _ _ _ _ hη]
    rcases Nat.eq_zero_or_pos K with rfl | hK
    · simp
    · rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  · intro j _
    exact (cont_lorentz (lam j) η hη).intervalIntegrable _ _

/-- The same identity for `m` and `ϱ`. -/
theorem arctan_count_varrho (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) (E₁ E₂ η : ℝ)
    (hη : 0 < η) :
    ∫ x in E₁..E₂, (mFun N σ (↑x + ↑η * Complex.I)).im =
      ∫ x, (Real.arctan ((E₂ - x) / η) - Real.arctan ((E₁ - x) / η)) ∂(varrho N σ) := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  simp_rw [mFun_im_eq σ hσ hN _ hη]
  have hsw := swap_ivl (μ := varrho N σ) (fun x t => η / ((t - x) ^ 2 + η ^ 2))
    (by unfold Function.uncurry; fun_prop) (a := E₁) (b := E₂) (C := 1 / η) (by
      intro x _ t
      rw [abs_of_pos (by positivity)]
      rw [div_le_div_iff₀ (by positivity) hη]
      nlinarith [sq_nonneg (t - x)])
  beta_reduce at hsw
  refine hsw.trans (integral_congr_ae (ae_of_all (varrho N σ) fun t => ?_))
  exact arctan_term t E₁ E₂ η hη

/-! ## The smoothed indicator -/

/-- The tail of the arctan: `π⁻¹(π/2 − arctan(d/η)) ≤ 2η/(d + η)` for `d ≥ 0`. -/
private lemma arc_tail {η d : ℝ} (hη : 0 < η) (hd : 0 ≤ d) :
    (Real.pi / 2 - Real.arctan (d / η)) / Real.pi ≤ 2 * η / (d + η) := by
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  rw [div_le_div_iff₀ hpi (by positivity)]
  have h0 : 0 ≤ Real.arctan (d / η) := by
    rw [← Real.arctan_zero]; exact Real.arctan_mono (by positivity)
  rcases le_or_gt d η with h | h
  · nlinarith
  · have hd0 : 0 < d := by linarith
    have hinv : Real.pi / 2 - Real.arctan (d / η) = Real.arctan (η / d) := by
      rw [← Real.arctan_inv_of_pos (by positivity), inv_div]
    have h2 : Real.arctan (η / d) ≤ η / d := Real.arctan_le_self (by positivity)
    have h3 : (Real.pi / 2 - Real.arctan (d / η)) * (d + η) ≤ 2 * η := by
      calc (Real.pi / 2 - Real.arctan (d / η)) * (d + η) ≤ (η / d) * (d + η) := by
            rw [hinv]; exact mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = η + η * η / d := by field_simp
        _ ≤ 2 * η := by
            have : η * η / d ≤ η := by
              rw [div_le_iff₀ hd0]; nlinarith
            linarith
    nlinarith

/-- The smoothed indicator differs from `𝟙_{[E₁,E₂]}` by at most
`2η/(|x − E₁| + η) + 2η/(|x − E₂| + η)`. -/
theorem arctan_indicator_le {E₁ E₂ η x : ℝ} (hη : 0 < η) (h12 : E₁ ≤ E₂) :
    |(Real.arctan ((E₂ - x) / η) - Real.arctan ((E₁ - x) / η)) / Real.pi -
        (Set.Icc E₁ E₂).indicator (fun _ => (1 : ℝ)) x| ≤
      2 * η / (|x - E₁| + η) + 2 * η / (|x - E₂| + η) := by
  have hpi := Real.pi_pos
  have t1 := arc_tail hη (abs_nonneg (x - E₁))
  have t2 := arc_tail hη (abs_nonneg (x - E₂))
  have hp1 : 0 ≤ 2 * η / (|x - E₁| + η) := by positivity
  have hp2 : 0 ≤ 2 * η / (|x - E₂| + η) := by positivity
  have hAlt : Real.arctan ((E₂ - x) / η) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have hBgt : -(Real.pi / 2) < Real.arctan ((E₁ - x) / η) := Real.neg_pi_div_two_lt_arctan _
  rcases lt_or_ge x E₁ with h | h
  · -- `x < E₁`
    rw [Set.indicator_of_notMem (fun hx : x ∈ Set.Icc E₁ E₂ => absurd hx.1 (not_le.mpr h)),
      sub_zero]
    rw [show |x - E₁| / η = (E₁ - x) / η by rw [abs_of_neg (by linarith : x - E₁ < 0)]; ring]
      at t1
    have hmono : Real.arctan ((E₁ - x) / η) ≤ Real.arctan ((E₂ - x) / η) :=
      Real.arctan_mono (div_le_div_of_nonneg_right (by linarith) hη.le)
    rw [abs_of_nonneg (div_nonneg (by linarith) hpi.le)]
    calc (Real.arctan ((E₂ - x) / η) - Real.arctan ((E₁ - x) / η)) / Real.pi
        ≤ (Real.pi / 2 - Real.arctan ((E₁ - x) / η)) / Real.pi :=
          div_le_div_of_nonneg_right (by linarith) hpi.le
      _ ≤ _ := by linarith
  rcases le_or_gt x E₂ with h' | h'
  · -- `E₁ ≤ x ≤ E₂`
    rw [Set.indicator_of_mem (show x ∈ Set.Icc E₁ E₂ from ⟨h, h'⟩)]
    rw [show |x - E₁| / η = (x - E₁) / η by rw [abs_of_nonneg (by linarith : 0 ≤ x - E₁)]] at t1
    rw [show |x - E₂| / η = (E₂ - x) / η by
      rw [abs_of_nonpos (by linarith : x - E₂ ≤ 0)]; ring] at t2
    have hB : Real.arctan ((E₁ - x) / η) = -Real.arctan ((x - E₁) / η) := by
      rw [← Real.arctan_neg]; congr 1; ring
    have hid : (Real.arctan ((E₂ - x) / η) - Real.arctan ((E₁ - x) / η)) / Real.pi - 1 =
        -((Real.pi / 2 - Real.arctan ((x - E₁) / η)) / Real.pi +
          (Real.pi / 2 - Real.arctan ((E₂ - x) / η)) / Real.pi) := by
      rw [hB]; field_simp; ring
    have hn : 0 ≤ (Real.pi / 2 - Real.arctan ((x - E₁) / η)) / Real.pi +
        (Real.pi / 2 - Real.arctan ((E₂ - x) / η)) / Real.pi :=
      add_nonneg (div_nonneg (by linarith [Real.arctan_lt_pi_div_two ((x - E₁) / η)]) hpi.le)
        (div_nonneg (by linarith) hpi.le)
    rw [hid, abs_neg, abs_of_nonneg hn]
    linarith
  · -- `E₂ < x`
    rw [Set.indicator_of_notMem (fun hx : x ∈ Set.Icc E₁ E₂ => absurd hx.2 (not_le.mpr h')),
      sub_zero]
    rw [show |x - E₂| / η = (x - E₂) / η by rw [abs_of_pos (by linarith : 0 < x - E₂)]] at t2
    have hA : Real.arctan ((E₂ - x) / η) = -Real.arctan ((x - E₂) / η) := by
      rw [← Real.arctan_neg]; congr 1; ring
    have hB : Real.arctan ((E₁ - x) / η) = -Real.arctan ((x - E₁) / η) := by
      rw [← Real.arctan_neg]; congr 1; ring
    have hmono : Real.arctan ((x - E₂) / η) ≤ Real.arctan ((x - E₁) / η) :=
      Real.arctan_mono (div_le_div_of_nonneg_right (by linarith) hη.le)
    have ha1 := Real.arctan_lt_pi_div_two ((x - E₁) / η)
    have ha2 := Real.neg_pi_div_two_lt_arctan ((x - E₂) / η)
    rw [hA, hB, abs_of_nonneg (div_nonneg (by linarith) hpi.le)]
    calc (-Real.arctan ((x - E₂) / η) - -Real.arctan ((x - E₁) / η)) / Real.pi
        ≤ (Real.pi / 2 - Real.arctan ((x - E₂) / η)) / Real.pi :=
          div_le_div_of_nonneg_right (by linarith) hpi.le
      _ ≤ _ := by linarith

/-! ## Dyadic smoothing bounds -/

/-- Pointwise dyadic bound: `η/(d + η) ≤ 4η ∑_{l ≤ L} 2^l η/(d² + (2^l η)²) + 2^{−L}`. -/
private lemma shell_bound {η d : ℝ} (hη : 0 < η) (hd : 0 ≤ d) (L : ℕ) :
    η / (d + η) ≤ 4 * η * ∑ l ∈ Finset.range (L + 1),
        (2 ^ l * η) / (d ^ 2 + (2 ^ l * η) ^ 2) + 1 / 2 ^ L := by
  have hnn : ∀ l : ℕ, 0 ≤ (2 ^ l * η) / (d ^ 2 + (2 ^ l * η) ^ 2) := fun l => by positivity
  have hsingle : ∀ l ≤ L, (2 ^ l * η) / (d ^ 2 + (2 ^ l * η) ^ 2) ≤
      ∑ l' ∈ Finset.range (L + 1), (2 ^ l' * η) / (d ^ 2 + (2 ^ l' * η) ^ 2) := fun l hl =>
    Finset.single_le_sum (f := fun l' : ℕ => (2 ^ l' * η) / (d ^ 2 + (2 ^ l' * η) ^ 2))
      (fun l' _ => hnn l') (Finset.mem_range.2 (Nat.lt_succ_of_le hl))
  have hpos : 0 < 1 / (2 : ℝ) ^ L := by positivity
  have hsum0 : 0 ≤ ∑ l ∈ Finset.range (L + 1), (2 ^ l * η) / (d ^ 2 + (2 ^ l * η) ^ 2) :=
    Finset.sum_nonneg fun l _ => hnn l
  by_cases hex : ∃ l, d ≤ 2 ^ l * η ∧ l ≤ L
  · have hP : ∃ l, d ≤ 2 ^ l * η := by
      obtain ⟨l, hl, -⟩ := hex
      exact ⟨l, hl⟩
    obtain ⟨l₁, h₁, hl₁⟩ := hex
    have hl₀ : Nat.find hP ≤ L := (Nat.find_min' hP h₁).trans hl₁
    have hspec : d ≤ 2 ^ Nat.find hP * η := Nat.find_spec hP
    have hterm := hsingle _ hl₀
    generalize hl : Nat.find hP = l₀ at hl₀ hspec hterm
    rcases l₀ with _ | l'
    · simp only [pow_zero, one_mul] at hspec hterm
      have h1 : η / (d + η) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      have h2 : 1 ≤ 4 * η * (η / (d ^ 2 + η ^ 2)) := by
        rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
        nlinarith
      have : 4 * η * (η / (d ^ 2 + η ^ 2)) ≤
          4 * η * ∑ l ∈ Finset.range (L + 1), (2 ^ l * η) / (d ^ 2 + (2 ^ l * η) ^ 2) :=
        mul_le_mul_of_nonneg_left hterm (by positivity)
      linarith
    · have hnot : 2 ^ l' * η < d :=
        lt_of_not_ge (Nat.find_min hP (by omega : l' < Nat.find hP))
      have hw : 0 < 2 ^ l' * η := by positivity
      have hy : (2 : ℝ) ^ (l' + 1) * η = 2 * (2 ^ l' * η) := by ring
      rw [hy] at hspec hterm
      have h1 : η / (d + η) ≤ η / (2 ^ l' * η) :=
        div_le_div_of_nonneg_left hη.le hw (by linarith)
      have h2 : η / (2 ^ l' * η) ≤ 4 * η * ((2 * (2 ^ l' * η)) /
          (d ^ 2 + (2 * (2 ^ l' * η)) ^ 2)) := by
        rw [← mul_div_assoc, div_le_div_iff₀ hw (by positivity)]
        have hd2 : d ^ 2 ≤ (2 * (2 ^ l' * η)) ^ 2 := pow_le_pow_left₀ hd hspec 2
        nlinarith [mul_le_mul_of_nonneg_left hd2 hη.le]
      have : 4 * η * ((2 * (2 ^ l' * η)) / (d ^ 2 + (2 * (2 ^ l' * η)) ^ 2)) ≤
          4 * η * ∑ l ∈ Finset.range (L + 1), (2 ^ l * η) / (d ^ 2 + (2 ^ l * η) ^ 2) := by
        exact mul_le_mul_of_nonneg_left hterm (by positivity)
      linarith
  · have hd2 : 2 ^ L * η < d := by
      by_contra hcon
      exact hex ⟨L, not_lt.mp hcon, le_rfl⟩
    have h1 : η / (d + η) ≤ 1 / 2 ^ L := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have : 0 ≤ 4 * η * ∑ l ∈ Finset.range (L + 1), (2 ^ l * η) / (d ^ 2 + (2 ^ l * η) ^ 2) :=
      by positivity
    linarith

/-- `t ↦ y / ((t − E)² + y²)` is integrable against a finite measure. -/
private lemma integrable_lorentz (μ : Measure ℝ) [IsFiniteMeasure μ] (E : ℝ) {y : ℝ}
    (hy : 0 < y) : Integrable (fun t : ℝ => y / ((t - E) ^ 2 + y ^ 2)) μ := by
  refine Integrable.of_bound ?_ (1 / y) (ae_of_all _ fun t => ?_)
  · exact (continuous_const.div (by fun_prop) fun t => by positivity).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_le_div_iff₀ (by positivity) hy]
    nlinarith [sq_nonneg (t - E)]

/-- Dyadic bound of `∑_j η/(|λ_j − E| + η)` by `Im s` at heights `2^l η`, `l ≤ L`. -/
theorem smooth_sum_le {K : ℕ} (lam : Fin K → ℝ) (E η : ℝ) (hη : 0 < η) (L : ℕ) :
    ∑ j, η / (|lam j - E| + η) ≤
      4 * K * η * ∑ l ∈ Finset.range (L + 1),
          (empStieltjes lam (↑E + ↑(2 ^ l * η) * Complex.I)).im + K / 2 ^ L := by
  simp_rw [emp_im]
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp
  have hKne : (K : ℝ) ≠ 0 := by positivity
  calc ∑ j, η / (|lam j - E| + η)
      ≤ ∑ j, (4 * η * ∑ l ∈ Finset.range (L + 1),
          (2 ^ l * η) / ((lam j - E) ^ 2 + (2 ^ l * η) ^ 2) + 1 / 2 ^ L) :=
        Finset.sum_le_sum fun j _ => by
          have := shell_bound hη (abs_nonneg (lam j - E)) L
          rwa [sq_abs] at this
    _ = 4 * η * ∑ l ∈ Finset.range (L + 1), ∑ j,
          (2 ^ l * η) / ((lam j - E) ^ 2 + (2 ^ l * η) ^ 2) + K / 2 ^ L := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
        simp
        ring
    _ = _ := by
        rw [← Finset.mul_sum]
        field_simp

/-- `t ↦ η / (|t − E| + η)` is integrable against a finite measure. -/
private lemma integrable_decay (μ : Measure ℝ) [IsFiniteMeasure μ] (E η : ℝ) (hη : 0 < η) :
    Integrable (fun x : ℝ => η / (|x - E| + η)) μ := by
  refine Integrable.of_bound ?_ 1 (ae_of_all _ fun t => ?_)
  · exact (continuous_const.div (by fun_prop) fun t => by positivity).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_le_one (by positivity)]
    linarith [abs_nonneg (t - E)]

/-- The same bound for `ϱ` and `m`. -/
theorem smooth_int_le (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) (E η : ℝ) (hη : 0 < η)
    (L : ℕ) :
    ∫ x, η / (|x - E| + η) ∂(varrho N σ) ≤
      4 * η * ∑ l ∈ Finset.range (L + 1), (mFun N σ (↑E + ↑(2 ^ l * η) * Complex.I)).im +
        1 / 2 ^ L := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  have hy : ∀ l : ℕ, 0 < 2 ^ l * η := fun l => by positivity
  rw [Finset.sum_congr rfl fun l _ => mFun_im_eq σ hσ hN E (hy l)]
  have hint : ∀ l : ℕ, Integrable (fun t : ℝ => (2 ^ l * η) / ((t - E) ^ 2 + (2 ^ l * η) ^ 2))
      (varrho N σ) := fun l => integrable_lorentz _ E (hy l)
  have hsumint : Integrable (fun t : ℝ => 4 * η * ∑ l ∈ Finset.range (L + 1),
      (2 ^ l * η) / ((t - E) ^ 2 + (2 ^ l * η) ^ 2)) (varrho N σ) :=
    (integrable_finsetSum _ fun l _ => hint l).const_mul _
  have hrhs : 4 * η * ∑ l ∈ Finset.range (L + 1),
      ∫ t, (2 ^ l * η) / ((t - E) ^ 2 + (2 ^ l * η) ^ 2) ∂(varrho N σ) + 1 / 2 ^ L =
      ∫ t, (4 * η * ∑ l ∈ Finset.range (L + 1),
        (2 ^ l * η) / ((t - E) ^ 2 + (2 ^ l * η) ^ 2) + 1 / 2 ^ L) ∂(varrho N σ) := by
    rw [integral_add hsumint (integrable_const _), integral_const_mul,
      integral_finsetSum _ fun l _ => hint l]
    simp
  rw [hrhs]
  refine integral_mono (integrable_decay _ E η hη) (hsumint.add (integrable_const _)) fun t => ?_
  have := shell_bound hη (abs_nonneg (t - E)) L
  rwa [sq_abs] at this

/-! ## The vertical-segment identities -/

/-- `|a / (a² + y²)| ≤ 1/y` for `y > 0`. -/
private lemma re_bound (a y : ℝ) (hy : 0 < y) : |a / (a ^ 2 + y ^ 2)| ≤ 1 / y := by
  rw [abs_div, abs_of_pos (by positivity : 0 < a ^ 2 + y ^ 2),
    div_le_div_iff₀ (by positivity) hy]
  nlinarith [sq_abs a, sq_nonneg (|a| - y), abs_nonneg a]

/-- `t ↦ (t − E) / ((t − E)² + y²)` is integrable against a finite measure. -/
private lemma integrable_lorentz_re (μ : Measure ℝ) [IsFiniteMeasure μ] (E : ℝ) {y : ℝ}
    (hy : 0 < y) : Integrable (fun t : ℝ => (t - E) / ((t - E) ^ 2 + y ^ 2)) μ := by
  refine Integrable.of_bound ?_ (1 / y) (ae_of_all _ fun t => ?_)
  · exact ((continuous_id.sub continuous_const).div (by fun_prop)
      fun t => by positivity).aestronglyMeasurable
  · rw [Real.norm_eq_abs]; exact re_bound _ _ hy

/-- The arctan difference `t ↦ arctan((E₂ − t)/y) − arctan((E₁ − t)/y)` is integrable against a
finite measure. -/
private lemma integrable_arcdiff (μ : Measure ℝ) [IsFiniteMeasure μ] (E₁ E₂ y : ℝ) :
    Integrable (fun t : ℝ => Real.arctan ((E₂ - t) / y) - Real.arctan ((E₁ - t) / y)) μ := by
  refine Integrable.of_bound ?_ Real.pi (ae_of_all _ fun t => ?_)
  · exact (by fun_prop : Continuous fun t : ℝ =>
      Real.arctan ((E₂ - t) / y) - Real.arctan ((E₁ - t) / y)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_le]
    constructor <;>
    linarith [Real.arctan_lt_pi_div_two ((E₂ - t) / y), Real.arctan_lt_pi_div_two ((E₁ - t) / y),
      Real.neg_pi_div_two_lt_arctan ((E₂ - t) / y), Real.neg_pi_div_two_lt_arctan ((E₁ - t) / y)]

/-- `y ↦ (t − E) / ((t − E)² + y²)` is interval integrable on `[η, η₀]` for `0 < η ≤ η₀`. -/
private lemma ii_re (t E η η₀ : ℝ) (hη : 0 < η) (hηη₀ : η ≤ η₀) :
    IntervalIntegrable (fun y : ℝ => (t - E) / ((t - E) ^ 2 + y ^ 2)) volume η η₀ := by
  refine ContinuousOn.intervalIntegrable ?_
  refine continuousOn_const.div (by fun_prop) fun y hy => ?_
  rw [Set.uIcc_of_le hηη₀] at hy
  have : 0 < y := lt_of_lt_of_le hη hy.1
  positivity

/-- `∫_η^{η₀} (t − E)/((t − E)² + y²) dy = arctan((E − t)/η₀) − arctan((E − t)/η)`. -/
private lemma arctan_y_term (t E η η₀ : ℝ) (hη : 0 < η) (hηη₀ : η ≤ η₀) :
    ∫ y in η..η₀, (t - E) / ((t - E) ^ 2 + y ^ 2) =
      Real.arctan ((E - t) / η₀) - Real.arctan ((E - t) / η) := by
  have hd : ∀ y ∈ Set.uIcc η η₀, HasDerivAt (fun y : ℝ => Real.arctan ((E - t) / y))
      ((t - E) / ((t - E) ^ 2 + y ^ 2)) y := by
    intro y hy
    rw [Set.uIcc_of_le hηη₀] at hy
    have hy0 : 0 < y := lt_of_lt_of_le hη hy.1
    have h1 : HasDerivAt (fun y : ℝ => (E - t) / y) (-(E - t) / y ^ 2) y := by
      have := (hasDerivAt_const y (E - t)).div (hasDerivAt_id y) hy0.ne'
      convert this using 1
      · rfl
      · simp
    have := h1.arctan
    convert this using 1
    have : (t - E) ^ 2 = (E - t) ^ 2 := by ring
    rw [this]
    field_simp
    ring
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt hd (ii_re t E η η₀ hη hηη₀))

/-- The `y`-integral of the real parts at `E₂` and `E₁` for a point mass at `t`. -/
private lemma g_integral (t E₁ E₂ η η₀ : ℝ) (hη : 0 < η) (hηη₀ : η ≤ η₀) :
    ∫ y in η..η₀, ((t - E₂) / ((t - E₂) ^ 2 + y ^ 2) - (t - E₁) / ((t - E₁) ^ 2 + y ^ 2)) =
      (Real.arctan ((E₂ - t) / η₀) - Real.arctan ((E₁ - t) / η₀)) -
        (Real.arctan ((E₂ - t) / η) - Real.arctan ((E₁ - t) / η)) := by
  rw [intervalIntegral.integral_sub (ii_re t E₂ η η₀ hη hηη₀) (ii_re t E₁ η η₀ hη hηη₀),
    arctan_y_term t E₂ η η₀ hη hηη₀, arctan_y_term t E₁ η η₀ hη hηη₀]
  ring

/-- Vertical-segment identity for the Stieltjes transform of the eigenvalues:
`∫ Im s(x + iη) dx` over `[E₁, E₂]` equals the same at `η₀` minus
`∫_η^{η₀} (Re s(E₂ + iy) − Re s(E₁ + iy)) dy`. -/
theorem segment_identity {K : ℕ} (lam : Fin K → ℝ) (E₁ E₂ η η₀ : ℝ) (hη : 0 < η)
    (hηη₀ : η ≤ η₀) :
    (∫ x in E₁..E₂, (empStieltjes lam (↑x + ↑η * Complex.I)).im) =
      (∫ x in E₁..E₂, (empStieltjes lam (↑x + ↑η₀ * Complex.I)).im) -
        ∫ y in η..η₀, ((empStieltjes lam (↑E₂ + ↑y * Complex.I)).re -
          (empStieltjes lam (↑E₁ + ↑y * Complex.I)).re) := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp [emp_im, emp_re]
  have hKne : (K : ℝ) ≠ 0 := by positivity
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, ∀ y, G y = ∑ j,
      (Real.arctan ((E₂ - lam j) / y) - Real.arctan ((E₁ - lam j) / y)) :=
    ⟨fun y => ∑ j, (Real.arctan ((E₂ - lam j) / y) - Real.arctan ((E₁ - lam j) / y)),
      fun y => rfl⟩
  have him : ∀ y : ℝ, 0 < y → ∫ x in E₁..E₂, (empStieltjes lam (↑x + ↑y * Complex.I)).im =
      (K : ℝ)⁻¹ * G y :=
    fun y hy => by
      rw [hG y, ← arctan_count lam E₁ E₂ y hy, ← mul_assoc, inv_mul_cancel₀ hKne, one_mul]
  have hre : ∫ y in η..η₀, ((empStieltjes lam (↑E₂ + ↑y * Complex.I)).re -
        (empStieltjes lam (↑E₁ + ↑y * Complex.I)).re) = (K : ℝ)⁻¹ * (G η₀ - G η) := by
    have h1 : ∀ y : ℝ, (empStieltjes lam (↑E₂ + ↑y * Complex.I)).re -
        (empStieltjes lam (↑E₁ + ↑y * Complex.I)).re = (K : ℝ)⁻¹ * ∑ j,
          ((lam j - E₂) / ((lam j - E₂) ^ 2 + y ^ 2) -
            (lam j - E₁) / ((lam j - E₁) ^ 2 + y ^ 2)) := fun y => by
      rw [emp_re, emp_re, Finset.sum_sub_distrib]; ring
    simp_rw [h1]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum, hG, hG]
    · simp_rw [g_integral _ E₁ E₂ η η₀ hη hηη₀]
      rw [Finset.sum_sub_distrib]
    · intro j _
      exact (ii_re _ E₂ η η₀ hη hηη₀).sub (ii_re _ E₁ η η₀ hη hηη₀)
  rw [him η hη, him η₀ (hη.trans_le hηη₀), hre]
  ring

/-- The vertical-segment identity for `m`. -/
theorem segment_identity_m (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) (E₁ E₂ η η₀ : ℝ)
    (hη : 0 < η) (hηη₀ : η ≤ η₀) :
    (∫ x in E₁..E₂, (mFun N σ (↑x + ↑η * Complex.I)).im) =
      (∫ x in E₁..E₂, (mFun N σ (↑x + ↑η₀ * Complex.I)).im) -
        ∫ y in η..η₀, ((mFun N σ (↑E₂ + ↑y * Complex.I)).re -
          (mFun N σ (↑E₁ + ↑y * Complex.I)).re) := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  have hη₀ : 0 < η₀ := hη.trans_le hηη₀
  rw [arctan_count_varrho σ hσ hN E₁ E₂ η hη, arctan_count_varrho σ hσ hN E₁ E₂ η₀ hη₀]
  have h1 : ∫ y in η..η₀, ((mFun N σ (↑E₂ + ↑y * Complex.I)).re -
        (mFun N σ (↑E₁ + ↑y * Complex.I)).re) =
      ∫ y in η..η₀, ∫ t, ((t - E₂) / ((t - E₂) ^ 2 + y ^ 2) -
        (t - E₁) / ((t - E₁) ^ 2 + y ^ 2)) ∂(varrho N σ) := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [Set.uIcc_of_le hηη₀] at hy
    have hy0 : 0 < y := lt_of_lt_of_le hη hy.1
    rw [mFun_re_eq σ hσ hN E₂ hy0, mFun_re_eq σ hσ hN E₁ hy0,
      ← integral_sub (integrable_lorentz_re _ E₂ hy0) (integrable_lorentz_re _ E₁ hy0)]
  have hsw := swap_ivl (μ := varrho N σ) (fun y t => ((t - E₂) / ((t - E₂) ^ 2 + y ^ 2) -
        (t - E₁) / ((t - E₁) ^ 2 + y ^ 2)))
    (by unfold Function.uncurry; fun_prop) (a := η) (b := η₀) (C := 1 / η + 1 / η) (by
      intro y hy t
      rw [Set.uIoc_of_le hηη₀] at hy
      have hy0 : 0 < y := lt_of_lt_of_le hη hy.1.le
      have hyη : 1 / y ≤ 1 / η := one_div_le_one_div_of_le hη hy.1.le
      calc |(t - E₂) / ((t - E₂) ^ 2 + y ^ 2) - (t - E₁) / ((t - E₁) ^ 2 + y ^ 2)|
          ≤ |(t - E₂) / ((t - E₂) ^ 2 + y ^ 2)| + |(t - E₁) / ((t - E₁) ^ 2 + y ^ 2)| :=
            abs_sub _ _
        _ ≤ 1 / η + 1 / η := add_le_add ((re_bound _ _ hy0).trans hyη)
            ((re_bound _ _ hy0).trans hyη))
  beta_reduce at hsw
  rw [h1, hsw]
  have h2 : ∫ t, (∫ y in η..η₀, ((t - E₂) / ((t - E₂) ^ 2 + y ^ 2) -
        (t - E₁) / ((t - E₁) ^ 2 + y ^ 2))) ∂(varrho N σ) =
      ∫ t, ((Real.arctan ((E₂ - t) / η₀) - Real.arctan ((E₁ - t) / η₀)) -
        (Real.arctan ((E₂ - t) / η) - Real.arctan ((E₁ - t) / η))) ∂(varrho N σ) :=
    integral_congr_ae (ae_of_all _ fun t => g_integral t E₁ E₂ η η₀ hη hηη₀)
  rw [h2, integral_sub (integrable_arcdiff _ E₁ E₂ η₀) (integrable_arcdiff _ E₁ E₂ η)]
  ring

/-! ## The counting comparison -/

/-- `ϱ({x}) = 0` for `x > 0`: the only atom of `ϱ` is at `0`. -/
private lemma seg_varrho_singleton (N : ℕ) (σ : Fin M → ℝ) {x : ℝ} (hx : 0 < x) :
    varrho N σ {x} = 0 := by
  have hA : MeasurableSet ({x} : Set ℝ) := measurableSet_singleton x
  have hsub : ({x} : Set ℝ) ⊆ Set.Ioi 0 := fun y hy => by
    rw [Set.mem_singleton_iff.mp hy]; exact hx
  have h0 : (0 : ℝ) ∉ ({x} : Set ℝ) := fun h => hx.ne (Set.mem_singleton_iff.mp h)
  rw [varrho, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hA,
    Set.indicator_of_notMem h0, smul_zero, zero_add, withDensity_apply _ hA,
    Measure.restrict_restrict hA, Set.inter_eq_left.mpr hsub]
  exact setLIntegral_measure_zero _ _ Real.volume_singleton

/-- `x ↦ Im m(x + iη)` is continuous for `η > 0`. -/
private lemma continuous_im_mFun (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {η : ℝ}
    (hη : 0 < η) : Continuous fun x : ℝ => (mFun N σ (↑x + ↑η * Complex.I)).im := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  simp_rw [mFun_im_eq σ hσ hN _ hη]
  refine continuous_of_dominated (bound := fun _ => 1 / η)
    (fun x => (integrable_lorentz (varrho N σ) x hη).aestronglyMeasurable)
    (fun x => ae_of_all _ fun t => ?_) (integrable_const _)
    (ae_of_all _ fun t => continuous_const.div (by fun_prop) fun x => by positivity)
  rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_le_div_iff₀ (by positivity) hη]
  nlinarith [sq_nonneg (t - x)]

/-- The count of eigenvalues in `[E₁, E₂)` as a sum of indicators. -/
private lemma count_eq_sum {K : ℕ} (lam : Fin K → ℝ) {E₁ E₂ : ℝ} (h12 : E₁ ≤ E₂) :
    ((Finset.univ.filter fun j => E₁ ≤ lam j).card : ℝ) -
        (Finset.univ.filter fun j => E₂ ≤ lam j).card =
      ∑ j, (Set.Ico E₁ E₂).indicator (fun _ => (1 : ℝ)) (lam j) := by
  rw [Finset.natCast_card_filter, Finset.natCast_card_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h1 : E₁ ≤ lam j <;> by_cases h2 : E₂ ≤ lam j
  · simp [Set.indicator, h1, h2, not_lt.mpr h2]
  · simp [Set.indicator, h1, h2, not_le.mp h2]
  · exact absurd (h12.trans h2) h1
  · simp [Set.indicator, h1, h2]

/-- Pointwise: the indicator of `[E₁, E₂)` against the smoothed indicator. -/
private lemma point_bound {E₁ E₂ η : ℝ} (hη : 0 < η) (h12 : E₁ ≤ E₂) (t : ℝ) :
    |(Set.Ico E₁ E₂).indicator (fun _ => (1 : ℝ)) t -
        (Real.arctan ((E₂ - t) / η) - Real.arctan ((E₁ - t) / η)) / Real.pi| ≤
      3 * (η / (|t - E₁| + η) + η / (|t - E₂| + η)) := by
  have h := arctan_indicator_le (x := t) hη h12
  have ha1 : 0 < η / (|t - E₁| + η) := by positivity
  have ha2 : 0 < η / (|t - E₂| + η) := by positivity
  have e1 : 2 * η / (|t - E₁| + η) = 2 * (η / (|t - E₁| + η)) := by ring
  have e2 : 2 * η / (|t - E₂| + η) = 2 * (η / (|t - E₂| + η)) := by ring
  rw [e1, e2] at h
  by_cases ht : t = E₂
  · subst ht
    have hI : (Set.Icc E₁ t).indicator (fun _ => (1 : ℝ)) t = 1 :=
      Set.indicator_of_mem (show t ∈ Set.Icc E₁ t from ⟨h12, le_rfl⟩) _
    have hd : η / (|t - t| + η) = 1 := by simp [div_self hη.ne']
    rw [Set.indicator_of_notMem (by simp), zero_sub, abs_neg]
    rw [hI] at h
    rw [hd] at h ⊢
    have := abs_add_le (((Real.arctan ((t - t) / η) - Real.arctan ((E₁ - t) / η)) / Real.pi - 1))
      1
    simp only [sub_add_cancel] at this
    linarith
  · have hsame : (Set.Ico E₁ E₂).indicator (fun _ => (1 : ℝ)) t =
        (Set.Icc E₁ E₂).indicator (fun _ => (1 : ℝ)) t := by
      by_cases hm : t ∈ Set.Ico E₁ E₂
      · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (Set.Ico_subset_Icc_self hm)]
      · have : t ∉ Set.Icc E₁ E₂ := fun hc =>
          hm ⟨hc.1, lt_of_le_of_ne hc.2 ht⟩
        rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem this]
    rw [hsame, abs_sub_comm]
    linarith

/-- `n(E₁) − n(E₂) = N ϱ([E₁, E₂])` for `0 < E₂`, `E₁ ≤ E₂`. -/
private lemma nClass_sub (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {E₁ E₂ : ℝ}
    (h12 : E₁ ≤ E₂) (hE₂ : 0 < E₂) :
    nClass N σ E₁ - nClass N σ E₂ =
      N * ∫ t, (Set.Icc E₁ E₂).indicator (fun _ => (1 : ℝ)) t ∂(varrho N σ) := by
  have hprob := isProbabilityMeasure_varrho N σ hσ hN
  have hI : ∫ t, (Set.Icc E₁ E₂).indicator (fun _ => (1 : ℝ)) t ∂(varrho N σ) =
      (varrho N σ (Set.Icc E₁ E₂)).toReal := by
    simp [Measure.real]
  have hIcc : varrho N σ (Set.Icc E₁ E₂) = varrho N σ (Set.Ico E₁ E₂) := by
    refine le_antisymm ?_ (measure_mono Set.Ico_subset_Icc_self)
    rw [← Set.Ico_insert_right h12, Set.insert_eq]
    exact (measure_union_le _ _).trans (by rw [seg_varrho_singleton N σ hE₂, zero_add])
  have hsplit : varrho N σ (Set.Ici E₁) =
      varrho N σ (Set.Ico E₁ E₂) + varrho N σ (Set.Ici E₂) := by
    rw [← measure_union _ measurableSet_Ici, Set.Ico_union_Ici_eq_Ici h12]
    rw [Set.disjoint_left]
    intro z hz1 hz2
    exact absurd hz1.2 (not_lt.mpr hz2)
  unfold nClass
  rw [hI, hIcc, hsplit, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  ring

/-- Counting comparison: the eigenvalue count in `[E₁, E₂)` minus `n(E₁) − n(E₂)` is bounded by the
integral of `Im (s − m)` along `[E₁, E₂] + iη` and the smoothing errors at `E₁`, `E₂`. -/
theorem count_compare (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) (lam : Fin N → ℝ)
    {E₁ E₂ η : ℝ} (hη : 0 < η) (h12 : E₁ ≤ E₂) (hE₁ : 0 < E₁) :
    |((Finset.univ.filter fun j => E₁ ≤ lam j).card : ℝ) -
        (Finset.univ.filter fun j => E₂ ≤ lam j).card - (nClass N σ E₁ - nClass N σ E₂)| ≤
      N * |∫ x in E₁..E₂,
          (empStieltjes lam (↑x + ↑η * Complex.I) - mFun N σ (↑x + ↑η * Complex.I)).im| /
          Real.pi +
        3 * ∑ j, (η / (|lam j - E₁| + η) + η / (|lam j - E₂| + η)) +
        2 * N * ∫ x, (η / (|x - E₁| + η) + η / (|x - E₂| + η)) ∂(varrho N σ) := by
  have hprob := isProbabilityMeasure_varrho N σ hσ hN
  have hpi := Real.pi_pos
  have hE₂ : 0 < E₂ := lt_of_lt_of_le hE₁ h12
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hIm_s : Continuous fun x : ℝ => (empStieltjes lam (↑x + ↑η * Complex.I)).im := by
    simp_rw [emp_im]
    exact continuous_const.mul (continuous_finsetSum _ fun j _ => cont_lorentz (lam j) η hη)
  have hIm_m := continuous_im_mFun σ hσ hN hη
  have hint : ∫ x in E₁..E₂,
      (empStieltjes lam (↑x + ↑η * Complex.I) - mFun N σ (↑x + ↑η * Complex.I)).im =
      (∫ x in E₁..E₂, (empStieltjes lam (↑x + ↑η * Complex.I)).im) -
        ∫ x in E₁..E₂, (mFun N σ (↑x + ↑η * Complex.I)).im := by
    simp_rw [Complex.sub_im]
    exact intervalIntegral.integral_sub (hIm_s.intervalIntegrable _ _)
      (hIm_m.intervalIntegrable _ _)
  have hK := arctan_count lam E₁ E₂ η hη
  have hM := arctan_count_varrho σ hσ hN E₁ E₂ η hη
  rw [hint, count_eq_sum lam h12, nClass_sub σ hσ hN h12 hE₂]
  have hA : |∑ j, (Set.Ico E₁ E₂).indicator (fun _ => (1 : ℝ)) (lam j) -
      (∑ j, (Real.arctan ((E₂ - lam j) / η) - Real.arctan ((E₁ - lam j) / η))) / Real.pi| ≤
      3 * ∑ j, (η / (|lam j - E₁| + η) + η / (|lam j - E₂| + η)) := by
    rw [Finset.sum_div, ← Finset.sum_sub_distrib, Finset.mul_sum]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun j _ => point_bound hη h12 (lam j))
  have hC : |(∫ t, (Real.arctan ((E₂ - t) / η) - Real.arctan ((E₁ - t) / η)) ∂(varrho N σ)) /
        Real.pi - ∫ t, (Set.Icc E₁ E₂).indicator (fun _ => (1 : ℝ)) t ∂(varrho N σ)| ≤
      2 * ∫ x, (η / (|x - E₁| + η) + η / (|x - E₂| + η)) ∂(varrho N σ) := by
    have hFint := integrable_arcdiff (varrho N σ) E₁ E₂ η
    have hind : Integrable (fun t : ℝ => (Set.Icc E₁ E₂).indicator (fun _ => (1 : ℝ)) t)
        (varrho N σ) := (integrable_const (1 : ℝ)).indicator measurableSet_Icc
    have hg : Integrable (fun x : ℝ => η / (|x - E₁| + η) + η / (|x - E₂| + η)) (varrho N σ) :=
      (integrable_decay _ E₁ η hη).add (integrable_decay _ E₂ η hη)
    rw [← integral_div, ← integral_sub (hFint.div_const _) hind, ← integral_const_mul]
    refine (Real.norm_eq_abs _ ▸ norm_integral_le_of_norm_le (hg.const_mul 2)
      (ae_of_all _ fun t => ?_))
    rw [Real.norm_eq_abs]
    have := arctan_indicator_le (x := t) hη h12
    calc |(Real.arctan ((E₂ - t) / η) - Real.arctan ((E₁ - t) / η)) / Real.pi -
          (Set.Icc E₁ E₂).indicator (fun _ => (1 : ℝ)) t|
        ≤ 2 * η / (|t - E₁| + η) + 2 * η / (|t - E₂| + η) := this
      _ = 2 * (η / (|t - E₁| + η) + η / (|t - E₂| + η)) := by ring
  have hrw : ∑ j, (Set.Ico E₁ E₂).indicator (fun _ => (1 : ℝ)) (lam j) -
      N * ∫ t, (Set.Icc E₁ E₂).indicator (fun _ => (1 : ℝ)) t ∂(varrho N σ) =
      (∑ j, (Set.Ico E₁ E₂).indicator (fun _ => (1 : ℝ)) (lam j) -
        (∑ j, (Real.arctan ((E₂ - lam j) / η) - Real.arctan ((E₁ - lam j) / η))) / Real.pi) +
      N * ((∫ x in E₁..E₂, (empStieltjes lam (↑x + ↑η * Complex.I)).im) -
        ∫ x in E₁..E₂, (mFun N σ (↑x + ↑η * Complex.I)).im) / Real.pi +
      N * ((∫ t, (Real.arctan ((E₂ - t) / η) - Real.arctan ((E₁ - t) / η)) ∂(varrho N σ)) /
        Real.pi - ∫ t, (Set.Icc E₁ E₂).indicator (fun _ => (1 : ℝ)) t ∂(varrho N σ)) := by
    rw [← hK, ← hM]
    field_simp
    ring
  rw [hrw]
  have hB : |(N : ℝ) * ((∫ x in E₁..E₂, (empStieltjes lam (↑x + ↑η * Complex.I)).im) -
        ∫ x in E₁..E₂, (mFun N σ (↑x + ↑η * Complex.I)).im) / Real.pi| =
      N * |(∫ x in E₁..E₂, (empStieltjes lam (↑x + ↑η * Complex.I)).im) -
        ∫ x in E₁..E₂, (mFun N σ (↑x + ↑η * Complex.I)).im| / Real.pi := by
    rw [abs_div, abs_mul, abs_of_nonneg hN0, abs_of_pos hpi]
  refine (abs_add_three _ _ _).trans ?_
  rw [hB, abs_mul, abs_of_nonneg hN0]
  have := mul_le_mul_of_nonneg_left hC hN0
  nlinarith [hA, this]

/-! ## Concrete instances

A single eigenvalue `λ = 0` (`K = 1`) for the deterministic statements, and the Marchenko–Pastur
instance `M = 1`, `N = 2`, `σ = 1` for the statements about `m` and `ϱ`. -/

/-- `arctan_count` at `λ = 0`, `[E₁, E₂] = [−1, 1]`, `η = 1`: the integral is `π/2`. -/
example : ∫ x in (-1 : ℝ)..1,
    (empStieltjes (![0] : Fin 1 → ℝ) (↑x + ↑(1 : ℝ) * Complex.I)).im = Real.pi / 2 := by
  have h := arctan_count (![0] : Fin 1 → ℝ) (-1) 1 1 one_pos
  simp only [Nat.cast_one, one_mul, Fin.sum_univ_one] at h
  rw [h]
  simp [Real.arctan_one, Real.arctan_neg]
  ring

/-- `arctan_count_varrho` at MP, `[E₁, E₂] = [1/2, 3]`, `η = 1/2`. -/
example := arctan_count_varrho (N := 2) (fun _ : Fin 1 => (1 : ℝ)) (fun _ => by norm_num)
  (by norm_num) (1 / 2) 3 (1 / 2) (by norm_num)

/-- `arctan_indicator_le` at `[E₁, E₂] = [0, 1]`, `η = 1`, `x = 1/2`. -/
example := arctan_indicator_le (E₁ := 0) (E₂ := 1) (η := 1) (x := 1 / 2) one_pos zero_le_one

/-- `smooth_sum_le` at `λ = 0`, `E = 0`, `η = 1`, `L = 2`. -/
example := smooth_sum_le (![0] : Fin 1 → ℝ) 0 1 one_pos 2

/-- `smooth_int_le` at MP, `E = 1`, `η = 1/2`, `L = 2`. -/
example := smooth_int_le (N := 2) (fun _ : Fin 1 => (1 : ℝ)) (fun _ => by norm_num)
  (by norm_num) 1 (1 / 2) (by norm_num) 2

/-- `segment_identity` at `λ = 0`, `[E₁, E₂] = [−1, 1]`, `η = 1`, `η₀ = 2`. -/
example := segment_identity (![0] : Fin 1 → ℝ) (-1) 1 1 2 one_pos (by norm_num)

/-- `segment_identity_m` at MP, `[E₁, E₂] = [1/2, 3]`, `η = 1/2`, `η₀ = 1`. -/
example := segment_identity_m (N := 2) (fun _ : Fin 1 => (1 : ℝ)) (fun _ => by norm_num)
  (by norm_num) (1 / 2) 3 (1 / 2) 1 (by norm_num) (by norm_num)

/-- `count_compare` at MP with the eigenvalues `λ = (1, 0)` of `XᵀΣX` for `Σ = 1`,
`X = (1/√2, 1/√2)`, `[E₁, E₂] = [1/2, 3]`, `η = 1/10`: the count in `[1/2, 3)` is `1`. -/
example := count_compare (N := 2) (fun _ : Fin 1 => (1 : ℝ)) (fun _ => by norm_num)
  (by norm_num) (![1, 0] : Fin 2 → ℝ) (E₁ := 1 / 2) (E₂ := 3) (η := 1 / 10) (by norm_num)
  (by norm_num) (by norm_num)

end Anisotropic
