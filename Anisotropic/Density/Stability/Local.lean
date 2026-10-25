import Anisotropic.Density.GenProp
import Anisotropic.Density.SelfConsistent
import Anisotropic.Density.Stability.Bulk
import Anisotropic.Density.Stability.Defs
import Anisotropic.Density.Stability.Domains
import Anisotropic.Density.Stability.Quadratic

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # Lemma A.6 with the hypothesis `Im m ≥ c_b` on a spectral domain (weak stability with `K₀ = 0`) -/

/-- `|β| ≥ min(1, 2 sin² θ₀)`, `sin θ₀ = (c_b/C_m)(τ/(C_m+τ))`, for a lower bound `c_b` of
`Im m`. -/
def locCbeta (τ cb : ℝ) : ℝ := min 1 (2 * (cb / mBoundConst τ * (τ / (mBoundConst τ + τ))) ^ 2)

/-- `|u m| ≤ C_ε` for `|u − m| ≤ c_b/2`. -/
def locCeps (τ cb : ℝ) : ℝ := (mBoundConst τ + cb / 2) * mBoundConst τ

/-- The minimal `C₀` of the weak stability with `Im m ≥ c_b`. -/
def locC0wmin (τ cb : ℝ) : ℝ :=
  max (4 * (mBoundConst τ + 1)) (2 * locCeps τ cb / locCbeta τ cb * (mBoundConst τ + 1))

/-- `bulkC0wmin` is the case `c_b = c_b(τ, τ', c)`. -/
example (τ τ' : ℝ) (c : ℝ → ℝ) : bulkC0wmin τ τ' c = locC0wmin τ (bulkcb τ τ' c) := rfl

/-- `|α| ≤ C_α` for `|u − m| ≤ c_b/2`. -/
private def locCalpha (τ cb : ℝ) : ℝ :=
  τ⁻¹ * mBoundConst τ * (1 + mBoundConst τ / cb) * 2 / cb ^ 2

private lemma loc_empMeasure_apply (σ : Fin M → ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    empMeasure σ s = (M : ℝ≥0∞)⁻¹ * ((Finset.univ.filter fun i => σ i ∈ s).card : ℝ≥0∞) := by
  simp only [empMeasure, Measure.smul_apply, Measure.finsetSum_apply,
    Measure.dirac_apply' _ hs, smul_eq_mul]
  congr 1
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Set.indicator]

/-- Under the assumptions, `N > 0` and some `σ i` is positive. -/
private lemma loc_facts {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) :
    0 < N ∧ (posVals σ).Nonempty := by
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · exfalso
      have := h.phi_lower
      simp [phiRatio, h0] at this
      linarith [h.pos]
    · exact h0
  refine ⟨hN, ?_⟩
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have hM : M ≠ 0 := by
    rintro rfl
    have := h.phi_lower
    simp [phiRatio] at this
    linarith [h.pos]
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
  rw [loc_empMeasure_apply σ measurableSet_Icc] at hgap
  simp only [hall, Set.mem_Icc, le_refl, h.pos.le, and_self, Finset.filter_true,
    Finset.card_univ, Fintype.card_fin] at hgap
  have hM' : (M : ℝ≥0∞)⁻¹ * (M : ℝ≥0∞) = 1 :=
    ENNReal.inv_mul_cancel (by exact_mod_cast hM) (ENNReal.natCast_ne_top _)
  rw [hM', ENNReal.toReal_one] at hgap
  linarith [h.pos]

/-- `τ ≤ 1` under the assumptions. -/
private lemma loc_tau_le_one {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) :
    τ ≤ 1 := by
  have h1 : τ ≤ τ⁻¹ := h.phi_lower.trans h.phi_upper
  by_contra hc
  exact absurd h1 (not_le.mpr ((inv_lt_one_of_one_lt₀ (not_le.mp hc)).trans (not_le.mp hc)))

private lemma loc_mBound_pos {τ : ℝ} (hτ : 0 < τ) : 0 < mBoundConst τ := by
  unfold mBoundConst genPropConst
  exact div_pos (pow_pos (by linarith) 2) (pow_pos (half_pos hτ) 4)


private lemma loc_one_add_ne {a : ℝ} (ha : 0 ≤ a) {w : ℂ} (hw : 0 < w.im) :
    1 + (a : ℂ) * w ≠ 0 := by
  intro h0
  rcases ha.eq_or_lt with h | h
  · subst h
    simp at h0
  · have h1 := congrArg Complex.im h0
    simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, Complex.zero_im, zero_add] at h1
    have := mul_pos h hw
    linarith

/-- One term of `β`: `Re(m² a² / (N (1 + a m)²)) ≤ (1 - 2 s₀²) a² |m|² / (N |1 + a m|²)` when
`s₀ |m| |1 + a m| ≤ Im m`. -/
private lemma loc_re_term {m : ℂ} {a n s₀ : ℝ} (hn : 0 < n) (hm : 0 < m.im) (ha : 0 ≤ a)
    (hs : s₀ * ‖m‖ * ‖1 + (a : ℂ) * m‖ ≤ m.im) (hs₀ : 0 ≤ s₀) :
    (m ^ 2 * (a : ℂ) ^ 2 / ((n : ℂ) * (1 + a * m) ^ 2)).re ≤
      (1 - 2 * s₀ ^ 2) * (a ^ 2 * ‖m‖ ^ 2 / (n * ‖1 + (a : ℂ) * m‖ ^ 2)) := by
  set w : ℂ := 1 + (a : ℂ) * m with hwdef
  have hw : w ≠ 0 := loc_one_add_ne ha hm
  have hnw : 0 < Complex.normSq w := Complex.normSq_pos.2 hw
  have hwre : w.re = 1 + a * m.re := by simp [hwdef]
  have hwim : w.im = a * m.im := by simp [hwdef]
  have e : m ^ 2 * (a : ℂ) ^ 2 / ((n : ℂ) * w ^ 2) = ((a ^ 2 / n : ℝ) : ℂ) * (m / w) ^ 2 := by
    have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    push_cast
    field_simp
  have h1 : (m / w).im = m.im / Complex.normSq w := by
    rw [Complex.div_im, hwre, hwim]
    field_simp
    ring
  have h2 := Complex.normSq_div m w
  rw [Complex.normSq_apply (m / w), h1] at h2
  have hre2 : ((m / w) ^ 2).re =
      Complex.normSq m / Complex.normSq w - 2 * (m.im / Complex.normSq w) ^ 2 := by
    rw [pow_two, Complex.mul_re, h1]
    linear_combination h2
  rw [e, Complex.re_ofReal_mul, hre2, Complex.sq_norm, Complex.sq_norm]
  have hkey : s₀ ^ 2 * Complex.normSq m * Complex.normSq w ≤ m.im ^ 2 := by
    have h0 : 0 ≤ s₀ * ‖m‖ * ‖w‖ := by positivity
    have := pow_le_pow_left₀ h0 hs 2
    rw [mul_pow, mul_pow, Complex.sq_norm, Complex.sq_norm] at this
    exact this
  have hdiff : a ^ 2 / n * (Complex.normSq m / Complex.normSq w -
      2 * (m.im / Complex.normSq w) ^ 2) -
      (1 - 2 * s₀ ^ 2) * (a ^ 2 * Complex.normSq m / (n * Complex.normSq w)) =
      2 * a ^ 2 / (n * Complex.normSq w ^ 2) *
        (s₀ ^ 2 * Complex.normSq m * Complex.normSq w - m.im ^ 2) := by
    field_simp
    ring
  have : 2 * a ^ 2 / (n * Complex.normSq w ^ 2) *
      (s₀ ^ 2 * Complex.normSq m * Complex.normSq w - m.im ^ 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  linarith
/-- (mz_reg) on a domain where `Im m ≥ c_b`. -/
private lemma loc_mz_reg {cb : ℝ} {N : ℕ} {σ : Fin M → ℝ} {z : ℂ}
    (him : cb ≤ (mFun N σ z).im) :
    ∀ s ∈ posVals σ, cb ≤ ‖mFun N σ z + ((s⁻¹ : ℝ) : ℂ)‖ := by
  intro s _
  refine him.trans ?_
  have := Complex.abs_im_le_norm (mFun N σ z + ((s⁻¹ : ℝ) : ℂ))
  simp only [Complex.add_im, Complex.ofReal_im, add_zero] at this
  exact (le_abs_self _).trans this

/-- `Re β ≥ min(1, 2 sin² θ₀)` where `Im m ≥ c_b` (from (im_def_m)). -/
private lemma loc_beta_ge {τ cb : ℝ} {N : ℕ} {σ : Fin M → ℝ}
    (h : DensityAssumptions τ N σ) (hcb : 0 < cb) {z : ℂ} (hz : z ∈ specDomain τ N)
    (him : cb ≤ (mFun N σ z).im) :
    locCbeta τ cb ≤ (betaCoef N σ (mFun N σ z)).re := by
  obtain ⟨hN, -⟩ := loc_facts h
  have hm := gen_prop_m_specDomain h hz
  have hη := hz.1
  have hCm := loc_mBound_pos h.pos
  have hτ := h.pos
  have hdef := im_def_m (N := N) h.nonneg hη
  set m := mFun N σ z with hmdef
  set Cm := mBoundConst τ with hCmdef
  set s₀ := cb / Cm * (τ / (Cm + τ)) with hs₀def
  have hs₀ : 0 ≤ s₀ := by positivity
  have hmpos : 0 < m.im := lt_of_lt_of_le hcb him
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hterm : ∀ i, (m ^ 2 * (σ i : ℂ) ^ 2 / ((N : ℂ) * (1 + σ i * m) ^ 2)).re ≤
      (1 - 2 * s₀ ^ 2) * (σ i ^ 2 * ‖m‖ ^ 2 / (N * ‖1 + (σ i : ℂ) * m‖ ^ 2)) := by
    intro i
    have hσi := h.nonneg i
    refine loc_re_term (n := (N : ℝ)) hNpos hmpos hσi ?_ hs₀
    have hw : ‖1 + (σ i : ℂ) * m‖ ≤ 1 + τ⁻¹ * Cm := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg hσi]
      have := mul_le_mul (h.bound_Sigma i) hm.2.1 (norm_nonneg _) (inv_pos.2 hτ).le
      linarith
    have heq : s₀ * Cm * (1 + τ⁻¹ * Cm) = cb := by
      rw [hs₀def]
      field_simp
      ring
    calc s₀ * ‖m‖ * ‖1 + (σ i : ℂ) * m‖ ≤ s₀ * Cm * (1 + τ⁻¹ * Cm) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hm.2.1 hs₀) hw (norm_nonneg _) (by positivity)
      _ = cb := heq
      _ ≤ m.im := him
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
  rw [← Finset.mul_sum, hdef] at hsum
  have hS0 : 0 ≤ 1 - ‖m‖ ^ 2 * z.im / m.im := by
    rw [← hdef]
    exact Finset.sum_nonneg fun i _ => by positivity
  have hS1 : 0 ≤ ‖m‖ ^ 2 * z.im / m.im := by positivity
  unfold betaCoef
  rw [Complex.sub_re, Complex.one_re, Complex.re_sum]
  unfold locCbeta
  rw [← hs₀def]
  by_cases hs : 2 * s₀ ^ 2 ≤ 1
  · refine (min_le_right _ _).trans ?_
    nlinarith
  · refine (min_le_left _ _).trans ?_
    nlinarith

private lemma loc_cbeta_pos {τ cb : ℝ} (hτ : 0 < τ) (hcb : 0 < cb) : 0 < locCbeta τ cb := by
  have := loc_mBound_pos hτ
  unfold locCbeta
  exact lt_min one_pos (by positivity)

private lemma loc_Calpha_pos {τ cb : ℝ} (hτ : 0 < τ) (hcb : 0 < cb) : 0 < locCalpha τ cb := by
  have := loc_mBound_pos hτ
  unfold locCalpha
  have := inv_pos.2 hτ
  positivity

/-- `|α| ≤ C_α` when `|m| ≤ C_m`, (mz_reg) holds with `c_b` and `|u - m| ≤ c_b / 2`. -/
private lemma loc_alpha_le {τ cb Cm : ℝ} {N : ℕ} {σ : Fin M → ℝ}
    (h : DensityAssumptions τ N σ) (hN : 0 < N) (hcb : 0 < cb) (hCm : 0 < Cm) {u m : ℂ}
    (hm : ‖m‖ ≤ Cm) (hmz : ∀ s ∈ posVals σ, cb ≤ ‖m + ((s⁻¹ : ℝ) : ℂ)‖)
    (hx : ‖u - m‖ ≤ cb / 2) :
    ‖alphaCoef N σ u m‖ ≤ τ⁻¹ * Cm * (1 + Cm / cb) * 2 / cb ^ 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set L := 1 + Cm / cb with hL
  have hL1 : 1 ≤ L := by
    have : 0 ≤ Cm / cb := by positivity
    linarith
  set K := Cm * L * 2 / cb ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hterm : ∀ i, ‖m * (σ i : ℂ) ^ 2 / (N * (1 + σ i * m) ^ 2 * (1 + σ i * u))‖ ≤ K / N := by
    intro i
    rcases (h.nonneg i).eq_or_lt with h0 | hpos
    · rw [← h0]
      simp only [Complex.ofReal_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, mul_zero, zero_div, norm_zero]
      positivity
    · set a := σ i with ha
      have hmem : a ∈ posVals σ := by
        simp only [posVals, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨⟨i, rfl⟩, hpos⟩
      have hr := hmz a hmem
      have hs : (a : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
      have em : 1 + (a : ℂ) * m = (a : ℂ) * (m + ((a⁻¹ : ℝ) : ℂ)) := by
        push_cast
        field_simp
        ring
      have eu : 1 + (a : ℂ) * u = (a : ℂ) * (u + ((a⁻¹ : ℝ) : ℂ)) := by
        push_cast
        field_simp
        ring
      have hnm : ‖1 + (a : ℂ) * m‖ = a * ‖m + ((a⁻¹ : ℝ) : ℂ)‖ := by
        rw [em, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpos.le]
      have hnu : ‖1 + (a : ℂ) * u‖ = a * ‖u + ((a⁻¹ : ℝ) : ℂ)‖ := by
        rw [eu, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpos.le]
      have hu2 : cb / 2 ≤ ‖u + ((a⁻¹ : ℝ) : ℂ)‖ := by
        have := norm_sub_norm_le (m + ((a⁻¹ : ℝ) : ℂ)) (m - u)
        rw [show m + ((a⁻¹ : ℝ) : ℂ) - (m - u) = u + ((a⁻¹ : ℝ) : ℂ) by ring,
          norm_sub_rev] at this
        linarith
      have A : a * cb ≤ ‖1 + (a : ℂ) * m‖ := by
        rw [hnm]; exact mul_le_mul_of_nonneg_left hr hpos.le
      have B : a * cb / 2 ≤ ‖1 + (a : ℂ) * u‖ := by
        rw [hnu, mul_div_assoc]; exact mul_le_mul_of_nonneg_left hu2 hpos.le
      have C : 1 ≤ ‖1 + (a : ℂ) * m‖ * L := by
        have h1 : ‖(1 : ℂ)‖ ≤ ‖1 + (a : ℂ) * m‖ + ‖(a : ℂ) * m‖ := by
          have := norm_sub_le (1 + (a : ℂ) * m) ((a : ℂ) * m)
          simpa using this
        rw [norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpos.le] at h1
        have h2 : a * ‖m‖ ≤ ‖1 + (a : ℂ) * m‖ * (Cm / cb) := by
          rw [mul_div_assoc', le_div_iff₀ hcb]
          have := mul_le_mul_of_nonneg_left hm hpos.le
          nlinarith [norm_nonneg (1 + (a : ℂ) * m), norm_nonneg m]
        rw [hL]
        nlinarith
      set Q := ‖1 + (a : ℂ) * m‖ ^ 2 * ‖1 + (a : ℂ) * u‖ with hQ
      have hP : a ^ 2 * cb ^ 2 ≤ 2 * L * Q := by
        have h1 : a * cb * (a * cb / 2) ≤ ‖1 + (a : ℂ) * m‖ * ‖1 + (a : ℂ) * u‖ :=
          mul_le_mul A B (by positivity) (norm_nonneg _)
        have h2 : ‖1 + (a : ℂ) * m‖ * ‖1 + (a : ℂ) * u‖ ≤
            ‖1 + (a : ℂ) * m‖ * ‖1 + (a : ℂ) * u‖ * (‖1 + (a : ℂ) * m‖ * L) :=
          le_mul_of_one_le_right (by positivity) C
        rw [hQ]
        nlinarith
      have hQpos : 0 < Q := by
        have : 0 < a ^ 2 * cb ^ 2 := by positivity
        nlinarith
      have ha2 : a ^ 2 ≤ 2 * L * Q / cb ^ 2 := by
        rw [le_div_iff₀ (by positivity)]; exact hP
      simp only [norm_div, norm_mul, norm_pow, Complex.norm_real, Complex.norm_natCast,
        Real.norm_of_nonneg hpos.le]
      have hden : (N : ℝ) * ‖1 + (a : ℂ) * m‖ ^ 2 * ‖1 + (a : ℂ) * u‖ = N * Q := by
        rw [hQ, mul_assoc]
      rw [hden]
      calc ‖m‖ * a ^ 2 / (N * Q)
          ≤ Cm * (2 * L * Q / cb ^ 2) / (N * Q) := by gcongr
        _ = K / N := by
          rw [hK]
          field_simp
  unfold alphaCoef
  rw [norm_neg]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => hterm i).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hφ : (M : ℝ) / N ≤ τ⁻¹ := h.phi_upper
  have : (M : ℝ) * (K / N) = (M / N) * K := by ring
  rw [this]
  calc (M : ℝ) / N * K ≤ τ⁻¹ * K := mul_le_mul_of_nonneg_right hφ hK0
    _ = τ⁻¹ * Cm * (1 + Cm / cb) * 2 / cb ^ 2 := by rw [hK, hL]; ring

/-- `z + i N⁻⁵ ∈ S` for `z ∈ S` with `Im z < 1`, when `N⁻⁵ ≤ τ⁻¹ - 1` for `τ < 1`. -/
private lemma loc_shift_mem {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {S : Set ℂ}
    (h : DensityAssumptions τ N σ) (hS : SpectralDomain τ N S)
    (hshift : 0 < τ → τ < 1 → ((N : ℝ) ^ 5)⁻¹ ≤ τ⁻¹ - 1)
    {z : ℂ} (hz : z ∈ S) (hη1 : z.im < 1) : shiftUp N z ∈ S := by
  refine shiftUp_mem hS hz ?_
  rcases (loc_tau_le_one h).lt_or_eq with hτ | hτ
  · have := hshift h.pos hτ
    linarith
  · exfalso
    have h1 := (hS.1 hz).2.2.2.1
    rw [hτ, show (-1 + 1 : ℝ) = 0 by norm_num, Real.rpow_zero] at h1
    linarith

/-- With `K₀ = 0` the regime is thick: `0 < κ + η`. -/
private lemma loc_twoRegime_thick {C₀ C₁ κ η d D : ℝ} (hth : 0 < κ + η) :
    twoRegime C₀ C₁ 0 κ η d D = C₀ * (d / (D + √d)) := by
  unfold twoRegime
  simp only [zero_mul, hth, ↓reduceIte]

private lemma loc_quot_le_sqrt {d D : ℝ} (hd : 0 < d) (hD : 0 ≤ D) : d / (D + √d) ≤ √d := by
  have hs : 0 < √d := Real.sqrt_pos.2 hd
  calc d / (D + √d) ≤ d / √d := div_le_div_of_nonneg_left hd.le hs (by linarith)
    _ = √d := Real.div_sqrt

/-- `max(2, X) d ≤ C₀ d / (D + √d)` when `D + √d ≤ D_max + 1` and
`C₀ ≥ max(4(D_max + 1), X(D_max + 1))`. -/
private lemma loc_final {C₀ X Dm D d : ℝ} (hd : 0 < d) (hD : 0 ≤ D) (hDm : D + √d ≤ Dm + 1)
    (hDm0 : 0 ≤ Dm) (hC : max (4 * (Dm + 1)) (X * (Dm + 1)) ≤ C₀) :
    max 2 X * d ≤ C₀ * (d / (D + √d)) := by
  have hpos : 0 < D + √d := by have := Real.sqrt_pos.2 hd; linarith
  have h1 : 0 < Dm + 1 := by linarith
  have hC0 : 0 ≤ C₀ := le_trans (by positivity) (le_trans (le_max_left _ _) hC)
  have h2 : max 2 X * (Dm + 1) ≤ C₀ := by
    refine le_trans ?_ hC
    rcases le_total 2 X with hX | hX
    · rw [max_eq_right hX]; exact le_max_right _ _
    · rw [max_eq_left hX]
      exact le_trans (by nlinarith) (le_max_left _ _)
  calc max 2 X * d = max 2 X * (Dm + 1) * (d / (Dm + 1)) := by field_simp
    _ ≤ C₀ * (d / (Dm + 1)) := mul_le_mul_of_nonneg_right h2 (by positivity)
    _ ≤ C₀ * (d / (D + √d)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hd.le hpos hDm) hC0

/-- The stability step on a spectral domain `S` where `Im m ≥ c_b`: with the a priori bound
`C₀ √δ` at `z + i N⁻⁵`, `|u - m| ≤ max(2, 2 C_ε / c_β) δ`. -/
private lemma loc_step {τ cb C₀ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {S : Set ℂ}
    (h : DensityAssumptions τ N σ) (hS : SpectralDomain τ N S) (hcb : 0 < cb)
    (him : ∀ z ∈ S, cb ≤ (mFun N σ z).im)
    (hlog : (Real.log N)⁻¹ ≤ 1 / 2)
    (hshift : 0 < τ → τ < 1 → ((N : ℝ) ^ 5)⁻¹ ≤ τ⁻¹ - 1)
    (hsmall : 0 < τ → C₀ * √((Real.log N)⁻¹) + 2 * ((N : ℝ) ^ 3)⁻¹ ≤
      min (cb / 2) (locCbeta τ cb / (2 * locCalpha τ cb)))
    (hC₀ : 0 ≤ C₀) {δ : ℂ → ℝ} (hδ : AdmissibleDelta N S δ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {z : ℂ} (hz : z ∈ S)
    (hw : ‖fC N σ (resolventTransform μ z) - z‖ ≤ δ z)
    (hprev : z.im < 1 → ‖resolventTransform μ (shiftUp N z) - mFun N σ (shiftUp N z)‖ ≤
      C₀ * √(δ (shiftUp N z))) :
    ‖resolventTransform μ z - mFun N σ z‖ ≤
      max 2 (2 * locCeps τ cb / locCbeta τ cb) * δ z := by
  obtain ⟨hN, hSne⟩ := loc_facts h
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hzs := hS.1 hz
  have hη := hzs.1
  have hu : 0 < (resolventTransform μ z).im := im_resolventTransform_pos μ hη
  have hδpos : 0 < δ z := lt_of_lt_of_le (by positivity) (hδ.lower z hz)
  have hδ1 : δ z ≤ 1 / 2 := (hδ.upper z hz).trans hlog
  by_cases hη1 : 1 ≤ z.im
  · have := norm_sub_mFun_le_of_im_ge h.nonneg hN one_pos hη1 hu (by linarith)
    rw [one_pow, div_one] at this
    calc _ ≤ 2 * ‖fC N σ (resolventTransform μ z) - z‖ := this
      _ ≤ 2 * δ z := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hδpos.le
  push Not at hη1
  -- the a priori bound at `z` from the bound at `z' = z + i N⁻⁵`
  set z' := shiftUp N z with hz'def
  have hz' : z' ∈ S := loc_shift_mem h hS hshift hz hη1
  have hη' : 0 < z'.im := (hS.1 hz').1
  have hz'im : z'.im = z.im + ((N : ℝ) ^ 5)⁻¹ := by
    rw [hz'def, shiftUp, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have hdist : ‖z - z'‖ = ((N : ℝ) ^ 5)⁻¹ := by
    rw [hz'def, shiftUp, sub_add_cancel_left, norm_neg, norm_mul, Complex.norm_real,
      Complex.norm_I, mul_one, Real.norm_of_nonneg (by positivity)]
  have hNη : ((N : ℝ))⁻¹ ≤ z.im := by
    have h1 := hzs.2.2.2.1
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have h2 : (N : ℝ) ^ (-1 : ℝ) ≤ (N : ℝ) ^ (-1 + τ) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [h.pos])
    rw [Real.rpow_neg_one] at h2
    linarith
  have hdrift : ‖z - z'‖ / (z.im * z'.im) ≤ ((N : ℝ) ^ 3)⁻¹ := by
    rw [hdist]
    have hNη' : (N : ℝ)⁻¹ ≤ z'.im := by
      rw [hz'im]
      have : (0 : ℝ) ≤ ((N : ℝ) ^ 5)⁻¹ := by positivity
      linarith
    have hprod : (N : ℝ)⁻¹ * (N : ℝ)⁻¹ ≤ z.im * z'.im :=
      mul_le_mul hNη hNη' (by positivity) hη.le
    calc ((N : ℝ) ^ 5)⁻¹ / (z.im * z'.im) ≤ ((N : ℝ) ^ 5)⁻¹ / ((N : ℝ)⁻¹ * (N : ℝ)⁻¹) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hprod
      _ = ((N : ℝ) ^ 3)⁻¹ := by field_simp
  have := isProbabilityMeasure_varrho N σ h.nonneg hN
  have h1 := norm_resolventTransform_sub_le μ hη hη'
  have h2 := norm_resolventTransform_sub_le (varrho N σ) hη' hη
  rw [resolventTransform_varrho N σ h.nonneg hN hη',
    resolventTransform_varrho N σ h.nonneg hN hη, norm_sub_rev z' z, mul_comm z'.im] at h2
  have hδ' : δ z' ≤ (Real.log N)⁻¹ := hδ.upper z' hz'
  have hsq : C₀ * √(δ z') ≤ C₀ * √((Real.log N)⁻¹) :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hδ') hC₀
  have hsm := hsmall h.pos
  -- the quadratic equation
  have hCm := loc_mBound_pos h.pos
  have hm := gen_prop_m_specDomain h hzs
  have hmz := loc_mz_reg (σ := σ) (him z hz)
  have hβ := loc_beta_ge h hcb hzs (him z hz)
  have hcβ : 0 < locCbeta τ cb := loc_cbeta_pos h.pos hcb
  have hCα : 0 < locCalpha τ cb := loc_Calpha_pos h.pos hcb
  obtain ⟨hmim, hfm⟩ := mFun_spec N σ h.nonneg hη
  set u := resolventTransform μ z with hudef
  set m := mFun N σ z with hmdef
  have hx : ‖u - m‖ ≤ min (cb / 2) (locCbeta τ cb / (2 * locCalpha τ cb)) := by
    have e : u - m = (u - resolventTransform μ z') + (resolventTransform μ z' - mFun N σ z') +
        (mFun N σ z' - m) := by ring
    rw [e]
    refine (norm_add₃_le).trans ?_
    have := hprev hη1
    linarith
  have hxcb : ‖u - m‖ ≤ cb / 2 := hx.trans (min_le_left _ _)
  have hxa : ‖u - m‖ ≤ locCbeta τ cb / (2 * locCalpha τ cb) := hx.trans (min_le_right _ _)
  have hu0 : u ≠ 0 := fun h0 => by rw [h0] at hu; simp at hu
  have hm0 : m ≠ 0 := fun h0 => by rw [h0] at hmim; simp at hmim
  have hq := quadr_edge N σ hu0 hm0 (fun i => loc_one_add_ne (h.nonneg i) hu)
    (fun i => loc_one_add_ne (h.nonneg i) hmim)
  rw [hfm] at hq
  have hα := loc_alpha_le h hN hcb hCm hm.2.1 hmz hxcb
  have hβn : locCbeta τ cb ≤ ‖betaCoef N σ m‖ := hβ.trans (Complex.re_le_norm _)
  have hβ0 : betaCoef N σ m ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hβn; linarith
  have hroot := root_dichotomy hα hβ0 hq.symm (by
    have : 2 * locCalpha τ cb * ‖u - m‖ ≤ locCbeta τ cb := by
      rw [le_div_iff₀ (by positivity)] at hxa
      linarith
    exact this.trans hβn)
  have hun : ‖u‖ ≤ mBoundConst τ + cb / 2 := by
    have := norm_le_norm_add_norm_sub' u m
    linarith [hm.2.1]
  have hε : ‖u * m * (fC N σ u - z)‖ ≤ locCeps τ cb * δ z := by
    rw [norm_mul, norm_mul]
    unfold locCeps
    have h0 : 0 ≤ ‖u‖ * ‖m‖ := by positivity
    calc ‖u‖ * ‖m‖ * ‖fC N σ u - z‖ ≤ ‖u‖ * ‖m‖ * δ z := mul_le_mul_of_nonneg_left hw h0
      _ ≤ (mBoundConst τ + cb / 2) * mBoundConst τ * δ z := by
          gcongr
          exact hm.2.1
  have hCε : 0 ≤ locCeps τ cb * δ z := by
    unfold locCeps
    positivity
  calc ‖u - m‖ ≤ 2 * ‖u * m * (fC N σ u - z)‖ / ‖betaCoef N σ m‖ := hroot
    _ ≤ 2 * (locCeps τ cb * δ z) / locCbeta τ cb :=
        div_le_div₀ (by linarith) (by linarith) hcβ hβn
    _ = 2 * locCeps τ cb / locCbeta τ cb * δ z := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hδpos.le

/-- The conditions on `N` used in the stability step hold for all large `N`. -/
private lemma loc_eventually (τ cb C₀ : ℝ) (hcb : 0 < cb) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, (Real.log N)⁻¹ ≤ 1 / 2 ∧
      (0 < τ → τ < 1 → ((N : ℝ) ^ 5)⁻¹ ≤ τ⁻¹ - 1) ∧
      (0 < τ → C₀ * √((Real.log N)⁻¹) + 2 * ((N : ℝ) ^ 3)⁻¹ ≤
        min (cb / 2) (locCbeta τ cb / (2 * locCalpha τ cb))) := by
  have hlog : Tendsto (fun N : ℕ => (Real.log N)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hpow : ∀ n : ℕ, 0 < n → Tendsto (fun N : ℕ => ((N : ℝ) ^ n)⁻¹) atTop (𝓝 0) :=
    fun n hn => tendsto_inv_atTop_zero.comp
      ((tendsto_pow_atTop hn.ne').comp tendsto_natCast_atTop_atTop)
  have e0 : ∀ᶠ N : ℕ in atTop, (Real.log N)⁻¹ ≤ 1 / 2 :=
    (hlog.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono fun _ h => h.le
  have e2 : ∀ᶠ N : ℕ in atTop, 0 < τ → τ < 1 → ((N : ℝ) ^ 5)⁻¹ ≤ τ⁻¹ - 1 := by
    by_cases hτ : 0 < τ ∧ τ < 1
    · have hpos : 0 < τ⁻¹ - 1 := by
        have := one_lt_inv₀ hτ.1 |>.2 hτ.2
        linarith
      exact ((hpow 5 (by norm_num)).eventually (gt_mem_nhds hpos)).mono
        fun _ h _ _ => h.le
    · exact Eventually.of_forall fun _ h1 h2 => absurd ⟨h1, h2⟩ hτ
  have e3 : ∀ᶠ N : ℕ in atTop, 0 < τ →
      C₀ * √((Real.log N)⁻¹) + 2 * ((N : ℝ) ^ 3)⁻¹ ≤
        min (cb / 2) (locCbeta τ cb / (2 * locCalpha τ cb)) := by
    by_cases hτ : 0 < τ
    · have hcβ : 0 < locCbeta τ cb := loc_cbeta_pos hτ hcb
      have hCα : 0 < locCalpha τ cb := loc_Calpha_pos hτ hcb
      have hmin : 0 < min (cb / 2) (locCbeta τ cb / (2 * locCalpha τ cb)) :=
        lt_min (by positivity) (by positivity)
      have hsq : Tendsto (fun N : ℕ => √((Real.log N)⁻¹)) atTop (𝓝 0) := by
        have := (Real.continuous_sqrt.tendsto 0).comp hlog
        rwa [Real.sqrt_zero] at this
      have ht := (hsq.const_mul C₀).add ((hpow 3 (by norm_num)).const_mul 2)
      rw [mul_zero, mul_zero, add_zero] at ht
      exact (ht.eventually (gt_mem_nhds hmin)).mono fun _ h _ => h.le
    · exact Eventually.of_forall fun _ h1 => absurd h1 hτ
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (e0.and (e2.and e3))
  exact ⟨N₀, fun N hN => hN₀ N hN⟩

/-- Lemma A.6 (weak stability, Definition 5.4) on a spectral domain `S` where `Im m ≥ c_b`. -/
theorem stab_loc_weak {τ cb C₀ C₁ : ℝ} (hcb : 0 < cb) (hC₀ : locC0wmin τ cb ≤ C₀) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {M : ℕ} (σ : Fin M → ℝ) (S : Set ℂ),
      DensityAssumptions τ N σ → SpectralDomain τ N S → (∀ z ∈ S, cb ≤ (mFun N σ z).im) →
        StableOn C₀ C₁ 0 N σ S := by
  obtain ⟨N₀, hN₀⟩ := loc_eventually τ cb C₀ hcb
  refine ⟨N₀, fun N hN M σ S h hS him => ?_⟩
  obtain ⟨hlog, hshift, hsmall⟩ := hN₀ N hN
  have hCm := loc_mBound_pos h.pos
  have hC₀0 : 0 ≤ C₀ := le_trans (by positivity) (le_trans (le_max_left _ _) hC₀)
  intro δ hδ μ hμ z hz hw hprev
  have hthick : ∀ ζ ∈ S, 0 < kappa N σ ζ.re + ζ.im := fun ζ hζ => by
    have := kappa_nonneg N σ ζ.re
    have := (hS.1 hζ).1
    linarith
  have hstep := loc_step h hS hcb him hlog hshift hsmall hC₀0 hδ μ hz hw (fun hη1 => by
    have hz' := loc_shift_mem h hS hshift hz hη1
    refine (hprev hη1).trans ?_
    unfold weakBound
    rw [loc_twoRegime_thick (hthick _ hz')]
    have him' := (mFun_spec N σ h.nonneg (hS.1 hz').1).1
    exact mul_le_mul_of_nonneg_left (loc_quot_le_sqrt (lt_of_lt_of_le (by
      have := (loc_facts h).1
      positivity) (hδ.lower _ hz')) him'.le) hC₀0)
  unfold weakBound
  rw [loc_twoRegime_thick (hthick z hz)]
  have hδpos : 0 < δ z := lt_of_lt_of_le (by have := (loc_facts h).1; positivity)
    (hδ.lower z hz)
  have hδ1 : δ z ≤ 1 := by linarith [(hδ.upper z hz).trans hlog]
  have hzs := hS.1 hz
  have him' := (mFun_spec N σ h.nonneg hzs.1).1
  have hm := gen_prop_m_specDomain h hzs
  refine hstep.trans (loc_final hδpos him'.le ?_ hCm.le hC₀)
  have h1 : (mFun N σ z).im ≤ mBoundConst τ :=
    (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans hm.2.1)
  have h2 : √(δ z) ≤ 1 := Real.sqrt_le_one.mpr hδ1
  linarith

/-- Stability on the bulk domain (Definition 5.4) with `K₀ = 0` and `C₀ = bulkC0wmin`, obtained
from the weak stability with `Im m ≥ c_b` and the lower bound `c_b = bulkcb τ τ' c` of
`im_mFun_bulk_ge`. -/
example (τ τ' C₁ : ℝ) (c : ℝ → ℝ) (hτ : 0 < τ) (hτ' : 0 < τ') (hc : 0 < c (τ' / 2)) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {M : ℕ} (σ : Fin M → ℝ) (k : ℕ),
      DensityAssumptions τ N σ → RegularBulk c N σ k →
        StableOn (bulkC0wmin τ τ' c) C₁ 0 N σ (bulkDomain τ τ' N σ k) := by
  have hcb : 0 < bulkcb τ τ' c := by
    have ha : 0 < Real.arctan (τ * τ' / 2) := Real.arctan_pos.2 (by positivity)
    unfold bulkcb
    positivity
  obtain ⟨N₀, hN₀⟩ := stab_loc_weak (τ := τ) (C₁ := C₁) hcb (le_refl (bulkC0wmin τ τ' c))
  exact ⟨N₀, fun N hN M σ k h hb =>
    hN₀ N hN σ _ h (spectralDomain_bulkDomain τ τ' N σ k)
      (fun z hz => im_mFun_bulk_ge h hb hτ' hz)⟩

/-- The same at the Marchenko–Pastur parameters `τ = 1/20`, `τ' = 1/2`, `c(t) = min(t, 1)/50`
(for which `c_b > 0`), `C₀ = bulkC0wmin`, `C₁ = 2 C₀`. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {M : ℕ} (σ : Fin M → ℝ) (k : ℕ),
    DensityAssumptions (1 / 20) N σ → RegularBulk (fun t : ℝ => min t 1 / 50) N σ k →
      StableOn (bulkC0wmin (1 / 20) (1 / 2) (fun t : ℝ => min t 1 / 50))
        (2 * bulkC0wmin (1 / 20) (1 / 2) (fun t : ℝ => min t 1 / 50)) 0 N σ
        (bulkDomain (1 / 20) (1 / 2) N σ k) := by
  have hcb : 0 < bulkcb (1 / 20) (1 / 2) (fun t : ℝ => min t 1 / 50) := by
    have ha : 0 < Real.arctan (1 / 20 * (1 / 2) / 2 : ℝ) := Real.arctan_pos.2 (by norm_num)
    unfold bulkcb
    have : (0 : ℝ) < min ((1 / 2 : ℝ) / 2) 1 / 50 := by norm_num
    positivity
  obtain ⟨N₀, hN₀⟩ := stab_loc_weak (τ := 1 / 20)
    (C₁ := 2 * bulkC0wmin (1 / 20) (1 / 2) (fun t : ℝ => min t 1 / 50)) hcb
    (le_refl (bulkC0wmin (1 / 20) (1 / 2) (fun t : ℝ => min t 1 / 50)))
  exact ⟨N₀, fun N hN M σ k h hb =>
    hN₀ N hN σ _ h (spectralDomain_bulkDomain _ _ N σ k)
      (fun z hz => im_mFun_bulk_ge h hb (by norm_num) hz)⟩

end Anisotropic
