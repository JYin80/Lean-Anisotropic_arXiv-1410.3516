module

public import Anisotropic.Density.Stability.Defs
public import Anisotropic.Density.Stability.Quadratic
public import Anisotropic.Density.Count

@[expose] public section

/-!
# Stability in a regular bulk component (Lemma A.6)

On `𝐃^b_k(τ,τ',N)`, for a bulk component `k` that is regular in the sense of
Definition 2.7 (ii): the lower bound `Im m ≥ c_b`, (m_sq_root) in the band case, (mz_reg), the
lower bound on `Re β` from (im_def_m), and strong stability (Definition A.2) and stability
(Definition 5.4) for every `C₁`, `K₀` and all large `N`.

Proofs (Section A.3, Lemma A.6).
* `Im m = ∫ η / ((x - E)² + η²) dϱ(x)`, and `ϱ ≥ c(τ'/2)` times Lebesgue measure on the window
  `[E - τ'/2, E + τ'/2] ⊂ [a_{2k} + τ'/2, a_{2k-1} - τ'/2] ⊂ (0, ∞)`; the window integral is
  `2 arctan(τ'/(2η)) ≥ 2 arctan(τ τ'/2)` for `η ≤ τ⁻¹`.
* `κ ≥ τ'`, since the edges are ordered (Lemma 2.5) and `E` lies `τ'` inside the band.
* With `q_i = σ_i m / (1 + σ_i m)`: `Re q_i² ≤ (1 - 2 sin² θ₀) |q_i|²`, and
  `N⁻¹ Σ_i |q_i|² = 1 - |m|² η / Im m ∈ [0, 1]` by (im_def_m).
* Stability: for large `N`, `K₀ δ < τ' ≤ κ`, so only the regime with constant `C₀` occurs. For
  `Im z ≥ 1`, `|u - m| ≤ 2δ`. For `Im z < 1`, the bound at `z + i N⁻⁵` gives
  `|u - m| ≤ min(c_b/2, c_β/(2 C_α))`, and the small root of (quadr_edge) gives
  `|u - m| ≤ 2 C_ε δ / c_β`.
-/

open MeasureTheory Polynomial Filter Topology
open scoped ENNReal

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

private lemma bulk_empMeasure_apply (σ : Fin M → ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    empMeasure σ s = (M : ℝ≥0∞)⁻¹ * ((Finset.univ.filter fun i => σ i ∈ s).card : ℝ≥0∞) := by
  simp only [empMeasure, Measure.smul_apply, Measure.finsetSum_apply,
    Measure.dirac_apply' _ hs, smul_eq_mul]
  congr 1
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Set.indicator]

/-- Under the assumptions, `N > 0` and some `σ i` is positive. -/
private lemma bulk_facts {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) :
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
  rw [bulk_empMeasure_apply σ measurableSet_Icc] at hgap
  simp only [hall, Set.mem_Icc, le_refl, h.pos.le, and_self, Finset.filter_true,
    Finset.card_univ, Fintype.card_fin] at hgap
  have hM' : (M : ℝ≥0∞)⁻¹ * (M : ℝ≥0∞) = 1 :=
    ENNReal.inv_mul_cancel (by exact_mod_cast hM) (ENNReal.natCast_ne_top _)
  rw [hM', ENNReal.toReal_one] at hgap
  linarith [h.pos]

/-- `τ ≤ 1` under the assumptions. -/
private lemma bulk_tau_le_one {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) :
    τ ≤ 1 := by
  have h1 : τ ≤ τ⁻¹ := h.phi_lower.trans h.phi_upper
  by_contra hc
  exact absurd h1 (not_le.mpr ((inv_lt_one_of_one_lt₀ (not_le.mp hc)).trans (not_le.mp hc)))

private lemma bulk_ofReal_sub_ne {z : ℂ} (hz : 0 < z.im) (x : ℝ) : (x : ℂ) - z ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

private lemma bulk_integrable_kernel (μ : Measure ℝ) [IsProbabilityMeasure μ] {z : ℂ}
    (hz : 0 < z.im) : Integrable (fun x : ℝ => ((x : ℂ) - z)⁻¹) μ := by
  refine Integrable.of_bound ?_ (z.im)⁻¹ (ae_of_all _ fun x => ?_)
  · exact ((Complex.continuous_ofReal.sub continuous_const).inv₀
      fun x => bulk_ofReal_sub_ne hz x).aestronglyMeasurable
  · rw [norm_inv]
    refine inv_anti₀ hz ?_
    have h := Complex.abs_im_le_norm ((x : ℂ) - z)
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] at h
    exact le_trans (le_abs_self _) h

private lemma bulk_kernel_im (z : ℂ) (x : ℝ) :
    (((x : ℂ) - z)⁻¹).im = z.im / ((x - z.re) ^ 2 + z.im ^ 2) := by
  rw [Complex.inv_im, Complex.normSq_apply]
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, neg_neg, Complex.sub_re,
    Complex.ofReal_re]
  ring_nf

/-- `Im u(z) = ∫ η / ((x - E)² + η²) dμ(x)` for a Stieltjes transform `u`. -/
private lemma bulk_im_eq_integral (μ : Measure ℝ) [IsProbabilityMeasure μ] {z : ℂ}
    (hz : 0 < z.im) :
    (resolventTransform μ z : ℂ).im = ∫ x : ℝ, z.im / ((x - z.re) ^ 2 + z.im ^ 2) ∂μ := by
  have hint := bulk_integrable_kernel μ hz
  rw [resolventTransform_apply]
  have hres : ∀ x : ℝ, resolvent z x = ((x : ℂ) - z)⁻¹ := by
    intro x
    simp [resolvent, Ring.inverse_eq_inv']
  simp_rw [hres]
  have := integral_im (𝕜 := ℂ) hint
  simp only [RCLike.im_to_complex] at this
  rw [← this]
  simp_rw [bulk_kernel_im]

/-- On `[a, b] ⊂ (0, ∞)` with `ρ ≥ c₀`, the measure `ϱ` dominates `c₀` times Lebesgue. -/
private lemma bulk_measure_ge (N : ℕ) (σ : Fin M → ℝ) {a b c₀ : ℝ} (ha : 0 < a)
    (hρ : ∀ x ∈ Set.Icc a b, c₀ ≤ rhoDens N σ x) :
    ENNReal.ofReal c₀ • volume.restrict (Set.Icc a b) ≤ varrho N σ := by
  rw [Measure.le_iff]
  intro s hs
  rw [Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul, ← setLIntegral_const]
  calc ∫⁻ _ in s ∩ Set.Icc a b, ENNReal.ofReal c₀
      ≤ ∫⁻ x in s ∩ Set.Icc a b, ENNReal.ofReal (rhoDens N σ x) :=
        setLIntegral_mono' (hs.inter measurableSet_Icc)
          fun x hx => ENNReal.ofReal_le_ofReal (hρ x hx.2)
    _ ≤ ∫⁻ x in s ∩ Set.Ioi 0, ENNReal.ofReal (rhoDens N σ x) :=
        lintegral_mono_set fun x hx => ⟨hx.1, lt_of_lt_of_le ha hx.2.1⟩
    _ = ((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
          (fun x => ENNReal.ofReal (rhoDens N σ x))) s := by
        rw [withDensity_apply _ hs, Measure.restrict_restrict hs]
    _ ≤ varrho N σ s := by
        rw [varrho, Measure.add_apply]
        exact le_add_self

/-- `∫_{E-r}^{E+r} η / ((x - E)² + η²) dx = 2 arctan(r / η)`. -/
private lemma bulk_window_integral {E η r : ℝ} (hη : 0 < η) :
    ∫ x in (E - r)..(E + r), η / ((x - E) ^ 2 + η ^ 2) = 2 * Real.arctan (r / η) := by
  have hd : ∀ x ∈ Set.uIcc (E - r) (E + r),
      HasDerivAt (fun x => Real.arctan ((x - E) / η)) (η / ((x - E) ^ 2 + η ^ 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun x => (x - E) / η) (1 / η) x :=
      ((hasDerivAt_id x).sub_const E).div_const η
    have h2 := (Real.hasDerivAt_arctan ((x - E) / η)).comp x h1
    refine h2.congr_deriv ?_
    have : (x - E) ^ 2 + η ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  have hc : Continuous fun x : ℝ => η / ((x - E) ^ 2 + η ^ 2) :=
    continuous_const.div (by fun_prop) fun x => by positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)]
  simp only [add_sub_cancel_left, sub_sub_cancel_left, neg_div, Real.arctan_neg]
  ring

/-- `Im m ≥ c_b = 2 c(τ'/2) arctan(τ τ'/2)` on `𝐃^b_k`. -/
def bulkcb (τ τ' : ℝ) (c : ℝ → ℝ) : ℝ := 2 * c (τ' / 2) * Real.arctan (τ * τ' / 2)
/-- `|β| ≥ min(1, 2 sin² θ₀)`, `sin θ₀ = (c_b/C_m)(τ/(C_m+τ))`. -/
def bulkcbeta (τ τ' : ℝ) (c : ℝ → ℝ) : ℝ :=
  min 1 (2 * (bulkcb τ τ' c / mBoundConst τ * (τ / (mBoundConst τ + τ))) ^ 2)
/-- `|α| ≤ C_α` for `|u - m| ≤ c_b / 2`. -/
def bulkCalpha (τ τ' : ℝ) (c : ℝ → ℝ) : ℝ :=
  τ⁻¹ * mBoundConst τ * (1 + mBoundConst τ / bulkcb τ τ' c) * 2 / bulkcb τ τ' c ^ 2
/-- `|u m| ≤ C_ε` for `|u - m| ≤ c_b / 2`. -/
def bulkCeps (τ τ' : ℝ) (c : ℝ → ℝ) : ℝ := (mBoundConst τ + bulkcb τ τ' c / 2) * mBoundConst τ
/-- Minimal `C₀`, strong form. -/
def bulkC0min (τ τ' : ℝ) (c : ℝ → ℝ) : ℝ :=
  max (4 * (√(kappaMax τ + τ⁻¹) + 1))
    (2 * bulkCeps τ τ' c / bulkcbeta τ τ' c * (√(kappaMax τ + τ⁻¹) + 1))
/-- Minimal `C₀`, weak form. -/
def bulkC0wmin (τ τ' : ℝ) (c : ℝ → ℝ) : ℝ :=
  max (4 * (mBoundConst τ + 1)) (2 * bulkCeps τ τ' c / bulkcbeta τ τ' c * (mBoundConst τ + 1))

private lemma bulk_mBound_pos {τ : ℝ} (hτ : 0 < τ) : 0 < mBoundConst τ := by
  unfold mBoundConst genPropConst
  exact div_pos (pow_pos (by linarith) 2) (pow_pos (half_pos hτ) 4)

private lemma bulk_cb_pos {τ τ' : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ} {c : ℝ → ℝ}
    (h : DensityAssumptions τ N σ) (hb : RegularBulk c N σ k) (hτ' : 0 < τ') :
    0 < bulkcb τ τ' c := by
  have hc := (hb.2.2 (τ' / 2) (half_pos hτ')).1
  have ha : 0 < Real.arctan (τ * τ' / 2) := Real.arctan_pos.2 (by have := h.pos; positivity)
  unfold bulkcb
  positivity

/-- `a_j ≤ a_i` for `1 ≤ i ≤ j ≤ 2p` (Lemma 2.5). -/
private lemma bulk_edge_anti (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j)
    (hj : j ≤ 2 * numBands N σ) : edgeVal N σ j ≤ edgeVal N σ i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ n hin ih =>
    exact (edgeVal_succ_le N σ hσ hN hS (by omega) (by omega)).trans (ih (by omega))

theorem im_mFun_bulk_ge {τ τ' : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ} {c : ℝ → ℝ}
    (h : DensityAssumptions τ N σ) (hb : RegularBulk c N σ k) (hτ' : 0 < τ') {z : ℂ}
    (hz : z ∈ bulkDomain τ τ' N σ k) : bulkcb τ τ' c ≤ (mFun N σ z).im := by
  obtain ⟨hN, hS⟩ := bulk_facts h
  obtain ⟨hk1, hkp, hreg⟩ := hb
  obtain ⟨hc, hρ⟩ := hreg (τ' / 2) (half_pos hτ')
  obtain ⟨hzD, hE1, hE2⟩ := hz
  obtain ⟨hη, -, -, -, hητ⟩ := hzD
  have ha := edgeVal_mem_Icc N σ h.nonneg hN hS h.pos h.phi_lower h.phi_upper h.bound_Sigma
    (k := 2 * k) (by omega) (by omega)
  have hwin : ∀ x ∈ Set.Icc (z.re - τ' / 2) (z.re + τ' / 2), c (τ' / 2) ≤ rhoDens N σ x :=
    fun x hx => hρ x ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hpos : 0 < z.re - τ' / 2 := by linarith [ha.1]
  have hle := bulk_measure_ge N σ hpos hwin
  have := isProbabilityMeasure_varrho N σ h.nonneg hN
  have hint : Integrable (fun x : ℝ => z.im / ((x - z.re) ^ 2 + z.im ^ 2)) (varrho N σ) := by
    refine (bulk_integrable_kernel (varrho N σ) hη).im.congr (ae_of_all _ fun x => ?_)
    exact bulk_kernel_im z x
  have hmono := integral_mono_measure hle (ae_of_all _ fun x => by positivity) hint
  rw [integral_smul_measure, ENNReal.toReal_ofReal hc.le, smul_eq_mul,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    bulk_window_integral hη] at hmono
  rw [← resolventTransform_varrho N σ h.nonneg hN hη, bulk_im_eq_integral _ hη]
  refine le_trans ?_ hmono
  have hτη : z.im * τ ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hητ h.pos.le
    rw [mul_inv_cancel₀ h.pos.ne'] at this
    linarith
  have harg : τ * τ' / 2 ≤ τ' / 2 / z.im := by
    rw [le_div_iff₀ hη]
    nlinarith
  have := Real.arctan_strictMono.monotone harg
  unfold bulkcb
  nlinarith

/-- Lemma A.6, (m_sq_root) (band case) on `𝐃^b_k`. -/
theorem m_sq_root_bulk {τ τ' : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ} {c : ℝ → ℝ}
    (h : DensityAssumptions τ N σ) (hb : RegularBulk c N σ k) (hτ' : 0 < τ') {z : ℂ}
    (hz : z ∈ bulkDomain τ τ' N σ k) :
    z.re ∈ (varrho N σ).support ∧ τ' ≤ kappa N σ z.re ∧
    bulkcb τ τ' c / √(kappaMax τ + τ⁻¹) * √(kappa N σ z.re + z.im) ≤ (mFun N σ z).im ∧
    (mFun N σ z).im ≤ mBoundConst τ / √τ' * √(kappa N σ z.re + z.im) := by
  obtain ⟨hN, hS⟩ := bulk_facts h
  have hcb := bulk_cb_pos h hb hτ'
  have him := im_mFun_bulk_ge h hb hτ' hz
  obtain ⟨hk1, hkp, -⟩ := hb
  obtain ⟨hzD, hE1, hE2⟩ := hz
  have hm := gen_prop_m_specDomain h hzD
  obtain ⟨hη, -, hre, -, hητ⟩ := hzD
  have ha := edgeVal_mem_Icc N σ h.nonneg hN hS h.pos h.phi_lower h.phi_upper h.bound_Sigma
    (k := 2 * k) (by omega) (by omega)
  have hsupp : z.re ∈ (varrho N σ).support :=
    (mem_support_varrho_iff N σ h.nonneg hN hS (by linarith [ha.1])).2
      ⟨k, hk1, hkp, by linarith, by linarith⟩
  have hκ : τ' ≤ kappa N σ z.re := by
    unfold kappa
    have hp := (card_innerCrit N σ h.nonneg hN hS).2
    have : Nonempty (Finset.Icc 1 (2 * numBands N σ)) :=
      ⟨⟨1, Finset.mem_Icc.2 ⟨le_rfl, by omega⟩⟩⟩
    refine le_ciInf fun l => ?_
    obtain ⟨l, hl⟩ := l
    rw [Finset.mem_Icc] at hl
    by_cases hlk : l ≤ 2 * k - 1
    · have := bulk_edge_anti N σ h.nonneg hN hS hl.1 hlk (by omega)
      rw [abs_sub_comm, abs_of_nonneg (by simp only; linarith)]
      simp only
      linarith
    · have := bulk_edge_anti N σ h.nonneg hN hS (i := 2 * k) (j := l) (by omega) (by omega) hl.2
      rw [abs_of_nonneg (by simp only; linarith)]
      simp only
      linarith
  have hκle := kappa_le h hre
  have hA : 0 < kappaMax τ + τ⁻¹ := by
    have := kappa_nonneg N σ z.re
    linarith [inv_pos.2 h.pos]
  have hCm := bulk_mBound_pos h.pos
  refine ⟨hsupp, hκ, ?_, ?_⟩
  · refine le_trans ?_ him
    rw [div_mul_eq_mul_div, div_le_iff₀ (Real.sqrt_pos.2 hA)]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) hcb.le
  · have h1 : (mFun N σ z).im ≤ mBoundConst τ :=
      (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans hm.2.1)
    refine h1.trans ?_
    rw [div_mul_eq_mul_div, le_div_iff₀ (Real.sqrt_pos.2 hτ')]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) hCm.le

/-- Lemma A.6, (mz_reg) on `𝐃^b_k`. -/
theorem mz_reg_bulk {τ τ' : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ} {c : ℝ → ℝ}
    (h : DensityAssumptions τ N σ) (hb : RegularBulk c N σ k) (hτ' : 0 < τ') {z : ℂ}
    (hz : z ∈ bulkDomain τ τ' N σ k) :
    ∀ s ∈ posVals σ, bulkcb τ τ' c ≤ ‖mFun N σ z + ((s⁻¹ : ℝ) : ℂ)‖ := by
  intro s _
  have him := im_mFun_bulk_ge h hb hτ' hz
  refine him.trans ?_
  have := Complex.abs_im_le_norm (mFun N σ z + ((s⁻¹ : ℝ) : ℂ))
  simp only [Complex.add_im, Complex.ofReal_im, add_zero] at this
  exact (le_abs_self _).trans this

private lemma bulk_one_add_ne {a : ℝ} (ha : 0 ≤ a) {w : ℂ} (hw : 0 < w.im) :
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
private lemma bulk_re_term {m : ℂ} {a n s₀ : ℝ} (hn : 0 < n) (hm : 0 < m.im) (ha : 0 ≤ a)
    (hs : s₀ * ‖m‖ * ‖1 + (a : ℂ) * m‖ ≤ m.im) (hs₀ : 0 ≤ s₀) :
    (m ^ 2 * (a : ℂ) ^ 2 / ((n : ℂ) * (1 + a * m) ^ 2)).re ≤
      (1 - 2 * s₀ ^ 2) * (a ^ 2 * ‖m‖ ^ 2 / (n * ‖1 + (a : ℂ) * m‖ ^ 2)) := by
  set w : ℂ := 1 + (a : ℂ) * m with hwdef
  have hw : w ≠ 0 := bulk_one_add_ne ha hm
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

/-- `Re β ≥ min(1, 2 sin² θ₀)` on `𝐃^b_k` (from (im_def_m)). -/
theorem betaCoef_bulk_ge {τ τ' : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ} {c : ℝ → ℝ}
    (h : DensityAssumptions τ N σ) (hb : RegularBulk c N σ k) (hτ' : 0 < τ') {z : ℂ}
    (hz : z ∈ bulkDomain τ τ' N σ k) :
    bulkcbeta τ τ' c ≤ (betaCoef N σ (mFun N σ z)).re := by
  obtain ⟨hN, -⟩ := bulk_facts h
  have hcb := bulk_cb_pos h hb hτ'
  have him := im_mFun_bulk_ge h hb hτ' hz
  have hm := gen_prop_m_specDomain h hz.1
  have hη := hz.1.1
  have hCm := bulk_mBound_pos h.pos
  have hτ := h.pos
  have hdef := im_def_m (N := N) h.nonneg hη
  set m := mFun N σ z with hmdef
  set Cm := mBoundConst τ with hCmdef
  set s₀ := bulkcb τ τ' c / Cm * (τ / (Cm + τ)) with hs₀def
  have hs₀ : 0 ≤ s₀ := by positivity
  have hmpos : 0 < m.im := lt_of_lt_of_le hcb him
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hterm : ∀ i, (m ^ 2 * (σ i : ℂ) ^ 2 / ((N : ℂ) * (1 + σ i * m) ^ 2)).re ≤
      (1 - 2 * s₀ ^ 2) * (σ i ^ 2 * ‖m‖ ^ 2 / (N * ‖1 + (σ i : ℂ) * m‖ ^ 2)) := by
    intro i
    have hσi := h.nonneg i
    refine bulk_re_term (n := (N : ℝ)) hNpos hmpos hσi ?_ hs₀
    have hw : ‖1 + (σ i : ℂ) * m‖ ≤ 1 + τ⁻¹ * Cm := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg hσi]
      have := mul_le_mul (h.bound_Sigma i) hm.2.1 (norm_nonneg _) (inv_pos.2 hτ).le
      linarith
    have heq : s₀ * Cm * (1 + τ⁻¹ * Cm) = bulkcb τ τ' c := by
      rw [hs₀def]
      field_simp
      ring
    calc s₀ * ‖m‖ * ‖1 + (σ i : ℂ) * m‖ ≤ s₀ * Cm * (1 + τ⁻¹ * Cm) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hm.2.1 hs₀) hw (norm_nonneg _) (by positivity)
      _ = bulkcb τ τ' c := heq
      _ ≤ m.im := him
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
  rw [← Finset.mul_sum, hdef] at hsum
  have hS0 : 0 ≤ 1 - ‖m‖ ^ 2 * z.im / m.im := by
    rw [← hdef]
    exact Finset.sum_nonneg fun i _ => by positivity
  have hS1 : 0 ≤ ‖m‖ ^ 2 * z.im / m.im := by positivity
  unfold betaCoef
  rw [Complex.sub_re, Complex.one_re, Complex.re_sum]
  unfold bulkcbeta
  rw [← hs₀def]
  by_cases hs : 2 * s₀ ^ 2 ≤ 1
  · refine (min_le_right _ _).trans ?_
    nlinarith
  · refine (min_le_left _ _).trans ?_
    nlinarith

private lemma bulk_cbeta_pos {τ τ' : ℝ} {c : ℝ → ℝ}
    (hτ : 0 < τ) (hcb : 0 < bulkcb τ τ' c) : 0 < bulkcbeta τ τ' c := by
  have := bulk_mBound_pos hτ
  unfold bulkcbeta
  exact lt_min one_pos (by positivity)

/-- `|α| ≤ C_α` when `|m| ≤ C_m`, (mz_reg) holds with `c_b` and `|u - m| ≤ c_b / 2`. -/
private lemma bulk_alpha_le {τ cb Cm : ℝ} {N : ℕ} {σ : Fin M → ℝ}
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

/-- `z + i N⁻⁵ ∈ 𝐃^b_k` for `z ∈ 𝐃^b_k` with `Im z < 1`, when `N⁻⁵ ≤ τ⁻¹ - 1` for `τ < 1`. -/
private lemma bulk_shift_mem {τ τ' : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ}
    (h : DensityAssumptions τ N σ) (hshift : 0 < τ → τ < 1 → ((N : ℝ) ^ 5)⁻¹ ≤ τ⁻¹ - 1)
    {z : ℂ} (hz : z ∈ bulkDomain τ τ' N σ k) (hη1 : z.im < 1) :
    shiftUp N z ∈ bulkDomain τ τ' N σ k := by
  refine shiftUp_mem (spectralDomain_bulkDomain τ τ' N σ k) hz ?_
  rcases (bulk_tau_le_one h).lt_or_eq with hτ | hτ
  · have := hshift h.pos hτ
    linarith
  · exfalso
    have h1 := hz.1.2.2.2.1
    rw [hτ, show (-1 + 1 : ℝ) = 0 by norm_num, Real.rpow_zero] at h1
    linarith

/-- On `𝐃^b_k` the regime is thick: `K₀ δ < κ + η`, when `K₀⁺ (log N)⁻¹ < τ'`. -/
private lemma bulk_thick {τ τ' K₀ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ} {c : ℝ → ℝ}
    (h : DensityAssumptions τ N σ) (hb : RegularBulk c N σ k) (hτ' : 0 < τ')
    (hK : max K₀ 0 * (Real.log N)⁻¹ < τ') {δ : ℂ → ℝ}
    (hδ : AdmissibleDelta N (bulkDomain τ τ' N σ k) δ) {ζ : ℂ}
    (hζ : ζ ∈ bulkDomain τ τ' N σ k) : K₀ * δ ζ < kappa N σ ζ.re + ζ.im := by
  have hκ := (m_sq_root_bulk h hb hτ' hζ).2.1
  have hη := hζ.1.1
  have hδ0 : 0 ≤ δ ζ := le_trans (by positivity) (hδ.lower ζ hζ)
  have h1 : K₀ * δ ζ ≤ max K₀ 0 * δ ζ := mul_le_mul_of_nonneg_right (le_max_left _ _) hδ0
  have h2 : max K₀ 0 * δ ζ ≤ max K₀ 0 * (Real.log N)⁻¹ :=
    mul_le_mul_of_nonneg_left (hδ.upper ζ hζ) (le_max_right _ _)
  linarith

private lemma bulk_twoRegime_thick {C₀ C₁ K₀ κ η d D : ℝ} (hth : K₀ * d < κ + η) :
    twoRegime C₀ C₁ K₀ κ η d D = C₀ * (d / (D + √d)) := by
  unfold twoRegime
  simp only [hth, ↓reduceIte]

private lemma bulk_quot_le_sqrt {d D : ℝ} (hd : 0 < d) (hD : 0 ≤ D) : d / (D + √d) ≤ √d := by
  have hs : 0 < √d := Real.sqrt_pos.2 hd
  calc d / (D + √d) ≤ d / √d := div_le_div_of_nonneg_left hd.le hs (by linarith)
    _ = √d := Real.div_sqrt

/-- `max(2, X) d ≤ C₀ d / (D + √d)` when `D + √d ≤ D_max + 1` and
`C₀ ≥ max(4(D_max + 1), X(D_max + 1))`. -/
private lemma bulk_final {C₀ X Dm D d : ℝ} (hd : 0 < d) (hD : 0 ≤ D) (hDm : D + √d ≤ Dm + 1)
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

/-- The stability step on `𝐃^b_k`: with the a priori bound `C₀ √δ` at `z + i N⁻⁵`,
`|u - m| ≤ max(2, 2 C_ε / c_β) δ`. -/
private lemma bulk_step {τ τ' C₀ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ} {c : ℝ → ℝ}
    (h : DensityAssumptions τ N σ) (hb : RegularBulk c N σ k) (hτ' : 0 < τ')
    (hlog : (Real.log N)⁻¹ ≤ 1 / 2)
    (hshift : 0 < τ → τ < 1 → ((N : ℝ) ^ 5)⁻¹ ≤ τ⁻¹ - 1)
    (hsmall : 0 < τ → 0 < c (τ' / 2) → C₀ * √((Real.log N)⁻¹) + 2 * ((N : ℝ) ^ 3)⁻¹ ≤
      min (bulkcb τ τ' c / 2) (bulkcbeta τ τ' c / (2 * bulkCalpha τ τ' c)))
    (hC₀ : 0 ≤ C₀) {δ : ℂ → ℝ} (hδ : AdmissibleDelta N (bulkDomain τ τ' N σ k) δ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {z : ℂ} (hz : z ∈ bulkDomain τ τ' N σ k)
    (hw : ‖fC N σ (resolventTransform μ z) - z‖ ≤ δ z)
    (hprev : z.im < 1 → ‖resolventTransform μ (shiftUp N z) - mFun N σ (shiftUp N z)‖ ≤
      C₀ * √(δ (shiftUp N z))) :
    ‖resolventTransform μ z - mFun N σ z‖ ≤
      max 2 (2 * bulkCeps τ τ' c / bulkcbeta τ τ' c) * δ z := by
  obtain ⟨hN, hS⟩ := bulk_facts h
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hη := hz.1.1
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
  have hz' : z' ∈ bulkDomain τ τ' N σ k := bulk_shift_mem h hshift hz hη1
  have hη' : 0 < z'.im := hz'.1.1
  have hz'im : z'.im = z.im + ((N : ℝ) ^ 5)⁻¹ := by
    rw [hz'def, shiftUp, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have hdist : ‖z - z'‖ = ((N : ℝ) ^ 5)⁻¹ := by
    rw [hz'def, shiftUp, sub_add_cancel_left, norm_neg, norm_mul, Complex.norm_real,
      Complex.norm_I, mul_one, Real.norm_of_nonneg (by positivity)]
  have hNη : ((N : ℝ))⁻¹ ≤ z.im := by
    have h1 := hz.1.2.2.2.1
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
  have hcb := bulk_cb_pos h hb hτ'
  have hc2 : 0 < c (τ' / 2) := (hb.2.2 (τ' / 2) (half_pos hτ')).1
  have hsm := hsmall h.pos hc2
  -- the quadratic equation
  have hCm := bulk_mBound_pos h.pos
  have hm := gen_prop_m_specDomain h hz.1
  have hmz := mz_reg_bulk h hb hτ' hz
  have hβ := betaCoef_bulk_ge h hb hτ' hz
  have hcβ : 0 < bulkcbeta τ τ' c := bulk_cbeta_pos h.pos hcb
  have hCα : 0 < bulkCalpha τ τ' c := by
    unfold bulkCalpha
    have := inv_pos.2 h.pos
    positivity
  obtain ⟨hmim, hfm⟩ := mFun_spec N σ h.nonneg hη
  set u := resolventTransform μ z with hudef
  set m := mFun N σ z with hmdef
  have hx : ‖u - m‖ ≤ min (bulkcb τ τ' c / 2) (bulkcbeta τ τ' c / (2 * bulkCalpha τ τ' c)) := by
    have e : u - m = (u - resolventTransform μ z') + (resolventTransform μ z' - mFun N σ z') +
        (mFun N σ z' - m) := by ring
    rw [e]
    refine (norm_add₃_le).trans ?_
    have := hprev hη1
    linarith
  have hxcb : ‖u - m‖ ≤ bulkcb τ τ' c / 2 := hx.trans (min_le_left _ _)
  have hxa : ‖u - m‖ ≤ bulkcbeta τ τ' c / (2 * bulkCalpha τ τ' c) := hx.trans (min_le_right _ _)
  have hu0 : u ≠ 0 := fun h0 => by rw [h0] at hu; simp at hu
  have hm0 : m ≠ 0 := fun h0 => by rw [h0] at hmim; simp at hmim
  have hq := quadr_edge N σ hu0 hm0 (fun i => bulk_one_add_ne (h.nonneg i) hu)
    (fun i => bulk_one_add_ne (h.nonneg i) hmim)
  rw [hfm] at hq
  have hα := bulk_alpha_le h hN hcb hCm hm.2.1 hmz hxcb
  have hβn : bulkcbeta τ τ' c ≤ ‖betaCoef N σ m‖ := hβ.trans (Complex.re_le_norm _)
  have hβ0 : betaCoef N σ m ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hβn; linarith
  have hroot := root_dichotomy hα hβ0 hq.symm (by
    have : 2 * bulkCalpha τ τ' c * ‖u - m‖ ≤ bulkcbeta τ τ' c := by
      rw [le_div_iff₀ (by positivity)] at hxa
      linarith
    exact this.trans hβn)
  have hun : ‖u‖ ≤ mBoundConst τ + bulkcb τ τ' c / 2 := by
    have := norm_le_norm_add_norm_sub' u m
    linarith [hm.2.1]
  have hε : ‖u * m * (fC N σ u - z)‖ ≤ bulkCeps τ τ' c * δ z := by
    rw [norm_mul, norm_mul]
    unfold bulkCeps
    have h0 : 0 ≤ ‖u‖ * ‖m‖ := by positivity
    calc ‖u‖ * ‖m‖ * ‖fC N σ u - z‖ ≤ ‖u‖ * ‖m‖ * δ z := mul_le_mul_of_nonneg_left hw h0
      _ ≤ (mBoundConst τ + bulkcb τ τ' c / 2) * mBoundConst τ * δ z := by
          gcongr
          exact hm.2.1
  have hCε : 0 ≤ bulkCeps τ τ' c * δ z := by
    unfold bulkCeps
    positivity
  calc ‖u - m‖ ≤ 2 * ‖u * m * (fC N σ u - z)‖ / ‖betaCoef N σ m‖ := hroot
    _ ≤ 2 * (bulkCeps τ τ' c * δ z) / bulkcbeta τ τ' c :=
        div_le_div₀ (by linarith) (by linarith) hcβ hβn
    _ = 2 * bulkCeps τ τ' c / bulkcbeta τ τ' c * δ z := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hδpos.le

/-- The conditions on `N` used in the stability step hold for all large `N`. -/
private lemma bulk_eventually (τ τ' C₀ K₀ : ℝ) (c : ℝ → ℝ) (hτ' : 0 < τ') :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, (Real.log N)⁻¹ ≤ 1 / 2 ∧ max K₀ 0 * (Real.log N)⁻¹ < τ' ∧
      (0 < τ → τ < 1 → ((N : ℝ) ^ 5)⁻¹ ≤ τ⁻¹ - 1) ∧
      (0 < τ → 0 < c (τ' / 2) → C₀ * √((Real.log N)⁻¹) + 2 * ((N : ℝ) ^ 3)⁻¹ ≤
        min (bulkcb τ τ' c / 2) (bulkcbeta τ τ' c / (2 * bulkCalpha τ τ' c))) := by
  have hlog : Tendsto (fun N : ℕ => (Real.log N)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hpow : ∀ n : ℕ, 0 < n → Tendsto (fun N : ℕ => ((N : ℝ) ^ n)⁻¹) atTop (𝓝 0) :=
    fun n hn => tendsto_inv_atTop_zero.comp
      ((tendsto_pow_atTop hn.ne').comp tendsto_natCast_atTop_atTop)
  have e0 : ∀ᶠ N : ℕ in atTop, (Real.log N)⁻¹ ≤ 1 / 2 :=
    (hlog.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono fun _ h => h.le
  have e1 : ∀ᶠ N : ℕ in atTop, max K₀ 0 * (Real.log N)⁻¹ < τ' := by
    have := hlog.const_mul (max K₀ 0)
    rw [mul_zero] at this
    exact this.eventually (gt_mem_nhds hτ')
  have e2 : ∀ᶠ N : ℕ in atTop, 0 < τ → τ < 1 → ((N : ℝ) ^ 5)⁻¹ ≤ τ⁻¹ - 1 := by
    by_cases hτ : 0 < τ ∧ τ < 1
    · have hpos : 0 < τ⁻¹ - 1 := by
        have := one_lt_inv₀ hτ.1 |>.2 hτ.2
        linarith
      exact ((hpow 5 (by norm_num)).eventually (gt_mem_nhds hpos)).mono
        fun _ h _ _ => h.le
    · exact Eventually.of_forall fun _ h1 h2 => absurd ⟨h1, h2⟩ hτ
  have e3 : ∀ᶠ N : ℕ in atTop, 0 < τ → 0 < c (τ' / 2) →
      C₀ * √((Real.log N)⁻¹) + 2 * ((N : ℝ) ^ 3)⁻¹ ≤
        min (bulkcb τ τ' c / 2) (bulkcbeta τ τ' c / (2 * bulkCalpha τ τ' c)) := by
    by_cases hτ : 0 < τ ∧ 0 < c (τ' / 2)
    · have hcb : 0 < bulkcb τ τ' c := by
        have ha : 0 < Real.arctan (τ * τ' / 2) :=
          Real.arctan_pos.2 (by have := hτ.1; positivity)
        unfold bulkcb
        have := hτ.2
        positivity
      have hcβ : 0 < bulkcbeta τ τ' c := bulk_cbeta_pos hτ.1 hcb
      have hCm := bulk_mBound_pos hτ.1
      have hCα : 0 < bulkCalpha τ τ' c := by
        unfold bulkCalpha
        have := inv_pos.2 hτ.1
        positivity
      have hmin : 0 < min (bulkcb τ τ' c / 2) (bulkcbeta τ τ' c / (2 * bulkCalpha τ τ' c)) :=
        lt_min (by positivity) (by positivity)
      have hsq : Tendsto (fun N : ℕ => √((Real.log N)⁻¹)) atTop (𝓝 0) := by
        have := (Real.continuous_sqrt.tendsto 0).comp hlog
        rwa [Real.sqrt_zero] at this
      have ht := (hsq.const_mul C₀).add ((hpow 3 (by norm_num)).const_mul 2)
      rw [mul_zero, mul_zero, add_zero] at ht
      exact (ht.eventually (gt_mem_nhds hmin)).mono fun _ h _ _ => h.le
    · exact Eventually.of_forall fun _ h1 h2 => absurd ⟨h1, h2⟩ hτ
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (e0.and (e1.and (e2.and e3)))
  exact ⟨N₀, fun N hN => hN₀ N hN⟩

/-- Lemma A.6, stability (Definition 5.4) on `𝐃^b_k`. -/
theorem stab_bulk_weak {τ τ' C₀ C₁ K₀ : ℝ} {c : ℝ → ℝ} (hτ' : 0 < τ')
    (hC₀ : bulkC0wmin τ τ' c ≤ C₀) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {M : ℕ} (σ : Fin M → ℝ) (k : ℕ),
      DensityAssumptions τ N σ → RegularBulk c N σ k →
        StableOn C₀ C₁ K₀ N σ (bulkDomain τ τ' N σ k) := by
  obtain ⟨N₀, hN₀⟩ := bulk_eventually τ τ' C₀ K₀ c hτ'
  refine ⟨N₀, fun N hN M σ k h hb => ?_⟩
  obtain ⟨hlog, hK, hshift, hsmall⟩ := hN₀ N hN
  have hCm := bulk_mBound_pos h.pos
  have hC₀0 : 0 ≤ C₀ := le_trans (by positivity) (le_trans (le_max_left _ _) hC₀)
  intro δ hδ μ hμ z hz hw hprev
  have hthick := fun ζ (hζ : ζ ∈ bulkDomain τ τ' N σ k) => bulk_thick h hb hτ' hK hδ hζ
  have hstep := bulk_step h hb hτ' hlog hshift hsmall hC₀0 hδ μ hz hw (fun hη1 => by
    have hz' := bulk_shift_mem h hshift hz hη1
    refine (hprev hη1).trans ?_
    unfold weakBound
    rw [bulk_twoRegime_thick (hthick _ hz')]
    have him := (mFun_spec N σ h.nonneg hz'.1.1).1
    exact mul_le_mul_of_nonneg_left (bulk_quot_le_sqrt (lt_of_lt_of_le (by
      have := (bulk_facts h).1
      positivity) (hδ.lower _ hz')) him.le) hC₀0)
  unfold weakBound
  rw [bulk_twoRegime_thick (hthick z hz)]
  have hδpos : 0 < δ z := lt_of_lt_of_le (by have := (bulk_facts h).1; positivity)
    (hδ.lower z hz)
  have hδ1 : δ z ≤ 1 := by linarith [(hδ.upper z hz).trans hlog]
  have him := (mFun_spec N σ h.nonneg hz.1.1).1
  have hm := gen_prop_m_specDomain h hz.1
  refine hstep.trans (bulk_final hδpos him.le ?_ hCm.le hC₀)
  have h1 : (mFun N σ z).im ≤ mBoundConst τ :=
    (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans hm.2.1)
  have h2 : √(δ z) ≤ 1 := Real.sqrt_le_one.mpr hδ1
  linarith

/-! ## Instances

Marchenko–Pastur: `M = 1`, `N = 2`, `σ = 1` (`φ = 1/2`), `τ = 1/20`, bulk component `k = 1`,
`τ' = 1/2`, `c(t) = min(t, 1)/50`, at `z = 3/2 + 3i/4`. Here `a_1 = 3/2 + √2`,
`a_2 = 3/2 - √2`, so `3/2 ∈ [a_2 + 1/2, a_1 - 1/2]`; these two edge facts and the regularity
`RegularBulk c 2 σ 1` (true for this `c`: on `[a_2 + t, a_1 - t]` the density
`√((a_1 - E)(E - a_2))/(2πE)` is at least `0.0649 √t`) enter as hypotheses. -/

/-- Stability (Definition 5.4) for the same parameters, with the minimal weak `C₀`. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {M : ℕ} (σ : Fin M → ℝ) (k : ℕ),
    DensityAssumptions (1 / 20) N σ → RegularBulk (fun t : ℝ => min t 1 / 50) N σ k →
      StableOn (bulkC0wmin (1 / 20) (1 / 2) (fun t : ℝ => min t 1 / 50))
        (2 * bulkC0wmin (1 / 20) (1 / 2) (fun t : ℝ => min t 1 / 50)) 36 N σ
        (bulkDomain (1 / 20) (1 / 2) N σ k) :=
  stab_bulk_weak (by norm_num) le_rfl

end Anisotropic
