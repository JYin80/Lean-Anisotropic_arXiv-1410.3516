import Anisotropic.Density.Stability.EdgeSqRoot
import Anisotropic.Density.Stability.Defs
import Anisotropic.Density.Count

/-!
# Lemma A.8 (`lem:stab_outside`) and (im_m_asymp)

Estimates and stability of (def_m) on the outside domain `𝐃^o(τ, τ')`, with explicit constants
depending only on `τ` and `τ'`, and the estimate (im_m_asymp) of §10.1 for `E ∈ [τ, τ⁻¹] ∖ supp ϱ`.
Write `z = E + iη`, `κ = κ(E)`, `t_s = s⁻¹`, `A = 2τ⁻¹(1 + τ⁻¹)` (so `a_1 ≤ A`), `C_m` for the
constant of Lemma 4.10 on `𝐃(τ, N)` and `C_κ` for the bound on `κ`.

* `im_m_outside`: (im_m_outside), `η/(A + 2τ⁻¹)² ≤ Im m ≤ η/τ'²`.
* `m_sq_root_outside`: (m_sq_root) on `𝐃^o`; `E ∉ supp ϱ` and `κ ≥ τ'`.
* `mz_reg_outside`: (mz_reg) on `𝐃^o`.
* `betaCoef_outside_ge`: `|β| ≥ τ'²/C_m²`.
* `stab_outside`, `stab_outside_weak`: Definition A.2 and Definition 5.4 on `𝐃^o`, for every
  `C₁` and `K₀`.
* `im_m_asymp`: (im_m_asymp), `Im m ≍ η (κ + η)^{-1/2}`.

Proofs.
* `Im m = ∫ η ((x - E)² + η²)⁻¹ ϱ(dx)` (Definition 2.2), with `supp ϱ ⊆ [0, a_1]` and
  `|x - E| ≥ τ'` on `supp ϱ`.
* Every edge `a_l` lies in `supp ϱ` (closure of the band `(a_{2k}, a_{2k-1})`), so `κ ≥ τ'`.
* (mz_reg) on the real axis: on `J = [E - ρ, E + ρ]`, `ρ = min(τ', τ/2)/2`, the boundary value
  `m(E')` equals the real integral `M(E') = ∫ (x - E')⁻¹ ϱ(dx)`, which is continuous and increases
  with slope at least `(A + τ⁻¹ + τ')⁻²`. Since `M(E')` is a root of the polynomial of (def_m) at
  `E'` and `-t_s` is not, the intermediate value theorem gives `|M(E) + t_s| ≥ ρ (A + τ⁻¹ + τ')⁻²`.
* (mz_reg) on `𝐃^o`: `|m + t_s| ≥ Im m` when `|E| < τ/2` or `η` is not small, and otherwise
  `|m(z) - M(E)| ≤ η/τ'²`.
* `|β| ≥ 1 - Σ_i σ_i² |m|² / (N |1 + σ_i m|²) = |m|² η / Im m` by (im_def_m).
* Stability: for `N ≥ N₀` the regime `κ + η ≤ K₀ δ` is empty on `𝐃^o`; for `η ≥ 1` the bound
  `|u - m| ≤ 2δ` of Lemma A.5 applies, and for `η < 1` the bound at `z + iN⁻⁵` makes `|u - m|`
  small, so that (quadr_edge) with `|α| ≤ C_α`, `|β| ≥ c_β` selects the small root.
* (im_m_asymp): if `dist(E, supp ϱ) ≥ τ'(τ/2)` use `m_sq_root_outside`; otherwise the band edge
  `a_l` between `E` and the nearest point of `supp ϱ` satisfies `a_l ≥ τ/2` and
  `|E - a_l| < τ'(τ/2)`, and (m_sq_root) of Lemma A.4 at `τ/2` applies.
-/

open MeasureTheory Polynomial Filter Topology
open scoped ENNReal

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-- `(a_1 + 2τ⁻¹)⁻²` with `a_1 ≤ 2τ⁻¹(1 + τ⁻¹)`: `Im m ≥ η · outImLower`. -/
def outImLower (τ : ℝ) : ℝ := ((2 * τ⁻¹ * (1 + τ⁻¹) + 2 * τ⁻¹) ^ 2)⁻¹
/-- (mz_reg) on the real axis: `min(τ', τ/2) / (2 (a_1 + τ⁻¹ + τ')²)`. -/
def outcr (τ τ' : ℝ) : ℝ := min τ' (τ / 2) / (2 * (2 * τ⁻¹ * (1 + τ⁻¹) + τ⁻¹ + τ') ^ 2)
/-- (mz_reg) on `𝐃^o`. -/
def outMz (τ τ' : ℝ) : ℝ :=
  min (outcr τ τ' / 2)
    (min (outcr τ τ' * τ' ^ 2 / 2 * outImLower τ) (√3 / 2 * τ * outImLower τ))
/-- `|β| ≥ τ'² / C_m²`. -/
def outcbeta (τ τ' : ℝ) : ℝ := τ' ^ 2 / mBoundConst τ ^ 2
def outCalpha (τ τ' : ℝ) : ℝ :=
  τ⁻¹ * mBoundConst τ * (1 + mBoundConst τ / outMz τ τ') * 2 / outMz τ τ' ^ 2
def outCeps (τ τ' : ℝ) : ℝ := (mBoundConst τ + outMz τ τ' / 2) * mBoundConst τ
def outC0min (τ τ' : ℝ) : ℝ :=
  max (4 * (√(kappaMax τ + τ⁻¹) + 1))
    (2 * outCeps τ τ' / outcbeta τ τ' * (√(kappaMax τ + τ⁻¹) + 1))
def outC0wmin (τ τ' : ℝ) : ℝ :=
  max (4 * (mBoundConst τ + 1)) (2 * outCeps τ τ' / outcbeta τ τ' * (mBoundConst τ + 1))

/-! ## Elementary consequences of the assumptions -/

/-- (phi_bounded), (bound_Sigma) and (Sigma_gap) give `N > 0`, `τ < 1` and some positive
`σ i`. -/
private lemma out_facts {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) :
    0 < N ∧ τ < 1 ∧ (posVals σ).Nonempty := by
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
  have hM' : (M : ℝ≥0∞)⁻¹ * (M : ℝ≥0∞) = 1 :=
    ENNReal.inv_mul_cancel (by exact_mod_cast hM) (ENNReal.natCast_ne_top _)
  have hfull : (∀ i, σ i ∈ Set.Icc 0 τ) → False := by
    intro hall
    have hgap := h.Sigma_gap
    have happ : empMeasure σ (Set.Icc 0 τ) = (M : ℝ≥0∞)⁻¹ * (M : ℝ≥0∞) := by
      simp only [empMeasure, Measure.smul_apply, Measure.finsetSum_apply,
        Measure.dirac_apply' _ measurableSet_Icc, smul_eq_mul]
      congr 1
      rw [Finset.sum_congr rfl fun i _ => Set.indicator_of_mem (hall i) (1 : ℝ → ℝ≥0∞)]
      simp
    rw [happ, hM', ENNReal.toReal_one] at hgap
    linarith
  refine ⟨hN, ?_, ?_⟩
  · by_contra hc
    push Not at hc
    exact hfull fun i =>
      ⟨h.nonneg i, (h.bound_Sigma i).trans ((inv_le_one_of_one_le₀ hc).trans hc)⟩
  · by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    refine hfull fun i => ⟨h.nonneg i, ?_⟩
    by_contra hi
    have hpos : 0 < σ i := hτ.trans (not_le.1 hi)
    have hmem : σ i ∈ posVals σ := by
      simp only [posVals, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨i, rfl⟩, hpos⟩
    rw [hne] at hmem
    simp at hmem

/-- The constants of Lemma A.8 are positive. -/
private lemma out_consts {τ τ' : ℝ} (hτ : 0 < τ) (hτ' : 0 < τ') :
    0 < outImLower τ ∧ 0 < outcr τ τ' ∧ 0 < outMz τ τ' ∧ 0 < outcbeta τ τ' ∧
      0 < outCalpha τ τ' ∧ 0 < outCeps τ τ' ∧ 0 < mBoundConst τ := by
  have hCm : 0 < mBoundConst τ := by unfold mBoundConst genPropConst; positivity
  have h1 : 0 < outImLower τ := by unfold outImLower; positivity
  have h2 : 0 < outcr τ τ' := by
    unfold outcr
    exact div_pos (lt_min hτ' (half_pos hτ)) (by positivity)
  have h3 : 0 < outMz τ τ' := by
    unfold outMz
    exact lt_min (half_pos h2) (lt_min (by positivity) (by positivity))
  have h4 : 0 < outcbeta τ τ' := by unfold outcbeta; positivity
  have h5 : 0 < outCalpha τ τ' := by unfold outCalpha; positivity
  have h6 : 0 < outCeps τ τ' := by unfold outCeps; positivity
  exact ⟨h1, h2, h3, h4, h5, h6, hCm⟩

/-- `0 ≤ a_1 ≤ 2τ⁻¹(1 + τ⁻¹)`. -/
private lemma out_a1 {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) :
    edgeVal N σ 1 ∈ Set.Icc 0 (2 * τ⁻¹ * (1 + τ⁻¹)) := by
  obtain ⟨hN, -, hS⟩ := out_facts h
  have hp := (card_innerCrit N σ h.nonneg hN hS).2
  exact edgeVal_mem_Icc N σ h.nonneg hN hS h.pos h.phi_lower h.phi_upper h.bound_Sigma le_rfl
    (by omega)

/-! ## The Stieltjes integral of `ϱ` -/

private lemma out_ofReal_sub_ne {z : ℂ} (hz : 0 < z.im) (x : ℝ) : (x : ℂ) - z ≠ 0 := by
  intro h0
  have := congrArg Complex.im h0
  simp at this
  linarith

/-- The kernel `x ↦ (x - z)⁻¹` is integrable for a probability measure when `Im z > 0`. -/
private lemma out_integrable_kernel (μ : Measure ℝ) [IsProbabilityMeasure μ] {z : ℂ}
    (hz : 0 < z.im) : Integrable (fun x : ℝ => ((x : ℂ) - z)⁻¹) μ := by
  refine Integrable.of_bound ?_ (z.im)⁻¹ (ae_of_all _ fun x => ?_)
  · exact ((Complex.continuous_ofReal.sub continuous_const).inv₀
      fun x => out_ofReal_sub_ne hz x).aestronglyMeasurable
  · rw [norm_inv]
    refine inv_anti₀ hz ?_
    have h := Complex.abs_im_le_norm ((x : ℂ) - z)
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] at h
    exact le_trans (le_abs_self _) h

/-- `m(z) = ∫ (x - z)⁻¹ ϱ(dx)` (Definition 2.2). -/
private lemma out_mFun_eq {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {z : ℂ}
    (hz : 0 < z.im) : mFun N σ z = ∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂(varrho N σ) := by
  rw [← resolventTransform_varrho N σ hσ hN hz, resolventTransform_apply]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp [resolvent, Ring.inverse_eq_inv']

/-- The Poisson kernel `Im (x - z)⁻¹ = η / ((x - E)² + η²)`. -/
private def outKer (z : ℂ) (x : ℝ) : ℝ := z.im / ((x - z.re) ^ 2 + z.im ^ 2)

private lemma outKer_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] {z : ℂ} (hz : 0 < z.im) :
    Integrable (outKer z) μ := by
  refine Integrable.of_bound ?_ z.im⁻¹ (ae_of_all _ fun x => ?_)
  · have hc : Continuous (outKer z) := by
      unfold outKer
      exact continuous_const.div (((continuous_id.sub continuous_const).pow 2).add
        continuous_const) fun x => by positivity
    exact hc.aestronglyMeasurable
  · have h0 : 0 ≤ outKer z x := by unfold outKer; positivity
    rw [Real.norm_of_nonneg h0]
    unfold outKer
    rw [div_le_iff₀ (by positivity)]
    have e : z.im⁻¹ * z.im ^ 2 = z.im := by field_simp
    nlinarith [mul_nonneg (inv_nonneg.2 hz.le) (sq_nonneg (x - z.re))]

/-- `Im m(z) = ∫ η / ((x - E)² + η²) ϱ(dx)` (Definition 2.2). -/
private lemma out_im_mFun {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {z : ℂ}
    (hz : 0 < z.im) : (mFun N σ z).im = ∫ x, outKer z x ∂(varrho N σ) := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  have hint := out_integrable_kernel (varrho N σ) hz
  rw [out_mFun_eq hσ hN hz]
  have him : (∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂(varrho N σ)).im =
      ∫ x : ℝ, (((x : ℂ) - z)⁻¹).im ∂(varrho N σ) := by
    have := integral_im (𝕜 := ℂ) hint
    simpa using this.symm
  rw [him]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [outKer]
  rw [Complex.inv_im, Complex.normSq_apply]
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.sub_re, Complex.ofReal_re]
  ring

/-- `ϱ`-almost every point lies in `supp ϱ`. -/
private lemma out_ae_support (N : ℕ) (σ : Fin M → ℝ) :
    ∀ᵐ x ∂(varrho N σ), x ∈ (varrho N σ).support :=
  Measure.support_mem_ae

/-- `ϱ`-almost every point lies in `[0, a_1]`. -/
private lemma out_ae_Icc {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) : ∀ᵐ x ∂(varrho N σ), x ∈ Set.Icc 0 (edgeVal N σ 1) :=
  mem_ae_iff.2 (varrho_compl_Icc_edgeVal N σ hσ hN hS)

/-- `τ' ≤ |y - E|` for `y ∈ S` when `τ' ≤ dist(E, S)`. -/
private lemma out_le_abs_of_mem {S : Set ℝ} {E τ' y : ℝ} (hd : τ' ≤ Metric.infDist E S)
    (hy : y ∈ S) : τ' ≤ |y - E| := by
  have := Metric.infDist_le_dist_of_mem (x := E) hy
  rw [Real.dist_eq, abs_sub_comm] at this
  linarith

/-- Every edge `a_l`, `1 ≤ l ≤ 2p`, lies in `supp ϱ`. -/
private lemma out_edge_mem_support {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ}
    (h : DensityAssumptions τ N σ) {l : ℕ} (hl1 : 1 ≤ l) (hl2 : l ≤ 2 * numBands N σ) :
    edgeVal N σ l ∈ (varrho N σ).support := by
  obtain ⟨hN, -, hS⟩ := out_facts h
  have hσ := h.nonneg
  have key : ∀ k, 1 ≤ k → k ≤ numBands N σ →
      edgeVal N σ (2 * k) ∈ (varrho N σ).support ∧
        edgeVal N σ (2 * k - 1) ∈ (varrho N σ).support := by
    intro k hk1 hk2
    have hlt := edgeVal_band_lt N σ hσ hN hS hk1 hk2
    have h0 : 0 ≤ edgeVal N σ (2 * k) :=
      (edgeVal_mem_Icc N σ hσ hN hS h.pos h.phi_lower h.phi_upper h.bound_Sigma
        (k := 2 * k) (by omega) (by omega)).1
    have hsub : Set.Icc (edgeVal N σ (2 * k)) (edgeVal N σ (2 * k - 1)) ⊆
        (varrho N σ).support := by
      rw [← closure_Ioo hlt.ne]
      refine closure_minimal (fun y hy => ?_) Measure.isClosed_support
      exact (mem_support_varrho_iff N σ hσ hN hS (h0.trans_lt hy.1)).2
        ⟨k, hk1, hk2, hy.1.le, hy.2.le⟩
    exact ⟨hsub ⟨le_rfl, hlt.le⟩, hsub ⟨hlt.le, le_rfl⟩⟩
  rcases Nat.even_or_odd' l with ⟨k, rfl | rfl⟩
  · exact (key k (by omega) (by omega)).1
  · have e : 2 * k + 1 = 2 * (k + 1) - 1 := by omega
    rw [e]
    exact (key (k + 1) (by omega) (by omega)).2

/-! ## The real Stieltjes integral off the support -/

/-- `M(E) = ∫ (x - E)⁻¹ ϱ(dx)`. -/
private def outM (N : ℕ) (σ : Fin M → ℝ) (E : ℝ) : ℝ := ∫ x, (x - E)⁻¹ ∂(varrho N σ)

private lemma out_integrable_re {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    {E d : ℝ} (hd : 0 < d) (hs : ∀ y ∈ (varrho N σ).support, d ≤ |y - E|) :
    Integrable (fun x : ℝ => (x - E)⁻¹) (varrho N σ) := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  refine Integrable.of_bound ((measurable_id.sub_const E).inv.aestronglyMeasurable) d⁻¹ ?_
  filter_upwards [out_ae_support N σ] with x hx
  rw [Real.norm_eq_abs, abs_inv]
  exact inv_anti₀ hd (hs x hx)

/-- `|m(z) - M(E)| ≤ η / d²` when `|x - E| ≥ d` on `supp ϱ`. -/
private lemma out_norm_mFun_sub_le {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    {z : ℂ} (hz : 0 < z.im) {d : ℝ} (hd : 0 < d)
    (hs : ∀ y ∈ (varrho N σ).support, d ≤ |y - z.re|) :
    ‖mFun N σ z - (outM N σ z.re : ℂ)‖ ≤ z.im / d ^ 2 := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  have hi1 := out_integrable_kernel (varrho N σ) hz
  have hi2 : Integrable (fun x : ℝ => ((x : ℂ) - (z.re : ℂ))⁻¹) (varrho N σ) := by
    have := (out_integrable_re hσ hN hd hs).ofReal (𝕜 := ℂ)
    refine this.congr (ae_of_all _ fun x => ?_)
    push_cast
    rfl
  have h2 : ((outM N σ z.re : ℝ) : ℂ) = ∫ x : ℝ, ((x : ℂ) - (z.re : ℂ))⁻¹ ∂(varrho N σ) := by
    rw [outM, ← integral_complex_ofReal]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    push_cast
    rfl
  rw [out_mFun_eq hσ hN hz, h2, ← integral_sub hi1 hi2]
  have hb : ∀ᵐ x : ℝ ∂(varrho N σ),
      ‖((x : ℂ) - z)⁻¹ - ((x : ℂ) - (z.re : ℂ))⁻¹‖ ≤ z.im / d ^ 2 := by
    filter_upwards [out_ae_support N σ] with x hx
    have hxd := hs x hx
    have n1 : (x : ℂ) - z ≠ 0 := out_ofReal_sub_ne hz x
    have hn3 : ‖(x : ℂ) - (z.re : ℂ)‖ = |x - z.re| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have n2 : (x : ℂ) - (z.re : ℂ) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hn3
      linarith
    have e : ((x : ℂ) - z)⁻¹ - ((x : ℂ) - (z.re : ℂ))⁻¹ =
        (z - (z.re : ℂ)) / (((x : ℂ) - z) * ((x : ℂ) - (z.re : ℂ))) := by
      field_simp
      ring
    have hn1 : ‖z - (z.re : ℂ)‖ = z.im := by
      have : z - (z.re : ℂ) = (z.im : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hz]
    have hn2 : d ≤ ‖(x : ℂ) - z‖ := by
      calc d ≤ |x - z.re| := hxd
        _ = |((x : ℂ) - z).re| := by simp
        _ ≤ _ := Complex.abs_re_le_norm _
    rw [e, norm_div, norm_mul, hn1, hn3]
    refine div_le_div_of_nonneg_left hz.le (by positivity) ?_
    rw [sq]
    exact mul_le_mul hn2 hxd hd.le (norm_nonneg _)
  have := norm_integral_le_of_norm_le_const hb
  simpa using this

/-- For `E ≠ 0` off the support, the boundary value `m(E)` is the real integral `M(E)`. -/
private lemma out_mExt_eq {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {E d : ℝ}
    (hE : E ≠ 0) (hd : 0 < d) (hs : ∀ y ∈ (varrho N σ).support, d ≤ |y - E|) :
    mExt N σ E = (outM N σ E : ℂ) := by
  set g : ℝ → ℂ := fun η => (E : ℂ) + (η : ℂ) * Complex.I with hg
  have hgt : Tendsto g (𝓝[>] 0) (𝓝[upperHalf] (E : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hc : Continuous g := by rw [hg]; fun_prop
      have := hc.tendsto 0
      have e : g 0 = (E : ℂ) := by simp [hg]
      rw [e] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with η hη
      change 0 < (g η).im
      simpa [hg] using hη
  have h1 : Tendsto (fun η => mFun N σ (g η)) (𝓝[>] 0) (𝓝 (mExt N σ E)) :=
    (tendsto_mFun_of_ne_zero N σ hσ hE).comp hgt
  have h2 : Tendsto (fun η => mFun N σ (g η)) (𝓝[>] 0) (𝓝 (outM N σ E : ℂ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (g := fun η : ℝ => η / d ^ 2)
      (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with η hη
      have hre : (g η).re = E := by simp [hg]
      have him : (g η).im = η := by simp [hg]
      have := out_norm_mFun_sub_le hσ hN (z := g η) (by rw [him]; exact hη) hd
        (by rw [hre]; exact hs)
      rwa [hre, him] at this
    · have : Tendsto (fun η : ℝ => η / d ^ 2) (𝓝 0) (𝓝 (0 / d ^ 2)) :=
        (continuous_id.div_const _).tendsto 0
      rw [zero_div] at this
      exact this.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique h1 h2

/-- `|M(E₂) - M(E₁)| ≤ |E₂ - E₁| / d²` when both points are at distance `≥ d` from
`supp ϱ`. -/
private lemma out_lip {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {E₁ E₂ d : ℝ}
    (hd : 0 < d) (h1 : ∀ y ∈ (varrho N σ).support, d ≤ |y - E₁|)
    (h2 : ∀ y ∈ (varrho N σ).support, d ≤ |y - E₂|) :
    |outM N σ E₂ - outM N σ E₁| ≤ |E₂ - E₁| / d ^ 2 := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  rw [outM, outM, ← integral_sub (out_integrable_re hσ hN hd h2) (out_integrable_re hσ hN hd h1)]
  have hb : ∀ᵐ x ∂(varrho N σ), ‖(x - E₂)⁻¹ - (x - E₁)⁻¹‖ ≤ |E₂ - E₁| / d ^ 2 := by
    filter_upwards [out_ae_support N σ] with x hx
    have a1 := h1 x hx
    have a2 := h2 x hx
    have n1 : x - E₁ ≠ 0 := fun h0 => by rw [h0, abs_zero] at a1; linarith
    have n2 : x - E₂ ≠ 0 := fun h0 => by rw [h0, abs_zero] at a2; linarith
    have e : (x - E₂)⁻¹ - (x - E₁)⁻¹ = (E₂ - E₁) / ((x - E₁) * (x - E₂)) := by
      field_simp
      ring
    rw [Real.norm_eq_abs, e, abs_div, abs_mul]
    refine div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) ?_
    rw [sq]
    exact mul_le_mul a1 a2 hd.le (abs_nonneg _)
  have := norm_integral_le_of_norm_le_const hb
  simpa using this

/-- `M(E₂) - M(E₁) ≥ (E₂ - E₁) / L` when `0 < (x - E₁)(x - E₂) ≤ L` on `supp ϱ ∩ [0, a_1]`. -/
private lemma out_slope {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {E₁ E₂ d L : ℝ} (hd : 0 < d) (h12 : E₁ ≤ E₂)
    (h1 : ∀ y ∈ (varrho N σ).support, d ≤ |y - E₁|)
    (h2 : ∀ y ∈ (varrho N σ).support, d ≤ |y - E₂|)
    (hP : ∀ y ∈ (varrho N σ).support, y ∈ Set.Icc 0 (edgeVal N σ 1) →
      0 < (y - E₁) * (y - E₂) ∧ (y - E₁) * (y - E₂) ≤ L) :
    (E₂ - E₁) / L ≤ outM N σ E₂ - outM N σ E₁ := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  have hi := (out_integrable_re hσ hN hd h2).sub (out_integrable_re hσ hN hd h1)
  rw [outM, outM, ← integral_sub (out_integrable_re hσ hN hd h2) (out_integrable_re hσ hN hd h1)]
  have hb : ∀ᵐ x ∂(varrho N σ), (E₂ - E₁) / L ≤ (x - E₂)⁻¹ - (x - E₁)⁻¹ := by
    filter_upwards [out_ae_support N σ, out_ae_Icc hσ hN hS] with x hx hxI
    obtain ⟨hp, hpL⟩ := hP x hx hxI
    have n1 : x - E₁ ≠ 0 := fun h0 => by rw [h0, zero_mul] at hp; exact lt_irrefl _ hp
    have n2 : x - E₂ ≠ 0 := fun h0 => by rw [h0, mul_zero] at hp; exact lt_irrefl _ hp
    have e : (x - E₂)⁻¹ - (x - E₁)⁻¹ = (E₂ - E₁) / ((x - E₁) * (x - E₂)) := by
      field_simp
      ring
    rw [e]
    exact div_le_div_of_nonneg_left (by linarith) hp hpL
  have := integral_mono_ae (integrable_const ((E₂ - E₁) / L)) hi hb
  simpa using this

/-- (mz_reg) on the real axis, in terms of `M(E)`. -/
private lemma out_real_core {τ τ' : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ)
    (hτ' : 0 < τ') {E : ℝ} (hE : τ / 2 ≤ |E|) (hEτ : |E| ≤ τ⁻¹)
    (hd : τ' ≤ Metric.infDist E (varrho N σ).support) :
    mExt N σ E = (outM N σ E : ℂ) ∧ ∀ s ∈ posVals σ, outcr τ τ' ≤ |outM N σ E + s⁻¹| := by
  obtain ⟨hN, -, hS⟩ := out_facts h
  have hσ := h.nonneg
  have hτ := h.pos
  obtain ⟨ha0, haA⟩ := out_a1 h
  have hτi : 0 < τ⁻¹ := inv_pos.2 hτ
  set A := 2 * τ⁻¹ * (1 + τ⁻¹) with hA
  have hA0 : 0 ≤ A := by positivity
  set ρ := min τ' (τ / 2) / 2 with hρ
  have hρ0 : 0 < ρ := div_pos (lt_min hτ' (half_pos hτ)) two_pos
  have hρ1 : ρ ≤ τ' / 2 := by have := min_le_left τ' (τ / 2); linarith
  have hρ2 : ρ ≤ τ / 4 := by have := min_le_right τ' (τ / 2); linarith
  set L := A + τ⁻¹ + τ' with hL
  have hL0 : 0 < L := by positivity
  have hcr : outcr τ τ' = ρ / L ^ 2 := by
    rw [hρ, div_div]
    rfl
  have hsE : ∀ y ∈ (varrho N σ).support, τ' ≤ |y - E| := fun y hy => out_le_abs_of_mem hd hy
  obtain ⟨hE1, hE2⟩ := abs_le.1 hEτ
  have hJd : ∀ E' ∈ Set.Icc (E - ρ) (E + ρ), ∀ y ∈ (varrho N σ).support,
      τ' / 2 ≤ |y - E'| := by
    intro E' hE' y hy
    have := hsE y hy
    have h1 : |E' - E| ≤ ρ := abs_le.2 ⟨by linarith [hE'.1], by linarith [hE'.2]⟩
    have h2 : |y - E| ≤ |y - E'| + |E' - E| := abs_sub_le y E' E
    linarith
  have hJ0 : ∀ E' ∈ Set.Icc (E - ρ) (E + ρ), E' ≠ 0 := by
    intro E' hE' h0
    rw [h0] at hE'
    have : |E| ≤ ρ := abs_le.2 ⟨by linarith [hE'.2], by linarith [hE'.1]⟩
    linarith
  have hJm : ∀ E' ∈ Set.Icc (E - ρ) (E + ρ), mExt N σ E' = (outM N σ E' : ℂ) := fun E' hE' =>
    out_mExt_eq hσ hN (hJ0 E' hE') (half_pos hτ') (hJd E' hE')
  have hcont : ContinuousOn (outM N σ) (Set.Icc (E - ρ) (E + ρ)) := by
    rw [Metric.continuousOn_iff]
    intro b hb ε hε
    refine ⟨ε * (τ' / 2) ^ 2, by positivity, fun a ha hab => ?_⟩
    rw [Real.dist_eq] at hab ⊢
    have := out_lip hσ hN (half_pos hτ') (hJd b hb) (hJd a ha)
    calc |outM N σ a - outM N σ b| ≤ |a - b| / (τ' / 2) ^ 2 := this
      _ < ε := by rw [div_lt_iff₀ (by positivity)]; exact hab
  have hslope : ∀ E₁ ∈ Set.Icc (E - ρ) (E + ρ), ∀ E₂ ∈ Set.Icc (E - ρ) (E + ρ), E₁ ≤ E₂ →
      (E₂ - E₁) / L ^ 2 ≤ outM N σ E₂ - outM N σ E₁ := by
    intro E₁ h1 E₂ h2 h12
    refine out_slope hσ hN hS (half_pos hτ') h12 (hJd E₁ h1) (hJd E₂ h2) ?_
    intro y hy hyI
    have hyE := hsE y hy
    obtain ⟨hy0, hya⟩ := hyI
    have hy1 : |y - E₁| ≤ L := abs_le.2 ⟨by linarith [h1.2], by linarith [h1.1]⟩
    have hy2 : |y - E₂| ≤ L := abs_le.2 ⟨by linarith [h2.2], by linarith [h2.1]⟩
    have hsame : 0 < (y - E₁) * (y - E₂) := by
      rcases le_or_gt E y with hyE' | hyE'
      · rw [abs_of_nonneg (by linarith)] at hyE
        apply mul_pos <;> linarith [h1.2, h2.2]
      · rw [abs_of_neg (by linarith)] at hyE
        apply mul_pos_of_neg_of_neg <;> linarith [h1.1, h2.1]
    refine ⟨hsame, ?_⟩
    calc (y - E₁) * (y - E₂) ≤ |(y - E₁) * (y - E₂)| := le_abs_self _
      _ = |y - E₁| * |y - E₂| := abs_mul _ _
      _ ≤ L * L := mul_le_mul hy1 hy2 (abs_nonneg _) hL0.le
      _ = L ^ 2 := by ring
  have hEJ : E ∈ Set.Icc (E - ρ) (E + ρ) := ⟨by linarith, by linarith⟩
  refine ⟨hJm E hEJ, fun s hs => ?_⟩
  rw [hcr]
  by_contra hlt
  push Not at hlt
  have hlo : E - ρ ∈ Set.Icc (E - ρ) (E + ρ) := ⟨le_rfl, by linarith⟩
  have hhi : E + ρ ∈ Set.Icc (E - ρ) (E + ρ) := ⟨by linarith, le_rfl⟩
  have s1 := hslope (E - ρ) hlo E hEJ (by linarith)
  have s2 := hslope E hEJ (E + ρ) hhi (by linarith)
  rw [show E - (E - ρ) = ρ by ring] at s1
  rw [show E + ρ - E = ρ by ring] at s2
  obtain ⟨l1, l2⟩ := abs_lt.1 hlt
  have hmem : -s⁻¹ ∈ Set.Icc (outM N σ (E - ρ)) (outM N σ (E + ρ)) :=
    ⟨by linarith, by linarith⟩
  obtain ⟨E', hE', hval⟩ := intermediate_value_Icc (by linarith) hcont hmem
  have hP := scPoly_eval_mExt N σ hσ (hJ0 E' hE')
  rw [hJm E' hE', hval] at hP
  exact scPoly_eval_pole N σ hN (E' : ℂ) hs (by push_cast at hP; exact hP)

/-! ## Lemma A.8: (im_m_outside), (m_sq_root), (mz_reg) and `|β|` -/

/-- (im_m_outside): `Im m ≍ η` on `𝐃^o`. -/
theorem im_m_outside {τ τ' : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ)
    (hτ' : 0 < τ') {z : ℂ} (hz : z ∈ outsideDomain τ τ' N σ) :
    outImLower τ * z.im ≤ (mFun N σ z).im ∧ (mFun N σ z).im ≤ z.im / τ' ^ 2 := by
  obtain ⟨hN, -, hS⟩ := out_facts h
  have hσ := h.nonneg
  have hτ := h.pos
  have := isProbabilityMeasure_varrho N σ hσ hN
  obtain ⟨⟨hη, -, hEτ, -, hητ⟩, hd⟩ := hz
  obtain ⟨ha0, haA⟩ := out_a1 h
  have hτi : 0 < τ⁻¹ := inv_pos.2 hτ
  obtain ⟨hE1, hE2⟩ := abs_le.1 hEτ
  rw [out_im_mFun hσ hN hη]
  refine ⟨?_, ?_⟩
  · have hb : ∀ᵐ x ∂(varrho N σ), outImLower τ * z.im ≤ outKer z x := by
      filter_upwards [out_ae_Icc hσ hN hS] with x hx
      obtain ⟨hx0, hxa⟩ := hx
      unfold outKer outImLower
      rw [inv_mul_eq_div]
      refine div_le_div_of_nonneg_left hη.le (by positivity) ?_
      have h1 : (x - z.re) ^ 2 ≤ (2 * τ⁻¹ * (1 + τ⁻¹) + τ⁻¹) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _)
          (abs_le.2 ⟨by linarith, by linarith⟩) 2
      have h2 : z.im ^ 2 ≤ τ⁻¹ ^ 2 := pow_le_pow_left₀ hη.le hητ 2
      nlinarith
    have := integral_mono_ae (integrable_const (outImLower τ * z.im))
      (outKer_integrable _ hη) hb
    simpa using this
  · have hb : ∀ᵐ x ∂(varrho N σ), outKer z x ≤ z.im / τ' ^ 2 := by
      filter_upwards [out_ae_support N σ] with x hx
      have hxE := out_le_abs_of_mem hd hx
      unfold outKer
      refine div_le_div_of_nonneg_left hη.le (by positivity) ?_
      have : τ' ^ 2 ≤ (x - z.re) ^ 2 := by
        rw [← sq_abs (x - z.re)]
        exact pow_le_pow_left₀ hτ'.le hxE 2
      nlinarith
    have := integral_mono_ae (outKer_integrable _ hη) (integrable_const (z.im / τ' ^ 2)) hb
    simpa using this

/-- Lemma A.8, (m_sq_root) (outside case) on `𝐃^o`. -/
theorem m_sq_root_outside {τ τ' : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ)
    (hτ' : 0 < τ') {z : ℂ} (hz : z ∈ outsideDomain τ τ' N σ) :
    z.re ∉ (varrho N σ).support ∧ τ' ≤ kappa N σ z.re ∧
    outImLower τ * √τ' * (z.im / √(kappa N σ z.re + z.im)) ≤ (mFun N σ z).im ∧
    (mFun N σ z).im ≤ √(kappaMax τ + τ⁻¹) / τ' ^ 2 * (z.im / √(kappa N σ z.re + z.im)) := by
  obtain ⟨hN, -, hS⟩ := out_facts h
  have hτ := h.pos
  obtain ⟨hlow, hup⟩ := im_m_outside h hτ' hz
  obtain ⟨⟨hη, -, hEτ, -, hητ⟩, hd⟩ := hz
  have hoIL : 0 < outImLower τ := (out_consts hτ hτ').1
  have hnot : z.re ∉ (varrho N σ).support := by
    intro hmem
    rw [Metric.infDist_zero_of_mem hmem] at hd
    linarith
  have hκ : τ' ≤ kappa N σ z.re := by
    have hp := (card_innerCrit N σ h.nonneg hN hS).2
    have hmem : (1 : ℕ) ∈ Finset.Icc 1 (2 * numBands N σ) :=
      Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
    have : Nonempty (Finset.Icc 1 (2 * numBands N σ)) := ⟨⟨1, hmem⟩⟩
    refine le_ciInf fun l => ?_
    obtain ⟨l1, l2⟩ := Finset.mem_Icc.1 l.2
    have := out_le_abs_of_mem hd (out_edge_mem_support h l1 l2)
    rwa [abs_sub_comm] at this
  have hκ0 : 0 < kappa N σ z.re + z.im := by linarith
  have hsq := Real.sqrt_pos.2 hκ0
  refine ⟨hnot, hκ, ?_, ?_⟩
  · have hr : √τ' / √(kappa N σ z.re + z.im) ≤ 1 :=
      (div_le_one hsq).2 (Real.sqrt_le_sqrt (by linarith))
    calc outImLower τ * √τ' * (z.im / √(kappa N σ z.re + z.im))
        = outImLower τ * z.im * (√τ' / √(kappa N σ z.re + z.im)) := by ring
      _ ≤ outImLower τ * z.im * 1 :=
          mul_le_mul_of_nonneg_left hr (by positivity)
      _ = outImLower τ * z.im := mul_one _
      _ ≤ _ := hlow
  · refine hup.trans ?_
    have hκu : kappa N σ z.re ≤ kappaMax τ := kappa_le h hEτ
    have hs : √(kappa N σ z.re + z.im) ≤ √(kappaMax τ + τ⁻¹) :=
      Real.sqrt_le_sqrt (by linarith)
    rw [div_mul_div_comm, le_div_iff₀ (by positivity)]
    have : z.im / τ' ^ 2 * (τ' ^ 2 * √(kappa N σ z.re + z.im)) =
        z.im * √(kappa N σ z.re + z.im) := by field_simp
    rw [this, mul_comm (√(kappaMax τ + τ⁻¹)) z.im]
    exact mul_le_mul_of_nonneg_left hs hη.le

/-- Lemma A.8, (mz_reg) on `𝐃^o`. -/
theorem mz_reg_outside {τ τ' : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ)
    (hτ' : 0 < τ') {z : ℂ} (hz : z ∈ outsideDomain τ τ' N σ) :
    ∀ s ∈ posVals σ, outMz τ τ' ≤ ‖mFun N σ z + ((s⁻¹ : ℝ) : ℂ)‖ := by
  obtain ⟨hN, -, -⟩ := out_facts h
  have hσ := h.nonneg
  have hτ := h.pos
  obtain ⟨h1, h2, -, -, -, -, -⟩ := out_consts hτ hτ'
  have himo := (im_m_outside h hτ' hz).1
  obtain ⟨⟨hη, hnorm, hEτ, -, -⟩, hd⟩ := hz
  intro s hs
  have hIm : (mFun N σ z).im ≤ ‖mFun N σ z + ((s⁻¹ : ℝ) : ℂ)‖ := by
    have := Complex.im_le_norm (mFun N σ z + ((s⁻¹ : ℝ) : ℂ))
    simpa using this
  have hm1 : outMz τ τ' ≤ outcr τ τ' / 2 := min_le_left _ _
  have hm2 : outMz τ τ' ≤ outcr τ τ' * τ' ^ 2 / 2 * outImLower τ :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hm3 : outMz τ τ' ≤ √3 / 2 * τ * outImLower τ :=
    (min_le_right _ _).trans (min_le_right _ _)
  by_cases hEs : |z.re| < τ / 2
  · have hηl : √3 / 2 * τ ≤ z.im := by
      have hn2 : τ ^ 2 ≤ z.re ^ 2 + z.im ^ 2 := by
        have := pow_le_pow_left₀ hτ.le hnorm 2
        rwa [Complex.sq_norm, Complex.normSq_apply, ← sq, ← sq] at this
      obtain ⟨r1, r2⟩ := abs_lt.1 hEs
      have hre2 : z.re ^ 2 < (τ / 2) ^ 2 := sq_lt_sq' r1 r2
      by_contra hc
      push Not at hc
      have hc2 : z.im ^ 2 < (√3 / 2 * τ) ^ 2 := pow_lt_pow_left₀ hc hη.le two_ne_zero
      have h3 : (√3 / 2 * τ) ^ 2 = 3 / 4 * τ ^ 2 := by
        rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
        ring
      nlinarith
    calc outMz τ τ' ≤ √3 / 2 * τ * outImLower τ := hm3
      _ = outImLower τ * (√3 / 2 * τ) := by ring
      _ ≤ outImLower τ * z.im := mul_le_mul_of_nonneg_left hηl h1.le
      _ ≤ _ := himo.trans hIm
  · push Not at hEs
    by_cases hηs : outcr τ τ' * τ' ^ 2 / 2 ≤ z.im
    · calc outMz τ τ' ≤ outcr τ τ' * τ' ^ 2 / 2 * outImLower τ := hm2
        _ = outImLower τ * (outcr τ τ' * τ' ^ 2 / 2) := by ring
        _ ≤ outImLower τ * z.im := mul_le_mul_of_nonneg_left hηs h1.le
        _ ≤ _ := himo.trans hIm
    · push Not at hηs
      obtain ⟨-, hreg⟩ := out_real_core h hτ' hEs hEτ hd
      have hr := hreg s hs
      have hdiff := out_norm_mFun_sub_le hσ hN hη hτ' (fun y hy => out_le_abs_of_mem hd hy)
      have hsmall : z.im / τ' ^ 2 < outcr τ τ' / 2 := by
        rw [div_lt_iff₀ (by positivity)]
        have e : outcr τ τ' / 2 * τ' ^ 2 = outcr τ τ' * τ' ^ 2 / 2 := by ring
        rw [e]
        exact hηs
      have htri := norm_sub_le (mFun N σ z + ((s⁻¹ : ℝ) : ℂ)) (mFun N σ z - (outM N σ z.re : ℂ))
      have e : mFun N σ z + ((s⁻¹ : ℝ) : ℂ) - (mFun N σ z - (outM N σ z.re : ℂ)) =
          ((outM N σ z.re + s⁻¹ : ℝ) : ℂ) := by
        push_cast
        ring
      rw [e, Complex.norm_real, Real.norm_eq_abs] at htri
      linarith

theorem betaCoef_outside_ge {τ τ' : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ)
    (hτ' : 0 < τ') {z : ℂ} (hz : z ∈ outsideDomain τ τ' N σ) :
    outcbeta τ τ' ≤ ‖betaCoef N σ (mFun N σ z)‖ := by
  have hσ := h.nonneg
  have hτ := h.pos
  obtain ⟨-, -, -, -, -, -, hCm⟩ := out_consts hτ hτ'
  have hη : 0 < z.im := hz.1.1
  obtain ⟨hmpos, -⟩ := mFun_spec N σ hσ hη
  obtain ⟨hmlow, -, -⟩ := gen_prop_m_specDomain h hz.1
  have hup := (im_m_outside h hτ' hz).2
  have hid := im_def_m (N := N) hσ hη
  set m := mFun N σ z with hm
  have hsum : ‖∑ i, m ^ 2 * (σ i : ℂ) ^ 2 / (N * (1 + σ i * m) ^ 2)‖ ≤
      1 - ‖m‖ ^ 2 * z.im / m.im := by
    rw [← hid]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    simp only [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Complex.norm_natCast]
    ring
  have hβ : 1 - ‖∑ i, m ^ 2 * (σ i : ℂ) ^ 2 / (N * (1 + σ i * m) ^ 2)‖ ≤
      ‖betaCoef N σ m‖ := by
    have := norm_sub_norm_le (1 : ℂ) (∑ i, m ^ 2 * (σ i : ℂ) ^ 2 / (N * (1 + σ i * m) ^ 2))
    rw [norm_one] at this
    unfold betaCoef
    exact this
  have hq : τ' ^ 2 ≤ z.im / m.im := by
    rw [le_div_iff₀ hmpos]
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < τ' ^ 2)).1 hup
    linarith
  have hm2 : (mBoundConst τ)⁻¹ ^ 2 ≤ ‖m‖ ^ 2 := pow_le_pow_left₀ (by positivity) hmlow 2
  calc outcbeta τ τ' = (mBoundConst τ)⁻¹ ^ 2 * τ' ^ 2 := by unfold outcbeta; field_simp
    _ ≤ ‖m‖ ^ 2 * (z.im / m.im) := mul_le_mul hm2 hq (by positivity) (by positivity)
    _ = ‖m‖ ^ 2 * z.im / m.im := by ring
    _ ≤ _ := by linarith

/-! ## Lemma A.8: stability -/

/-- `d / (D + √d) ≤ √d`. -/
private lemma out_quot_le_sqrt {d D : ℝ} (hd : 0 ≤ d) (hD : 0 ≤ D) : d / (D + √d) ≤ √d := by
  rcases hd.eq_or_lt with h0 | h0
  · rw [← h0]; simp
  · have hs := Real.sqrt_pos.2 h0
    rw [div_le_iff₀ (by positivity)]
    have := Real.mul_self_sqrt hd
    nlinarith

/-- `1 + σ_i w ≠ 0` for `Im w > 0`. -/
private lemma out_one_add_ne {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) {w : ℂ} (hw : 0 < w.im)
    (i : Fin M) : 1 + (σ i : ℂ) * w ≠ 0 := by
  intro h0
  have him : (1 + (σ i : ℂ) * w).im = σ i * w.im := by simp
  rw [h0, Complex.zero_im] at him
  rcases (hσ i).eq_or_lt with h' | h'
  · rw [← h'] at h0
    simp at h0
  · have := mul_pos h' hw
    linarith

/-- `|α| ≤ τ⁻¹ C_m (1 + C_m/c) · 2/c²` when `|m| ≤ C_m`, `|m + t_s| ≥ c` and
`|u + t_s| ≥ c/2`. -/
private lemma out_alpha_le {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ)
    {u m : ℂ} {c Cm : ℝ} (hc : 0 < c) (hm : ‖m‖ ≤ Cm)
    (hmr : ∀ s ∈ posVals σ, c ≤ ‖m + ((s⁻¹ : ℝ) : ℂ)‖)
    (hur : ∀ s ∈ posVals σ, c / 2 ≤ ‖u + ((s⁻¹ : ℝ) : ℂ)‖) :
    ‖alphaCoef N σ u m‖ ≤ τ⁻¹ * Cm * (1 + Cm / c) * 2 / c ^ 2 := by
  obtain ⟨hN, -, -⟩ := out_facts h
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hCm : 0 ≤ Cm := (norm_nonneg _).trans hm
  set K := Cm * (1 + Cm / c) * 2 / c ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hterm : ∀ i, ‖m * (σ i : ℂ) ^ 2 / (N * (1 + σ i * m) ^ 2 * (1 + σ i * u))‖ ≤ K / N := by
    intro i
    rcases (h.nonneg i).eq_or_lt with h0 | hpos
    · rw [← h0]
      simp only [Complex.ofReal_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, mul_zero, zero_div, norm_zero]
      positivity
    · have hs : σ i ∈ posVals σ := by
        simp only [posVals, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨⟨i, rfl⟩, hpos⟩
      have ht : 0 < (σ i)⁻¹ := inv_pos.2 hpos
      have a := hmr (σ i) hs
      have b := hur (σ i) hs
      set t := (σ i)⁻¹ with htdef
      set A := ‖m + (t : ℂ)‖ with hAdef
      set B := ‖u + (t : ℂ)‖ with hBdef
      have hA : 0 < A := hc.trans_le a
      have hB : 0 < B := (half_pos hc).trans_le b
      have hσc : (σ i : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
      have e1 : (1 : ℂ) + σ i * m = σ i * (m + t) := by
        rw [htdef]; push_cast; field_simp; ring
      have e2 : (1 : ℂ) + σ i * u = σ i * (u + t) := by
        rw [htdef]; push_cast; field_simp; ring
      have hnorm : ‖m * (σ i : ℂ) ^ 2 / (N * (1 + σ i * m) ^ 2 * (1 + σ i * u))‖ =
          ‖m‖ * t / (N * (A ^ 2 * B)) := by
        rw [e1, e2, norm_div, norm_mul, norm_mul, norm_mul, norm_mul, mul_pow, norm_mul,
          norm_pow, norm_pow, Complex.norm_real, Complex.norm_natCast,
          Real.norm_of_nonneg hpos.le, ← hAdef, ← hBdef, htdef]
        field_simp
      rw [hnorm, div_le_div_iff₀ (by positivity) hNr]
      have htA : t ≤ A + ‖m‖ := by
        have := norm_sub_le (m + (t : ℂ)) m
        rw [add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg ht.le] at this
        exact this
      have h1 : ‖m‖ * t / (A ^ 2 * B) ≤ ‖m‖ / (A * B) + ‖m‖ ^ 2 / (A ^ 2 * B) := by
        rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
          (by positivity)]
        have : ‖m‖ * t ≤ ‖m‖ * (A + ‖m‖) := mul_le_mul_of_nonneg_left htA (norm_nonneg _)
        have hpos' : 0 ≤ A * B * (A ^ 2 * B) := by positivity
        have e : (‖m‖ * (A ^ 2 * B) + A * B * ‖m‖ ^ 2) = ‖m‖ * (A + ‖m‖) * (A * B) := by ring
        rw [e]
        have hAB : 0 ≤ A * B := by positivity
        nlinarith [mul_le_mul_of_nonneg_right this (mul_nonneg hAB (mul_nonneg hAB hA.le))]
      have h2 : ‖m‖ / (A * B) ≤ Cm / (c * (c / 2)) :=
        div_le_div₀ hCm hm (by positivity) (mul_le_mul a b (by positivity) hA.le)
      have h3 : ‖m‖ ^ 2 / (A ^ 2 * B) ≤ Cm ^ 2 / (c ^ 2 * (c / 2)) :=
        div_le_div₀ (by positivity) (pow_le_pow_left₀ (norm_nonneg _) hm 2) (by positivity)
          (mul_le_mul (pow_le_pow_left₀ hc.le a 2) b (by positivity) (by positivity))
      have h4 : Cm / (c * (c / 2)) + Cm ^ 2 / (c ^ 2 * (c / 2)) = K := by
        rw [hK]
        field_simp
      have h5 : ‖m‖ * t / (A ^ 2 * B) ≤ K := by linarith
      rw [div_le_iff₀ (by positivity)] at h5
      nlinarith
  unfold alphaCoef
  rw [norm_neg]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => hterm i).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hphi : (M : ℝ) / N ≤ τ⁻¹ := h.phi_upper
  calc (M : ℝ) * (K / N) = (M / N) * K := by ring
    _ ≤ τ⁻¹ * K := mul_le_mul_of_nonneg_right hphi hK0
    _ = τ⁻¹ * Cm * (1 + Cm / c) * 2 / c ^ 2 := by rw [hK]; ring

/-- The stability step on `𝐃^o` for `N` satisfying the four smallness conditions, with the
two-regime bound of denominator `D`, `0 ≤ D ≤ D_max` on `𝐃^o`. -/
private lemma out_stab_core {τ τ' C₀ C₁ K₀ Dmax : ℝ} (hτ' : 0 < τ')
    (hC₀ : max (4 * (Dmax + 1)) (2 * outCeps τ τ' / outcbeta τ τ' * (Dmax + 1)) ≤ C₀)
    {N : ℕ} (hN1 : (Real.log N)⁻¹ ≤ 1 / 2) (hN2 : K₀ * (Real.log N)⁻¹ < τ')
    (hN3 : ((N : ℝ) ^ 5)⁻¹ ≤ τ⁻¹ - 1)
    (hN4 : C₀ * √((Real.log N)⁻¹) + 2 * ((N : ℝ) ^ 3)⁻¹ ≤
      min (outMz τ τ' / 2) (outcbeta τ τ' / (2 * outCalpha τ τ')))
    {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) (D : ℂ → ℝ)
    (hD0 : ∀ z ∈ outsideDomain τ τ' N σ, 0 ≤ D z)
    (hD1 : ∀ z ∈ outsideDomain τ τ' N σ, D z ≤ Dmax) :
    StableWith (fun δ z => twoRegime C₀ C₁ K₀ (kappa N σ z.re) z.im (δ z) (D z)) N σ
      (outsideDomain τ τ' N σ) := by
  obtain ⟨hN, -, -⟩ := out_facts h
  have hσ := h.nonneg
  have hτ := h.pos
  obtain ⟨-, -, hMz, hcb, hCa, hCe, hCm⟩ := out_consts hτ hτ'
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hC₀a : 4 * (Dmax + 1) ≤ C₀ := (le_max_left _ _).trans hC₀
  have hC₀b : 2 * outCeps τ τ' / outcbeta τ τ' * (Dmax + 1) ≤ C₀ :=
    (le_max_right _ _).trans hC₀
  intro δ hδ μ hμ z hz hw hprev
  set S := outsideDomain τ τ' N σ with hSdef
  have hδpos : ∀ w ∈ S, 0 < δ w := fun w hw => lt_of_lt_of_le (by positivity) (hδ.lower w hw)
  have hthick : ∀ w ∈ S, K₀ * δ w < kappa N σ w.re + w.im := by
    intro w hw'
    have hk := (m_sq_root_outside h hτ' hw').2.1
    have hw0 : 0 < w.im := hw'.1.1
    have hKδ : K₀ * δ w < τ' := by
      rcases le_or_gt 0 K₀ with hK | hK
      · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hδ.upper w hw') hK) hN2
      · have := mul_neg_of_neg_of_pos hK (hδpos w hw')
        linarith
    linarith
  have hB : ∀ w ∈ S, twoRegime C₀ C₁ K₀ (kappa N σ w.re) w.im (δ w) (D w) =
      C₀ * (δ w / (D w + √(δ w))) := by
    intro w hw'
    simp only [twoRegime, hthick w hw', ↓reduceIte]
  change ‖resolventTransform μ z - mFun N σ z‖ ≤
    twoRegime C₀ C₁ K₀ (kappa N σ z.re) z.im (δ z) (D z)
  rw [hB z hz]
  set u := resolventTransform μ z with hu_def
  have hη : 0 < z.im := hz.1.1
  have hδ0 := hδpos z hz
  have hδh : δ z ≤ 1 / 2 := (hδ.upper z hz).trans hN1
  have hsδ : √(δ z) ≤ 1 := Real.sqrt_le_one.2 (by linarith)
  have hsδ0 := Real.sqrt_pos.2 hδ0
  have hDz0 := hD0 z hz
  have hDz1 := hD1 z hz
  have hC0pos : 0 < C₀ := by linarith
  have hden : 0 < D z + √(δ z) := by positivity
  have hden1 : D z + √(δ z) ≤ Dmax + 1 := by linarith
  have hfinal : ∀ K : ℝ, 0 ≤ K → K * (Dmax + 1) ≤ C₀ →
      K * δ z ≤ C₀ * (δ z / (D z + √(δ z))) := by
    intro K hK0 hK
    rw [← mul_div_assoc, le_div_iff₀ hden]
    have h1 : K * δ z * (D z + √(δ z)) ≤ K * δ z * (Dmax + 1) :=
      mul_le_mul_of_nonneg_left hden1 (by positivity)
    have h2 : K * (Dmax + 1) * δ z ≤ C₀ * δ z := mul_le_mul_of_nonneg_right hK hδ0.le
    nlinarith
  have hu : 0 < u.im := im_resolventTransform_pos μ hη
  by_cases hη1 : 1 ≤ z.im
  · have hw' : ‖fC N σ u - z‖ ≤ 1 / 2 := hw.trans hδh
    have := norm_sub_mFun_le_of_im_ge hσ hN one_pos hη1 hu hw'
    rw [one_pow, div_one] at this
    calc ‖u - mFun N σ z‖ ≤ 2 * ‖fC N σ u - z‖ := this
      _ ≤ 2 * δ z := by linarith
      _ ≤ C₀ * (δ z / (D z + √(δ z))) := hfinal 2 (by norm_num) (by linarith)
  · push Not at hη1
    have hS' := spectralDomain_outsideDomain τ τ' N σ
    have hz'S : shiftUp N z ∈ S := shiftUp_mem hS' hz (by linarith)
    have hp := hprev hη1
    beta_reduce at hp
    rw [hB _ hz'S] at hp
    set z' := shiftUp N z with hz'def
    have hz'im : z'.im = z.im + ((N : ℝ) ^ 5)⁻¹ := by
      rw [hz'def, shiftUp, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      ring
    have hz'0 : 0 < z'.im := hz'S.1.1
    have hp' : ‖resolventTransform μ z' - mFun N σ z'‖ ≤ C₀ * √((Real.log N)⁻¹) := by
      refine hp.trans (mul_le_mul_of_nonneg_left ?_ hC0pos.le)
      exact (out_quot_le_sqrt (hδpos z' hz'S).le (hD0 z' hz'S)).trans
        (Real.sqrt_le_sqrt (hδ.upper z' hz'S))
    have hηN : (N : ℝ)⁻¹ ≤ z.im := by
      have := Real.rpow_le_rpow_of_exponent_le hNr (show (-1 : ℝ) ≤ -1 + τ by linarith)
      rw [Real.rpow_neg_one] at this
      exact this.trans hz.1.2.2.2.1
    have hη' : (N : ℝ)⁻¹ ≤ z'.im := by
      rw [hz'im]
      have : 0 ≤ ((N : ℝ) ^ 5)⁻¹ := by positivity
      linarith
    have hdrift : ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν],
        ‖resolventTransform ν z - resolventTransform ν z'‖ ≤ ((N : ℝ) ^ 3)⁻¹ := by
      intro ν _
      refine (norm_resolventTransform_sub_le ν hη hz'0).trans ?_
      have hzz : ‖z - z'‖ = ((N : ℝ) ^ 5)⁻¹ := by
        rw [hz'def, shiftUp, sub_add_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one,
          Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      rw [hzz, div_le_iff₀ (mul_pos hη hz'0)]
      have hN0 : (0 : ℝ) < N := by linarith
      calc ((N : ℝ) ^ 5)⁻¹ = ((N : ℝ) ^ 3)⁻¹ * ((N : ℝ)⁻¹ * (N : ℝ)⁻¹) := by
            field_simp
        _ ≤ ((N : ℝ) ^ 3)⁻¹ * (z.im * z'.im) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hηN hη' (by positivity) hη.le)
              (by positivity)
    have hx : ‖u - mFun N σ z‖ ≤
        min (outMz τ τ' / 2) (outcbeta τ τ' / (2 * outCalpha τ τ')) := by
      have h1 := hdrift μ
      have := isProbabilityMeasure_varrho N σ hσ hN
      have h2 := hdrift (varrho N σ)
      rw [resolventTransform_varrho N σ hσ hN hη, resolventTransform_varrho N σ hσ hN hz'0]
        at h2
      have e : u - mFun N σ z = (u - resolventTransform μ z') +
          (resolventTransform μ z' - mFun N σ z') + (mFun N σ z' - mFun N σ z) := by ring
      rw [e]
      refine norm_add₃_le.trans ?_
      rw [norm_sub_rev (mFun N σ z')]
      linarith
    have hxm : ‖u - mFun N σ z‖ ≤ outMz τ τ' / 2 := hx.trans (min_le_left _ _)
    have hxb : ‖u - mFun N σ z‖ ≤ outcbeta τ τ' / (2 * outCalpha τ τ') :=
      hx.trans (min_le_right _ _)
    obtain ⟨-, hmC, -⟩ := gen_prop_m_specDomain h hz.1
    have hmreg := mz_reg_outside h hτ' hz
    have hureg : ∀ s ∈ posVals σ, outMz τ τ' / 2 ≤ ‖u + ((s⁻¹ : ℝ) : ℂ)‖ := by
      intro s hs
      have h1 := hmreg s hs
      have e : mFun N σ z + ((s⁻¹ : ℝ) : ℂ) = (u + ((s⁻¹ : ℝ) : ℂ)) + (mFun N σ z - u) := by
        ring
      have h2 := norm_add_le (u + ((s⁻¹ : ℝ) : ℂ)) (mFun N σ z - u)
      rw [← e, norm_sub_rev] at h2
      linarith
    obtain ⟨hmim, hfm⟩ := mFun_spec N σ hσ hη
    have hu0 : u ≠ 0 := fun h0 => by rw [h0, Complex.zero_im] at hu; exact lt_irrefl _ hu
    have hm0 : mFun N σ z ≠ 0 := fun h0 => by
      rw [h0, Complex.zero_im] at hmim; exact lt_irrefl _ hmim
    have hq := quadr_edge N σ hu0 hm0 (out_one_add_ne hσ hu) (out_one_add_ne hσ hmim)
    rw [hfm] at hq
    have hβ := betaCoef_outside_ge h hτ' hz
    have hβ0 : betaCoef N σ (mFun N σ z) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hβ
      linarith
    have hα : ‖alphaCoef N σ u (mFun N σ z)‖ ≤ outCalpha τ τ' :=
      out_alpha_le h hMz hmC hmreg hureg
    have hroot := root_dichotomy hα hβ0 hq.symm (by
      have h1 := mul_le_mul_of_nonneg_left hxb (by positivity : 0 ≤ 2 * outCalpha τ τ')
      have e : 2 * outCalpha τ τ' * (outcbeta τ τ' / (2 * outCalpha τ τ')) = outcbeta τ τ' := by
        field_simp
      rw [e] at h1
      linarith)
    have hun : ‖u‖ ≤ mBoundConst τ + outMz τ τ' / 2 := by
      have e : mFun N σ z + (u - mFun N σ z) = u := by ring
      have := norm_add_le (mFun N σ z) (u - mFun N σ z)
      rw [e] at this
      linarith
    have hε : ‖u * mFun N σ z * (fC N σ u - z)‖ ≤ outCeps τ τ' * δ z := by
      rw [norm_mul, norm_mul]
      unfold outCeps
      exact mul_le_mul (mul_le_mul hun hmC (norm_nonneg _) (by positivity)) hw (norm_nonneg _)
        (by positivity)
    calc ‖u - mFun N σ z‖
        ≤ 2 * ‖u * mFun N σ z * (fC N σ u - z)‖ / ‖betaCoef N σ (mFun N σ z)‖ := hroot
      _ ≤ 2 * (outCeps τ τ' * δ z) / outcbeta τ τ' :=
          div_le_div₀ (by positivity) (by linarith) hcb hβ
      _ = 2 * outCeps τ τ' / outcbeta τ τ' * δ z := by ring
      _ ≤ C₀ * (δ z / (D z + √(δ z))) := hfinal _ (by positivity) hC₀b

/-- The threshold `N₀`: `(log N)⁻¹ ≤ 1/2`, `K₀ (log N)⁻¹ < τ'`, `N⁻⁵ ≤ τ⁻¹ - 1` and
`C₀ (log N)^{-1/2} + 2N⁻³ ≤ θ` for `N ≥ N₀`. -/
private lemma out_N₀ {τ τ' C₀ K₀ θ : ℝ} (hτ' : 0 < τ') (hτ : 0 < τ) (hτ1 : τ < 1)
    (hθ : 0 < θ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, (Real.log N)⁻¹ ≤ 1 / 2 ∧ K₀ * (Real.log N)⁻¹ < τ' ∧
      ((N : ℝ) ^ 5)⁻¹ ≤ τ⁻¹ - 1 ∧ C₀ * √((Real.log N)⁻¹) + 2 * ((N : ℝ) ^ 3)⁻¹ ≤ θ := by
  have hlog : Tendsto (fun N : ℕ => (Real.log N)⁻¹) atTop (𝓝 0) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  have hpow : ∀ k : ℕ, k ≠ 0 → Tendsto (fun N : ℕ => ((N : ℝ) ^ k)⁻¹) atTop (𝓝 0) :=
    fun k hk => ((tendsto_pow_atTop hk).comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  have e1 : ∀ᶠ N : ℕ in atTop, (Real.log N)⁻¹ < 1 / 2 :=
    hlog.eventually_lt_const (by norm_num)
  have e2 : ∀ᶠ N : ℕ in atTop, K₀ * (Real.log N)⁻¹ < τ' := by
    have : Tendsto (fun N : ℕ => K₀ * (Real.log N)⁻¹) atTop (𝓝 0) := by
      simpa using hlog.const_mul K₀
    exact this.eventually_lt_const hτ'
  have e3 : ∀ᶠ N : ℕ in atTop, ((N : ℝ) ^ 5)⁻¹ < τ⁻¹ - 1 := by
    have : 1 < τ⁻¹ := (one_lt_inv₀ hτ).2 hτ1
    exact (hpow 5 (by norm_num)).eventually_lt_const (by linarith)
  have e4 : ∀ᶠ N : ℕ in atTop, C₀ * √((Real.log N)⁻¹) + 2 * ((N : ℝ) ^ 3)⁻¹ < θ := by
    have hs : Tendsto (fun N : ℕ => √((Real.log N)⁻¹)) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp hlog
      rwa [Real.sqrt_zero] at this
    have : Tendsto (fun N : ℕ => C₀ * √((Real.log N)⁻¹) + 2 * ((N : ℝ) ^ 3)⁻¹) atTop
        (𝓝 0) := by
      simpa using (hs.const_mul C₀).add ((hpow 3 (by norm_num)).const_mul 2)
    exact this.eventually_lt_const hθ
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (e1.and (e2.and (e3.and e4)))
  exact ⟨N₀, fun N hN => by
    obtain ⟨a, b, c, d⟩ := hN₀ N hN
    exact ⟨a.le, b, c.le, d.le⟩⟩

/-- Lemma A.8, strong stability on `𝐃^o` (every `C₁`, every `K₀`). -/
theorem stab_outside {τ τ' C₀ C₁ K₀ : ℝ} (hτ' : 0 < τ') (hC₀ : outC0min τ τ' ≤ C₀) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {M : ℕ} (σ : Fin M → ℝ),
      DensityAssumptions τ N σ → StronglyStableOn C₀ C₁ K₀ N σ (outsideDomain τ τ' N σ) := by
  by_cases hτ : 0 < τ ∧ τ < 1
  · obtain ⟨-, -, hMz, hcb, hCa, -, -⟩ := out_consts hτ.1 hτ'
    obtain ⟨N₀, hN₀⟩ := out_N₀ (C₀ := C₀) (K₀ := K₀) hτ' hτ.1 hτ.2
      (lt_min (half_pos hMz) (div_pos hcb (by positivity)) :
        0 < min (outMz τ τ' / 2) (outcbeta τ τ' / (2 * outCalpha τ τ')))
    refine ⟨N₀, fun N hN M σ h => ?_⟩
    obtain ⟨h1, h2, h3, h4⟩ := hN₀ N hN
    exact out_stab_core hτ' hC₀ h1 h2 h3 h4 h (fun z => √(kappa N σ z.re + z.im))
      (fun _ _ => Real.sqrt_nonneg _)
      (fun z hz => Real.sqrt_le_sqrt (add_le_add (kappa_le h hz.1.2.2.1) hz.1.2.2.2.2))
  · exact ⟨0, fun N _ M σ h => absurd ⟨h.pos, (out_facts h).2.1⟩ hτ⟩

/-- Lemma A.8, stability (Definition 5.4) on `𝐃^o`. -/
theorem stab_outside_weak {τ τ' C₀ C₁ K₀ : ℝ} (hτ' : 0 < τ') (hC₀ : outC0wmin τ τ' ≤ C₀) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {M : ℕ} (σ : Fin M → ℝ),
      DensityAssumptions τ N σ → StableOn C₀ C₁ K₀ N σ (outsideDomain τ τ' N σ) := by
  by_cases hτ : 0 < τ ∧ τ < 1
  · obtain ⟨-, -, hMz, hcb, hCa, -, -⟩ := out_consts hτ.1 hτ'
    obtain ⟨N₀, hN₀⟩ := out_N₀ (C₀ := C₀) (K₀ := K₀) hτ' hτ.1 hτ.2
      (lt_min (half_pos hMz) (div_pos hcb (by positivity)) :
        0 < min (outMz τ τ' / 2) (outcbeta τ τ' / (2 * outCalpha τ τ')))
    refine ⟨N₀, fun N hN M σ h => ?_⟩
    obtain ⟨h1, h2, h3, h4⟩ := hN₀ N hN
    exact out_stab_core hτ' hC₀ h1 h2 h3 h4 h (fun z => (mFun N σ z).im)
      (fun z hz => (mFun_spec N σ h.nonneg hz.1.1).1.le)
      (fun z hz => (Complex.im_le_norm _).trans (gen_prop_m_specDomain h hz.1).2.1)
  · exact ⟨0, fun N _ M σ h => absurd ⟨h.pos, (out_facts h).2.1⟩ hτ⟩

/-! ## (im_m_asymp) -/

def imAsympLower (τ : ℝ) : ℝ := min (sqLower (τ / 2)) (outImLower τ * √(edgeTau' (τ / 2)))
def imAsympUpper (τ : ℝ) : ℝ :=
  max (sqUpper (τ / 2)) (√(kappaMax τ + τ⁻¹) / edgeTau' (τ / 2) ^ 2)

/-- `0 < τ'(t) ≤ t` for `0 < t ≤ 1`. -/
private lemma out_edgeTau' {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    0 < edgeTau' t ∧ edgeTau' t ≤ t := by
  have hs := Real.sqrt_pos.2 ht
  have hcx : 0 < edgecx t := by unfold edgecx; positivity
  have hCx : 0 < edgeCx t := by unfold edgeCx; positivity
  have h2 : 0 < edgec2 t := by unfold edgec2; positivity
  have h3 : 0 < edgeC3 t := by unfold edgeC3; positivity
  have h0 : 0 < edgeRho0 t := by unfold edgeRho0; positivity
  have h1 : 0 < edgeRho1 t := by unfold edgeRho1; positivity
  have hc2 : edgec2 t ≤ t ^ 3 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hρ : edgeRho1 t ≤ t / 2 := by
    refine (min_le_left _ _).trans ?_
    unfold edgeRho0
    linarith [min_le_right (edgecx t) t]
  have hsq : edgeRho1 t ^ 2 ≤ (t / 2) ^ 2 := pow_le_pow_left₀ h1.le hρ 2
  have hmul : edgec2 t * edgeRho1 t ^ 2 ≤ t ^ 3 / 4 * (t / 2) ^ 2 :=
    mul_le_mul hc2 hsq (sq_nonneg _) (by positivity)
  have ht4 : t ^ 4 ≤ 1 := pow_le_one₀ ht.le ht1
  refine ⟨by unfold edgeTau' edgeTau0; positivity, ?_⟩
  unfold edgeTau' edgeTau0
  nlinarith

/-- (im_m_asymp): `Im m ≍ η (κ + η)^{-1/2}` for `E ∈ [τ, τ⁻¹] ∖ supp ϱ`, when every edge
`a_k ≥ τ/2` is regular with parameter `τ/2`. -/
theorem im_m_asymp {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ)
    (hreg : ∀ k, 1 ≤ k → k ≤ 2 * numBands N σ → τ / 2 ≤ edgeVal N σ k →
      RegularEdge (τ / 2) N σ k)
    {z : ℂ} (hz : z ∈ specDomain τ N) (hE : z.re ∈ Set.Icc τ τ⁻¹)
    (hout : z.re ∉ (varrho N σ).support) :
    imAsympLower τ * (z.im / √(kappa N σ z.re + z.im)) ≤ (mFun N σ z).im ∧
      (mFun N σ z).im ≤ imAsympUpper τ * (z.im / √(kappa N σ z.re + z.im)) := by
  obtain ⟨hN, hτ1, hS⟩ := out_facts h
  have hσ := h.nonneg
  have hτ := h.pos
  have := isProbabilityMeasure_varrho N σ hσ hN
  obtain ⟨hte0, hte⟩ := out_edgeTau' (t := τ / 2) (by positivity) (by linarith)
  set te := edgeTau' (τ / 2) with htedef
  have hη : 0 < z.im := hz.1
  have hq0 : 0 ≤ z.im / √(kappa N σ z.re + z.im) := by positivity
  have hL1 : imAsympLower τ ≤ sqLower (τ / 2) := min_le_left _ _
  have hL2 : imAsympLower τ ≤ outImLower τ * √te := min_le_right _ _
  have hU1 : sqUpper (τ / 2) ≤ imAsympUpper τ := le_max_left _ _
  have hU2 : √(kappaMax τ + τ⁻¹) / te ^ 2 ≤ imAsympUpper τ := le_max_right _ _
  by_cases hfar : te ≤ Metric.infDist z.re (varrho N σ).support
  · obtain ⟨-, -, l, u⟩ := m_sq_root_outside h hte0 ⟨hz, hfar⟩
    exact ⟨(mul_le_mul_of_nonneg_right hL2 hq0).trans l,
      u.trans (mul_le_mul_of_nonneg_right hU2 hq0)⟩
  · push Not at hfar
    have hne : (varrho N σ).support.Nonempty :=
      Measure.nonempty_support (IsProbabilityMeasure.ne_zero _)
    obtain ⟨y, hy, hyd⟩ := (Metric.infDist_lt_iff hne).1 hfar
    rw [Real.dist_eq] at hyd
    obtain ⟨hyd1, hyd2⟩ := abs_lt.1 hyd
    obtain ⟨hE1, hE2⟩ := hE
    have hy0 : 0 < y := by linarith
    have hE0 : 0 < z.re := by linarith
    obtain ⟨j, hj1, hj2, hyj⟩ := (mem_support_varrho_iff N σ hσ hN hS hy0).1 hy
    have hEnot : z.re ∉ Set.Icc (edgeVal N σ (2 * j)) (edgeVal N σ (2 * j - 1)) := fun hm =>
      hout ((mem_support_varrho_iff N σ hσ hN hS hE0).2 ⟨j, hj1, hj2, hm⟩)
    obtain ⟨l, hl1, hl2, hla, hEl⟩ : ∃ l, 1 ≤ l ∧ l ≤ 2 * numBands N σ ∧
        τ / 2 ≤ edgeVal N σ l ∧ |z.re - edgeVal N σ l| < te := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hEnot
      rcases hEnot with hlt | hgt
      · refine ⟨2 * j, by omega, by omega, by linarith, ?_⟩
        rw [abs_of_neg (by linarith)]
        linarith [hyj.1]
      · refine ⟨2 * j - 1, by omega, by omega, by linarith [hyj.2], ?_⟩
        rw [abs_of_pos (by linarith)]
        linarith [hyj.2]
    have hreg' := hreg l hl1 hl2 hla
    have h2 : DensityAssumptions (τ / 2) N σ := h.mono (by positivity) (by linarith)
    obtain ⟨hEl1, hEl2⟩ := abs_lt.1 hEl
    have hzD : z ∈ edgeDomain (τ / 2) te N σ l :=
      ⟨specDomain_subset (by positivity) (by linarith) hN hz, by linarith, by linarith⟩
    obtain ⟨l', u'⟩ := (m_sq_root_edge h2 hreg' le_rfl hzD).2 hout
    exact ⟨(mul_le_mul_of_nonneg_right hL1 hq0).trans l',
      u'.trans (mul_le_mul_of_nonneg_right hU1 hq0)⟩

/-! ## Instances

Marchenko–Pastur: `M = 100`, `N = 200`, `σ = 1` (`φ = 1/2`), `τ = 1/20`, `τ' = 1/2`.
* `z = 7/2 + i/100`: `200^{-19/20} ≤ 1/100`, so `z ∈ 𝐃(1/20, 200)`; the bound
  `dist(7/2, supp ϱ) ≥ 1/2` (`supp ϱ ⊆ {0} ∪ [(1 - 1/√2)², (1 + 1/√2)²]`, `(1 + 1/√2)² < 3`)
  is a hypothesis of these examples, and so is the regularity of the two edges at `τ/2 = 1/40`
  for (im_m_asymp).
* `z = -1 + i/100`: `supp ϱ ⊆ [0, a_1]` gives `dist(-1, supp ϱ) ≥ 1`, so `z ∈ 𝐃^o(1/20, 1/2)`
  with no further hypothesis.
-/

local notation "σP" => (fun _ : Fin 100 => (1 : ℝ))
local notation "zP" => (⟨7 / 2, 1 / 100⟩ : ℂ)
local notation "zN" => (⟨-1, 1 / 100⟩ : ℂ)

/-- The constants at `τ = 1/20`, `τ' = 1/2` are positive. -/
example : 0 < outImLower (1 / 20) ∧ 0 < outcr (1 / 20) (1 / 2) ∧ 0 < outMz (1 / 20) (1 / 2) ∧
    0 < outcbeta (1 / 20) (1 / 2) ∧ 0 < outCalpha (1 / 20) (1 / 2) ∧
      0 < outCeps (1 / 20) (1 / 2) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := out_consts (τ := 1 / 20) (τ' := 1 / 2) (by norm_num)
    (by norm_num)
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- Strong stability on `𝐃^o(1/20, 1/2)` with `C₀ = outC0min`, `C₁ = 2C₀`, `K₀ = 1`. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {M : ℕ} (σ : Fin M → ℝ),
    DensityAssumptions (1 / 20) N σ →
      StronglyStableOn (outC0min (1 / 20) (1 / 2)) (2 * outC0min (1 / 20) (1 / 2)) 1 N σ
        (outsideDomain (1 / 20) (1 / 2) N σ) :=
  stab_outside (by norm_num) le_rfl

/-- Stability (Definition 5.4) on `𝐃^o(1/20, 1/2)` with `C₀ = outC0wmin`, `C₁ = 2C₀`,
`K₀ = 1`. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {M : ℕ} (σ : Fin M → ℝ),
    DensityAssumptions (1 / 20) N σ →
      StableOn (outC0wmin (1 / 20) (1 / 2)) (2 * outC0wmin (1 / 20) (1 / 2)) 1 N σ
        (outsideDomain (1 / 20) (1 / 2) N σ) :=
  stab_outside_weak (by norm_num) le_rfl

end Anisotropic
