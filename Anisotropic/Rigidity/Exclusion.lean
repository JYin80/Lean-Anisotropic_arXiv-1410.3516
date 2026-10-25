import Anisotropic.Averaged.Defs
import Anisotropic.Density.GenProp
import Anisotropic.Density.SelfConsistent
import Anisotropic.Density.Stability.Domains
import Anisotropic.Density.Varrho
import Anisotropic.Entrywise.Defs
import Anisotropic.Entrywise.DiagModel
import Anisotropic.Framework.Model
import Anisotropic.Rigidity.Defs

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # The deterministic part of Lemma 10.1: the empirical Stieltjes transform, the gap domain, the grid, (Phi_cond) for `(κ+η)^{−1/2}Ψ²` -/

/-- The Stieltjes transform `K⁻¹ ∑_j (λ_j − z)⁻¹` of the empirical measure of `λ`. -/
def empStieltjes {K : ℕ} (lam : Fin K → ℝ) (z : ℂ) : ℂ :=
  (K : ℂ)⁻¹ * ∑ j, ((lam j : ℂ) - z)⁻¹

private lemma resolventTransform_empMeasure {K : ℕ} (lam : Fin K → ℝ) (z : ℂ) :
    resolventTransform (empMeasure lam) z = empStieltjes lam z := by
  rw [resolventTransform_apply, empMeasure, integral_smul_measure, integral_finsetSum_measure]
  · simp only [integral_dirac, resolvent, Ring.inverse_eq_inv', Complex.coe_algebraMap]
    rw [Complex.real_smul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    simp [empStieltjes]
  · intro k _
    exact integrable_dirac (by simp [resolvent, Ring.inverse_eq_inv'])

/-- (def_m_N): `m_N` is the Stieltjes transform of the eigenvalues of `Q_N = XᵀΣX`. -/
theorem mN_eq_empStieltjes {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) :
    mN Sig Xm z = empStieltjes (specOf (QN Sig Xm)) z := by
  rw [mN_eq_resolventTransform hSig Xm hz, ← resolventTransform_empMeasure]
  rfl

/-- An eigenvalue in `[E − η, E + η]` forces `Im s(E + iη) ≥ (2Kη)⁻¹`. -/
theorem im_empStieltjes_ge {K : ℕ} (lam : Fin K → ℝ) {z : ℂ} (hz : 0 < z.im) (j : Fin K)
    (hj : |lam j - z.re| ≤ z.im) : 1 / (2 * K * z.im) ≤ (empStieltjes lam z).im := by
  have hterm : ∀ i, (((lam i : ℂ) - z)⁻¹).im = z.im / ((lam i - z.re) ^ 2 + z.im ^ 2) := by
    intro i
    rw [Complex.inv_im, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, zero_sub,
      neg_neg]
    ring_nf
  have hK : (0 : ℝ) < K := by
    have := j.pos
    exact_mod_cast this
  have hnn : ∀ i, 0 ≤ (((lam i : ℂ) - z)⁻¹).im := fun i => by
    rw [hterm]; positivity
  have hsum : z.im / ((lam j - z.re) ^ 2 + z.im ^ 2) ≤ ∑ i, (((lam i : ℂ) - z)⁻¹).im := by
    rw [← hterm]
    exact Finset.single_le_sum (f := fun i => (((lam i : ℂ) - z)⁻¹).im) (fun i _ => hnn i)
      (Finset.mem_univ j)
  have hj2 : (lam j - z.re) ^ 2 ≤ z.im ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hj 2
  have hlow : 1 / (2 * z.im) ≤ z.im / ((lam j - z.re) ^ 2 + z.im ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have him : (empStieltjes lam z).im = (K : ℝ)⁻¹ * ∑ i, (((lam i : ℂ) - z)⁻¹).im := by
    unfold empStieltjes
    rw [Complex.mul_im, Complex.im_sum]
    simp
  rw [him]
  calc 1 / (2 * K * z.im) = (K : ℝ)⁻¹ * (1 / (2 * z.im)) := by field_simp
    _ ≤ (K : ℝ)⁻¹ * ∑ i, (((lam i : ℂ) - z)⁻¹).im :=
        mul_le_mul_of_nonneg_left (hlow.trans hsum) (by positivity)

/-- The spectral domain of Lemma 10.1: `z ∈ 𝐃(τ₀, N)`, `E ∉ supp ϱ`, `κ ≥ N^{−2/3+ε}/2` and
`η ≥ N^{−1/2−ε/4} κ^{1/4}`. -/
def gapDomain (τ₀ ε : ℝ) (N : ℕ) (σ : Fin M → ℝ) : Set ℂ :=
  {z | z ∈ specDomain τ₀ N ∧ z.re ∉ (varrho N σ).support ∧
    (N : ℝ) ^ (-2 / 3 + ε) / 2 ≤ kappa N σ z.re ∧
    (N : ℝ) ^ (-1 / 2 - ε / 4) * kappa N σ z.re ^ (1 / 4 : ℝ) ≤ z.im}

/-- The domain of Lemma 10.1 is a spectral domain (Definition 5.3). -/
theorem spectralDomain_gapDomain (τ₀ ε : ℝ) (N : ℕ) (σ : Fin M → ℝ) :
    SpectralDomain τ₀ N (gapDomain τ₀ ε N σ) := by
  refine ⟨fun z hz => hz.1, fun z hz w hw hre hle => ⟨hw, ?_, ?_, ?_⟩⟩
  · rw [hre]; exact hz.2.1
  · rw [hre]; exact hz.2.2.1
  · rw [hre]; exact hz.2.2.2.trans hle

/-- `N > 0` and some `σ i` is positive under (phi_bounded), (bound_Sigma), (Sigma_gap). -/
private lemma excl_facts {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) :
    0 < N ∧ (posVals σ).Nonempty := by
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
  refine ⟨hN, ?_⟩
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  refine hfull fun i => ⟨h.nonneg i, ?_⟩
  by_contra hi
  have hpos : 0 < σ i := hτ.trans (not_le.1 hi)
  have hmem : σ i ∈ posVals σ := by
    simp only [posVals, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨i, rfl⟩, hpos⟩
  rw [hne] at hmem
  simp at hmem

/-- Every edge `a_l`, `1 ≤ l ≤ 2p`, lies in `supp ϱ`. -/
private lemma excl_edge_mem_support {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ}
    (h : DensityAssumptions τ N σ) {l : ℕ} (hl1 : 1 ≤ l) (hl2 : l ≤ 2 * numBands N σ) :
    edgeVal N σ l ∈ (varrho N σ).support := by
  obtain ⟨hN, hS⟩ := excl_facts h
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

/-- `κ(E) ≥ dist(E, supp ϱ)`: the edges `a_l` lie in the support. -/
private lemma excl_infDist_le_kappa {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ}
    (h : DensityAssumptions τ N σ) (E : ℝ) :
    Metric.infDist E (varrho N σ).support ≤ kappa N σ E := by
  obtain ⟨hN, hS⟩ := excl_facts h
  have hp := (card_innerCrit N σ h.nonneg hN hS).2
  have hmem : (1 : ℕ) ∈ Finset.Icc 1 (2 * numBands N σ) := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
  have : Nonempty (Finset.Icc 1 (2 * numBands N σ)) := ⟨⟨1, hmem⟩⟩
  refine le_ciInf fun l => ?_
  have hl := Finset.mem_Icc.1 l.2
  have := Metric.infDist_le_dist_of_mem (x := E) (excl_edge_mem_support h hl.1 hl.2)
  rwa [Real.dist_eq] at this

/-- The grid of Lemma 10.1 (step `N⁻¹`): if `dist(E, supp ϱ) ≥ N^{−2/3+ε}`, the grid point
`E' = ⌊EN⌋/N` lies outside `supp ϱ`, has `κ(E') ≥ N^{−2/3+ε}/2`, and `|E − E'| ≤ η(E')` with
`η(E') = N^{−1/2−ε/4} κ(E')^{1/4}`. -/
theorem gap_grid {τ ε E : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) (hε : 0 < ε)
    (hε2 : ε < 2 / 3) (hNbig : 2 / (N : ℝ) ≤ (N : ℝ) ^ (-2 / 3 + ε))
    (hE : (N : ℝ) ^ (-2 / 3 + ε) ≤ Metric.infDist E (varrho N σ).support) :
    ((⌊E * N⌋ : ℝ) / N) ∉ (varrho N σ).support ∧
      (N : ℝ) ^ (-2 / 3 + ε) / 2 ≤ kappa N σ ((⌊E * N⌋ : ℝ) / N) ∧
      |E - (⌊E * N⌋ : ℝ) / N| ≤
        (N : ℝ) ^ (-1 / 2 - ε / 4) * kappa N σ ((⌊E * N⌋ : ℝ) / N) ^ (1 / 4 : ℝ) := by
  obtain ⟨hN, -⟩ := excl_facts h
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set a : ℝ := (N : ℝ) ^ (-2 / 3 + ε) with ha
  have ha0 : 0 < a := Real.rpow_pos_of_pos hn _
  have ha1 : a ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
  have hN2 : (2 : ℝ) ≤ N := by
    have h1 : 2 / (N : ℝ) ≤ 1 := hNbig.trans ha1
    rw [div_le_one hn] at h1
    exact h1
  set E' : ℝ := (⌊E * N⌋ : ℝ) / N with hE'
  have hfl1 : (⌊E * N⌋ : ℝ) ≤ E * N := Int.floor_le _
  have hfl2 : E * N < (⌊E * N⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hd1 : 0 ≤ E - E' := by
    rw [hE', sub_nonneg, div_le_iff₀ hn]; exact hfl1
  have hd2 : E - E' < 1 / N := by
    rw [hE', lt_div_iff₀ hn]
    have : (E - (⌊E * N⌋ : ℝ) / N) * N = E * N - ⌊E * N⌋ := by field_simp
    rw [this]; linarith
  have hNinv : 1 / (N : ℝ) ≤ a / 2 := by
    have : 2 / (N : ℝ) = 2 * (1 / N) := by ring
    linarith
  have hdist : dist E E' = E - E' := by
    rw [Real.dist_eq, abs_of_nonneg hd1]
  have hinf : a / 2 ≤ Metric.infDist E' (varrho N σ).support := by
    have := Metric.infDist_le_infDist_add_dist (x := E) (y := E') (s := (varrho N σ).support)
    rw [hdist] at this
    linarith
  have hk : a / 2 ≤ kappa N σ E' := hinf.trans (excl_infDist_le_kappa h E')
  refine ⟨fun hmem => ?_, hk, ?_⟩
  · rw [Metric.infDist_zero_of_mem hmem] at hinf
    linarith
  · rw [abs_of_nonneg hd1]
    refine hd2.le.trans ?_
    have h1 : (a / 2) ^ (1 / 4 : ℝ) ≤ kappa N σ E' ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hk (by norm_num)
    have h2 : (N : ℝ) ^ (-1 / 2 - ε / 4) * (a / 2) ^ (1 / 4 : ℝ) =
        (N : ℝ) ^ (-2 / 3 : ℝ) / 2 ^ (1 / 4 : ℝ) := by
      rw [Real.div_rpow ha0.le (by norm_num), ha, ← Real.rpow_mul hn.le, mul_div_assoc',
        ← mul_div_assoc, ← Real.rpow_add hn]
      congr 2
      ring
    have h3 : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) :=
      calc (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 ^ (1 / 3 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ ≤ (N : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by norm_num) hN2 (by norm_num)
    have h4 : 1 / (N : ℝ) = (N : ℝ) ^ (-2 / 3 : ℝ) * (N : ℝ) ^ (-1 / 3 : ℝ) := by
      rw [← Real.rpow_add hn, show (-2 / 3 : ℝ) + -1 / 3 = -1 by norm_num, Real.rpow_neg_one]
      simp
    have h5 : (N : ℝ) ^ (-1 / 3 : ℝ) ≤ 1 / (2 : ℝ) ^ (1 / 4 : ℝ) := by
      rw [le_div_iff₀ (by positivity)]
      have : (N : ℝ) ^ (-1 / 3 : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ) = 1 := by
        rw [← Real.rpow_add hn]; norm_num
      calc (N : ℝ) ^ (-1 / 3 : ℝ) * (2 : ℝ) ^ (1 / 4 : ℝ)
          ≤ (N : ℝ) ^ (-1 / 3 : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = 1 := this
    calc 1 / (N : ℝ) = (N : ℝ) ^ (-2 / 3 : ℝ) * (N : ℝ) ^ (-1 / 3 : ℝ) := h4
      _ ≤ (N : ℝ) ^ (-2 / 3 : ℝ) * (1 / (2 : ℝ) ^ (1 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
      _ = (N : ℝ) ^ (-1 / 2 - ε / 4) * (a / 2) ^ (1 / 4 : ℝ) := by rw [h2]; ring
      _ ≤ (N : ℝ) ^ (-1 / 2 - ε / 4) * kappa N σ E' ^ (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)

/-! ### Estimates for `gapPhi` -/

/-- `(κ + y)^{−1/2} Ψ²` is at most `2C/(n(κ + y)) + 2/(√(κ + y)(ny)²)` if `μ ≤ C y/√(κ + y)`. -/
private lemma excl_phi_real {n y κ μ C : ℝ} (hn : 0 < n) (hy : 0 < y) (hκ : 0 ≤ κ) (hC : 0 ≤ C)
    (hμ : μ ≤ C * (y / √(κ + y))) :
    (κ + y) ^ (-(1 / 2 : ℝ)) * (√(μ / (n * y)) + 1 / (n * y)) ^ 2 ≤
      2 * C / (n * (κ + y)) + 2 / (√(κ + y) * (n * y) ^ 2) := by
  have hky : 0 < κ + y := by linarith
  set S := √(κ + y) with hS
  have hS0 : 0 < S := Real.sqrt_pos.2 hky
  have hS2 : S ^ 2 = κ + y := Real.sq_sqrt hky.le
  have hrp : (κ + y) ^ (-(1 / 2 : ℝ)) = S⁻¹ := by
    rw [Real.rpow_neg hky.le, ← Real.sqrt_eq_rpow]
  have hA : √(μ / (n * y)) ^ 2 ≤ C / (n * S) := by
    by_cases h0 : 0 ≤ μ / (n * y)
    · rw [Real.sq_sqrt h0]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : μ * S ≤ C * y := by
        have := mul_le_mul_of_nonneg_right hμ hS0.le
        calc μ * S ≤ C * (y / S) * S := this
          _ = C * y := by field_simp
      nlinarith [this, hn]
    · rw [Real.sqrt_eq_zero_of_nonpos (not_le.1 h0).le, zero_pow two_ne_zero]
      positivity
  have hB : (1 / (n * y)) ^ 2 = 1 / (n * y) ^ 2 := by rw [one_div, one_div, inv_pow]
  have hsq : (√(μ / (n * y)) + 1 / (n * y)) ^ 2 ≤
      2 * (C / (n * S)) + 2 * (1 / (n * y) ^ 2) := by
    rw [← hB]
    nlinarith [sq_nonneg (√(μ / (n * y)) - 1 / (n * y))]
  rw [hrp]
  calc S⁻¹ * (√(μ / (n * y)) + 1 / (n * y)) ^ 2
      ≤ S⁻¹ * (2 * (C / (n * S)) + 2 * (1 / (n * y) ^ 2)) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 2 * C / (n * (κ + y)) + 2 / (S * (n * y) ^ 2) := by
        rw [← hS2]; field_simp

/-- The upper bound of the control parameter, in the variables `q = N^{1/6}`, `u = N^{ε/8}`,
`t = κ^{1/4}`. -/
private lemma excl_core5 {q u t y κ μ C : ℝ} (hq : 1 ≤ q) (hu : 1 ≤ u) (ht0 : 0 < t)
    (hκt : κ = t ^ 4)
    (hκ : u ^ 8 / q ^ 4 / 2 ≤ κ) (hy : t / (q ^ 3 * u ^ 2) ≤ y) (hC : 0 ≤ C)
    (hμ : μ ≤ C * (y / √(κ + y))) :
    (κ + y) ^ (-(1 / 2 : ℝ)) * (√(μ / (q ^ 6 * y)) + 1 / (q ^ 6 * y)) ^ 2 ≤
      (4 * C + 4) / q ^ 2 := by
  have hq0 : 0 < q := by linarith
  have hu0 : 0 < u := by linarith
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy
  have hκ0 : 0 < κ := by rw [hκt]; positivity
  have hn : 0 < q ^ 6 := by positivity
  refine (excl_phi_real hn hy0 hκ0.le hC hμ).trans ?_
  have hS : t ^ 2 ≤ √(κ + y) := by
    rw [show t ^ 2 = √(κ) by
      rw [hκt, show t ^ 4 = (t ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hny : q ^ 3 * t / u ^ 2 ≤ q ^ 6 * y := by
    have : q ^ 3 * t / u ^ 2 = q ^ 6 * (t / (q ^ 3 * u ^ 2)) := by field_simp
    rw [this]; exact mul_le_mul_of_nonneg_left hy hn.le
  have hny0 : 0 < q ^ 3 * t / u ^ 2 := by positivity
  have h1 : 2 * C / (q ^ 6 * (κ + y)) ≤ 2 * C / (q ^ 6 * κ) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith
  have h2 : 2 / (√(κ + y) * (q ^ 6 * y) ^ 2) ≤ 2 * u ^ 4 / (q ^ 6 * κ) := by
    have h3 : (q ^ 3 * t / u ^ 2) ^ 2 ≤ (q ^ 6 * y) ^ 2 := pow_le_pow_left₀ hny0.le hny 2
    have h4 : t ^ 2 * (q ^ 3 * t / u ^ 2) ^ 2 ≤ √(κ + y) * (q ^ 6 * y) ^ 2 :=
      mul_le_mul hS h3 (by positivity) (by positivity)
    have h5 : t ^ 2 * (q ^ 3 * t / u ^ 2) ^ 2 = q ^ 6 * κ / u ^ 4 := by
      rw [hκt]; field_simp
    rw [h5] at h4
    calc 2 / (√(κ + y) * (q ^ 6 * y) ^ 2) ≤ 2 / (q ^ 6 * κ / u ^ 4) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) h4
      _ = 2 * u ^ 4 / (q ^ 6 * κ) := by field_simp
  have h6 : 2 * C / (q ^ 6 * κ) + 2 * u ^ 4 / (q ^ 6 * κ) ≤ (4 * C + 4) / q ^ 2 := by
    rw [← add_div]
    have hk' : 1 / κ ≤ 2 * q ^ 4 / u ^ 8 := by
      rw [div_le_div_iff₀ hκ0 (by positivity)]
      have : u ^ 8 / q ^ 4 / 2 * (2 * q ^ 4) = u ^ 8 := by field_simp
      nlinarith [mul_le_mul_of_nonneg_right hκ (by positivity : (0:ℝ) ≤ 2 * q ^ 4)]
    have hu4 : u ^ 4 ≤ u ^ 8 := pow_le_pow_right₀ hu (by norm_num)
    have hu8 : 1 ≤ u ^ 8 := one_le_pow₀ hu
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have e1 : (2 * C + 2 * u ^ 4) * q ^ 2 ≤ (4 * C + 4) * (q ^ 6 * κ) := by
      have hq4 : 0 < q ^ 4 := by positivity
      have hkk : u ^ 8 / q ^ 4 ≤ 2 * κ := by linarith
      have hkk' : u ^ 8 ≤ 2 * κ * q ^ 4 := by
        rwa [div_le_iff₀ hq4] at hkk
      have hq2 : 0 < q ^ 2 := by positivity
      -- (2C+2u^4) q^2 ≤ (4C+4) q^6 κ
      have : (2 * C + 2 * u ^ 4) * q ^ 2 ≤ (2 * C + 2 * u ^ 8) * q ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hq2.le
        nlinarith
      refine this.trans ?_
      have : (2 * C + 2 * u ^ 8) * q ^ 2 ≤ (2 * C * u ^ 8 + 2 * u ^ 8) * q ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hq2.le
        nlinarith [mul_le_mul_of_nonneg_left hu8 hC]
      refine this.trans ?_
      calc (2 * C * u ^ 8 + 2 * u ^ 8) * q ^ 2 = (2 * C + 2) * (u ^ 8 * q ^ 2) := by ring
        _ ≤ (2 * C + 2) * (2 * κ * q ^ 4 * q ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_right hkk' hq2.le
        _ = (4 * C + 4) * (q ^ 6 * κ) := by ring
    linarith
  linarith

/-- The exclusion estimate at `η = t/(q³u²)`, in the variables `q = N^{1/6}`, `u = N^{ε/8}`,
`t = κ^{1/4}`. -/
private lemma excl_core6 {q u t y κ μ C : ℝ} (hq : 1 ≤ q) (hu : 1 ≤ u) (ht0 : 0 < t)
    (hκt : κ = t ^ 4)
    (hκ : u ^ 8 / q ^ 4 / 2 ≤ κ) (hy : y = t / (q ^ 3 * u ^ 2)) (hC : 0 ≤ C)
    (hμ : μ ≤ C * (y / √(κ + y))) :
    q ^ 6 * y * (μ + u * ((κ + y) ^ (-(1 / 2 : ℝ)) *
      (√(μ / (q ^ 6 * y)) + 1 / (q ^ 6 * y)) ^ 2)) ≤ (17 * C + 16) / u ^ 3 := by
  have hq0 : 0 < q := by linarith
  have hu0 : 0 < u := by linarith
  have hy0 : 0 < y := by rw [hy]; positivity
  have hκ0 : 0 < κ := by rw [hκt]; positivity
  have hn : 0 < q ^ 6 := by positivity
  have hS : t ^ 2 ≤ √(κ + y) := by
    rw [show t ^ 2 = √(κ) by
      rw [hκt, show t ^ 4 = (t ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hS0 : 0 < √(κ + y) := lt_of_lt_of_le (by positivity) hS
  -- t ≥ u² / (2q)
  have ht1 : u ^ 2 / (2 * q) ≤ t := by
    have h4 : (u ^ 2 / (2 * q)) ^ 4 ≤ t ^ 4 := by
      rw [← hκt]
      have : (u ^ 2 / (2 * q)) ^ 4 = u ^ 8 / q ^ 4 / 16 := by field_simp; ring
      rw [this]
      have : 0 ≤ u ^ 8 / q ^ 4 := by positivity
      linarith
    exact le_of_pow_le_pow_left₀ (by norm_num) ht0.le h4
  have ht3 : u ^ 6 / (8 * q ^ 3) ≤ t ^ 3 := by
    have := pow_le_pow_left₀ (by positivity) ht1 3
    have e : (u ^ 2 / (2 * q)) ^ 3 = u ^ 6 / (8 * q ^ 3) := by field_simp; ring
    rwa [e] at this
  have hu3 : 0 < u ^ 3 := by positivity
  -- A1
  have A1 : q ^ 6 * y * μ ≤ C / u ^ 4 := by
    have h1 : q ^ 6 * y * μ ≤ q ^ 6 * y * (C * (y / √(κ + y))) :=
      mul_le_mul_of_nonneg_left hμ (by positivity)
    have h2 : y / √(κ + y) ≤ y / t ^ 2 :=
      div_le_div_of_nonneg_left hy0.le (by positivity) hS
    have h3 : q ^ 6 * y * (C * (y / √(κ + y))) ≤ q ^ 6 * y * (C * (y / t ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hC) (by positivity)
    refine h1.trans (h3.trans (le_of_eq ?_))
    rw [hy]; field_simp
  -- A2
  have A2 : q ^ 6 * y * ((κ + y) ^ (-(1 / 2 : ℝ)) *
      (√(μ / (q ^ 6 * y)) + 1 / (q ^ 6 * y)) ^ 2) ≤ 16 * C / u ^ 8 + 16 / u ^ 4 := by
    have hP := excl_phi_real hn hy0 hκ0.le hC hμ
    refine (mul_le_mul_of_nonneg_left hP (by positivity)).trans ?_
    have e1 : q ^ 6 * y * (2 * C / (q ^ 6 * (κ + y))) = 2 * C * (y / (κ + y)) := by
      field_simp
    have e2 : q ^ 6 * y * (2 / (√(κ + y) * (q ^ 6 * y) ^ 2)) = 2 / (√(κ + y) * (q ^ 6 * y)) := by
      field_simp
    rw [mul_add, e1, e2]
    have b1 : y / (κ + y) ≤ 8 / u ^ 8 := by
      have : y / (κ + y) ≤ y / κ := div_le_div_of_nonneg_left hy0.le hκ0 (by linarith)
      refine this.trans ?_
      rw [hy, hκt, div_le_div_iff₀ (by positivity) (by positivity)]
      -- t / (q^3 u^2) * u^8 ≤ 8 * t^4
      have h := mul_le_mul_of_nonneg_left ht3 (by positivity : 0 ≤ 8 * q ^ 3 * t)
      have e : t / (q ^ 3 * u ^ 2) * u ^ 8 = t * u ^ 6 / q ^ 3 := by field_simp
      rw [e, div_le_iff₀ (by positivity)]
      have e' : 8 * q ^ 3 * t * (u ^ 6 / (8 * q ^ 3)) = t * u ^ 6 := by field_simp
      rw [e'] at h
      nlinarith [h]
    have b2 : 2 / (√(κ + y) * (q ^ 6 * y)) ≤ 16 / u ^ 4 := by
      have hqy : q ^ 6 * y = q ^ 3 * t / u ^ 2 := by rw [hy]; field_simp
      have h1 : t ^ 2 * (q ^ 6 * y) ≤ √(κ + y) * (q ^ 6 * y) :=
        mul_le_mul_of_nonneg_right hS (by positivity)
      calc 2 / (√(κ + y) * (q ^ 6 * y)) ≤ 2 / (t ^ 2 * (q ^ 6 * y)) :=
            div_le_div_of_nonneg_left (by norm_num) (by positivity) h1
        _ = 2 * u ^ 2 / (q ^ 3 * t ^ 3) := by rw [hqy]; field_simp
        _ ≤ 16 / u ^ 4 := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            have h := mul_le_mul_of_nonneg_left ht3 (by positivity : 0 ≤ 16 * q ^ 3)
            have e' : 16 * q ^ 3 * (u ^ 6 / (8 * q ^ 3)) = 2 * u ^ 6 := by field_simp; ring
            rw [e'] at h
            nlinarith [h]
    have : 2 * C * (y / (κ + y)) ≤ 2 * C * (8 / u ^ 8) :=
      mul_le_mul_of_nonneg_left b1 (by positivity)
    calc 2 * C * (y / (κ + y)) + 2 / (√(κ + y) * (q ^ 6 * y))
        ≤ 2 * C * (8 / u ^ 8) + 16 / u ^ 4 := add_le_add this b2
      _ = 16 * C / u ^ 8 + 16 / u ^ 4 := by ring
  rw [mul_add]
  have hu8 : 1 ≤ u ^ 8 := one_le_pow₀ hu
  have f1 : C / u ^ 4 ≤ C / u ^ 3 := by
    apply div_le_div_of_nonneg_left hC hu3 (pow_le_pow_right₀ hu (by norm_num))
  have f2 : u * (16 * C / u ^ 8 + 16 / u ^ 4) ≤ 16 * C / u ^ 3 + 16 / u ^ 3 := by
    have e : u * (16 * C / u ^ 8 + 16 / u ^ 4) = 16 * C / u ^ 7 + 16 / u ^ 3 := by
      field_simp
    rw [e]
    have : 16 * C / u ^ 7 ≤ 16 * C / u ^ 3 :=
      div_le_div_of_nonneg_left (by positivity) hu3 (pow_le_pow_right₀ hu (by norm_num))
    linarith
  have hh : q ^ 6 * y * (u * ((κ + y) ^ (-(1 / 2 : ℝ)) *
      (√(μ / (q ^ 6 * y)) + 1 / (q ^ 6 * y)) ^ 2)) = u * (q ^ 6 * y * ((κ + y) ^ (-(1 / 2 : ℝ)) *
      (√(μ / (q ^ 6 * y)) + 1 / (q ^ 6 * y)) ^ 2)) := by ring
  rw [hh]
  have := mul_le_mul_of_nonneg_left A2 hu0.le
  have e : (17 * C + 16) / u ^ 3 = C / u ^ 3 + 16 * C / u ^ 3 + 16 / u ^ 3 := by ring
  rw [e]
  linarith

/-- `q = N^{1/6}` and `u = N^{ε/8}` express the powers of `N` occurring in Lemma 10.1. -/
private lemma excl_powers {n : ℝ} (hn : 1 ≤ n) (ε : ℝ) :
    n = (n ^ (1 / 6 : ℝ)) ^ 6 ∧
    n ^ (-2 / 3 + ε) = (n ^ (ε / 8)) ^ 8 / (n ^ (1 / 6 : ℝ)) ^ 4 ∧
    n ^ (-1 / 2 - ε / 4) = 1 / ((n ^ (1 / 6 : ℝ)) ^ 3 * (n ^ (ε / 8)) ^ 2) ∧
    n ^ (-1 / 3 : ℝ) = 1 / (n ^ (1 / 6 : ℝ)) ^ 2 := by
  have hn0 : 0 < n := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; norm_num
  · rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le,
      ← Real.rpow_mul hn0.le, ← Real.rpow_sub hn0]
    congr 1; push_cast; ring
  · rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le,
      ← Real.rpow_mul hn0.le, ← Real.rpow_add hn0, one_div, ← Real.rpow_neg hn0.le]
    congr 1; push_cast; ring
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le, one_div, ← Real.rpow_neg hn0.le]
    congr 1; push_cast; ring

/-- The control parameter `(κ + η)^{−1/2} Ψ²` of (improved_avg_G). -/
def gapPhi (N : ℕ) (σ : Fin M → ℝ) (z : ℂ) : ℝ :=
  (kappa N σ z.re + z.im) ^ (-(1 / 2 : ℝ)) * Psi N σ z ^ 2

/-- (Phi_cond) for `Φ = (κ + η)^{−1/2} Ψ²` on the domain of Lemma 10.1, given
`Im m ≤ C_up η/√(κ + η)` there. -/
theorem phiCond_gap (τ₀ ε Cup : ℝ) (hτ₀ : 0 < τ₀) (hτ₀4 : τ₀ ≤ 1 / 4) (hε : 0 < ε)
    (hε2 : ε < 2 / 3) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {M : ℕ} (σ : Fin M → ℝ) (S : Set ℂ), DensityAssumptions τ₀ N σ →
      S ⊆ gapDomain τ₀ ε N σ →
      (∀ z ∈ S, (mFun N σ z).im ≤ Cup * (z.im / √(kappa N σ z.re + z.im))) →
      PhiCond τ₀ ((kappaMax τ₀ + τ₀⁻¹) ^ (-(1 / 2 : ℝ))) N σ S (gapPhi N σ) := by
  set C : ℝ := max Cup 0 with hC
  have hC0 : 0 ≤ C := le_max_right _ _
  refine ⟨max 1 ⌈(4 * C + 4) ^ (24 / 5 : ℝ)⌉₊, fun N hN M σ S hD hS hIm z hz => ?_⟩
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hn0 : (0 : ℝ) < N := by linarith
  obtain ⟨hzD, -, hκ, hy⟩ := hS hz
  have hy0 : 0 < z.im := hzD.1
  set κ := kappa N σ z.re with hκdef
  obtain ⟨e1, e2, e3, e4⟩ := excl_powers hn1 ε
  set q : ℝ := (N : ℝ) ^ (1 / 6 : ℝ) with hq
  set u : ℝ := (N : ℝ) ^ (ε / 8) with hu
  have hq1 : 1 ≤ q := Real.one_le_rpow hn1 (by norm_num)
  have hu1 : 1 ≤ u := Real.one_le_rpow hn1 (by linarith)
  have hκ0 : 0 < κ := by
    refine lt_of_lt_of_le ?_ hκ
    have := Real.rpow_pos_of_pos hn0 (-2 / 3 + ε)
    positivity
  set t : ℝ := κ ^ (1 / 4 : ℝ) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hκ0 _
  have hκt : κ = t ^ 4 := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hκ0.le]; norm_num
  have hκ' : u ^ 8 / q ^ 4 / 2 ≤ κ := by rw [← e2]; exact hκ
  have hy' : t / (q ^ 3 * u ^ 2) ≤ z.im := by
    have : t / (q ^ 3 * u ^ 2) = (N : ℝ) ^ (-1 / 2 - ε / 4) * κ ^ (1 / 4 : ℝ) := by
      rw [e3]; ring
    rw [this]; exact hy
  have hμ : (mFun N σ z).im ≤ C * (z.im / √(κ + z.im)) :=
    (hIm z hz).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have key := excl_core5 hq1 hu1 ht0 hκt hκ' hy' hC0 hμ
  rw [← e1] at key
  have hΦ : gapPhi N σ z ≤ (4 * C + 4) / q ^ 2 := by
    unfold gapPhi Psi
    exact key
  have hKy : κ + z.im ≤ kappaMax τ₀ + τ₀⁻¹ := by
    have h1 := kappa_le hD hzD.2.2.1
    have h2 := hzD.2.2.2.2
    linarith
  constructor
  · unfold gapPhi
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos (by linarith) hKy (by norm_num)) (by positivity)
  · refine hΦ.trans ?_
    have hq2 : q ^ 2 = (N : ℝ) ^ (1 / 3 : ℝ) := by
      rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; norm_num
    have hlow : (N : ℝ) ^ (-1 / 8 : ℝ) ≤ (N : ℝ) ^ (-τ₀ / 2) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    have hbig : 4 * C + 4 ≤ (N : ℝ) ^ (5 / 24 : ℝ) := by
      have h1 : ((4 * C + 4) ^ (24 / 5 : ℝ)) ≤ N := by
        refine (Nat.le_ceil _).trans ?_
        exact_mod_cast (le_max_right _ _).trans hN
      have h2 := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ 5 / 24)
      rwa [← Real.rpow_mul (by positivity), show (24 / 5 : ℝ) * (5 / 24) = 1 by norm_num,
        Real.rpow_one] at h2
    rw [hq2, div_le_iff₀ (Real.rpow_pos_of_pos hn0 _)]
    calc 4 * C + 4 ≤ (N : ℝ) ^ (5 / 24 : ℝ) := hbig
      _ = (N : ℝ) ^ (-1 / 8 : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ) := by
          rw [← Real.rpow_add hn0]; norm_num
      _ ≤ (N : ℝ) ^ (-τ₀ / 2) * (N : ℝ) ^ (1 / 3 : ℝ) :=
          mul_le_mul_of_nonneg_right hlow (by positivity)

/-- The exclusion step of Lemma 10.1: at `η = N^{−1/2−ε/4} κ^{1/4}`,
`Im m + N^{ε/8} (κ + η)^{−1/2} Ψ² < (2Nη)⁻¹`. -/
theorem gap_exclusion (ε Cup : ℝ) (hε : 0 < ε) (hε2 : ε < 2 / 3) (hCup : 0 ≤ Cup) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {M : ℕ} (σ : Fin M → ℝ) (z : ℂ),
      (N : ℝ) ^ (-2 / 3 + ε) / 2 ≤ kappa N σ z.re →
      z.im = (N : ℝ) ^ (-1 / 2 - ε / 4) * kappa N σ z.re ^ (1 / 4 : ℝ) →
      (mFun N σ z).im ≤ Cup * (z.im / √(kappa N σ z.re + z.im)) →
      (mFun N σ z).im + (N : ℝ) ^ (ε / 8) * gapPhi N σ z < 1 / (2 * N * z.im) := by
  refine ⟨max 1 ⌈(34 * Cup + 33) ^ (8 / (3 * ε) : ℝ)⌉₊,
    fun N hN M σ z hκ hy hμ => ?_⟩
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hn0 : (0 : ℝ) < N := by linarith
  set κ := kappa N σ z.re with hκdef
  obtain ⟨e1, e2, e3, -⟩ := excl_powers hn1 ε
  set q : ℝ := (N : ℝ) ^ (1 / 6 : ℝ) with hq
  set u : ℝ := (N : ℝ) ^ (ε / 8) with hu
  have hq1 : 1 ≤ q := Real.one_le_rpow hn1 (by norm_num)
  have hu1 : 1 ≤ u := Real.one_le_rpow hn1 (by linarith)
  have hκ0 : 0 < κ := by
    refine lt_of_lt_of_le ?_ hκ
    have := Real.rpow_pos_of_pos hn0 (-2 / 3 + ε)
    positivity
  set t : ℝ := κ ^ (1 / 4 : ℝ) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hκ0 _
  have hκt : κ = t ^ 4 := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hκ0.le]; norm_num
  have hκ' : u ^ 8 / q ^ 4 / 2 ≤ κ := by rw [← e2]; exact hκ
  have hy' : z.im = t / (q ^ 3 * u ^ 2) := by
    rw [hy, e3]; ring
  have hy0 : 0 < z.im := by rw [hy']; positivity
  have key := excl_core6 hq1 hu1 ht0 hκt hκ' hy' hCup hμ
  rw [← e1] at key
  have hΦ : (mFun N σ z).im + u * gapPhi N σ z =
      (mFun N σ z).im + u * ((κ + z.im) ^ (-(1 / 2 : ℝ)) *
        (√((mFun N σ z).im / (N * z.im)) + 1 / (N * z.im)) ^ 2) := rfl
  have hu3 : 34 * Cup + 33 ≤ u ^ 3 := by
    have h1 : ((34 * Cup + 33) ^ (8 / (3 * ε) : ℝ)) ≤ N := by
      refine (Nat.le_ceil _).trans ?_
      exact_mod_cast (le_max_right _ _).trans hN
    have h2 := Real.rpow_le_rpow (by positivity) h1 (by positivity : (0 : ℝ) ≤ 3 * ε / 8)
    rw [← Real.rpow_mul (by positivity), show 8 / (3 * ε) * (3 * ε / 8) = 1 by field_simp,
      Real.rpow_one] at h2
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    convert h2 using 2
    push_cast; ring
  have hu30 : 0 < u ^ 3 := by positivity
  have hlt : (17 * Cup + 16) / u ^ 3 < 1 / 2 := by
    rw [div_lt_iff₀ hu30]; linarith
  rw [hΦ, lt_div_iff₀ (by positivity)]
  have : ((mFun N σ z).im + u * ((κ + z.im) ^ (-(1 / 2 : ℝ)) *
        (√((mFun N σ z).im / (N * z.im)) + 1 / (N * z.im)) ^ 2)) * (2 * N * z.im) =
      2 * ((N : ℝ) * z.im * ((mFun N σ z).im + u * ((κ + z.im) ^ (-(1 / 2 : ℝ)) *
        (√((mFun N σ z).im / (N * z.im)) + 1 / (N * z.im)) ^ 2))) := by ring
  rw [this]
  linarith

/-! ### Instances

Marchenko–Pastur: `M = 100`, `N = 200`, `σ = 1` (`φ = 1/2`), `τ = 1/20`. The statements with `∃ N₀`
(`phiCond_gap`, `gap_exclusion`) have no small concrete instance of their conclusion; their
examples fix the parameters and leave the hypotheses of the quantified statement as binders. -/

local notation "σP" => (fun _ : Fin 100 => (1 : ℝ))

/-- (def_m_N) at `M = N = 1`, `Σ = X = 1`, `z = i`. -/
example : mN (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ) Complex.I =
    empStieltjes (specOf (QN (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)))
      Complex.I :=
  mN_eq_empStieltjes Matrix.PosDef.one (1 : Matrix (Fin 1) (Fin 1) ℝ) (by simp)

/-- `K = 2`, `λ = (0, 3)`, `z = i`, `j = 0`. -/
example : 1 / (2 * ((2 : ℕ) : ℝ) * Complex.I.im) ≤ (empStieltjes ![0, 3] Complex.I).im :=
  im_empStieltjes_ge (K := 2) ![0, 3] (z := Complex.I) (by simp) 0 (by simp)

/-- The grid point of `E = −997/1000` at `N = 200`, `ε = 1/2`, for MP: `E' = −1`. -/
example : ⌊(-997 / 1000 : ℝ) * ((200 : ℕ) : ℝ)⌋ = -200 := by
  rw [Int.floor_eq_iff]; norm_num

/-- `phiCond_gap` at `τ₀ = 1/20`, `ε = 1/3`, `C_up = 1`: conditional, the hypotheses of the
quantified statement are its binders. -/
example := phiCond_gap (1 / 20) (1 / 3) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `gap_exclusion` at `ε = 1/3`, `C_up = 1`: conditional, the hypotheses of the quantified
statement are its binders. -/
example := gap_exclusion (1 / 3) 1 (by norm_num) (by norm_num) (by norm_num)

end Anisotropic
