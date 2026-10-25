import Anisotropic.Averaged.Defs
import Anisotropic.Density.Basic
import Anisotropic.Density.Critical
import Anisotropic.Density.GenProp
import Anisotropic.Density.Stability.Defs
import Anisotropic.Density.Stability.Domains
import Anisotropic.Density.Stability.EdgeTools
import Anisotropic.Density.Structure
import Anisotropic.Density.Varrho
import Anisotropic.Entrywise.Defs
import Anisotropic.Framework.Model

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # The large-`η` domain and the covering of `𝐃(τ, N)` (proof of Theorem 3.6) -/

/-- `edgeTau' τ > 0` (the window of Lemmas A.4 and A.5). -/
theorem edgeTau'_pos {τ : ℝ} (hτ : 0 < τ) : 0 < edgeTau' τ := by
  have hcx : 0 < edgecx τ := by unfold edgecx; positivity
  have hCx : 0 < edgeCx τ := by unfold edgeCx; positivity
  have hc2 : 0 < edgec2 τ := by unfold edgec2; positivity
  have hC3 : 0 < edgeC3 τ := by unfold edgeC3; positivity
  have hr0 : 0 < edgeRho0 τ := by unfold edgeRho0; positivity
  have hr1 : 0 < edgeRho1 τ := by unfold edgeRho1; positivity
  unfold edgeTau' edgeTau0
  positivity

/-- The window `τ' = min(τ'(τ/2), τ/4)` of the covering of `𝐃(τ, N)`. -/
def coverTau (τ : ℝ) : ℝ := min (edgeTau' (τ / 2)) (τ / 4)

theorem coverTau_pos {τ : ℝ} (hτ : 0 < τ) : 0 < coverTau τ :=
  lt_min (edgeTau'_pos (half_pos hτ)) (by linarith)

/-- `{z ∈ 𝐃(τ, N) : η ≥ τ/2}`. -/
def highDomain (τ : ℝ) (N : ℕ) : Set ℂ := {z | z ∈ specDomain τ N ∧ τ / 2 ≤ z.im}

theorem spectralDomain_highDomain (τ : ℝ) (N : ℕ) : SpectralDomain τ N (highDomain τ N) :=
  ⟨fun _ hz => hz.1, fun _ hz _ hw _ hle => ⟨hw, le_trans hz.2 hle⟩⟩

/-- The stability constant `8(C_m + 1)/τ²` on the large-`η` domain (Lemma A.5, `Im z ≥ τ/2`). -/
def highC (τ : ℝ) : ℝ := 8 * (mBoundConst τ + 1) / τ ^ 2

/-- The (1+xm) constant `min(1/2, τ/(4 C_m²))` on the large-`η` domain. -/
def highc (τ : ℝ) : ℝ := min (1 / 2) (τ / (4 * mBoundConst τ ^ 2))

theorem highc_pos {τ : ℝ} (hτ : 0 < τ) : 0 < highc τ := by
  have := mBoundConst_pos hτ
  unfold highc
  exact lt_min (by norm_num) (by positivity)

/-- Under Assumption 2.1 on `σ`, `τ ≤ 1` (from `τ ≤ φ ≤ τ⁻¹`). -/
private theorem regions_tau_le_one {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ}
    (h : DensityAssumptions τ N σ) : τ ≤ 1 := by
  have h1 : τ ≤ τ⁻¹ := h.phi_lower.trans h.phi_upper
  have h2 : τ * τ ≤ 1 := by
    calc τ * τ ≤ τ⁻¹ * τ := mul_le_mul_of_nonneg_right h1 h.pos.le
      _ = 1 := inv_mul_cancel₀ h.pos.ne'
  nlinarith [h.pos]

/-- Stability (Definition 5.4) on the large-`η` domain, from the case `Im z ≥ h` of Lemma A.5. -/
theorem stab_high (τ : ℝ) (hτ : 0 < τ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {M : ℕ} (σ : Fin M → ℝ), DensityAssumptions τ N σ →
      StableOn (highC τ) (highC τ) 0 N σ (highDomain τ N) := by
  refine ⟨⌈Real.exp (4 / τ)⌉₊, fun N hN M σ h => ?_⟩
  have hexp : Real.exp (4 / τ) ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hNr : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos _) hexp
  have hN0 : 0 < N := by exact_mod_cast hNr
  have hlog : 4 / τ ≤ Real.log N := by
    rw [← Real.log_exp (4 / τ)]
    exact Real.log_le_log (Real.exp_pos _) hexp
  have hlogpos : 0 < Real.log N := lt_of_lt_of_le (by positivity) hlog
  have hloginv : (Real.log N)⁻¹ ≤ τ / 4 := by
    rw [inv_le_comm₀ hlogpos (by positivity), inv_div]
    exact hlog
  have hτ1 := regions_tau_le_one h
  have hC := mBoundConst_pos hτ
  intro δ hδ μ hμ z hz hw _
  simp only [weakBound, twoRegime, ite_self]
  set C := mBoundConst τ with hCdef
  set u := resolventTransform μ z with hudef
  have hη : 0 < z.im := hz.1.1
  have hu : 0 < u.im := im_resolventTransform_pos μ hη
  have hδpos : 0 < δ z := lt_of_lt_of_le (by positivity) (hδ.lower z hz)
  have hδτ : δ z ≤ τ / 4 := (hδ.upper z hz).trans hloginv
  have hA := norm_sub_mFun_le_of_im_ge h.nonneg hN0 (half_pos hτ) hz.2 hu
    (hw.trans (by linarith))
  have hm := gen_prop_m_specDomain h hz.1
  have himpos : 0 < (mFun N σ z).im :=
    lt_of_lt_of_le (mul_pos (inv_pos.2 hC) hη) hm.2.2
  have himle : (mFun N σ z).im ≤ C := (Complex.im_le_norm _).trans hm.2.1
  have hsq : √(δ z) ≤ 1 := Real.sqrt_le_one.2 (by linarith)
  set D := (mFun N σ z).im + √(δ z) with hDdef
  have hDpos : 0 < D := by positivity
  have hDle : D ≤ C + 1 := by linarith
  have hB : ‖u - mFun N σ z‖ ≤ 8 * δ z / τ ^ 2 := by
    refine hA.trans ?_
    rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hw, norm_nonneg (fC N σ u - z)]
  refine hB.trans ?_
  rw [highC, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
  have h8 : 0 ≤ 8 * δ z * τ ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hDle h8]

/-- (1+xm) on the large-`η` domain. -/
theorem oneXm_high {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) :
    OneXmOn (highc τ) N σ (highDomain τ N) := by
  intro z hz i
  have hτ := h.pos
  have hC := mBoundConst_pos hτ
  set C := mBoundConst τ with hCdef
  set m := mFun N σ z with hmdef
  have hm := gen_prop_m_specDomain h hz.1
  have hσ := h.nonneg i
  have hnm : ‖(σ i : ℂ) * m‖ = σ i * ‖m‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hσ]
  by_cases hsm : σ i * ‖m‖ ≤ 1 / 2
  · refine (min_le_left _ _).trans ?_
    have := norm_sub_le (1 + (σ i : ℂ) * m) ((σ i : ℂ) * m)
    rw [add_sub_cancel_right, norm_one, hnm] at this
    linarith
  · push Not at hsm
    refine (min_le_right _ _).trans ?_
    have him : (1 + (σ i : ℂ) * m).im = σ i * m.im := by simp
    have hle : σ i * m.im ≤ ‖1 + (σ i : ℂ) * m‖ := him ▸ Complex.im_le_norm _
    refine le_trans ?_ hle
    have hsC : 1 / 2 < σ i * C := lt_of_lt_of_le hsm (mul_le_mul_of_nonneg_left hm.2.1 hσ)
    have h1 : σ i * (C⁻¹ * z.im) ≤ σ i * m.im := mul_le_mul_of_nonneg_left hm.2.2 hσ
    refine le_trans ?_ h1
    rw [div_le_iff₀ (by positivity)]
    have e : σ i * (C⁻¹ * z.im) * (4 * C ^ 2) = 4 * (σ i * C) * z.im := by
      field_simp
    rw [e]
    nlinarith [hz.2]

/-- `ϱ` puts no mass on `(-∞, 0)`, so `supp ϱ ⊆ [0, ∞)` (definition of `ϱ`, Lemma 2.2). -/
private theorem regions_support_nonneg (N : ℕ) (σ : Fin M → ℝ) {x : ℝ}
    (hx : x ∈ (varrho N σ).support) : 0 ≤ x := by
  by_contra hneg
  push Not at hneg
  refine (Measure.notMem_support_iff_exists.2 ⟨Set.Iio 0, Iio_mem_nhds hneg, ?_⟩) hx
  rw [varrho, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ measurableSet_Iio,
    Set.indicator_of_notMem (lt_irrefl (0 : ℝ)), smul_zero, zero_add,
    withDensity_apply _ measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
  have he : Set.Iio (0 : ℝ) ∩ Set.Ioi 0 = ∅ := by
    ext y; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi, Set.mem_empty_iff_false,
      iff_false, not_and, not_lt]; intro hy; exact hy.le
  rw [he, Measure.restrict_empty, lintegral_zero_measure]

/-- Under Assumption 2.1 on `σ`, some `σ_i` is positive (from (Sigma_gap)). -/
private theorem regions_posVals_nonempty {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ}
    (h : DensityAssumptions τ N σ) : (posVals σ).Nonempty := by
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
  have hemp : empMeasure σ (Set.Icc 0 τ) = 1 := by
    simp only [empMeasure, Measure.smul_apply, Measure.finsetSum_apply,
      Measure.dirac_apply' _ measurableSet_Icc, hall, smul_eq_mul]
    have h0 : (0 : ℝ) ∈ Set.Icc 0 τ := ⟨le_rfl, h.pos.le⟩
    simp only [Set.indicator_of_mem h0, Pi.one_apply, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast hM) (ENNReal.natCast_ne_top _)
  rw [hemp, ENNReal.toReal_one] at hgap
  linarith [h.pos]

/-- The covering of `𝐃(τ, N)` in the proof of Theorem 3.6, together with the
large-`η` domain: every `z ∈ 𝐃(τ, N)` lies in `{η ≥ τ/2}`, in `𝐃^o`, in some `𝐃^b_k`, or in
some `𝐃^e_l` with `a_l ≥ τ/2`, the last three at `(τ/2, coverTau τ)`. -/
theorem specDomain_cover {τ : ℝ} (hτ : 0 < τ) {N : ℕ} (hN : 1 ≤ N) {σ : Fin M → ℝ}
    (h : DensityAssumptions τ N σ) {z : ℂ} (hz : z ∈ specDomain τ N) :
    z ∈ highDomain τ N ∨ z ∈ outsideDomain (τ / 2) (coverTau τ) N σ ∨
      (∃ k, 1 ≤ k ∧ k ≤ numBands N σ ∧ z ∈ bulkDomain (τ / 2) (coverTau τ) N σ k) ∨
      (∃ l, 1 ≤ l ∧ l ≤ 2 * numBands N σ ∧ τ / 2 ≤ edgeVal N σ l ∧
        z ∈ edgeDomain (τ / 2) (coverTau τ) N σ l) := by
  by_cases hη : τ / 2 ≤ z.im
  · exact Or.inl ⟨hz, hη⟩
  push Not at hη
  right
  have hz' : z ∈ specDomain (τ / 2) N := specDomain_subset (half_pos hτ) (by linarith) hN hz
  have hN0 : 0 < N := hN
  set τ' := coverTau τ with hτ'def
  have hτ'pos : 0 < τ' := coverTau_pos hτ
  have hτ'4 : τ' ≤ τ / 4 := min_le_right _ _
  set E := z.re with hEdef
  -- `|E| > τ/2 + τ'`, from `|z| ≥ τ` and `η < τ/2`
  have hE : τ / 2 + τ' < |E| := by
    have hnorm : τ ^ 2 ≤ E ^ 2 + z.im ^ 2 := by
      have h1 : τ ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ hτ.le hz.2.1 2
      rw [Complex.sq_norm, Complex.normSq_apply] at h1
      nlinarith
    have hη2 : z.im ^ 2 < (τ / 2) ^ 2 := pow_lt_pow_left₀ hη hz.1.le two_ne_zero
    have hsq : (τ / 2 + τ') ^ 2 < E ^ 2 := by nlinarith
    have := sq_lt_sq.1 hsq
    rwa [abs_of_pos (by positivity : 0 < τ / 2 + τ')] at this
  have := isProbabilityMeasure_varrho N σ h.nonneg hN0
  have hne : (varrho N σ).support.Nonempty :=
    Measure.nonempty_support (IsProbabilityMeasure.ne_zero _)
  rcases le_or_gt E 0 with hE0 | hE0
  · -- `E < 0`: the outside domain
    left
    refine ⟨hz', (Metric.le_infDist hne).2 fun y hy => ?_⟩
    have hy0 := regions_support_nonneg N σ hy
    rw [abs_of_nonpos hE0] at hE
    rw [Real.dist_eq]
    exact le_trans (by linarith) (neg_le_abs (E - y))
  by_cases hd : τ' ≤ Metric.infDist E (varrho N σ).support
  · exact Or.inl ⟨hz', hd⟩
  push Not at hd
  right
  rw [abs_of_pos hE0] at hE
  obtain ⟨x, hx, hxE⟩ := (Metric.infDist_lt_iff hne).1 hd
  rw [Real.dist_eq, abs_lt] at hxE
  have hx0 : 0 < x := by linarith
  obtain ⟨k, hk1, hkp, hxk⟩ :=
    (mem_support_varrho_iff N σ h.nonneg hN0 (regions_posVals_nonempty h) hx0).1 hx
  by_cases hlo : edgeVal N σ (2 * k) + τ' ≤ E
  · by_cases hhi : E ≤ edgeVal N σ (2 * k - 1) - τ'
    · exact Or.inl ⟨k, hk1, hkp, hz', hlo, hhi⟩
    · push Not at hhi
      refine Or.inr ⟨2 * k - 1, by omega, by omega, by linarith [hxk.2], hz', ?_, ?_⟩ <;>
        linarith [hxk.2]
  · push Not at hlo
    refine Or.inr ⟨2 * k, by omega, by omega, by linarith [hxk.1], hz', ?_, ?_⟩ <;>
      linarith [hxk.1]

/-- Stability on the large-`η` domain for the family `M = N`, `σ ≡ 1`, `τ = 1/20` (so `φ = 1`):
Assumption 2.1 on `σ` is discharged at every `N ≥ max N₀ 1`, with `N₀` the threshold of
`stab_high`. -/
example : ∃ N₀ : ℕ, ∀ N ≥ max N₀ 1,
    StableOn (highC (1 / 20)) (highC (1 / 20)) 0 N (fun _ : Fin N => (1 : ℝ))
      (highDomain (1 / 20) N) := by
  obtain ⟨N₀, hN₀⟩ := stab_high (1 / 20) (by norm_num)
  refine ⟨N₀, fun N hN => hN₀ N (le_of_max_le_left hN) _ ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast le_of_max_le_right hN
  have hphi : phiRatio N N = 1 := by
    simp only [phiRatio]; exact div_self (by positivity)
  refine ⟨by norm_num, fun _ => by norm_num, ?_, ?_, fun _ => by norm_num, ?_⟩
  · rw [hphi]; norm_num
  · rw [hphi]; norm_num
  · simp [empMeasure]
    norm_num

end Anisotropic
