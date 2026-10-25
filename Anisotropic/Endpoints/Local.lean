import Anisotropic.Averaged.Defs
import Anisotropic.Averaged.Main
import Anisotropic.Density.Critical
import Anisotropic.Density.GenProp
import Anisotropic.Density.SelfConsistent
import Anisotropic.Density.Stability.Domains
import Anisotropic.Density.Stability.Local
import Anisotropic.Density.Stability.Quadratic
import Anisotropic.Endpoints.Regions
import Anisotropic.Entrywise.Defs
import Anisotropic.Entrywise.DiagModel
import Anisotropic.Framework.Model
import Anisotropic.Gaussian.Ensemble
import Anisotropic.Probability.NormBound.GaussianLower

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # The covering of the spectral domain with a window parameter and the localized bulk law -/

/-- `ϱ` puts no mass on `(-∞, 0)`, so `supp ϱ ⊆ [0, ∞)` (definition of `ϱ`, Lemma 2.2). -/
private theorem loc_support_nonneg (N : ℕ) (σ : Fin M → ℝ) {x : ℝ}
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
private theorem loc_posVals_nonempty {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ}
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

/-- The covering of `𝐃(τ, N)` with window `τ_c ∈ (0, τ/4]`: `{η ≥ τ/2}`, `𝐃^o` with `|E| > τ/2`,
`𝐃^b_k`, or `𝐃^e_l` with `a_l ≥ τ/2`, the last three at `(τ/2, τ_c)`. -/
theorem specDomain_cover' {τ τc : ℝ} (hτ : 0 < τ) (hτc : 0 < τc) (hτc4 : τc ≤ τ / 4)
    (hN : 1 ≤ N) {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) {z : ℂ}
    (hz : z ∈ specDomain τ N) :
    z ∈ highDomain τ N ∨ (z ∈ outsideDomain (τ / 2) τc N σ ∧ τ / 2 < |z.re|) ∨
      (∃ k, 1 ≤ k ∧ k ≤ numBands N σ ∧ z ∈ bulkDomain (τ / 2) τc N σ k) ∨
      (∃ l, 1 ≤ l ∧ l ≤ 2 * numBands N σ ∧ τ / 2 ≤ edgeVal N σ l ∧
        z ∈ edgeDomain (τ / 2) τc N σ l) := by
  by_cases hη : τ / 2 ≤ z.im
  · exact Or.inl ⟨hz, hη⟩
  push Not at hη
  right
  have hz' : z ∈ specDomain (τ / 2) N := specDomain_subset (half_pos hτ) (by linarith) hN hz
  have hN0 : 0 < N := hN
  set E := z.re with hEdef
  -- `|E| > τ/2 + τc`, from `|z| ≥ τ` and `η < τ/2`
  have hE : τ / 2 + τc < |E| := by
    have hnorm : τ ^ 2 ≤ E ^ 2 + z.im ^ 2 := by
      have h1 : τ ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ hτ.le hz.2.1 2
      rw [Complex.sq_norm, Complex.normSq_apply] at h1
      nlinarith
    have hη2 : z.im ^ 2 < (τ / 2) ^ 2 := pow_lt_pow_left₀ hη hz.1.le two_ne_zero
    have hsq : (τ / 2 + τc) ^ 2 < E ^ 2 := by nlinarith
    have := sq_lt_sq.1 hsq
    rwa [abs_of_pos (by positivity : 0 < τ / 2 + τc)] at this
  have hE2 : τ / 2 < |E| := by linarith
  have := isProbabilityMeasure_varrho N σ h.nonneg hN0
  have hne : (varrho N σ).support.Nonempty :=
    Measure.nonempty_support (IsProbabilityMeasure.ne_zero _)
  rcases le_or_gt E 0 with hE0 | hE0
  · -- `E < 0`: the outside domain
    left
    refine ⟨⟨hz', (Metric.le_infDist hne).2 fun y hy => ?_⟩, by rwa [hEdef] at hE2⟩
    have hy0 := loc_support_nonneg N σ hy
    rw [abs_of_nonpos hE0] at hE
    rw [Real.dist_eq]
    exact le_trans (by linarith) (neg_le_abs (E - y))
  by_cases hd : τc ≤ Metric.infDist E (varrho N σ).support
  · exact Or.inl ⟨⟨hz', hd⟩, by rwa [hEdef] at hE2⟩
  push Not at hd
  right
  rw [abs_of_pos hE0] at hE
  obtain ⟨x, hx, hxE⟩ := (Metric.infDist_lt_iff hne).1 hd
  rw [Real.dist_eq, abs_lt] at hxE
  have hx0 : 0 < x := by linarith
  obtain ⟨k, hk1, hkp, hxk⟩ :=
    (mem_support_varrho_iff N σ h.nonneg hN0 (loc_posVals_nonempty h) hx0).1 hx
  by_cases hlo : edgeVal N σ (2 * k) + τc ≤ E
  · by_cases hhi : E ≤ edgeVal N σ (2 * k - 1) - τc
    · exact Or.inl ⟨k, hk1, hkp, hz', hlo, hhi⟩
    · push Not at hhi
      refine Or.inr ⟨2 * k - 1, by omega, by omega, by linarith [hxk.2], hz', ?_, ?_⟩ <;>
        linarith [hxk.2]
  · push Not at hlo
    refine Or.inr ⟨2 * k, by omega, by omega, by linarith [hxk.1], hz', ?_, ?_⟩ <;>
      linarith [hxk.1]

/-- `|E| > τ/2` on `𝐃(τ, N)` when `η < τ/2`. -/
theorem abs_re_gt_of_im_lt {τ : ℝ} (hτ : 0 < τ) {z : ℂ} (hz : z ∈ specDomain τ N)
    (hη : z.im < τ / 2) : τ / 2 < |z.re| := by
  have hnorm : τ ^ 2 ≤ z.re ^ 2 + z.im ^ 2 := by
    have h1 : τ ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ hτ.le hz.2.1 2
    rw [Complex.sq_norm, Complex.normSq_apply] at h1
    nlinarith
  have hη2 : z.im ^ 2 < (τ / 2) ^ 2 := pow_lt_pow_left₀ hη hz.1.le two_ne_zero
  have hsq : (τ / 2) ^ 2 < z.re ^ 2 := by nlinarith
  have := sq_lt_sq.1 hsq
  rwa [abs_of_pos (by positivity : 0 < τ / 2)] at this

/-- The anisotropic and averaged laws under (T_diag) on a spectral domain `S` on which
`Im m ≥ c_b` (Theorem 3.15 (i) with Definition 2.7 (ii) replaced by this bound). -/
theorem loc_law (τ cb : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hcb : 0 < cb) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (S : Set ℂ),
      IsModel τ C M N Sig X → SpectralDomain τ N S →
      (∀ z ∈ S, cb ≤ (mFun N (specOf Sig) z).im) →
      AnisotropicLawAt N ε D Sig X S ∧ AveragedLawAt N ε D Sig X S := by
  have hC : 0 < mBoundConst τ := mBoundConst_pos hτ
  have hc : 0 < oneXmConst cb (mBoundConst τ) := lt_min (by norm_num) (div_pos hcb (by linarith))
  obtain ⟨ε₁, D₁, hε₁, N₁, h₁⟩ := gen_iso_aniso τ _ C ε D hτ hc hε
  obtain ⟨ε₂, D₂, hε₂, N₂, h₂⟩ := gen_iso_avg τ _ C ε D hτ hc hε
  obtain ⟨N₃, h₃⟩ := gauss_avg_input τ _ (locC0wmin τ cb) (locC0wmin τ cb) 0 ε₁ D₁ hτ hc hε₁
  obtain ⟨N₄, h₄⟩ := gauss_avg_input τ _ (locC0wmin τ cb) (locC0wmin τ cb) 0 ε₂ D₂ hτ hc hε₂
  obtain ⟨N₅, h₅⟩ := stab_loc_weak (τ := τ) (C₁ := locC0wmin τ cb) hcb le_rfl
  refine ⟨max (max (max N₁ N₂) (max N₃ N₄)) (max N₅ 1),
    fun N hN Ω _ _ M Sig X S hm hS him => ?_⟩
  have hA : max (max N₁ N₂) (max N₃ N₄) ≤ N := le_of_max_le_left hN
  have hB : max N₅ 1 ≤ N := le_of_max_le_right hN
  have hN1 : 1 ≤ N := le_of_max_le_right hB
  have hda : DensityAssumptions τ N (specOf Sig) := hm.diagModel_specOf.densityAssumptions hτ
  have hx : OneXmOn (oneXmConst cb (mBoundConst τ)) N (specOf Sig) S := fun z hz =>
    one_add_mul_ge_of_mz_reg hda.nonneg hcb hC (gen_prop_m_specDomain hda (hS.1 hz)).2.1
      fun s _ => by
        have h1 := Complex.abs_im_le_norm (mFun N (specOf Sig) z + ((s⁻¹ : ℝ) : ℂ))
        have h2 : (mFun N (specOf Sig) z + ((s⁻¹ : ℝ) : ℂ)).im = (mFun N (specOf Sig) z).im := by
          simp
        rw [h2] at h1
        exact (him z hz).trans ((le_abs_self _).trans h1)
  have hst := h₅ N (le_of_max_le_left hB) (specOf Sig) S hda hS him
  have hgm : IsModel τ gaussMoment M N Sig (gaussX M N) :=
    isModel_gaussX hN1 hm.ratio_ge hm.ratio_le hm.sigma
  have g₁ := h₃ N (le_of_max_le_left (le_of_max_le_right hA)) M Sig _ hgm hS hx hst
  have g₂ := h₄ N (le_of_max_le_right (le_of_max_le_right hA)) M Sig _ hgm hS hx hst
  exact ⟨h₁ N (le_of_max_le_left (le_of_max_le_left hA)) M Sig X _ hm hS hx g₁.1,
    h₂ N (le_of_max_le_right (le_of_max_le_left hA)) M Sig X _ hm hS hx g₂.1
      (averagedPhiLawAt_inv_iff.1 g₂.2)⟩

/-! ## Instances -/

/-- Conditional instance of `loc_law` at the Gaussian ensemble with `Σ = I`, `M = N`, `τ = 1/2`,
`c_b = 1/25`: the model, spectral-domain and `Im m ≥ c_b` hypotheses are binders (the threshold
`N₀` is not explicit); the conclusion is the two laws on `S`. -/
example (S : Set ℂ) : ∃ N₀ : ℕ, ∀ N ≥ N₀,
    IsModel (1 / 2 : ℝ) gaussMoment N N (1 : Matrix (Fin N) (Fin N) ℝ) (gaussX N N) →
    SpectralDomain (1 / 2 : ℝ) N S →
    (∀ z ∈ S, (1 / 25 : ℝ) ≤ (mFun N (specOf (1 : Matrix (Fin N) (Fin N) ℝ)) z).im) →
    AnisotropicLawAt N 1 1 (1 : Matrix (Fin N) (Fin N) ℝ) (gaussX N N) S ∧
      AveragedLawAt N 1 1 (1 : Matrix (Fin N) (Fin N) ℝ) (gaussX N N) S := by
  obtain ⟨N₀, h⟩ := loc_law (1 / 2 : ℝ) (1 / 25) gaussMoment 1 1 (by norm_num) (by norm_num)
    (by norm_num)
  exact ⟨N₀, fun N hN hm hS him => h N hN N 1 (gaussX N N) S hm hS him⟩

#print axioms Anisotropic.specDomain_cover'
#print axioms Anisotropic.abs_re_gt_of_im_lt
#print axioms Anisotropic.loc_law

end Anisotropic
