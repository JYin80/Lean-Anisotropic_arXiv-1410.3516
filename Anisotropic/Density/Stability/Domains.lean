module

public import Anisotropic.Framework.Model
public import Anisotropic.Density.Ordering
public import Anisotropic.Density.Varrho

@[expose] public section

open MeasureTheory Polynomial Filter Topology
open scoped ENNReal

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! ## Spectral domains and `κ` (Definition 3.20, §3.3, (def_kappa)) -/

/-- Definition 3.20: `S ⊆ 𝐃(τ,N)`, closed under increasing `η` at fixed `E`. -/
def SpectralDomain (τ : ℝ) (N : ℕ) (S : Set ℂ) : Prop :=
  S ⊆ specDomain τ N ∧
    ∀ z ∈ S, ∀ w ∈ specDomain τ N, w.re = z.re → z.im ≤ w.im → w ∈ S

/-- `𝐃^e_k(τ,τ',N)`: `E ∈ [a_k - τ', a_k + τ']` (§3.3). -/
def edgeDomain (τ τ' : ℝ) (N : ℕ) (σ : Fin M → ℝ) (k : ℕ) : Set ℂ :=
  {z | z ∈ specDomain τ N ∧ z.re ∈ Set.Icc (edgeVal N σ k - τ') (edgeVal N σ k + τ')}

/-- `𝐃^b_k(τ,τ',N)`: `E ∈ [a_{2k} + τ', a_{2k-1} - τ']` (§3.3). -/
def bulkDomain (τ τ' : ℝ) (N : ℕ) (σ : Fin M → ℝ) (k : ℕ) : Set ℂ :=
  {z | z ∈ specDomain τ N ∧
    z.re ∈ Set.Icc (edgeVal N σ (2 * k) + τ') (edgeVal N σ (2 * k - 1) - τ')}

/-- `𝐃^o(τ,τ',N)`: `dist(E, supp ϱ) ≥ τ'` (§3.3). -/
def outsideDomain (τ τ' : ℝ) (N : ℕ) (σ : Fin M → ℝ) : Set ℂ :=
  {z | z ∈ specDomain τ N ∧ τ' ≤ Metric.infDist z.re (varrho N σ).support}

/-- `κ(E)`, the distance from `E` to the nearest edge `a_l`, `l = 1, …, 2p` ((def_kappa),
read on the critical values). -/
def kappa (N : ℕ) (σ : Fin M → ℝ) (E : ℝ) : ℝ :=
  ⨅ l : Finset.Icc 1 (2 * numBands N σ), |E - edgeVal N σ (l : ℕ)|

theorem spectralDomain_specDomain (τ : ℝ) (N : ℕ) : SpectralDomain τ N (specDomain τ N) :=
  ⟨subset_rfl, fun _ _ _ hw _ _ => hw⟩

theorem spectralDomain_edgeDomain (τ τ' : ℝ) (N : ℕ) (σ : Fin M → ℝ) (k : ℕ) :
    SpectralDomain τ N (edgeDomain τ τ' N σ k) :=
  ⟨fun _ hz => hz.1, fun z hz w hw hre _ => ⟨hw, by rw [hre]; exact hz.2⟩⟩

theorem spectralDomain_bulkDomain (τ τ' : ℝ) (N : ℕ) (σ : Fin M → ℝ) (k : ℕ) :
    SpectralDomain τ N (bulkDomain τ τ' N σ k) :=
  ⟨fun _ hz => hz.1, fun z hz w hw hre _ => ⟨hw, by rw [hre]; exact hz.2⟩⟩

theorem spectralDomain_outsideDomain (τ τ' : ℝ) (N : ℕ) (σ : Fin M → ℝ) :
    SpectralDomain τ N (outsideDomain τ τ' N σ) :=
  ⟨fun _ hz => hz.1, fun z hz w hw hre _ => ⟨hw, by rw [hre]; exact hz.2⟩⟩

/-- `𝐃(τ₂,N) ⊆ 𝐃(τ₁,N)` for `τ₁ ≤ τ₂`. -/
theorem specDomain_subset {τ₁ τ₂ : ℝ} (h₁ : 0 < τ₁) (h : τ₁ ≤ τ₂) {N : ℕ} (hN : 1 ≤ N) :
    specDomain τ₂ N ⊆ specDomain τ₁ N := by
  rintro z ⟨h0, hn, hre, hη, him⟩
  have hinv : τ₂⁻¹ ≤ τ₁⁻¹ := inv_anti₀ h₁ h
  refine ⟨h0, h.trans hn, hre.trans hinv, ?_, him.trans hinv⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  exact (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)).trans hη

/-! ### Elementary facts on the empirical measure -/

private lemma dom_empMeasure_apply (σ : Fin M → ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    empMeasure σ s = (M : ℝ≥0∞)⁻¹ * ((Finset.univ.filter fun i => σ i ∈ s).card : ℝ≥0∞) := by
  simp only [empMeasure, Measure.smul_apply, Measure.finsetSum_apply,
    Measure.dirac_apply' _ hs, smul_eq_mul]
  congr 1
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Set.indicator]

private lemma dom_empMeasure_ne_top (σ : Fin M → ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    empMeasure σ s ≠ ⊤ := by
  rw [dom_empMeasure_apply σ hs]
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    simp
  · refine ENNReal.mul_ne_top ?_ (ENNReal.natCast_ne_top _)
    rw [Ne, ENNReal.inv_eq_top]
    exact_mod_cast hM.ne'

/-- Consequences of `DensityAssumptions` used below: `N > 0` and some `σ i` is positive. -/
private lemma dom_facts {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) :
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
  rw [dom_empMeasure_apply σ measurableSet_Icc] at hgap
  simp only [hall, Set.mem_Icc, le_refl, h.pos.le, and_self, Finset.filter_true,
    Finset.card_univ, Fintype.card_fin] at hgap
  have hM' : (M : ℝ≥0∞)⁻¹ * (M : ℝ≥0∞) = 1 :=
    ENNReal.inv_mul_cancel (by exact_mod_cast hM) (ENNReal.natCast_ne_top _)
  rw [hM', ENNReal.toReal_one] at hgap
  linarith [h.pos]

/-- The assumptions weaken as `τ` decreases. -/
theorem DensityAssumptions.mono {τ τ₂ : ℝ} {N : ℕ} {σ : Fin M → ℝ}
    (h : DensityAssumptions τ N σ) (h₀ : 0 < τ₂) (h₂ : τ₂ ≤ τ) : DensityAssumptions τ₂ N σ := by
  have hinv : τ⁻¹ ≤ τ₂⁻¹ := inv_anti₀ h₀ h₂
  refine ⟨h₀, h.nonneg, h₂.trans h.phi_lower, h.phi_upper.trans hinv,
    fun i => (h.bound_Sigma i).trans hinv, ?_⟩
  have hmono : empMeasure σ (Set.Icc 0 τ₂) ≤ empMeasure σ (Set.Icc 0 τ) :=
    measure_mono (Set.Icc_subset_Icc le_rfl h₂)
  have hfin := dom_empMeasure_ne_top σ (measurableSet_Icc (a := (0 : ℝ)) (b := τ))
  have := (ENNReal.toReal_mono hfin hmono).trans h.Sigma_gap
  linarith

theorem kappa_nonneg (N : ℕ) (σ : Fin M → ℝ) (E : ℝ) : 0 ≤ kappa N σ E :=
  Real.iInf_nonneg fun _ => abs_nonneg _

/-- `κ ≤ C_κ = τ⁻¹ + 2τ⁻¹(1 + τ⁻¹)` for `|E| ≤ τ⁻¹`. -/
def kappaMax (τ : ℝ) : ℝ := τ⁻¹ + 2 * τ⁻¹ * (1 + τ⁻¹)

theorem kappa_le {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) {E : ℝ}
    (hE : |E| ≤ τ⁻¹) : kappa N σ E ≤ kappaMax τ := by
  obtain ⟨hN, hS⟩ := dom_facts h
  have hp := (card_innerCrit N σ h.nonneg hN hS).2
  have hmem : (1 : ℕ) ∈ Finset.Icc 1 (2 * numBands N σ) := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
  have ha := edgeVal_mem_Icc N σ h.nonneg hN hS h.pos h.phi_lower h.phi_upper h.bound_Sigma
    (k := 1) le_rfl (by omega)
  have h1 : kappa N σ E ≤ |E - edgeVal N σ 1| :=
    ciInf_le (f := fun l : Finset.Icc 1 (2 * numBands N σ) => |E - edgeVal N σ (l : ℕ)|)
      (Finite.bddBelow_range _) ⟨1, hmem⟩
  refine h1.trans ?_
  rw [kappaMax]
  obtain ⟨hE1, hE2⟩ := abs_le.1 hE
  obtain ⟨ha1, ha2⟩ := ha
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- `|m| ≍ 1` and `Im m ≥ c η` on `𝐃(τ,N)`: Lemma 4.10 at `τ/2`. -/
def mBoundConst (τ : ℝ) : ℝ := genPropConst (τ / 2)

theorem gen_prop_m_specDomain {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ)
    {z : ℂ} (hz : z ∈ specDomain τ N) :
    (mBoundConst τ)⁻¹ ≤ ‖mFun N σ z‖ ∧ ‖mFun N σ z‖ ≤ mBoundConst τ ∧
      (mBoundConst τ)⁻¹ * z.im ≤ (mFun N σ z).im := by
  obtain ⟨h0, hn, hre, -, him⟩ := hz
  have hhalf : 0 < τ / 2 := half_pos h.pos
  have h' : DensityAssumptions (τ / 2) N σ := h.mono hhalf (by linarith [h.pos])
  have hnorm : ‖z‖ ≤ (τ / 2)⁻¹ := by
    have h1 : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos h0] at h1
    have : (τ / 2)⁻¹ = 2 * τ⁻¹ := by rw [inv_div]; field_simp
    rw [this]
    linarith
  exact gen_prop_m h' h0 (by linarith [h.pos]) hnorm

/-- `z + i N⁻⁵`. -/
def shiftUp (N : ℕ) (z : ℂ) : ℂ := z + ((((N : ℝ) ^ 5)⁻¹ : ℝ) : ℂ) * Complex.I

theorem shiftUp_mem {τ : ℝ} {N : ℕ} {S : Set ℂ} (hS : SpectralDomain τ N S) {z : ℂ}
    (hz : z ∈ S) (h : z.im + ((N : ℝ) ^ 5)⁻¹ ≤ τ⁻¹) : shiftUp N z ∈ S := by
  obtain ⟨h0, hn, hre, hη, him⟩ := hS.1 hz
  have hre' : (shiftUp N z).re = z.re := by
    rw [shiftUp, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have him' : (shiftUp N z).im = z.im + ((N : ℝ) ^ 5)⁻¹ := by
    rw [shiftUp, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have hpos : 0 ≤ ((N : ℝ) ^ 5)⁻¹ := by positivity
  have hle : z.im ≤ (shiftUp N z).im := by rw [him']; linarith
  have hnorm : ‖z‖ ≤ ‖shiftUp N z‖ := by
    by_contra hc
    rw [not_le] at hc
    have hsq := pow_lt_pow_left₀ hc (norm_nonneg _) (two_ne_zero)
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply, hre'] at hsq
    nlinarith
  refine hS.2 z hz _ ⟨by linarith, hn.trans hnorm, by rw [hre']; exact hre, ?_, ?_⟩ hre' hle
  · exact hη.trans hle
  · rw [him']; exact h

/-! ## Instance -/

/-- MP, `τ = 1/20`, `N = 200`: the point `2.9 + i` of `𝐃^e_1` lies in `𝐃(τ,N)`. -/
example : (⟨29 / 10, 1⟩ : ℂ) ∈ specDomain (1 / 20) 200 := by
  refine ⟨by norm_num, ?_, by norm_num, ?_, by norm_num⟩
  · calc (1 / 20 : ℝ) ≤ |(⟨29 / 10, 1⟩ : ℂ).re| := by norm_num
      _ ≤ ‖(⟨29 / 10, 1⟩ : ℂ)‖ := Complex.abs_re_le_norm _
  · exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)

/-- MP, `τ = 1/20`, `τ' = 1/10`: `SpectralDomain` of `𝐃`. -/
example : SpectralDomain (1 / 20) 2 (specDomain (1 / 20) 2) := spectralDomain_specDomain _ _

/-- `κ ≥ 0` at MP, `E = 2.9`. -/
example : 0 ≤ kappa 2 (fun _ : Fin 1 => (1 : ℝ)) (29 / 10) := kappa_nonneg _ _ _

end Anisotropic
