import Anisotropic.Density.Count
import Anisotropic.EdgeUniv.CompareQ
import Anisotropic.EdgeUniv.Defs
import Anisotropic.EdgeUniv.Invariance
import Anisotropic.EdgeUniv.Reduction
import Anisotropic.EdgeUniv.RegimeQ
import Anisotropic.Entrywise.DiagModel
import Anisotropic.Framework.Domination
import Anisotropic.Framework.Model
import Anisotropic.GeneralT.Spectra
import Anisotropic.Instances.MarchenkoPastur
import Anisotropic.Instances.Models

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # Theorem 3.18 under (T_diag): bounded Lipschitz test functions with rate, bounded uniformly continuous test functions -/

/-! ## Deterministic facts at a regular edge -/

/-- (phi_bounded) and (Sigma_gap) give `N > 0` and some positive `σ i`. -/
private lemma main_facts {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) :
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
  refine ⟨hN, ?_⟩
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

/-- The radius `r(τ) = min(τ₀(τ), τ/2)` of the window next to a regular edge. -/
private def mainR (τ : ℝ) : ℝ := min (edgeTau0 τ) (τ / 2)

/-- The constant `c(τ) = π⁻¹ √(r/(2 C₂(τ))) · r/2`: a lower bound for `N_{k̂}/N` at a regular
edge `k`. -/
private def mainC (τ : ℝ) : ℝ := √(mainR τ / 2 / edgeC2 τ) / Real.pi * (mainR τ / 2)

private lemma main_pos {τ : ℝ} (hτ : 0 < τ) : 0 < edgeTau0 τ ∧ 0 < edgeC2 τ := by
  have hcx : 0 < edgecx τ := by unfold edgecx; positivity
  have hCx : 0 < edgeCx τ := by unfold edgeCx; positivity
  have hc2 : 0 < edgec2 τ := by unfold edgec2; positivity
  have hC3 : 0 < edgeC3 τ := by unfold edgeC3; positivity
  have hr0 : 0 < edgeRho0 τ := by unfold edgeRho0; positivity
  have hr1 : 0 < edgeRho1 τ := by unfold edgeRho1; positivity
  exact ⟨by unfold edgeTau0; positivity, by unfold edgeC2; positivity⟩

private lemma mainR_pos {τ : ℝ} (hτ : 0 < τ) : 0 < mainR τ :=
  lt_min (main_pos hτ).1 (by linarith)

private lemma mainC_pos {τ : ℝ} (hτ : 0 < τ) : 0 < mainC τ := by
  have hr := mainR_pos hτ
  have hC := (main_pos hτ).2
  have hs : 0 < √(mainR τ / 2 / edgeC2 τ) := Real.sqrt_pos.2 (by positivity)
  unfold mainC
  have := Real.pi_pos
  positivity

/-- `0 < r₀(τ) = min(τ'/2, τ/2)`. -/
private lemma main_edgeR0_pos {τ : ℝ} (hτ : 0 < τ) : 0 < edgeR0 τ := by
  have h := (main_pos hτ).1
  have : 0 < edgeTau' τ := by unfold edgeTau'; positivity
  exact lt_min (half_pos this) (half_pos hτ)

/-- If `ρ ≥ c₀` on `[x, y) ⊆ [a_{2j}, a_{2j−1}]` with `0 < x ≤ y`, then `N_j ≥ N c₀ (y − x)`. -/
private lemma main_bandCount_ge_of {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    {j : ℕ} {x y c₀ : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hc₀ : 0 ≤ c₀)
    (hsub : Set.Ico x y ⊆ Set.Icc (edgeVal N σ (2 * j)) (edgeVal N σ (2 * j - 1)))
    (hρ : ∀ u ∈ Set.Ico x y, c₀ ≤ rhoDens N σ u) :
    N * c₀ * (y - x) ≤ bandCount N σ j := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  have hpos : Set.Ico x y ⊆ Set.Ioi 0 := fun u hu => lt_of_lt_of_le hx hu.1
  have h0 : (0 : ℝ) ∉ Set.Ico x y := fun h => lt_irrefl (0 : ℝ) (Set.mem_Ioi.mp (hpos h))
  have happ : varrho N σ (Set.Ico x y) = ∫⁻ u in Set.Ico x y, ENNReal.ofReal (rhoDens N σ u) := by
    rw [varrho, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ measurableSet_Ico,
      Set.indicator_of_notMem h0, smul_zero, zero_add, withDensity_apply _ measurableSet_Ico,
      Measure.restrict_restrict measurableSet_Ico, Set.inter_eq_left.mpr hpos]
  have hge : ENNReal.ofReal (c₀ * (y - x)) ≤ varrho N σ (Set.Ico x y) := by
    rw [happ]
    calc ENNReal.ofReal (c₀ * (y - x))
        = ∫⁻ u in Set.Ico x y, ENNReal.ofReal c₀ := by
          rw [setLIntegral_const, Real.volume_Ico, ENNReal.ofReal_mul hc₀]
      _ ≤ ∫⁻ u in Set.Ico x y, ENNReal.ofReal (rhoDens N σ u) :=
          setLIntegral_mono' measurableSet_Ico fun u hu =>
            ENNReal.ofReal_le_ofReal (hρ u hu)
  have h1 : c₀ * (y - x) ≤ (varrho N σ (Set.Ico x y)).toReal := by
    have := ENNReal.toReal_mono (measure_ne_top _ _) hge
    rwa [ENNReal.toReal_ofReal (mul_nonneg hc₀ (by linarith))] at this
  have h2 : (varrho N σ (Set.Ico x y)).toReal ≤
      (varrho N σ (Set.Icc (edgeVal N σ (2 * j)) (edgeVal N σ (2 * j - 1)))).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  unfold bandCount
  calc (N : ℝ) * c₀ * (y - x) = N * (c₀ * (y - x)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (h1.trans h2) hN0

/-- At a regular edge `k`, `N_{k̂} ≥ c(τ) N` with `k̂ = ⌈k/2⌉` (square-root density on the band
side, Lemma A.4). -/
private lemma main_bandCount_edge {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ)
    {k : ℕ} (hk : RegularEdge τ N σ k) : N * mainC τ ≤ bandCount N σ ((k + 1) / 2) := by
  obtain ⟨hN, hS⟩ := main_facts h
  have hτ := h.pos
  obtain ⟨hk1, hk2, hτa, hsep, -⟩ := id hk
  have hr := mainR_pos hτ
  have hr1 : mainR τ ≤ edgeTau0 τ := min_le_left _ _
  have hr2 : mainR τ ≤ τ / 2 := min_le_right _ _
  have hC := (main_pos hτ).2
  set r := mainR τ with hrdef
  set a := edgeVal N σ k with hadef
  have hc₀ : 0 ≤ √(r / 2 / edgeC2 τ) / Real.pi := by have := Real.pi_pos; positivity
  have hdens : ∀ u, r / 2 ≤ |u - a| → |u - a| ≤ r → (-1 : ℝ) ^ (k + 1) * (u - a) ≤ 0 →
      √(r / 2 / edgeC2 τ) / Real.pi ≤ rhoDens N σ u := by
    intro u hu1 hu2 hside
    have hρ := ((rhoDens_edge h hk (hu2.trans hr1)).1 hside).1
    have hmono : √(r / 2 / edgeC2 τ) ≤ √(|u - a| / edgeC2 τ) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hu1 hC.le)
    rw [div_le_iff₀ Real.pi_pos]
    linarith
  have hσ := h.nonneg
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- even `k = 2m`: the lower edge of the band `m`, window `[a_k + r/2, a_k + r)`
    have hj : (k + 1) / 2 = m := by omega
    have hkm1 : 1 ≤ k - 1 := by omega
    have hsucc := edgeVal_succ_le N σ hσ hN hS hkm1 (by omega)
    rw [show k - 1 + 1 = k by omega] at hsucc
    have hs := hsep (k - 1) hkm1 (by omega) (by omega)
    rw [abs_of_nonpos (by linarith)] at hs
    have hsign : (-1 : ℝ) ^ (k + 1) = -1 := Odd.neg_one_pow ⟨m, by omega⟩
    have hb := main_bandCount_ge_of (N := N) (σ := σ) (j := m) hσ hN (x := a + r / 2)
      (y := a + r) (by linarith) (by linarith) hc₀ (fun u hu => by
        rw [show 2 * m = k by omega, ← hadef]
        exact ⟨by linarith [hu.1], by linarith [hu.2]⟩)
      (fun u hu => by
        have h1 : |u - a| = u - a := abs_of_nonneg (by linarith [hu.1])
        refine hdens u (by rw [h1]; linarith [hu.1]) (by rw [h1]; linarith [hu.2]) ?_
        rw [hsign]
        linarith [hu.1])
    rw [hj]
    unfold mainC
    linarith
  · -- odd `k = 2m + 1`: the upper edge of the band `m + 1`, window `[a_k − r, a_k − r/2)`
    have hj : (k + 1) / 2 = m + 1 := by omega
    have hsucc := edgeVal_succ_le N σ hσ hN hS hk1 (by omega)
    have hs := hsep (k + 1) (by omega) (by omega) (by omega)
    rw [abs_of_nonneg (by linarith)] at hs
    have hsign : (-1 : ℝ) ^ (k + 1) = 1 := Even.neg_one_pow ⟨m + 1, by omega⟩
    have hb := main_bandCount_ge_of (N := N) (σ := σ) (j := m + 1) hσ hN (x := a - r)
      (y := a - r / 2) (by linarith) (by linarith) hc₀ (fun u hu => by
        rw [show 2 * (m + 1) = k + 1 by omega, show k + 1 - 1 = k by omega, ← hadef]
        exact ⟨by linarith [hu.1], by linarith [hu.2]⟩)
      (fun u hu => by
        have h1 : |u - a| = a - u := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith [hu.2])
        refine hdens u (by rw [h1]; linarith [hu.2]) (by rw [h1]; linarith [hu.1]) ?_
        rw [hsign]
        linarith [hu.2])
    rw [hj]
    unfold mainC
    linarith

/-- At a regular edge the component `k̂ = ⌈k/2⌉` holds at least `l` classical eigenvalues and
`d_{k̂} ≤ N`, for `N ≥ N₀(τ, l)`. -/
private lemma main_cumCount_window (τ : ℝ) (l : ℕ) (hτ : 0 < τ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (σ : Fin M → ℝ), DensityAssumptions τ N σ →
      ∀ k, RegularEdge τ N σ k →
        cumCount N σ ((k + 1) / 2 - 1) + l ≤ cumCount N σ ((k + 1) / 2) ∧
          cumCount N σ ((k + 1) / 2) ≤ N := by
  have hc := mainC_pos hτ
  refine ⟨⌈(l : ℝ) / mainC τ⌉₊, fun N hN M σ hda k hk => ?_⟩
  obtain ⟨hN0, hS⟩ := main_facts hda
  have hp1 : 1 ≤ (k + 1) / 2 := by have := hk.1; omega
  have hp2 : (k + 1) / 2 ≤ numBands N σ := by have := hk.2.1; omega
  obtain ⟨hc1, hb, hrel⟩ := cumCount_spec hda hp1 hp2
  have hband := main_bandCount_edge hda hk
  have hl : (l : ℝ) ≤ N * mainC τ := by
    have h1 : (l : ℝ) / mainC τ ≤ N := Nat.ceil_le.1 hN
    rw [div_le_iff₀ hc] at h1
    exact h1
  constructor
  · rw [← hrel]
    have : (l : ℝ) ≤ bandNat N σ ((k + 1) / 2) := by rw [hb]; linarith
    have : l ≤ bandNat N σ ((k + 1) / 2) := by exact_mod_cast this
    omega
  · have hsum := sum_bandCount N σ hda.nonneg hN0 hS
    have hnn : ∀ j ∈ Finset.Icc 1 (numBands N σ), j ∉ Finset.Icc 1 ((k + 1) / 2) →
        0 ≤ bandCount N σ j := fun j _ _ => by unfold bandCount; positivity
    have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := fun j => bandCount N σ j)
      (Finset.Icc_subset_Icc le_rfl hp2) hnn
    have : (cumCount N σ ((k + 1) / 2) : ℝ) ≤ N := by
      rw [hc1]
      exact hle.trans (hsum.le.trans (min_le_left _ _))
    exact_mod_cast this

/-- `Q_N = Xᵀ Σ X` and `±Q_N` are symmetric for symmetric `Σ`. -/
private lemma main_QN_herm {Sig : Matrix (Fin M) (Fin M) ℝ} (hS : Sig.IsHermitian)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (c : ℝ) : (c • QN Sig Xm).IsHermitian := by
  have h := Matrix.isHermitian_conjTranspose_mul_mul Xm hS
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h.smul (IsSelfAdjoint.all c)

/-- `Xm ↦ c Q_N` is continuous. -/
private lemma main_continuous_QN (Sig : Matrix (Fin M) (Fin M) ℝ) (c : ℝ) :
    Continuous fun Xm : Matrix (Fin M) (Fin N) ℝ => c • QN Sig Xm := by
  unfold QN
  fun_prop

/-! ## Two analytic facts -/

/-- On a probability space, `|E f(Y) - E g(Y)| ≤ δ` for bounded measurable `f, g` with
`|f - g| ≤ δ`. -/
private lemma main_integral_sub_le {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {l : ℕ} {Y : Ω → Fin l → ℝ} (hY : Measurable Y)
    {f g : (Fin l → ℝ) → ℝ} (hf : Measurable f) (hg : Measurable g) {B δ : ℝ}
    (hfB : ∀ x, |f x| ≤ B) (hgB : ∀ x, |g x| ≤ B) (hfg : ∀ x, |f x - g x| ≤ δ) :
    |(∫ ω, f (Y ω)) - ∫ ω, g (Y ω)| ≤ δ := by
  have hfi : Integrable (fun ω => f (Y ω)) :=
    Integrable.of_bound (hf.comp hY).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hfB _)
  have hgi : Integrable (fun ω => g (Y ω)) :=
    Integrable.of_bound (hg.comp hY).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hgB _)
  rw [← integral_sub hfi hgi]
  have := norm_integral_le_of_norm_le_const (μ := (ℙ : Measure Ω))
    (f := fun ω => f (Y ω) - g (Y ω)) (C := δ)
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hfg _)
  rwa [Real.norm_eq_abs, probReal_univ, mul_one] at this

/-- The rate `K (B + L) N^{-1/(800(l+1))}` is eventually at most `ε`. -/
private lemma main_rate_eventually (K B : ℝ) (L : ℝ≥0) (l : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, K * (B + L) * (N : ℝ) ^ (-(1 / (800 * (l + 1)) : ℝ)) ≤ ε := by
  have hθ : (0 : ℝ) < 1 / (800 * (l + 1)) := by positivity
  have ht : Tendsto (fun N : ℕ => K * (B + L) * (N : ℝ) ^ (-(1 / (800 * (l + 1)) : ℝ)))
      atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop hθ).comp tendsto_natCast_atTop_atTop).const_mul
      (K * (B + L))
    simpa using this
  exact eventually_atTop.mp (ht.eventually (ge_mem_nhds hε))

/-! ## Theorem 3.18 -/

/-- Theorem 3.18 (`thm:edge_univ`) under (T_diag), bounded Lipschitz `h`, with rate. -/
theorem edge_univ_lip (τ : ℝ) (C : ℕ → ℝ) (l : ℕ) (hτ : 0 < τ) :
    ∃ K : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)] (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (X : Ω → Matrix (Fin M) (Fin N) ℝ) (k : ℕ),
      IsModel τ C M N Sig X → RegularEdge τ N (specOf Sig) k →
      ∀ (h : (Fin l → ℝ) → ℝ) (B : ℝ) (L : ℝ≥0), (∀ x, |h x| ≤ B) → LipschitzWith L h →
        |(∫ ω, h (qVec Sig (X ω) k l)) - bRef N (specOf Sig) k l h| ≤
          K * (B + L) * (N : ℝ) ^ (-(1 / (800 * (l + 1)) : ℝ)) := by
  have hε : (0 : ℝ) < 1 / 200 := by norm_num
  have hl0 : (0 : ℝ) < l + 1 := by positivity
  have hδ : (0 : ℝ) < 1 / 200 / (8 * (l + 1)) := by positivity
  have hδ1 : (1 / 200 : ℝ) / (8 * (l + 1)) < 2 / 3 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  obtain ⟨N₁, h₁⟩ := edgeRegime_Q τ C l (1 / 200 / (8 * (l + 1))) 1 hτ hδ hδ1
  obtain ⟨N₂, h₂⟩ := edgeRegime_Q τ gaussMoment l (1 / 200 / (8 * (l + 1))) 1 hτ hδ hδ1
  obtain ⟨N₃, h₃⟩ := smoothComparable_Q τ C l (1 / 200) hτ hε le_rfl
  obtain ⟨N₄, h₄⟩ := main_cumCount_window τ l hτ
  have hc₂ := edgec2_pos hτ
  have hϖm : 0 < (edgec2 τ / 2) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have hKc : 1 ≤ edgeKc τ := by
    have : 0 ≤ 4 / (3 * Real.pi * Real.sqrt (edgec2 τ)) := by positivity
    unfold edgeKc
    linarith
  obtain ⟨K, N₅, h₅⟩ := edge_reduction l (1 / 200) (1 / 6 - 25 * (1 / 200))
    ((edgec2 τ / 2) ^ (1 / 3 : ℝ))
    (max ((edgec2 τ / 2) ^ (1 / 3 : ℝ)) ((edgeC2 τ / 2) ^ (1 / 3 : ℝ))) (edgeKc τ) (edgeR0 τ)
    hε le_rfl (by norm_num) hϖm (le_max_left _ _) (by linarith) (main_edgeR0_pos hτ)
  refine ⟨K, max (max (max N₁ N₂) (max N₃ N₄)) (max N₅ 1), ?_⟩
  intro N hN Ω _ _ M Sig X k hm hk h B L hB hL
  have hNa : max (max N₁ N₂) (max N₃ N₄) ≤ N := le_of_max_le_left hN
  have hNb : max N₅ 1 ≤ N := le_of_max_le_right hN
  have hN1 : N₁ ≤ N := le_of_max_le_left (le_of_max_le_left hNa)
  have hN2 : N₂ ≤ N := le_of_max_le_right (le_of_max_le_left hNa)
  have hN3 : N₃ ≤ N := le_of_max_le_left (le_of_max_le_right hNa)
  have hN4 : N₄ ≤ N := le_of_max_le_right (le_of_max_le_right hNa)
  have hN5 : N₅ ≤ N := le_of_max_le_left hNb
  have hN0 : 1 ≤ N := le_of_max_le_right hNb
  have hda : DensityAssumptions τ N (specOf Sig) := hm.diagModel_specOf.densityAssumptions hτ
  have hg : IsModel τ gaussMoment M N Sig (gaussX M N) :=
    isModel_gaussX hN0 hm.ratio_ge hm.ratio_le hm.sigma
  obtain ⟨hw1, hw2⟩ := h₄ N hN4 M (specOf Sig) hda k hk
  obtain ⟨_, hϖ1, hϖ2⟩ := edgeScale_bounds hda hk
  have hϖI : edgeScale N (specOf Sig) k ∈ Set.Icc ((edgec2 τ / 2) ^ (1 / 3 : ℝ))
      (max ((edgec2 τ / 2) ^ (1 / 3 : ℝ)) ((edgeC2 τ / 2) ^ (1 / 3 : ℝ))) := by
    have he : edgeScale N (specOf Sig) k = (edgeScale N (specOf Sig) k ^ 3) ^ (1 / 3 : ℝ) := by
      rw [edgeScale_cube]
      rfl
    rw [he]
    exact ⟨Real.rpow_le_rpow (by positivity) hϖ1 (by norm_num),
      (Real.rpow_le_rpow (by linarith) hϖ2 (by norm_num)).trans (le_max_right _ _)⟩
  have hSH : Sig.IsHermitian := hm.sigma.posDef.isHermitian
  have hQ : ∀ Xm : Matrix (Fin M) (Fin N) ℝ, qVec Sig Xm k l =
      edgeQ N (edgeSign k * edgeVal N (specOf Sig) k) (edgeScale N (specOf Sig) k)
        (edgeD N (specOf Sig) k) l (edgeSign k • QN Sig Xm) := fun Xm => by
    have := main_QN_herm hSH Xm 1
    rw [one_smul] at this
    exact qVecA_eq_edgeQ this hw1 hw2
  have hXm : Measurable X :=
    measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun μ => hm.entries.measurable i μ
  have hGm : Measurable (gaussX M N) := (gaussX_isGaussianEnsemble M N).measurable_mat
  have hnC : (N : ℝ) ≤ edgeKc τ * N := by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  have key := h₅ N hN5 N (edgeD N (specOf Sig) k) (edgeSign k * edgeVal N (specOf Sig) k)
    (edgeScale N (specOf Sig) k) hnC hϖI (fun ω => edgeSign k • QN Sig (X ω))
    (fun ω => edgeSign k • QN Sig (gaussX M N ω))
    ((main_continuous_QN Sig (edgeSign k)).measurable.comp hXm)
    ((main_continuous_QN Sig (edgeSign k)).measurable.comp hGm)
    (fun ω => main_QN_herm hSH (X ω) _) (fun ω => main_QN_herm hSH (gaussX M N ω) _)
    (h₁ N hN1 M Sig X k hm hk) (h₂ N hN2 M Sig (gaussX M N) k hg hk)
    (h₃ N hN3 M Sig X k hm hk) h B L hB hL
  rw [← bRef_gauss hm.sigma.posDef N k l hL.continuous.measurable]
  simp_rw [hQ]
  have hexp : (1 / 200 : ℝ) / (4 * (l + 1)) = 1 / (800 * (l + 1)) := by
    field_simp
    ring
  rw [hexp] at key
  exact key

/-- Theorem 3.18 (`thm:edge_univ`) under (T_diag), bounded uniformly continuous `h`. -/
theorem edge_univ (τ : ℝ) (C : ℕ → ℝ) (l : ℕ) (h : (Fin l → ℝ) → ℝ) (ε : ℝ) (hτ : 0 < τ)
    (hb : ∃ B, ∀ x, |h x| ≤ B) (hu : UniformContinuous h) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (k : ℕ),
      IsModel τ C M N Sig X → RegularEdge τ N (specOf Sig) k →
      |(∫ ω, h (qVec Sig (X ω) k l)) - bRef N (specOf Sig) k l h| ≤ ε := by
  obtain ⟨B, hB⟩ := hb
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨g, L, hgL, hgB, hhg⟩ := exists_lipschitz_approx hB hu hε3
  obtain ⟨K, N₀, hK⟩ := edge_univ_lip τ C l hτ
  obtain ⟨N₁, hN₁⟩ := main_rate_eventually K B L l hε3
  refine ⟨max N₀ N₁, fun N hN Ω _ _ M Sig X k hm hk => ?_⟩
  have hhm : Measurable h := hu.continuous.measurable
  have hgm : Measurable g := hgL.continuous.measurable
  have hXm : Measurable X :=
    measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun μ => hm.entries.measurable i μ
  have hGm : Measurable (gaussX M N) := (gaussX_isGaussianEnsemble M N).measurable_mat
  have hY : Measurable fun ω => qVec Sig (X ω) k l := by
    have := (main_continuous_QN (N := N) Sig 1).measurable
    simp only [one_smul] at this
    exact (measurable_qVecA N (specOf Sig) N k l).comp (this.comp hXm)
  have hY0 : Measurable fun ω =>
      qVecA N (specOf Sig) (QN (diagonal (specOf Sig)) (gaussX M N ω)) k l := by
    have := (main_continuous_QN (N := N) (diagonal (specOf Sig)) 1).measurable
    simp only [one_smul] at this
    exact (measurable_qVecA N (specOf Sig) N k l).comp (this.comp hGm)
  have e1 := main_integral_sub_le hY hhm hgm hB hgB hhg
  have e2 := (hK N (le_of_max_le_left hN) M Sig X k hm hk g B L hgB hgL).trans
    (hN₁ N (le_of_max_le_right hN))
  have e3 : |bRef N (specOf Sig) k l g - bRef N (specOf Sig) k l h| ≤ ε / 3 := by
    unfold bRef
    exact main_integral_sub_le hY0 hgm hhm hgB hB (fun x => by rw [abs_sub_comm]; exact hhg x)
  have := abs_add_three ((∫ ω, h (qVec Sig (X ω) k l)) - ∫ ω, g (qVec Sig (X ω) k l))
    ((∫ ω, g (qVec Sig (X ω) k l)) - bRef N (specOf Sig) k l g)
    (bRef N (specOf Sig) k l g - bRef N (specOf Sig) k l h)
  rw [sub_add_sub_cancel, sub_add_sub_cancel] at this
  linarith

/-- Theorem 3.18, the paper's form: there is `b_N(h, π)`, depending only on `N` and the
nonzero eigenvalues of `Σ` with multiplicity, such that `E h(q_{k,l}) - b_N(h, π) → 0` along
every sequence of models with `N → ∞` and the edge `k_n` regular. -/
example (τ : ℝ) (C : ℕ → ℝ) (l : ℕ) (h : (Fin l → ℝ) → ℝ) (hτ : 0 < τ)
    (hb : ∃ B, ∀ x, |h x| ≤ B) (hu : UniformContinuous h) :
    ∃ b : (N : ℕ) → (M : ℕ) → (Fin M → ℝ) → ℕ → ℝ,
      (∀ (N M M' : ℕ) (σ : Fin M → ℝ) (σ' : Fin M' → ℝ) (k : ℕ), NzEq σ σ' →
          (∀ i, 0 ≤ σ i) → (∀ j, 0 ≤ σ' j) → b N M σ k = b N M' σ' k) ∧
      ∀ (Ω : ℕ → Type) [∀ n, MeasureSpace (Ω n)] [∀ n, IsProbabilityMeasure (ℙ : Measure (Ω n))]
        (Ms Ns : ℕ → ℕ) (Sig : ∀ n, Matrix (Fin (Ms n)) (Fin (Ms n)) ℝ)
        (X : ∀ n, Ω n → Matrix (Fin (Ms n)) (Fin (Ns n)) ℝ) (k : ℕ → ℕ),
        Tendsto Ns atTop atTop →
        (∀ n, IsModel τ C (Ms n) (Ns n) (Sig n) (X n)) →
        (∀ n, RegularEdge τ (Ns n) (specOf (Sig n)) (k n)) →
        Tendsto (fun n => (∫ ω, h (qVec (Sig n) (X n ω) (k n) l)) -
          b (Ns n) (Ms n) (specOf (Sig n)) (k n)) atTop (𝓝 0) := by
  refine ⟨fun N M σ k => bRef N σ k l h, fun N M M' σ σ' k hz hσ hσ' =>
    bRef_nzEq hz hσ hσ' N k l hu.continuous.measurable, ?_⟩
  intro Ω _ _ Ms Ns Sig X k hNs hm hk
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := edge_univ τ C l h (ε / 2) hτ hb hu (half_pos hε)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hNs.eventually_ge_atTop N₀)
  refine ⟨n₀, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero]
  exact (hN₀ (Ns n) (hn₀ n hn) (Ms n) (Sig n) (X n) (k n) (hm n) (hk n)).trans_lt
    (half_lt_self hε)

/-- The hypotheses of Theorem 3.18 hold together at the Marchenko–Pastur point, for every `n ≥ 1`. -/
example {n : ℕ} (hn : 0 < n) :
    IsModel (Ω := SignSpace (Fin n × Fin (2 * n))) (1 / 5) (fun _ => 1) n (2 * n) 1 (radXn n) ∧
      RegularEdge (1 / 5) (2 * n) (specOf (1 : Matrix (Fin n) (Fin n) ℝ)) 1 := by
  refine ⟨isModel_radXn hn, ?_⟩
  rw [specOf_one_eq]
  exact regularEdge_mp hn

/-- The constants of the reduction for Theorem 3.18 (`ε = 1/200`, `c₁ = 1/6 - 25ε = 1/24`) satisfy
its side conditions, and the rate exponent is `ε/(4(l+1)) = 1/(800(l+1))`. -/
example (l : ℕ) :
    (0 : ℝ) < 1 / 200 ∧ (1 / 200 : ℝ) ≤ 1 / 200 ∧ (1 / 200 : ℝ) ≤ 1 / 6 - 25 * (1 / 200) ∧
      (1 / 200 : ℝ) / (4 * (l + 1)) = 1 / (800 * (l + 1)) ∧
      9 * (1 / 200 : ℝ) + 1 / 6 < 1 / 3 := by
  refine ⟨by norm_num, le_rfl, by norm_num, ?_, by norm_num⟩
  have : (0 : ℝ) < l + 1 := by positivity
  field_simp
  ring

/-- The clamp `x ↦ max(-1, min(x₁, 1))` is bounded by `1` and `1`-Lipschitz. -/
private theorem clamp_bounded_lipschitz :
    (∀ x : Fin 1 → ℝ, |max (-1) (min (x 0) 1)| ≤ 1) ∧
      LipschitzWith 1 (fun x : Fin 1 → ℝ => max (-1) (min (x 0) 1)) := by
  refine ⟨fun x => abs_le.2 ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩, ?_⟩
  exact ((LipschitzWith.eval (α := fun _ : Fin 1 => ℝ) 0).min_const 1).const_max (-1)

/-- Theorem 3.18 at the Marchenko–Pastur point for the clamp of the top eigenvalue
(`l = 1`, `k = 1`). -/
example : ∃ K : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, 0 < n → N₀ ≤ 2 * n →
    |(∫ ω, max (-1) (min (qVec (1 : Matrix (Fin n) (Fin n) ℝ) (radXn n ω) 1 1 0) 1)) -
        bRef (2 * n) (specOf (1 : Matrix (Fin n) (Fin n) ℝ)) 1 1
          (fun x => max (-1) (min (x 0) 1))| ≤
      K * (1 + 1) * ((2 * n : ℕ) : ℝ) ^ (-(1 / (800 * (1 + 1)) : ℝ)) := by
  obtain ⟨K, N₀, h⟩ := edge_univ_lip (1 / 5) (fun _ => 1) 1 (by norm_num)
  refine ⟨K, N₀, fun n hn hN => ?_⟩
  have hk : RegularEdge (1 / 5) (2 * n) (specOf (1 : Matrix (Fin n) (Fin n) ℝ)) 1 := by
    rw [specOf_one_eq]; exact regularEdge_mp hn
  have := h (2 * n) hN n 1 (radXn n) 1 (isModel_radXn hn) hk
    (fun x => max (-1) (min (x 0) 1)) 1 1 clamp_bounded_lipschitz.1 clamp_bounded_lipschitz.2
  simpa using this

/-- The sequence hypotheses of the paper's form hold together along the Marchenko–Pastur
family `M_n = n + 1`, `N_n = 2(n + 1)`, `Σ_n = 1`, Rademacher entries, `k_n = 1`, `τ = 1/5`,
`C ≡ 1`. -/
example :
    Tendsto (fun n : ℕ => 2 * (n + 1)) atTop atTop ∧
      (∀ n : ℕ, IsModel (Ω := SignSpace (Fin (n + 1) × Fin (2 * (n + 1)))) (1 / 5) (fun _ => 1)
        (n + 1) (2 * (n + 1)) 1 (radXn (n + 1))) ∧
      ∀ n : ℕ, RegularEdge (1 / 5) (2 * (n + 1))
        (specOf (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) 1 := by
  refine ⟨tendsto_atTop_mono (fun n => show n ≤ 2 * (n + 1) by omega) tendsto_id,
    fun n => isModel_radXn n.succ_pos, fun n => ?_⟩
  rw [specOf_one_eq]
  exact regularEdge_mp n.succ_pos

/-- Theorem 3.18 for bounded uniformly continuous `h` at the Marchenko–Pastur point, for the
clamp of the top eigenvalue (`l = 1`, `k = 1`) and the precision `ε = 1/10`. -/
example : ∃ N₀ : ℕ, ∀ n : ℕ, 0 < n → N₀ ≤ 2 * n →
    |(∫ ω, max (-1) (min (qVec (1 : Matrix (Fin n) (Fin n) ℝ) (radXn n ω) 1 1 0) 1)) -
        bRef (2 * n) (specOf (1 : Matrix (Fin n) (Fin n) ℝ)) 1 1
          (fun x => max (-1) (min (x 0) 1))| ≤ 1 / 10 := by
  obtain ⟨N₀, h⟩ := edge_univ (1 / 5) (fun _ => 1) 1 (fun x => max (-1) (min (x 0) 1)) (1 / 10)
    (by norm_num) ⟨1, clamp_bounded_lipschitz.1⟩ clamp_bounded_lipschitz.2.uniformContinuous
    (by norm_num)
  refine ⟨N₀, fun n hn hN => ?_⟩
  have hk : RegularEdge (1 / 5) (2 * n) (specOf (1 : Matrix (Fin n) (Fin n) ℝ)) 1 := by
    rw [specOf_one_eq]; exact regularEdge_mp hn
  exact h (2 * n) hN n 1 (radXn n) 1 (isModel_radXn hn) hk

#print axioms edge_univ_lip
#print axioms edge_univ

end Anisotropic
