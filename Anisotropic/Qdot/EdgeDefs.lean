import Anisotropic.Density.Basic
import Anisotropic.Density.Count
import Anisotropic.Density.Critical
import Anisotropic.Density.GenProp
import Anisotropic.Density.Stability.EdgeTaylor
import Anisotropic.EdgeUniv.Defs
import Anisotropic.Entrywise.Defs
import Anisotropic.Entrywise.DiagModel
import Anisotropic.Framework.Domination
import Anisotropic.GeneralT.Spectra
import Anisotropic.Instances.MarchenkoPasturTwo
import Anisotropic.Qdot.Classical
import Anisotropic.Qdot.Defs
import Anisotropic.Rigidity.Defs

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # The rescaled extreme eigenvalues of `Q̇` at the partner edge of the `N − 1` data, the partner index, and the window lemmas -/

/-- `q̇_{k,l}` with the classical quantities of `N − 1` samples:
`q̇_{2j−1,l} = (N−1)^{2/3} ϖ̇⁻¹ (λ̇_{j,i} − ȧ_{2j−1})_{i ≤ l}` and
`q̇_{2j,l} = −(N−1)^{2/3} ϖ̇⁻¹ (λ̇_{j,Ṅ_j+1−i} − ȧ_{2j})_{i ≤ l}`, from the eigenvalues of the
`N × N` companion of `Q̇`. -/
def qDotVec (Sig : Matrix (Fin M) (Fin M) ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (k l : ℕ) :
    Fin l → ℝ :=
  qVecA (N - 1) (specOf Sig) (QdotN Sig Xm) k l

/-- `q̇_{k,l}` for a general `T`, with the classical quantities of `Σ = T Tᵀ` at `N − 1`. -/
def qDotVecT {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ) (Xm : Matrix (Fin K) (Fin N) ℝ) (k l : ℕ) :
    Fin l → ℝ :=
  qVecA (N - 1) (specOf (T * Tᵀ)) (QdotNT T Xm) k l

/-- The partner for `N − 1` samples of the edge `k` for `N` samples: an index `j ≤ 2ṗ` of the
parity of `k` minimising `|ȧ_j − a_k|` (`k` itself if there is no such index). -/
def edgePartner (N : ℕ) (σ : Fin M → ℝ) (k : ℕ) : ℕ :=
  if h : ((Finset.Icc 1 (2 * numBands (N - 1) σ)).filter (fun j => j % 2 = k % 2)).Nonempty then
    (Finset.exists_min_image _ (fun j => |edgeVal (N - 1) σ j - edgeVal N σ k|) h).choose
  else k

/-- The number of eigenvalues of an `n × n` matrix beyond the edge `k` of the data `(N, σ)` on
its gap side: `d_{k̂−1}` (odd `k`) or `n − d_{k̂}` (even `k`). -/
def edgeDn (n N : ℕ) (σ : Fin M → ℝ) (k : ℕ) : ℕ :=
  if k % 2 = 1 then cumCount N σ ((k + 1) / 2 - 1) else n - cumCount N σ ((k + 1) / 2)

/-- A regular edge `l` of `N − 1` samples, of the parity of `k` and within `r < τ'/2` of `a_k`,
is the partner of `k`. -/
theorem edgePartner_eq {N : ℕ} {σ : Fin M → ℝ} {k l : ℕ} {τ' r : ℝ}
    (hl : RegularEdge τ' (N - 1) σ l) (hpar : l % 2 = k % 2)
    (hr : |edgeVal (N - 1) σ l - edgeVal N σ k| ≤ r) (hrτ : 2 * r < τ') :
    edgePartner N σ k = l := by
  have hls : l ∈ (Finset.Icc 1 (2 * numBands (N - 1) σ)).filter (fun j => j % 2 = k % 2) := by
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hl.1, hl.2.1⟩, hpar⟩
  unfold edgePartner
  rw [dite_eq_left_of_eq_true (eq_true ⟨l, hls⟩)]
  obtain ⟨hps, hpmin⟩ := (Finset.exists_min_image _
    (fun j => |edgeVal (N - 1) σ j - edgeVal N σ k|) ⟨l, hls⟩).choose_spec
  by_contra hpl
  have hp1 := Finset.mem_Icc.1 (Finset.mem_filter.1 hps).1
  have hsep := hl.2.2.2.1 _ hp1.1 hp1.2 hpl
  have hmin := hpmin l hls
  have htri := abs_sub_le (edgeVal (N - 1) σ l) (edgeVal N σ k)
    (edgeVal (N - 1) σ (Finset.exists_min_image _
      (fun j => |edgeVal (N - 1) σ j - edgeVal N σ k|) ⟨l, hls⟩).choose)
  rw [abs_sub_comm (edgeVal N σ k)] at htri
  linarith

/-- The partner of a regular edge (the edge of `edge_pred`): same parity, within `C₁/N`, regular
at `τ/2` for `N − 1` samples; it depends on `(N, σ, k)` only. -/
theorem edgePartner_spec (τ : ℝ) (hτ : 0 < τ) :
    ∃ C₁ : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (σ : Fin M → ℝ), DensityAssumptions τ N σ →
      ∀ k, RegularEdge τ N σ k → edgePartner N σ k % 2 = k % 2 ∧
        |edgeVal (N - 1) σ (edgePartner N σ k) - edgeVal N σ k| ≤ C₁ / N ∧
        RegularEdge (τ / 2) (N - 1) σ (edgePartner N σ k) := by
  obtain ⟨C₁, N₀, h⟩ := edge_pred τ hτ
  refine ⟨C₁, max N₀ (⌈4 * |C₁| / τ⌉₊ + 1), fun N hN M σ hda k hk => ?_⟩
  obtain ⟨l, hpar, hd, hreg⟩ := h N (le_of_max_le_left hN) M σ hda k hk
  have hN1 : ((⌈4 * |C₁| / τ⌉₊ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast le_of_max_le_right hN
  have hc := Nat.le_ceil (4 * |C₁| / τ)
  push_cast at hN1
  have hlt : 4 * |C₁| / τ < N := by linarith
  have hNpos : (0 : ℝ) < N := by
    have : (0 : ℝ) ≤ 4 * |C₁| / τ := by positivity
    linarith
  have h4 : 4 * |C₁| < N * τ := (div_lt_iff₀ hτ).1 hlt
  have h2 : 2 * (C₁ / N) < τ / 2 := by
    rw [show 2 * (C₁ / N) = (2 * C₁) / N by ring, div_lt_iff₀ hNpos]
    nlinarith [le_abs_self C₁]
  rw [edgePartner_eq hreg hpar hd h2]
  exact ⟨hpar, hd, hreg⟩

/-- The partner depends on the nonzero eigenvalues of `Σ` (with multiplicity) only. -/
theorem NzEq.edgePartner_eq {K : ℕ} {σ : Fin M → ℝ} {σ' : Fin K → ℝ} (h : NzEq σ σ') (N k : ℕ) :
    edgePartner N σ k = edgePartner N σ' k := by
  unfold edgePartner
  simp only [h.numBands_eq, h.edgeVal_eq]

/-- Removing one sample keeps the density assumptions at `τ/2`. -/
theorem densityAssumptions_pred {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ)
    (hN : 2 ≤ N) : DensityAssumptions (τ / 2) (N - 1) σ := by
  have hτ := h.pos
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hc : ((N - 1 : ℕ) : ℝ) = N - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hMpos : (0 : ℝ) < M := by
    have h1 := h.phi_lower
    unfold phiRatio at h1
    rcases (Nat.cast_nonneg M : (0 : ℝ) ≤ M).lt_or_eq with hM | hM
    · exact hM
    · rw [← hM, zero_div] at h1; linarith
  have hM0 : 0 < M := by exact_mod_cast hMpos
  have hlow := h.phi_lower
  have hup := h.phi_upper
  unfold phiRatio at hlow hup
  refine ⟨by linarith, h.nonneg, ?_, ?_, ?_, ?_⟩
  · unfold phiRatio
    rw [hc]
    have : (M : ℝ) / N ≤ M / (N - 1) :=
      div_le_div_of_nonneg_left hMpos.le (by linarith) (by linarith)
    linarith
  · unfold phiRatio
    rw [hc, inv_div, div_le_iff₀ (by linarith)]
    rw [div_le_iff₀ (by linarith)] at hup
    have : (M : ℝ) ≤ τ⁻¹ * N := hup
    have hτi : 0 < τ⁻¹ := inv_pos.2 hτ
    rw [show 2 / τ = 2 * τ⁻¹ by ring]
    nlinarith
  · intro i
    have := h.bound_Sigma i
    have : τ⁻¹ ≤ (τ / 2)⁻¹ := inv_anti₀ (by linarith) (by linarith)
    linarith [h.bound_Sigma i]
  · have hP := isProbabilityMeasure_empMeasure σ hM0
    have hmono : empMeasure σ (Set.Icc 0 (τ / 2)) ≤ empMeasure σ (Set.Icc 0 τ) :=
      measure_mono (Set.Icc_subset_Icc le_rfl (by linarith))
    have := ENNReal.toReal_mono (measure_ne_top _ _) hmono
    linarith [h.Sigma_gap]

/-- (phi_bounded) and (Sigma_gap) give `N > 0` and some positive `σ i`. -/
private lemma qdot_facts {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) :
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
private def qdotR (τ : ℝ) : ℝ := min (edgeTau0 τ) (τ / 2)

/-- The constant `c(τ) = π⁻¹ √(r/(2 C₂(τ))) · r/2`: a lower bound for `N_{k̂}/N` at a regular
edge `k`. -/
private def qdotC (τ : ℝ) : ℝ := √(qdotR τ / 2 / edgeC2 τ) / Real.pi * (qdotR τ / 2)

private lemma qdot_pos {τ : ℝ} (hτ : 0 < τ) : 0 < edgeTau0 τ ∧ 0 < edgeC2 τ := by
  have hcx : 0 < edgecx τ := by unfold edgecx; positivity
  have hCx : 0 < edgeCx τ := by unfold edgeCx; positivity
  have hc2 : 0 < edgec2 τ := by unfold edgec2; positivity
  have hC3 : 0 < edgeC3 τ := by unfold edgeC3; positivity
  have hr0 : 0 < edgeRho0 τ := by unfold edgeRho0; positivity
  have hr1 : 0 < edgeRho1 τ := by unfold edgeRho1; positivity
  exact ⟨by unfold edgeTau0; positivity, by unfold edgeC2; positivity⟩

private lemma qdotR_pos {τ : ℝ} (hτ : 0 < τ) : 0 < qdotR τ :=
  lt_min (qdot_pos hτ).1 (by linarith)

private lemma qdotC_pos {τ : ℝ} (hτ : 0 < τ) : 0 < qdotC τ := by
  have hr := qdotR_pos hτ
  have hC := (qdot_pos hτ).2
  have hs : 0 < √(qdotR τ / 2 / edgeC2 τ) := Real.sqrt_pos.2 (by positivity)
  unfold qdotC
  have := Real.pi_pos
  positivity

/-- If `ρ ≥ c₀` on `[x, y) ⊆ [a_{2j}, a_{2j−1}]` with `0 < x ≤ y`, then `N_j ≥ N c₀ (y − x)`. -/
private lemma qdot_bandCount_ge_of {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
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
private lemma qdot_bandCount_edge {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ)
    {k : ℕ} (hk : RegularEdge τ N σ k) : N * qdotC τ ≤ bandCount N σ ((k + 1) / 2) := by
  obtain ⟨hN, hS⟩ := qdot_facts h
  have hτ := h.pos
  obtain ⟨hk1, hk2, hτa, hsep, -⟩ := id hk
  have hr := qdotR_pos hτ
  have hr1 : qdotR τ ≤ edgeTau0 τ := min_le_left _ _
  have hr2 : qdotR τ ≤ τ / 2 := min_le_right _ _
  have hC := (qdot_pos hτ).2
  set r := qdotR τ with hrdef
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
    have hb := qdot_bandCount_ge_of (N := N) (σ := σ) (j := m) hσ hN (x := a + r / 2) (y := a + r)
      (by linarith) (by linarith) hc₀ (fun u hu => by
        rw [show 2 * m = k by omega, ← hadef]
        exact ⟨by linarith [hu.1], by linarith [hu.2]⟩)
      (fun u hu => by
        have h1 : |u - a| = u - a := abs_of_nonneg (by linarith [hu.1])
        refine hdens u (by rw [h1]; linarith [hu.1]) (by rw [h1]; linarith [hu.2]) ?_
        rw [hsign]
        linarith [hu.1])
    rw [hj]
    unfold qdotC
    linarith
  · -- odd `k = 2m + 1`: the upper edge of the band `m + 1`, window `[a_k − r, a_k − r/2)`
    have hj : (k + 1) / 2 = m + 1 := by omega
    have hsucc := edgeVal_succ_le N σ hσ hN hS hk1 (by omega)
    have hs := hsep (k + 1) (by omega) (by omega) (by omega)
    rw [abs_of_nonneg (by linarith)] at hs
    have hsign : (-1 : ℝ) ^ (k + 1) = 1 := Even.neg_one_pow ⟨m + 1, by omega⟩
    have hb := qdot_bandCount_ge_of (N := N) (σ := σ) (j := m + 1) hσ hN (x := a - r)
      (y := a - r / 2) (by linarith) (by linarith) hc₀ (fun u hu => by
        rw [show 2 * (m + 1) = k + 1 by omega, show k + 1 - 1 = k by omega, ← hadef]
        exact ⟨by linarith [hu.1], by linarith [hu.2]⟩)
      (fun u hu => by
        have h1 : |u - a| = a - u := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith [hu.2])
        refine hdens u (by rw [h1]; linarith [hu.2]) (by rw [h1]; linarith [hu.1]) ?_
        rw [hsign]
        linarith [hu.2])
    rw [hj]
    unfold qdotC
    linarith

/-- At a regular edge the component `k̂ = ⌈k/2⌉` holds at least `l` classical eigenvalues and
`d_{k̂} ≤ N`, for `N ≥ N₀(τ, l)`. -/
theorem cumCount_edge_window (τ : ℝ) (l : ℕ) (hτ : 0 < τ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (σ : Fin M → ℝ), DensityAssumptions τ N σ →
      ∀ k, RegularEdge τ N σ k →
        cumCount N σ ((k + 1) / 2 - 1) + l ≤ cumCount N σ ((k + 1) / 2) ∧
          cumCount N σ ((k + 1) / 2) ≤ N := by
  have hc := qdotC_pos hτ
  refine ⟨⌈(l : ℝ) / qdotC τ⌉₊, fun N hN M σ hda k hk => ?_⟩
  obtain ⟨hN0, hS⟩ := qdot_facts hda
  have hp1 : 1 ≤ (k + 1) / 2 := by have := hk.1; omega
  have hp2 : (k + 1) / 2 ≤ numBands N σ := by have := hk.2.1; omega
  obtain ⟨hc1, hb, hrel⟩ := cumCount_spec hda hp1 hp2
  have hband := qdot_bandCount_edge hda hk
  have hl : (l : ℝ) ≤ N * qdotC τ := by
    have h1 : (l : ℝ) / qdotC τ ≤ N := Nat.ceil_le.1 hN
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

private lemma qdot_charpoly_neg_herm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    (-A).charpoly = ∏ i, (Polynomial.X - Polynomial.C (-hA.eigenvalues i)) := by
  have h := hA.spectral_theorem
  have h2 : -A = Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
      (diagonal fun i => -hA.eigenvalues i) := by
    conv_lhs => rw [h]
    rw [← map_neg, ← diagonal_neg]
    congr 2
  rw [h2, Unitary.conjStarAlgAut_apply, charpoly_mul_comm, ← mul_assoc]
  simp [charpoly_diagonal]

private lemma qdot_eigenvalues₀_neg_multiset {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) :
    Multiset.map hA.neg.eigenvalues₀ Finset.univ.val =
      Multiset.map (fun i => -hA.eigenvalues₀ i) Finset.univ.val := by
  have h1 := hA.neg.roots_charpoly_eq_eigenvalues₀
  have h2 := hA.roots_charpoly_eq_eigenvalues₀
  have h3 : (-A).charpoly.roots = A.charpoly.roots.map fun x => -x := by
    rw [qdot_charpoly_neg_herm hA, hA.roots_charpoly_eq_eigenvalues, Polynomial.roots_prod]
    · simp
      exact List.Perm.refl _
    · rw [Finset.prod_ne_zero_iff]
      intro a _
      simpa [sub_eq_add_neg] using Polynomial.X_sub_C_ne_zero (-hA.eigenvalues a)
  have h4 := h1.symm.trans (h3.trans (congrArg (Multiset.map fun x => -x) h2))
  simp only [RCLike.ofReal_real_eq_id, Function.id_comp, Multiset.map_map] at h4
  simpa [Function.comp_def] using h4

private lemma qdot_sortedEig_neg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    {j : ℕ} (hj : 1 ≤ j) (hjn : j ≤ n) : sortedEig (-A) j = -sortedEig A (n + 1 - j) := by
  set m := Fintype.card (Fin n) with hm
  have hm' : m = n := Fintype.card_fin n
  set f : Fin m → ℝ := hA.eigenvalues₀ with hf
  set g : Fin m → ℝ := hA.neg.eigenvalues₀ with hg
  set h : Fin m → ℝ := fun i => -f (Fin.rev i) with hh
  have hmul : Multiset.map g Finset.univ.val = Multiset.map h Finset.univ.val := by
    have h1 := qdot_eigenvalues₀_neg_multiset hA
    have h2 : Multiset.map h Finset.univ.val =
        Multiset.map (fun i => -f i) Finset.univ.val := by
      have : Multiset.map (fun i => -f i) (Multiset.map Fin.revPerm Finset.univ.val) =
          Multiset.map (fun i => -f i) Finset.univ.val := by
        rw [Multiset.map_univ_val_equiv]
      rw [← this, Multiset.map_map]
      rfl
    rw [h2]; exact h1
  have hgl : (List.ofFn g).SortedGE := hA.neg.eigenvalues₀_antitone.sortedGE_ofFn
  have hhl : (List.ofFn h).SortedGE := by
    refine Antitone.sortedGE_ofFn fun a b hab => ?_
    have : f (Fin.rev a) ≤ f (Fin.rev b) := hA.eigenvalues₀_antitone (Fin.rev_le_rev.2 hab)
    simp only [hh]
    linarith
  have hperm : (List.ofFn g).Perm (List.ofFn h) := by
    have := hmul
    rw [Fin.univ_val_map, Fin.univ_val_map, Multiset.coe_eq_coe] at this
    exact this
  have heq := List.ofFn_inj.1 (hperm.eq_of_sortedGE hgl hhl)
  have hcond : (-A).IsHermitian ∧ 1 ≤ j ∧ j ≤ Fintype.card (Fin n) :=
    ⟨hA.neg, hj, by rw [Fintype.card_fin]; exact hjn⟩
  have hcond' : A.IsHermitian ∧ 1 ≤ n + 1 - j ∧ n + 1 - j ≤ Fintype.card (Fin n) :=
    ⟨hA, by omega, by rw [Fintype.card_fin]; omega⟩
  have e1 : sortedEig (-A) j = g ⟨j - 1, by omega⟩ := by
    unfold sortedEig
    rw [dite_eq_left_of_eq_true (eq_true hcond)]
  have e2 : sortedEig A (n + 1 - j) = f ⟨n + 1 - j - 1, by omega⟩ := by
    unfold sortedEig
    rw [dite_eq_left_of_eq_true (eq_true hcond')]
  rw [e1, e2, show g ⟨j - 1, by omega⟩ = h ⟨j - 1, by omega⟩ from congrFun heq _]
  simp only [hh]
  congr 2
  ext
  simp only [Fin.val_rev]
  omega

/-- The mirror relation for an `n × n` matrix and the data `(N, σ)`: `q_{k,l}` is the upper-edge
vector of `(−1)^{k+1} A` at `(−1)^{k+1} a_k` with `edgeDn n N σ k` eigenvalues beyond the edge. -/
theorem qVecA_eq_edgeQ_gen {n N : ℕ} {σ : Fin M → ℝ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) {k l : ℕ}
    (hl : cumCount N σ ((k + 1) / 2 - 1) + l ≤ cumCount N σ ((k + 1) / 2))
    (hd : cumCount N σ ((k + 1) / 2) ≤ n) :
    qVecA N σ A k l = edgeQ N (edgeSign k * edgeVal N σ k) (edgeScale N σ k) (edgeDn n N σ k) l
      (edgeSign k • A) := by
  funext i
  unfold qVecA edgeQ
  by_cases hk : k % 2 = 1
  · have hs : edgeSign k = 1 := by simp [edgeSign, hk]
    have hi : edgeIdx N σ k ((i : ℕ) + 1) = edgeDn n N σ k + ((i : ℕ) + 1) := by
      simp [edgeIdx, edgeDn, hk]
    rw [hs, hi]
    simp
  · have hs : edgeSign k = -1 := by simp [edgeSign, hk]
    have hil : (i : ℕ) < l := i.2
    have hi : edgeIdx N σ k ((i : ℕ) + 1) = cumCount N σ ((k + 1) / 2) + 1 - ((i : ℕ) + 1) := by
      simp [edgeIdx, hk]
    have hdd : edgeDn n N σ k = n - cumCount N σ ((k + 1) / 2) := by simp [edgeDn, hk]
    have hr := qdot_sortedEig_neg hA (j := n - cumCount N σ ((k + 1) / 2) + ((i : ℕ) + 1))
      (by omega) (by omega)
    rw [hs, hi, hdd, neg_one_smul, hr, show n + 1 - (n - cumCount N σ ((k + 1) / 2) + ((i : ℕ) + 1))
      = cumCount N σ ((k + 1) / 2) + 1 - ((i : ℕ) + 1) by omega]
    ring

/-! ## Witnesses

The instance `σ ≡ 1` on `Fin (2n)` (`Σ = I_{2n}`, rank `Σ ≥ N`): `φ = 2` at `N = n`, one band,
`a₁ = (1 + √2)²`, `a₂ = (√2 − 1)²`, both edges regular at `τ = 1/20`. -/

/-- `edgePartner_eq` at `σ ≡ 1` on `Fin 200`, `N = 101` (`φ = 200/101`, `φ̇ = 2`), the bottom edge
`k = l = 2`, `τ' = 1/20`, `r = 1/50`: `ȧ₂ = (√2 − 1)²`, `a₂ = (√(200/101) − 1)²`. -/
example : edgePartner 101 (fun _ : Fin (2 * 100) => (1 : ℝ)) 2 = 2 := by
  have hreg : RegularEdge (1 / 10 / 2) (101 - 1) (fun _ : Fin (2 * 100) => (1 : ℝ)) 2 :=
    regularEdge_two (n := 100) (by norm_num) (by norm_num) le_rfl
  refine edgePartner_eq (r := 1 / 50) hreg rfl ?_ (by norm_num)
  rw [show (101 : ℕ) - 1 = 100 from rfl, edgeVal_two_two (by norm_num),
    edgeVal_one_two (by norm_num) (by norm_num)]
  have e : ((2 * 100 : ℕ) : ℝ) / ((101 : ℕ) : ℝ) = 200 / 101 := by norm_num
  rw [e]
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have ht2 : Real.sqrt (200 / 101) ^ 2 = 200 / 101 := Real.sq_sqrt (by norm_num)
  have hs0 := Real.sqrt_nonneg 2
  have ht0 := Real.sqrt_nonneg (200 / 101)
  have hs1 : (1.41 : ℝ) ≤ Real.sqrt 2 := by nlinarith
  have hs3 : Real.sqrt 2 ≤ 1.42 := by nlinarith
  have ht1 : (1.40 : ℝ) ≤ Real.sqrt (200 / 101) := by nlinarith
  have ht3 : Real.sqrt (200 / 101) ≤ 1.41 := by nlinarith
  rw [abs_le]
  constructor <;> nlinarith

/-- `NzEq.edgePartner_eq` for the spectra of `T Tᵀ` and `Tᵀ T`. -/
example {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ) (N k : ℕ) :
    edgePartner N (specOf (T * Tᵀ)) k = edgePartner N (specOf (Tᵀ * T)) k :=
  (nzEq_specOf_mul_transpose T).edgePartner_eq N k

/-- `densityAssumptions_pred` at `σ ≡ 1` on `Fin 20`, `N = 10`, `τ = 1/10`. -/
example : DensityAssumptions (1 / 10 / 2) (10 - 1) (fun _ : Fin (2 * 10) => (1 : ℝ)) :=
  densityAssumptions_pred (densityAssumptions_two (by norm_num)) (by norm_num)

#print axioms qDotVec
#print axioms qDotVecT
#print axioms edgePartner
#print axioms edgeDn
#print axioms edgePartner_eq
#print axioms edgePartner_spec
#print axioms NzEq.edgePartner_eq
#print axioms densityAssumptions_pred
#print axioms cumCount_edge_window
#print axioms qdot_charpoly_neg_herm
#print axioms qdot_eigenvalues₀_neg_multiset
#print axioms qdot_sortedEig_neg
#print axioms qVecA_eq_edgeQ_gen

end Anisotropic
