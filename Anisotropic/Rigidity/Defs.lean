import Anisotropic.Density.Count
import Anisotropic.Density.Critical
import Anisotropic.Density.GenProp
import Anisotropic.Density.Structure
import Anisotropic.Density.Varrho
import Anisotropic.Entrywise.DiagModel

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # Eigenvalues of `Q`, the counting function `eigCount`, sorted eigenvalues, classical locations, `N_k`, the relabelling `λ_{k,i}`, `γ_{k,i}`, the rigidity bound, the window `edgeWin` -/

/-- `Q_N = Xᵀ Σ X` (`N × N`); its nonzero eigenvalues are those of `Q = Σ^{1/2} X Xᵀ Σ^{1/2}`
(§3.2, before Theorem 3.12). -/
def QN (Sig : Matrix (Fin M) (Fin M) ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  Xmᵀ * Sig * Xm

/-- The counting function `n_A(E) = #{j : λ_j(A) ≥ E}` of a symmetric matrix. -/
def eigCount {K : ℕ} (A : Matrix (Fin K) (Fin K) ℝ) (E : ℝ) : ℕ :=
  (Finset.univ.filter fun j => E ≤ specOf A j).card

/-- The eigenvalues in decreasing order, `λ_1 ≥ ⋯ ≥ λ_K` (index from `1`; `0` off range). -/
def sortedEig {K : ℕ} (A : Matrix (Fin K) (Fin K) ℝ) (i : ℕ) : ℝ :=
  if h : A.IsHermitian ∧ 1 ≤ i ∧ i ≤ Fintype.card (Fin K) then
    h.1.eigenvalues₀ ⟨i - 1, by have := h.2.1; have := h.2.2; omega⟩
  else 0

/-- The classical counting function `n(E) = N ϱ([E, ∞))`. -/
def nClass (N : ℕ) (σ : Fin M → ℝ) (E : ℝ) : ℝ :=
  N * (varrho N σ (Set.Ici E)).toReal

/-- The classical locations (def:gamma_alpha): `γ_i = sup {E > 0 : n(E) ≥ i − 1/2}`. -/
def gammaLoc (N : ℕ) (σ : Fin M → ℝ) (i : ℕ) : ℝ :=
  sSup {E | 0 < E ∧ (i : ℝ) - 1 / 2 ≤ nClass N σ E}

/-- `d_k = N_1 + ⋯ + N_k` as a natural number (`N_l ∈ ℕ`, Lemma A.1). -/
def cumCount (N : ℕ) (σ : Fin M → ℝ) (k : ℕ) : ℕ :=
  ⌊∑ l ∈ Finset.Icc 1 k, bandCount N σ l⌋₊

/-- `N_k` (def_N_k) as a natural number. -/
def bandNat (N : ℕ) (σ : Fin M → ℝ) (k : ℕ) : ℕ :=
  ⌊bandCount N σ k⌋₊

/-- The relabelled eigenvalue `λ_{k,i} = λ_{i + d_{k−1}}`. -/
def lamBand (Sig : Matrix (Fin M) (Fin M) ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (k i : ℕ) : ℝ :=
  sortedEig (QN Sig Xm) (cumCount N (specOf Sig) (k - 1) + i)

/-- The relabelled classical location `γ_{k,i} = γ_{i + d_{k−1}}`. -/
def gammaBand (N : ℕ) (σ : Fin M → ℝ) (k i : ℕ) : ℝ :=
  gammaLoc N σ (cumCount N σ (k - 1) + i)

/-- The right side of (rigidity) at level `ε`: `N^ε (i ∧ (N_k + 1 − i))^{−1/3} N^{−2/3}`. -/
def rigBound (N Nk i : ℕ) (ε : ℝ) : ℝ :=
  (N : ℝ) ^ ε * ((min i (Nk + 1 - i) : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ))

/-- The midpoint `(a_{2k} + a_{2k+1})/2` of the `k`-th gap. -/
def gapMid (N : ℕ) (σ : Fin M → ℝ) (k : ℕ) : ℝ :=
  (edgeVal N σ (2 * k) + edgeVal N σ (2 * k + 1)) / 2

/-- The energy window of Theorem 3.12 under the edge hypothesis at `τ/2` (every edge with `a_k ≥ τ/2` regular at `τ/2`): `[3τ/4, ∞)` together with the
`τ/8`-neighbourhoods of the edges `a_l ≥ τ/2`. -/
def edgeWin (τ : ℝ) (N : ℕ) (σ : Fin M → ℝ) : Set ℝ :=
  Set.Ici (3 * τ / 4) ∪ {E | ∃ l, 1 ≤ l ∧ l ≤ 2 * numBands N σ ∧ τ / 2 ≤ edgeVal N σ l ∧
    |E - edgeVal N σ l| ≤ τ / 8}

section RigHelpers

variable {σ : Fin M → ℝ}

private lemma eigCount_eq_card₀ {K : ℕ} {A : Matrix (Fin K) (Fin K) ℝ} (hA : A.IsHermitian) (E : ℝ) :
    eigCount A E =
      (Finset.univ.filter fun j : Fin (Fintype.card (Fin K)) => E ≤ hA.eigenvalues₀ j).card := by
  unfold eigCount
  rw [specOf_eq hA]
  refine Finset.card_equiv (Fintype.equivOfCardEq (Fintype.card_fin _)).symm ?_
  intro j
  rw [Finset.mem_filter, Finset.mem_filter]
  simp [Matrix.IsHermitian.eigenvalues]

private lemma QN_isHermitian {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (Xm : Matrix (Fin M) (Fin N) ℝ) : (QN Sig Xm).IsHermitian := by
  have := Matrix.isHermitian_conjTranspose_mul_mul Xm (show Sig.IsHermitian from hSig.isHermitian)
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

private lemma rank_QN_le (Sig : Matrix (Fin M) (Fin M) ℝ)
    (Xm : Matrix (Fin M) (Fin N) ℝ) : (QN Sig Xm).rank ≤ min M N := by
  refine le_min ?_ ?_
  · calc (QN Sig Xm).rank ≤ (Xmᵀ * Sig).rank := Matrix.rank_mul_le_left _ _
      _ ≤ Xmᵀ.rank := Matrix.rank_mul_le_left _ _
      _ = Xm.rank := Matrix.rank_transpose _
      _ ≤ M := by simpa using Matrix.rank_le_card_height Xm
  · calc (QN Sig Xm).rank ≤ Xm.rank := Matrix.rank_mul_le_right _ _
      _ ≤ N := by simpa using Matrix.rank_le_card_width Xm

/-- (phi_bounded) and (Sigma_gap) give `N > 0`, `M > 0` and some positive `σ i`. -/
private lemma rig_facts {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) :
    0 < N ∧ 0 < M ∧ (posVals σ).Nonempty := by
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
  refine ⟨hN, Nat.pos_of_ne_zero hM, ?_⟩
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

/-- `a_j ≥ a_k` for `1 ≤ j ≤ k ≤ 2p`. -/
private lemma rig_edgeVal_anti (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j)
    (hj : j ≤ 2 * numBands N σ) : edgeVal N σ j ≤ edgeVal N σ i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    exact (edgeVal_succ_le N σ hσ hN hS (by omega) (by omega)).trans (ih (by omega))

private lemma rig_edgeVal_nonneg {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : k ≤ 2 * numBands N σ) : 0 ≤ edgeVal N σ k := by
  obtain ⟨hN, -, hS⟩ := rig_facts h
  exact (edgeVal_mem_Icc N σ h.nonneg hN hS h.pos h.phi_lower h.phi_upper h.bound_Sigma hk1 hk).1

/-- `ϱ(A) = ∫_A ρ` for measurable `A ⊆ (0, ∞)`. -/
private lemma rig_varrho_apply (N : ℕ) (σ : Fin M → ℝ) {A : Set ℝ} (hA : MeasurableSet A)
    (hsub : A ⊆ Set.Ioi 0) :
    varrho N σ A = ∫⁻ x in A, ENNReal.ofReal (rhoDens N σ x) := by
  have h0 : (0 : ℝ) ∉ A := fun h => lt_irrefl (0 : ℝ) (Set.mem_Ioi.mp (hsub h))
  rw [varrho, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hA,
    Set.indicator_of_notMem h0, smul_zero, zero_add, withDensity_apply _ hA,
    Measure.restrict_restrict hA, Set.inter_eq_left.mpr hsub]

private lemma rig_varrho_singleton (N : ℕ) (σ : Fin M → ℝ) {x : ℝ} (hx : 0 < x) :
    varrho N σ {x} = 0 := by
  rw [rig_varrho_apply N σ (measurableSet_singleton x) (by simpa using hx)]
  exact setLIntegral_measure_zero _ _ Real.volume_singleton

private lemma rig_continuousOn_rhoDens (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) :
    ContinuousOn (rhoDens N σ) (Set.Ioi 0) := by
  have h1 : ContinuousOn (fun x : ℝ => mExt N σ x) (Set.Ioi 0) :=
    (continuousOn_mExt N σ hσ).comp Complex.continuous_ofReal.continuousOn
      (fun x hx => Or.inr ⟨Complex.ofReal_im x, Complex.ofReal_ne_zero.mpr (ne_of_gt hx)⟩)
  exact (Complex.continuous_im.comp_continuousOn h1).div_const _

private lemma rig_nClass_anti (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) : Antitone (nClass N σ) := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  intro x y hxy
  exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono (Set.Ici_subset_Ici.mpr hxy))) (Nat.cast_nonneg N)

private lemma rig_nClass_lip (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {a b : ℝ} (ha : 0 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, x ≤ y →
      nClass N σ x - nClass N σ y ≤ K * (y - x) := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun x hx => lt_of_lt_of_le ha hx.1
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image
    ((rig_continuousOn_rhoDens N σ hσ).mono hsub)
  refine ⟨N * max B 0, by positivity, fun x hx y hy hxy => ?_⟩
  have hsplit : varrho N σ (Set.Ici x) = varrho N σ (Set.Ico x y) + varrho N σ (Set.Ici y) := by
    rw [← measure_union _ measurableSet_Ici, Set.Ico_union_Ici_eq_Ici hxy]
    rw [Set.disjoint_left]
    intro z hz1 hz2
    exact absurd hz1.2 (not_lt.mpr hz2)
  have hIco : varrho N σ (Set.Ico x y) ≤ ENNReal.ofReal (max B 0 * (y - x)) := by
    have hsub' : Set.Ico x y ⊆ Set.Icc a b := fun z hz => ⟨hx.1.trans hz.1, hz.2.le.trans hy.2⟩
    rw [rig_varrho_apply N σ measurableSet_Ico (hsub'.trans hsub)]
    calc ∫⁻ z in Set.Ico x y, ENNReal.ofReal (rhoDens N σ z)
        ≤ ∫⁻ z in Set.Ico x y, ENNReal.ofReal (max B 0) := by
          refine setLIntegral_mono' measurableSet_Ico fun z hz => ?_
          exact ENNReal.ofReal_le_ofReal
            ((hB ⟨z, hsub' hz, rfl⟩).trans (le_max_left _ _))
      _ = ENNReal.ofReal (max B 0 * (y - x)) := by
          rw [setLIntegral_const, Real.volume_Ico, ← ENNReal.ofReal_mul (le_max_right _ _)]
  have hc : 0 ≤ max B 0 * (y - x) := mul_nonneg (le_max_right _ _) (by linarith)
  have h1 : (varrho N σ (Set.Ico x y)).toReal ≤ max B 0 * (y - x) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hIco
    rwa [ENNReal.toReal_ofReal hc] at this
  have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (α := ℝ) N)
  unfold nClass
  rw [hsplit, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  linarith

private lemma rig_nClass_continuousOn (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) :
    ContinuousOn (nClass N σ) (Set.Ioi 0) := by
  intro E0 hE0
  have hE0' : (0 : ℝ) < E0 := hE0
  have hmem : Set.Icc (E0 / 2) (2 * E0) ∈ 𝓝 E0 :=
    Icc_mem_nhds (by linarith) (by linarith)
  obtain ⟨K, hK0, hK⟩ := rig_nClass_lip (σ := σ) hσ hN (a := E0 / 2) (b := 2 * E0) (by linarith)
  have hanti := rig_nClass_anti (σ := σ) hσ hN
  have hlip : LipschitzOnWith K.toNNReal (nClass N σ) (Set.Icc (E0 / 2) (2 * E0)) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hK0]
    rcases le_total x y with hxy | hxy
    · have h1 := hK x hx y hy hxy
      have h2 := hanti hxy
      rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
      linarith
    · have h1 := hK y hy x hx hxy
      have h2 := hanti hxy
      rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
      linarith
  exact (hlip.continuousOn.continuousAt hmem).continuousWithinAt

private lemma rig_nClass_eq_zero (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) (hS : (posVals σ).Nonempty)
    {E : ℝ} (hE : edgeVal N σ 1 < E) : nClass N σ E = 0 := by
  have h0 : varrho N σ (Set.Ici E) = 0 :=
    measure_mono_null (t := (Set.Icc 0 (edgeVal N σ 1))ᶜ)
      (fun x hx h => absurd (lt_of_lt_of_le hE hx) (not_lt.mpr h.2))
      (varrho_compl_Icc_edgeVal N σ hσ hN hS)
  unfold nClass
  rw [h0]
  simp

/-- `N ϱ((0, ∞)) = N ∧ M`. -/
private lemma rig_varrho_Ioi (hσ : ∀ j, 0 < σ j) (hN : 0 < N) (hM : 0 < M) :
    (N : ℝ) * (varrho N σ (Set.Ioi 0)).toReal = min (N : ℝ) M := by
  have hσ' : ∀ i, 0 ≤ σ i := fun i => (hσ i).le
  have hS : (posVals σ).Nonempty :=
    ⟨σ ⟨0, hM⟩, Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), hσ _⟩⟩
  have := isProbabilityMeasure_varrho N σ hσ' hN
  have hIio : varrho N σ (Set.Iio 0) = 0 :=
    measure_mono_null (t := (Set.Icc 0 (edgeVal N σ 1))ᶜ)
      (fun x hx h => (not_le.mpr (Set.mem_Iio.mp hx)) (Set.mem_Icc.mp h).1)
      (varrho_compl_Icc_edgeVal N σ hσ' hN hS)
  have hIic : varrho N σ (Set.Iic 0) = varrho N σ {0} := by
    refine le_antisymm ?_ (measure_mono (by simp))
    calc varrho N σ (Set.Iic 0) = varrho N σ (Set.Iio 0 ∪ {0}) := by rw [Set.Iio_union_right]
      _ ≤ varrho N σ (Set.Iio 0) + varrho N σ {0} := measure_union_le _ _
      _ = varrho N σ {0} := by rw [hIio, zero_add]
  have h1 := (Ni_sum N σ hσ hN hM).1
  rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, hIic,
    ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one, mul_sub, mul_one,
    h1]
  rcases le_total (N : ℝ) M with h | h
  · rw [max_eq_right (by linarith), min_eq_left h]; ring
  · rw [max_eq_left (by linarith), min_eq_right h]; ring

private lemma rig_exists_large (hσ : ∀ j, 0 < σ j) (hN : 0 < N) (hM : 0 < M) {c : ℝ}
    (hc : c < min (N : ℝ) M) : ∃ E, 0 < E ∧ c < nClass N σ E := by
  have hσ' : ∀ i, 0 ≤ σ i := fun i => (hσ i).le
  have hprob := isProbabilityMeasure_varrho N σ hσ' hN
  set f : ℕ → Set ℝ := fun k => Set.Ici (1 / ((k : ℝ) + 1)) with hf
  have hmono : Monotone f := by
    intro k l hkl
    refine Set.Ici_subset_Ici.mpr ?_
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hkl 1)
  have hU : (⋃ k, f k) = Set.Ioi 0 := by
    ext x
    simp only [Set.mem_iUnion, hf, Set.mem_Ici, Set.mem_Ioi]
    constructor
    · rintro ⟨k, hk⟩
      exact lt_of_lt_of_le (by positivity) hk
    · intro hx
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hx
      exact ⟨k, hk.le⟩
  have ht := tendsto_measure_iUnion_atTop (μ := varrho N σ) hmono
  rw [hU] at ht
  have ht' : Tendsto (fun k => (varrho N σ (f k)).toReal) atTop
      (𝓝 (varrho N σ (Set.Ioi 0)).toReal) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp ht
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hlt : c / N < (varrho N σ (Set.Ioi 0)).toReal := by
    rw [div_lt_iff₀ hNr]
    have := rig_varrho_Ioi hσ hN hM
    linarith
  obtain ⟨k, hk⟩ := (ht'.eventually (lt_mem_nhds hlt)).exists
  refine ⟨1 / ((k : ℝ) + 1), by positivity, ?_⟩
  unfold nClass
  rw [div_lt_iff₀ hNr] at hk
  simpa [hf, mul_comm] using hk

/-- `ϱ([t, ∞))` as a sum over the first `q` bands, when no later band reaches above `t` and
`t` lies below the first `q` bands. -/
private lemma rig_varrho_Ici {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) {t : ℝ}
    (ht : 0 < t) {q : ℕ} (hq : q ≤ numBands N σ)
    (h1 : ∀ l, 1 ≤ l → l ≤ q → t ≤ edgeVal N σ (2 * l))
    (h2 : ∀ l, q < l → l ≤ numBands N σ → edgeVal N σ (2 * l - 1) ≤ t) :
    varrho N σ (Set.Ici t) = ∑ l ∈ Finset.Icc 1 q,
      varrho N σ (Set.Icc (edgeVal N σ (2 * l)) (edgeVal N σ (2 * l - 1))) := by
  obtain ⟨hN, hM, hS⟩ := rig_facts h
  have hσ := h.nonneg
  set B : ℕ → Set ℝ := fun l => Set.Icc (edgeVal N σ (2 * l)) (edgeVal N σ (2 * l - 1)) with hB
  set U : Set ℝ := ⋃ l ∈ Finset.Icc 1 q, B l with hU
  have hUsub : U ⊆ Set.Ici t := by
    intro x hx
    simp only [hU, Set.mem_iUnion, exists_prop, Finset.mem_Icc] at hx
    obtain ⟨l, hl, hxl⟩ := hx
    exact (h1 l hl.1 hl.2).trans hxl.1
  have hNull : varrho N σ ((varrho N σ).supportᶜ ∪ {t}) = 0 := by
    refine measure_union_null Measure.measure_compl_support (rig_varrho_singleton N σ ht)
  have hcover : Set.Ici t ⊆ U ∪ ((varrho N σ).supportᶜ ∪ {t}) := by
    intro x hx
    by_cases hxs : x ∈ (varrho N σ).support
    · have hx0 : 0 < x := lt_of_lt_of_le ht hx
      rw [mem_support_varrho_iff N σ hσ hN hS hx0] at hxs
      obtain ⟨l, hl1, hlp, hxl⟩ := hxs
      by_cases hlq : l ≤ q
      · left
        simp only [hU, Set.mem_iUnion, exists_prop, Finset.mem_Icc]
        exact ⟨l, ⟨hl1, hlq⟩, hxl⟩
      · right; right
        have := h2 l (not_le.mp hlq) hlp
        exact le_antisymm (hxl.2.trans this) hx
    · right; left
      exact hxs
  have hUeq : varrho N σ (Set.Ici t) = varrho N σ U := by
    refine le_antisymm ?_ (measure_mono hUsub)
    calc varrho N σ (Set.Ici t) ≤ varrho N σ (U ∪ ((varrho N σ).supportᶜ ∪ {t})) :=
          measure_mono hcover
      _ ≤ varrho N σ U + varrho N σ ((varrho N σ).supportᶜ ∪ {t}) := measure_union_le _ _
      _ = varrho N σ U := by rw [hNull, add_zero]
  rw [hUeq, hU]
  refine measure_biUnion_finset₀ ?_ (fun l _ => measurableSet_Icc.nullMeasurableSet)
  have key : ∀ k j, 1 ≤ k → k < j → j ≤ q → AEDisjoint (varrho N σ) (B k) (B j) := by
    intro k j hk hkj hjq
    have hjp : j ≤ numBands N σ := hjq.trans hq
    have hlt := edgeVal_band_lt N σ hσ hN hS (by omega : 1 ≤ j) hjp
    have h0 := rig_edgeVal_nonneg h (k := 2 * j) (by omega) (by omega)
    have hge := rig_edgeVal_anti N σ hσ hN hS (i := 2 * k) (j := 2 * j - 1) (by omega) (by omega)
      (by omega)
    refine measure_mono_null (t := {edgeVal N σ (2 * k)}) ?_
      (rig_varrho_singleton N σ (by linarith))
    rintro x ⟨hx1, hx2⟩
    exact le_antisymm (hx2.2.trans hge) hx1.1
  intro k hk j hj hkj
  simp only [Finset.coe_Icc, Set.mem_Icc] at hk hj
  rcases lt_or_gt_of_ne hkj with hlt | hlt
  · exact key k j hk.1 hlt hj.2
  · exact (key j k hj.1 hlt hk.2).symm

/-- Partial sums of the band counts are natural numbers. -/
private lemma rig_cum_eq {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) {q : ℕ}
    (hq : q ≤ numBands N σ) :
    (cumCount N σ q : ℝ) = ∑ l ∈ Finset.Icc 1 q, bandCount N σ l := by
  obtain ⟨hN, hM, hS⟩ := rig_facts h
  have hex : ∀ q, q ≤ numBands N σ → ∃ n : ℕ, ∑ l ∈ Finset.Icc 1 q, bandCount N σ l = n := by
    intro q
    induction q with
    | zero => intro _; exact ⟨0, by simp⟩
    | succ q ih =>
      intro hq
      obtain ⟨n, hn⟩ := ih (by omega)
      obtain ⟨m, hm⟩ := bandCount_eq_natCast N σ h.nonneg hN hS (k := q + 1) (by omega) hq
      refine ⟨n + m, ?_⟩
      rw [Finset.sum_Icc_succ_top (by omega), hn, hm]
      push_cast; rfl
  obtain ⟨n, hn⟩ := hex q hq
  unfold cumCount
  rw [hn, Nat.floor_natCast]

private lemma rig_nClass_Ici {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) {t : ℝ}
    (ht : 0 < t) {q : ℕ} (hq : q ≤ numBands N σ)
    (h1 : ∀ l, 1 ≤ l → l ≤ q → t ≤ edgeVal N σ (2 * l))
    (h2 : ∀ l, q < l → l ≤ numBands N σ → edgeVal N σ (2 * l - 1) ≤ t) :
    nClass N σ t = cumCount N σ q := by
  have := isProbabilityMeasure_varrho N σ h.nonneg (rig_facts h).1
  rw [rig_cum_eq h hq]
  unfold nClass
  rw [rig_varrho_Ici h ht hq h1 h2, ENNReal.toReal_sum (fun l _ => measure_ne_top _ _),
    Finset.mul_sum]
  rfl

end RigHelpers

/-- `λ_i ≥ E` iff at least `i` eigenvalues are `≥ E`. -/
theorem sortedEig_ge_iff {K : ℕ} {A : Matrix (Fin K) (Fin K) ℝ} (hA : A.IsHermitian) {i : ℕ}
    (hi : 1 ≤ i) (hiK : i ≤ K) (E : ℝ) : E ≤ sortedEig A i ↔ i ≤ eigCount A E := by
  have hK : i - 1 < Fintype.card (Fin K) := by rw [Fintype.card_fin]; omega
  have hcond : A.IsHermitian ∧ 1 ≤ i ∧ i ≤ Fintype.card (Fin K) :=
    ⟨hA, hi, by rw [Fintype.card_fin]; exact hiK⟩
  have hs : sortedEig A i = hA.eigenvalues₀ ⟨i - 1, hK⟩ := by
    unfold sortedEig
    split
    · rfl
    · rename_i h; exact absurd hcond h
  rw [hs, eigCount_eq_card₀ hA]
  set S := Finset.univ.filter fun j : Fin (Fintype.card (Fin K)) => E ≤ hA.eigenvalues₀ j with hS
  have hanti := hA.eigenvalues₀_antitone
  constructor
  · intro h
    have hsub : Finset.Iic (⟨i - 1, hK⟩ : Fin (Fintype.card (Fin K))) ⊆ S := by
      intro j hj
      rw [Finset.mem_Iic] at hj
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
      exact h.trans (hanti hj)
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    simpa [Nat.sub_add_cancel hi] using this
  · intro h
    by_contra hlt
    replace hlt := not_le.mp hlt
    have hsub : S ⊆ Finset.Iio (⟨i - 1, hK⟩ : Fin (Fintype.card (Fin K))) := by
      intro j hj
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      rw [Finset.mem_Iio]
      by_contra hjn
      replace hjn := not_lt.mp hjn
      exact absurd (hj.trans (hanti hjn)) (not_le.mpr hlt)
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    simp only at this
    omega

/-- `n_A` is nonincreasing. -/
theorem eigCount_antitone {K : ℕ} (A : Matrix (Fin K) (Fin K) ℝ) : Antitone (eigCount A) := by
  intro E E' h
  unfold eigCount
  exact Finset.card_le_card fun j hj => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    linarith

/-- For `E > 0`, `Q_N` has at most `M ∧ N` eigenvalues `≥ E` (`rank Q_N ≤ M ∧ N`). -/
theorem eigCount_QN_le {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {E : ℝ} (hE : 0 < E) : eigCount (QN Sig Xm) E ≤ min M N := by
  have hH := QN_isHermitian hSig Xm
  have h1 : eigCount (QN Sig Xm) E ≤ Fintype.card {i // hH.eigenvalues i ≠ 0} := by
    rw [Fintype.card_subtype]
    unfold eigCount
    rw [specOf_eq hH]
    refine Finset.card_le_card fun j hj => ?_
    rw [Finset.mem_filter] at hj ⊢
    exact ⟨hj.1, fun h0 => by have := hj.2; rw [h0] at this; linarith⟩
  rw [← hH.rank_eq_card_non_zero_eigs] at h1
  exact h1.trans (rank_QN_le Sig Xm)

/-- `d_k = N_1 + ⋯ + N_k` and `N_k` as natural numbers (Lemma A.1), and `d_{k−1} + N_k = d_k`. -/
theorem cumCount_spec {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) {k : ℕ}
    (hk : 1 ≤ k) (hkp : k ≤ numBands N σ) :
    (cumCount N σ k : ℝ) = ∑ l ∈ Finset.Icc 1 k, bandCount N σ l ∧
      (bandNat N σ k : ℝ) = bandCount N σ k ∧
      cumCount N σ (k - 1) + bandNat N σ k = cumCount N σ k := by
  obtain ⟨hN, hM, hS⟩ := rig_facts h
  have h2 : (bandNat N σ k : ℝ) = bandCount N σ k := by
    obtain ⟨m, hm⟩ := bandCount_eq_natCast N σ h.nonneg hN hS hk hkp
    unfold bandNat
    rw [hm, Nat.floor_natCast]
  refine ⟨rig_cum_eq h hkp, h2, ?_⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  apply Nat.cast_injective (R := ℝ)
  push_cast
  rw [h2, rig_cum_eq h (by omega), rig_cum_eq h hkp, Finset.sum_Icc_succ_top (by omega)]

/-- (def:gamma_alpha): `n(γ_i) = i − 1/2` for `1 ≤ i ≤ M ∧ N`, with `γ_i > 0`. -/
theorem nClass_gammaLoc {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ)
    (hσ : ∀ j, 0 < σ j) {i : ℕ} (hi : 1 ≤ i) (hiMN : i ≤ min M N) :
    0 < gammaLoc N σ i ∧ nClass N σ (gammaLoc N σ i) = (i : ℝ) - 1 / 2 := by
  obtain ⟨hN, hM, hS⟩ := rig_facts h
  have hσ' := h.nonneg
  have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hiM : (i : ℝ) ≤ min (N : ℝ) M := by
    rw [le_min_iff]
    exact ⟨by exact_mod_cast (le_min_iff.mp hiMN).2, by exact_mod_cast (le_min_iff.mp hiMN).1⟩
  have hc0 : (0 : ℝ) < (i : ℝ) - 1 / 2 := by linarith
  obtain ⟨E0, hE0, hcE0⟩ := rig_exists_large hσ hN hM (c := (i : ℝ) - 1 / 2) (by linarith)
  set S : Set ℝ := {E | 0 < E ∧ (i : ℝ) - 1 / 2 ≤ nClass N σ E} with hSdef
  have hgam : gammaLoc N σ i = sSup S := rfl
  have hE0S : E0 ∈ S := ⟨hE0, hcE0.le⟩
  have hbdd : BddAbove S := by
    refine ⟨edgeVal N σ 1, fun E hE => ?_⟩
    by_contra hlt
    have := rig_nClass_eq_zero hσ' hN hS (not_le.mp hlt)
    linarith [hE.2]
  have hγ0 : 0 < sSup S := lt_of_lt_of_le hE0 (le_csSup hbdd hE0S)
  have hcont : ContinuousAt (nClass N σ) (sSup S) :=
    (rig_nClass_continuousOn hσ' hN).continuousAt (Ioi_mem_nhds hγ0)
  rw [hgam]
  refine ⟨hγ0, le_antisymm ?_ ?_⟩
  · by_contra hlt
    rw [not_le] at hlt
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp hcont ((nClass N σ (sSup S)) - ((i : ℝ) - 1 / 2))
      (by linarith)
    have hlt2 : sSup S < sSup S + δ / 2 := by linarith
    have hmem : sSup S + δ / 2 ∈ S := by
      refine ⟨by linarith, ?_⟩
      have := hδ' (x := sSup S + δ / 2) (by rw [Real.dist_eq]; rw [abs_of_pos (by linarith)]; linarith)
      rw [Real.dist_eq, abs_lt] at this
      linarith [this.1]
    exact absurd (le_csSup hbdd hmem) (not_le.mpr hlt2)
  · by_contra hlt
    rw [not_le] at hlt
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp hcont (((i : ℝ) - 1 / 2) - nClass N σ (sSup S))
      (by linarith)
    obtain ⟨E, hES, hE⟩ := exists_lt_of_lt_csSup ⟨E0, hE0S⟩ (show sSup S - δ < sSup S by linarith)
    have hEle : E ≤ sSup S := le_csSup hbdd hES
    have := hδ' (x := E) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    rw [Real.dist_eq, abs_lt] at this
    linarith [hES.2, this.2]

/-- `n(a_{2k−1}) = d_{k−1}`, and `n(a_{2k}) = d_k` when `a_{2k} > 0`. -/
theorem nClass_edgeVal {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) {k : ℕ}
    (hk : 1 ≤ k) (hkp : k ≤ numBands N σ) :
    nClass N σ (edgeVal N σ (2 * k - 1)) = cumCount N σ (k - 1) ∧
      (0 < edgeVal N σ (2 * k) → nClass N σ (edgeVal N σ (2 * k)) = cumCount N σ k) := by
  obtain ⟨hN, hM, hS⟩ := rig_facts h
  have hσ := h.nonneg
  constructor
  · have hlt := edgeVal_band_lt N σ hσ hN hS hk hkp
    have h0 := rig_edgeVal_nonneg h (k := 2 * k) (by omega) (by omega)
    refine rig_nClass_Ici h (by linarith) (by omega) (fun l hl1 hlq => ?_) (fun l hlq hlp => ?_)
    · exact rig_edgeVal_anti N σ hσ hN hS (i := 2 * l) (j := 2 * k - 1) (by omega) (by omega)
        (by omega)
    · exact rig_edgeVal_anti N σ hσ hN hS (i := 2 * k - 1) (j := 2 * l - 1) (by omega) (by omega)
        (by omega)
  · intro hpos
    refine rig_nClass_Ici h hpos hkp (fun l hl1 hlq => ?_) (fun l hlq hlp => ?_)
    · exact rig_edgeVal_anti N σ hσ hN hS (i := 2 * l) (j := 2 * k) (by omega) (by omega)
        (by omega)
    · exact rig_edgeVal_anti N σ hσ hN hS (i := 2 * k) (j := 2 * l - 1) (by omega) (by omega)
        (by omega)

/-- `γ_{k,i} ∈ (a_{2k}, a_{2k−1})` for `1 ≤ i ≤ N_k` (§3.2, before Theorem 3.12). -/
theorem gammaBand_mem {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ)
    (hσ : ∀ j, 0 < σ j) {k i : ℕ} (hk : 1 ≤ k) (hkp : k ≤ numBands N σ) (hi : 1 ≤ i)
    (hiN : i ≤ bandNat N σ k) :
    gammaBand N σ k i ∈ Set.Ioo (edgeVal N σ (2 * k)) (edgeVal N σ (2 * k - 1)) := by
  obtain ⟨hN, hM, hS⟩ := rig_facts h
  have hσ' := h.nonneg
  obtain ⟨hc1, hc2, hc3⟩ := cumCount_spec h hk hkp
  -- `d_k ≤ M ∧ N`
  have hdk : cumCount N σ k ≤ min M N := by
    have hsum := (Ni_sum N σ hσ hN hM).2
    have hle : ∑ l ∈ Finset.Icc 1 k, bandCount N σ l ≤
        ∑ l ∈ Finset.Icc 1 (numBands N σ), bandCount N σ l :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl hkp)
        (fun l _ _ => by unfold bandCount; positivity)
    rw [hsum, ← hc1] at hle
    have : (cumCount N σ k : ℝ) ≤ ((min M N : ℕ) : ℝ) := by
      rw [Nat.cast_min, min_comm]; exact hle
    exact_mod_cast this
  have hj1 : 1 ≤ cumCount N σ (k - 1) + i := by omega
  have hjle : cumCount N σ (k - 1) + i ≤ min M N := by omega
  obtain ⟨hγ0, hγn⟩ := nClass_gammaLoc h hσ hj1 hjle
  obtain ⟨he1, he2⟩ := nClass_edgeVal h hk hkp
  have hanti := rig_nClass_anti (σ := σ) hσ' hN
  have hg : gammaBand N σ k i = gammaLoc N σ (cumCount N σ (k - 1) + i) := rfl
  rw [hg]
  have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hjk : ((cumCount N σ (k - 1) + i : ℕ) : ℝ) ≤ cumCount N σ k := by
    exact_mod_cast (by omega : cumCount N σ (k - 1) + i ≤ cumCount N σ k)
  push_cast at hγn hjk
  have h0 := rig_edgeVal_nonneg h (k := 2 * k) (by omega) (by omega)
  constructor
  · rcases h0.eq_or_lt with h0' | h0'
    · rw [← h0']; exact hγ0
    · by_contra hle
      rw [not_lt] at hle
      have := hanti hle
      rw [hγn, he2 h0'] at this
      linarith
  · by_contra hle
    rw [not_lt] at hle
    have := hanti hle
    rw [hγn, he1] at this
    linarith

/-- Definition 2.7 (i) is monotone in its parameter. -/
theorem regularEdge_mono {τ τ₂ : ℝ} {σ : Fin M → ℝ} {k : ℕ} (h : RegularEdge τ N σ k)
    (h₂ : τ₂ ≤ τ) : RegularEdge τ₂ N σ k := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h₂.trans h3, fun l a b c => h₂.trans (h4 l a b c),
    fun hn s hs => h₂.trans (h5 hn s hs)⟩

/-- `regularEdge_mono` at the Marchenko–Pastur instance `M = 1`, `N = 2`, `σ = 1` (edge 1,
`RegularEdge (1/20)`), lowered to `1/40`. -/
example (h : RegularEdge (1 / 20) 2 (fun _ : Fin 1 => (1 : ℝ)) 1) :
    RegularEdge (1 / 40) 2 (fun _ : Fin 1 => (1 : ℝ)) 1 :=
  regularEdge_mono h (by norm_num)

/-- `eigCount` and `sortedEig` of `diag(2, 1)`: `λ_2 = 1 ≥ 1` iff at least two eigenvalues are
`≥ 1`. -/
example : (1 : ℝ) ≤ sortedEig (Matrix.diagonal ![(2 : ℝ), 1]) 2 ↔
    2 ≤ eigCount (Matrix.diagonal ![(2 : ℝ), 1]) 1 :=
  sortedEig_ge_iff (Matrix.isHermitian_diagonal _) (by norm_num) (by norm_num) 1

/-- `Σ = 1` (`M = 1`), `X = (1 1)` (`N = 2`): `Q_N = XᵀX` has at most `min M N = 1` eigenvalue
`≥ 1`. -/
example : eigCount (QN (1 : Matrix (Fin 1) (Fin 1) ℝ) (Matrix.of ![![(1 : ℝ), 1]])) 1 ≤
    min 1 2 :=
  eigCount_QN_le Matrix.PosDef.one _ one_pos

end Anisotropic
