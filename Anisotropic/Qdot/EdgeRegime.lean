module

public import Anisotropic.Density.Count
public import Anisotropic.Density.Critical
public import Anisotropic.EdgeUniv.Defs
public import Anisotropic.EdgeUniv.RegimeQ
public import Anisotropic.EdgeUniv.SmCount
public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.Framework.Domination
public import Anisotropic.Framework.Model
public import Anisotropic.Qdot.Classical
public import Anisotropic.Qdot.Defs
public import Anisotropic.Qdot.EdgeDefs
public import Anisotropic.Qdot.RigidityLocal
public import Anisotropic.Rigidity.EdgeLow

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # The edge regime for `Q̇` at the partner edge -/

/-! ## The measure `ϱ`, the classical count `n`, the edges and the support -/

/-- (phi_bounded) and (Sigma_gap) give `N > 0`, `M > 0` and some positive `σ i`. -/
private lemma er_facts {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) :
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

/-- `a_j ≤ a_i` for `1 ≤ i ≤ j ≤ 2p`. -/
private lemma er_anti {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) {i j : ℕ}
    (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ 2 * numBands N σ) : edgeVal N σ j ≤ edgeVal N σ i := by
  obtain ⟨hN, -, hS⟩ := er_facts h
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ k hik ih =>
    exact (edgeVal_succ_le N σ h.nonneg hN hS (by omega) (by omega)).trans (ih (by omega))

/-- `0 ≤ a_k ≤ 2τ⁻¹(1 + τ⁻¹)` for `1 ≤ k ≤ 2p`. -/
private lemma er_edge_mem {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) {k : ℕ}
    (hk : 1 ≤ k) (hkp : k ≤ 2 * numBands N σ) :
    0 ≤ edgeVal N σ k ∧ edgeVal N σ k ≤ 2 * τ⁻¹ * (1 + τ⁻¹) := by
  obtain ⟨hN, -, hS⟩ := er_facts h
  exact edgeVal_mem_Icc N σ h.nonneg hN hS h.pos h.phi_lower h.phi_upper h.bound_Sigma hk hkp

/-- `n(x) − n(y) = N ϱ([x, y))` for `x ≤ y`. -/
private lemma er_nClass_sub {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {x y : ℝ}
    (hxy : x ≤ y) :
    nClass N σ x - nClass N σ y = N * (varrho N σ (Set.Ico x y)).toReal := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  have hsplit : varrho N σ (Set.Ici x) =
      varrho N σ (Set.Ico x y) + varrho N σ (Set.Ici y) := by
    rw [← measure_union _ measurableSet_Ici, Set.Ico_union_Ici_eq_Ici hxy]
    rw [Set.disjoint_left]
    intro z hz1 hz2
    exact absurd hz1.2 (not_lt.mpr hz2)
  unfold nClass
  rw [hsplit, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  ring

/-- `n` is nonincreasing. -/
private lemma er_nClass_anti {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {x y : ℝ}
    (hxy : x ≤ y) : nClass N σ y ≤ nClass N σ x := by
  have := er_nClass_sub hσ hN hxy
  have h0 : 0 ≤ (N : ℝ) * (varrho N σ (Set.Ico x y)).toReal := by positivity
  linarith

/-- `n ≥ 0`. -/
private lemma er_nClass_nonneg (σ : Fin M → ℝ) (x : ℝ) : 0 ≤ nClass N σ x := by
  unfold nClass; positivity

/-- `d_k ≤ M ∧ N` for `1 ≤ k ≤ p`, and `d_p = M ∧ N`. -/
private lemma er_cum {τ : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ)
    (hσ : ∀ j, 0 < σ j) {k : ℕ} (hk : 1 ≤ k) (hkp : k ≤ numBands N σ) :
    cumCount N σ k ≤ min M N ∧ cumCount N σ (numBands N σ) = min M N := by
  obtain ⟨hN, hM, hS⟩ := er_facts hda
  have hp := (card_innerCrit N σ hda.nonneg hN hS).2
  have hsum := (Ni_sum N σ hσ hN hM).2
  have hnn : ∀ l ∈ Finset.Icc 1 (numBands N σ), l ∉ Finset.Icc 1 k →
      0 ≤ bandCount N σ l := fun l _ _ => by unfold bandCount; positivity
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := fun l => bandCount N σ l)
    (Finset.Icc_subset_Icc le_rfl hkp) hnn
  obtain ⟨hc1, -, -⟩ := cumCount_spec hda hk hkp
  obtain ⟨hcp, -, -⟩ := cumCount_spec hda hp le_rfl
  rw [hsum] at hle hcp
  rw [← hc1] at hle
  constructor
  · have : (cumCount N σ k : ℝ) ≤ ((min M N : ℕ) : ℝ) := by
      rw [Nat.cast_min, min_comm]; exact hle
    exact_mod_cast this
  · have : (cumCount N σ (numBands N σ) : ℝ) = ((min M N : ℕ) : ℝ) := by
      rw [Nat.cast_min, min_comm]; exact hcp
    exact_mod_cast this

/-- `d_0 = 0`. -/
private lemma er_cum_zero (N : ℕ) (σ : Fin M → ℝ) : cumCount N σ 0 = 0 := by
  simp [cumCount]

/-- Two events of probability `≥ 1 − N^{−D−1}` intersect in an event of probability
`≥ 1 − N^{−D}`, for `N ≥ 2`. -/
private lemma er_hp_inter {Ω : Type*} [MeasureSpace Ω] {N : ℕ} {D : ℝ} {A B : Set Ω}
    (hN : 2 ≤ N) (hA : HighProbAt N (D + 1) A) (hB : HighProbAt N (D + 1) B) :
    HighProbAt N D (A ∩ B) := by
  unfold HighProbAt at *
  rw [Set.compl_inter]
  refine (measure_union_le _ _).trans ((add_le_add hA hB).trans ?_)
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : (0 : ℝ) < N := by linarith
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have e : (N : ℝ) ^ (-(D + 1)) = (N : ℝ) ^ (-D) * (N : ℝ)⁻¹ := by
    rw [show -(D + 1) = -D + -1 by ring, Real.rpow_add hpos, Real.rpow_neg_one]
  rw [e]
  have h0 : 0 ≤ (N : ℝ) ^ (-D) := by positivity
  have h1 : (N : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hN'
  nlinarith

/-- The eigenvalues `σ` of `Σ` are positive under Assumption 2.1. -/
private lemma er_sigma_pos {Ω : Type*} [MeasureSpace Ω] {τ : ℝ} {C : ℕ → ℝ}
    {Sig : Matrix (Fin M) (Fin M) ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ}
    (hm : IsModel τ C M N Sig X) : ∀ i, 0 < specOf Sig i := fun i => by
  rw [specOf_eq hm.sigma.posDef.isHermitian]
  exact hm.sigma.posDef.eigenvalues_pos i

/-- `C N^a ≤ N^b` for `a < b` and `N` large. -/
private lemma er_ev (C : ℝ) {a b : ℝ} (hab : a < b) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → C * (N : ℝ) ^ a ≤ (N : ℝ) ^ b := by
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) ^ (b - a)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1
    ((h1.eventually_ge_atTop C).and (Filter.eventually_ge_atTop 1))
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨h2, h3⟩ := hN₀ N hN
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc C * (N : ℝ) ^ a ≤ (N : ℝ) ^ (b - a) * (N : ℝ) ^ a :=
        mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hN.le _)
    _ = (N : ℝ) ^ b := by rw [← Real.rpow_add hN]; ring_nf

/-- `(N − 1 : ℕ) = N − 1` in `ℝ` for `N ≥ 2`. -/
private lemma er_cast_pred (hN : 2 ≤ N) : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
  rw [Nat.cast_sub (by omega)]; simp

/-- (phi_bounded), (bound_Sigma), (Sigma_gap) at `N − 1` with `τ/2`, from those at `N` with `τ`. -/
private lemma er_da_pred {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) (hN : 2 ≤ N) :
    DensityAssumptions (τ / 2) (N - 1) σ := by
  have hτ := h.pos
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hc := er_cast_pred hN
  have hφl := h.phi_lower
  have hφu := h.phi_upper
  unfold phiRatio at hφl hφu
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  refine ⟨by positivity, h.nonneg, ?_, ?_, ?_, ?_⟩
  · unfold phiRatio
    rw [hc, le_div_iff₀ hN1]
    rw [le_div_iff₀ (by linarith)] at hφl
    nlinarith
  · unfold phiRatio
    rw [hc, div_le_iff₀ hN1]
    rw [div_le_iff₀ (by linarith)] at hφu
    have : (τ / 2)⁻¹ = 2 * τ⁻¹ := by field_simp
    rw [this]
    have hτi : 0 < τ⁻¹ := inv_pos.mpr hτ
    nlinarith
  · intro i
    have := h.bound_Sigma i
    have : τ⁻¹ ≤ (τ / 2)⁻¹ := inv_anti₀ (by positivity) (by linarith)
    linarith
  · have := (h.mono (show 0 < τ / 2 by positivity) (by linarith)).Sigma_gap
    linarith

section SpecSub

variable {K : ℕ} {A : Matrix (Fin K) (Fin K) ℝ}

/-- The orthogonal matrix whose columns are the eigenvectors of `A`. -/
private def erU (hA : A.IsHermitian) : Matrix (Fin K) (Fin K) ℝ :=
  (hA.eigenvectorUnitary : Matrix (Fin K) (Fin K) ℝ)

/-- The coordinates of `w` in the eigenbasis of `A`. -/
private def erC (hA : A.IsHermitian) (w : Fin K → ℝ) : Fin K → ℝ :=
  star (erU hA) *ᵥ w

private lemma erU_star_mul (hA : A.IsHermitian) : star (erU hA) * erU hA = 1 :=
  Unitary.coe_star_mul_self _

private lemma erU_mul_star (hA : A.IsHermitian) : erU hA * star (erU hA) = 1 :=
  Unitary.coe_mul_star_self _

private lemma erU_mulVec_erC (hA : A.IsHermitian) (w : Fin K → ℝ) : erU hA *ᵥ erC hA w = w := by
  unfold erC
  rw [mulVec_mulVec, erU_mul_star, one_mulVec]

private lemma erU_orth_dot (hA : A.IsHermitian) (x y : Fin K → ℝ) :
    (erU hA *ᵥ x) ⬝ᵥ (erU hA *ᵥ y) = x ⬝ᵥ y := by
  rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, mulVec_mulVec]
  have : (erU hA)ᵀ * erU hA = 1 := by
    have h := erU_star_mul hA
    rwa [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h
  rw [this, one_mulVec]

private lemma erU_decomp (hA : A.IsHermitian) :
    A = erU hA * diagonal hA.eigenvalues * star (erU hA) := by
  have := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at this
  simpa [erU] using this

private lemma er_dot_eq_sum (hA : A.IsHermitian) (w : Fin K → ℝ) :
    w ⬝ᵥ w = ∑ j, (erC hA w j) ^ 2 := by
  conv_lhs => rw [← erU_mulVec_erC hA w]
  rw [erU_orth_dot]
  simp [dotProduct, sq]

private lemma er_quad_eq_sum (hA : A.IsHermitian) (w : Fin K → ℝ) :
    w ⬝ᵥ (A *ᵥ w) = ∑ j, hA.eigenvalues j * (erC hA w j) ^ 2 := by
  have h1 : A *ᵥ w = erU hA *ᵥ (diagonal hA.eigenvalues *ᵥ erC hA w) := by
    conv_lhs => rw [erU_decomp hA]
    unfold erC
    rw [← mulVec_mulVec, ← mulVec_mulVec]
  rw [h1]
  nth_rewrite 1 [← erU_mulVec_erC hA w]
  rw [erU_orth_dot]
  simp only [dotProduct, mulVec_diagonal, sq]
  refine Finset.sum_congr rfl fun j _ => by ring

/-- The linear map recording the eigencoordinates of `w` indexed by `s`. -/
private def erMap (hA : A.IsHermitian) (s : Finset (Fin K)) : (Fin K → ℝ) →ₗ[ℝ] (s → ℝ) :=
  (LinearMap.funLeft ℝ ℝ (Subtype.val : s → Fin K)) ∘ₗ Matrix.mulVecLin (star (erU hA))

private lemma er_mem_ker_erMap (hA : A.IsHermitian) (s : Finset (Fin K)) (w : Fin K → ℝ) :
    w ∈ LinearMap.ker (erMap hA s) ↔ ∀ j ∈ s, erC hA w j = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h j hj
    exact congrFun h ⟨j, hj⟩
  · intro h
    funext j
    exact h j.1 j.2

private lemma er_le_finrank_ker (hA : A.IsHermitian) (s : Finset (Fin K)) :
    K ≤ Module.finrank ℝ (LinearMap.ker (erMap hA s)) + s.card := by
  have h := LinearMap.finrank_range_add_finrank_ker (erMap hA s)
  have h1 : Module.finrank ℝ (LinearMap.range (erMap hA s)) ≤ s.card := by
    calc Module.finrank ℝ (LinearMap.range (erMap hA s)) ≤ Module.finrank ℝ (s → ℝ) :=
          Submodule.finrank_le _
      _ = s.card := by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  have h2 : Module.finrank ℝ (Fin K → ℝ) = K := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  omega

private lemma er_eigCount_add_card (hA : A.IsHermitian) (E : ℝ) :
    eigCount A E + (Finset.univ.filter fun j => ¬ E ≤ hA.eigenvalues j).card = K := by
  have : eigCount A E = (Finset.univ.filter fun j => E ≤ hA.eigenvalues j).card := by
    unfold eigCount
    rw [specOf_eq hA]
  rw [this, Finset.card_filter_add_card_filter_not]
  simp

/-- A spectral subspace: dimension at least `n_A(E)`, and `⟨w, A w⟩ ≥ E |w|²` on it. -/
private lemma er_spectral_subspace (hA : A.IsHermitian) (E : ℝ) :
    ∃ W : Submodule ℝ (Fin K → ℝ), eigCount A E ≤ Module.finrank ℝ W ∧
      ∀ w ∈ W, E * (w ⬝ᵥ w) ≤ w ⬝ᵥ (A *ᵥ w) := by
  set s := Finset.univ.filter fun j => ¬ E ≤ hA.eigenvalues j with hs
  have hz : ∀ w ∈ LinearMap.ker (erMap hA s), ∀ j, hA.eigenvalues j < E → erC hA w j = 0 := by
    intro w hw j hj
    exact (er_mem_ker_erMap hA s w).mp hw j (by simpa [hs] using hj)
  refine ⟨LinearMap.ker (erMap hA s), ?_, ?_⟩
  · have h1 := er_le_finrank_ker hA s
    have h2 : eigCount A E + s.card = K := er_eigCount_add_card hA E
    omega
  · intro w hw
    rw [er_quad_eq_sum hA, er_dot_eq_sum hA, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hj : hA.eigenvalues j < E
    · rw [hz w hw j hj]; simp
    · exact mul_le_mul_of_nonneg_right (not_lt.mp hj) (sq_nonneg _)

/-- `n_A(E) ≤ n_{cA}(cE)` for `c > 0`. -/
private lemma er_eigCount_le_smul (hA : A.IsHermitian) {c : ℝ} (hc : 0 < c) (E : ℝ) :
    eigCount A E ≤ eigCount (c • A) (c * E) := by
  obtain ⟨W, hW1, hW2⟩ := er_spectral_subspace hA E
  have hcA : (c • A).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_smul, hA.eq, star_trivial]
  refine hW1.trans (eigCount_ge_of_subspace hcA W fun w hw => ?_)
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hW2 w hw) hc.le

/-- `n_{cA}(cE) = n_A(E)` for `c > 0`. -/
private lemma er_eigCount_smul (hA : A.IsHermitian) {c : ℝ} (hc : 0 < c) (E : ℝ) :
    eigCount (c • A) (c * E) = eigCount A E := by
  have hcA : (c • A).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_smul, hA.eq, star_trivial]
  refine le_antisymm ?_ (er_eigCount_le_smul hA hc E)
  have := er_eigCount_le_smul hcA (inv_pos.mpr hc) (c * E)
  rwa [smul_smul, inv_mul_cancel₀ hc.ne', one_smul, ← mul_assoc, inv_mul_cancel₀ hc.ne',
    one_mul] at this

end SpecSub

/-- `λ̇_{k,i} = (N/(N−1)) λ_j(π̄ B π̄)`, `j = Ṅ_1 + ⋯ + Ṅ_{k−1} + i`. -/
private lemma er_C_pos {τ : ℝ} (hτ : 0 < τ) : 0 < edgeC2 τ ∧ 0 < edgec2 τ := by
  have hs := Real.sqrt_pos.2 hτ
  have hcx : 0 < edgecx τ := by unfold edgecx; positivity
  refine ⟨by unfold edgeC2 edgeCx; positivity, by unfold edgec2 edgeCx; positivity⟩

private lemma er_edgeTau'_le {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) : edgeTau' τ ≤ τ / 2 := by
  have hs := Real.sqrt_pos.2 hτ
  have hcx : 0 < edgecx τ := by unfold edgecx; positivity
  have h2 : 0 < edgec2 τ := by unfold edgec2 edgeCx; positivity
  have h3 : 0 < edgeC3 τ := by unfold edgeC3; positivity
  have h0 : 0 < edgeRho0 τ := by unfold edgeRho0; positivity
  have h1 : 0 < edgeRho1 τ := by unfold edgeRho1; positivity
  have h10 : edgeRho1 τ ≤ edgeRho0 τ := min_le_left _ _
  have h1τ : edgeRho1 τ ≤ τ / 2 := by
    refine h10.trans ?_
    unfold edgeRho0; linarith [min_le_right (edgecx τ) τ]
  have hc2τ : edgec2 τ ≤ τ ^ 3 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have heq : edgeTau' τ = edgec2 τ * edgeRho1 τ ^ 2 / 32 := by
    unfold edgeTau' edgeTau0; ring
  rw [heq]
  have hsq : edgeRho1 τ ^ 2 ≤ (τ / 2) ^ 2 := pow_le_pow_left₀ h1.le h1τ 2
  have hmul : edgec2 τ * edgeRho1 τ ^ 2 ≤ τ ^ 3 / 4 * (τ / 2) ^ 2 :=
    mul_le_mul hc2τ hsq (sq_nonneg _) (by positivity)
  have hτ4 : τ ^ 4 ≤ 1 := pow_le_one₀ hτ.le hτ1
  nlinarith

/-- `0 < τ'(τ)`, `τ₀(τ) = 4 τ'(τ)` and `τ'(τ) ≤ τ/2` for `τ ∈ (0, 1]`. -/
private lemma er_tau_facts {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    0 < edgeTau' τ ∧ edgeTau0 τ = 4 * edgeTau' τ ∧ edgeTau' τ ≤ τ / 2 := by
  refine ⟨edgeTau'_pos hτ, by unfold edgeTau'; ring, er_edgeTau'_le hτ hτ1⟩

/-- A positive point of `supp ϱ` lies in a band `[a_{2k}, a_{2k−1}]`, `1 ≤ k ≤ p`. -/
private lemma er_supp {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) {y : ℝ}
    (hy : y ∈ (varrho N σ).support) (hy0 : 0 < y) :
    ∃ k, 1 ≤ k ∧ k ≤ numBands N σ ∧ edgeVal N σ (2 * k) ≤ y ∧ y ≤ edgeVal N σ (2 * k - 1) := by
  obtain ⟨hN, -, hS⟩ := er_facts h
  obtain ⟨k, hk1, hk2, hyk⟩ := (mem_support_varrho_iff N σ h.nonneg hN hS hy0).1 hy
  exact ⟨k, hk1, hk2, hyk.1, hyk.2⟩

/-- A point of a band `[a_{2k}, a_{2k−1}]` with `0 < y` lies in `supp ϱ`. -/
private lemma er_mem_supp {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) {k : ℕ}
    (hk : 1 ≤ k) (hkp : k ≤ numBands N σ) {y : ℝ} (hy0 : 0 < y)
    (hy1 : edgeVal N σ (2 * k) ≤ y) (hy2 : y ≤ edgeVal N σ (2 * k - 1)) :
    y ∈ (varrho N σ).support := by
  obtain ⟨hN, -, hS⟩ := er_facts h
  exact (mem_support_varrho_iff N σ h.nonneg hN hS hy0).2 ⟨k, hk, hkp, hy1, hy2⟩

/-- A point `x ≥ r` at distance `≥ r` from every band is at distance `≥ r` from `supp ϱ`. -/
private lemma er_dist {τ : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ) {x r : ℝ}
    (hr : 0 ≤ r) (hx : r ≤ x) (hne : (varrho N σ).support.Nonempty)
    (h : ∀ l, 1 ≤ l → l ≤ numBands N σ →
      x + r ≤ edgeVal N σ (2 * l) ∨ edgeVal N σ (2 * l - 1) + r ≤ x) :
    r ≤ Metric.infDist x (varrho N σ).support := by
  refine (Metric.le_infDist hne).2 fun y hy => ?_
  rw [Real.dist_eq]
  rcases le_or_gt y 0 with hy0 | hy0
  · rw [abs_of_nonneg (by linarith)]; linarith
  obtain ⟨l, hl1, hl2, hyl1, hyl2⟩ := er_supp hda hy hy0
  rcases h l hl1 hl2 with h' | h'
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith)]; linarith

/-- `a_{2k−2} ≥ a_{2k−1} + τ` when the edge `2k − 1` is regular at `τ`, `k ≥ 2`. -/
private lemma er_sep_up {τ : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ) {k : ℕ}
    (hk : 2 ≤ k) (hreg : RegularEdge τ N σ (2 * k - 1)) :
    edgeVal N σ (2 * k - 1) + τ ≤ edgeVal N σ (2 * k - 2) := by
  have hkp := hreg.2.1
  have h1 := hreg.2.2.2.1 (2 * k - 2) (by omega) (by omega) (by omega)
  have h2 := er_anti hda (i := 2 * k - 2) (j := 2 * k - 1) (by omega) (by omega) hkp
  rw [abs_of_nonpos (by linarith)] at h1
  linarith

/-- `a_{2k+1} + τ ≤ a_{2k}` when the edge `2k` is regular at `τ`, `k < p`. -/
private lemma er_sep_dn {τ : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ) {k : ℕ}
    (hk : 1 ≤ k) (hkp : k < numBands N σ) (hreg : RegularEdge τ N σ (2 * k)) :
    edgeVal N σ (2 * k + 1) + τ ≤ edgeVal N σ (2 * k) := by
  have h1 := hreg.2.2.2.1 (2 * k + 1) (by omega) (by omega) (by omega)
  have h2 := er_anti hda (i := 2 * k) (j := 2 * k + 1) (by omega) (by omega) (by omega)
  rw [abs_of_nonneg (by linarith)] at h1
  linarith

/-- `x_{2k} < 0` for a band `k < p`, and for `k = p` when `R = #{σ_i > 0}/N < 1`. -/
private lemma er_xCrit_neg {τ : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ) {k : ℕ}
    (hk : 1 ≤ k) (hkp : k ≤ numBands N σ) (hcase : k < numBands N σ ∨ massRatio N σ < 1) :
    xCrit N σ (2 * k) < 0 := by
  obtain ⟨hN, -, hS⟩ := er_facts hda
  have hσ := hda.nonneg
  have hp := card_innerCrit N σ hσ hN hS
  by_cases hkl : k < numBands N σ
  · have hne : 2 * k ≠ 2 * numBands N σ := by omega
    unfold xCrit
    rw [ite_eq_right_of_eq_false _ _ (eq_false hne)]
    have hlen : ((innerCrit N σ).sort (· ≤ ·)).reverse.length = Multiset.card (innerCrit N σ) := by
      rw [List.length_reverse, Multiset.length_sort]
    have hidx : 2 * k - 1 < ((innerCrit N σ).sort (· ≤ ·)).reverse.length := by
      rw [hlen]; omega
    rw [List.getD_eq_getElem _ _ hidx]
    have hmem := List.getElem_mem hidx
    rw [List.mem_reverse, Multiset.mem_sort] at hmem
    exact (Multiset.mem_filter.1 hmem).2.1
  · have hk' : k = numBands N σ := by omega
    have hmr : massRatio N σ < 1 := hcase.resolve_left hkl
    unfold xCrit
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 2 * k = 2 * numBands N σ by omega))]
    obtain ⟨-, hF⟩ := yEdge_spec N σ hσ hN hS
    rw [inv_lt_zero]
    by_contra hy
    push Not at hy
    have hle : ∑ s ∈ posVals σ, weight N σ s * s ^ 2 / (yEdge N σ + s) ^ 2 ≤
        ∑ s ∈ posVals σ, weight N σ s := by
      refine Finset.sum_le_sum fun s hs => ?_
      have hs0 : 0 < s := (Finset.mem_filter.1 hs).2
      have hw : 0 ≤ weight N σ s := by unfold weight; positivity
      have h1 : s ^ 2 ≤ (yEdge N σ + s) ^ 2 := by nlinarith
      rw [mul_div_assoc]
      calc weight N σ s * (s ^ 2 / (yEdge N σ + s) ^ 2) ≤ weight N σ s * 1 :=
            mul_le_mul_of_nonneg_left (div_le_one_of_le₀ h1 (sq_nonneg _)) hw
        _ = weight N σ s := mul_one _
    have hsw := sum_weight N σ
    unfold FChart1 at hF
    linarith

/-- In the gap above the band `k` (between `a_{2k−1}` and `a_{2k−2}`, or above `a_1`):
`n(x) = d_{k−1}`. -/
private lemma er_n_gap_up {τ : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ) {k : ℕ}
    (hk : 1 ≤ k) (hkp : k ≤ numBands N σ) {x : ℝ} (hx1 : edgeVal N σ (2 * k - 1) ≤ x)
    (hx2 : 2 ≤ k → x ≤ edgeVal N σ (2 * k - 2)) : nClass N σ x = cumCount N σ (k - 1) := by
  obtain ⟨hN, -, hS⟩ := er_facts hda
  have hσ := hda.nonneg
  have hna := (nClass_edgeVal hda hk hkp).1
  have hup := er_nClass_anti hσ hN hx1
  rcases lt_or_ge k 2 with hk2 | hk2
  · have : k = 1 := by omega
    subst this
    rw [er_cum_zero] at hna ⊢
    have := er_nClass_nonneg (N := N) σ x
    push_cast at hna ⊢
    linarith
  · have hb := edgeVal_band_lt N σ hσ hN hS hk hkp
    have h0 := (er_edge_mem hda (k := 2 * k) (by omega) (by omega)).1
    have hpos : 0 < edgeVal N σ (2 * (k - 1)) := by
      rw [show 2 * (k - 1) = 2 * k - 2 by omega]; linarith [hx2 hk2]
    have hnb := (nClass_edgeVal hda (k := k - 1) (by omega) (by omega)).2 hpos
    rw [show 2 * (k - 1) = 2 * k - 2 by omega] at hnb
    have hlo := er_nClass_anti hσ hN (hx2 hk2)
    linarith

/-- In the gap below the band `k` (between `a_{2k+1}` and `a_{2k}`, or in `(0, a_{2p}]`):
`n(x) = d_k`. -/
private lemma er_n_gap_dn {τ : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ)
    (hσp : ∀ j, 0 < σ j) {k : ℕ} (hk : 1 ≤ k) (hkp : k ≤ numBands N σ) {x : ℝ} (hx0 : 0 < x)
    (hx1 : x ≤ edgeVal N σ (2 * k)) (hx2 : k < numBands N σ → edgeVal N σ (2 * k + 1) ≤ x) :
    nClass N σ x = cumCount N σ k := by
  obtain ⟨hN, hM, hS⟩ := er_facts hda
  have hσ := hda.nonneg
  have hna := (nClass_edgeVal hda hk hkp).2 (by linarith)
  have hlo := er_nClass_anti hσ hN hx1
  rcases lt_or_eq_of_le hkp with hlt | heq
  · have hnb := (nClass_edgeVal hda (k := k + 1) (by omega) (by omega)).1
    rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega, show k + 1 - 1 = k by omega] at hnb
    have hup := er_nClass_anti hσ hN (hx2 hlt)
    linarith
  · have hcp := (er_cum hda hσp hk hkp).2
    rw [← heq] at hcp
    have hz := (Ni_sum N σ hσp hN hM).1
    have := isProbabilityMeasure_varrho N σ hσ hN
    have hdisj : Disjoint ({0} : Set ℝ) (Set.Ici x) := by
      rw [Set.disjoint_left]
      intro t ht1 ht2
      rw [Set.mem_singleton_iff] at ht1
      rw [ht1, Set.mem_Ici] at ht2
      linarith
    have hsum : varrho N σ {0} + varrho N σ (Set.Ici x) ≤ 1 := by
      rw [← measure_union hdisj measurableSet_Ici]
      exact prob_le_one
    have hsum' : (varrho N σ {0}).toReal + (varrho N σ (Set.Ici x)).toReal ≤ 1 := by
      rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
      have := ENNReal.toReal_mono ENNReal.one_ne_top hsum
      simpa using this
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hmul := mul_le_mul_of_nonneg_left hsum' hN0
    have hle : nClass N σ x ≤ (min M N : ℕ) := by
      unfold nClass
      rw [Nat.cast_min]
      rcases le_total M N with hMN | hMN
      · rw [min_eq_left (by exact_mod_cast hMN)]
        rw [max_eq_left (by have : (M : ℝ) ≤ N := by exact_mod_cast hMN
                            linarith)] at hz
        nlinarith
      · rw [min_eq_right (by exact_mod_cast hMN)]
        have : 0 ≤ (varrho N σ {0}).toReal := ENNReal.toReal_nonneg
        nlinarith
    rw [hcp] at hna ⊢
    linarith

/-- `Σ̲⁻¹ = diag(Σ⁻¹, 1)` for `Σ > 0`. -/
private lemma er_ulSigma_inv {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) :
    (ulSigma N Sig)⁻¹ = fromBlocks (cplx Sig)⁻¹ 0 0 1 := by
  have hu : IsUnit (cplx Sig) := hSig.isUnit.map (algebraMap ℝ ℂ).mapMatrix
  rw [ulSigma, inv_fromBlocks_zero₂₁_of_isUnit_iff _ _ _ (iff_of_true hu isUnit_one)]
  simp

/-- The `𝓘_N × 𝓘_N` block of `Σ̲⁻¹ (G − Π) Σ̲⁻¹` is `G_N − m`. -/
private lemma er_lawMat_22 {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) :
    (lawMat Sig Xm z).toBlocks₂₂ = GN Sig Xm z - mFun N (specOf Sig) z • 1 := by
  have h2 : ∀ K : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ,
      (fromBlocks (cplx Sig)⁻¹ 0 0 1 * K * fromBlocks (cplx Sig)⁻¹ 0 0 1).toBlocks₂₂ =
        K.toBlocks₂₂ := by
    intro K
    rw [← fromBlocks_toBlocks K]
    simp [fromBlocks_multiply]
  unfold lawMat
  rw [er_ulSigma_inv hSig, h2]
  ext i j
  simp [toBlocks₂₂, piMat, (GeqG hSig Xm hz).1]

/-- `⟨(0, 1_N), A (0, 1_N)⟩ = ⟨1_N, A_{𝓘_N 𝓘_N} 1_N⟩`. -/
private lemma er_testBilin_inr (A : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) :
    testBilin (Sum.elim (0 : Fin M → ℝ) (fun _ : Fin N => (1 : ℝ))) A
      (Sum.elim (0 : Fin M → ℝ) (fun _ : Fin N => (1 : ℝ))) =
      testBilin (fun _ : Fin N => (1 : ℝ)) A.toBlocks₂₂ (fun _ => 1) := by
  simp [testBilin, dotProduct, mulVec, Fintype.sum_sum_type, toBlocks₂₂]

/-- `|(0, 1_N)| = √N`. -/
private lemma er_testNorm_inr :
    testNorm (Sum.elim (0 : Fin M → ℝ) (fun _ : Fin N => (1 : ℝ))) = √N := by
  simp [testNorm, Fintype.sum_sum_type]

/-- `⟨1, (G − w) 1⟩ = ⟨1, G 1⟩ − N w`. -/
private lemma er_testBilin_sub (G : Matrix (Fin N) (Fin N) ℂ) (w : ℂ) :
    testBilin (fun _ : Fin N => (1 : ℝ)) (G - w • 1) (fun _ => 1) =
      testBilin (fun _ : Fin N => (1 : ℝ)) G (fun _ => 1) - N * w := by
  simp only [testBilin, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul]
  simp [dotProduct]
  ring

/-- `A − E` is invertible when `E` is not an eigenvalue of the symmetric matrix `A`. -/
private lemma er_isUnit_sub {K : ℕ} {A : Matrix (Fin K) (Fin K) ℝ} (hA : A.IsHermitian) {E : ℝ}
    (hne : ∀ j, specOf A j ≠ E) : IsUnit (A - E • (1 : Matrix (Fin K) (Fin K) ℝ)) := by
  have hE : E ∉ spectrum ℝ A := by
    rw [hA.spectrum_real_eq_range_eigenvalues]
    rintro ⟨j, hj⟩
    exact hne j (by rw [specOf_eq hA]; exact hj)
  rw [spectrum.mem_iff, not_not] at hE
  have e : A - E • (1 : Matrix (Fin K) (Fin K) ℝ) =
      -(algebraMap ℝ (Matrix (Fin K) (Fin K) ℝ) E - A) := by
    rw [Algebra.algebraMap_eq_smul_one]; abel
  rw [e]
  exact hE.neg

/-- The secular count at `E₁ > 0`, `z₁ = E₁ + i δ₁`: if no eigenvalue of `B = XᵀΣX` lies within
`δ₁` of `E₁`, the anisotropic law holds at `z₁` for the test vector `(0, 1_N)`, and
`Re m(z₁) + Im m(z₁) + 2 N^{ε} Ψ(z₁) < 0`, then `π̄ B π̄` and `B` have the same number of
eigenvalues `≥ E₁`. -/
private lemma er_secular {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (hN : 0 < N) {E₁ δ₁ ε₄ : ℝ} (hE₁ : 0 < E₁) (hδ : 0 < δ₁)
    (hgap : ∀ j, δ₁ ≤ |specOf (QN Sig Xm) j - E₁|)
    (hlaw : ‖testBilin (Sum.elim (0 : Fin M → ℝ) (fun _ : Fin N => (1 : ℝ)))
        (lawMat Sig Xm ((E₁ : ℂ) + δ₁ * Complex.I)) (Sum.elim 0 fun _ => 1)‖ ≤
      (N : ℝ) ^ ε₄ * (Psi N (specOf Sig) ((E₁ : ℂ) + δ₁ * Complex.I) *
        testNorm (Sum.elim (0 : Fin M → ℝ) (fun _ : Fin N => (1 : ℝ))) *
        testNorm (Sum.elim (0 : Fin M → ℝ) (fun _ : Fin N => (1 : ℝ)))))
    (hsign : (mFun N (specOf Sig) ((E₁ : ℂ) + δ₁ * Complex.I)).re +
        (mFun N (specOf Sig) ((E₁ : ℂ) + δ₁ * Complex.I)).im +
        2 * ((N : ℝ) ^ ε₄ * Psi N (specOf Sig) ((E₁ : ℂ) + δ₁ * Complex.I)) < 0) :
    eigCount (QN Sig (Xdot Xm)) E₁ = eigCount (QN Sig Xm) E₁ := by
  set z₁ : ℂ := (E₁ : ℂ) + δ₁ * Complex.I with hz₁
  have hz : 0 < z₁.im := by simp [hz₁, hδ]
  have hB := XSX_isHermitian hSig.1 Xm
  have hres : (fun _ => (1 : ℝ)) ⬝ᵥ ((QN Sig Xm - E₁ • (1 : Matrix (Fin N) (Fin N) ℝ))⁻¹ *ᵥ
      fun _ => 1) ≤ (testBilin (fun _ : Fin N => (1 : ℝ)) (GN Sig Xm z₁) (fun _ => 1)).re +
        (testBilin (fun _ : Fin N => (1 : ℝ)) (GN Sig Xm z₁) (fun _ => 1)).im :=
    resolvent_real_le hB (fun _ => (1 : ℝ)) hδ hgap
  rw [er_testBilin_inr, er_lawMat_22 hSig Xm hz, er_testBilin_sub, er_testNorm_inr] at hlaw
  set T := testBilin (fun _ : Fin N => (1 : ℝ)) (GN Sig Xm z₁) (fun _ => 1) with hT
  set m := mFun N (specOf Sig) z₁ with hm
  set P := (N : ℝ) ^ ε₄ * Psi N (specOf Sig) z₁ with hP
  have hNN : √(N : ℝ) * √N = N := Real.mul_self_sqrt (Nat.cast_nonneg N)
  have h1 : ‖T - N * m‖ ≤ P * N := by
    have e : (N : ℝ) ^ ε₄ * (Psi N (specOf Sig) z₁ * √(N : ℝ) * √N) = P * N := by
      rw [hP, mul_assoc (Psi N (specOf Sig) z₁), hNN]; ring
    rw [← e]; exact hlaw
  have hre := (abs_le.1 ((Complex.abs_re_le_norm (T - N * m)).trans h1)).2
  have him := (abs_le.1 ((Complex.abs_im_le_norm (T - N * m)).trans h1)).2
  have e1 : (T - N * m).re = T.re - N * m.re := by simp
  have e2 : (T - N * m).im = T.im - N * m.im := by simp
  rw [e1] at hre
  rw [e2] at him
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hneg : (fun _ => (1 : ℝ)) ⬝ᵥ ((QN Sig Xm - E₁ • (1 : Matrix (Fin N) (Fin N) ℝ))⁻¹ *ᵥ
      fun _ => 1) < 0 := by
    have : (N : ℝ) * (m.re + m.im + 2 * P) < 0 := mul_neg_of_pos_of_neg hNpos hsign
    linarith
  have hinv : IsUnit (QN Sig Xm - E₁ • (1 : Matrix (Fin N) (Fin N) ℝ)) :=
    er_isUnit_sub (A := QN Sig Xm) hB (E := E₁) (fun j h => by
      have := hgap j; rw [h, sub_self, abs_zero] at this; linarith)
  exact eigCount_compress_secular hSig.1 Xm hE₁ hinv hneg

/-- Near a regular edge `a_k` with `x_k < 0`: for `Im z > 0` and `|z − a_k| ≤ τ₀(τ)`,
`Re m(z) + Im m(z) ≤ −c_x(τ) + 4 √(|z − a_k| / c₂(τ))` and `Im m(z) ≤ 1`. -/
private lemma er_sign {τ : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ) (hτ1 : τ ≤ 1)
    {k : ℕ} (hreg : RegularEdge τ N σ k) (hx : xCrit N σ k < 0) {z : ℂ} (hz : 0 < z.im)
    (hza : ‖z - edgeVal N σ k‖ ≤ edgeTau0 τ) :
    (mFun N σ z).re + (mFun N σ z).im ≤
      -edgecx τ + 4 * √(‖z - edgeVal N σ k‖ / edgec2 τ) ∧ (mFun N σ z).im ≤ 1 := by
  have hτ := hda.pos
  obtain ⟨hloc, -, hlow, -, -⟩ := z_a_taylor hda hreg hz.le hza
  have hm : mExt N σ z = mFun N σ z := by
    unfold mExt; rw [ite_eq_left_of_eq_true _ _ (eq_true hz)]
  rw [hm] at hloc hlow
  have hcx := (xCrit_bounds hda hreg).1
  rw [abs_of_neg hx] at hcx
  have hc2 := (er_C_pos hτ).2
  set d := ‖mFun N σ z - xCrit N σ k‖ with hd
  have hd0 : 0 ≤ d := norm_nonneg _
  have hdle : d ≤ 2 * √(‖z - edgeVal N σ k‖ / edgec2 τ) := by
    have h4 : d ^ 2 ≤ 4 * (‖z - edgeVal N σ k‖ / edgec2 τ) := by
      rw [mul_div_assoc']
      rw [le_div_iff₀ hc2]
      nlinarith
    have : d ≤ √(4 * (‖z - edgeVal N σ k‖ / edgec2 τ)) := Real.le_sqrt_of_sq_le h4
    rwa [Real.sqrt_mul (by norm_num), show √(4 : ℝ) = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)] at this
  have hre : (mFun N σ z).re ≤ xCrit N σ k + d := by
    have := Complex.re_le_norm (mFun N σ z - xCrit N σ k)
    simp only [Complex.sub_re, Complex.ofReal_re] at this
    linarith
  have him : (mFun N σ z).im ≤ d := by
    have := Complex.im_le_norm (mFun N σ z - xCrit N σ k)
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
    linarith
  have hρ1 : edgeRho1 τ ≤ 1 := by
    have h10 : edgeRho1 τ ≤ edgeRho0 τ := min_le_left _ _
    have : edgeRho0 τ ≤ τ / 2 := by unfold edgeRho0; linarith [min_le_right (edgecx τ) τ]
    linarith
  exact ⟨by linarith, by linarith⟩

/-- `Ψ(z) ≤ 2 √(1/(N η))` when `Im m(z) ≤ 1` and `N η ≥ 1`. -/
private lemma er_psi_le {σ : Fin M → ℝ} {z : ℂ} (hm : (mFun N σ z).im ≤ 1)
    (hNη : 1 ≤ (N : ℝ) * z.im) : Psi N σ z ≤ 2 * √(1 / ((N : ℝ) * z.im)) := by
  unfold Psi
  have h0 : 0 < (N : ℝ) * z.im := by linarith
  have h1 : √((mFun N σ z).im / (N * z.im)) ≤ √(1 / ((N : ℝ) * z.im)) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hm h0.le)
  have h2 : 1 / ((N : ℝ) * z.im) ≤ √(1 / ((N : ℝ) * z.im)) := by
    have h3 : 1 / ((N : ℝ) * z.im) ≤ 1 := by rw [div_le_one h0]; exact hNη
    have h4 : 0 ≤ 1 / ((N : ℝ) * z.im) := by positivity
    calc 1 / ((N : ℝ) * z.im) = √((1 / ((N : ℝ) * z.im)) ^ 2) := (Real.sqrt_sq h4).symm
      _ ≤ √(1 / ((N : ℝ) * z.im)) := Real.sqrt_le_sqrt (by nlinarith)
  linarith

/-- `N^a ≤ c` for `a < 0`, `c > 0` and `N` large. -/
private lemma er_ev_small {c a : ℝ} (hc : 0 < c) (ha : a < 0) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (N : ℝ) ^ a ≤ c := by
  obtain ⟨N₀, h⟩ := er_ev (1 / c) (a := a) (b := 0) ha
  refine ⟨N₀, fun N hN => ?_⟩
  have := h N hN
  rw [Real.rpow_zero] at this
  rw [div_mul_eq_mul_div, one_mul, div_le_one hc] at this
  exact this

/-- `R = #{σ_i > 0}/N = M/N` for positive `σ`. -/
private lemma er_massRatio {σ : Fin M → ℝ} (hσ : ∀ j, 0 < σ j) :
    massRatio N σ = (M : ℝ) / N := by
  unfold massRatio
  rw [Finset.filter_true_of_mem (fun i _ => hσ i), Finset.card_univ, Fintype.card_fin]

/-! ## Counting eigenvalues of `−A` -/

open Polynomial in
private lemma er_charpoly_neg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    (-A).charpoly = (diagonal (fun j => -hA.eigenvalues j)).charpoly := by
  have hs := hA.spectral_theorem
  have h1 : -A = (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
      diagonal (fun j => -hA.eigenvalues j) *
        star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) := by
    conv_lhs => rw [hs]
    rw [Unitary.conjStarAlgAut_apply]
    simp [← diagonal_neg]
  rw [h1, charpoly_mul_comm, ← mul_assoc]
  simp

private lemma er_specOf_neg_perm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    ∃ e : Equiv.Perm (Fin n), specOf (-A) = fun j => -specOf A (e j) := by
  have hA' : (-A).IsHermitian := hA.neg
  have hD : (diagonal (fun j => -hA.eigenvalues j)).IsHermitian := isHermitian_diagonal _
  have h1 : hA'.eigenvalues = hD.eigenvalues :=
    (hA'.eigenvalues_eq_eigenvalues_iff hD).2 (er_charpoly_neg hA)
  obtain ⟨e, he⟩ := exists_perm_specOf_diagonal (fun j => -hA.eigenvalues j)
  refine ⟨e, ?_⟩
  rw [specOf_eq hA', h1, ← specOf_eq hD, he, specOf_eq hA]
  rfl

/-- The number of eigenvalues of `A` that are `≤ x`. -/
private def erLe {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : ℝ) : ℕ :=
  (Finset.univ.filter fun j => specOf A j ≤ x).card

/-- The number of eigenvalues of `A` that are `> x`. -/
private def erGt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : ℝ) : ℕ :=
  (Finset.univ.filter fun j => x < specOf A j).card

private lemma er_eigCount_neg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (E : ℝ) : eigCount (-A) E = erLe A (-E) := by
  obtain ⟨e, he⟩ := er_specOf_neg_perm hA
  unfold eigCount erLe
  rw [he]
  refine Finset.card_equiv e ?_
  intro j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor <;> intro h <;> linarith

private lemma er_le_add_gt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : ℝ) :
    erLe A x + erGt A x = n := by
  unfold erLe erGt
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun j => specOf A j ≤ x)
  simp only [not_le, Finset.card_univ, Fintype.card_fin] at this
  exact this

private lemma er_gt_anti {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {x y : ℝ} (hxy : x ≤ y) :
    erGt A y ≤ erGt A x := by
  unfold erGt
  exact Finset.card_le_card fun j hj => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    linarith

private lemma er_gt_le_eigCount {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : ℝ) :
    erGt A x ≤ eigCount A x := by
  unfold erGt eigCount
  exact Finset.card_le_card fun j hj => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact hj.le

private lemma er_eigCount_le_gt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {x y : ℝ} (hxy : x < y) :
    eigCount A y ≤ erGt A x := by
  unfold erGt eigCount
  exact Finset.card_le_card fun j hj => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    linarith

/-! ## Gaps from equal counts, and the scaling `Q̇ = (N/(N−1)) π̄ B π̄` -/

/-- Equal counts `n_A(α) = n_A(β)`, `α ≤ β`: no eigenvalue of `A` lies in `[α, β)`. -/
private lemma er_gap_of_eigCount {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {α β : ℝ}
    (h : eigCount A α = eigCount A β) : ∀ j, specOf A j < α ∨ β ≤ specOf A j := by
  intro j
  by_contra hc
  push Not at hc
  have hsub : (Finset.univ.filter fun i => β ≤ specOf A i) ⊆
      (Finset.univ.filter fun i => α ≤ specOf A i) := fun i hi => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    linarith
  have hj : j ∈ (Finset.univ.filter fun i => α ≤ specOf A i) := by simp [hc.1]
  have hj' : j ∉ (Finset.univ.filter fun i => β ≤ specOf A i) := by simp [hc.2]
  have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hsub, fun he => hj' (he ▸ hj)⟩)
  unfold eigCount at h
  omega

/-- Equal counts `#{λ ≤ α} = #{λ ≤ β}`, `α ≤ β`: no eigenvalue of `A` lies in `(α, β]`. -/
private lemma er_gap_of_erLe {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {α β : ℝ}
    (h : erLe A α = erLe A β) : ∀ j, specOf A j ≤ α ∨ β < specOf A j := by
  intro j
  by_contra hc
  push Not at hc
  have hsub : (Finset.univ.filter fun i => specOf A i ≤ α) ⊆
      (Finset.univ.filter fun i => specOf A i ≤ β) := fun i hi => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    linarith
  have hj : j ∈ (Finset.univ.filter fun i => specOf A i ≤ β) := by simp [hc.2]
  have hj' : j ∉ (Finset.univ.filter fun i => specOf A i ≤ α) := by simp [hc.1]
  have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hsub, fun he => hj' (he ▸ hj)⟩)
  unfold erLe at h
  omega

/-- `n_{Q̇}(y) = n_{π̄Bπ̄}(y (N−1)/N)` for the companion `Q̇ = (N/(N−1)) π̄ B π̄`, `N ≥ 2`. -/
private lemma er_eigCount_QdotN {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.IsHermitian)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (hN : 2 ≤ N) (y : ℝ) :
    eigCount (QdotN Sig Xm) y = eigCount (QN Sig (Xdot Xm)) (y - y / N) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hc : 0 < (N : ℝ) / (N - 1) := div_pos (by linarith) (by linarith)
  have hN1 : (N : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  have hN0 : (N : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have e : y = (N : ℝ) / (N - 1) * (y - y / N) := by field_simp
  unfold QdotN
  conv_lhs => rw [e]
  exact er_eigCount_smul (XSX_isHermitian hSig (Xdot Xm)) hc _

/-- `x_k < 0` for every `k < 2p` (the inner critical points are negative). -/
private lemma er_xCrit_neg_lt {σ : Fin M → ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hkp : k < 2 * numBands N σ) : xCrit N σ k < 0 := by
  have hne : k ≠ 2 * numBands N σ := by omega
  have hcard : 2 * numBands N σ ≤ Multiset.card (innerCrit N σ) + 1 := by
    unfold numBands; omega
  unfold xCrit
  rw [ite_eq_right_of_eq_false _ _ (eq_false hne)]
  have hlen : ((innerCrit N σ).sort (· ≤ ·)).reverse.length = Multiset.card (innerCrit N σ) := by
    rw [List.length_reverse, Multiset.length_sort]
  have hidx : k - 1 < ((innerCrit N σ).sort (· ≤ ·)).reverse.length := by
    rw [hlen]; omega
  rw [List.getD_eq_getElem _ _ hidx]
  have hmem := List.getElem_mem hidx
  rw [List.mem_reverse, Multiset.mem_sort] at hmem
  exact (Multiset.mem_filter.1 hmem).2.1

/-! ## The chart of the lowest edge: `a_{2p}` for `N` and `N − 1` -/

/-- `(N − 1) F_{N−1}(y) = N F_N(y) + y`. -/
private lemma er_FChart_pred (σ : Fin M → ℝ) (hN : 2 ≤ N) (y : ℝ) :
    ((N : ℝ) - 1) * FChart (N - 1) σ y = N * FChart N σ y + y := by
  have hN1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := er_cast_pred hN
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have hN10 : (N : ℝ) - 1 ≠ 0 := by linarith
  unfold FChart weight
  rw [hN1, mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
  have h : ∀ s ∈ posVals σ,
      ((N : ℝ) - 1) * (((Finset.univ.filter fun i => σ i = s).card : ℝ) / ((N : ℝ) - 1) * s * y /
        (y + s)) = (N : ℝ) * (((Finset.univ.filter fun i => σ i = s).card : ℝ) / N * s * y /
        (y + s)) := by
    intro s _
    field_simp
  rw [Finset.sum_congr rfl h]
  ring

/-- `F` lies below its tangent at `y₀` on the chart: `F(y) ≤ F(y₀) + F'(y₀) (y − y₀)`. -/
private lemma er_FChart_tangent (K : ℕ) (σ : Fin M → ℝ) {y y₀ : ℝ} (hy : InChart σ y)
    (hy₀ : InChart σ y₀) : FChart K σ y ≤ FChart K σ y₀ + FChart1 K σ y₀ * (y - y₀) := by
  unfold FChart FChart1
  have key : ∀ s ∈ posVals σ, weight K σ s * s * y / (y + s) ≤
      weight K σ s * s * y₀ / (y₀ + s) + weight K σ s * s ^ 2 / (y₀ + s) ^ 2 * (y - y₀) := by
    intro s hs
    have h1 := hy s hs
    have h2 := hy₀ s hs
    have hw : 0 ≤ weight K σ s := by unfold weight; positivity
    have e : weight K σ s * s * y₀ / (y₀ + s) + weight K σ s * s ^ 2 / (y₀ + s) ^ 2 * (y - y₀) -
        weight K σ s * s * y / (y + s) =
        weight K σ s * (s ^ 2 * (y - y₀) ^ 2 / ((y₀ + s) ^ 2 * (y + s))) := by
      field_simp
      ring
    have : 0 ≤ weight K σ s * (s ^ 2 * (y - y₀) ^ 2 / ((y₀ + s) ^ 2 * (y + s))) := by positivity
    linarith
  have hsum := Finset.sum_le_sum key
  rw [Finset.sum_add_distrib, ← Finset.sum_mul] at hsum
  nlinarith

/-- `y_{2p} ≤ 2/τ²` for `N − 1` samples (from `a_{2p} ≥ 0`, `σ ≤ τ⁻¹`, `M/(N−1) ≤ 2/τ`). -/
private lemma er_yEdge_le {τ : ℝ} {K : ℕ} {σ : Fin M → ℝ} (hda : DensityAssumptions (τ / 2) K σ)
    (hσ : ∀ i, σ i ≤ τ⁻¹) (hK : 0 < K) (hS : (posVals σ).Nonempty)
    (ha : 0 ≤ FChart K σ (yEdge K σ)) : yEdge K σ ≤ 2 * τ⁻¹ * τ⁻¹ := by
  have hτ : 0 < τ := by have := hda.pos; linarith
  have hchart := (yEdge_spec K σ hda.nonneg hK hS).1
  set y := yEdge K σ with hy
  rcases le_or_gt y 0 with h0 | h0
  · have : 0 ≤ 2 * τ⁻¹ * τ⁻¹ := by positivity
    linarith
  have hterm : ∀ s ∈ posVals σ, weight K σ s * s * y / (y + s) ≤ weight K σ s * τ⁻¹ := by
    intro s hs
    have hs0 : 0 < s := (Finset.mem_filter.1 hs).2
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 (Finset.mem_filter.1 hs).1
    have hsτ : s ≤ τ⁻¹ := hi ▸ hσ i
    have hw : 0 ≤ weight K σ s := by unfold weight; positivity
    have h1 : s * y / (y + s) ≤ s := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    calc weight K σ s * s * y / (y + s) = weight K σ s * (s * y / (y + s)) := by ring
      _ ≤ weight K σ s * s := mul_le_mul_of_nonneg_left h1 hw
      _ ≤ weight K σ s * τ⁻¹ := mul_le_mul_of_nonneg_left hsτ hw
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.sum_mul, sum_weight] at hsum
  have hR : massRatio K σ ≤ 2 * τ⁻¹ := by
    have := (massRatio_le_phiRatio K σ).trans hda.phi_upper
    rwa [show (τ / 2)⁻¹ = 2 * τ⁻¹ by field_simp] at this
  have hτi : 0 < τ⁻¹ := inv_pos.mpr hτ
  unfold FChart at ha
  nlinarith

/-- The lowest edges for `N` and `N − 1` are within `C/N`, `C = 4τ⁻¹(1 + 2τ⁻¹) + 4τ⁻²`. -/
private lemma er_bottom_close {τ : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ)
    (hN : 2 ≤ N) :
    |edgeVal (N - 1) σ (2 * numBands (N - 1) σ) - edgeVal N σ (2 * numBands N σ)| ≤
      (4 * τ⁻¹ * (1 + 2 * τ⁻¹) + 4 * τ⁻¹ * τ⁻¹) / N := by
  have hτ := hda.pos
  have hτi : 0 < τ⁻¹ := inv_pos.mpr hτ
  have hda' := er_da_pred hda hN
  obtain ⟨hN0, -, hS⟩ := er_facts hda
  have hN10 : 0 < N - 1 := by omega
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hσ := hda.nonneg
  obtain ⟨hc0, hF0⟩ := yEdge_spec N σ hσ hN0 hS
  obtain ⟨hc1, hF1⟩ := yEdge_spec (N - 1) σ hσ hN10 hS
  have ea : edgeVal N σ (2 * numBands N σ) = FChart N σ (yEdge N σ) := by
    unfold edgeVal; simp
  have eb : edgeVal (N - 1) σ (2 * numBands (N - 1) σ) = FChart (N - 1) σ (yEdge (N - 1) σ) := by
    unfold edgeVal; simp
  have hp0 := (card_innerCrit N σ hσ hN0 hS).2
  have hp1 := (card_innerCrit (N - 1) σ hσ hN10 hS).2
  have ha0 := er_edge_mem hda (k := 2 * numBands N σ) (by omega) le_rfl
  have ha1 := er_edge_mem hda' (k := 2 * numBands (N - 1) σ) (by omega) le_rfl
  rw [ea] at ha0
  rw [eb] at ha1
  rw [ea, eb]
  set a := FChart N σ (yEdge N σ)
  set b := FChart (N - 1) σ (yEdge (N - 1) σ)
  set y₀ := yEdge N σ
  set y₁ := yEdge (N - 1) σ
  -- tangent inequalities at the two critical points
  have t1 := er_FChart_tangent N σ hc1 hc0
  have t2 := er_FChart_tangent (N - 1) σ hc0 hc1
  rw [hF0, zero_mul, add_zero] at t1
  rw [hF1, zero_mul, add_zero] at t2
  have p1 := er_FChart_pred σ hN y₁
  have p0 := er_FChart_pred σ hN y₀
  have hy₁ := er_yEdge_le hda' (fun i => hda.bound_Sigma i) hN10 hS ha1.1
  have hy₀ : -τ⁻¹ < y₀ := by
    obtain ⟨s, hs⟩ := hS
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 (Finset.mem_filter.1 hs).1
    have := hc0 s hs
    have : s ≤ τ⁻¹ := hi ▸ hda.bound_Sigma i
    linarith
  have hb : b ≤ 2 * (τ / 2)⁻¹ * (1 + (τ / 2)⁻¹) := ha1.2
  rw [show (τ / 2)⁻¹ = 2 * τ⁻¹ by field_simp] at hb
  -- `N (b − a) ≤ b + y₁` and `(N − 1)(b − a) ≥ a + y₀`
  have hup : (N : ℝ) * (b - a) ≤ b + y₁ := by nlinarith
  have hlo : a + y₀ ≤ ((N : ℝ) - 1) * (b - a) := by nlinarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hfin : -(2 * τ⁻¹) ≤ (N : ℝ) * (b - a) := by
    rcases le_or_gt 0 (b - a) with h | h
    · have : 0 ≤ (N : ℝ) * (b - a) := by positivity
      linarith
    · have e2 : (N : ℝ) * (b - a) = ((N : ℝ) - 1) * (b - a) + (b - a) := by ring
      have hN1 : (1 : ℝ) ≤ N - 1 := by linarith
      have h1 : -τ⁻¹ ≤ ((N : ℝ) - 1) * (b - a) := by linarith [ha0.1]
      have h2 : ((N : ℝ) - 1) * (b - a) ≤ b - a := by nlinarith
      linarith
  have hK1 : 2 * τ⁻¹ ≤ 4 * τ⁻¹ * (1 + 2 * τ⁻¹) + 4 * τ⁻¹ * τ⁻¹ := by nlinarith
  have hK2 : b + y₁ ≤ 4 * τ⁻¹ * (1 + 2 * τ⁻¹) + 4 * τ⁻¹ * τ⁻¹ := by nlinarith
  rw [abs_le]
  constructor
  · rw [← neg_div, div_le_iff₀ hNpos]
    nlinarith
  · rw [le_div_iff₀ hNpos]
    nlinarith

/-- The partner of the lowest edge `2p` is the lowest edge `2ṗ` of `N − 1`. -/
private lemma er_partner_bottom {τ C₁ : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ)
    (hN : 2 ≤ N) {k' : ℕ} (hreg' : RegularEdge (τ / 2) (N - 1) σ k')
    (hk'a : |edgeVal (N - 1) σ k' - edgeVal N σ (2 * numBands N σ)| ≤ C₁ / N)
    (hsmall : C₁ / N + (4 * τ⁻¹ * (1 + 2 * τ⁻¹) + 4 * τ⁻¹ * τ⁻¹) / N < τ / 2) :
    k' = 2 * numBands (N - 1) σ := by
  by_contra hne
  have hb := er_bottom_close hda hN
  have hsep := hreg'.2.2.2.1 (2 * numBands (N - 1) σ)
    (by have := hreg'.1; have := hreg'.2.1; omega) le_rfl (Ne.symm hne)
  have htri := abs_sub_le (edgeVal (N - 1) σ k') (edgeVal N σ (2 * numBands N σ))
    (edgeVal (N - 1) σ (2 * numBands (N - 1) σ))
  rw [abs_sub_comm (edgeVal N σ (2 * numBands N σ))] at htri
  linarith

/-- The index alignment at the partner edge: `ḋ_{k̂'−1} = d_{k̂−1}` (odd `k`); `ḋ_{k̂'} = d_{k̂}`
(even `k`), except at the lowest edge with `M > N`, where `ḋ_{k̂'} = N − 1` and `d_{k̂} = N`. -/
private lemma er_align {τ C₁ : ℝ} {σ : Fin M → ℝ} (hda : DensityAssumptions τ N σ)
    (hσ : ∀ j, 0 < σ j) (hN : 2 ≤ N) {k k' : ℕ} (hk : RegularEdge τ N σ k)
    (hpar : k' % 2 = k % 2) (hk'a : |edgeVal (N - 1) σ k' - edgeVal N σ k| ≤ C₁ / N)
    (hreg' : RegularEdge (τ / 2) (N - 1) σ k') (hC : C₁ / N ≤ τ / 12)
    (hCb : C₁ / N + (4 * τ⁻¹ * (1 + 2 * τ⁻¹) + 4 * τ⁻¹ * τ⁻¹) / N < τ / 2)
    (hgapc : ∀ E, τ / 2 ≤ E → τ / 4 ≤ Metric.infDist E (varrho N σ).support →
      (∃ x ∈ (varrho N σ).support, x < E) → nClass (N - 1) σ E = nClass N σ E) :
    (k % 2 = 1 → cumCount (N - 1) σ ((k' + 1) / 2 - 1) = cumCount N σ ((k + 1) / 2 - 1)) ∧
    (k % 2 = 0 → (cumCount (N - 1) σ ((k' + 1) / 2) = cumCount N σ ((k + 1) / 2) ∧
        xCrit N σ k < 0) ∨
      (N < M ∧ cumCount (N - 1) σ ((k' + 1) / 2) + 1 = N ∧ cumCount N σ ((k + 1) / 2) = N)) := by
  have hτ := hda.pos
  have hda' := er_da_pred hda hN
  obtain ⟨hN0, hM0, hS⟩ := er_facts hda
  have hN10 : 0 < N - 1 := by omega
  have hσ' := hda.nonneg
  obtain ⟨hk1, hk2, hka, -, -⟩ := id hk
  obtain ⟨hk'1, hk'2, -, -, -⟩ := id hreg'
  have hak := abs_le.1 hk'a
  set a := edgeVal N σ k with ha
  have hne : (varrho N σ).support.Nonempty := by
    have hp := (card_innerCrit N σ hσ' hN0 hS).2
    have h1 := er_anti hda (i := 1) (j := k) le_rfl hk1 hk2
    have h3 := edgeVal_band_lt N σ hσ' hN0 hS (k := 1) le_rfl hp
    have h4 := (er_edge_mem hda (k := 2 * 1) (by norm_num) (by omega)).1
    exact ⟨edgeVal N σ 1, er_mem_supp hda (k := 1) le_rfl hp (by linarith) h3.le (by simp)⟩
  constructor
  · intro hodd
    obtain ⟨m, hm⟩ : ∃ m, k = 2 * m + 1 := ⟨k / 2, by omega⟩
    obtain ⟨m', hm'⟩ : ∃ m', k' = 2 * m' + 1 := ⟨k' / 2, by omega⟩
    have hmp : m + 1 ≤ numBands N σ := by omega
    have hm'p : m' + 1 ≤ numBands (N - 1) σ := by omega
    have e1 : 2 * (m + 1) - 1 = k := by omega
    have e1' : 2 * (m' + 1) - 1 = k' := by omega
    rw [show (k' + 1) / 2 - 1 = m' by omega, show (k + 1) / 2 - 1 = m by omega]
    set E := a + τ / 3 with hE
    -- `n_N(E) = d_m`
    have hn1 : nClass N σ E = cumCount N σ m := by
      have := er_n_gap_up hda (k := m + 1) (by omega) hmp (x := E) (by rw [e1]; linarith)
        (fun h2 => by
          have hs := er_sep_up hda (k := m + 1) h2 (by rw [e1]; exact hk)
          rw [e1] at hs
          linarith)
      simpa using this
    -- `n_{N−1}(E) = ḋ_{m'}`
    have hn2 : nClass (N - 1) σ E = cumCount (N - 1) σ m' := by
      have := er_n_gap_up hda' (k := m' + 1) (by omega) hm'p (x := E) (by rw [e1']; linarith)
        (fun h2 => by
          have hs := er_sep_up hda' (k := m' + 1) h2 (by rw [e1']; exact hreg')
          rw [e1'] at hs
          linarith)
      simpa using this
    have hdist : τ / 3 ≤ Metric.infDist E (varrho N σ).support := by
      refine er_dist hda (by linarith) (by linarith) hne fun l hl1 hl2 => ?_
      rcases le_or_gt l m with hle | hgt
      · left
        have hs := er_sep_up hda (k := m + 1) (by omega) (by rw [e1]; exact hk)
        rw [e1, show 2 * (m + 1) - 2 = 2 * m by omega] at hs
        have := er_anti hda (i := 2 * l) (j := 2 * m) (by omega) (by omega) (by omega)
        linarith
      · right
        have := er_anti hda (i := k) (j := 2 * l - 1) hk1 (by omega) (by omega)
        linarith
    have hmem : a ∈ (varrho N σ).support := by
      refine er_mem_supp hda (k := m + 1) (by omega) hmp (by linarith) ?_ (by rw [e1])
      have := er_anti hda (i := k) (j := 2 * (m + 1)) hk1 (by omega) (by omega)
      linarith
    have h := hgapc E (by linarith) (by linarith) ⟨a, hmem, by linarith⟩
    rw [hn1, hn2] at h
    exact_mod_cast h
  · intro heven
    obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m := ⟨k / 2, by omega⟩
    obtain ⟨m', rfl⟩ : ∃ m', k' = 2 * m' := ⟨k' / 2, by omega⟩
    have hm1 : 1 ≤ m := by omega
    have hmp : m ≤ numBands N σ := by omega
    have hm'1 : 1 ≤ m' := by omega
    have hm'p : m' ≤ numBands (N - 1) σ := by omega
    rw [show (2 * m' + 1) / 2 = m' by omega, show (2 * m + 1) / 2 = m by omega]
    rcases lt_or_eq_of_le hmp with hlt | heq
    · left
      set E := a - τ / 3 with hE
      have hsep := er_sep_dn hda hm1 hlt hk
      have hn1 : nClass N σ E = cumCount N σ m :=
        er_n_gap_dn hda hσ hm1 hmp (by linarith) (by linarith) fun _ => by linarith
      have hn2 : nClass (N - 1) σ E = cumCount (N - 1) σ m' := by
        refine er_n_gap_dn hda' hσ hm'1 hm'p (by linarith) (by linarith) fun h2 => ?_
        have hs := er_sep_dn hda' hm'1 h2 hreg'
        linarith
      have hdist : τ / 3 ≤ Metric.infDist E (varrho N σ).support := by
        refine er_dist hda (by linarith) (by linarith) hne fun l hl1 hl2 => ?_
        rcases le_or_gt l m with hle | hgt
        · left
          have := er_anti hda (i := 2 * l) (j := 2 * m) (by omega) (by omega) hk2
          linarith
        · right
          have := er_anti hda (i := 2 * m + 1) (j := 2 * l - 1) (by omega) (by omega) (by omega)
          linarith
      have hb := edgeVal_band_lt N σ hσ' hN0 hS (k := m + 1) (by omega) (by omega)
      have hb0 := (er_edge_mem hda (k := 2 * (m + 1)) (by omega) (by omega)).1
      rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega] at hb
      have hmem : edgeVal N σ (2 * m + 1) ∈ (varrho N σ).support :=
        er_mem_supp hda (k := m + 1) (by omega) (by omega) (by linarith) hb.le
          (by rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega])
      have h := hgapc E (by linarith) (by linarith) ⟨_, hmem, by linarith⟩
      rw [hn1, hn2] at h
      exact ⟨by exact_mod_cast h, er_xCrit_neg_lt (by omega) (by omega)⟩
    · -- the lowest edge
      have hk2p : 2 * m = 2 * numBands N σ := by omega
      have hpart := er_partner_bottom hda hN hreg' (by rw [← hk2p]; exact hk'a) hCb
      have hm'e : m' = numBands (N - 1) σ := by omega
      have hc1 := (er_cum hda' hσ (k := m') hm'1 hm'p).2
      rw [← hm'e] at hc1
      have hc0 := (er_cum hda hσ (k := m) hm1 hmp).2
      rw [← heq] at hc0
      rw [hc1, hc0]
      have hMN : M ≠ N := by
        intro hMN
        have hR : massRatio N σ = 1 := by
          rw [er_massRatio hσ, hMN, div_self (by exact_mod_cast hN0.ne')]
        have hy := (yEdge_eq_zero_iff N σ hσ' hN0 hS).2 hR
        have : edgeVal N σ (2 * m) = 0 := by
          rw [hk2p]; unfold edgeVal; simp [hy, FChart]
        linarith
      rcases lt_or_gt_of_ne hMN with hlt | hgt
      · left
        refine ⟨by rw [min_eq_left (by omega), min_eq_left (by omega)], ?_⟩
        refine er_xCrit_neg hda hm1 hmp (Or.inr ?_)
        rw [er_massRatio hσ, div_lt_one (by exact_mod_cast hN0)]
        exact_mod_cast hlt
      · right
        refine ⟨hgt, ?_, ?_⟩
        · rw [min_eq_right (by omega)]; omega
        · rw [min_eq_right (by omega)]

/-! ## The secular count near a regular edge -/

/-- The secular count at `E > 0`, `z = E + iη`, near a regular edge `a_k` with `x_k < 0`: if no
eigenvalue of `B` lies within `η` of `E`, `|z − a_k|` is small, `N η` is large and the anisotropic
law holds at `z` for `(0, 1_N)` at level `N^{1/12}`, then `π̄ B π̄` and `B` have the same number of
eigenvalues `≥ E`. -/
private lemma er_secular_at {τ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (hN : 0 < N) (hda : DensityAssumptions τ N (specOf Sig))
    (hτ1 : τ ≤ 1) {k : ℕ} (hk : RegularEdge τ N (specOf Sig) k)
    (hx : xCrit N (specOf Sig) k < 0) {E η : ℝ} (hE : 0 < E) (hη : 0 < η)
    (hgap : ∀ j, η ≤ |specOf (QN Sig Xm) j - E|)
    (hza : ‖(E : ℂ) + η * Complex.I - (edgeVal N (specOf Sig) k : ℂ)‖ ≤ edgeTau0 τ)
    (hq1 : 16 * (‖(E : ℂ) + η * Complex.I - (edgeVal N (specOf Sig) k : ℂ)‖ / edgec2 τ) ≤
      (edgecx τ / 3) ^ 2)
    (hNη : 1 ≤ (N : ℝ) * η)
    (hq2 : 16 * (N : ℝ) ^ (1 / 6 : ℝ) ≤ (edgecx τ / 3) ^ 2 * ((N : ℝ) * η))
    (hlaw : ‖testBilin (Sum.elim (0 : Fin M → ℝ) (fun _ : Fin N => (1 : ℝ)))
        (lawMat Sig Xm ((E : ℂ) + η * Complex.I)) (Sum.elim 0 fun _ => 1)‖ ≤
      (N : ℝ) ^ (1 / 12 : ℝ) * (Psi N (specOf Sig) ((E : ℂ) + η * Complex.I) *
        testNorm (Sum.elim (0 : Fin M → ℝ) (fun _ : Fin N => (1 : ℝ))) *
        testNorm (Sum.elim (0 : Fin M → ℝ) (fun _ : Fin N => (1 : ℝ))))) :
    eigCount (QN Sig (Xdot Xm)) E = eigCount (QN Sig Xm) E := by
  have hτ := hda.pos
  set z : ℂ := (E : ℂ) + η * Complex.I with hz
  have hzim : z.im = η := by simp [hz]
  obtain ⟨hs1, hs2⟩ := er_sign hda hτ1 hk hx (by rw [hzim]; exact hη) hza
  have hpsi := er_psi_le (N := N) (σ := specOf Sig) hs2 (by rw [hzim]; exact hNη)
  have hcx0 : 0 < edgecx τ := by unfold edgecx; have := Real.sqrt_pos.2 hτ; positivity
  have hc20 : 0 < edgec2 τ := (er_C_pos hτ).2
  have h1 : 4 * √(‖z - (edgeVal N (specOf Sig) k : ℂ)‖ / edgec2 τ) ≤ edgecx τ / 3 := by
    have : ‖z - (edgeVal N (specOf Sig) k : ℂ)‖ / edgec2 τ ≤ (edgecx τ / 12) ^ 2 := by
      nlinarith
    have := Real.sqrt_le_sqrt this
    rw [Real.sqrt_sq (by positivity)] at this
    linarith
  have h2 : 2 * ((N : ℝ) ^ (1 / 12 : ℝ) * (2 * √(1 / ((N : ℝ) * z.im)))) ≤ edgecx τ / 3 := by
    rw [hzim]
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hsq : (N : ℝ) ^ (1 / 6 : ℝ) = ((N : ℝ) ^ (1 / 12 : ℝ)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; norm_num
    set P := (N : ℝ) ^ (1 / 12 : ℝ) with hP
    have hP0 : 0 ≤ P := by positivity
    have hNd : 0 < (N : ℝ) * η := by positivity
    have hsq2 : (4 * P * √(1 / ((N : ℝ) * η))) ^ 2 = 16 * P ^ 2 / ((N : ℝ) * η) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
    have hle : (4 * P * √(1 / ((N : ℝ) * η))) ^ 2 ≤ (edgecx τ / 3) ^ 2 := by
      rw [hsq2, div_le_iff₀ hNd]
      rw [hsq] at hq2
      linarith
    have hX0 : 0 ≤ 4 * P * √(1 / ((N : ℝ) * η)) := by positivity
    have := (pow_le_pow_iff_left₀ hX0 (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).1 hle
    linarith
  refine er_secular hSig Xm hN hE hη hgap hlaw ?_
  have hP0 : 0 ≤ (N : ℝ) ^ (1 / 12 : ℝ) := by positivity
  have := mul_le_mul_of_nonneg_left hpsi hP0
  linarith

/-! ## The deterministic step: from the edge regime of `B` to the edge regime of `Q̇` -/

/-- `(t + u)^{3/2} ≤ 4 (t^{3/2} + u^{3/2})` for `t, u ≥ 0`. -/
private lemma er_rpow_add {t u : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u) :
    (t + u) ^ (3 / 2 : ℝ) ≤ 4 * (t ^ (3 / 2 : ℝ) + u ^ (3 / 2 : ℝ)) := by
  have h4 : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 4 := by
    have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
      (show (3 / 2 : ℝ) ≤ 2 by norm_num)
    rw [show (2 : ℝ) ^ (2 : ℝ) = 4 by norm_num] at this
    exact this
  have ht' : 0 ≤ t ^ (3 / 2 : ℝ) := by positivity
  have hu' : 0 ≤ u ^ (3 / 2 : ℝ) := by positivity
  rcases le_total t u with h | h
  · have h1 : (t + u) ^ (3 / 2 : ℝ) ≤ (2 * u) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    rw [Real.mul_rpow (by norm_num) hu] at h1
    nlinarith
  · have h1 : (t + u) ^ (3 / 2 : ℝ) ≤ (2 * t) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    rw [Real.mul_rpow (by norm_num) ht] at h1
    nlinarith

/-- `Q̇` is symmetric. -/
private lemma er_QdotN_herm {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.IsHermitian)
    (Xm : Matrix (Fin M) (Fin N) ℝ) : (QdotN Sig Xm).IsHermitian := by
  have hA : (QN Sig (Xdot Xm)).IsHermitian := XSX_isHermitian hSig (Xdot Xm)
  unfold QdotN Matrix.IsHermitian
  rw [conjTranspose_smul, hA.eq, star_trivial]

/-- The local count bound: `N^{δ_Q} + K N (t + u)^{3/2} + e` is at most `Ṅ^δ + C₀ Ṅ t^{3/2}`. -/
private lemma er_count_bound {N' t u Kc C₀ δQ δ e : ℝ} {N : ℝ} (ht : 0 ≤ t) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1) (hKc : 0 ≤ Kc) (hN : 0 ≤ N)
    (h4 : N ^ δQ + e + 4 * Kc * (N * u) ≤ N' ^ δ) (h5 : 4 * Kc * N ≤ C₀ * N') :
    N ^ δQ + Kc * N * (t + u) ^ (3 / 2 : ℝ) + e ≤ N' ^ δ + C₀ * N' * t ^ (3 / 2 : ℝ) := by
  have h1 := er_rpow_add ht hu0
  have h2 : u ^ (3 / 2 : ℝ) ≤ u := by
    have := Real.rpow_le_rpow_of_exponent_ge' hu0 hu1 (show (0 : ℝ) ≤ 1 by norm_num)
      (show (1 : ℝ) ≤ 3 / 2 by norm_num)
    rwa [Real.rpow_one] at this
  have ht' : 0 ≤ t ^ (3 / 2 : ℝ) := by positivity
  have hKN : 0 ≤ Kc * N := mul_nonneg hKc hN
  have h3 : Kc * N * (t + u) ^ (3 / 2 : ℝ) ≤ 4 * Kc * N * t ^ (3 / 2 : ℝ) + 4 * Kc * (N * u) := by
    have := mul_le_mul_of_nonneg_left h1 hKN
    have h' := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 4 * (Kc * N) by positivity)
    nlinarith
  have h6 : 4 * Kc * N * t ^ (3 / 2 : ℝ) ≤ C₀ * N' * t ^ (3 / 2 : ℝ) :=
    mul_le_mul_of_nonneg_right h5 ht'
  linarith

set_option maxHeartbeats 1000000 in
-- many linear-arithmetic steps over a large context
/-- The odd edge: from the edge regime of `B = Xᵀ Σ X` at `a` (exponent `δ_Q`, length `l + 1`)
and the secular count at `a + 3r/4`, the edge regime of `Q̇` at `ȧ` with `N − 1`. -/
private lemma er_det_odd {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.IsHermitian)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (hN : 2 ≤ N) {a b r Kc δ δQ C₀ u E₁ : ℝ} {d l : ℕ}
    (hB : EdgeRegime N a d (l + 1) δQ r Kc (QN Sig Xm))
    (hsec : eigCount (QN Sig Xm) (a + 3 * r / 4) ≤ eigCount (QN Sig (Xdot Xm)) (a + 3 * r / 4))
    (hlo : a - u ≤ b - E₁ / N) (hhi : b ≤ a + u) (hE₁ : b + 1 ≤ E₁) (hb : r / 2 < b)
    (hu0 : 0 ≤ u) (hur : u ≤ r / 4) (hu1 : u ≤ 1) (hKc : 0 ≤ Kc) (hr1 : r ≤ 1)
    (h1 : (N : ℝ) ^ (-2 / 3 + δQ) + u ≤ ((N - 1 : ℕ) : ℝ) ^ (-2 / 3 + δ))
    (h2 : ((N - 1 : ℕ) : ℝ) ^ (-2 / 3 + δ) ≤ r / 2)
    (h4 : (N : ℝ) ^ δQ + 0 + 4 * Kc * (N * u) ≤ ((N - 1 : ℕ) : ℝ) ^ δ)
    (h5 : 4 * Kc * N ≤ C₀ * ((N - 1 : ℕ) : ℝ)) :
    EdgeRegime (N - 1) b d l δ (r / 2) C₀ (QdotN Sig Xm) := by
  obtain ⟨hB1, hB2, hB3, hB4⟩ := hB
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  set t₀ := ((N - 1 : ℕ) : ℝ) ^ (-2 / 3 + δ) with ht₀
  set tQ := (N : ℝ) ^ (-2 / 3 + δQ) with htQ
  have htQ0 : 0 < tQ := by positivity
  have hE₁0 : 0 ≤ E₁ := by linarith
  set P := QN Sig (Xdot Xm)
  set B := QN Sig Xm
  have KD := er_eigCount_QdotN hSig Xm hN
  have hdiv : ∀ y : ℝ, 0 ≤ y → y ≤ E₁ → y - E₁ / N ≤ y - y / N ∧ y - y / N ≤ y ∧
      0 ≤ y - y / N := by
    intro y hy0 hyE
    have h1 : y / N ≤ E₁ / N := div_le_div_of_nonneg_right hyE hNpos.le
    have h2 : 0 ≤ y / N := by positivity
    have h3 : y / N ≤ y / 2 := div_le_div_of_nonneg_left hy0 (by norm_num) hNr
    exact ⟨by linarith, by linarith, by linarith⟩
  have hpos : ∀ y : ℝ, 0 < y → 0 < y - y / N := by
    intro y hy
    have h3 : y / N ≤ y / 2 := div_le_div_of_nonneg_left hy.le (by norm_num) hNr
    linarith
  have hA : ∀ x : ℝ, t₀ ≤ x → x ≤ r / 2 → eigCount (QdotN Sig Xm) (b + x) ≤ d := by
    intro x hx1 hx2
    rw [KD]
    obtain ⟨d1, -, -⟩ := hdiv (b + x) (by linarith) (by linarith)
    have hy := hpos (b + x) (by linarith)
    refine (eigCount_compress_le hSig Xm hy).trans ?_
    rw [← hB1]
    exact eigCount_antitone _ (by linarith)
  have hBl : d ≤ eigCount (QdotN Sig Xm) (b + r / 2) := by
    rw [KD]
    obtain ⟨-, d2, -⟩ := hdiv (b + r / 2) (by linarith) (by linarith)
    calc d = eigCount B (a + r) := hB2.symm
      _ ≤ eigCount B (a + 3 * r / 4) := eigCount_antitone _ (by linarith)
      _ ≤ eigCount P (a + 3 * r / 4) := hsec
      _ ≤ eigCount P (b + r / 2 - (b + r / 2) / N) := eigCount_antitone _ (by linarith)
  refine ⟨le_antisymm (hA t₀ le_rfl h2) (hBl.trans (eigCount_antitone _ (by linarith))),
    le_antisymm (hA (r / 2) h2 le_rfl) hBl, ?_, ?_⟩
  · rw [KD]
    obtain ⟨-, d2, -⟩ := hdiv (b - t₀) (by linarith) (by linarith)
    have h3 := eigCount_le_compress_add_one hSig Xm (a - tQ)
    have h4 : eigCount P (a - tQ) ≤ eigCount P (b - t₀ - (b - t₀) / N) :=
      eigCount_antitone _ (by linarith)
    show d + l ≤ eigCount P (b - t₀ - (b - t₀) / N)
    have h3' : eigCount B (a - tQ) ≤ eigCount P (a - tQ) + 1 := h3
    omega
  · intro t ht
    obtain ⟨ht0, ht1⟩ := ht
    rw [KD]
    obtain ⟨d1, -, -⟩ := hdiv (b - t) (by linarith) (by linarith)
    have hy := hpos (b - t) (by linarith)
    have h3 : eigCount P (b - t - (b - t) / N) ≤ eigCount B (a - (t + u)) :=
      (eigCount_compress_le hSig Xm hy).trans (eigCount_antitone _ (by linarith))
    have h6 := hB4 (t + u) ⟨by linarith, by linarith⟩
    have h7 := er_count_bound (N' := ((N - 1 : ℕ) : ℝ)) ht0 hu0 hu1 hKc hNpos.le h4 h5
    have h3' : (eigCount P (b - t - (b - t) / N) : ℝ) ≤ eigCount B (a - (t + u)) := by
      exact_mod_cast h3
    linarith

set_option maxHeartbeats 1000000 in
-- many linear-arithmetic steps over a large context
/-- The even edge: from the edge regime of `−B` at `−a` (exponent `δ_Q`, length `l + 1`, `d_k̂`
eigenvalues of `B` above the edge) and a count of `π̄ B π̄` at `a − y₂`, the edge regime of `−Q̇`
at `−ȧ` with `N − 1` and `ḋ` eigenvalues of `Q̇` above the edge. -/
private lemma er_det_even {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.IsHermitian)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (hN : 2 ≤ N) {a b r Kc δ δQ C₀ u E₁ y₂ : ℝ}
    {cum cd l : ℕ}
    (hB : EdgeRegime N (-a) (N - cum) (l + 1) δQ r Kc (-QN Sig Xm))
    (hsec : eigCount (QN Sig Xm) (a - y₂) ≤ eigCount (QN Sig (Xdot Xm)) (a - y₂) + (cum - cd))
    (hcd : cd ≤ cum) (hcum : cum ≤ cd + 1) (hcN : cum ≤ N)
    (hlast : cum = cd ∨ eigCount (QdotN Sig Xm) (b - r / 2) ≤ cd)
    (hlo : a - u ≤ b - E₁ / N) (hhi : b + 1 / N ≤ a + u) (hE₁ : b + 1 ≤ E₁) (hb : r / 2 < b)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hKc : 0 ≤ Kc) (hr1 : r ≤ 1)
    (h1 : (N : ℝ) ^ (-2 / 3 + δQ) + u < ((N - 1 : ℕ) : ℝ) ^ (-2 / 3 + δ))
    (h1' : y₂ + u ≤ ((N - 1 : ℕ) : ℝ) ^ (-2 / 3 + δ) / 2)
    (h3 : (N : ℝ) ^ (-2 / 3 + δQ) ≤ y₂)
    (h2 : ((N - 1 : ℕ) : ℝ) ^ (-2 / 3 + δ) ≤ r / 2)
    (h4 : (N : ℝ) ^ δQ + 1 + 4 * Kc * (N * u) ≤ ((N - 1 : ℕ) : ℝ) ^ δ)
    (h5 : 4 * Kc * N ≤ C₀ * ((N - 1 : ℕ) : ℝ)) :
    EdgeRegime (N - 1) (-b) (N - cd) l δ (r / 2) C₀ (-QdotN Sig Xm) := by
  obtain ⟨hB1, hB2, hB3, hB4⟩ := hB
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  set t₀ := ((N - 1 : ℕ) : ℝ) ^ (-2 / 3 + δ) with ht₀
  set tQ := (N : ℝ) ^ (-2 / 3 + δQ) with htQ
  have htQ0 : 0 < tQ := by positivity
  have hN1' : 0 ≤ 1 / (N : ℝ) := by positivity
  have ht₀0 : 0 < t₀ := by
    have : (0 : ℝ) < ((N - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < N - 1 by omega)
    positivity
  have hE₁0 : 0 ≤ E₁ := by linarith
  set P := QN Sig (Xdot Xm)
  set B := QN Sig Xm
  have hBH : B.IsHermitian := XSX_isHermitian hSig Xm
  have hQH := er_QdotN_herm hSig Xm
  have KD := er_eigCount_QdotN hSig Xm hN
  have hdiv : ∀ y : ℝ, 0 ≤ y → y ≤ E₁ → y - E₁ / N ≤ y - y / N ∧ y - y / N ≤ y ∧
      0 ≤ y - y / N := by
    intro y hy0 hyE
    have h1 : y / N ≤ E₁ / N := div_le_div_of_nonneg_right hyE hNpos.le
    have h2 : 0 ≤ y / N := by positivity
    have h3 : y / N ≤ y / 2 := div_le_div_of_nonneg_left hy0 (by norm_num) hNr
    exact ⟨by linarith, by linarith, by linarith⟩
  have hpos : ∀ y : ℝ, 0 < y → 0 < y - y / N := by
    intro y hy
    have h3 : y / N ≤ y / 2 := div_le_div_of_nonneg_left hy.le (by norm_num) hNr
    linarith
  -- the counts of `B` above `a ± t`
  have hLG : ∀ x, erLe B x + erGt B x = N := fun x => by simpa using er_le_add_gt B x
  have hLGQ : ∀ x, erLe (QdotN Sig Xm) x + erGt (QdotN Sig Xm) x = N := fun x => by
    simpa using er_le_add_gt (QdotN Sig Xm) x
  rw [er_eigCount_neg hBH] at hB1 hB2 hB3
  rw [show -(-a + tQ) = a - tQ by ring] at hB1
  rw [show -(-a + r) = a - r by ring] at hB2
  rw [show -(-a - tQ) = a + tQ by ring] at hB3
  have g1 : erGt B (a - tQ) = cum := by have := hLG (a - tQ); omega
  have g2 : erGt B (a - r) = cum := by have := hLG (a - r); omega
  have g3 : erGt B (a + tQ) + (l + 1) ≤ cum := by have := hLG (a + tQ); omega
  have g4 : ∀ t ∈ Set.Icc (0 : ℝ) r,
      (cum : ℝ) - erGt B (a + t) ≤ (N : ℝ) ^ δQ + Kc * N * t ^ (3 / 2 : ℝ) := by
    intro t ht
    have h := hB4 t ht
    rw [er_eigCount_neg hBH, show -(-a - t) = a + t by ring] at h
    have hl := hLG (a + t)
    have e : ((erLe B (a + t) : ℕ) : ℝ) - ((N - cum : ℕ) : ℝ) = (cum : ℝ) - erGt B (a + t) := by
      have : (erLe B (a + t) : ℝ) + erGt B (a + t) = N := by exact_mod_cast hl
      rw [Nat.cast_sub hcN]
      linarith
    linarith
  -- the counts of `Q̇` above `ȧ − x`
  have hge : cd ≤ erGt (QdotN Sig Xm) (b - t₀) := by
    refine le_trans ?_ (er_eigCount_le_gt _ (show b - t₀ < b - t₀ / 2 by linarith))
    rw [KD]
    obtain ⟨-, d2, -⟩ := hdiv (b - t₀ / 2) (by linarith) (by linarith)
    have e1 : eigCount P (a - y₂) ≤ eigCount P (b - t₀ / 2 - (b - t₀ / 2) / N) :=
      eigCount_antitone _ (by linarith)
    have e2 : erGt B (a - tQ) ≤ erGt B (a - y₂) := er_gt_anti _ (by linarith)
    have e3 := er_gt_le_eigCount B (a - y₂)
    show cd ≤ eigCount P (b - t₀ / 2 - (b - t₀ / 2) / N)
    have hsec' : eigCount B (a - y₂) ≤ eigCount P (a - y₂) + (cum - cd) := hsec
    omega
  have hle : erGt (QdotN Sig Xm) (b - r / 2) ≤ cd := by
    refine (er_gt_le_eigCount _ _).trans ?_
    rcases hlast with hc | hc
    · rw [KD]
      obtain ⟨d1, -, -⟩ := hdiv (b - r / 2) (by linarith) (by linarith)
      have hy := hpos (b - r / 2) (by linarith)
      refine (eigCount_compress_le hSig Xm hy).trans ?_
      refine (er_eigCount_le_gt B (show a - r < b - r / 2 - (b - r / 2) / N by linarith)).trans ?_
      rw [g2, hc]
    · exact hc
  have hGt : ∀ x, t₀ ≤ x → x ≤ r / 2 → erGt (QdotN Sig Xm) (b - x) = cd := by
    intro x hx1 hx2
    refine le_antisymm ((er_gt_anti _ (by linarith)).trans hle)
      (hge.trans (er_gt_anti _ (by linarith)))
  have hcdN : cd ≤ N := hcd.trans hcN
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [er_eigCount_neg hQH, show -(-b + t₀) = b - t₀ by ring]
    have := hLGQ (b - t₀)
    have := hGt t₀ le_rfl h2
    omega
  · rw [er_eigCount_neg hQH, show -(-b + r / 2) = b - r / 2 by ring]
    have := hLGQ (b - r / 2)
    have := hGt (r / 2) h2 le_rfl
    omega
  · rw [er_eigCount_neg hQH, show -(-b - t₀) = b + t₀ by ring]
    have hL := hLGQ (b + t₀)
    have e0 := er_gt_le_eigCount (QdotN Sig Xm) (b + t₀)
    rw [KD] at e0
    obtain ⟨d1, -, -⟩ := hdiv (b + t₀) (by linarith) (by linarith)
    have hy := hpos (b + t₀) (by linarith)
    have e1 := eigCount_compress_le hSig Xm hy
    have e2 := er_eigCount_le_gt B (show a + tQ < b + t₀ - (b + t₀) / N by linarith)
    have e1' : eigCount P (b + t₀ - (b + t₀) / N) ≤ eigCount B (b + t₀ - (b + t₀) / N) := e1
    have e0' : erGt (QdotN Sig Xm) (b + t₀) ≤ eigCount P (b + t₀ - (b + t₀) / N) := e0
    omega
  · intro t ht
    obtain ⟨ht0, ht1⟩ := ht
    rw [er_eigCount_neg hQH, show -(-b - t) = b + t by ring]
    have hL := hLGQ (b + t)
    have hN1 : (1 : ℝ) / N > 0 := by positivity
    have e0 := er_eigCount_le_gt (QdotN Sig Xm) (show b + t < b + t + 1 / N by linarith)
    rw [KD] at e0
    obtain ⟨-, d2, -⟩ := hdiv (b + t + 1 / N) (by linarith) (by
      have : 1 / (N : ℝ) ≤ 1 / 2 := by rw [div_le_div_iff₀ hNpos (by norm_num)]; linarith
      linarith)
    have e1 := eigCount_le_compress_add_one hSig Xm (b + t + 1 / N - (b + t + 1 / N) / N)
    have e2 := er_gt_le_eigCount B (b + t + 1 / N - (b + t + 1 / N) / N)
    have e3 : erGt B (a + (t + u)) ≤ erGt B (b + t + 1 / N - (b + t + 1 / N) / N) :=
      er_gt_anti _ (by linarith)
    have e1' : eigCount B (b + t + 1 / N - (b + t + 1 / N) / N) ≤
        eigCount P (b + t + 1 / N - (b + t + 1 / N) / N) + 1 := e1
    have hgtB : erGt B (a + (t + u)) ≤ cum := by
      have := er_gt_anti B (show a - tQ ≤ a + (t + u) by linarith)
      omega
    have e0' : eigCount P (b + t + 1 / N - (b + t + 1 / N) / N) ≤ erGt (QdotN Sig Xm) (b + t) :=
      e0
    have hk : cd ≤ erGt (QdotN Sig Xm) (b + t) + (cum - erGt B (a + (t + u))) + 1 := by omega
    have h6 := g4 (t + u) ⟨by linarith, by linarith⟩
    have h7 := er_count_bound (N' := ((N - 1 : ℕ) : ℝ)) ht0 hu0 hu1 hKc hNpos.le h4 h5
    have hk' : (cd : ℝ) ≤ erGt (QdotN Sig Xm) (b + t) + ((cum : ℝ) - erGt B (a + (t + u))) + 1 := by
      have : ((cum - erGt B (a + (t + u)) : ℕ) : ℝ) = (cum : ℝ) - erGt B (a + (t + u)) :=
        Nat.cast_sub hgtB
      rw [← this]; exact_mod_cast hk
    have e : ((erLe (QdotN Sig Xm) (b + t) : ℕ) : ℝ) - ((N - cd : ℕ) : ℝ) =
        (cd : ℝ) - erGt (QdotN Sig Xm) (b + t) := by
      have : (erLe (QdotN Sig Xm) (b + t) : ℝ) + erGt (QdotN Sig Xm) (b + t) = N := by
        exact_mod_cast hL
      rw [Nat.cast_sub hcdN]
      linarith
    rw [e]
    linarith

/-! ## The exponent rows -/

/-- `N^e ≤ (N − 1)^e ≤ 2 N^e` for `e ∈ [−1, 0]`, and `N^δ/2 ≤ (N − 1)^δ` for `δ ∈ [0, 1]`,
`N ≥ 2`. -/
private lemma er_pred_rpow (hN : 2 ≤ N) {e δ : ℝ} (he : -1 ≤ e) (he0 : e ≤ 0) (hδ : 0 ≤ δ)
    (hδ1 : δ ≤ 1) :
    (N : ℝ) ^ e ≤ ((N - 1 : ℕ) : ℝ) ^ e ∧ ((N - 1 : ℕ) : ℝ) ^ e ≤ 2 * (N : ℝ) ^ e ∧
      (N : ℝ) ^ δ / 2 ≤ ((N - 1 : ℕ) : ℝ) ^ δ := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hc : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := er_cast_pred hN
  have h1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have h2 : (N : ℝ) / 2 ≤ (N : ℝ) - 1 := by linarith
  have h22 : (0 : ℝ) < (N : ℝ) / 2 := by linarith
  rw [hc]
  refine ⟨Real.rpow_le_rpow_of_nonpos h1 (by linarith) he0, ?_, ?_⟩
  · have := Real.rpow_le_rpow_of_nonpos h22 h2 he0
    rw [Real.div_rpow (by linarith) (by norm_num)] at this
    have h2e : (2 : ℝ) ^ (-1 : ℝ) ≤ (2 : ℝ) ^ e :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) he
    rw [Real.rpow_neg_one] at h2e
    have hpos : 0 < (2 : ℝ) ^ e := by positivity
    have hNe : 0 ≤ (N : ℝ) ^ e := by positivity
    have : (N : ℝ) ^ e / (2 : ℝ) ^ e ≤ 2 * (N : ℝ) ^ e := by
      rw [div_le_iff₀ hpos]; nlinarith
    linarith
  · have := Real.rpow_le_rpow h22.le h2 hδ
    rw [Real.div_rpow (by linarith) (by norm_num)] at this
    have h2δ : (2 : ℝ) ^ δ ≤ (2 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hδ1
    rw [Real.rpow_one] at h2δ
    have hpos : 0 < (2 : ℝ) ^ δ := by positivity
    have hNe : 0 ≤ (N : ℝ) ^ δ := by positivity
    have : (N : ℝ) ^ δ / 2 ≤ (N : ℝ) ^ δ / (2 : ℝ) ^ δ :=
      div_le_div_of_nonneg_left hNe hpos h2δ
    linarith

/-- `N · N^e = N^{1+e}`. -/
private lemma er_mul_rpow {N : ℕ} (hN : 0 < N) (e : ℝ) :
    (N : ℝ) * (N : ℝ) ^ e = (N : ℝ) ^ (1 + e) := by
  rw [Real.rpow_add (by exact_mod_cast hN), Real.rpow_one]

/-- `C / N = C N^{-1}`. -/
private lemma er_div_eq (C : ℝ) (N : ℕ) : C / N = C * (N : ℝ) ^ (-1 : ℝ) := by
  rw [Real.rpow_neg_one, div_eq_mul_inv]

set_option maxHeartbeats 1000000 in
-- many linear-arithmetic steps over a large context
/-- The exponent rows of the edge regime of `Q̇`, for `N` large (`δ_Q = δ/4`, `y₂ = N^{−2/3+δ/2}`,
`t₀ = (N−1)^{−2/3+δ}`, `u = C_u/N`, `η₁ = r/8`, `η₂ = y₂/2`). -/
private lemma er_numeric {δ r Cu K cx c2 τ₂ τ0 : ℝ} (hδ : 0 < δ) (hδ1 : δ < 2 / 3) (hr : 0 < r)
    (hcx : 0 < cx) (hc2 : 0 < c2) (hτ₂ : 0 < τ₂)
    (hτ₂4 : τ₂ ≤ 1 / 4) (hτ0 : 0 < τ0) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      4 ≤ N ∧
      (N : ℝ) ^ (-2 / 3 + δ / 4) + Cu / N < ((N - 1 : ℕ) : ℝ) ^ (-2 / 3 + δ) ∧
      (N : ℝ) ^ (-2 / 3 + δ / 2) + Cu / N ≤ ((N - 1 : ℕ) : ℝ) ^ (-2 / 3 + δ) / 2 ∧
      2 * (N : ℝ) ^ (-2 / 3 + δ / 4) ≤ (N : ℝ) ^ (-2 / 3 + δ / 2) ∧
      ((N - 1 : ℕ) : ℝ) ^ (-2 / 3 + δ) ≤ r / 8 ∧
      Cu / N ≤ r / 16 ∧
      16 * (N : ℝ) ^ (1 / 6 : ℝ) ≤ (cx / 3) ^ 2 * ((N : ℝ) * (r / 8)) ∧
      1 ≤ (N : ℝ) * (r / 8) ∧
      16 * (N : ℝ) ^ (1 / 6 : ℝ) ≤
        (cx / 3) ^ 2 * ((N : ℝ) * ((N : ℝ) ^ (-2 / 3 + δ / 2) / 2)) ∧
      1 ≤ (N : ℝ) * ((N : ℝ) ^ (-2 / 3 + δ / 2) / 2) ∧
      (N : ℝ) ^ (-1 + τ₂) ≤ r / 8 ∧
      (N : ℝ) ^ (-1 + τ₂) ≤ (N : ℝ) ^ (-2 / 3 + δ / 2) / 2 ∧
      16 * (3 / 2 * (N : ℝ) ^ (-2 / 3 + δ / 2) / c2) ≤ (cx / 3) ^ 2 ∧
      3 / 2 * (N : ℝ) ^ (-2 / 3 + δ / 2) ≤ τ0 ∧
      (N : ℝ) ^ (δ / 4) + 1 + K ≤ ((N - 1 : ℕ) : ℝ) ^ δ := by
  obtain ⟨N₁, f1⟩ := er_ev 4 (show -2 / 3 + δ / 4 < -2 / 3 + δ by linarith)
  obtain ⟨N₂, f2⟩ := er_ev (4 * Cu) (show (-1 : ℝ) < -2 / 3 + δ by linarith)
  obtain ⟨N₃, f3⟩ := er_ev 4 (show -2 / 3 + δ / 2 < -2 / 3 + δ by linarith)
  obtain ⟨N₄, f4⟩ := er_ev 2 (show -2 / 3 + δ / 4 < -2 / 3 + δ / 2 by linarith)
  obtain ⟨N₅, f5⟩ := er_ev_small (show 0 < r / 16 by positivity)
    (show -2 / 3 + δ < 0 by linarith)
  obtain ⟨N₆, f6⟩ := er_ev (16 * Cu / r) (show (-1 : ℝ) < 0 by norm_num)
  obtain ⟨N₇, f7⟩ := er_ev (1152 / (cx ^ 2 * r)) (show (1 / 6 : ℝ) < 1 by norm_num)
  obtain ⟨N₈, f8⟩ := er_ev (8 / r) (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨N₉, f9⟩ := er_ev (288 / cx ^ 2) (show (1 / 6 : ℝ) < 1 + (-2 / 3 + δ / 2) by linarith)
  obtain ⟨N₁₀, f10⟩ := er_ev 2 (show (0 : ℝ) < 1 + (-2 / 3 + δ / 2) by linarith)
  obtain ⟨N₁₁, f11⟩ := er_ev_small (show 0 < r / 8 by positivity)
    (show -1 + τ₂ < 0 by linarith)
  obtain ⟨N₁₂, f12⟩ := er_ev 2 (show -1 + τ₂ < -2 / 3 + δ / 2 by linarith)
  obtain ⟨N₁₃, f13⟩ := er_ev_small (show 0 < min (cx ^ 2 * c2 / 216) (2 / 3 * τ0) by
    positivity) (show -2 / 3 + δ / 2 < 0 by linarith)
  obtain ⟨N₁₄, f14⟩ := er_ev 4 (show δ / 4 < δ by linarith)
  obtain ⟨N₁₅, f15⟩ := er_ev (4 * (1 + K)) (show (0 : ℝ) < δ by linarith)
  refine ⟨N₁ + N₂ + N₃ + N₄ + N₅ + N₆ + N₇ + N₈ + N₉ + N₁₀ + N₁₁ + N₁₂ + N₁₃ + N₁₄ + N₁₅ + 4,
    fun N hN => ?_⟩
  have g1 := f1 N (by omega)
  have g2 := f2 N (by omega)
  have g3 := f3 N (by omega)
  have g4 := f4 N (by omega)
  have g5 := f5 N (by omega)
  have g6 := f6 N (by omega)
  have g7 := f7 N (by omega)
  have g8 := f8 N (by omega)
  have g9 := f9 N (by omega)
  have g10 := f10 N (by omega)
  have g11 := f11 N (by omega)
  have g12 := f12 N (by omega)
  have g13 := f13 N (by omega)
  have g14 := f14 N (by omega)
  have g15 := f15 N (by omega)
  have hN4 : 4 ≤ N := by omega
  have hN0 : 0 < N := by omega
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN4
  have hNpos : (0 : ℝ) < N := by linarith
  obtain ⟨p1, p2, -⟩ := er_pred_rpow (N := N) (by omega) (e := -2 / 3 + δ) (δ := δ) (by linarith)
    (by linarith) hδ.le (by linarith)
  obtain ⟨-, -, p3⟩ := er_pred_rpow (N := N) (by omega) (e := -2 / 3 + δ) (δ := δ) (by linarith)
    (by linarith) hδ.le (by linarith)
  have hNe0 : 0 < (N : ℝ) ^ (-2 / 3 + δ) := by positivity
  have hu : Cu / N = Cu * (N : ℝ) ^ (-1 : ℝ) := er_div_eq Cu N
  rw [Real.rpow_zero] at g6 g8 g10 g15
  rw [← er_mul_rpow hN0] at g9 g10
  rw [Real.rpow_one] at g7 g8
  have hm1 : (N : ℝ) ^ (-1 : ℝ) = (N : ℝ)⁻¹ := Real.rpow_neg_one _
  have hy0 : 0 < (N : ℝ) ^ (-2 / 3 + δ / 2) := by positivity
  have hmin1 := min_le_left (cx ^ 2 * c2 / 216) (2 / 3 * τ0)
  have hmin2 := min_le_right (cx ^ 2 * c2 / 216) (2 / 3 * τ0)
  refine ⟨hN4, ?_, ?_, g4, ?_, ?_, ?_, ?_, ?_, ?_, g11, by linarith, ?_, by linarith, ?_⟩
  · rw [hu]; linarith
  · rw [hu]; linarith
  · linarith
  · rw [hu]
    have : 16 * Cu / r * (N : ℝ) ^ (-1 : ℝ) = 16 / r * (Cu * (N : ℝ) ^ (-1 : ℝ)) := by ring
    rw [this] at g6
    have hr16 : 0 < 16 / r := by positivity
    have := (le_div_iff₀' hr16).2 g6
    rw [show (1 : ℝ) / (16 / r) = r / 16 by field_simp] at this
    exact this
  · have e : (cx / 3) ^ 2 * ((N : ℝ) * (r / 8)) = cx ^ 2 * r / 72 * N := by ring
    rw [e]
    have h0 : 0 < cx ^ 2 * r / 72 := by positivity
    have e2 : 1152 / (cx ^ 2 * r) = 16 / (cx ^ 2 * r / 72) := by field_simp; norm_num
    rw [e2] at g7
    have := mul_le_mul_of_nonneg_left g7 h0.le
    rw [← mul_assoc, mul_div_cancel₀ _ h0.ne'] at this
    linarith
  · have e : (8 / r) * 1 = 8 / r := by ring
    rw [e, div_le_iff₀ hr] at g8
    linarith
  · have e : (cx / 3) ^ 2 * ((N : ℝ) * ((N : ℝ) ^ (-2 / 3 + δ / 2) / 2)) =
        cx ^ 2 / 18 * ((N : ℝ) * (N : ℝ) ^ (-2 / 3 + δ / 2)) := by ring
    rw [e]
    have h0 : 0 < cx ^ 2 / 18 := by positivity
    have e2 : 288 / cx ^ 2 = 16 / (cx ^ 2 / 18) := by field_simp; norm_num
    rw [e2] at g9
    have := mul_le_mul_of_nonneg_left g9 h0.le
    rw [← mul_assoc, mul_div_cancel₀ _ h0.ne'] at this
    linarith
  · linarith
  · have : 16 * (3 / 2 * (N : ℝ) ^ (-2 / 3 + δ / 2) / c2) =
        24 / c2 * (N : ℝ) ^ (-2 / 3 + δ / 2) := by ring
    rw [this]
    have h1 : 24 / c2 * (N : ℝ) ^ (-2 / 3 + δ / 2) ≤ 24 / c2 * (cx ^ 2 * c2 / 216) :=
      mul_le_mul_of_nonneg_left (g13.trans hmin1) (by positivity)
    have h2 : 24 / c2 * (cx ^ 2 * c2 / 216) = (cx / 3) ^ 2 := by field_simp; ring
    linarith
  · have : 0 ≤ (N : ℝ) ^ (δ / 4) := by positivity
    linarith

/-! ## Events -/

/-- A point `E + iη` with `τ₂ ≤ E ≤ τ₂⁻¹`, `N^{−1+τ₂} ≤ η ≤ τ₂⁻¹` and `|E − a_k| ≤ τ'` lies in
`𝐃^e_k(τ₂, τ', N)`. -/
private lemma er_mem_edgeDomain {τ₂ τ' E η : ℝ} {σ : Fin M → ℝ} {k : ℕ} (hη : 0 < η)
    (hτ₂E : τ₂ ≤ E) (hEτ₂ : E ≤ τ₂⁻¹) (hηlo : (N : ℝ) ^ (-1 + τ₂) ≤ η) (hηhi : η ≤ τ₂⁻¹)
    (hEa : |E - edgeVal N σ k| ≤ τ') :
    (E : ℂ) + η * Complex.I ∈ edgeDomain τ₂ τ' N σ k := by
  set z : ℂ := (E : ℂ) + η * Complex.I with hz
  have hzre : z.re = E := by simp [hz]
  have hzim : z.im = η := by simp [hz]
  have hE0 : 0 ≤ E := by
    have : 0 ≤ (N : ℝ) ^ (-1 + τ₂) := by positivity
    have : 0 < τ₂⁻¹ := lt_of_lt_of_le hη hηhi
    have : 0 < τ₂ := inv_pos.mp this
    linarith
  refine ⟨⟨by rw [hzim]; exact hη, ?_, ?_, by rw [hzim]; exact hηlo, by rw [hzim]; exact hηhi⟩, ?_⟩
  · have := Complex.abs_re_le_norm z
    rw [hzre, abs_of_nonneg hE0] at this
    linarith
  · rw [hzre, abs_of_nonneg hE0]; exact hEτ₂
  · rw [hzre]
    obtain ⟨h1, h2⟩ := abs_le.1 hEa
    constructor <;> linarith

/-- The anisotropic law at one `z ∈ S` for the test vector `(0, 1_N)`, as an event. -/
private lemma er_law_event {Ω : Type*} [MeasureSpace Ω] {ε D : ℝ}
    {Sig : Matrix (Fin M) (Fin M) ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ} {S : Set ℂ} {z : ℂ}
    (hlaw : AnisotropicLawAt N ε D Sig X S) (hz : z ∈ S) :
    HighProbAt N D {ω | ‖testBilin (Sum.elim (0 : Fin M → ℝ) (fun _ : Fin N => (1 : ℝ)))
        (lawMat Sig (X ω) z) (Sum.elim 0 fun _ => 1)‖ ≤
      (N : ℝ) ^ ε * (Psi N (specOf Sig) z *
        testNorm (Sum.elim (0 : Fin M → ℝ) (fun _ : Fin N => (1 : ℝ))) *
        testNorm (Sum.elim (0 : Fin M → ℝ) (fun _ : Fin N => (1 : ℝ))))} := by
  set v := Sum.elim (0 : Fin M → ℝ) (fun _ : Fin N => (1 : ℝ)) with hv
  have h := hlaw z hz v v
  unfold DomAt at h
  unfold HighProbAt
  have hset : {ω | ‖testBilin v (lawMat Sig (X ω) z) v‖ ≤
      (N : ℝ) ^ ε * (Psi N (specOf Sig) z * testNorm v * testNorm v)}ᶜ =
      {ω | (N : ℝ) ^ ε * (Psi N (specOf Sig) z * testNorm v * testNorm v) <
        ‖testBilin v (lawMat Sig (X ω) z) v‖} := by
    ext ω
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
  rw [hset]
  exact h

/-- An event of probability `≥ 1 − N^{−2}` has probability `≥ 1 − (N − 1)^{−1}`, `N ≥ 2`. -/
private lemma er_hp_final {Ω : Type*} [MeasureSpace Ω] {A B : Set Ω} (hN : 2 ≤ N)
    (h : HighProbAt N 2 A) (hAB : A ⊆ B) : HighProbAt (N - 1) 1 B := by
  unfold HighProbAt at *
  refine (measure_mono (Set.compl_subset_compl.2 hAB)).trans (h.trans (ENNReal.ofReal_le_ofReal ?_))
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  rw [er_cast_pred hN, Real.rpow_neg (by linarith), Real.rpow_neg (by linarith), Real.rpow_one,
    show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact inv_anti₀ (by linarith) (by nlinarith)

/-- `n_{Q̇}(y) ≤ N − 1` for `y > 0` (`λ̇_N = 0`). -/
private lemma er_eigCount_QdotN_lt {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosSemidef)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (hN : 1 ≤ N) {y : ℝ} (hy : 0 < y) :
    eigCount (QdotN Sig Xm) y ≤ N - 1 := by
  have h0 := sortedEig_QdotN_last hSig Xm hN
  have hH := er_QdotN_herm hSig.1 Xm
  by_contra hc
  have : N ≤ eigCount (QdotN Sig Xm) y := by omega
  have := (sortedEig_ge_iff hH hN le_rfl y).2 this
  linarith

/-! ## The edge regime for `Q̇` -/

set_option maxHeartbeats 8000000 in
-- many linear-arithmetic steps over a large context
/-- The edge-regime input of the reduction for `Q̇` at the partner edge `k' = edgePartner N σ k`, with `N − 1` samples: with
probability `≥ 1 − (N−1)^{−1}`, `(−1)^{k'+1}` times the `N × N` companion of `Q̇` has exactly
`edgeDn N (N − 1) σ k'` eigenvalues above `±ȧ_{k'} + (N−1)^{−2/3+δ}` and above `±ȧ_{k'} + r₀`, at
least `l` more above `±ȧ_{k'} − (N−1)^{−2/3+δ}`, and the local count bound with constant `C₀`;
`r₀` and `C₀ ≥ 2` depend on `τ` only. -/
theorem edgeRegime_dot (τ : ℝ) (hτ : 0 < τ) :
    ∃ r₀ C₀ : ℝ, 0 < r₀ ∧ 2 ≤ C₀ ∧ ∀ (C : ℕ → ℝ) (l : ℕ) (δ : ℝ), 0 < δ → δ < 2 / 3 →
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (k : ℕ),
        IsModel τ C M N Sig X → RegularEdge τ N (specOf Sig) k →
        HighProbAt (N - 1) 1 {ω | EdgeRegime (N - 1)
          (edgeSign (edgePartner N (specOf Sig) k) *
            edgeVal (N - 1) (specOf Sig) (edgePartner N (specOf Sig) k))
          (edgeDn N (N - 1) (specOf Sig) (edgePartner N (specOf Sig) k)) l δ r₀ C₀
          (edgeSign (edgePartner N (specOf Sig) k) • QdotN Sig (X ω))} := by
  have hτ'0 : 0 < edgeTau' τ := edgeTau'_pos hτ
  have hr0 : 0 < edgeR0 τ := lt_min (by positivity) (by positivity)
  have hKc : 0 < edgeKc τ := by
    have := (er_C_pos hτ).2
    unfold edgeKc; positivity
  refine ⟨edgeR0 τ / 2, max 2 (8 * edgeKc τ), by positivity, le_max_left _ _, ?_⟩
  intro C l δ hδ hδ1
  by_cases hτ1 : τ ≤ 1
  swap
  · exact ⟨0, fun N _ Ω _ _ M Sig X k hm _ => absurd hm.tau_le_one hτ1⟩
  set r := edgeR0 τ with hr
  set Kc := edgeKc τ with hKcdef
  have hrτ : r ≤ τ / 2 := min_le_right _ _
  have hrτ' : r ≤ edgeTau' τ / 2 := min_le_left _ _
  obtain ⟨-, ht0e, ht'τ⟩ := er_tau_facts hτ hτ1
  have hτi : 0 < τ⁻¹ := inv_pos.mpr hτ
  -- the domain parameter
  set τ₂ := min (1 / 4) (2 * τ⁻¹ * (1 + τ⁻¹) + 1)⁻¹ with hτ₂
  have hτ₂0 : 0 < τ₂ := lt_min (by norm_num) (by positivity)
  have hτ₂4 : τ₂ ≤ 1 / 4 := min_le_left _ _
  have hτ₂C : τ₂ ≤ (2 * τ⁻¹ * (1 + τ⁻¹) + 1)⁻¹ := min_le_right _ _
  have hτ₂inv : 2 * τ⁻¹ * (1 + τ⁻¹) + 1 ≤ τ₂⁻¹ := by
    rw [le_inv_comm₀ (by positivity) hτ₂0]; exact hτ₂C
  have hτ₂τ : τ₂ ≤ τ / 2 := by
    have h1 : τ / 2 ≥ (2 * τ⁻¹ * (1 + τ⁻¹) + 1)⁻¹ := by
      rw [ge_iff_le, inv_le_comm₀ (by positivity) (by positivity)]
      have : (τ / 2)⁻¹ = 2 * τ⁻¹ := by field_simp
      rw [this]
      have : 0 ≤ 2 * τ⁻¹ * τ⁻¹ := by positivity
      nlinarith
    linarith
  have hτ₂4' : (4 : ℝ) ≤ τ₂⁻¹ := by rw [le_inv_comm₀ (by norm_num) hτ₂0]; linarith
  -- the window constants
  have hcx0 : 0 < edgecx τ := by unfold edgecx; have := Real.sqrt_pos.2 hτ; positivity
  have hc20 : 0 < edgec2 τ := (er_C_pos hτ).2
  have hτ0 : 0 < edgeTau0 τ := by linarith
  have hρ1 : edgeRho1 τ ≤ edgecx τ / 2 := by
    have h10 : edgeRho1 τ ≤ edgeRho0 τ := min_le_left _ _
    have : edgeRho0 τ ≤ edgecx τ / 2 := by
      unfold edgeRho0; linarith [min_le_left (edgecx τ) τ]
    linarith
  have hρ10 : 0 < edgeRho1 τ := by
    unfold edgeRho1 edgeRho0
    have := (er_C_pos hτ).2
    have h3 : 0 < edgeC3 τ := by unfold edgeC3; positivity
    positivity
  have hτ'e : edgeTau' τ = edgec2 τ * edgeRho1 τ ^ 2 / 32 := by
    unfold edgeTau' edgeTau0; ring
  have hodd_q1 : 16 * (7 / 8 * r / edgec2 τ) ≤ (edgecx τ / 3) ^ 2 := by
    have h1 : r ≤ edgec2 τ * edgeRho1 τ ^ 2 / 64 := by rw [hτ'e] at hrτ'; linarith
    have h2 : edgeRho1 τ ^ 2 ≤ (edgecx τ / 2) ^ 2 := pow_le_pow_left₀ hρ10.le hρ1 2
    have : 16 * (7 / 8 * r / edgec2 τ) = 14 * r / edgec2 τ := by ring
    rw [this, div_le_iff₀ hc20]
    have h3 := mul_le_mul_of_nonneg_left h2 hc20.le
    nlinarith
  -- the inputs
  obtain ⟨C₁, Np, hpart⟩ := edgePartner_spec τ hτ
  obtain ⟨NQ, hQ⟩ := edgeRegime_Q τ C (l + 1) (δ / 4) (2 + 1) hτ (by positivity) (by linarith)
  obtain ⟨NL, hL⟩ := edge_law' τ τ₂ (edgeTau' τ) C (1 / 12) (2 + 1) hτ₂0
    (by linarith) hτ'0 le_rfl (by norm_num)
  obtain ⟨Ng, hgap⟩ := nClass_pred_gap τ hτ
  set E' := 4 * τ⁻¹ * (1 + 2 * τ⁻¹) with hE'
  set Cb := 4 * τ⁻¹ * (1 + 2 * τ⁻¹) + 4 * τ⁻¹ * τ⁻¹ with hCb
  set Cu := |C₁| + (E' + 1) + 1 + Cb with hCu
  have hE'0 : 0 ≤ E' := by positivity
  have hCb0 : 0 ≤ Cb := by positivity
  obtain ⟨Nn, hnum⟩ := er_numeric (δ := δ) (r := r) (Cu := Cu) (K := 4 * Kc * Cu)
    (cx := edgecx τ) (c2 := edgec2 τ) (τ₂ := τ₂) (τ0 := edgeTau0 τ) hδ hδ1 hr0 hcx0 hc20 hτ₂0
    hτ₂4 hτ0
  refine ⟨Np + NQ + NL + Ng + Nn, fun N hN Ω _ _ M Sig X k hm hk => ?_⟩
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14⟩ := hnum N (by omega)
  have hN2 : 2 ≤ N := by omega
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast n0
  have hNpos : (0 : ℝ) < N := by linarith
  have hN0 : 0 < N := by omega
  have hda : DensityAssumptions τ N (specOf Sig) := hm.diagModel_specOf.densityAssumptions hτ
  have hσ := er_sigma_pos hm
  have hSigPD := hm.sigma.posDef
  have hSig := hSigPD.isHermitian
  have hda' := er_da_pred hda hN2
  set σ := specOf Sig with hσdef
  obtain ⟨hk'par, hk'a, hk'reg⟩ := hpart N (by omega) M σ hda k hk
  set k' := edgePartner N σ k with hk'
  have hgapc : ∀ E, τ / 2 ≤ E → τ / 4 ≤ Metric.infDist E (varrho N σ).support →
      (∃ x ∈ (varrho N σ).support, x < E) → nClass (N - 1) σ E = nClass N σ E :=
    fun E h1 h2 h3 => hgap N (by omega) M σ hda E h1 h2 h3
  -- the shift `u = C_u / N`
  set u := Cu / N with hu
  have hC1N : |C₁| / N ≤ u := div_le_div_of_nonneg_right (by linarith [abs_nonneg C₁]) hNpos.le
  have hC1N' : C₁ / N ≤ |C₁| / N := div_le_div_of_nonneg_right (le_abs_self _) hNpos.le
  have hu0 : 0 ≤ u := by positivity
  have hsplit : |C₁| / N + (E' + 1) / N + 1 / N + Cb / N = u := by rw [hu, hCu]; ring
  have hE1N : 0 ≤ (E' + 1) / N := by positivity
  have hCbN : 0 ≤ Cb / N := by positivity
  have h1N : 0 ≤ 1 / (N : ℝ) := by positivity
  have hal := er_align hda hσ hN2 hk hk'par hk'a hk'reg (by linarith) (by linarith) hgapc
  -- the edges
  obtain ⟨hk1, hk2, hka, -, -⟩ := id hk
  obtain ⟨hk'1, hk'2, -, -, -⟩ := id hk'reg
  set a := edgeVal N σ k with ha
  set b := edgeVal (N - 1) σ k' with hb
  have haC := (er_edge_mem hda hk1 hk2).2
  have hbE : b ≤ E' := by
    have := (er_edge_mem hda' hk'1 hk'2).2
    rwa [show (τ / 2)⁻¹ = 2 * τ⁻¹ by field_simp, show 2 * (2 * τ⁻¹) * (1 + 2 * τ⁻¹) = E' by
      rw [hE']; ring] at this
  have hba := abs_le.1 hk'a
  have hlo : a - u ≤ b - (E' + 1) / N := by linarith
  have hhi : b + 1 / N ≤ a + u := by linarith
  have hu16 : u ≤ r / 16 := n5
  have hbr : r / 2 < b := by linarith
  have hu1 : u ≤ 1 := by linarith
  have hr1 : r ≤ 1 := by linarith
  have hNu : (N : ℝ) * u = Cu := by rw [hu]; field_simp
  have h5 : 4 * Kc * N ≤ max 2 (8 * Kc) * ((N - 1 : ℕ) : ℝ) := by
    rw [er_cast_pred hN2]
    have : 8 * Kc ≤ max 2 (8 * Kc) := le_max_right _ _
    have h' : 4 * Kc * N ≤ 8 * Kc * ((N : ℝ) - 1) := by nlinarith
    exact h'.trans (mul_le_mul_of_nonneg_right this (by linarith))
  -- the events
  have hQev := hQ N (by omega) M Sig X k hm hk
  have hlaw := (hL N (by omega) M Sig X k hm hk).1
  have hcases : k % 2 = 1 ∨ k % 2 = 0 := by omega
  rcases hcases with hodd | heven
  · -- the odd edge: the secular count at `a + 3r/4`
    have hs : edgeSign k = 1 := by simp [edgeSign, hodd]
    have hs' : edgeSign k' = 1 := by simp [edgeSign, hk'par, hodd]
    have hd : edgeDn N (N - 1) σ k' = edgeD N σ k := by
      simp only [edgeDn, edgeD, hk'par, hodd, ite_true]
      exact hal.1 hodd
    set E₁ := a + 3 * r / 4 with hE₁
    have hzdom : (E₁ : ℂ) + (r / 8 : ℝ) * Complex.I ∈ edgeDomain τ₂ (edgeTau' τ) N σ k := by
      refine er_mem_edgeDomain (by positivity) (by linarith) (by linarith) n10 (by linarith) ?_
      rw [hE₁, show a + 3 * r / 4 - edgeVal N σ k = 3 * r / 4 by rw [← ha]; ring,
        abs_of_pos (by positivity)]
      linarith
    have hLev := er_law_event hlaw hzdom
    refine er_hp_final hN2 (er_hp_inter hN2 hQev hLev) ?_
    rintro ω ⟨hω1, hω2⟩
    simp only [Set.mem_ofPred_eq] at hω1 hω2 ⊢
    rw [hs, one_mul, one_smul] at hω1
    rw [hs', one_mul, one_smul, hd]
    have hgapB := er_gap_of_eigCount _ (hω1.1.trans hω1.2.1.symm)
    have hsec : eigCount (QN Sig (X ω)) E₁ ≤ eigCount (QN Sig (Xdot (X ω))) E₁ := by
      refine le_of_eq (er_secular_at hSigPD (X ω) hN0 hda hτ1 hk
        (er_xCrit_neg_lt (σ := σ) hk1 (show k < 2 * numBands N σ by omega)) (by linarith)
        (by positivity) (fun j => ?_) ?_ ?_ n7 n6 hω2).symm
      · rcases hgapB j with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_nonneg (by linarith)]; linarith
      · refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
        simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.sub_im, Complex.add_im,
          Complex.mul_im]
        rw [hE₁, ← ha]
        ring_nf
        rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
        linarith
      · have hza : ‖(E₁ : ℂ) + (r / 8 : ℝ) * Complex.I - (edgeVal N σ k : ℂ)‖ ≤ 7 / 8 * r := by
          refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
          simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
            Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.sub_im, Complex.add_im,
            Complex.mul_im]
          rw [hE₁, ← ha]
          ring_nf
          rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
          linarith
        have : ‖(E₁ : ℂ) + (r / 8 : ℝ) * Complex.I - (edgeVal N σ k : ℂ)‖ / edgec2 τ ≤
            7 / 8 * r / edgec2 τ := div_le_div_of_nonneg_right hza hc20.le
        linarith
    have hB : EdgeRegime N a (edgeD N σ k) (l + 1) (δ / 4) r Kc (QN Sig (X ω)) := hω1
    exact er_det_odd hSig (X ω) hN2 hB hsec hlo (by linarith) (by linarith) hbr hu0 (by linarith)
      hu1 hKc.le hr1 n1.le (by linarith) (by rw [hNu]; linarith) h5
  · -- the even edge: the secular count at `a − y₂`, or the zero eigenvalue at the lowest edge
    have hs : edgeSign k = -1 := by simp [edgeSign, heven]
    have hs' : edgeSign k' = -1 := by simp [edgeSign, hk'par, heven]
    set cum := cumCount N σ ((k + 1) / 2) with hcum
    set cd := cumCount (N - 1) σ ((k' + 1) / 2) with hcd
    have hd : edgeDn N (N - 1) σ k' = N - cd := by
      simp only [edgeDn, hk'par, heven]; rfl
    have hdQ : edgeD N σ k = N - cum := by
      simp only [edgeD, heven]; rfl
    have hcumN : cum ≤ N := by
      have := (er_cum hda hσ (k := (k + 1) / 2) (by omega) (by omega)).1
      exact this.trans (min_le_right _ _)
    set y₂ := (N : ℝ) ^ (-2 / 3 + δ / 2) with hy₂
    have hy₂0 : 0 < y₂ := by positivity
    have htQ0 : 0 < (N : ℝ) ^ (-2 / 3 + δ / 4) := by positivity
    have ht₀0 : 0 < ((N - 1 : ℕ) : ℝ) ^ (-2 / 3 + δ) := by
      have : (0 : ℝ) < ((N - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < N - 1 by omega)
      positivity
    set E₂ := a - y₂ with hE₂
    have hzdom : (E₂ : ℂ) + (y₂ / 2 : ℝ) * Complex.I ∈ edgeDomain τ₂ (edgeTau' τ) N σ k := by
      refine er_mem_edgeDomain (by positivity) (by linarith) (by linarith) n11 (by linarith) ?_
      rw [hE₂, show a - y₂ - edgeVal N σ k = -y₂ by rw [← ha]; ring, abs_neg,
        abs_of_pos hy₂0]
      linarith
    have hLev := er_law_event hlaw hzdom
    refine er_hp_final hN2 (er_hp_inter hN2 hQev hLev) ?_
    rintro ω ⟨hω1, hω2⟩
    simp only [Set.mem_ofPred_eq] at hω1 hω2 ⊢
    rw [hs, neg_one_mul, neg_one_smul, hdQ] at hω1
    rw [hs', neg_one_mul, neg_one_smul, hd]
    have hB : EdgeRegime N (-a) (N - cum) (l + 1) (δ / 4) r Kc (-QN Sig (X ω)) := hω1
    have hBH : (QN Sig (X ω)).IsHermitian := XSX_isHermitian hSig (X ω)
    rcases hal.2 heven with ⟨hcc, hxk⟩ | ⟨hMN, hcc, hcN⟩
    · -- `ḋ = d`: the secular count
      have h1' := hB.1
      have h2' := hB.2.1
      rw [er_eigCount_neg hBH, show -(-a + (N : ℝ) ^ (-2 / 3 + δ / 4)) =
        a - (N : ℝ) ^ (-2 / 3 + δ / 4) by ring] at h1'
      rw [er_eigCount_neg hBH, show -(-a + r) = a - r by ring] at h2'
      have hgapB := er_gap_of_erLe _ (h2'.trans h1'.symm)
      have hsec : eigCount (QN Sig (X ω)) E₂ ≤
          eigCount (QN Sig (Xdot (X ω))) E₂ + (cum - cd) := by
        rw [hcc, Nat.sub_self, add_zero]
        refine le_of_eq (er_secular_at hSigPD (X ω) hN0 hda hτ1 hk hxk (by linarith)
          (by positivity) (fun j => ?_) ?_ ?_ n9 n8 hω2).symm
        · rcases hgapB j with h | h
          · rw [abs_of_nonpos (by linarith)]; linarith
          · rw [abs_of_pos (by linarith)]; linarith
        · refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
          simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
            Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.sub_im, Complex.add_im,
            Complex.mul_im]
          rw [hE₂, ← ha]
          ring_nf
          rw [abs_neg, abs_of_pos (by positivity), abs_of_pos (by positivity)]
          linarith
        · have hza : ‖(E₂ : ℂ) + (y₂ / 2 : ℝ) * Complex.I - (edgeVal N σ k : ℂ)‖ ≤
              3 / 2 * y₂ := by
            refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
            simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
              Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.sub_im, Complex.add_im,
              Complex.mul_im]
            rw [hE₂, ← ha]
            ring_nf
            rw [abs_neg, abs_of_pos (by positivity), abs_of_pos (by positivity)]
            linarith
          have : ‖(E₂ : ℂ) + (y₂ / 2 : ℝ) * Complex.I - (edgeVal N σ k : ℂ)‖ / edgec2 τ ≤
              3 / 2 * y₂ / edgec2 τ := div_le_div_of_nonneg_right hza hc20.le
          linarith
      exact er_det_even hSig (X ω) hN2 hB hsec hcc.le (by omega) hcumN (Or.inl hcc.symm) hlo hhi
        (by linarith) hbr hu0 hu1 hKc.le hr1 n1 n2 (by linarith) (by linarith)
        (by rw [hNu]; linarith) h5
    · -- the lowest edge with `M > N`: interlacing and `λ̇_N = 0`
      have hsec : eigCount (QN Sig (X ω)) E₂ ≤
          eigCount (QN Sig (Xdot (X ω))) E₂ + (cum - cd) := by
        rw [show cum - cd = 1 by omega]
        exact eigCount_le_compress_add_one hSig (X ω) E₂
      have hlast : eigCount (QdotN Sig (X ω)) (b - r / 2) ≤ cd := by
        have := er_eigCount_QdotN_lt hSigPD.posSemidef (X ω) (by omega)
          (show 0 < b - r / 2 by linarith)
        omega
      exact er_det_even hSig (X ω) hN2 hB hsec (by omega) (by omega) hcumN (Or.inr hlast) hlo
        hhi (by linarith) hbr hu0 hu1 hKc.le hr1 n1 n2 (by linarith) (by linarith)
        (by rw [hNu]; linarith) h5

/-! ## Instances -/

/-- `edgeRegime_dot` at `Σ = I_{2n}`, `N = n`, Gaussian `X`, `τ = 1/20`, `l = 1`,
`δ = 1/100`, at the lowest edge `k = 2` (rank `Σ = 2n > N`, one eigenvalue of `Q̇` below the
edge): every hypothesis is discharged. -/
example : ∃ r₀ C₀ : ℝ, 0 < r₀ ∧ 2 ≤ C₀ ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
    HighProbAt (n - 1) 1 {ω | EdgeRegime (n - 1)
      (edgeSign (edgePartner n (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) 2) *
        edgeVal (n - 1) (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ))
          (edgePartner n (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) 2))
      (edgeDn n (n - 1) (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ))
        (edgePartner n (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) 2)) 1 (1 / 100) r₀ C₀
      (edgeSign (edgePartner n (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) 2) •
        QdotN 1 (gaussX (2 * n) n ω))} := by
  obtain ⟨r₀, C₀, hr₀, hC₀, h⟩ := edgeRegime_dot (1 / 10 / 2) (by norm_num)
  obtain ⟨N₀, hN₀⟩ := h gaussMoment 1 (1 / 100) (by norm_num) (by norm_num)
  refine ⟨r₀, C₀, hr₀, hC₀, max N₀ 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_of_max_le_right hn
  have hm := (isModel_two hn1).mono (τ₂ := 1 / 10 / 2) (by norm_num) (by norm_num)
  refine hN₀ n (le_of_max_le_left hn) (2 * n) 1 (gaussX (2 * n) n) 2 hm ?_
  rw [specOf_one_eq]
  exact regularEdge_two (by omega) (by norm_num) le_rfl

/-- The same instance at the upper edge `k = 1`. -/
example : ∃ r₀ C₀ : ℝ, 0 < r₀ ∧ 2 ≤ C₀ ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
    HighProbAt (n - 1) 1 {ω | EdgeRegime (n - 1)
      (edgeSign (edgePartner n (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) 1) *
        edgeVal (n - 1) (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ))
          (edgePartner n (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) 1))
      (edgeDn n (n - 1) (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ))
        (edgePartner n (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) 1)) 1 (1 / 100) r₀ C₀
      (edgeSign (edgePartner n (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) 1) •
        QdotN 1 (gaussX (2 * n) n ω))} := by
  obtain ⟨r₀, C₀, hr₀, hC₀, h⟩ := edgeRegime_dot (1 / 10 / 2) (by norm_num)
  obtain ⟨N₀, hN₀⟩ := h gaussMoment 1 (1 / 100) (by norm_num) (by norm_num)
  refine ⟨r₀, C₀, hr₀, hC₀, max N₀ 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_of_max_le_right hn
  have hm := (isModel_two hn1).mono (τ₂ := 1 / 10 / 2) (by norm_num) (by norm_num)
  refine hN₀ n (le_of_max_le_left hn) (2 * n) 1 (gaussX (2 * n) n) 1 hm ?_
  rw [specOf_one_eq]
  exact regularEdge_two (by omega) le_rfl (by norm_num)

#print axioms edgeRegime_dot

end Anisotropic
