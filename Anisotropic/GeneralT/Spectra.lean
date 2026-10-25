import Anisotropic.Density.Basic
import Anisotropic.Density.Count
import Anisotropic.Density.Critical
import Anisotropic.Density.SelfConsistent
import Anisotropic.Density.Varrho
import Anisotropic.Entrywise.Defs
import Anisotropic.Entrywise.DiagModel
import Anisotropic.Framework.Model
import Anisotropic.GeneralT.Model
import Anisotropic.Rigidity.Defs

/-!
# Zero atoms, the spectra of `T Tᵀ` and `Tᵀ T`, and `Ŝ + κ P₀`

For a real `M × K` matrix `T`, the nonzero eigenvalues of `T Tᵀ` and `Tᵀ T` agree with
multiplicities, and every datum of Section 2 (`m`, `Ψ`, `ϱ`, the critical points and values, the
regularity conditions, the counts `d_k`, the classical locations) depends on the eigenvalues
only through their nonzero values. The matrix `Ŝ + κ P₀` of Section 11.1 is defined by spectral
calculus; it is positive definite, its `f` is that of `T Tᵀ` plus an atom `κ`, and it satisfies
Assumption 2.1 under (T_diag) at `τ³` when `(T, X)` satisfies Assumption 2.1 for a general `T`
at `τ`.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # Zero atoms, the spectra of `T Tᵀ` and `Tᵀ T`, and the regularized matrix `Ŝ + κ P₀` -/

/-- `σ` and `σ'` have the same nonzero values with the same multiplicities. -/
def NzEq {K : ℕ} (σ : Fin M → ℝ) (σ' : Fin K → ℝ) : Prop :=
  ∀ s : ℝ, s ≠ 0 → (Finset.univ.filter fun i => σ i = s).card =
    (Finset.univ.filter fun j => σ' j = s).card

/-- For a real symmetric matrix, the multiplicity of a value as an eigenvalue is its root
multiplicity in the characteristic polynomial. -/
private theorem nzEq_card_eigen {K : ℕ} {A : Matrix (Fin K) (Fin K) ℝ} (hA : A.IsHermitian)
    (s : ℝ) :
    (Finset.univ.filter fun i => specOf A i = s).card = A.charpoly.roots.count s := by
  rw [hA.roots_charpoly_eq_eigenvalues, specOf_eq hA]
  simp only [Function.comp_def, RCLike.ofReal_real_eq_id, id]
  rw [Multiset.count_map]
  rw [Finset.card_def, Finset.filter_val]
  congr 1
  exact Multiset.filter_congr fun a _ => eq_comm

theorem nzEq_specOf_mul_transpose {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ) :
    NzEq (specOf (T * Tᵀ)) (specOf (Tᵀ * T)) := by
  intro s hs
  have h1 : (T * Tᵀ).IsHermitian := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.posSemidef_self_mul_conjTranspose T).isHermitian
  have h2 : (Tᵀ * T).IsHermitian := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.posSemidef_conjTranspose_mul_self T).isHermitian
  rw [nzEq_card_eigen h1, nzEq_card_eigen h2]
  have h := Matrix.charpoly_mul_comm' T Tᵀ
  have hc := congrArg (fun p => p.roots.count s) h
  rw [Polynomial.roots_mul, Polynomial.roots_mul, Multiset.count_add, Multiset.count_add] at hc
  · simpa [Polynomial.roots_X_pow, Multiset.count_nsmul, Multiset.count_singleton, hs] using hc
  · exact mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (Matrix.charpoly_monic _).ne_zero
  · exact mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (Matrix.charpoly_monic _).ne_zero

/-- Sums of a function vanishing at `0` agree. -/
private theorem nzEq_sum_eq {K : ℕ} {σ : Fin M → ℝ} {σ' : Fin K → ℝ} (h : NzEq σ σ')
    {E : Type*} [AddCommMonoid E] (g : ℝ → E) (hg : g 0 = 0) :
    ∑ i, g (σ i) = ∑ j, g (σ' j) := by
  set S : Finset ℝ := Finset.univ.image σ ∪ Finset.univ.image σ' with hS
  have key : ∀ {L : ℕ} (τ : Fin L → ℝ), Finset.univ.image τ ⊆ S →
      ∑ i, g (τ i) = ∑ s ∈ S, (Finset.univ.filter fun i => τ i = s).card • g s := by
    intro L τ hτ
    rw [Finset.sum_comp, Finset.sum_subset hτ]
    intro s _ hs
    have : (Finset.univ.filter fun i => τ i = s) = ∅ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro rfl
      exact hs (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    simp [this]
  rw [key σ Finset.subset_union_left, key σ' Finset.subset_union_right]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : s = 0
  · simp [hs, hg]
  · rw [h s hs]

private theorem nzEq_fC_eq {K : ℕ} {σ : Fin M → ℝ} {σ' : Fin K → ℝ} (h : NzEq σ σ') (N : ℕ) :
    fC N σ = fC N σ' := by
  funext w
  unfold fC
  congr 1
  exact nzEq_sum_eq h (fun s : ℝ => (s : ℂ) / (N * (1 + s * w))) (by simp)

private theorem nzEq_fR_eq {K : ℕ} {σ : Fin M → ℝ} {σ' : Fin K → ℝ} (h : NzEq σ σ') (N : ℕ) :
    fR N σ = fR N σ' := by
  funext w
  unfold fR
  congr 1
  exact nzEq_sum_eq h (fun s : ℝ => s / (N * (1 + s * w))) (by simp)

theorem NzEq.mFun_eq {K : ℕ} {σ : Fin M → ℝ} {σ' : Fin K → ℝ} (h : NzEq σ σ') (N : ℕ) :
    mFun N σ = mFun N σ' := by
  funext z
  unfold mFun
  rw [nzEq_fC_eq h N]

private theorem nzEq_posVals_eq {K : ℕ} {σ : Fin M → ℝ} {σ' : Fin K → ℝ} (h : NzEq σ σ') :
    posVals σ = posVals σ' := by
  ext s
  simp only [posVals, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  refine and_congr_left fun hs => ?_
  have h1 := h s hs.ne'
  have e1 : (∃ i, σ i = s) ↔ 0 < (Finset.univ.filter fun i => σ i = s).card := by
    rw [Finset.card_pos, Finset.filter_nonempty_iff]; simp
  have e2 : (∃ i, σ' i = s) ↔ 0 < (Finset.univ.filter fun i => σ' i = s).card := by
    rw [Finset.card_pos, Finset.filter_nonempty_iff]; simp
  rw [e1, e2, h1]

private theorem nzEq_weight_eq {K : ℕ} {σ : Fin M → ℝ} {σ' : Fin K → ℝ} (h : NzEq σ σ')
    (N : ℕ) {s : ℝ} (hs : s ≠ 0) : weight N σ s = weight N σ' s := by
  unfold weight
  rw [h s hs]

private theorem nzEq_massRatio_eq {K : ℕ} {σ : Fin M → ℝ} {σ' : Fin K → ℝ} (h : NzEq σ σ')
    (N : ℕ) : massRatio N σ = massRatio N σ' := by
  rw [← sum_weight, ← sum_weight, nzEq_posVals_eq h]
  refine Finset.sum_congr rfl fun s hs => nzEq_weight_eq h N ?_
  exact (Finset.mem_filter.mp hs).2.ne'

private theorem nzEq_mExt_eq {K : ℕ} {σ : Fin M → ℝ} {σ' : Fin K → ℝ} (h : NzEq σ σ')
    (N : ℕ) : mExt N σ = mExt N σ' := by
  funext z
  unfold mExt
  rw [h.mFun_eq N]

private theorem nzEq_rhoDens_eq {K : ℕ} {σ : Fin M → ℝ} {σ' : Fin K → ℝ} (h : NzEq σ σ')
    (N : ℕ) : rhoDens N σ = rhoDens N σ' := by
  funext x
  unfold rhoDens
  rw [nzEq_mExt_eq h N]

theorem NzEq.varrho_eq {K : ℕ} {σ : Fin M → ℝ} {σ' : Fin K → ℝ} (h : NzEq σ σ') (N : ℕ) :
    varrho N σ = varrho N σ' := by
  unfold varrho
  rw [nzEq_massRatio_eq h N, nzEq_rhoDens_eq h N]

private theorem nzEq_critPoly_eq {K : ℕ} {σ : Fin M → ℝ} {σ' : Fin K → ℝ} (h : NzEq σ σ')
    (N : ℕ) : critPoly N σ = critPoly N σ' := by
  unfold critPoly
  rw [← nzEq_posVals_eq h]
  refine congrArg _ (congrArg _ (Finset.sum_congr rfl fun s hs => ?_))
  rw [nzEq_weight_eq h N (Finset.mem_filter.mp hs).2.ne']

private theorem nzEq_innerCrit_eq {K : ℕ} {σ : Fin M → ℝ} {σ' : Fin K → ℝ} (h : NzEq σ σ')
    (N : ℕ) : innerCrit N σ = innerCrit N σ' := by
  have hI : InInner σ = InInner σ' := funext fun x => by simp only [InInner, nzEq_posVals_eq h]
  unfold innerCrit
  rw [nzEq_critPoly_eq h N, hI]

theorem NzEq.numBands_eq {K : ℕ} {σ : Fin M → ℝ} {σ' : Fin K → ℝ} (h : NzEq σ σ') (N : ℕ) :
    numBands N σ = numBands N σ' := by
  unfold numBands
  rw [nzEq_innerCrit_eq h N]

private theorem nzEq_FChart_eq {K : ℕ} {σ : Fin M → ℝ} {σ' : Fin K → ℝ} (h : NzEq σ σ')
    (N : ℕ) : FChart N σ = FChart N σ' := by
  funext y
  unfold FChart
  rw [← nzEq_posVals_eq h]
  refine congrArg _ (Finset.sum_congr rfl fun s hs => ?_)
  rw [nzEq_weight_eq h N (Finset.mem_filter.mp hs).2.ne']

private theorem nzEq_FChart1_eq {K : ℕ} {σ : Fin M → ℝ} {σ' : Fin K → ℝ} (h : NzEq σ σ')
    (N : ℕ) : FChart1 N σ = FChart1 N σ' := by
  funext y
  unfold FChart1
  rw [← nzEq_posVals_eq h]
  refine congrArg _ (Finset.sum_congr rfl fun s hs => ?_)
  rw [nzEq_weight_eq h N (Finset.mem_filter.mp hs).2.ne']

private theorem nzEq_InChart_eq {K : ℕ} {σ : Fin M → ℝ} {σ' : Fin K → ℝ} (h : NzEq σ σ') :
    InChart σ = InChart σ' := funext fun y => by simp only [InChart, nzEq_posVals_eq h]

private theorem nzEq_yEdge_eq {K : ℕ} {σ : Fin M → ℝ} {σ' : Fin K → ℝ} (h : NzEq σ σ')
    (N : ℕ) : yEdge N σ = yEdge N σ' := by
  unfold yEdge
  rw [nzEq_InChart_eq h, nzEq_FChart1_eq h N]

private theorem nzEq_xCrit_eq {K : ℕ} {σ : Fin M → ℝ} {σ' : Fin K → ℝ} (h : NzEq σ σ')
    (N : ℕ) : xCrit N σ = xCrit N σ' := by
  unfold xCrit
  rw [h.numBands_eq N, nzEq_yEdge_eq h N, nzEq_innerCrit_eq h N]

theorem NzEq.edgeVal_eq {K : ℕ} {σ : Fin M → ℝ} {σ' : Fin K → ℝ} (h : NzEq σ σ') (N : ℕ) :
    edgeVal N σ = edgeVal N σ' := by
  unfold edgeVal
  rw [h.numBands_eq N, nzEq_FChart_eq h N, nzEq_yEdge_eq h N, nzEq_fR_eq h N, nzEq_xCrit_eq h N]

theorem NzEq.regularEdge_iff {K : ℕ} {σ : Fin M → ℝ} {σ' : Fin K → ℝ} (h : NzEq σ σ')
    (τ : ℝ) (N k : ℕ) : RegularEdge τ N σ k ↔ RegularEdge τ N σ' k := by
  unfold RegularEdge
  rw [h.numBands_eq N, h.edgeVal_eq N, nzEq_yEdge_eq h N, nzEq_xCrit_eq h N, nzEq_posVals_eq h]

theorem NzEq.regularBulk_iff {K : ℕ} {σ : Fin M → ℝ} {σ' : Fin K → ℝ} (h : NzEq σ σ')
    (c : ℝ → ℝ) (N k : ℕ) : RegularBulk c N σ k ↔ RegularBulk c N σ' k := by
  unfold RegularBulk
  rw [h.numBands_eq N, h.edgeVal_eq N, nzEq_rhoDens_eq h N]

theorem NzEq.cumCount_eq {K : ℕ} {σ : Fin M → ℝ} {σ' : Fin K → ℝ} (h : NzEq σ σ') (N : ℕ) :
    cumCount N σ = cumCount N σ' := by
  funext k
  unfold cumCount bandCount
  rw [h.varrho_eq N, h.edgeVal_eq N]

/-- `Ŝ + κ P₀` (`P₀` the projection on `ker Ŝ`): `κ` on `ker Ŝ`, `Ŝ` on `ran Ŝ`, by spectral
calculus. -/
def regS {K : ℕ} (κ : ℝ) (S : Matrix (Fin K) (Fin K) ℝ) : Matrix (Fin K) (Fin K) ℝ :=
  cfc (fun x : ℝ => if 0 < x then x else κ) S

private theorem regS_isHermitian {K : ℕ} (κ : ℝ) (S : Matrix (Fin K) (Fin K) ℝ) :
    (regS κ S).IsHermitian :=
  Matrix.isHermitian_iff_isSelfAdjoint.mpr (cfc_predicate _ S)

/-- The eigenvalue multiset of `regS κ S` is the image of that of `S` under `x ↦ if 0 < x then x
else κ`. -/
private theorem regS_eig_multiset {K : ℕ} (κ : ℝ) {S : Matrix (Fin K) (Fin K) ℝ}
    (hS : S.IsHermitian) :
    Finset.univ.val.map (specOf (regS κ S)) =
      Finset.univ.val.map (fun j => if 0 < specOf S j then specOf S j else κ) := by
  have h1 := (regS_isHermitian κ S).roots_charpoly_eq_eigenvalues
  have h2 : (regS κ S).charpoly = ∏ i, (Polynomial.X - Polynomial.C
      (if 0 < hS.eigenvalues i then hS.eigenvalues i else κ)) :=
    hS.charpoly_cfc_eq _
  rw [h2, Polynomial.roots_prod] at h1
  · rw [specOf_eq (regS_isHermitian κ S), specOf_eq hS]
    simp only [Polynomial.roots_X_sub_C] at h1
    simpa [Function.comp_def, RCLike.ofReal_real_eq_id] using h1.symm
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

private theorem regS_sum {K : ℕ} (κ : ℝ) {S : Matrix (Fin K) (Fin K) ℝ} (hS : S.IsHermitian)
    {E : Type*} [AddCommMonoid E] (F : ℝ → E) :
    ∑ i, F (specOf (regS κ S) i) = ∑ j, F (if 0 < specOf S j then specOf S j else κ) := by
  have h := congrArg (fun m => (m.map F).sum) (regS_eig_multiset κ hS)
  simpa [Multiset.map_map, Finset.sum_eq_multiset_sum, Function.comp_def] using h

theorem regS_posDef {K : ℕ} {κ : ℝ} (hκ : 0 < κ) (T : Matrix (Fin M) (Fin K) ℝ) :
    (regS κ (Tᵀ * T)).PosDef := by
  have hS : (Tᵀ * T).IsHermitian := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.posSemidef_conjTranspose_mul_self T).isHermitian
  have hB := regS_isHermitian κ (Tᵀ * T)
  rw [hB.posDef_iff_eigenvalues_pos]
  intro i
  have hmem : specOf (regS κ (Tᵀ * T)) i ∈
      Finset.univ.val.map (fun j => if 0 < specOf (Tᵀ * T) j then specOf (Tᵀ * T) j else κ) := by
    rw [← regS_eig_multiset κ hS]
    exact Multiset.mem_map_of_mem _ (Finset.mem_univ i)
  rw [Multiset.mem_map] at hmem
  obtain ⟨j, -, hj⟩ := hmem
  rw [specOf_eq hB] at hj
  rw [← hj]
  split_ifs with h
  · exact h
  · exact hκ

private theorem regS_hermitian_TT {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ) :
    (Tᵀ * T).IsHermitian := by
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.posSemidef_conjTranspose_mul_self T).isHermitian

private theorem regS_card_zero {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ) :
    (Finset.univ.filter fun j => specOf (Tᵀ * T) j = 0).card = K - T.rank := by
  have hS := regS_hermitian_TT T
  have h1 := hS.rank_eq_card_non_zero_eigs
  rw [Matrix.rank_transpose_mul_self, Fintype.card_subtype] at h1
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin K)))
    (fun j => specOf (Tᵀ * T) j = 0)
  rw [Finset.card_univ, Fintype.card_fin] at h2
  have h3 : (Finset.univ.filter fun j => hS.eigenvalues j ≠ 0).card =
      (Finset.univ.filter fun j => ¬ specOf (Tᵀ * T) j = 0).card := by
    rw [specOf_eq hS]
  omega

/-- `f` of `Ŝ + κ P₀` is `f` of `Σ = T Tᵀ` plus the atom `κ` of weight `(K − rank T)/N`. -/
theorem fC_regS {K : ℕ} (N : ℕ) {κ : ℝ} (hκ : 0 < κ) (T : Matrix (Fin M) (Fin K) ℝ) (w : ℂ) :
    fC N (specOf (regS κ (Tᵀ * T))) w = fC N (specOf (T * Tᵀ)) w +
      ((K - T.rank : ℕ) : ℂ) * κ / (N * (1 + κ * w)) := by
  have _ := hκ
  have hS := regS_hermitian_TT T
  set F : ℝ → ℂ := fun s => (s : ℂ) / (N * (1 + s * w)) with hF
  have hF0 : F 0 = 0 := by simp [hF]
  have hnn : ∀ j, 0 ≤ specOf (Tᵀ * T) j := by
    intro j
    rw [specOf_eq hS]
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.posSemidef_conjTranspose_mul_self T).eigenvalues_nonneg j
  unfold fC
  rw [add_assoc]
  congr 1
  have e1 : ∑ i, ((specOf (regS κ (Tᵀ * T)) i : ℝ) : ℂ) /
      (N * (1 + specOf (regS κ (Tᵀ * T)) i * w)) =
      ∑ j, F (if 0 < specOf (Tᵀ * T) j then specOf (Tᵀ * T) j else κ) :=
    regS_sum κ hS F
  have e2 : ∀ j, F (if 0 < specOf (Tᵀ * T) j then specOf (Tᵀ * T) j else κ) =
      F (specOf (Tᵀ * T) j) + if specOf (Tᵀ * T) j = 0 then F κ else 0 := by
    intro j
    by_cases h : 0 < specOf (Tᵀ * T) j
    · simp [h, h.ne']
    · have h0 : specOf (Tᵀ * T) j = 0 := le_antisymm (not_lt.mp h) (hnn j)
      simp [h0, hF0]
  have e3 : ∑ j, F (specOf (Tᵀ * T) j) = ∑ i, F (specOf (T * Tᵀ) i) :=
    (nzEq_sum_eq (nzEq_specOf_mul_transpose T) F hF0).symm
  rw [e1]
  simp_rw [e2]
  rw [Finset.sum_add_distrib, e3, ← Finset.sum_filter, Finset.sum_const, regS_card_zero,
    nsmul_eq_mul, mul_div_assoc]

private theorem regS_ncard_setOf {n : ℕ} (P : Fin n → Prop) :
    {i | P i}.ncard = (Finset.univ.filter P).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext i
  simp

private theorem regS_card_zero_left {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ) :
    (Finset.univ.filter fun i => specOf (T * Tᵀ) i = 0).card = M - T.rank := by
  have h := regS_card_zero Tᵀ
  rw [Matrix.transpose_transpose, Matrix.rank_transpose] at h
  exact h

/-- Assumption 2.1 for general `T` at `τ` gives Assumption 2.1 under (T_diag) for
`(Ŝ + κ P₀, X)` at `τ³`, for `0 < κ ≤ τ³`. -/
theorem isModel_regS {Ω : Type*} [MeasureSpace Ω] {τ : ℝ} {C : ℕ → ℝ} {K : ℕ}
    {T : Matrix (Fin M) (Fin K) ℝ} {X : Ω → Matrix (Fin K) (Fin N) ℝ} (hτ : 0 < τ)
    (hm : IsModelT τ C M K N T X) {κ : ℝ} (hκ : 0 < κ) (hκτ : κ ≤ τ ^ 3) :
    IsModel (τ ^ 3) C K N (regS κ (Tᵀ * T)) X := by
  have hS := regS_hermitian_TT T
  have hnz := nzEq_specOf_mul_transpose T
  have hN : (0 : ℝ) < N := by
    rcases (Nat.cast_nonneg N : (0 : ℝ) ≤ N).lt_or_eq with h | h
    · exact h
    · have := hm.ratio_ge
      rw [← h, div_zero] at this
      linarith
  have hMr : τ * N ≤ M := by
    have := hm.ratio_ge
    rwa [le_div_iff₀ hN] at this
  have hKr : (K : ℝ) ≤ τ⁻¹ * N := by
    have := hm.ratioK_le
    rwa [div_le_iff₀ hN] at this
  have hKr' : τ * K ≤ N := by
    have h := mul_le_mul_of_nonneg_left hKr hτ.le
    rwa [← mul_assoc, mul_inv_cancel₀ hτ.ne', one_mul] at h
  have hτ1 : τ ≤ 1 := by
    by_contra hc
    have hc := not_le.mp hc
    have h1 : (M : ℝ) / N ≤ τ⁻¹ := hm.ratio_le
    have h2 : τ ≤ (M : ℝ) / N := hm.ratio_ge
    have h3 : τ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hc
    linarith
  have hτ3 : τ ^ 3 ≤ τ := by
    have : τ ^ 3 = τ * (τ * τ) := by ring
    rw [this]
    nlinarith [mul_pos hτ hτ]
  have hτ3pos : 0 < τ ^ 3 := by positivity
  have hinv : τ⁻¹ ≤ (τ ^ 3)⁻¹ := inv_anti₀ hτ3pos hτ3
  refine ⟨?_, ?_, hm.entries, ⟨regS_posDef hκ T, ?_, ?_⟩⟩
  · rw [le_div_iff₀ hN]
    have : τ ^ 3 * N ≤ τ * N := mul_le_mul_of_nonneg_right hτ3 hN.le
    have h2 : τ * N ≤ K := by
      have := hm.ratioK_ge
      rwa [le_div_iff₀ hN] at this
    linarith
  · exact hm.ratioK_le.trans hinv
  · intro i
    have hB := regS_isHermitian κ (Tᵀ * T)
    have hmem : specOf (regS κ (Tᵀ * T)) i ∈
        Finset.univ.val.map
          (fun j => if 0 < specOf (Tᵀ * T) j then specOf (Tᵀ * T) j else κ) := by
      rw [← regS_eig_multiset κ hS]
      exact Multiset.mem_map_of_mem _ (Finset.mem_univ i)
    rw [Multiset.mem_map] at hmem
    obtain ⟨j, -, hj⟩ := hmem
    have he : (regS_posDef hκ T).isHermitian.eigenvalues i = specOf (regS κ (Tᵀ * T)) i :=
      (congrFun (specOf_eq (regS_isHermitian κ (Tᵀ * T))) i).symm
    rw [he, ← hj]
    split_ifs with h
    · have hpos : 0 < (Finset.univ.filter fun j' =>
          specOf (Tᵀ * T) j' = specOf (Tᵀ * T) j).card := by
        rw [Finset.card_pos]
        exact ⟨j, by simp⟩
      rw [← hnz _ h.ne'] at hpos
      obtain ⟨i', hi'⟩ := Finset.card_pos.mp hpos
      have := hm.eig_le i'
      rw [(Finset.mem_filter.mp hi').2] at this
      exact this.trans hinv
    · have : κ ≤ 1 := hκτ.trans (pow_le_one₀ hτ.le hτ1)
      exact this.trans (by
        have : (1 : ℝ) ≤ (τ ^ 3)⁻¹ := one_le_inv₀ hτ3pos |>.mpr (pow_le_one₀ hτ.le hτ1)
        exact this)
  · -- counting
    have hgap := hm.gap
    rw [regS_ncard_setOf] at hgap
    have he : ∀ i, (regS_posDef hκ T).isHermitian.eigenvalues i =
        specOf (regS κ (Tᵀ * T)) i := fun i =>
      (congrFun (specOf_eq (regS_isHermitian κ (Tᵀ * T))) i).symm
    simp only [he]
    rw [regS_ncard_setOf]
    set r := T.rank with hr
    have hrM : r ≤ M := Matrix.rank_le_height T
    have hrK : r ≤ K := Matrix.rank_le_width T
    have c1 : (Finset.univ.filter fun i => specOf (regS κ (Tᵀ * T)) i ∈ Set.Icc 0 (τ ^ 3)).card =
        (K - r) + (Finset.univ.filter fun i => specOf (T * Tᵀ) i ∈ Set.Ioc 0 (τ ^ 3)).card := by
      rw [Finset.card_filter, Finset.card_filter]
      rw [regS_sum κ hS (fun s => if s ∈ Set.Icc 0 (τ ^ 3) then (1 : ℕ) else 0)]
      have e1 : ∀ j, (if (if 0 < specOf (Tᵀ * T) j then specOf (Tᵀ * T) j else κ) ∈
          Set.Icc 0 (τ ^ 3) then (1 : ℕ) else 0) =
          (if specOf (Tᵀ * T) j = 0 then 1 else 0) +
          (if specOf (Tᵀ * T) j ∈ Set.Ioc 0 (τ ^ 3) then 1 else 0) := by
        intro j
        have hnn : 0 ≤ specOf (Tᵀ * T) j := by
          rw [specOf_eq hS]
          simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
            (Matrix.posSemidef_conjTranspose_mul_self T).eigenvalues_nonneg j
        by_cases h : 0 < specOf (Tᵀ * T) j
        · simp [h, h.ne', Set.mem_Icc, Set.mem_Ioc, h.le]
        · have h0 : specOf (Tᵀ * T) j = 0 := le_antisymm (not_lt.mp h) hnn
          simp [h0, hκ.le, hκτ]
      simp_rw [e1]
      rw [Finset.sum_add_distrib, ← Finset.card_filter, regS_card_zero T]
      congr 1
      exact (nzEq_sum_eq hnz (fun s => if s ∈ Set.Ioc 0 (τ ^ 3) then (1 : ℕ) else 0)
        (by simp)).symm
    suffices key : (((K - r + (Finset.univ.filter fun i => specOf (T * Tᵀ) i ∈
        Set.Ioc 0 (τ ^ 3)).card : ℕ)) : ℝ) ≤ (1 - τ ^ 3) * K by
      rw [← c1] at key
      convert key
    have c2 : (Finset.univ.filter fun i => specOf (T * Tᵀ) i ∈ Set.Ioc 0 (τ ^ 3)).card +
        (Finset.univ.filter fun i => specOf (T * Tᵀ) i = 0).card ≤
        (Finset.univ.filter fun i => specOf (T * Tᵀ) i ∈ Set.Icc 0 τ).card := by
      rw [← Finset.card_union_of_disjoint]
      · apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Ioc,
          Set.mem_Icc] at hi ⊢
        rcases hi with h | h
        · exact ⟨h.1.le, h.2.trans hτ3⟩
        · exact ⟨h.ge, by rw [h]; exact hτ.le⟩
      · rw [Finset.disjoint_filter]
        intro i _ h1 h2
        simp only [Set.mem_Ioc] at h1
        rw [h2] at h1
        exact lt_irrefl _ h1.1
    rw [regS_card_zero_left T] at c2
    have c2' : (((Finset.univ.filter fun i => specOf (T * Tᵀ) i ∈ Set.Ioc 0 (τ ^ 3)).card : ℕ) : ℝ)
        + ((M - r : ℕ) : ℝ) ≤
        (((Finset.univ.filter fun i => specOf (T * Tᵀ) i ∈ Set.Icc 0 τ).card : ℕ) : ℝ) := by
      exact_mod_cast c2
    rw [Nat.cast_sub hrM] at c2'
    have hgap' : (((Finset.univ.filter fun i => specOf (T * Tᵀ) i ∈ Set.Icc 0 τ).card : ℕ) : ℝ)
        ≤ (1 - τ) * M := by
      convert hgap
    push_cast [Nat.cast_sub hrK]
    have h3 : τ ^ 2 * K ≤ M := by
      have := mul_le_mul_of_nonneg_left hKr' hτ.le
      nlinarith
    have h4 : τ ^ 3 * K ≤ τ * M := by
      have := mul_le_mul_of_nonneg_left h3 hτ.le
      nlinarith
    nlinarith

/-! ## Instances of the statements above at `T = (1; 0)` (`M = 2`, `K = 1`, `N = 2`),
where `T Tᵀ = diag(1, 0)` and `Tᵀ T = (1)` have different sizes. -/

example : mFun 2 (specOf (!![(1 : ℝ); 0] * (!![(1 : ℝ); 0])ᵀ)) =
    mFun 2 (specOf ((!![(1 : ℝ); 0])ᵀ * !![(1 : ℝ); 0])) :=
  (nzEq_specOf_mul_transpose _).mFun_eq 2

example : varrho 2 (specOf (!![(1 : ℝ); 0] * (!![(1 : ℝ); 0])ᵀ)) =
    varrho 2 (specOf ((!![(1 : ℝ); 0])ᵀ * !![(1 : ℝ); 0])) :=
  (nzEq_specOf_mul_transpose _).varrho_eq 2

example : numBands 2 (specOf (!![(1 : ℝ); 0] * (!![(1 : ℝ); 0])ᵀ)) =
    numBands 2 (specOf ((!![(1 : ℝ); 0])ᵀ * !![(1 : ℝ); 0])) :=
  (nzEq_specOf_mul_transpose _).numBands_eq 2

example : edgeVal 2 (specOf (!![(1 : ℝ); 0] * (!![(1 : ℝ); 0])ᵀ)) =
    edgeVal 2 (specOf ((!![(1 : ℝ); 0])ᵀ * !![(1 : ℝ); 0])) :=
  (nzEq_specOf_mul_transpose _).edgeVal_eq 2

example : RegularEdge (1 / 2) 2 (specOf (!![(1 : ℝ); 0] * (!![(1 : ℝ); 0])ᵀ)) 1 ↔
    RegularEdge (1 / 2) 2 (specOf ((!![(1 : ℝ); 0])ᵀ * !![(1 : ℝ); 0])) 1 :=
  (nzEq_specOf_mul_transpose _).regularEdge_iff _ 2 1

example : RegularBulk (fun t => t) 2 (specOf (!![(1 : ℝ); 0] * (!![(1 : ℝ); 0])ᵀ)) 1 ↔
    RegularBulk (fun t => t) 2 (specOf ((!![(1 : ℝ); 0])ᵀ * !![(1 : ℝ); 0])) 1 :=
  (nzEq_specOf_mul_transpose _).regularBulk_iff _ 2 1

example : cumCount 2 (specOf (!![(1 : ℝ); 0] * (!![(1 : ℝ); 0])ᵀ)) =
    cumCount 2 (specOf ((!![(1 : ℝ); 0])ᵀ * !![(1 : ℝ); 0])) :=
  (nzEq_specOf_mul_transpose _).cumCount_eq 2

/-- `T = (1, 1)` (`M = 1`, `K = 2`), `κ = 1/8`: `Ŝ + κ P₀` is positive definite. -/
example : (regS (1 / 8 : ℝ) ((!![(1 : ℝ), 1])ᵀ * !![(1 : ℝ), 1])).PosDef :=
  regS_posDef (by norm_num) _

/-- `T = (1, 1)`, `N = 2`, `κ = 1/8`, `w = i`: `f` of `Ŝ + κ P₀` is `f` of `Σ = (2)` plus the
atom `κ` of weight `(K − rank T)/N = 1/2`. -/
example : fC 2 (specOf (regS (1 / 8 : ℝ) ((!![(1 : ℝ), 1])ᵀ * !![(1 : ℝ), 1]))) Complex.I =
    fC 2 (specOf (!![(1 : ℝ), 1] * (!![(1 : ℝ), 1])ᵀ)) Complex.I +
      (((2 - (!![(1 : ℝ), 1]).rank : ℕ) : ℂ)) * ((1 / 8 : ℝ) : ℂ) /
        ((2 : ℕ) * (1 + ((1 / 8 : ℝ) : ℂ) * Complex.I)) :=
  fC_regS 2 (by norm_num) _ _

end Anisotropic
