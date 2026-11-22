module

public import Anisotropic.EdgeUniv.Defs
public import Anisotropic.EdgeUniv.Eigen
public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.Framework.Domination
public import Anisotropic.Gaussian.Invariance
public import Anisotropic.GeneralT.Spectra
public import Anisotropic.Probability.NormBound.GaussianLower

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # Invariance of `ϖ_k` and `bRef` under nonzero-spectrum equivalence, and the Gaussian reduction -/

/-! ## `ϖ_k` depends only on the nonzero values with multiplicity -/

/-- Sums of a function vanishing at `0` over two families with the same nonzero values and
multiplicities agree. -/
private theorem sum_eq_of_nzEq {K : ℕ} {σ : Fin M → ℝ} {σ' : Fin K → ℝ} (h : NzEq σ σ')
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

private theorem posVals_eq_of_nzEq {K : ℕ} {σ : Fin M → ℝ} {σ' : Fin K → ℝ} (h : NzEq σ σ') :
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

private theorem weight_eq_of_nzEq {K : ℕ} {σ : Fin M → ℝ} {σ' : Fin K → ℝ} (h : NzEq σ σ')
    (N : ℕ) {s : ℝ} (hs : s ≠ 0) : weight N σ s = weight N σ' s := by
  unfold weight
  rw [h s hs]

private theorem critPoly_eq_of_nzEq {K : ℕ} {σ : Fin M → ℝ} {σ' : Fin K → ℝ} (h : NzEq σ σ')
    (N : ℕ) : critPoly N σ = critPoly N σ' := by
  unfold critPoly
  rw [← posVals_eq_of_nzEq h]
  refine congrArg _ (congrArg _ (Finset.sum_congr rfl fun s hs => ?_))
  rw [weight_eq_of_nzEq h N (Finset.mem_filter.mp hs).2.ne']

private theorem innerCrit_eq_of_nzEq {K : ℕ} {σ : Fin M → ℝ} {σ' : Fin K → ℝ} (h : NzEq σ σ')
    (N : ℕ) : innerCrit N σ = innerCrit N σ' := by
  have hI : InInner σ = InInner σ' :=
    funext fun x => by simp only [InInner, posVals_eq_of_nzEq h]
  unfold innerCrit
  rw [critPoly_eq_of_nzEq h N, hI]

private theorem FChart1_eq_of_nzEq {K : ℕ} {σ : Fin M → ℝ} {σ' : Fin K → ℝ} (h : NzEq σ σ')
    (N : ℕ) : FChart1 N σ = FChart1 N σ' := by
  funext y
  unfold FChart1
  rw [← posVals_eq_of_nzEq h]
  refine congrArg _ (Finset.sum_congr rfl fun s hs => ?_)
  rw [weight_eq_of_nzEq h N (Finset.mem_filter.mp hs).2.ne']

private theorem yEdge_eq_of_nzEq {K : ℕ} {σ : Fin M → ℝ} {σ' : Fin K → ℝ} (h : NzEq σ σ')
    (N : ℕ) : yEdge N σ = yEdge N σ' := by
  have hC : InChart σ = InChart σ' :=
    funext fun y => by simp only [InChart, posVals_eq_of_nzEq h]
  unfold yEdge
  rw [hC, FChart1_eq_of_nzEq h N]

private theorem xCrit_eq_of_nzEq {K : ℕ} {σ : Fin M → ℝ} {σ' : Fin K → ℝ} (h : NzEq σ σ')
    (N : ℕ) : xCrit N σ = xCrit N σ' := by
  unfold xCrit
  rw [h.numBands_eq N, yEdge_eq_of_nzEq h N, innerCrit_eq_of_nzEq h N]

private theorem fR2_eq_of_nzEq {K : ℕ} {σ : Fin M → ℝ} {σ' : Fin K → ℝ} (h : NzEq σ σ')
    (N : ℕ) : fR2 N σ = fR2 N σ' := by
  funext x
  unfold fR2
  congr 2
  exact sum_eq_of_nzEq h (fun s : ℝ => s ^ 3 / (N * (1 + s * x) ^ 3)) (by simp)

/-- `ϖ_k` depends only on the nonzero values of `σ` with multiplicity. -/
theorem NzEq.edgeScale_eq {K : ℕ} {σ : Fin M → ℝ} {σ' : Fin K → ℝ} (h : NzEq σ σ') (N : ℕ) :
    edgeScale N σ = edgeScale N σ' := by
  funext k
  unfold edgeScale
  rw [xCrit_eq_of_nzEq h N, fR2_eq_of_nzEq h N]

/-! ## The law of `Q_N` depends only on the nonzero values of `σ` with multiplicity -/

/-- The scale-and-centre data of `q_{k,l}` depend on `σ` only through its nonzero values with
multiplicity. -/
private theorem qVecA_eq_of_nzEq {K n : ℕ} {σ : Fin M → ℝ} {σ' : Fin K → ℝ} (h : NzEq σ σ')
    (N : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (k l : ℕ) : qVecA N σ' A k l = qVecA N σ A k l := by
  funext i
  unfold qVecA edgeIdx
  rw [h.cumCount_eq N, h.edgeVal_eq N, h.edgeScale_eq N]

/-- The matrix of entries of a point of `Fin K × Fin N → ℝ`. -/
private def unflatMat {K N : ℕ} (x : Fin K × Fin N → ℝ) : Matrix (Fin K) (Fin N) ℝ :=
  fun i μ => x (i, μ)

private lemma measurable_unflatMat {K N : ℕ} : Measurable (unflatMat (K := K) (N := N)) :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun μ => measurable_pi_apply (i, μ)

/-- `A ↦ Aᵀ Σ A` is measurable. -/
private lemma measurable_QN (Sig : Matrix (Fin M) (Fin M) ℝ) :
    Measurable fun Xm : Matrix (Fin M) (Fin N) ℝ => QN Sig Xm :=
  ((continuous_id.matrix_transpose.matrix_mul continuous_const).matrix_mul
    continuous_id).measurable

/-- The law of a Gaussian ensemble is the image of the product of the entry laws. -/
private lemma map_eq_pi_map {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {K N : ℕ} {X : Ω → Matrix (Fin K) (Fin N) ℝ} (hX : IsGaussianEnsemble X) :
    (ℙ : Measure Ω).map X =
      (Measure.pi fun _ : Fin K × Fin N => gaussianReal 0 (N : ℝ≥0)⁻¹).map unflatMat := by
  have h : X = unflatMat ∘ fun ω (p : Fin K × Fin N) => X ω p.1 p.2 := rfl
  have hm : Measurable fun ω (p : Fin K × Fin N) => X ω p.1 p.2 :=
    measurable_pi_iff.2 fun p => hX.measurable p.1 p.2
  rw [h, ← Measure.map_map measurable_unflatMat hm, hX.map_entries]

/-- Two Gaussian ensembles of the same shape give the same integrals of measurable functions. -/
private lemma integral_ensemble_eq {Ω Ω' : Type*} [MeasureSpace Ω] [MeasureSpace Ω']
    [IsProbabilityMeasure (ℙ : Measure Ω)] [IsProbabilityMeasure (ℙ : Measure Ω')] {K N : ℕ}
    {X : Ω → Matrix (Fin K) (Fin N) ℝ} {Y : Ω' → Matrix (Fin K) (Fin N) ℝ}
    (hX : IsGaussianEnsemble X) (hY : IsGaussianEnsemble Y)
    {g : Matrix (Fin K) (Fin N) ℝ → ℝ} (hg : Measurable g) :
    ∫ ω, g (X ω) = ∫ ω, g (Y ω) := by
  rw [← integral_map hX.measurable_mat.aemeasurable hg.aestronglyMeasurable,
    ← integral_map hY.measurable_mat.aemeasurable hg.aestronglyMeasurable, map_eq_pi_map hX,
    map_eq_pi_map hY]

/-- The rows of `gaussX M N` along an injective index map form a Gaussian `m × N` ensemble. -/
private lemma isGaussianEnsemble_rows {m : ℕ} {e : Fin m → Fin M} (he : Function.Injective e)
    (N : ℕ) :
    IsGaussianEnsemble (fun (ω : GaussSpace M N) (a : Fin m) (μ : Fin N) =>
      gaussX M N ω (e a) μ) where
  measurable a μ := (gaussX_isGaussianEnsemble M N).measurable (e a) μ
  indep := (gaussX_isGaussianEnsemble M N).indep.precomp
    (g := fun p : Fin m × Fin N => (e p.1, p.2))
    (fun p q hpq => by
      simp only [Prod.mk.injEq] at hpq
      exact Prod.ext (he hpq.1) hpq.2)
  law a μ := (gaussX_isGaussianEnsemble M N).law (e a) μ

/-- The entries of `Xᵀ diag(v) X`. -/
private lemma QN_diagonal_apply {m : ℕ} (v : Fin m → ℝ) (Y : Matrix (Fin m) (Fin N) ℝ)
    (μ ν : Fin N) : QN (diagonal v) Y μ ν = ∑ i, Y i μ * v i * Y i ν := by
  rw [QN, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]

/-- `Xᵀ diag(σ) X` only involves the rows of `X` on which `σ` is nonzero. -/
private lemma QN_diagonal_rows {m : ℕ} {σ : Fin M → ℝ} {e : Fin m → Fin M}
    (he : Function.Injective e) (hz : ∀ i, i ∉ Set.range e → σ i = 0)
    (Xm : Matrix (Fin M) (Fin N) ℝ) :
    QN (diagonal σ) Xm =
      QN (diagonal (σ ∘ e)) (fun (a : Fin m) (μ : Fin N) => Xm (e a) μ) := by
  have key : ∀ F : Fin M → ℝ, (∀ i, i ∉ Set.range e → F i = 0) →
      ∑ i, F i = ∑ a, F (e a) := by
    intro F hF
    rw [← Finset.sum_image (f := F) (fun a _ b _ hab => he hab)]
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => hF i fun ⟨a, ha⟩ => hi ?_
    exact Finset.mem_image.2 ⟨a, Finset.mem_univ _, ha⟩
  ext μ ν
  rw [QN_diagonal_apply, QN_diagonal_apply (σ ∘ e) (fun (a : Fin m) (μ : Fin N) => Xm (e a) μ)]
  refine key _ fun i hi => ?_
  rw [hz i hi]
  ring

/-- Dropping the rows of `X` on which `σ` vanishes does not change the integral of a measurable
function of `Q_N = Xᵀ diag(σ) X` for Gaussian `X`. -/
private lemma integral_QN_rows {m : ℕ} {σ : Fin M → ℝ} {e : Fin m → Fin M}
    (he : Function.Injective e) (hz : ∀ i, i ∉ Set.range e → σ i = 0) (N : ℕ)
    {G : Matrix (Fin N) (Fin N) ℝ → ℝ} (hG : Measurable G) :
    ∫ ω, G (QN (diagonal σ) (gaussX M N ω)) =
      ∫ ω, G (QN (diagonal (σ ∘ e)) (gaussX m N ω)) := by
  have hQ : Measurable fun Xm : Matrix (Fin m) (Fin N) ℝ => G (QN (diagonal (σ ∘ e)) Xm) :=
    hG.comp (measurable_QN _)
  have h1 : ∀ ω : GaussSpace M N, G (QN (diagonal σ) (gaussX M N ω)) =
      G (QN (diagonal (σ ∘ e)) (fun (a : Fin m) (μ : Fin N) => gaussX M N ω (e a) μ)) :=
    fun ω => by rw [QN_diagonal_rows he hz]
  simp_rw [h1]
  exact integral_ensemble_eq (isGaussianEnsemble_rows he N) (gaussX_isGaussianEnsemble m N) hQ

/-- Two families with the same nonzero values and multiplicities are reindexed, by injective maps
whose ranges contain the supports, to one family. -/
private lemma exists_common_rows {K : ℕ} {σ : Fin M → ℝ} {σ' : Fin K → ℝ} (h : NzEq σ σ') :
    ∃ (m : ℕ) (e : Fin m → Fin M) (e' : Fin m → Fin K), Function.Injective e ∧
      Function.Injective e' ∧ (∀ i, i ∉ Set.range e → σ i = 0) ∧
      (∀ j, j ∉ Set.range e' → σ' j = 0) ∧ σ ∘ e = σ' ∘ e' := by
  let S := {i : Fin M // σ i ≠ 0}
  let S' := {j : Fin K // σ' j ≠ 0}
  have hfib : ∀ c : ℝ, Nonempty ({a : S // σ a.1 = c} ≃ {b : S' // σ' b.1 = c}) := by
    intro c
    by_cases hc : c = 0
    · subst hc
      have : IsEmpty {a : S // σ a.1 = 0} := ⟨fun a => a.1.2 a.2⟩
      have : IsEmpty {b : S' // σ' b.1 = 0} := ⟨fun b => b.1.2 b.2⟩
      exact ⟨Equiv.equivOfIsEmpty _ _⟩
    · have e1 : {a : S // σ a.1 = c} ≃ {i : Fin M // σ i = c} :=
        (Equiv.subtypeSubtypeEquivSubtypeInter (fun i => σ i ≠ 0) (fun i => σ i = c)).trans
          (Equiv.subtypeEquivRight fun i =>
            ⟨fun hi => hi.2, fun hi => ⟨by rw [hi]; exact hc, hi⟩⟩)
      have e2 : {b : S' // σ' b.1 = c} ≃ {j : Fin K // σ' j = c} :=
        (Equiv.subtypeSubtypeEquivSubtypeInter (fun j => σ' j ≠ 0) (fun j => σ' j = c)).trans
          (Equiv.subtypeEquivRight fun j =>
            ⟨fun hj => hj.2, fun hj => ⟨by rw [hj]; exact hc, hj⟩⟩)
      have hcard : Fintype.card {i : Fin M // σ i = c} = Fintype.card {j : Fin K // σ' j = c} := by
        rw [Fintype.card_subtype, Fintype.card_subtype]
        exact h c hc
      exact ⟨e1.trans ((Fintype.equivOfCardEq hcard).trans e2.symm)⟩
  let φ : S ≃ S' := Equiv.ofFiberEquiv (f := fun a : S => σ a.1) (g := fun b : S' => σ' b.1)
    fun c => (hfib c).some
  have hφ : ∀ a : S, σ' (φ a).1 = σ a.1 := fun a =>
    Equiv.ofFiberEquiv_map (f := fun a : S => σ a.1) (g := fun b : S' => σ' b.1)
      (fun c => (hfib c).some) a
  let ι : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  refine ⟨Fintype.card S, fun a => (ι.symm a).1, fun a => (φ (ι.symm a)).1, ?_, ?_, ?_, ?_, ?_⟩
  · exact Subtype.val_injective.comp ι.symm.injective
  · exact Subtype.val_injective.comp (φ.injective.comp ι.symm.injective)
  · intro i hi
    by_contra hne
    exact hi ⟨ι ⟨i, hne⟩, by simp⟩
  · intro j hj
    by_contra hne
    refine hj ⟨ι (φ.symm ⟨j, hne⟩), ?_⟩
    simp
  · funext a
    exact (hφ (ι.symm a)).symm

/-- `bRef` depends only on the nonzero values of `σ` with multiplicity (stated after
Theorem 3.18: not on the dimensions of `T`). -/
theorem bRef_nzEq {K : ℕ} {σ : Fin M → ℝ} {σ' : Fin K → ℝ} (h : NzEq σ σ')
    (hσ : ∀ i, 0 ≤ σ i) (hσ' : ∀ j, 0 ≤ σ' j) (N k l : ℕ) {f : (Fin l → ℝ) → ℝ}
    (hf : Measurable f) : bRef N σ k l f = bRef N σ' k l f := by
  have _ := hσ
  have _ := hσ'
  obtain ⟨m, e, e', he, he', hz, hz', hc⟩ := exists_common_rows h
  have hG : Measurable fun A : Matrix (Fin N) (Fin N) ℝ => f (qVecA N σ A k l) :=
    hf.comp (measurable_qVecA N σ N k l)
  have hG' : Measurable fun A : Matrix (Fin N) (Fin N) ℝ => f (qVecA N σ' A k l) :=
    hf.comp (measurable_qVecA N σ' N k l)
  have h1 := integral_QN_rows he hz N hG
  have h2 := integral_QN_rows he' hz' N hG'
  unfold bRef
  rw [h1, h2, ← hc]
  simp_rw [qVecA_eq_of_nzEq h]

/-! ## The Gaussian reduction -/

/-- The Gaussian reduction (proof of Theorem 3.18, last paragraph): for Gaussian `X`, the law of
`q_{k,l}` for `Σ` is that for `diag(spec Σ)`. -/
theorem bRef_gauss {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) (N k l : ℕ)
    {f : (Fin l → ℝ) → ℝ} (hf : Measurable f) :
    ∫ ω, f (qVec Sig (gaussX M N ω) k l) = bRef N (specOf Sig) k l f := by
  obtain ⟨U, hU, hD⟩ := exists_orth_diag hSig.isHermitian
  have hUU : U * Uᵀ = 1 := (Matrix.mem_orthogonalGroup_iff _ _).1 hU
  have hUU' : Uᵀ * U = 1 := (Matrix.mem_orthogonalGroup_iff' _ _).1 hU
  have hUt : Uᵀ ∈ Matrix.orthogonalGroup (Fin M) ℝ := by
    rw [Matrix.mem_orthogonalGroup_iff, transpose_transpose]
    exact hUU'
  have hdec : Sig = U * diagonal (specOf Sig) * Uᵀ := by
    rw [← hD]
    simp only [Matrix.mul_assoc]
    rw [hUU, Matrix.mul_one, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
  have hQ : ∀ Xm : Matrix (Fin M) (Fin N) ℝ,
      QN Sig Xm = QN (diagonal (specOf Sig)) (Uᵀ * Xm * (1 : Matrix (Fin N) (Fin N) ℝ)ᵀ) := by
    intro Xm
    conv_lhs => rw [QN, hdec]
    rw [QN, transpose_one, Matrix.mul_one, transpose_mul, transpose_transpose]
    simp only [Matrix.mul_assoc]
  have hG : Measurable fun Xm : Matrix (Fin M) (Fin N) ℝ =>
      f (qVecA N (specOf Sig) (QN (diagonal (specOf Sig)) Xm) k l) :=
    hf.comp ((measurable_qVecA N (specOf Sig) N k l).comp (measurable_QN _))
  have hrot := integral_ensemble_eq
    ((gaussX_isGaussianEnsemble M N).rotate hUt (Submonoid.one_mem _)) 
    (gaussX_isGaussianEnsemble M N) hG
  unfold bRef qVec
  simp_rw [hQ]
  exact hrot

/-- `ϖ_1` for the padding matrix `T = tPad 3` (`T Tᵀ` is `6 × 6`) and for `σ ≡ 1` on `Fin 3` agree:
the nonzero values of the two spectra coincide with multiplicity, the dimensions `6` and `3` do
not. -/
example : edgeScale 6 (specOf (tPad 3 * (tPad 3)ᵀ)) 1 = edgeScale 6 (fun _ : Fin 3 => (1 : ℝ)) 1 :=
  congrFun ((nzEq_tPad 3).edgeScale_eq 6) 1

/-- `bRef` of `T Tᵀ` for `T = tPad 3` and of `σ ≡ 1` on `Fin 3` agree, at `N = 6`, `k = 1`, `l = 1`
and the bounded measurable function `v ↦ arctan v₀`. The spectrum of `T Tᵀ` is nonnegative. -/
example :
    bRef 6 (specOf (tPad 3 * (tPad 3)ᵀ)) 1 1 (fun v : Fin 1 → ℝ => Real.arctan (v 0)) =
      bRef 6 (fun _ : Fin 3 => (1 : ℝ)) 1 1 (fun v : Fin 1 → ℝ => Real.arctan (v 0)) := by
  have hH : (tPad 3 * (tPad 3)ᵀ).IsHermitian := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.posSemidef_self_mul_conjTranspose (tPad 3)).isHermitian
  refine bRef_nzEq (nzEq_tPad 3) (fun i => ?_) (fun _ => zero_le_one) 6 1 1
    (Real.continuous_arctan.measurable.comp (measurable_pi_apply 0))
  rw [specOf_eq hH]
  have hP := Matrix.posSemidef_self_mul_conjTranspose (tPad 3)
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hP.eigenvalues_nonneg i

/-- The Gaussian reduction for the non-diagonal positive definite `Σ = [[3/2, 1/2], [1/2, 3/2]]`
(eigenvalues `2` and `1`), `M = 2`, `N = 4`, `k = 1`, `l = 1` and `v ↦ arctan v₀`. -/
example :
    ∫ ω, (fun v : Fin 1 → ℝ => Real.arctan (v 0))
        (qVec (!![(3 / 2 : ℝ), 1 / 2; 1 / 2, 3 / 2]) (gaussX 2 4 ω) 1 1) =
      bRef 4 (specOf (!![(3 / 2 : ℝ), 1 / 2; 1 / 2, 3 / 2])) 1 1
        (fun v : Fin 1 → ℝ => Real.arctan (v 0)) := by
  have hP : (!![(3 / 2 : ℝ), 1 / 2; 1 / 2, 3 / 2]).PosDef := by
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x hx => ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
    · have hx' : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
        by_contra hcon
        rw [not_or, not_not, not_not] at hcon
        exact hx (funext fun i => by fin_cases i <;> simp [hcon.1, hcon.2])
      simp only [dotProduct, Fin.sum_univ_two, Matrix.mulVec, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        star_trivial]
      rcases hx' with h0 | h1
      · nlinarith [sq_pos_of_ne_zero h0, sq_nonneg (x 0 + x 1), sq_nonneg (x 1)]
      · nlinarith [sq_pos_of_ne_zero h1, sq_nonneg (x 0 + x 1), sq_nonneg (x 0)]
  exact bRef_gauss hP 4 1 1 (Real.continuous_arctan.measurable.comp (measurable_pi_apply 0))

end Anisotropic

#print axioms Anisotropic.NzEq.edgeScale_eq
#print axioms Anisotropic.bRef_nzEq
#print axioms Anisotropic.bRef_gauss
