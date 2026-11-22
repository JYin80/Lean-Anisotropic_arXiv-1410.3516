module

public import Anisotropic.Entrywise.Control
public import Anisotropic.LinAlg.ResolventId
public import Anisotropic.LinAlg.ResolventIdDiag

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! # The minor fluctuations `Z^{(S)}_s` and their Möbius expansion over the other labels -/

/-- A set `T ⊆ 𝓘_N` of column labels, as a subset of `𝓘`. -/
def colSet {N : ℕ} (T : Finset (Fin N)) : Finset (Fin M ⊕ Fin N) :=
  T.map Function.Embedding.inr

/-- A set `T ⊆ 𝓘_M` of row labels, as a subset of `𝓘`. -/
def rowSet {N : ℕ} (T : Finset (Fin M)) : Finset (Fin M ⊕ Fin N) :=
  T.map Function.Embedding.inl

/-- `Z^{(S)}_μ = (Xᵀ G^{(Sμ)} X)_{μμ} − N⁻¹ Σ_i G^{(Sμ)}_{ii}` for `S ⊆ 𝓘_N` ((Gmumu_exp) for the
minor `G^{(S)}`). -/
def ZmuS {N : ℕ} (σ : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (S : Finset (Fin N))
    (μ : Fin N) : ℂ :=
  ((Xhat Xm)ᵀ * Gm (diagonal σ) Xm z (colSet (insert μ S)) * Xhat Xm) (Sum.inr μ) (Sum.inr μ)
    - (N : ℂ)⁻¹ * ∑ i, Gm (diagonal σ) Xm z (colSet (insert μ S)) (Sum.inl i) (Sum.inl i)

/-- `Z^{(S)}_i = (X G^{(Si)} Xᵀ)_{ii} − N⁻¹ Σ_ν G^{(Si)}_{νν}` for `S ⊆ 𝓘_M` ((Gii_exp) for the
minor `G^{(S)}`). -/
def ZiS {N : ℕ} (σ : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (S : Finset (Fin M))
    (i : Fin M) : ℂ :=
  (Xhat Xm * Gm (diagonal σ) Xm z (rowSet (insert i S)) * (Xhat Xm)ᵀ) (Sum.inl i) (Sum.inl i)
    - (N : ℂ)⁻¹ * ∑ ν, Gm (diagonal σ) Xm z (rowSet (insert i S)) (Sum.inr ν) (Sum.inr ν)

theorem ZmuS_empty {N : ℕ} (σ : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (μ : Fin N) :
    ZmuS σ Xm z ∅ μ = Zmu σ Xm z μ := by
  have h : colSet (M := M) (insert μ (∅ : Finset (Fin N))) = {Sum.inr μ} := by
    simp [colSet]
  simp only [ZmuS, Zmu, h]

theorem ZiS_empty {N : ℕ} (σ : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (i : Fin M) :
    ZiS σ Xm z ∅ i = Zi σ Xm z i := by
  have h : rowSet (N := N) (insert i (∅ : Finset (Fin M))) = {Sum.inl i} := by
    simp [rowSet]
  simp only [ZiS, Zi, h]

/-- `insert (inr μ) (colSet S) = colSet (insert μ S)`. -/
private theorem insert_inr_colSet {N : ℕ} (S : Finset (Fin N)) (μ : Fin N) :
    insert (Sum.inr μ) (colSet (M := M) S) = colSet (insert μ S) := by
  simp [colSet, Finset.map_insert]

/-- `insert (inl i) (rowSet S) = rowSet (insert i S)`. -/
private theorem insert_inl_rowSet {N : ℕ} (S : Finset (Fin M)) (i : Fin M) :
    insert (Sum.inl i) (rowSet (N := N) S) = rowSet (insert i S) := by
  simp [rowSet, Finset.map_insert]

/-- (Gmumu_exp) for `G^{(S)}`: `1/G^{(S)}_{μμ} = −z − N⁻¹ Σ_i G^{(Sμ)}_{ii} − Z^{(S)}_μ`. -/
theorem ZmuS_schur {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ)
    {z : ℂ} (hz : 0 < z.im) (S : Finset (Fin N)) (μ : Fin N) (hμ : μ ∉ S) :
    1 / Gm (diagonal σ) Xm z (colSet S) (Sum.inr μ) (Sum.inr μ) = -z
      - (N : ℂ)⁻¹ * ∑ i, Gm (diagonal σ) Xm z (colSet (insert μ S)) (Sum.inl i) (Sum.inl i)
      - ZmuS σ Xm z S μ := by
  have hμ' : (Sum.inr μ : Fin M ⊕ Fin N) ∉ colSet S := by simpa [colSet] using hμ
  have h := Gii_minor (posDef_diagonal_iff.2 hσ) Xm hz (colSet S) μ hμ'
  rw [insert_inr_colSet] at h
  rw [h, ZmuS]
  ring

/-- (Gii_exp) for `G^{(S)}`: `1/G^{(S)}_{ii} = −σ_i⁻¹ − N⁻¹ Σ_ν G^{(Si)}_{νν} − Z^{(S)}_i`. -/
theorem ZiS_schur {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ)
    {z : ℂ} (hz : 0 < z.im) (S : Finset (Fin M)) (i : Fin M) (hi : i ∉ S) :
    1 / Gm (diagonal σ) Xm z (rowSet S) (Sum.inl i) (Sum.inl i) = -1 / (σ i : ℂ)
      - (N : ℂ)⁻¹ * ∑ ν, Gm (diagonal σ) Xm z (rowSet (insert i S)) (Sum.inr ν) (Sum.inr ν)
      - ZiS σ Xm z S i := by
  have hi' : (Sum.inl i : Fin M ⊕ Fin N) ∉ rowSet S := by simpa [rowSet] using hi
  have h := Gaa_minor hσ Xm hz (rowSet S) i hi'
  rw [insert_inl_rowSet] at h
  rw [h, ZiS]
  ring

/-- The Möbius piece `F^{[U]}(T) = Σ_{V ⊆ U} (−1)^{|U∖V|} F(T ∖ V)`. -/
def mobPart {α R : Type*} [DecidableEq α] [CommRing R] (F : Finset α → R) (T U : Finset α) : R :=
  ∑ V ∈ U.powerset, (-1) ^ (U.card - V.card) * F (T \ V)

/-- `Σ_{W ⊆ A} (−1)^{|W|} = [A = ∅]` in any commutative ring. -/
private theorem sum_powerset_neg_one_pow_ring {α R : Type*} [DecidableEq α] [CommRing R]
    (A : Finset α) :
    ∑ W ∈ A.powerset, (-1 : R) ^ W.card = if A = ∅ then 1 else 0 := by
  have h := congrArg (Int.castRingHom R) (Finset.sum_powerset_neg_one_pow_card (x := A))
  simp only [map_sum, map_pow, map_neg, map_one] at h
  rw [h]
  split_ifs <;> simp

/-- For `V ⊆ T`: `Σ_{V ⊆ U ⊆ T} (−1)^{|U|−|V|} = [V = T]`. -/
private theorem sum_Icc_neg_one_pow {α R : Type*} [DecidableEq α] [CommRing R]
    {V T : Finset α} (hV : V ⊆ T) :
    ∑ U ∈ T.powerset.filter (fun U => V ⊆ U), (-1 : R) ^ (U.card - V.card)
      = if V = T then 1 else 0 := by
  have h1 : ∑ U ∈ T.powerset.filter (fun U => V ⊆ U), (-1 : R) ^ (U.card - V.card)
      = ∑ W ∈ (T \ V).powerset, (-1 : R) ^ W.card := by
    refine Finset.sum_nbij' (fun U => U \ V) (fun W => W ∪ V) ?_ ?_ ?_ ?_ ?_
    · intro U hU
      simp only [Finset.mem_filter, Finset.mem_powerset] at hU ⊢
      exact Finset.sdiff_subset_sdiff hU.1 le_rfl
    · intro W hW
      simp only [Finset.mem_filter, Finset.mem_powerset] at hW ⊢
      refine ⟨Finset.union_subset ((hW.trans Finset.sdiff_subset)) hV, Finset.subset_union_right⟩
    · intro U hU
      simp only [Finset.mem_filter, Finset.mem_powerset] at hU
      exact Finset.sdiff_union_of_subset hU.2
    · intro W hW
      simp only [Finset.mem_powerset] at hW
      have : Disjoint W V := Finset.disjoint_of_subset_left hW Finset.sdiff_disjoint
      exact Finset.union_sdiff_cancel_right this
    · intro U hU
      simp only [Finset.mem_filter, Finset.mem_powerset] at hU
      rw [Finset.card_sdiff_of_subset hU.2]
  rw [h1, sum_powerset_neg_one_pow_ring]
  have h2 : T \ V = ∅ ↔ V = T := by
    rw [Finset.sdiff_eq_empty_iff_subset]
    exact ⟨fun h => Finset.Subset.antisymm hV h, fun h => h ▸ le_rfl⟩
  simp only [h2]

/-- Möbius inversion on the subsets of `T`: `Σ_{U ⊆ T} F^{[U]}(T) = F(∅)`. -/
theorem sum_mobPart {α R : Type*} [DecidableEq α] [CommRing R] (F : Finset α → R)
    (T : Finset α) : ∑ U ∈ T.powerset, mobPart F T U = F ∅ := by
  unfold mobPart
  rw [Finset.sum_comm' (t' := T.powerset) (s' := fun V => T.powerset.filter (fun U => V ⊆ U))]
  · have : ∀ V ∈ T.powerset,
        ∑ U ∈ T.powerset.filter (fun U => V ⊆ U), (-1 : R) ^ (U.card - V.card) * F (T \ V)
          = (if V = T then 1 else 0) * F (T \ V) := by
      intro V hV
      rw [← Finset.sum_mul, sum_Icc_neg_one_pow (Finset.mem_powerset.1 hV)]
    rw [Finset.sum_congr rfl this]
    rw [Finset.sum_eq_single T]
    · simp
    · intro V _ hne
      simp [hne]
    · intro h
      exact absurd (Finset.mem_powerset.2 le_rfl) h
  · intro U V
    simp only [Finset.mem_powerset, Finset.mem_filter]
    constructor
    · rintro ⟨hU, hVU⟩
      exact ⟨⟨hU, hVU⟩, hVU.trans hU⟩
    · rintro ⟨⟨hU, hVU⟩, _⟩
      exact ⟨hU, hVU⟩

theorem mobPart_empty {α R : Type*} [DecidableEq α] [CommRing R] (F : Finset α → R)
    (T : Finset α) : mobPart F T ∅ = F T := by
  simp [mobPart]

/-- `Z^{[U]}_μ` relative to the set `T` of the other column labels. -/
def ZmuMob {N : ℕ} (σ : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (T U : Finset (Fin N)) (μ : Fin N) : ℂ :=
  mobPart (fun S => ZmuS σ Xm z S μ) T U

/-- `Z^{[U]}_i` relative to the set `T` of the other row labels. -/
def ZiMob {N : ℕ} (σ : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (T U : Finset (Fin M)) (i : Fin M) : ℂ :=
  mobPart (fun S => ZiS σ Xm z S i) T U

/-- `G^{(S)}` depends only on the entries `X_{iν}` with `i ∉ S`, `ν ∉ S`. -/
theorem Gm_congr {N : ℕ} (σ : Fin M → ℝ) (z : ℂ) (S : Finset (Fin M ⊕ Fin N))
    {Xm Xm' : Matrix (Fin M) (Fin N) ℝ}
    (h : ∀ i ν, Sum.inl i ∉ S → Sum.inr ν ∉ S → Xm i ν = Xm' i ν) :
    Gm (diagonal σ) Xm z S = Gm (diagonal σ) Xm' z S := by
  rw [Gm_eq_extend, Gm_eq_extend]
  have : Xm.submatrix (Subtype.val : idxM S → Fin M) (Subtype.val : idxN S → Fin N)
      = Xm'.submatrix (Subtype.val : idxM S → Fin M) (Subtype.val : idxN S → Fin N) := by
    ext ⟨i, hi⟩ ⟨ν, hν⟩
    exact h i ν hi hν
  rw [this]

/-- The quadratic form `(X̂ᵀ B X̂)_{μμ}` depends only on column `μ` of `X` and on `B`. -/
private theorem Xhat_quad_inr {N : ℕ} (Xm Xm' : Matrix (Fin M) (Fin N) ℝ) (μ : Fin N)
    (B : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) (h : ∀ i, Xm i μ = Xm' i μ) :
    ((Xhat Xm)ᵀ * B * Xhat Xm) (Sum.inr μ) (Sum.inr μ)
      = ((Xhat Xm')ᵀ * B * Xhat Xm') (Sum.inr μ) (Sum.inr μ) := by
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.transpose_apply, Xhat, cplx,
    Matrix.fromBlocks, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply,
    Matrix.map_apply, h]

/-- The quadratic form `(X̂ B X̂ᵀ)_{ii}` depends only on row `i` of `X` and on `B`. -/
private theorem Xhat_quad_inl {N : ℕ} (Xm Xm' : Matrix (Fin M) (Fin N) ℝ) (i : Fin M)
    (B : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) (h : ∀ ν, Xm i ν = Xm' i ν) :
    (Xhat Xm * B * (Xhat Xm)ᵀ) (Sum.inl i) (Sum.inl i)
      = (Xhat Xm' * B * (Xhat Xm')ᵀ) (Sum.inl i) (Sum.inl i) := by
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.transpose_apply, Xhat, cplx,
    Matrix.fromBlocks, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply,
    Matrix.map_apply, h]

/-- (α): for `μ ∉ T`, `Z^{[U]}_μ` depends only on the columns outside `T ∖ U`. -/
theorem ZmuMob_congr {N : ℕ} (σ : Fin M → ℝ) (z : ℂ) (T U : Finset (Fin N)) (μ : Fin N)
    (hμ : μ ∉ T) {Xm Xm' : Matrix (Fin M) (Fin N) ℝ}
    (h : ∀ i ν, ν ∉ T \ U → Xm i ν = Xm' i ν) :
    ZmuMob σ Xm z T U μ = ZmuMob σ Xm' z T U μ := by
  unfold ZmuMob mobPart
  refine Finset.sum_congr rfl fun V hV => ?_
  have hVU : V ⊆ U := Finset.mem_powerset.1 hV
  have hG : Gm (diagonal σ) Xm z (colSet (insert μ (T \ V)))
      = Gm (diagonal σ) Xm' z (colSet (insert μ (T \ V))) := by
    refine Gm_congr σ z _ fun i ν _ hν => h i ν ?_
    have hν' : ν ∉ insert μ (T \ V) := by simpa [colSet] using hν
    intro hmem
    apply hν'
    rw [Finset.mem_sdiff] at hmem
    exact Finset.mem_insert_of_mem (Finset.mem_sdiff.2 ⟨hmem.1, fun hv => hmem.2 (hVU hv)⟩)
  have hμ' : μ ∉ T \ U := fun hm => hμ (Finset.mem_sdiff.1 hm).1
  simp only [ZmuS]
  rw [hG, Xhat_quad_inr Xm Xm' μ _ fun i => h i μ hμ']

/-- (α): for `i ∉ T`, `Z^{[U]}_i` depends only on the rows outside `T ∖ U`. -/
theorem ZiMob_congr {N : ℕ} (σ : Fin M → ℝ) (z : ℂ) (T U : Finset (Fin M)) (i : Fin M)
    (hi : i ∉ T) {Xm Xm' : Matrix (Fin M) (Fin N) ℝ}
    (h : ∀ j ν, j ∉ T \ U → Xm j ν = Xm' j ν) :
    ZiMob σ Xm z T U i = ZiMob σ Xm' z T U i := by
  unfold ZiMob mobPart
  refine Finset.sum_congr rfl fun V hV => ?_
  have hVU : V ⊆ U := Finset.mem_powerset.1 hV
  have hG : Gm (diagonal σ) Xm z (rowSet (insert i (T \ V)))
      = Gm (diagonal σ) Xm' z (rowSet (insert i (T \ V))) := by
    refine Gm_congr σ z _ fun j ν hj _ => h j ν ?_
    have hj' : j ∉ insert i (T \ V) := by simpa [rowSet] using hj
    intro hmem
    apply hj'
    rw [Finset.mem_sdiff] at hmem
    exact Finset.mem_insert_of_mem (Finset.mem_sdiff.2 ⟨hmem.1, fun hv => hmem.2 (hVU hv)⟩)
  have hi' : i ∉ T \ U := fun hm => hi (Finset.mem_sdiff.1 hm).1
  simp only [ZiS]
  rw [hG, Xhat_quad_inl Xm Xm' i _ fun ν => h i ν hi']

example : ∑ U ∈ (Finset.univ : Finset (Fin 2)).powerset,
    mobPart (fun S : Finset (Fin 2) => ((S.card : ℤ) ^ 2 + 3 * S.card + 5)) Finset.univ U = 5 := by
  decide

example : colSet (M := 2) ({0} : Finset (Fin 2)) = {Sum.inr 0} := by decide

/-! ## Checks at the Rademacher instance `M = N = 2`, `σ ≡ 1`, `z = 2i` -/

section Checks

end Checks

end Anisotropic
