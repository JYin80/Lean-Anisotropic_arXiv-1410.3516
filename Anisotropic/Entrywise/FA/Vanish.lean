module

public import Anisotropic.Entrywise.FA.Bounds
public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.Entrywise.Indep
public import Anisotropic.Probability.LDE.Conditional
public import Anisotropic.Framework.DominationUnion

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! # The vanishing lemma (`E_s`-annihilation through product laws), the conditional LDE for `Z^{(S)}_s`, and the good event `FaGood` -/

/-! ## Second moments of a row family -/

/-- `x_i x_j` is integrable for a row family with `N ≥ 1`. -/
private theorem vanish_integrable_mul {Ω : Type*} [MeasureSpace Ω] {C : ℕ → ℝ} {N : ℕ}
    {ι : Type*} {x : ι → Ω → ℝ} (hN : 1 ≤ N) (hx : RowAssumption C N x) (i j : ι) :
    Integrable (fun ω => x i ω * x j ω) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsq : ∀ k, Integrable fun ω => x k ω ^ 2 := by
    intro k
    have h := (hx.integrable_moment 2 k).div_const (N : ℝ)
    refine h.congr (Eventually.of_forall fun ω => ?_)
    simp only [mul_pow, sq_abs, Real.sq_sqrt hNpos.le]
    field_simp
  refine ((hsq i).add (hsq j)).mono' ((hx.measurable i).mul (hx.measurable j)).aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul, Pi.add_apply]
  nlinarith [sq_abs (x i ω), sq_abs (x j ω), sq_nonneg (|x i ω| - |x j ω|)]

/-- `E[x_i x_j] = δ_{ij}/N` for a row family. -/
private theorem vanish_integral_mul {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {C : ℕ → ℝ} {N : ℕ} {ι : Type*} {x : ι → Ω → ℝ}
    (hx : RowAssumption C N x) (i j : ι) :
    ∫ ω, x i ω * x j ω = if i = j then 1 / (N : ℝ) else 0 := by
  split_ifs with h
  · subst h
    simp_rw [← sq]
    exact hx.var i
  · rw [(hx.indep.indepFun h).integral_fun_mul_eq_mul_integral
      (hx.measurable i).aestronglyMeasurable (hx.measurable j).aestronglyMeasurable, hx.mean i,
      zero_mul]

/-! ## The vanishing lemma -/

/-- (c), the vanishing lemma: for a family `x` with the entry conditions (a column or a row of
`X`) and `Y` independent of `x`,
`E[(Σ_{i,j} x_i A_{ij}(Y) x_j − N⁻¹ Σ_i A_{ii}(Y)) F(Y)] = 0`. -/
theorem integral_quadForm_mul_eq_zero {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {C : ℕ → ℝ} {N : ℕ} {ι β : Type*} [Fintype ι]
    [MeasurableSpace β] (x : ι → Ω → ℝ) (Y : Ω → β) (A : β → ι → ι → ℂ) (F : β → ℂ)
    (hN : 1 ≤ N) (hx : RowAssumption C N x) (hY : Measurable Y) (hA : ∀ i j, Measurable fun b => A b i j)
    (hF : Measurable F) (hind : IndepFun (fun ω i => x i ω) Y ℙ)
    (hint : ∀ i j, Integrable (fun ω => A (Y ω) i j * F (Y ω))) :
    ∫ ω, ((∑ i, ∑ j, (x i ω : ℂ) * A (Y ω) i j * x j ω) - (N : ℂ)⁻¹ * ∑ i, A (Y ω) i i) *
      F (Y ω) = 0 := by
  set g : ι → ι → Ω → ℂ := fun i j ω => A (Y ω) i j * F (Y ω) with hg
  have hc : ∀ i j, Integrable (fun ω => ((x i ω * x j ω : ℝ) : ℂ)) :=
    fun i j => (vanish_integrable_mul hN hx i j).ofReal
  have hindij : ∀ i j, IndepFun (fun ω => ((x i ω * x j ω : ℝ) : ℂ)) (g i j) ℙ := by
    intro i j
    have hφ : Measurable fun v : ι → ℝ => ((v i * v j : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp ((measurable_pi_apply i).mul (measurable_pi_apply j))
    exact hind.comp hφ ((hA i j).mul hF)
  have hint2 : ∀ i j, Integrable fun ω => ((x i ω * x j ω : ℝ) : ℂ) * g i j ω :=
    fun i j => (hindij i j).integrable_mul (hc i j) (hint i j)
  have hterm : ∀ i j, ∫ ω, ((x i ω * x j ω : ℝ) : ℂ) * g i j ω
      = (if i = j then (N : ℂ)⁻¹ else 0) * ∫ ω, g i j ω := by
    intro i j
    rw [(hindij i j).integral_fun_mul_eq_mul_integral (hc i j).aestronglyMeasurable
      (hint i j).aestronglyMeasurable, integral_complex_ofReal, vanish_integral_mul hx i j]
    split_ifs <;> simp
  have hpt : ∀ ω, ((∑ i, ∑ j, (x i ω : ℂ) * A (Y ω) i j * x j ω)
      - (N : ℂ)⁻¹ * ∑ i, A (Y ω) i i) * F (Y ω)
      = (∑ i, ∑ j, ((x i ω * x j ω : ℝ) : ℂ) * g i j ω) - (N : ℂ)⁻¹ * ∑ i, g i i ω := by
    intro ω
    simp only [hg, sub_mul, Finset.sum_mul, Finset.mul_sum, Complex.ofReal_mul]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    · refine Finset.sum_congr rfl fun i _ => ?_
      ring
  simp_rw [hpt]
  rw [integral_sub (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    hint2 i j) ((integrable_finsetSum _ fun i _ => hint i i).const_mul _),
    integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint2 i j,
    integral_const_mul, integral_finsetSum _ fun i _ => hint i i]
  rw [sub_eq_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hint2 i j]
  simp_rw [hterm]
  simp [hg]

/-! ## Independence of a column or a row from the rest of the matrix -/

/-- Column `μ` of `X` is independent of the family of the entries outside column `μ`. -/
theorem indepFun_col_rest {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {C : ℕ → ℝ} {K N : ℕ} {X : Ω → Matrix (Fin K) (Fin N) ℝ} (hX : EntryAssumption C X)
    (μ : Fin N) :
    IndepFun (fun ω (i : Fin K) => X ω i μ)
      (fun ω (q : {q : Fin K × Fin N // q.2 ≠ μ}) => X ω q.1.1 q.1.2) ℙ := by
  set P : Finset (Fin K × Fin N) := Finset.univ.filter (fun q => q.2 = μ) with hP
  set Q : Finset (Fin K × Fin N) := Finset.univ.filter (fun q => q.2 ≠ μ) with hQ
  have hdisj : Disjoint P Q := by
    rw [hP, hQ, Finset.disjoint_filter]
    intro q _ h h'
    exact h' h
  have h := hX.indep.indepFun_finset P Q hdisj (fun q => hX.measurable q.1 q.2)
  have hφ : Measurable fun (y : P → ℝ) (i : Fin K) => y ⟨(i, μ), by simp [hP]⟩ :=
    Measurable.of_eval fun i => measurable_pi_apply _
  have hψ : Measurable fun (y : Q → ℝ) (q : {q : Fin K × Fin N // q.2 ≠ μ}) =>
      y ⟨q.1, by simp [hQ, q.2]⟩ :=
    Measurable.of_eval fun q => measurable_pi_apply _
  exact h.comp hφ hψ

/-- Row `i` of `X` is independent of the family of the entries outside row `i`. -/
theorem indepFun_row_rest {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {C : ℕ → ℝ} {K N : ℕ} {X : Ω → Matrix (Fin K) (Fin N) ℝ} (hX : EntryAssumption C X)
    (i : Fin K) :
    IndepFun (fun ω (ν : Fin N) => X ω i ν)
      (fun ω (q : {q : Fin K × Fin N // q.1 ≠ i}) => X ω q.1.1 q.1.2) ℙ := by
  set P : Finset (Fin K × Fin N) := Finset.univ.filter (fun q => q.1 = i) with hP
  set Q : Finset (Fin K × Fin N) := Finset.univ.filter (fun q => q.1 ≠ i) with hQ
  have hdisj : Disjoint P Q := by
    rw [hP, hQ, Finset.disjoint_filter]
    intro q _ h h'
    exact h' h
  have h := hX.indep.indepFun_finset P Q hdisj (fun q => hX.measurable q.1 q.2)
  have hφ : Measurable fun (y : P → ℝ) (ν : Fin N) => y ⟨(i, ν), by simp [hP]⟩ :=
    Measurable.of_eval fun ν => measurable_pi_apply _
  have hψ : Measurable fun (y : Q → ℝ) (q : {q : Fin K × Fin N // q.1 ≠ i}) =>
      y ⟨q.1, by simp [hQ, q.2]⟩ :=
    Measurable.of_eval fun q => measurable_pi_apply _
  exact h.comp hφ hψ

/-! ## Deterministic facts on `Z^{(S)}_s` and the minors -/

/-- (opbound) for an entry of the minor `G^{(T)}` (zero-extended), `Im z > 0`:
`|G^{(T)}_{st}| ≤ (1+5|z|)η⁻¹ (1 + Σ_i σ_i)`. -/
private theorem vanish_Gm_entry_le {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (T : Finset (Fin M ⊕ Fin N))
    (s t : Fin M ⊕ Fin N) :
    ‖Gm (diagonal σ) Xm z T s t‖ ≤ (1 + 5 * ‖z‖) / z.im * (1 + ∑ i, σ i) := by
  have hσsum : 0 ≤ ∑ i, σ i := Finset.sum_nonneg fun i _ => (hσ i).le
  have hB : 0 ≤ (1 + 5 * ‖z‖) / z.im * (1 + ∑ i, σ i) := by positivity
  rw [Gm_eq_extend_G_of_diagonal σ (fun i => (hσ i).ne') Xm z T]
  unfold extend
  split_ifs with hs ht
  · simpa using hB
  · simpa using hB
  · set Sig' := (diagonal σ).submatrix (Subtype.val : idxM T → Fin M)
      (Subtype.val : idxM T → Fin M) with hSig'def
    have hSig' : Sig'.PosDef := by
      rw [hSig'def, submatrix_diagonal _ _ Subtype.val_injective]
      exact posDef_diagonal_iff.2 fun i => hσ _
    have hw : ∀ u : idxM T ⊕ idxN T,
        eI u ⬝ᵥ SigU (n := idxN T) Sig' *ᵥ eI u ≤ 1 + ∑ i, σ i := by
      intro u
      have he : eI u ⬝ᵥ SigU (n := idxN T) Sig' *ᵥ eI u = SigU (n := idxN T) Sig' u u := by
        simp [eI, dotProduct, mulVec, Pi.single_apply]
      rw [he]
      rcases u with u | u
      · simp only [SigU, fromBlocks_apply₁₁, hSig'def, submatrix_apply, diagonal_apply_eq]
        have := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => (hσ i).le)
          (Finset.mem_univ u.1)
        linarith
      · simp only [SigU, fromBlocks_apply₂₂, one_apply_eq]
        linarith
    have hw0 : ∀ u : idxM T ⊕ idxN T, 0 ≤ eI u ⬝ᵥ SigU (n := idxN T) Sig' *ᵥ eI u := by
      intro u
      have he : eI u ⬝ᵥ SigU (n := idxN T) Sig' *ᵥ eI u = SigU (n := idxN T) Sig' u u := by
        simp [eI, dotProduct, mulVec, Pi.single_apply]
      rw [he]
      rcases u with u | u
      · simp only [SigU, fromBlocks_apply₁₁, hSig'def, submatrix_apply, diagonal_apply_eq]
        exact (hσ _).le
      · simp only [SigU, fromBlocks_apply₂₂, one_apply_eq]
        exact zero_le_one
    rw [← ent_eI_eI (G Sig' (Xm.submatrix (Subtype.val : idxM T → Fin M)
      (Subtype.val : idxN T → Fin N)) z) (toSub T s hs) (toSub T t ht)]
    refine (opbound hSig' _ hz _ _).trans ?_
    have hK : 0 ≤ (1 + 5 * ‖z‖) / z.im := by positivity
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hK
    calc Real.sqrt (eI (toSub T s hs) ⬝ᵥ SigU (n := idxN T) Sig' *ᵥ eI (toSub T s hs))
          * Real.sqrt (eI (toSub T t ht) ⬝ᵥ SigU (n := idxN T) Sig' *ᵥ eI (toSub T t ht))
        ≤ Real.sqrt (1 + ∑ i, σ i) * Real.sqrt (1 + ∑ i, σ i) :=
          mul_le_mul (Real.sqrt_le_sqrt (hw _)) (Real.sqrt_le_sqrt (hw _))
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = 1 + ∑ i, σ i := Real.mul_self_sqrt (by positivity)

/-- `Z^{(S)}_μ = Σ_{i,j} X_{iμ} G^{(Sμ)}_{ij} X_{jμ} − N⁻¹ Σ_i G^{(Sμ)}_{ii}`. -/
private theorem vanish_ZmuS_eq {N : ℕ} (σ : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (S : Finset (Fin N)) (μ : Fin N) :
    ZmuS σ Xm z S μ = (∑ i, ∑ j, (Xm i μ : ℂ) *
        Gm (diagonal σ) Xm z (colSet (insert μ S)) (Sum.inl i) (Sum.inl j) * Xm j μ)
      - (N : ℂ)⁻¹ * ∑ i, Gm (diagonal σ) Xm z (colSet (insert μ S)) (Sum.inl i) (Sum.inl i) := by
  unfold ZmuS
  congr 1
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.transpose_apply, Xhat, cplx,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.map_apply,
    zero_mul, mul_zero, Finset.sum_const_zero, add_zero, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

/-- `Z^{(S)}_i = Σ_{ν,ν'} X_{iν} G^{(Si)}_{νν'} X_{iν'} − N⁻¹ Σ_ν G^{(Si)}_{νν}`. -/
private theorem vanish_ZiS_eq {N : ℕ} (σ : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (S : Finset (Fin M)) (i : Fin M) :
    ZiS σ Xm z S i = (∑ ν, ∑ ν', (Xm i ν : ℂ) *
        Gm (diagonal σ) Xm z (rowSet (insert i S)) (Sum.inr ν) (Sum.inr ν') * Xm i ν')
      - (N : ℂ)⁻¹ * ∑ ν, Gm (diagonal σ) Xm z (rowSet (insert i S)) (Sum.inr ν) (Sum.inr ν) := by
  unfold ZiS
  congr 1
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.transpose_apply, Xhat, cplx,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, Matrix.map_apply,
    zero_mul, mul_zero, Finset.sum_const_zero, zero_add, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

/-! ## Vanishing for `Z^{(S)}_μ` and `Z^{(S)}_i` -/

/-- The matrix with column `μ` equal to `0` and the other entries taken from `b`. -/
private def vanishFillCol {N : ℕ} (μ : Fin N) (b : {q : Fin M × Fin N // q.2 ≠ μ} → ℝ) :
    Matrix (Fin M) (Fin N) ℝ :=
  fun i ν => if h : ν = μ then 0 else b ⟨(i, ν), h⟩

/-- The matrix with row `i` equal to `0` and the other entries taken from `b`. -/
private def vanishFillRow {N : ℕ} (i : Fin M) (b : {q : Fin M × Fin N // q.1 ≠ i} → ℝ) :
    Matrix (Fin M) (Fin N) ℝ :=
  fun j ν => if h : j = i then 0 else b ⟨(j, ν), h⟩

private theorem measurable_vanishFillCol {N : ℕ} (μ : Fin N) (i : Fin M) (ν : Fin N) :
    Measurable fun b : {q : Fin M × Fin N // q.2 ≠ μ} → ℝ => vanishFillCol μ b i ν := by
  unfold vanishFillCol
  by_cases h : ν = μ
  · simp only [h, dite_true]
    exact measurable_const
  · simp only [h, dite_false]
    exact measurable_pi_apply _

private theorem measurable_vanishFillRow {N : ℕ} (i : Fin M) (j : Fin M) (ν : Fin N) :
    Measurable fun b : {q : Fin M × Fin N // q.1 ≠ i} → ℝ => vanishFillRow i b j ν := by
  unfold vanishFillRow
  by_cases h : j = i
  · simp only [h, dite_true]
    exact measurable_const
  · simp only [h, dite_false]
    exact measurable_pi_apply _

/-- (c) for column labels: if `F` does not depend on column `μ`, then `E[Z^{(S)}_μ F(X)] = 0`. -/
theorem integral_ZmuS_mul_eq_zero {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {τ : ℝ} {C : ℕ → ℝ} {N : ℕ} {σ : Fin M → ℝ}
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : DiagModel τ C M N σ X) {z : ℂ} (hz : 0 < z.im)
    (S : Finset (Fin N)) (μ : Fin N) (F : (Fin M → Fin N → ℝ) → ℂ) (hFm : Measurable F)
    (hF : ∀ Xm Xm' : Fin M → Fin N → ℝ, (∀ i ν, ν ≠ μ → Xm i ν = Xm' i ν) → F Xm = F Xm')
    (hint : Integrable (fun ω => F (X ω))) :
    ∫ ω, ZmuS σ (X ω) z S μ * F (X ω) = 0 := by
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.2 fun h => by subst h; exact μ.elim0
  set T : Finset (Fin M ⊕ Fin N) := colSet (insert μ S) with hT
  set Y : Ω → ({q : Fin M × Fin N // q.2 ≠ μ} → ℝ) := fun ω q => X ω q.1.1 q.1.2 with hYdef
  have hYm : Measurable Y := Measurable.of_eval fun q => hX.entries.measurable q.1.1 q.1.2
  have hfill : ∀ ω i ν, ν ≠ μ → vanishFillCol μ (Y ω) i ν = X ω i ν := by
    intro ω i ν h
    simp [vanishFillCol, h, hYdef]
  have hG : ∀ ω, Gm (diagonal σ) (vanishFillCol μ (Y ω)) z T = Gm (diagonal σ) (X ω) z T := by
    intro ω
    refine Gm_congr σ z T fun i ν _ hν => hfill ω i ν ?_
    rintro rfl
    exact hν (by simp [hT, colSet])
  have hFY : ∀ ω, F (vanishFillCol μ (Y ω)) = F (X ω) :=
    fun ω => hF _ _ fun i ν h => hfill ω i ν h
  have hA : ∀ i j, Measurable fun b : {q : Fin M × Fin N // q.2 ≠ μ} → ℝ =>
      Gm (diagonal σ) (vanishFillCol μ b) z T (Sum.inl i) (Sum.inl j) :=
    fun i j => measurable_Gm_apply σ (measurable_vanishFillCol μ) z T _ _
  have hFm' : Measurable fun b : {q : Fin M × Fin N // q.2 ≠ μ} → ℝ => F (vanishFillCol μ b) :=
    hFm.comp (Measurable.of_eval fun i =>
      Measurable.of_eval fun ν => measurable_vanishFillCol μ i ν)
  have hint' : ∀ i j, Integrable fun ω =>
      Gm (diagonal σ) (vanishFillCol μ (Y ω)) z T (Sum.inl i) (Sum.inl j) *
        F (vanishFillCol μ (Y ω)) := by
    intro i j
    simp_rw [hG, hFY]
    exact hint.bdd_mul
      (measurable_Gm_apply σ hX.entries.measurable z T _ _).aestronglyMeasurable
      (ae_of_all _ fun ω => vanish_Gm_entry_le hX.pos (X ω) hz T _ _)
  have key := integral_quadForm_mul_eq_zero (fun i ω => X ω i μ) Y
    (fun b i j => Gm (diagonal σ) (vanishFillCol μ b) z T (Sum.inl i) (Sum.inl j))
    (fun b => F (vanishFillCol μ b)) hN (hX.entries.col μ) hYm hA hFm'
    (indepFun_col_rest hX.entries μ) hint'
  rw [← key]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  simp only [hG, hFY]
  rw [vanish_ZmuS_eq]

/-- `N ≥ 1` under `DiagModel` once an index `i : Fin M` exists. -/
private theorem vanish_one_le_N {τ : ℝ} {C : ℕ → ℝ} {N : ℕ} {σ : Fin M → ℝ} {Ω : Type*}
    [MeasureSpace Ω] {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : DiagModel τ C M N σ X)
    (i : Fin M) : 1 ≤ N := by
  have hτ : 0 < τ := inv_pos.1 ((hX.pos i).trans_le (hX.le i))
  refine Nat.one_le_iff_ne_zero.2 fun h => ?_
  have h0 := hX.ratio_ge
  rw [h, Nat.cast_zero, div_zero] at h0
  linarith

/-- (c) for row labels: if `F` does not depend on row `i`, then `E[Z^{(S)}_i F(X)] = 0`. -/
theorem integral_ZiS_mul_eq_zero {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {τ : ℝ} {C : ℕ → ℝ} {N : ℕ} {σ : Fin M → ℝ}
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : DiagModel τ C M N σ X) {z : ℂ} (hz : 0 < z.im)
    (S : Finset (Fin M)) (i : Fin M) (F : (Fin M → Fin N → ℝ) → ℂ) (hFm : Measurable F)
    (hF : ∀ Xm Xm' : Fin M → Fin N → ℝ, (∀ j ν, j ≠ i → Xm j ν = Xm' j ν) → F Xm = F Xm')
    (hint : Integrable (fun ω => F (X ω))) :
    ∫ ω, ZiS σ (X ω) z S i * F (X ω) = 0 := by
  have hN : 1 ≤ N := vanish_one_le_N hX i
  set T : Finset (Fin M ⊕ Fin N) := rowSet (insert i S) with hT
  set Y : Ω → ({q : Fin M × Fin N // q.1 ≠ i} → ℝ) := fun ω q => X ω q.1.1 q.1.2 with hYdef
  have hYm : Measurable Y := Measurable.of_eval fun q => hX.entries.measurable q.1.1 q.1.2
  have hfill : ∀ ω j ν, j ≠ i → vanishFillRow i (Y ω) j ν = X ω j ν := by
    intro ω j ν h
    simp [vanishFillRow, h, hYdef]
  have hG : ∀ ω, Gm (diagonal σ) (vanishFillRow i (Y ω)) z T = Gm (diagonal σ) (X ω) z T := by
    intro ω
    refine Gm_congr σ z T fun j ν hj _ => hfill ω j ν ?_
    rintro rfl
    exact hj (by simp [hT, rowSet])
  have hFY : ∀ ω, F (vanishFillRow i (Y ω)) = F (X ω) :=
    fun ω => hF _ _ fun j ν h => hfill ω j ν h
  have hA : ∀ ν ν', Measurable fun b : {q : Fin M × Fin N // q.1 ≠ i} → ℝ =>
      Gm (diagonal σ) (vanishFillRow i b) z T (Sum.inr ν) (Sum.inr ν') :=
    fun ν ν' => measurable_Gm_apply σ (measurable_vanishFillRow i) z T _ _
  have hFm' : Measurable fun b : {q : Fin M × Fin N // q.1 ≠ i} → ℝ => F (vanishFillRow i b) :=
    hFm.comp (Measurable.of_eval fun j =>
      Measurable.of_eval fun ν => measurable_vanishFillRow i j ν)
  have hint' : ∀ ν ν', Integrable fun ω =>
      Gm (diagonal σ) (vanishFillRow i (Y ω)) z T (Sum.inr ν) (Sum.inr ν') *
        F (vanishFillRow i (Y ω)) := by
    intro ν ν'
    simp_rw [hG, hFY]
    exact hint.bdd_mul
      (measurable_Gm_apply σ hX.entries.measurable z T _ _).aestronglyMeasurable
      (ae_of_all _ fun ω => vanish_Gm_entry_le hX.pos (X ω) hz T _ _)
  have key := integral_quadForm_mul_eq_zero (fun ν ω => X ω i ν) Y
    (fun b ν ν' => Gm (diagonal σ) (vanishFillRow i b) z T (Sum.inr ν) (Sum.inr ν'))
    (fun b => F (vanishFillRow i b)) hN (hX.entries.row i) hYm hA hFm'
    (indepFun_row_rest hX.entries i) hint'
  rw [← key]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  simp only [hG, hFY]
  rw [vanish_ZiS_eq]

/-! ## Moments of `|x_μ|²` and `|x_i|²` -/

/-- For a row family `y` on `Fin K`, `K, N ≥ 1`: `E(Σ_k y_k²)^q ≤ (K/N)^q C_{2q}`. -/
private theorem vanish_sum_sq_moment {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {C : ℕ → ℝ} {N K : ℕ} {y : Fin K → Ω → ℝ}
    (hN : 1 ≤ N) (hK : 1 ≤ K) (hy : RowAssumption C N y) (q : ℕ) :
    Integrable (fun ω => (∑ k, y k ω ^ 2) ^ q) ∧
      ∫ ω, (∑ k, y k ω ^ 2) ^ q ≤ ((K : ℝ) / N) ^ q * C (2 * q) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have k0 : Fin K := ⟨0, hK⟩
  rcases q with _ | n
  · refine ⟨by simp, ?_⟩
    have h := hy.moment 0 k0
    simp only [pow_zero, integral_const, smul_eq_mul, mul_one, probReal_univ] at h ⊢
    simpa using h
  · set m : Fin K → Ω → ℝ := fun k ω => |Real.sqrt N * y k ω| ^ (2 * (n + 1)) with hm
    have hmi : ∀ k, Integrable (m k) := fun k => hy.integrable_moment _ k
    have hmy : ∀ k ω, (y k ω ^ 2) ^ (n + 1) = m k ω / (N : ℝ) ^ (n + 1) := by
      intro k ω
      simp only [hm]
      rw [pow_mul, sq_abs, mul_pow, Real.sq_sqrt hNpos.le, mul_pow]
      field_simp
    have hpt : ∀ ω, (∑ k, y k ω ^ 2) ^ (n + 1)
        ≤ (K : ℝ) ^ n / (N : ℝ) ^ (n + 1) * ∑ k, m k ω := by
      intro ω
      have h := pow_sum_le_card_mul_sum_pow (s := Finset.univ) (f := fun k => y k ω ^ 2)
        (fun k _ => sq_nonneg _) n
      simp only [Finset.card_univ, Fintype.card_fin, hmy] at h
      rw [← Finset.sum_div] at h
      calc _ ≤ _ := h
        _ = _ := by ring
    have hbd : Integrable fun ω => (K : ℝ) ^ n / (N : ℝ) ^ (n + 1) * ∑ k, m k ω :=
      (integrable_finsetSum _ fun k _ => hmi k).const_mul _
    have hmeas : Measurable fun ω => (∑ k, y k ω ^ 2) ^ (n + 1) :=
      (Finset.measurable_sum _ fun k _ => (hy.measurable k).pow_const 2).pow_const _
    have hint : Integrable fun ω => (∑ k, y k ω ^ 2) ^ (n + 1) :=
      hbd.mono' hmeas.aestronglyMeasurable (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact hpt ω)
    refine ⟨hint, ?_⟩
    calc ∫ ω, (∑ k, y k ω ^ 2) ^ (n + 1)
        ≤ ∫ ω, (K : ℝ) ^ n / (N : ℝ) ^ (n + 1) * ∑ k, m k ω :=
          integral_mono hint hbd hpt
      _ = (K : ℝ) ^ n / (N : ℝ) ^ (n + 1) * ∑ k, ∫ ω, m k ω := by
          rw [integral_const_mul, integral_finsetSum _ fun k _ => hmi k]
      _ ≤ (K : ℝ) ^ n / (N : ℝ) ^ (n + 1) * ∑ _k : Fin K, C (2 * (n + 1)) := by
          gcongr with k
          exact hy.moment _ k
      _ = ((K : ℝ) / N) ^ (n + 1) * C (2 * (n + 1)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_pow]
          field_simp
          ring

/-- `N ≥ 1` and `M ≥ 1` under `DiagModel` with `τ > 0`. -/
private theorem vanish_dims {τ : ℝ} {C : ℕ → ℝ} {N : ℕ} {σ : Fin M → ℝ} {Ω : Type*}
    [MeasureSpace Ω] {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hτ : 0 < τ)
    (hX : DiagModel τ C M N σ X) : 1 ≤ N ∧ 1 ≤ M := by
  have h1 : (0 : ℝ) < M / N := hτ.trans_le hX.ratio_ge
  constructor
  · refine Nat.one_le_iff_ne_zero.2 fun h => ?_
    rw [h, Nat.cast_zero, div_zero] at h1
    exact lt_irrefl 0 h1
  · refine Nat.one_le_iff_ne_zero.2 fun h => ?_
    rw [h, Nat.cast_zero, zero_div] at h1
    exact lt_irrefl 0 h1

/-- Moments of `|x_μ|²` and `|x_i|²`: `E(Σ_i X_{iμ}²)^q ≤ τ^{-q} C_{2q}`, `E(Σ_ν X_{iν}²)^q ≤ C_{2q}`. -/
theorem sq_norm_moment {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {τ : ℝ} {C : ℕ → ℝ} {N : ℕ} {σ : Fin M → ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ}
    (hτ : 0 < τ) (hX : DiagModel τ C M N σ X) (q : ℕ) :
    (∀ μ, Integrable (fun ω => (∑ i, X ω i μ ^ 2) ^ q) ∧
      ∫ ω, (∑ i, X ω i μ ^ 2) ^ q ≤ τ⁻¹ ^ q * C (2 * q)) ∧
    (∀ i, Integrable (fun ω => (∑ ν, X ω i ν ^ 2) ^ q) ∧
      ∫ ω, (∑ ν, X ω i ν ^ 2) ^ q ≤ C (2 * q)) := by
  obtain ⟨hN, hM⟩ := vanish_dims hτ hX
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hC : 0 ≤ C (2 * q) := by
    have h := hX.entries.moment (2 * q) ⟨0, hM⟩ ⟨0, hN⟩
    exact (integral_nonneg fun ω => by positivity).trans h
  refine ⟨fun μ => ?_, fun i => ?_⟩
  · obtain ⟨h1, h2⟩ := vanish_sum_sq_moment hN hM (hX.entries.col μ) q
    refine ⟨h1, h2.trans ?_⟩
    gcongr
    exact hX.ratio_le
  · obtain ⟨h1, h2⟩ := vanish_sum_sq_moment hN hN (hX.entries.row i) q
    refine ⟨h1, h2.trans ?_⟩
    rw [div_self hNpos.ne', one_pow, one_mul]

/-! ## The conditional LDE for `Z^{(S)}_s` -/

/-- `Σ_{i,j} x_i A_{ij} x_j − N⁻¹ Σ_i A_{ii}` as the off-diagonal part plus the diagonal part
`Σ_i A_{ii}(x_i² − 1/N)`. -/
private theorem vanish_quad_split {ι : Type*} [Fintype ι] [DecidableEq ι] (N : ℕ) (x : ι → ℝ)
    (A : ι → ι → ℂ) :
    (∑ i, ∑ j, (x i : ℂ) * A i j * x j) - (N : ℂ)⁻¹ * ∑ i, A i i
      = (∑ i, ∑ j ∈ Finset.univ.erase i, (x i : ℂ) * A i j * x j)
        + ∑ i, A i i * ((x i : ℂ) ^ 2 - 1 / ((N : ℝ) : ℂ)) := by
  have h : ∀ i, ∑ j, (x i : ℂ) * A i j * x j
      = (x i : ℂ) * A i i * x i + ∑ j ∈ Finset.univ.erase i, (x i : ℂ) * A i j * x j :=
    fun i => (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_add_distrib, Finset.mul_sum,
    add_comm (∑ i, (x i : ℂ) * A i i * x i), add_sub_assoc, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

/-- The conditional LDE for minor fluctuations: `|Z^{(S)}_μ| ≺ ldeZCol`, `|Z^{(S)}_i| ≺ ldeZRow`. -/
theorem ZS_lde (τ : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (σ : Fin M → ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ), DiagModel τ C M N σ X →
      ∀ z : ℂ,
      (∀ (S : Finset (Fin N)) (μ : Fin N),
        DomAt N ε D (fun ω => ‖ZmuS σ (X ω) z S μ‖) (fun ω => ldeZCol σ (X ω) z S μ)) ∧
      (∀ (S : Finset (Fin M)) (i : Fin M),
        DomAt N ε D (fun ω => ‖ZiS σ (X ω) z S i‖) (fun ω => ldeZRow σ (X ω) z S i)) := by
  obtain ⟨N₁, h₁⟩ := lde_offdiag_cond C hε (D + 1)
  obtain ⟨N₂, h₂⟩ := lde_diag_cond C hε (D + 1)
  refine ⟨max 2 (max N₁ N₂), fun N hN Ω _ _ M σ X hX z => ⟨fun S μ => ?_, fun S i => ?_⟩⟩
  · have hN2 : 2 ≤ N := le_of_max_le_left hN
    have hN₁ : N₁ ≤ N := le_trans (le_max_left _ _) (le_of_max_le_right hN)
    have hN₂ : N₂ ≤ N := le_trans (le_max_right _ _) (le_of_max_le_right hN)
    set T : Finset (Fin M ⊕ Fin N) := colSet (insert μ S) with hT
    set Y : Ω → ((Fin M ⊕ Fin N) × (Fin M ⊕ Fin N) → ℂ) :=
      fun ω st => Gm (diagonal σ) (X ω) z T st.1 st.2 with hYdef
    have hYm : Measurable Y :=
      Measurable.of_eval fun st => measurable_Gm_apply σ hX.entries.measurable z T st.1 st.2
    have hind : IndepFun (fun ω (i : Fin M) => X ω i μ) Y ℙ := by
      set P : Finset (Fin M × Fin N) := Finset.univ.filter (fun q => q.2 = μ) with hP
      have h := indep_entries_minor hX.pos hX.entries z T P fun q hq => Or.inr (by
        have hq2 : q.2 = μ := by simpa [hP] using hq
        simp [hT, colSet, hq2])
      have hφ : Measurable fun (y : P → ℝ) (i : Fin M) => y ⟨(i, μ), by simp [hP]⟩ :=
        Measurable.of_eval fun i => measurable_pi_apply _
      exact h.comp hφ measurable_id
    have hoff := h₁ N hN₁ (fun i ω => X ω i μ) Y (fun b i j => b (Sum.inl i, Sum.inl j))
      (hX.entries.col μ) hYm (fun i j => measurable_pi_apply _) hind
    have hdiag := h₂ N hN₂ (fun i ω => X ω i μ) Y (fun b i => b (Sum.inl i, Sum.inl i))
      (hX.entries.col μ) hYm (fun i => measurable_pi_apply _) hind
    refine DomAt.mono (by omega) (fun ω => ?_) (fun ω => le_rfl) (fun ω => ?_) le_rfl
      (by linarith) (DomAt.add hN2 hoff hdiag)
    · simp only [Pi.add_apply]
      rw [vanish_ZmuS_eq, vanish_quad_split]
      exact norm_add_le _ _
    · unfold ldeZCol ldeOffBound ldeDiagBound
      positivity
  · have hN2 : 2 ≤ N := le_of_max_le_left hN
    have hN₁ : N₁ ≤ N := le_trans (le_max_left _ _) (le_of_max_le_right hN)
    have hN₂ : N₂ ≤ N := le_trans (le_max_right _ _) (le_of_max_le_right hN)
    set T : Finset (Fin M ⊕ Fin N) := rowSet (insert i S) with hT
    set Y : Ω → ((Fin M ⊕ Fin N) × (Fin M ⊕ Fin N) → ℂ) :=
      fun ω st => Gm (diagonal σ) (X ω) z T st.1 st.2 with hYdef
    have hYm : Measurable Y :=
      Measurable.of_eval fun st => measurable_Gm_apply σ hX.entries.measurable z T st.1 st.2
    have hind : IndepFun (fun ω (ν : Fin N) => X ω i ν) Y ℙ := by
      set P : Finset (Fin M × Fin N) := Finset.univ.filter (fun q => q.1 = i) with hP
      have h := indep_entries_minor hX.pos hX.entries z T P fun q hq => Or.inl (by
        have hq1 : q.1 = i := by simpa [hP] using hq
        simp [hT, rowSet, hq1])
      have hφ : Measurable fun (y : P → ℝ) (ν : Fin N) => y ⟨(i, ν), by simp [hP]⟩ :=
        Measurable.of_eval fun ν => measurable_pi_apply _
      exact h.comp hφ measurable_id
    have hoff := h₁ N hN₁ (fun ν ω => X ω i ν) Y (fun b ν ν' => b (Sum.inr ν, Sum.inr ν'))
      (hX.entries.row i) hYm (fun ν ν' => measurable_pi_apply _) hind
    have hdiag := h₂ N hN₂ (fun ν ω => X ω i ν) Y (fun b ν => b (Sum.inr ν, Sum.inr ν))
      (hX.entries.row i) hYm (fun ν => measurable_pi_apply _) hind
    refine DomAt.mono (by omega) (fun ω => ?_) (fun ω => le_rfl) (fun ω => ?_) le_rfl
      (by linarith) (DomAt.add hN2 hoff hdiag)
    · simp only [Pi.add_apply]
      rw [vanish_ZiS_eq, vanish_quad_split]
      exact norm_add_le _ _
    · unfold ldeZRow ldeOffBound ldeDiagBound
      positivity

/-! ## The good event -/

/-- The good event `𝒜` at one matrix: `Λ ≤ N^{ε₁−c₀}`, `Λ_o ≤ N^{ε₁}Υ`, and
`|Z^{(S)}_s| ≤ N^{ε_L} ldeZ` for every label `s ∉ S` with `|S| + 1 ≤ 2p`, in both index sets. -/
def FaGood {N : ℕ} (σ : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (p : ℕ)
    (c₀ ε₁ εL Υ : ℝ) : Prop :=
  Lambda σ Xm z ≤ (N : ℝ) ^ (ε₁ - c₀) ∧ LambdaO σ Xm z ≤ (N : ℝ) ^ ε₁ * Υ ∧
    (∀ (S : Finset (Fin N)) (μ : Fin N), μ ∉ S → S.card + 1 ≤ 2 * p →
      ‖ZmuS σ Xm z S μ‖ ≤ (N : ℝ) ^ εL * ldeZCol σ Xm z S μ) ∧
    (∀ (S : Finset (Fin M)) (i : Fin M), i ∉ S → S.card + 1 ≤ 2 * p →
      ‖ZiS σ Xm z S i‖ ≤ (N : ℝ) ^ εL * ldeZRow σ Xm z S i)

/-- The labels `(S, s)` with `s ∉ S`, `|S| + 1 ≤ 2p` in an index set of size `K ≥ 1` number at
most `2p K^{2p}`. -/
private theorem vanish_card_index {K : ℕ} (hK : 1 ≤ K) (p : ℕ) :
    ((Finset.univ.filter fun q : Finset (Fin K) × Fin K =>
      q.2 ∉ q.1 ∧ q.1.card + 1 ≤ 2 * p).card : ℝ) ≤ 2 * p * (K : ℝ) ^ (2 * p) := by
  have hsub : (Finset.univ.filter fun q : Finset (Fin K) × Fin K =>
      q.2 ∉ q.1 ∧ q.1.card + 1 ≤ 2 * p)
      ⊆ (Finset.range (2 * p)).biUnion
        fun j => Finset.powersetCard j (Finset.univ : Finset (Fin K)) ×ˢ Finset.univ := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_product,
      Finset.mem_powersetCard, Finset.mem_univ, and_true]
    exact ⟨q.1.card, by omega, Finset.subset_univ _, rfl⟩
  have h : (Finset.univ.filter fun q : Finset (Fin K) × Fin K =>
      q.2 ∉ q.1 ∧ q.1.card + 1 ≤ 2 * p).card ≤ 2 * p * K ^ (2 * p) := by
    refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
    calc ∑ j ∈ Finset.range (2 * p),
          (Finset.powersetCard j (Finset.univ : Finset (Fin K)) ×ˢ
            (Finset.univ : Finset (Fin K))).card
        ≤ ∑ _j ∈ Finset.range (2 * p), K ^ (2 * p) := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [Finset.card_product, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
          have hj' : j + 1 ≤ 2 * p := by simp only [Finset.mem_range] at hj; omega
          calc K.choose j * K ≤ K ^ j * K := Nat.mul_le_mul_right K (Nat.choose_le_pow K j)
            _ = K ^ (j + 1) := (pow_succ K j).symm
            _ ≤ K ^ (2 * p) := Nat.pow_le_pow_right hK hj'
      _ = 2 * p * K ^ (2 * p) := by simp
  calc ((Finset.univ.filter fun q : Finset (Fin K) × Fin K =>
        q.2 ∉ q.1 ∧ q.1.card + 1 ≤ 2 * p).card : ℝ)
      ≤ ((2 * p * K ^ (2 * p) : ℕ) : ℝ) := by exact_mod_cast h
    _ = 2 * p * (K : ℝ) ^ (2 * p) := by push_cast; ring

/-- `P(𝒜ᶜ) ≤ N^{-(D₁-1)}` (LDE events at level `(ε_L, D₁ + 2p + 1)`). -/
theorem faGood_highProb (τ c₀ : ℝ) (C : ℕ → ℝ) (p : ℕ) (ε₁ εL D₁ : ℝ) (hτ : 0 < τ)
    (hεL : 0 < εL) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (σ : Fin M → ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ), DiagModel τ C M N σ X →
      ∀ z : ℂ, ∀ Υ : ℝ,
      DomAt N ε₁ D₁ (fun ω => Lambda σ (X ω) z) (fun _ => (N : ℝ) ^ (-c₀)) →
      DomAt N ε₁ D₁ (fun ω => LambdaO σ (X ω) z) (fun _ => Υ) →
      HighProbAt N (D₁ - 1) {ω | FaGood σ (X ω) z p c₀ ε₁ εL Υ} := by
  obtain ⟨N₃, h₃⟩ := ZS_lde τ C εL (D₁ + ((2 * p + 1 : ℕ) : ℝ)) hτ hεL
  refine ⟨max (max 4 (2 * p)) (max N₃ ⌈(2 * p : ℝ) * τ⁻¹ ^ (2 * p)⌉₊),
    fun N hN Ω _ _ M σ X hX z Υ hΛ hΛo => ?_⟩
  have hN4 : 4 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNp : 2 * p ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 : N₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNK' : ⌈(2 * p : ℝ) * τ⁻¹ ^ (2 * p)⌉₊ ≤ N :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hNK : (2 * p : ℝ) * τ⁻¹ ^ (2 * p) ≤ N :=
    (Nat.le_ceil _).trans (by exact_mod_cast hNK')
  obtain ⟨hN1, hM1⟩ := vanish_dims hτ hX
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNC : (N : ℝ) ^ (((2 * p + 1 : ℕ) : ℝ)) = (N : ℝ) * (N : ℝ) ^ (2 * p) := by
    rw [Real.rpow_natCast, pow_succ, mul_comm]
  obtain ⟨hcol, hrow⟩ := h₃ N hN3 M σ X hX z
  set Icol := Finset.univ.filter fun q : Finset (Fin N) × Fin N =>
    q.2 ∉ q.1 ∧ q.1.card + 1 ≤ 2 * p with hIcol
  set Irow := Finset.univ.filter fun q : Finset (Fin M) × Fin M =>
    q.2 ∉ q.1 ∧ q.1.card + 1 ≤ 2 * p with hIrow
  set A₁ := {ω | Lambda σ (X ω) z ≤ (N : ℝ) ^ (ε₁ - c₀)} with hA₁
  set A₂ := {ω | LambdaO σ (X ω) z ≤ (N : ℝ) ^ ε₁ * Υ} with hA₂
  set A₃ := ⋂ q ∈ Icol,
    {ω | ‖ZmuS σ (X ω) z q.1 q.2‖ ≤ (N : ℝ) ^ εL * ldeZCol σ (X ω) z q.1 q.2} with hA₃
  set A₄ := ⋂ q ∈ Irow,
    {ω | ‖ZiS σ (X ω) z q.1 q.2‖ ≤ (N : ℝ) ^ εL * ldeZRow σ (X ω) z q.1 q.2} with hA₄
  have h₁ : HighProbAt N D₁ A₁ := by
    have he : A₁ᶜ = {ω | (N : ℝ) ^ ε₁ * (N : ℝ) ^ (-c₀) < Lambda σ (X ω) z} := by
      ext ω
      simp [hA₁, ← Real.rpow_add hNpos, sub_eq_add_neg]
    unfold HighProbAt
    rw [he]
    exact hΛ
  have h₂ : HighProbAt N D₁ A₂ := by
    have he : A₂ᶜ = {ω | (N : ℝ) ^ ε₁ * Υ < LambdaO σ (X ω) z} := by
      ext ω
      simp [hA₂]
    unfold HighProbAt
    rw [he]
    exact hΛo
  have hcardcol : (Icol.card : ℝ) ≤ (N : ℝ) ^ (((2 * p + 1 : ℕ) : ℝ)) := by
    refine (vanish_card_index hN1 p).trans ?_
    rw [hNC]
    gcongr
    exact_mod_cast hNp
  have hcardrow : (Irow.card : ℝ) ≤ (N : ℝ) ^ (((2 * p + 1 : ℕ) : ℝ)) := by
    refine (vanish_card_index hM1 p).trans ?_
    have hMN : (M : ℝ) ≤ τ⁻¹ * N := by
      have := hX.ratio_le
      rwa [div_le_iff₀ hNpos] at this
    calc (2 * p : ℝ) * (M : ℝ) ^ (2 * p)
        ≤ (2 * p : ℝ) * (τ⁻¹ * N) ^ (2 * p) := by gcongr
      _ = (2 * p : ℝ) * τ⁻¹ ^ (2 * p) * (N : ℝ) ^ (2 * p) := by ring
      _ ≤ (N : ℝ) * (N : ℝ) ^ (2 * p) := by gcongr
      _ = _ := hNC.symm
  have h₃' : HighProbAt N D₁ A₃ := by
    refine HighProbAt.biInter Icol hN1 hcardcol fun q _ => ?_
    have he : {ω | ‖ZmuS σ (X ω) z q.1 q.2‖ ≤ (N : ℝ) ^ εL * ldeZCol σ (X ω) z q.1 q.2}ᶜ
        = {ω | (N : ℝ) ^ εL * ldeZCol σ (X ω) z q.1 q.2 < ‖ZmuS σ (X ω) z q.1 q.2‖} := by
      ext ω
      simp
    unfold HighProbAt
    rw [he]
    exact hcol q.1 q.2
  have h₄' : HighProbAt N D₁ A₄ := by
    refine HighProbAt.biInter Irow hN1 hcardrow fun q _ => ?_
    have he : {ω | ‖ZiS σ (X ω) z q.1 q.2‖ ≤ (N : ℝ) ^ εL * ldeZRow σ (X ω) z q.1 q.2}ᶜ
        = {ω | (N : ℝ) ^ εL * ldeZRow σ (X ω) z q.1 q.2 < ‖ZiS σ (X ω) z q.1 q.2‖} := by
      ext ω
      simp
    unfold HighProbAt
    rw [he]
    exact hrow q.1 q.2
  have hsub : {ω | FaGood σ (X ω) z p c₀ ε₁ εL Υ}ᶜ ⊆ A₁ᶜ ∪ A₂ᶜ ∪ A₃ᶜ ∪ A₄ᶜ := by
    intro ω hω
    by_contra hc
    simp only [Set.mem_union, not_or, Set.mem_compl_iff, not_not] at hc
    obtain ⟨⟨⟨g1, g2⟩, g3⟩, g4⟩ := hc
    refine hω ⟨g1, g2, fun S μ hμ hS => ?_, fun S i hi hS => ?_⟩
    · refine Set.mem_iInter₂.1 g3 (S, μ) ?_
      simp only [hIcol, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hμ, hS⟩
    · refine Set.mem_iInter₂.1 g4 (S, i) ?_
      simp only [hIrow, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hi, hS⟩
  have hfin : 4 * ENNReal.ofReal ((N : ℝ) ^ (-D₁)) ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D₁ - 1))) := by
    rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [show -(D₁ - 1) = 1 + -D₁ by ring, Real.rpow_add hNpos, Real.rpow_one]
    have h4 : (4 : ℝ) ≤ N := by exact_mod_cast hN4
    gcongr
  unfold HighProbAt at h₁ h₂ h₃' h₄' ⊢
  calc ℙ {ω | FaGood σ (X ω) z p c₀ ε₁ εL Υ}ᶜ ≤ ℙ (A₁ᶜ ∪ A₂ᶜ ∪ A₃ᶜ ∪ A₄ᶜ) := measure_mono hsub
    _ ≤ ℙ A₁ᶜ + ℙ A₂ᶜ + ℙ A₃ᶜ + ℙ A₄ᶜ := by
        refine (measure_union_le _ _).trans ?_
        gcongr
        refine (measure_union_le _ _).trans ?_
        gcongr
        exact measure_union_le _ _
    _ ≤ 4 * ENNReal.ofReal ((N : ℝ) ^ (-D₁)) := by
        calc _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D₁)) + ENNReal.ofReal ((N : ℝ) ^ (-D₁))
              + ENNReal.ofReal ((N : ℝ) ^ (-D₁)) + ENNReal.ofReal ((N : ℝ) ^ (-D₁)) := by
              gcongr
          _ = _ := by ring
    _ ≤ _ := hfin

/-! ## Checks at the Rademacher instance `M = N = 2`, `σ ≡ 1`, `τ = 1/2`, `z = 2i` -/

section Checks

open Complex

/-- `ZS_lde` at `τ = 1/2`, `C ≡ 1`, `ε = 1/4`, `D = 1`, `z = 2i`, column labels. This is a
conditional check: the models are binders, since the Rademacher model has `N = 2`, below the
threshold `N₀`. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (M : ℕ) (σ : Fin M → ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ),
    DiagModel (1 / 2) (fun _ => 1) M N σ X → ∀ (S : Finset (Fin N)) (μ : Fin N),
    DomAt N (1 / 4) 1 (fun ω => ‖ZmuS σ (X ω) (2 * I) S μ‖)
      (fun ω => ldeZCol σ (X ω) (2 * I) S μ) := by
  obtain ⟨N₀, h⟩ := ZS_lde (1 / 2) (fun _ => 1) (1 / 4) 1 (by norm_num) (by norm_num)
  exact ⟨N₀, fun N hN Ω _ _ M σ X hX => (h N hN M σ X hX (2 * I)).1⟩

/-- `faGood_highProb` at `τ = 1/2`, `C ≡ 1`, `p = 1`, `c₀ = 1/4`, `ε₁ = ε_L = 1/64`,
`D₁ = 10`, `z = 2i`, `Υ = N^{-1/2}`. This is a conditional check: the models and the two
domination hypotheses are binders, since the Rademacher model has `N = 2`, below the
threshold `N₀`. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (M : ℕ) (σ : Fin M → ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ),
    DiagModel (1 / 2) (fun _ => 1) M N σ X →
    DomAt N (1 / 64) 10 (fun ω => Lambda σ (X ω) (2 * I)) (fun _ => (N : ℝ) ^ (-(1 / 4 : ℝ))) →
    DomAt N (1 / 64) 10 (fun ω => LambdaO σ (X ω) (2 * I)) (fun _ => (N : ℝ) ^ (-(1 / 2 : ℝ))) →
    HighProbAt N (10 - 1)
      {ω | FaGood σ (X ω) (2 * I) 1 (1 / 4) (1 / 64) (1 / 64) ((N : ℝ) ^ (-(1 / 2 : ℝ)))} := by
  obtain ⟨N₀, h⟩ := faGood_highProb (1 / 2) (1 / 4) (fun _ => 1) 1 (1 / 64) (1 / 64) 10
    (by norm_num) (by norm_num)
  exact ⟨N₀, fun N hN Ω _ _ M σ X hX hΛ hΛo =>
    h N hN M σ X hX (2 * I) ((N : ℝ) ^ (-(1 / 2 : ℝ))) hΛ hΛo⟩

end Checks

end Anisotropic

#print axioms Anisotropic.integral_quadForm_mul_eq_zero
#print axioms Anisotropic.indepFun_col_rest
#print axioms Anisotropic.indepFun_row_rest
#print axioms Anisotropic.integral_ZmuS_mul_eq_zero
#print axioms Anisotropic.integral_ZiS_mul_eq_zero
#print axioms Anisotropic.sq_norm_moment
#print axioms Anisotropic.ZS_lde
#print axioms Anisotropic.FaGood
#print axioms Anisotropic.faGood_highProb
