import Anisotropic.Averaged.Defs
import Anisotropic.Comparison.Interpolation
import Anisotropic.Comparison.Ladder
import Anisotropic.Comparison.PrelimBounds
import Anisotropic.Comparison.Words
import Anisotropic.Entrywise.Defs
import Anisotropic.Entrywise.DiagModel
import Anisotropic.Framework.Domination
import Anisotropic.Framework.Model
import Anisotropic.LinAlg.Expansion

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # The chain of §7 for `F̃^p`: Taylor expansion, moment matching, `0 → θ` (§9) -/

private theorem chainP_opNorm_le {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) : ‖A‖ ≤ Real.sqrt (∑ i, ∑ j, A i j ^ 2) := by
  rw [l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (norm_nonneg x),
    ← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [LinearEquiv.trans_apply, LinearMap.coe_toContinuousLinearMap',
    Matrix.toLpLin_apply, Real.norm_eq_abs, sq_abs]
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [mulVec, dotProduct]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- `‖XᵀX‖ ≤ ‖X‖_F² = ∑_{iμ} X_{iμ}²`. -/
private theorem chainP_XtX_le (A : Matrix (Fin M) (Fin N) ℝ) :
    ‖Aᵀ * A‖ ≤ ∑ α : Fin M × Fin N, A α.1 α.2 ^ 2 := by
  have h1 : ‖Aᵀ * A‖ = ‖A‖ * ‖A‖ := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact l2_opNorm_conjTranspose_mul_self A
  have h2 := chainP_opNorm_le A
  have h0 : 0 ≤ ∑ i, ∑ j, A i j ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [h1, Fintype.sum_prod_type]
  calc ‖A‖ * ‖A‖ ≤ Real.sqrt (∑ i, ∑ j, A i j ^ 2) * Real.sqrt (∑ i, ∑ j, A i j ^ 2) :=
        mul_le_mul h2 h2 (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := Real.mul_self_sqrt h0
private theorem chainR_ent_add {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (v w : ι → ℝ) :
    ent (A + B) v w = ent A v w + ent B v w := by
  simp [ent, add_mulVec, dotProduct_add]

private theorem chainR_ent_eq {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (x y : ι → ℝ) :
    ent A x y = ∑ s, ∑ t, (x s : ℂ) * A s t * (y t : ℂ) := by
  simp only [ent, cvec, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

private theorem chainR_ent_transpose {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (x y : ι → ℝ) :
    ent Aᵀ x y = ent A y x := by
  rw [chainR_ent_eq, chainR_ent_eq, Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
    simp only [transpose_apply]; ring

private theorem chainR_ent_eI_right {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (x : ι → ℝ) (r : ι) : ent A x (eI r) = ∑ s, (x s : ℂ) * A s r := by
  rw [chainR_ent_eq]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [eI, Pi.single_apply, apply_ite]

private theorem chainR_ent_eI_left {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (y : ι → ℝ) (r : ι) : ent A (eI r) y = ∑ t, A r t * (y t : ℂ) := by
  rw [chainR_ent_eq]
  simp [eI, Pi.single_apply, apply_ite, ite_mul, Finset.sum_ite_eq']

private theorem chainR_diag {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) :
    ∃ U : Matrix (Fin M) (Fin M) ℝ, U * Uᵀ = 1 ∧ Uᵀ * U = 1 ∧
      Sig = U * diagonal (specOf Sig) * Uᵀ ∧ ∀ i, 0 < specOf Sig i := by
  obtain ⟨U, hU, hD⟩ := exists_orth_diag hSig.1
  have h₁ : Uᵀ * U = 1 := (Matrix.mem_orthogonalGroup_iff' _ _).1 hU
  have h₂ : U * Uᵀ = 1 := (Matrix.mem_orthogonalGroup_iff _ _).1 hU
  refine ⟨U, h₂, h₁, ?_, fun i => ?_⟩
  · rw [← hD]
    simp only [← Matrix.mul_assoc]
    rw [h₂, Matrix.one_mul, Matrix.mul_assoc, h₂, Matrix.mul_one]
  · rw [specOf_eq hSig.1]
    exact hSig.eigenvalues_pos i

private theorem chainR_sum_sq_UT {K : ℕ} {U : Matrix (Fin K) (Fin K) ℝ} (h₂ : U * Uᵀ = 1)
    (x : Fin K → ℝ) : ∑ i, (Uᵀ *ᵥ x) i ^ 2 = ∑ i, x i ^ 2 := by
  have e : (Uᵀ *ᵥ x) ⬝ᵥ (Uᵀ *ᵥ x) = x ⬝ᵥ x := by
    rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, h₂, one_mulVec, dotProduct_comm]
  simpa [dotProduct, sq] using e

private theorem chainR_row_sq {K : ℕ} {U : Matrix (Fin K) (Fin K) ℝ} (h₂ : U * Uᵀ = 1) (i : Fin K) :
    ∑ k, U i k ^ 2 = 1 := by
  have := congrFun (congrFun h₂ i) i
  simpa [Matrix.mul_apply, sq, Matrix.one_apply] using this

/-- `|Σ x|² ≤ τ⁻² |x|²` under (bound_Sigma). -/
private theorem chainR_sumsq_Sig {τ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hS : SigmaAssumption τ Sig) (x : Fin M → ℝ) :
    ∑ l, (Sig *ᵥ x) l ^ 2 ≤ τ⁻¹ ^ 2 * ∑ l, x l ^ 2 := by
  obtain ⟨U, h₂, h₁, hSd, hσ⟩ := chainR_diag hS.posDef
  have hle : ∀ k, specOf Sig k ≤ τ⁻¹ := fun k => by
    rw [specOf_eq hS.posDef.isHermitian]; exact hS.eigenvalues_le k
  have hUU : Uᵀ * Uᵀᵀ = 1 := by rw [transpose_transpose]; exact h₁
  have e : Sig *ᵥ x = Uᵀᵀ *ᵥ (diagonal (specOf Sig) *ᵥ (Uᵀ *ᵥ x)) := by
    rw [transpose_transpose, mulVec_mulVec, mulVec_mulVec]
    exact congrArg (· *ᵥ x) hSd
  rw [e, chainR_sum_sq_UT hUU, ← chainR_sum_sq_UT h₂ x, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [mulVec_diagonal, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hσ k).le (hle k) 2) (sq_nonneg _)

/-- `|Σ̲ y| ≤ τ⁻¹ |y|`. -/
private theorem chainR_testNorm_SigU {τ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hS : SigmaAssumption τ Sig) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (y : Fin M ⊕ Fin N → ℝ) :
    testNorm (SigU (n := Fin N) Sig *ᵥ y) ≤ τ⁻¹ * testNorm y := by
  have hτi : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  have h1 := chainR_sumsq_Sig hS (y ∘ Sum.inl)
  have h2 : 0 ≤ ∑ ν, y (Sum.inr ν) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h3 : 0 ≤ ∑ l, y (Sum.inl l) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  unfold testNorm
  rw [← Real.sqrt_sq (inv_pos.2 hτ).le, ← Real.sqrt_mul (sq_nonneg _)]
  refine Real.sqrt_le_sqrt ?_
  simp only [SigU, fromBlocks_mulVec, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    zero_mulVec, add_zero, zero_add, one_mulVec]
  simp only [Function.comp_def] at h1
  have h4 : ∑ ν, y (Sum.inr ν) ^ 2 ≤ τ⁻¹ ^ 2 * ∑ ν, y (Sum.inr ν) ^ 2 :=
    le_mul_of_one_le_left h2 (one_le_pow₀ hτi)
  rw [mul_add]
  exact add_le_add h1 h4

/-- `v̄` of `Σ̲ y` is `y`. -/
private theorem chainR_vbar_SigU {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (y : Fin M ⊕ Fin N → ℝ) : vbar Sig (SigU (n := Fin N) Sig *ᵥ y) = y := by
  have hS : Sig⁻¹ * Sig = 1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hSig.isUnit)
  funext s
  rcases s with j | ν
  · simp [vbar, SigU, fromBlocks_mulVec, mulVec_mulVec, hS]
  · simp [vbar, SigU, fromBlocks_mulVec]


/-- `(1 + wΣ)⁻¹_{li} = ∑ₖ U_{lk} (1 + σₖ w)⁻¹ U_{ik}`. -/
private theorem chainR_cinv_entry {Sig U : Matrix (Fin M) (Fin M) ℝ} {σ : Fin M → ℝ}
    (h₂ : U * Uᵀ = 1) (h₁ : Uᵀ * U = 1) (hS : Sig = U * diagonal σ * Uᵀ) {w : ℂ}
    (hw : ∀ i, 1 + (σ i : ℂ) * w ≠ 0) (l i : Fin M) :
    (1 + w • cplx Sig)⁻¹ l i = ∑ k, (U l k : ℂ) * (1 + (σ k : ℂ) * w)⁻¹ * (U i k : ℂ) := by
  have c₂ : (cplx Uᵀ)ᵀ * cplx Uᵀ = 1 := by
    simp only [cplx]
    rw [← transpose_map, transpose_transpose, ← Matrix.map_mul, h₂,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have c₁ : cplx Uᵀ * (cplx Uᵀ)ᵀ = 1 := by
    simp only [cplx]
    rw [← transpose_map, transpose_transpose, ← Matrix.map_mul, h₁,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hT : 1 + w • cplx Sig =
      (cplx Uᵀ)ᵀ * diagonal (fun i => 1 + (σ i : ℂ) * w) * cplx Uᵀ := by
    have e1 : cplx Sig = (cplx Uᵀ)ᵀ * diagonal (fun i => (σ i : ℂ)) * cplx Uᵀ := by
      simp only [cplx]
      rw [hS, ← transpose_map, transpose_transpose, Matrix.map_mul, Matrix.map_mul,
        diagonal_map (map_zero _)]
      rfl
    have e2 : diagonal (fun i => 1 + (σ i : ℂ) * w) =
        1 + w • diagonal (fun i => (σ i : ℂ)) := by
      rw [← diagonal_one, ← diagonal_smul, diagonal_add]
      congr 1
      funext i
      simp [mul_comm]
    rw [e2, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, c₂, Matrix.mul_smul,
      Matrix.smul_mul, e1]
  have hinv : (1 + w • cplx Sig)⁻¹ =
      (cplx Uᵀ)ᵀ * diagonal (fun i => (1 + (σ i : ℂ) * w)⁻¹) * cplx Uᵀ := by
    apply Matrix.inv_eq_right_inv
    rw [hT]
    have hd : diagonal (fun i => 1 + (σ i : ℂ) * w) *
        diagonal (fun i => (1 + (σ i : ℂ) * w)⁻¹) = 1 := by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      exact mul_inv_cancel₀ (hw i)
    calc (cplx Uᵀ)ᵀ * diagonal (fun i => 1 + (σ i : ℂ) * w) * cplx Uᵀ *
          ((cplx Uᵀ)ᵀ * diagonal (fun i => (1 + (σ i : ℂ) * w)⁻¹) * cplx Uᵀ)
        = (cplx Uᵀ)ᵀ * (diagonal (fun i => 1 + (σ i : ℂ) * w) * (cplx Uᵀ * (cplx Uᵀ)ᵀ) *
            diagonal (fun i => (1 + (σ i : ℂ) * w)⁻¹)) * cplx Uᵀ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [c₁, Matrix.mul_one, hd, Matrix.mul_one, c₂]
  rw [hinv]
  simp [Matrix.mul_apply, cplx, Matrix.diagonal_apply, mul_ite, Finset.sum_ite_eq']

private theorem chainR_abs_le_testNorm {ι : Type*} [Fintype ι] (x : ι → ℝ) (s : ι) :
    |x s| ≤ testNorm x := by
  unfold testNorm
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (fun t _ => sq_nonneg (x t)) (Finset.mem_univ s))

private theorem chainR_sqrt_inl_le (x : Fin M ⊕ Fin N → ℝ) :
    √(∑ j, x (Sum.inl j) ^ 2) ≤ testNorm x := by
  unfold testNorm
  refine Real.sqrt_le_sqrt ?_
  rw [Fintype.sum_sum_type]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- `|⟨v̄, Π e_p⟩| ≤ max(c⁻¹, K) |v|` when `|m| ≤ K` and `|1 + σᵢ m| ≥ c`. -/
private theorem chainR_pi_bound {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {c K : ℝ}
    (hc : 0 < c) {w : ℂ} (hwK : ‖w‖ ≤ K) (hOne : ∀ i, c ≤ ‖1 + (specOf Sig i : ℂ) * w‖)
    (x : Fin M ⊕ Fin N → ℝ) (p : Fin M ⊕ Fin N) :
    ‖ent (piMat (N := N) Sig w) (vbar Sig x) (eI p)‖ ≤ max c⁻¹ K * testNorm x := by
  rw [chainR_ent_eI_right, Fintype.sum_sum_type]
  rcases p with i | μ
  · simp only [piMat, fromBlocks_apply₁₁, fromBlocks_apply₂₁, Matrix.zero_apply, mul_zero,
      Finset.sum_const_zero, add_zero, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib, norm_neg]
    obtain ⟨U, h₂, h₁, hSd, hσ⟩ := chainR_diag hSig
    have hw0 : ∀ k, 1 + (specOf Sig k : ℂ) * w ≠ 0 := fun k h0 => by
      have := hOne k
      rw [h0, norm_zero] at this
      linarith
    set xM : Fin M → ℝ := fun j => x (Sum.inl j) with hxM
    have hSS : Sig * Sig⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hSig.isUnit)
    have hy : Sig *ᵥ (Sig⁻¹ *ᵥ xM) = xM := by rw [mulVec_mulVec, hSS, one_mulVec]
    have hT : Sigᵀ = Sig := by rw [← conjTranspose_eq_transpose_of_trivial]; exact hSig.1.eq
    have hsym : ∀ j l, Sig j l = Sig l j := fun j l => by
      conv_lhs => rw [← hT]
      rfl
    have e1 : ∑ j, ((vbar Sig x (Sum.inl j) : ℝ) : ℂ) * (cplx Sig * (1 + w • cplx Sig)⁻¹) j i =
        ∑ l, (xM l : ℂ) * (1 + w • cplx Sig)⁻¹ l i := by
      simp only [Matrix.mul_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      have e : xM l = ∑ j, Sig l j * (Sig⁻¹ *ᵥ xM) j := by
        conv_lhs => rw [← hy]
        rfl
      rw [e, Complex.ofReal_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [vbar, Sum.elim_inl, Function.comp_def, cplx, Matrix.map_apply,
        Complex.ofReal_mul, hsym l j, Complex.coe_algebraMap, ← hxM]
      ring
    have e2 : ∑ l, (xM l : ℂ) * (1 + w • cplx Sig)⁻¹ l i =
        ∑ k, (((Uᵀ *ᵥ xM) k : ℝ) : ℂ) * (1 + (specOf Sig k : ℂ) * w)⁻¹ * (U i k : ℂ) := by
      simp only [chainR_cinv_entry h₂ h₁ hSd hw0, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [mulVec, dotProduct, transpose_apply, Complex.ofReal_sum, Complex.ofReal_mul,
        Finset.sum_mul]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [e1, e2]
    have hb : ∀ k, ‖(((Uᵀ *ᵥ xM) k : ℝ) : ℂ) * (1 + (specOf Sig k : ℂ) * w)⁻¹ * (U i k : ℂ)‖ ≤
        c⁻¹ * (|(Uᵀ *ᵥ xM) k| * |U i k|) := by
      intro k
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, norm_inv]
      have hinv : ‖1 + (specOf Sig k : ℂ) * w‖⁻¹ ≤ c⁻¹ := inv_anti₀ hc (hOne k)
      have := mul_le_mul_of_nonneg_left hinv (abs_nonneg ((Uᵀ *ᵥ xM) k))
      nlinarith [abs_nonneg (U i k), abs_nonneg ((Uᵀ *ᵥ xM) k)]
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun k => |(Uᵀ *ᵥ xM) k|)
      (fun k => |U i k|)
    simp only [sq_abs] at hcs
    rw [chainR_sum_sq_UT h₂, chainR_row_sq h₂, Real.sqrt_one, mul_one] at hcs
    have hc0 : 0 ≤ c⁻¹ := (inv_pos.2 hc).le
    calc _ ≤ ∑ k, c⁻¹ * (|(Uᵀ *ᵥ xM) k| * |U i k|) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => hb k)
      _ ≤ c⁻¹ * √(∑ j, xM j ^ 2) := by
          rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hcs hc0
      _ ≤ max c⁻¹ K * testNorm x :=
          mul_le_mul (le_max_left _ _) (chainR_sqrt_inl_le x) (Real.sqrt_nonneg _)
            (hc0.trans (le_max_left _ _))
  · simp only [piMat, fromBlocks_apply₁₂, fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero,
      Finset.sum_const_zero, zero_add, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
      mul_one, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [vbar, Sum.elim_inr, Function.comp_apply]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul (hwK.trans (le_max_right _ _)) (chainR_abs_le_testNorm x _) (abs_nonneg _)
      ((norm_nonneg w).trans (hwK.trans (le_max_right _ _)))


private theorem chainR_cplx_mulVec {ι : Type*} [Fintype ι] (S : Matrix ι ι ℝ) (b : ι → ℝ) :
    cplx S *ᵥ cvec b = cvec (S *ᵥ b) := by
  funext s
  simp [cplx, cvec, mulVec, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul]

/-- `⟨a, S M S b⟩ = ⟨S a, M S b⟩` for a real symmetric `S`. -/
private theorem chainR_ent_conj {ι : Type*} [Fintype ι] (S : Matrix ι ι ℝ) (hS : Sᵀ = S)
    (B : Matrix ι ι ℂ) (a b : ι → ℝ) :
    ent (cplx S * B * cplx S) a b = ent B (S *ᵥ a) (S *ᵥ b) := by
  have hC : (cplx S)ᵀ = cplx S := by rw [cplx, ← transpose_map, hS]
  unfold ent
  rw [← mulVec_mulVec, ← mulVec_mulVec, chainR_cplx_mulVec, dotProduct_mulVec, ← hC,
    vecMul_transpose, chainR_cplx_mulVec]

private theorem chainR_SigU_inv {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) :
    (SigU (n := Fin N) Sig)⁻¹ = SigU (n := Fin N) Sig⁻¹ := by
  have hS : Sig * Sig⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hSig.isUnit)
  apply Matrix.inv_eq_right_inv
  rw [SigU, SigU, fromBlocks_multiply, hS]
  simp [fromBlocks_one]

private theorem chainR_testNorm_eq {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    Real.sqrt (x ⬝ᵥ x) = testNorm x := by
  unfold testNorm
  simp [dotProduct, sq]

/-- `|⟨v̄, G e_p⟩| ≤ ((1 + ‖AᵀA‖)/η + 1) |v| |Σ̲ e_p| + |v|` (Lemma 4.9). -/
private theorem chainR_G_left_op {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (x : Fin M ⊕ Fin N → ℝ)
    (p : Fin M ⊕ Fin N) :
    ‖ent (G Sig A z) (vbar Sig x) (eI p)‖ ≤
      ((1 + ‖Aᵀ * A‖) / z.im + 1) * testNorm x * testNorm (SigU (n := Fin N) Sig *ᵥ eI p) +
        testNorm x := by
  have hT : Sigᵀ = Sig := by rw [← conjTranspose_eq_transpose_of_trivial]; exact hSig.1.eq
  have hTi : (SigU (n := Fin N) Sig⁻¹)ᵀ = SigU (n := Fin N) Sig⁻¹ := by
    rw [SigU, fromBlocks_transpose, transpose_nonsing_inv, hT]
    simp
  have hvb : ∀ y, SigU (n := Fin N) Sig⁻¹ *ᵥ y = vbar Sig y := fun y => by
    funext s
    rcases s with j | ν
    · simp [vbar, SigU, fromBlocks_mulVec]
    · simp [vbar, SigU, fromBlocks_mulVec]
  have h := opnorm_G hSig A hz x (SigU (n := Fin N) Sig *ᵥ eI p)
  rw [chainR_SigU_inv hSig, Matrix.mul_add, Matrix.add_mul, chainR_ent_add, chainR_ent_conj _ hTi,
    chainR_ent_conj _ hTi, hvb, hvb, chainR_vbar_SigU hSig, chainR_testNorm_eq,
    chainR_testNorm_eq] at h
  have hS : ‖ent (cplx (SigU (n := Fin N) Sig)) (vbar Sig x) (eI p)‖ ≤ testNorm x := by
    have hTS : (SigU (n := Fin N) Sig)ᵀ = SigU (n := Fin N) Sig := by
      rw [SigU, fromBlocks_transpose, hT]; simp
    have hSv : SigU (n := Fin N) Sig *ᵥ vbar Sig x = x := by
      have hS' : Sig * Sig⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hSig.isUnit)
      funext s
      rcases s with j | ν
      · simp [SigU, vbar, fromBlocks_mulVec, mulVec_mulVec, hS']
      · simp [SigU, vbar, fromBlocks_mulVec]
    have hC : (cplx (SigU (n := Fin N) Sig))ᵀ = cplx (SigU (n := Fin N) Sig) := by
      rw [cplx, ← transpose_map, hTS]
    have e : ent (cplx (SigU (n := Fin N) Sig)) (vbar Sig x) (eI p) = (x p : ℂ) := by
      rw [← chainR_ent_transpose, hC, chainR_ent_eI_left]
      conv_rhs => rw [← hSv]
      simp [cplx, mulVec, dotProduct, Complex.ofReal_sum]
    rw [e, Complex.norm_real, Real.norm_eq_abs]
    exact chainR_abs_le_testNorm x p
  calc ‖ent (G Sig A z) (vbar Sig x) (eI p)‖
      = ‖(ent (G Sig A z) (vbar Sig x) (eI p) +
          ent (cplx (SigU (n := Fin N) Sig)) (vbar Sig x) (eI p)) -
          ent (cplx (SigU (n := Fin N) Sig)) (vbar Sig x) (eI p)‖ := by rw [add_sub_cancel_right]
    _ ≤ _ := (norm_sub_le _ _).trans (add_le_add h hS)


/-- The setting of §7 gives the density assumptions on the eigenvalues of `Σ` (Lemma 4.10
input). -/
private theorem chainR_density {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) : DensityAssumptions τ N (specOf Sig) :=
  (IsModel.diagModel_specOf (Ω := GaussSpace M N)
    ⟨hset.ratio_ge, hset.ratio_le, (gaussX_isGaussianEnsemble M N).entryAssumption hN,
      hset.sigma⟩).densityAssumptions hset.pos

private theorem chainR_testNorm_eI {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι) :
    testNorm (eI p) = 1 := by
  unfold testNorm
  simp [eI, Pi.single_apply, Finset.sum_ite_eq']


/-- `‖A‖_F² = ∑_{jν} A_{jν}²`. -/
private def chainSq (A : Matrix (Fin M) (Fin N) ℝ) : ℝ := ∑ α : Fin M × Fin N, A α.1 α.2 ^ 2

private theorem chainSq_nonneg (A : Matrix (Fin M) (Fin N) ℝ) : 0 ≤ chainSq A :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Replacing one entry by `s` raises `‖A‖_F²` by at most `s²`. -/
private theorem chainSq_Xupd_le (A : Matrix (Fin M) (Fin N) ℝ) (i : Fin M) (μ : Fin N) (s : ℝ) :
    chainSq (Xupd A i μ s) ≤ chainSq A + s ^ 2 := by
  unfold chainSq
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (i, μ)),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ (i, μ))]
  have h : ∑ α ∈ Finset.univ.erase (i, μ), Xupd A i μ s α.1 α.2 ^ 2 =
      ∑ α ∈ Finset.univ.erase (i, μ), A α.1 α.2 ^ 2 := by
    refine Finset.sum_congr rfl fun α hα => ?_
    have hne : α ≠ (i, μ) := Finset.ne_of_mem_erase hα
    have : ¬ (α.1 = i ∧ α.2 = μ) := fun h => hne (Prod.ext h.1 h.2)
    simp [Xupd, this]
  rw [h]
  simp only [Xupd, and_self, ite_true]
  nlinarith [sq_nonneg (A i μ)]

/-- `1 ≤ N η` on `𝐃(τ, N)`. -/
private theorem chain_one_le_N_im {τ : ℝ} {z : ℂ} (hN : 1 ≤ N) (hτ : 0 < τ)
    (hz : z ∈ specDomain τ N) : 1 ≤ (N : ℝ) * z.im := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have h1 : (N : ℝ) * (N : ℝ) ^ (-1 + τ) = (N : ℝ) ^ τ := by
    rw [mul_comm, ← Real.rpow_add_one hNp.ne']; ring_nf
  have h2 : 1 ≤ (N : ℝ) ^ τ := Real.one_le_rpow hN1r hτ.le
  calc (1 : ℝ) ≤ (N : ℝ) ^ τ := h2
    _ = (N : ℝ) * (N : ℝ) ^ (-1 + τ) := h1.symm
    _ ≤ (N : ℝ) * z.im := mul_le_mul_of_nonneg_left hz.2.2.2.1 hNp.le

/-- `Ψ ≥ 1/(Nη) ≥ τ/N` on `𝐃(τ, N)`. -/
private theorem chain_Psi_ge {τ : ℝ} {σ : Fin M → ℝ} {z : ℂ} (hN : 1 ≤ N) (hτ : 0 < τ)
    (hz : z ∈ specDomain τ N) : τ / N ≤ Psi N σ z := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hη : 0 < z.im := hz.1
  have hητ : z.im ≤ τ⁻¹ := hz.2.2.2.2
  unfold Psi
  have h1 : τ / N ≤ 1 / (N * z.im) := by
    rw [div_le_div_iff₀ hNp (by positivity), one_mul]
    calc τ * (N * z.im) ≤ τ * (N * τ⁻¹) := by gcongr
      _ = N := by field_simp
  linarith [Real.sqrt_nonneg ((mFun N σ z).im / (N * z.im))]

private theorem chain_continuous_G {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {z : ℂ}
    (hz : 0 < z.im) : Continuous fun A : Matrix (Fin M) (Fin N) ℝ => G Sig A z := by
  have hc : Continuous fun A : Matrix (Fin M) (Fin N) ℝ => linH Sig⁻¹ A z := by
    unfold linH cplx
    refine Continuous.matrix_fromBlocks continuous_const ?_ ?_ continuous_const
    · exact Continuous.matrix_map continuous_id Complex.continuous_ofReal
    · exact Continuous.matrix_map continuous_id.matrix_transpose Complex.continuous_ofReal
  have h : (fun A : Matrix (Fin M) (Fin N) ℝ => G Sig A z) =
      fun A => (linH Sig⁻¹ A z).det⁻¹ • (linH Sig⁻¹ A z).adjugate := by
    funext A
    change (linH Sig⁻¹ A z)⁻¹ = _
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  refine Continuous.smul ((hc.matrix_det).inv₀ fun A => ?_) hc.matrix_adjugate
  exact ((isUnit_iff_isUnit_det _).1 (H_isUnit hSig A hz)).ne_zero

private theorem chain_continuous_ent {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    Continuous fun B : Matrix ι ι ℂ => ent B x y := by
  have : (fun B : Matrix ι ι ℂ => ent B x y) =
      fun B => ∑ s, ∑ t, (x s : ℂ) * B s t * (y t : ℂ) := funext fun B => chainR_ent_eq B x y
  rw [this]
  exact continuous_finsetSum _ fun s _ => continuous_finsetSum _ fun t _ =>
    (continuous_const.mul (continuous_id.matrix_elem s t)).mul continuous_const

private theorem chain_continuous_Xupd (i : Fin M) (μ : Fin N) :
    Continuous fun q : Matrix (Fin M) (Fin N) ℝ × ℝ => Xupd q.1 i μ q.2 := by
  refine continuous_pi fun j => continuous_pi fun ν => ?_
  simp only [Xupd]
  split_ifs
  · exact continuous_snd
  · exact continuous_fst.matrix_elem j ν

private theorem chain_continuous_resCoeff {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    {z : ℂ} (hz : 0 < z.im) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) (k : ℕ) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => resCoeff Sig A z v i μ k := by
  have hG := chain_continuous_G (N := N) hSig hz
  unfold resCoeff
  refine continuous_const.mul ((chain_continuous_ent _ _).comp ?_)
  exact (hG.matrix_mul ((continuous_const.matrix_mul hG).pow k)).sub continuous_const

private theorem chain_continuous_fCoeff {X : Type*} [TopologicalSpace X] (p n : ℕ)
    {a : X → ℕ → ℂ} (ha : ∀ k, Continuous fun x => a x k) :
    Continuous fun x => fCoeff p (a x) n := by
  unfold fCoeff
  refine continuous_finsetSum _ fun κ _ => continuous_finsetProd _ fun r _ => ?_
  split_ifs
  · exact ha _
  · exact Complex.continuous_conj.comp (ha _)


private theorem chain_hp_mono {Ω : Type*} [MeasureSpace Ω] {N : ℕ} {D : ℝ} {A B : Set Ω}
    (h : A ⊆ B) (hA : HighProbAt N D A) : HighProbAt N D B :=
  (measure_mono (Set.compl_subset_compl.2 h)).trans hA

private theorem chain_le_rpow {K a : ℝ} (hK : 0 ≤ K) (ha : 0 < a) {N : ℕ}
    (hN : ⌈K ^ a⁻¹⌉₊ ≤ N) : K ≤ (N : ℝ) ^ a := by
  have h1 : K ^ a⁻¹ ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  calc K = (K ^ a⁻¹) ^ a := by rw [← Real.rpow_mul hK, inv_mul_cancel₀ ha.ne', Real.rpow_one]
    _ ≤ (N : ℝ) ^ a := Real.rpow_le_rpow (by positivity) h1 ha.le

private theorem chain_pow_three_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (q : ℕ) :
    (a + b + c) ^ q ≤ 4 ^ q * (a ^ q + b ^ q + c ^ q) := by
  have h1 := add_pow_le (add_nonneg ha hb) hc q
  have h2 := add_pow_le ha hb q
  have h3 : (2 : ℝ) ^ (q - 1) ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) (Nat.sub_le q 1)
  have h4 : (4 : ℝ) ^ q = 2 ^ q * 2 ^ q := by rw [← mul_pow]; norm_num
  have h5 : (1 : ℝ) ≤ 2 ^ q := one_le_pow₀ (by norm_num)
  have hab : 0 ≤ a ^ q + b ^ q := by positivity
  have hc' : 0 ≤ c ^ q := by positivity
  have hq0 : (0 : ℝ) ≤ 2 ^ (q - 1) := by positivity
  have h6 : (a + b) ^ q ≤ 2 ^ q * (a ^ q + b ^ q) :=
    h2.trans (mul_le_mul_of_nonneg_right h3 hab)
  have h7 : (a + b) ^ q + c ^ q ≤ 2 ^ q * (a ^ q + b ^ q + c ^ q) := by nlinarith
  calc (a + b + c) ^ q ≤ 2 ^ (q - 1) * ((a + b) ^ q + c ^ q) := h1
    _ ≤ 2 ^ q * (2 ^ q * (a ^ q + b ^ q + c ^ q)) :=
        mul_le_mul h3 h7 (by positivity) (by positivity)
    _ = 4 ^ q * (a ^ q + b ^ q + c ^ q) := by rw [h4]; ring

/-- The moment constant `4^q (2 + τ^{−q}) (1 + C'_{2q})`. -/
private def chainKW (τ : ℝ) (C : ℕ → ℝ) (q : ℕ) : ℝ :=
  4 ^ q * (2 + τ⁻¹ ^ q) * (1 + max (C (2 * q)) 0)

/-- Moments of `W = 1 + ‖X‖_F² + y²`: `E W^q ≤ 4^q (2 + τ^{−q}) (1 + C'_{2q}) N^{2q}`. -/
private theorem chain_moment_W {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {τ : ℝ} (hτ : 0 < τ) {C : ℕ → ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ} {y : Ω → ℝ}
    (hX : EntryAssumption C X) (hy : Measurable y)
    (hym : ∀ q : ℕ, Integrable (fun ω => |Real.sqrt N * y ω| ^ q) ∧
      ∫ ω, |Real.sqrt N * y ω| ^ q ≤ C q)
    (hN : 1 ≤ N) (hM : (M : ℝ) ≤ τ⁻¹ * N) (q : ℕ) :
    Integrable (fun ω => (1 + chainSq (X ω) + y ω ^ 2) ^ q) ∧
      ∫ ω, (1 + chainSq (X ω) + y ω ^ 2) ^ q ≤ chainKW τ C q * (N : ℝ) ^ (2 * q) := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · refine ⟨by simp, ?_⟩
    simp only [pow_zero, integral_const, probReal_univ, smul_eq_mul, mul_one, mul_zero]
    unfold chainKW
    have : 0 ≤ max (C (2 * 0)) 0 := le_max_right _ _
    simp only [pow_zero, one_mul]
    nlinarith
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  set C' := max (C (2 * (n + 1))) 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hpow : ∀ t : ℝ, (t ^ 2) ^ (n + 1) =
      ((N : ℝ) ^ (n + 1))⁻¹ * |Real.sqrt N * t| ^ (2 * (n + 1)) := by
    intro t
    rw [pow_mul, sq_abs, mul_pow, Real.sq_sqrt hNp.le, mul_pow, ← mul_assoc,
      inv_mul_cancel₀ (pow_pos hNp _).ne', one_mul]
  have hXi : ∀ α : Fin M × Fin N, Integrable fun ω => (X ω α.1 α.2 ^ 2) ^ (n + 1) := by
    intro α
    simp_rw [hpow]
    exact (hX.integrable_moment (2 * (n + 1)) α.1 α.2).const_mul _
  have hXle : ∀ α : Fin M × Fin N,
      ∫ ω, (X ω α.1 α.2 ^ 2) ^ (n + 1) ≤ ((N : ℝ) ^ (n + 1))⁻¹ * C' := by
    intro α
    simp_rw [hpow]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left ((hX.moment (2 * (n + 1)) α.1 α.2).trans (le_max_left _ _))
      (by positivity)
  have hyi : Integrable fun ω => (y ω ^ 2) ^ (n + 1) := by
    simp_rw [hpow]
    exact (hym (2 * (n + 1))).1.const_mul _
  have hyle : ∫ ω, (y ω ^ 2) ^ (n + 1) ≤ ((N : ℝ) ^ (n + 1))⁻¹ * C' := by
    simp_rw [hpow]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left ((hym (2 * (n + 1))).2.trans (le_max_left _ _))
      (by positivity)
  set cd : ℝ := ((Finset.univ : Finset (Fin M × Fin N)).card : ℝ) with hcd
  have hcdMN : cd = (M : ℝ) * N := by
    rw [hcd, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    push_cast; ring
  have hcd0 : 0 ≤ cd := by rw [hcdMN]; positivity
  have hSi : Integrable fun ω => ∑ α : Fin M × Fin N, (X ω α.1 α.2 ^ 2) ^ (n + 1) :=
    integrable_finsetSum _ fun α _ => hXi α
  have hSi' : Integrable fun ω => cd ^ n * ∑ α : Fin M × Fin N, (X ω α.1 α.2 ^ 2) ^ (n + 1) :=
    hSi.const_mul _
  have h1i : Integrable fun ω => 1 + cd ^ n * ∑ α : Fin M × Fin N, (X ω α.1 α.2 ^ 2) ^ (n + 1) :=
    (integrable_const _).add hSi'
  have h2i : Integrable fun ω =>
      1 + cd ^ n * (∑ α : Fin M × Fin N, (X ω α.1 α.2 ^ 2) ^ (n + 1)) + (y ω ^ 2) ^ (n + 1) :=
    h1i.add hyi
  set g : Ω → ℝ := fun ω => 4 ^ (n + 1) * (1 + cd ^ n * (∑ α : Fin M × Fin N,
      (X ω α.1 α.2 ^ 2) ^ (n + 1)) + (y ω ^ 2) ^ (n + 1)) with hg
  have hgi : Integrable g := h2i.const_mul _
  have hle : ∀ ω, (1 + chainSq (X ω) + y ω ^ 2) ^ (n + 1) ≤ g ω := by
    intro ω
    have h1 := chain_pow_three_le zero_le_one (chainSq_nonneg (X ω)) (sq_nonneg (y ω)) (n + 1)
    have h2 : chainSq (X ω) ^ (n + 1) ≤ cd ^ n * ∑ α : Fin M × Fin N, (X ω α.1 α.2 ^ 2) ^ (n + 1) :=
      pow_sum_le_card_mul_sum_pow (fun _ _ => sq_nonneg _) n
    calc _ ≤ _ := h1
      _ ≤ g ω := by
          simp only [hg, one_pow]
          gcongr
  have hmeas : Measurable fun ω => (1 + chainSq (X ω) + y ω ^ 2) ^ (n + 1) := by
    unfold chainSq
    refine ((measurable_const.add (Finset.measurable_sum _ fun α _ =>
      (hX.measurable α.1 α.2).pow_const 2)).add (hy.pow_const 2)).pow_const _
  have hWi : Integrable fun ω => (1 + chainSq (X ω) + y ω ^ 2) ^ (n + 1) :=
    hgi.mono' hmeas.aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (by have := chainSq_nonneg (X ω); positivity)]; exact hle ω)
  refine ⟨hWi, ?_⟩
  have hgval : ∫ ω, g ω = 4 ^ (n + 1) * (1 + cd ^ n * (∑ α : Fin M × Fin N,
      ∫ ω, (X ω α.1 α.2 ^ 2) ^ (n + 1)) + ∫ ω, (y ω ^ 2) ^ (n + 1)) := by
    rw [hg, integral_const_mul, integral_add h1i hyi, integral_add (integrable_const _) hSi',
      integral_const_mul, integral_finsetSum _ fun α _ => hXi α]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hsum : ∑ α : Fin M × Fin N, ∫ ω, (X ω α.1 α.2 ^ 2) ^ (n + 1) ≤
      cd * (((N : ℝ) ^ (n + 1))⁻¹ * C') := by
    calc _ ≤ ∑ _α : Fin M × Fin N, ((N : ℝ) ^ (n + 1))⁻¹ * C' :=
          Finset.sum_le_sum fun α _ => hXle α
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hM1 : cd ^ n * (cd * (((N : ℝ) ^ (n + 1))⁻¹ * C')) = (M : ℝ) ^ (n + 1) * C' := by
    rw [hcdMN]
    field_simp
    ring
  have hM2 : (M : ℝ) ^ (n + 1) ≤ τ⁻¹ ^ (n + 1) * (N : ℝ) ^ (n + 1) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) hM _
  have hNn : (1 : ℝ) ≤ (N : ℝ) ^ (n + 1) := one_le_pow₀ hN1r
  have hN2 : (N : ℝ) ^ (2 * (n + 1)) = (N : ℝ) ^ (n + 1) * (N : ℝ) ^ (n + 1) := by
    rw [two_mul, pow_add]
  have hyC : ((N : ℝ) ^ (n + 1))⁻¹ * C' ≤ C' :=
    mul_le_of_le_one_left hC'0 (inv_le_one_of_one_le₀ hNn)
  have hτn : 0 ≤ τ⁻¹ ^ (n + 1) := by positivity
  calc ∫ ω, (1 + chainSq (X ω) + y ω ^ 2) ^ (n + 1) ≤ ∫ ω, g ω := integral_mono hWi hgi hle
    _ ≤ 4 ^ (n + 1) * (1 + τ⁻¹ ^ (n + 1) * (N : ℝ) ^ (n + 1) * C' + C') := by
        rw [hgval]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have := mul_le_mul_of_nonneg_left hsum (pow_nonneg hcd0 n)
        rw [hM1] at this
        have h5 := mul_le_mul_of_nonneg_right hM2 hC'0
        linarith [hyle, hyC]
    _ ≤ chainKW τ C (n + 1) * (N : ℝ) ^ (2 * (n + 1)) := by
        unfold chainKW
        rw [← hC', hN2]
        have h4 : (0 : ℝ) ≤ 4 ^ (n + 1) := by positivity
        have hA : 1 + τ⁻¹ ^ (n + 1) * (N : ℝ) ^ (n + 1) * C' + C' ≤
            (2 + τ⁻¹ ^ (n + 1)) * (1 + C') * ((N : ℝ) ^ (n + 1) * (N : ℝ) ^ (n + 1)) := by
          have hNN : (N : ℝ) ^ (n + 1) ≤ (N : ℝ) ^ (n + 1) * (N : ℝ) ^ (n + 1) :=
            le_mul_of_one_le_left (by positivity) hNn
          have hNN1 : (1 : ℝ) ≤ (N : ℝ) ^ (n + 1) * (N : ℝ) ^ (n + 1) := by nlinarith
          nlinarith [mul_nonneg hτn hC'0, mul_nonneg (mul_nonneg hτn hC'0) (sub_nonneg.2 hNN)]
        calc 4 ^ (n + 1) * (1 + τ⁻¹ ^ (n + 1) * (N : ℝ) ^ (n + 1) * C' + C') ≤
            4 ^ (n + 1) * ((2 + τ⁻¹ ^ (n + 1)) * (1 + C') *
              ((N : ℝ) ^ (n + 1) * (N : ℝ) ^ (n + 1))) := mul_le_mul_of_nonneg_left hA h4
          _ = _ := by ring

/-- `|y| ≤ N^{ε − 1/2}` with probability `≥ 1 − N^{−D}`, from the moments of `√N y` (Markov). -/
private theorem chain_markov (C : ℕ → ℝ) (ε D : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (y : Ω → ℝ), (∀ q : ℕ, Integrable (fun ω => |Real.sqrt N * y ω| ^ q) ∧
        ∫ ω, |Real.sqrt N * y ω| ^ q ≤ C q) →
      HighProbAt N D {ω | |y ω| ≤ (N : ℝ) ^ (ε - 1 / 2)} := by
  set q : ℕ := ⌈2 * max D 0 / ε⌉₊ + 1 with hq
  set Cq := max (C q) 1 with hCq
  refine ⟨max 1 ⌈Cq ^ (ε / 2)⁻¹⌉₊, fun N hN Ω _ _ y hy => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hN
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : (0 : ℝ) < N := by linarith
  have hCqN : Cq ≤ (N : ℝ) ^ (ε / 2) :=
    chain_le_rpow (zero_le_one.trans (le_max_right _ _)) (by positivity)
      (le_trans (le_max_right _ _) hN)
  have hq1 : 2 * max D 0 / ε ≤ (q : ℝ) := by
    rw [hq]; push_cast
    linarith [Nat.le_ceil (2 * max D 0 / ε)]
  have hp : D ≤ (ε - ε / 2) * q := by
    calc D ≤ max D 0 := le_max_left _ _
      _ = (ε - ε / 2) * (2 * max D 0 / ε) := by field_simp; ring
      _ ≤ (ε - ε / 2) * q := mul_le_mul_of_nonneg_left hq1 (by linarith)
  have hNe1 : 1 ≤ (N : ℝ) ^ (ε / 2) := Real.one_le_rpow hN1r (by positivity)
  have hmom : ∫ ω, |Real.sqrt N * y ω| ^ q ≤ ((N : ℝ) ^ (ε / 2) * 1) ^ q := by
    rw [mul_one]
    calc ∫ ω, |Real.sqrt N * y ω| ^ q ≤ C q := (hy q).2
      _ ≤ Cq := le_max_left _ _
      _ ≤ (N : ℝ) ^ (ε / 2) := hCqN
      _ ≤ ((N : ℝ) ^ (ε / 2)) ^ q := le_self_pow₀ hNe1 (by omega)
  have hd := DomAt.of_moment (ε := ε / 2) (ε' := ε) (D := D) (ζ := 1)
    (ξ := fun ω => |Real.sqrt N * y ω|) q hN1 hp (fun ω => abs_nonneg _) one_pos
    (hy q).1 hmom
  unfold DomAt at hd
  unfold HighProbAt
  refine le_trans (measure_mono fun ω hω => ?_) hd
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω ⊢
  have hsq : Real.sqrt N = (N : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have hsq0 : 0 < Real.sqrt N := Real.sqrt_pos.2 hNp
  rw [abs_mul, abs_of_pos hsq0, mul_one]
  have e : (N : ℝ) ^ ε = Real.sqrt N * (N : ℝ) ^ (ε - 1 / 2) := by
    rw [hsq, ← Real.rpow_add hNp]; ring_nf
  rw [e]
  exact mul_lt_mul_of_pos_left hω hsq0

private theorem chain_abs_le_of_mem_uIcc {s t : ℝ} (hs : s ∈ Set.uIcc 0 t) : |s| ≤ |t| := by
  rcases Set.mem_uIcc.1 hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]; exact h2
  · rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]; linarith

private theorem chain_measurable_Xupd (i : Fin M) (μ : Fin N) (t : ℝ) :
    Measurable fun A : Matrix (Fin M) (Fin N) ℝ => Xupd A i μ t :=
  (chain_continuous_Xupd i μ).measurable.comp (measurable_id.prodMk measurable_const)

private theorem chain_integral_ofReal_pow {Ω : Type} [MeasureSpace Ω] (y : Ω → ℝ) (k : ℕ) :
    ∫ ω, (y ω : ℂ) ^ k = ((∫ ω, y ω ^ k : ℝ) : ℂ) := by
  simp_rw [← Complex.ofReal_pow]
  exact integral_complex_ofReal

private theorem chain_indep_entry {Ω : Type} [MeasureSpace Ω] {C : ℕ → ℝ}
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) (i : Fin M) (μ : Fin N) :
    IndepFun (fun ω => Xupd (X ω) i μ 0) (fun ω => X ω i μ) := by
  set T : Finset (Fin M × Fin N) := {(i, μ)} with hT
  set S : Finset (Fin M × Fin N) := Finset.univ.erase (i, μ) with hS
  have hST : Disjoint S T := by
    rw [hS, hT, Finset.disjoint_singleton_right]
    exact Finset.notMem_erase _ _
  have h := hX.indep.indepFun_finset S T hST (fun q => hX.measurable q.1 q.2)
  let φ : (S → ℝ) → Matrix (Fin M) (Fin N) ℝ :=
    fun x j ν => if hj : (j, ν) ∈ S then x ⟨(j, ν), hj⟩ else 0
  let ψ : (T → ℝ) → ℝ := fun x => x ⟨(i, μ), Finset.mem_singleton_self _⟩
  have hφ : Measurable φ := by
    refine measurable_pi_iff.2 fun j => measurable_pi_iff.2 fun ν => ?_
    by_cases hj : (j, ν) ∈ S
    · simp only [φ, hj, ↓reduceDIte]; exact measurable_pi_apply _
    · simp only [φ, hj, ↓reduceDIte]; exact measurable_const
  have hψ : Measurable ψ := measurable_pi_apply _
  have h2 := h.comp hφ hψ
  have e1 : (φ ∘ fun a (q : S) => X a (q : Fin M × Fin N).1 (q : Fin M × Fin N).2) =
      fun ω => Xupd (X ω) i μ 0 := by
    funext ω j ν
    simp only [Function.comp, φ, Xupd, hS, Finset.mem_erase, Finset.mem_univ, and_true, ne_eq,
      Prod.mk.injEq]
    by_cases h' : j = i ∧ ν = μ
    · simp [h']
    · simp [h']
  have e2 : (ψ ∘ fun a (q : T) => X a (q : Fin M × Fin N).1 (q : Fin M × Fin N).2) =
      fun ω => X ω i μ := rfl
  rw [e1, e2] at h2
  exact h2

/-- `|E ξ^k| ≤ N^{−k/2} C'_k` for `ξ = X_{iμ}`. -/
private theorem chain_moment_entry {Ω : Type} [MeasureSpace Ω] {C : ℕ → ℝ}
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) (hN : 1 ≤ N)
    (i : Fin M) (μ : Fin N) (k : ℕ) :
    ‖∫ ω, (X ω i μ : ℂ) ^ k‖ ≤ (N : ℝ) ^ (-(k : ℝ) / 2) * max (C k) 0 := by
  have hNp : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNp
  have e : ∀ x : ℝ, ‖(x : ℂ) ^ k‖ = (N : ℝ) ^ (-(k : ℝ) / 2) * |Real.sqrt N * x| ^ k := by
    intro x
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hs, mul_pow,
      ← mul_assoc]
    have : (N : ℝ) ^ (-(k : ℝ) / 2) * Real.sqrt N ^ k = 1 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hNp.le, ← Real.rpow_add hNp,
        show -(k : ℝ) / 2 + 1 / 2 * k = 0 by ring, Real.rpow_zero]
    rw [this, one_mul]
  calc ‖∫ ω, (X ω i μ : ℂ) ^ k‖ ≤ ∫ ω, ‖(X ω i μ : ℂ) ^ k‖ := norm_integral_le_integral_norm _
    _ = (N : ℝ) ^ (-(k : ℝ) / 2) * ∫ ω, |Real.sqrt N * X ω i μ| ^ k := by
        simp_rw [e]; exact integral_const_mul _ _
    _ ≤ (N : ℝ) ^ (-(k : ℝ) / 2) * max (C k) 0 :=
        mul_le_mul_of_nonneg_left ((hX.moment k i μ).trans (le_max_left _ _)) (by positivity)

private theorem chain_sc_mul {N : ℕ} (hN : 1 ≤ N) (n k : ℕ) :
    (N : ℝ) ^ (-(n : ℝ) / 2) * (N : ℝ) ^ (-(k : ℝ) / 2) = (N : ℝ) ^ (-((n + k : ℕ) : ℝ) / 2) := by
  have hNp : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  rw [← Real.rpow_add hNp]; push_cast; ring_nf

/-- One step of (Taylo_id1) after scaling: from `b = ∑_{k ≤ 4p−n} C(n+k, n) m_k a_{n+k} + e`,
`m_0 = 1`, `|m_k| ≤ N^{−k/2} C'_k`, `C(n+k, n) C'_k ≤ L`:
`N^{−n/2}|a_n| ≤ N^{−n/2}|b| + L ∑_{k < 4p−n} N^{−(n+k+1)/2}|a_{n+k+1}| + N^{−n/2}|e|`. -/
private theorem chain_recur_pair {N : ℕ} (hN : 1 ≤ N) {p n : ℕ} (a : ℕ → ℂ) (b e : ℂ)
    (m : ℕ → ℂ) (Cm : ℕ → ℝ) (L : ℝ)
    (hid : b = (∑ k ∈ Finset.range (4 * p - n + 1), ((n + k).choose n : ℂ) * m k * a (n + k)) + e)
    (hm0 : m 0 = 1) (hm : ∀ k, ‖m k‖ ≤ (N : ℝ) ^ (-(k : ℝ) / 2) * Cm k)
    (hL : ∀ k, k ≤ 4 * p - n → ((n + k).choose n : ℝ) * Cm k ≤ L) :
    (N : ℝ) ^ (-(n : ℝ) / 2) * ‖a n‖ ≤ (N : ℝ) ^ (-(n : ℝ) / 2) * ‖b‖ +
      L * ∑ k ∈ Finset.range (4 * p - n),
        (N : ℝ) ^ (-((n + k + 1 : ℕ) : ℝ) / 2) * ‖a (n + k + 1)‖ +
      (N : ℝ) ^ (-(n : ℝ) / 2) * ‖e‖ := by
  have hNp : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  set sc : ℝ := (N : ℝ) ^ (-(n : ℝ) / 2) with hsc
  have hsc0 : 0 ≤ sc := Real.rpow_nonneg hNp.le _
  rw [Finset.sum_range_succ'] at hid
  simp only [add_zero, Nat.choose_self, Nat.cast_one, one_mul, hm0] at hid
  have ha : a n = b - (∑ k ∈ Finset.range (4 * p - n),
      ((n + (k + 1)).choose n : ℂ) * m (k + 1) * a (n + (k + 1))) - e := by
    rw [hid]; ring
  have hterm : ∀ k ∈ Finset.range (4 * p - n),
      sc * ‖((n + (k + 1)).choose n : ℂ) * m (k + 1) * a (n + (k + 1))‖ ≤
        L * ((N : ℝ) ^ (-((n + k + 1 : ℕ) : ℝ) / 2) * ‖a (n + k + 1)‖) := by
    intro k hk
    have hk' : k + 1 ≤ 4 * p - n := Finset.mem_range.1 hk
    rw [norm_mul, norm_mul, Complex.norm_natCast]
    have h1 := hm (k + 1)
    have h2 := hL (k + 1) hk'
    have hcm : 0 ≤ Cm (k + 1) := by
      have := (norm_nonneg _).trans h1
      exact nonneg_of_mul_nonneg_right this (Real.rpow_pos_of_pos hNp _)
    have e3 : sc * (N : ℝ) ^ (-((k + 1 : ℕ) : ℝ) / 2) =
        (N : ℝ) ^ (-((n + k + 1 : ℕ) : ℝ) / 2) := by
      rw [hsc, chain_sc_mul hN n (k + 1), Nat.add_assoc]
    rw [show n + (k + 1) = n + k + 1 by ring]
    have hA0 : 0 ≤ ‖a (n + k + 1)‖ := norm_nonneg _
    calc sc * (((n + k + 1).choose n : ℝ) * ‖m (k + 1)‖ * ‖a (n + k + 1)‖)
        ≤ sc * (((n + k + 1).choose n : ℝ) * ((N : ℝ) ^ (-((k + 1 : ℕ) : ℝ) / 2) * Cm (k + 1)) *
            ‖a (n + k + 1)‖) := by gcongr
      _ = (((n + k + 1).choose n : ℝ) * Cm (k + 1)) *
            ((sc * (N : ℝ) ^ (-((k + 1 : ℕ) : ℝ) / 2)) * ‖a (n + k + 1)‖) := by ring
      _ ≤ L * ((N : ℝ) ^ (-((n + k + 1 : ℕ) : ℝ) / 2) * ‖a (n + k + 1)‖) := by
          rw [e3]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [show n + k + 1 = n + (k + 1) by ring]; exact h2
  rw [ha]
  calc sc * ‖b - (∑ k ∈ Finset.range (4 * p - n),
        ((n + (k + 1)).choose n : ℂ) * m (k + 1) * a (n + (k + 1))) - e‖
      ≤ sc * (‖b‖ + ∑ k ∈ Finset.range (4 * p - n),
          ‖((n + (k + 1)).choose n : ℂ) * m (k + 1) * a (n + (k + 1))‖ + ‖e‖) := by
        refine mul_le_mul_of_nonneg_left ?_ hsc0
        exact (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
          (add_le_add le_rfl (norm_sum_le _ _))) le_rfl)
    _ = sc * ‖b‖ + ∑ k ∈ Finset.range (4 * p - n),
          sc * ‖((n + (k + 1)).choose n : ℂ) * m (k + 1) * a (n + (k + 1))‖ + sc * ‖e‖ := by
        rw [mul_add, mul_add, Finset.mul_sum]
    _ ≤ sc * ‖b‖ + ∑ k ∈ Finset.range (4 * p - n),
          L * ((N : ℝ) ^ (-((n + k + 1 : ℕ) : ℝ) / 2) * ‖a (n + k + 1)‖) + sc * ‖e‖ := by
        exact add_le_add (add_le_add le_rfl (Finset.sum_le_sum hterm)) le_rfl
    _ = _ := by rw [← Finset.mul_sum]

/-- The downward induction of Lemma 7.16: from
`α_n ≤ B' + L ∑_{k < 4p−n} α_{n+k+1}` for `n ∈ [3, 4p]`, `α_n ≤ (1 + 4pL)^{4p−n} B'`. -/
private theorem chain_induct {p : ℕ} (α : ℕ → ℝ) {L B' : ℝ} (hL : 0 ≤ L) (hB' : 0 ≤ B')
    (hrec : ∀ n, 3 ≤ n → n ≤ 4 * p →
      α n ≤ B' + L * ∑ k ∈ Finset.range (4 * p - n), α (n + k + 1)) :
    ∀ n, 3 ≤ n → n ≤ 4 * p → α n ≤ (1 + 4 * p * L) ^ (4 * p - n) * B' := by
  set Q : ℝ := 1 + 4 * p * L with hQ
  have hQ1 : 1 ≤ Q := by
    have : (0 : ℝ) ≤ 4 * p * L := by positivity
    linarith
  suffices H : ∀ j, ∀ n, 3 ≤ n → n ≤ 4 * p → 4 * p - n = j → α n ≤ Q ^ j * B' from
    fun n h4 hn => H _ n h4 hn rfl
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro n h4 hn hj
    have hsum : ∑ k ∈ Finset.range (4 * p - n), α (n + k + 1) ≤
        ∑ _k ∈ Finset.range (4 * p - n), Q ^ (j - 1) * B' := by
      refine Finset.sum_le_sum fun k hk => ?_
      have hk' := Finset.mem_range.1 hk
      have h1 := ih (j - k - 1) (by omega) (n + k + 1) (by omega) (by omega) (by omega)
      exact h1.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hQ1 (by omega)) hB')
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    have hrn := hrec n h4 hn
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · have : 4 * p - n = 0 := hj
      rw [this, Finset.sum_range_zero, mul_zero, add_zero] at hrn
      simpa using hrn
    · have hcnt : ((4 * p - n : ℕ) : ℝ) ≤ 4 * p := by
        have : 4 * p - n ≤ 4 * p := Nat.sub_le _ _
        exact_mod_cast this
      have hQj : B' ≤ Q ^ (j - 1) * B' := le_mul_of_one_le_left hB' (one_le_pow₀ hQ1)
      have hQ0 : 0 ≤ Q ^ (j - 1) * B' := by positivity
      have hpow : Q ^ j = Q ^ (j - 1) * Q := by
        rw [← pow_succ]; congr 1; omega
      calc α n ≤ B' + L * (((4 * p - n : ℕ) : ℝ) * (Q ^ (j - 1) * B')) :=
            hrn.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum hL))
        _ ≤ Q ^ (j - 1) * B' + L * (4 * p * (Q ^ (j - 1) * B')) := by gcongr
        _ = Q ^ j * B' := by rw [hpow, hQ]; ring

/-- The constant `L = 2^{4p} ∑_{k ≤ 4p} C'_k` of Lemma 7.16. -/
private def chainL (C : ℕ → ℝ) (p : ℕ) : ℝ :=
  2 ^ (4 * p) * ∑ k ∈ Finset.range (4 * p + 1), max (C k) 0

private theorem chainL_nonneg (C : ℕ → ℝ) (p : ℕ) : 0 ≤ chainL C p := by
  unfold chainL
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => le_max_right _ _)

private theorem chainL_ge {C : ℕ → ℝ} {p n k : ℕ} (hnk : n + k ≤ 4 * p) :
    ((n + k).choose n : ℝ) * max (C k) 0 ≤ chainL C p := by
  unfold chainL
  have h1 : ((n + k).choose n : ℝ) ≤ 2 ^ (4 * p) := by
    have := Nat.choose_le_two_pow (n + k) n
    have h2 : 2 ^ (n + k) ≤ 2 ^ (4 * p) := Nat.pow_le_pow_right (by norm_num) hnk
    exact_mod_cast this.trans h2
  have h3 : max (C k) 0 ≤ ∑ j ∈ Finset.range (4 * p + 1), max (C j) 0 :=
    Finset.single_le_sum (f := fun j => max (C j) 0) (fun j _ => le_max_right _ _)
      (Finset.mem_range.2 (by omega))
  exact mul_le_mul h1 h3 (le_max_right _ _) (by positivity)

/-! ## `F̃` at `v = e_ν`: entry bounds give coefficient bounds -/

/-- `v̄ = e_ν` for `v = e_ν`, `ν ∈ 𝓘_N`. -/
private theorem chain_vbar_inr (Sig : Matrix (Fin M) (Fin M) ℝ) (ν : Fin N) :
    vbar Sig (eI (Sum.inr ν) : Fin M ⊕ Fin N → ℝ) = eI (Sum.inr ν) := by
  funext s
  rcases s with i | j
  · have h0 : ((eI (Sum.inr ν) : Fin M ⊕ Fin N → ℝ) ∘ Sum.inl) = 0 := by
      funext k
      simp [eI]
    simp only [vbar, Sum.elim_inl]
    rw [h0, mulVec_zero]
    simp [eI]
  · simp [vbar]

/-- `F_{e_ν} = |G_{νν} − m|`. -/
private theorem chain_Fv_inr (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (ν : Fin N) :
    Fv Sig A z (eI (Sum.inr ν)) =
      ‖G Sig A z (Sum.inr ν) (Sum.inr ν) - mFun N (specOf Sig) z‖ := by
  rw [Fv, chain_vbar_inr, ent_eI_eI, Matrix.sub_apply]
  simp [PiZ, piMat]

/-- The coefficients of `m_N − m` along `(i, μ)`: `|a_k| ≤ (2B)^{k+1}` when all entries of `G` and
all `|G_{νν} − m|` are at most `B` ((w_est) averaged over `ν`). -/
private theorem chain_avgCoeff_le {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (i : Fin M) (μ : Fin N) {B : ℝ}
    (hB : 0 ≤ B) (hG : ∀ q r, ‖G Sig A z q r‖ ≤ B)
    (hF : ∀ ν : Fin N, ‖G Sig A z (Sum.inr ν) (Sum.inr ν) - mFun N (specOf Sig) z‖ ≤ B)
    (k : ℕ) : ‖avgCoeff Sig A z i μ k‖ ≤ (2 * B) ^ (k + 1) := by
  have hres : ∀ ν : Fin N, ‖resCoeff Sig A z (eI (Sum.inr ν)) i μ k‖ ≤ (2 * B) ^ (k + 1) := by
    intro ν
    have h0 : Fv Sig A z (eI (Sum.inr ν)) ≤ B := by rw [chain_Fv_inr]; exact hF ν
    have h1 : ∀ b, ‖ent (G Sig A z) (vbar Sig (eI (Sum.inr ν))) (eI (letterT i μ b))‖ ≤ B :=
      fun b => by rw [chain_vbar_inr, ent_eI_eI]; exact hG _ _
    have h2 : ∀ b, ‖ent (G Sig A z) (eI (letterS i μ b)) (vbar Sig (eI (Sum.inr ν)))‖ ≤ B :=
      fun b => by rw [chain_vbar_inr, ent_eI_eI]; exact hG _ _
    have h3 : ∀ b b', ‖G Sig A z (letterS i μ b) (letterT i μ b')‖ ≤ B := fun b b' => hG _ _
    refine (norm_resCoeff_le hSig A hz _ i μ h0 h1 h2 h3 k).trans ?_
    have hB0 : 0 ≤ B ^ (k + 1) := by positivity
    calc (2 : ℝ) ^ k * B ^ (k + 1) ≤ 2 ^ (k + 1) * B ^ (k + 1) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hB0
      _ = (2 * B) ^ (k + 1) := (mul_pow 2 B (k + 1)).symm
  have hsum : ‖∑ ν : Fin N, resCoeff Sig A z (eI (Sum.inr ν)) i μ k‖ ≤
      (N : ℝ) * (2 * B) ^ (k + 1) := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun ν _ => hres ν).trans (le_of_eq ?_)
    simp
  have hP : 0 ≤ (2 * B) ^ (k + 1) := by positivity
  unfold avgCoeff
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  rcases eq_or_ne (N : ℝ) 0 with h | h
  · rw [h, _root_.inv_zero, zero_mul]; exact hP
  · calc (N : ℝ)⁻¹ * ‖∑ ν : Fin N, resCoeff Sig A z (eI (Sum.inr ν)) i μ k‖
        ≤ (N : ℝ)⁻¹ * ((N : ℝ) * (2 * B) ^ (k + 1)) :=
          mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 (Nat.cast_nonneg N))
      _ = (2 * B) ^ (k + 1) := by rw [← mul_assoc, inv_mul_cancel₀ h, one_mul]

/-- `|f_n| ≤ (n + 1)^p (2B)^{n+p}` for the coefficients of `F̃^p` under the bounds of
`chain_avgCoeff_le`. -/
private theorem chain_fCoeff_le {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (i : Fin M) (μ : Fin N) {B : ℝ}
    (hB : 1 ≤ 2 * B) (hG : ∀ q r, ‖G Sig A z q r‖ ≤ B)
    (hF : ∀ ν : Fin N, ‖G Sig A z (Sum.inr ν) (Sum.inr ν) - mFun N (specOf Sig) z‖ ≤ B)
    (p n : ℕ) :
    ‖fCoeff p (avgCoeff Sig A z i μ) n‖ ≤ ((n : ℝ) + 1) ^ p * (2 * B) ^ (n + p) :=
  norm_fCoeff_le p hB n fun k _ => chain_avgCoeff_le hSig A hz i μ (by linarith) hG hF k

/-! ## Rough deterministic bounds -/

/-- The rough constant `3τ⁻² + K_m + 1`. -/
private def chainKr (τ : ℝ) : ℝ := 3 * τ⁻¹ ^ 2 + mBoundConst τ + 1

private theorem chainKr_ge_one {τ : ℝ} (hτ : 0 < τ) : 1 ≤ chainKr τ := by
  have := mBoundConst_pos hτ
  unfold chainKr
  nlinarith [sq_nonneg τ⁻¹]

/-- Lemma 4.9 form of the entry bounds: `|G_{qr}| ≤ 3τ⁻² N (1 + ‖A‖_F²)` on `𝐃(τ, N)`. -/
private theorem chain_rough_G {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) {z : ℂ} (hz : z ∈ S)
    (A : Matrix (Fin M) (Fin N) ℝ) (q r : Fin M ⊕ Fin N) :
    ‖G Sig A z q r‖ ≤ 3 * τ⁻¹ ^ 2 * (N * (1 + chainSq A)) := by
  have hSig := hset.sigma.posDef
  have hτ := hset.pos
  have hzD := hset.domain.1 hz
  have hη : 0 < z.im := hzD.1
  have hNη := chain_one_le_N_im hN hτ hzD
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set s := chainSq A with hs
  have hs0 : 0 ≤ s := chainSq_nonneg A
  set Q : ℝ := N * (1 + s) with hQ
  have hQ1 : 1 ≤ Q := by nlinarith
  have hT1 : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hset.le_one
  have hXtX : ‖Aᵀ * A‖ ≤ s := by rw [hs]; exact chainP_XtX_le A
  have hop : (1 + ‖Aᵀ * A‖) / z.im + 1 ≤ Q + 1 := by
    have : (1 + ‖Aᵀ * A‖) / z.im ≤ Q := by
      rw [div_le_iff₀ hη, hQ]
      have h1 : 1 + ‖Aᵀ * A‖ ≤ 1 + s := by linarith
      have h2 : 0 ≤ 1 + ‖Aᵀ * A‖ := by positivity
      nlinarith
    linarith
  have hop0 : 0 ≤ (1 + ‖Aᵀ * A‖) / z.im + 1 := by positivity
  have hu : ∀ p, testNorm (SigU (n := Fin N) Sig *ᵥ eI p) ≤ τ⁻¹ := fun p => by
    have := chainR_testNorm_SigU (N := N) hset.sigma hτ hset.le_one (eI p)
    rwa [chainR_testNorm_eI, mul_one] at this
  rw [← ent_eI_eI (G Sig A z) q r, ← chainR_vbar_SigU (N := N) hSig (eI q)]
  refine (chainR_G_left_op hSig A hη _ r).trans ?_
  have hq0 : 0 ≤ testNorm (SigU (n := Fin N) Sig *ᵥ eI q) := Real.sqrt_nonneg _
  have hr0 : 0 ≤ testNorm (SigU (n := Fin N) Sig *ᵥ eI r) := Real.sqrt_nonneg _
  have h1 : ((1 + ‖Aᵀ * A‖) / z.im + 1) * testNorm (SigU (n := Fin N) Sig *ᵥ eI q) *
      testNorm (SigU (n := Fin N) Sig *ᵥ eI r) ≤ (Q + 1) * τ⁻¹ * τ⁻¹ := by
    gcongr
    · exact hu q
    · exact hu r
  have hq := hu q
  have hA1 : τ⁻¹ ≤ Q * τ⁻¹ := le_mul_of_one_le_left (by linarith) hQ1
  have hA3 : Q * τ⁻¹ ≤ Q * τ⁻¹ * τ⁻¹ := le_mul_of_one_le_right (by positivity) hT1
  have hA4 : τ⁻¹ * τ⁻¹ ≤ Q * τ⁻¹ * τ⁻¹ := by nlinarith
  have h2 : (Q + 1) * τ⁻¹ * τ⁻¹ + τ⁻¹ ≤ 3 * τ⁻¹ ^ 2 * Q := by nlinarith
  nlinarith

/-- `|f_n(A)| ≤ (n+1)^p (2 K N (1 + ‖A‖_F²))^{n+p}` (rough form of (w_est) for `F̃^p`). -/
private theorem chain_rough_fCoeff {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) {z : ℂ} (hz : z ∈ S)
    (A : Matrix (Fin M) (Fin N) ℝ) (i : Fin M) (μ : Fin N) (p n : ℕ) :
    ‖fCoeff p (avgCoeff Sig A z i μ) n‖ ≤
      ((n : ℝ) + 1) ^ p * (2 * (chainKr τ * (N * (1 + chainSq A)))) ^ (n + p) := by
  have hτ := hset.pos
  have hzD := hset.domain.1 hz
  have hη : 0 < z.im := hzD.1
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs0 := chainSq_nonneg A
  set Q : ℝ := N * (1 + chainSq A) with hQ
  have hQ1 : 1 ≤ Q := by nlinarith
  have hKr := chainKr_ge_one hτ
  have hm := (gen_prop_m_specDomain (chainR_density hset hN) hzD).2.1
  have hG : ∀ q r, ‖G Sig A z q r‖ ≤ chainKr τ * Q := by
    intro q r
    refine (chain_rough_G hset hN hz A q r).trans ?_
    have : 3 * τ⁻¹ ^ 2 ≤ chainKr τ := by
      unfold chainKr; linarith [mBoundConst_pos hτ]
    exact mul_le_mul_of_nonneg_right this (by linarith)
  have hF : ∀ ν : Fin N, ‖G Sig A z (Sum.inr ν) (Sum.inr ν) - mFun N (specOf Sig) z‖ ≤
      chainKr τ * Q := by
    intro ν
    refine (norm_sub_le _ _).trans ?_
    have h1 := chain_rough_G hset hN hz A (Sum.inr ν) (Sum.inr ν)
    have h2 : 3 * τ⁻¹ ^ 2 * Q + mBoundConst τ ≤ chainKr τ * Q := by
      unfold chainKr
      have := mBoundConst_pos hτ
      nlinarith
    linarith
  exact chain_fCoeff_le hset.sigma.posDef A hη i μ (by nlinarith) hG hF p n

/-! ## Continuity and derivatives in the entry `(i, μ)` -/

private theorem chain_continuous_avgCoeff {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    {z : ℂ} (hz : 0 < z.im) (i : Fin M) (μ : Fin N) (k : ℕ) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => avgCoeff Sig A z i μ k := by
  unfold avgCoeff
  exact continuous_const.mul (continuous_finsetSum _ fun ν _ =>
    chain_continuous_resCoeff hSig hz (eI (Sum.inr ν)) i μ k)

private theorem chain_continuous_fCoeff_upd {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    {z : ℂ} (hz : 0 < z.im) (i : Fin M) (μ : Fin N) (p n : ℕ) :
    Continuous fun q : Matrix (Fin M) (Fin N) ℝ × ℝ =>
      fCoeff p (avgCoeff Sig (Xupd q.1 i μ q.2) z i μ) n :=
  chain_continuous_fCoeff p n fun k =>
    (chain_continuous_avgCoeff hSig hz i μ k).comp (chain_continuous_Xupd i μ)

/-- `d/dx a_k(x) = (k + 1) a_{k+1}(x)` for the coefficients of `m_N − m` along `(i, μ)`. -/
private theorem chain_hasDerivAt_avgCoeff {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (i : Fin M) (μ : Fin N) (k : ℕ)
    (x : ℝ) :
    HasDerivAt (fun y => avgCoeff Sig (Xupd A i μ y) z i μ k)
      (((k : ℂ) + 1) * avgCoeff Sig (Xupd A i μ x) z i μ (k + 1)) x := by
  have h2 := (HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin N))) fun ν _ =>
    hasDerivAt_resCoeff hSig A hz (eI (Sum.inr ν)) i μ k x).const_mul ((N : ℂ)⁻¹)
  unfold avgCoeff
  refine h2.congr_deriv ?_
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-! ## The perturbation of one entry -/

/-- `(P (Δ^t Q))_{ab} = t (P_{a(i)} Q_{(μ)b} + P_{a(μ)} Q_{(i)b})`. -/
private theorem chain_mul_Delta (P Q : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) (i : Fin M)
    (μ : Fin N) (t : ℝ) (a b : Fin M ⊕ Fin N) :
    (P * (Delta i μ t * Q)) a b =
      (t : ℂ) * (P a (Sum.inl i) * Q (Sum.inr μ) b + P a (Sum.inr μ) * Q (Sum.inl i) b) := by
  have hD : ∀ c, (Delta i μ t * Q) c b =
      (if c = Sum.inl i then (t : ℂ) * Q (Sum.inr μ) b else 0) +
        (if c = Sum.inr μ then (t : ℂ) * Q (Sum.inl i) b else 0) := by
    intro c
    rw [Matrix.mul_apply]
    rcases c with j | ν
    · by_cases hj : j = i
      · subst hj
        simp [Delta]
      · simp [Delta, hj]
    · by_cases hν : ν = μ
      · subst hν
        simp [Delta]
      · simp [Delta, hν]
  rw [Matrix.mul_apply]
  simp only [hD, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  ring

/-- Replacing the entry `(i, μ)` of `A` by `s`: if all entries of `G(A)` are at most `B` and
`4 |A_{iμ} − s| B ≤ 1`, then all entries of `G(A^{(iμ),s})` are at most `2B` (the identity
`G' = G + G' Δ G` of (res_exp)). -/
private theorem chain_pert {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (i : Fin M) (μ : Fin N) (s : ℝ)
    {B : ℝ} (hB : ∀ a b, ‖G Sig A z a b‖ ≤ B) (ht : 4 * |A i μ - s| * B ≤ 1) :
    ∀ a b, ‖G Sig (Xupd A i μ s) z a b‖ ≤ 2 * B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB (Sum.inl i) (Sum.inl i))
  have h := res_exp hSig A hz i μ (A i μ) s 0
  rw [Xupd_self] at h
  simp only [zero_add, pow_one, Finset.Icc_eq_empty_of_lt one_pos, Finset.sum_empty,
    add_zero] at h
  set G' := G Sig (Xupd A i μ s) z with hG'
  set t : ℝ := A i μ - s with ht'
  have hent : ∀ a b, G' a b = G Sig A z a b +
      (t : ℂ) * (G' a (Sum.inl i) * G Sig A z (Sum.inr μ) b +
        G' a (Sum.inr μ) * G Sig A z (Sum.inl i) b) := by
    intro a b
    have := congrFun (congrFun h a) b
    rw [Matrix.add_apply, chain_mul_Delta] at this
    exact this
  have : Nonempty ((Fin M ⊕ Fin N) × (Fin M ⊕ Fin N)) := ⟨(Sum.inl i, Sum.inl i)⟩
  obtain ⟨p0, hp0⟩ := Finite.exists_max
    (fun q : (Fin M ⊕ Fin N) × (Fin M ⊕ Fin N) => ‖G' q.1 q.2‖)
  set α := ‖G' p0.1 p0.2‖ with hα
  have hα0 : 0 ≤ α := norm_nonneg _
  have hbd : ∀ a b, ‖G' a b‖ ≤ B + |t| * (α * B + α * B) := by
    intro a b
    rw [hent]
    have h1 : ‖G' a (Sum.inl i)‖ ≤ α := hp0 (a, Sum.inl i)
    have h2 : ‖G' a (Sum.inr μ)‖ ≤ α := hp0 (a, Sum.inr μ)
    calc ‖G Sig A z a b + (t : ℂ) * (G' a (Sum.inl i) * G Sig A z (Sum.inr μ) b +
          G' a (Sum.inr μ) * G Sig A z (Sum.inl i) b)‖
        ≤ ‖G Sig A z a b‖ + ‖(t : ℂ)‖ * (‖G' a (Sum.inl i)‖ * ‖G Sig A z (Sum.inr μ) b‖ +
          ‖G' a (Sum.inr μ)‖ * ‖G Sig A z (Sum.inl i) b‖) := by
          refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          refine (norm_add_le _ _).trans (le_of_eq ?_)
          rw [norm_mul, norm_mul]
      _ ≤ B + |t| * (α * B + α * B) := by
          rw [Complex.norm_real, Real.norm_eq_abs]
          gcongr
          · exact hB a b
          · exact hB _ _
          · exact hB _ _
  have hα2 : α ≤ 2 * B := by
    have h0 := hbd p0.1 p0.2
    have : |t| * (α * B + α * B) ≤ α / 2 := by
      have e : |t| * (α * B + α * B) = (4 * |t| * B) * (α / 2) := by ring
      rw [e]
      exact mul_le_of_le_one_left (by linarith) ht
    linarith
  intro a b
  exact (hp0 (a, b)).trans hα2

/-! ## Bounds on `Ψ` on `𝐃(τ, N)` -/

/-- `Ψ ≤ √K_m + 1` on `𝐃(τ, N)` (Lemma 4.10). -/
private theorem chain_Psi_le {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) {z : ℂ} (hz : z ∈ S) :
    Psi N (specOf Sig) z ≤ Real.sqrt (mBoundConst τ) + 1 := by
  have hzD := hset.domain.1 hz
  have hNη := chain_one_le_N_im hN hset.pos hzD
  obtain ⟨-, hm2, hm3⟩ := gen_prop_m_specDomain (chainR_density hset hN) hzD
  have hC := mBoundConst_pos hset.pos
  have hη : 0 < z.im := hzD.1
  have ha0 : 0 ≤ (mFun N (specOf Sig) z).im := le_trans (by positivity) hm3
  have haC : (mFun N (specOf Sig) z).im ≤ mBoundConst τ := le_trans (Complex.im_le_norm _) hm2
  have hpos : 0 < (N : ℝ) * z.im := by linarith
  unfold Psi
  have h1 : (mFun N (specOf Sig) z).im / (N * z.im) ≤ mBoundConst τ := by
    rw [div_le_iff₀ hpos]; nlinarith
  have h2 : 1 / ((N : ℝ) * z.im) ≤ 1 := by rw [div_le_one hpos]; exact hNη
  have h3 := Real.sqrt_le_sqrt h1
  linarith

/-- `Ψ² ≥ Im m/(Nη) ≥ (K_m N)⁻¹` on `𝐃(τ, N)` (Lemma 4.10). -/
private theorem chain_Psi_sq_ge {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) {z : ℂ} (hz : z ∈ S) :
    (mBoundConst τ * N)⁻¹ ≤ Psi N (specOf Sig) z ^ 2 := by
  have hzD := hset.domain.1 hz
  obtain ⟨-, -, hm3⟩ := gen_prop_m_specDomain (chainR_density hset hN) hzD
  have hC := mBoundConst_pos hset.pos
  have hη : 0 < z.im := hzD.1
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : 0 < (N : ℝ) * z.im := by positivity
  have ha0 : 0 ≤ (mFun N (specOf Sig) z).im := le_trans (by positivity) hm3
  set x := Real.sqrt ((mFun N (specOf Sig) z).im / (N * z.im)) with hx
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hsq : x ^ 2 = (mFun N (specOf Sig) z).im / (N * z.im) := Real.sq_sqrt (by positivity)
  have hle : x ≤ Psi N (specOf Sig) z := by
    unfold Psi
    have : 0 ≤ 1 / ((N : ℝ) * z.im) := by positivity
    linarith
  have h1 : (mBoundConst τ * N)⁻¹ ≤ (mFun N (specOf Sig) z).im / (N * z.im) := by
    rw [le_div_iff₀ hpos]
    calc (mBoundConst τ * N)⁻¹ * (N * z.im) = (mBoundConst τ)⁻¹ * z.im := by
          field_simp
      _ ≤ (mFun N (specOf Sig) z).im := hm3
  calc (mBoundConst τ * N)⁻¹ ≤ x ^ 2 := by rw [hsq]; exact h1
    _ ≤ Psi N (specOf Sig) z ^ 2 := pow_le_pow_left₀ hx0 hle 2

/-! ## Lemma 7.15 for `F̃^p` -/

/-- The event of Lemma 7.15 for `F̃^p`: `|y| ≤ N^{εa − 1/2}` and, for all `|s| ≤ |y|` and
`n ≤ 4p + 1`, `|f_n(s)| ≤ N^{4εa(n+p)}`. It contains the a priori event of the anisotropic law
at `X` (test vectors `Σ̲ e_a`), and `|X_{iμ}| ≤ N^{εa − 1/2}`. -/
private theorem chain_event (τ c : ℝ) (C : ℕ → ℝ) (p : ℕ) (εa Da : ℝ) (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (hc : 0 < c) (hp2 : 2 ≤ p) (hεa : 0 < εa) (hεap : 100 * p * εa ≤ 1) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ),
      CompSetting τ c M N Sig S → AnisoAllAt N C Sig S εa Da →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ) (y : Ω → ℝ), EntryAssumption C X →
        HighProbAt N Da {ω | |y ω| ≤ (N : ℝ) ^ (εa - 1 / 2)} →
        ∀ z ∈ S, ∀ (i : Fin M) (μ : Fin N),
          HighProbAt N (Da - 3) {ω | |y ω| ≤ (N : ℝ) ^ (εa - 1 / 2) ∧ ∀ s : ℝ, |s| ≤ |y ω| →
            ∀ n ≤ 4 * p + 1, ‖fCoeff p (avgCoeff Sig (Xupd (X ω) i μ s) z i μ) n‖ ≤
              (N : ℝ) ^ (4 * εa * ((n : ℝ) + p))} := by
  obtain ⟨N₂, h₂⟩ := chain_markov C εa Da hεa
  set Cm := mBoundConst τ with hCm
  have hCm0 : 0 < Cm := mBoundConst_pos hτ
  set κ := max c⁻¹ Cm with hκ
  have hκ0 : 0 ≤ κ := (inv_pos.2 hc).le.trans (le_max_left _ _)
  have hT0 : 0 ≤ τ⁻¹ := (inv_pos.2 hτ).le
  have hT1 : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  set K₁ : ℝ := κ * τ⁻¹ + τ⁻¹ ^ 2 * (Real.sqrt Cm + 1) with hK₁
  have hK₁1 : 1 ≤ K₁ := by
    have : 0 ≤ κ * τ⁻¹ := mul_nonneg hκ0 hT0
    have : 1 ≤ τ⁻¹ ^ 2 := one_le_pow₀ hT1
    have : 0 ≤ Real.sqrt Cm := Real.sqrt_nonneg _
    nlinarith
  set K₀ : ℝ := (4 * p + 2) * (2 * (2 * K₁ + Cm)) with hK₀
  have hK₀0 : 0 ≤ K₀ := by positivity
  have hεa200 : 200 * εa ≤ 1 := by
    have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    nlinarith
  refine ⟨max (max N₂ ⌈(τ⁻¹ + 1) ^ 2 + 2⌉₊) (max ⌈(8 * K₁) ^ (1 / 4 : ℝ)⁻¹⌉₊
    ⌈K₀ ^ (3 * εa)⁻¹⌉₊), ?_⟩
  intro N hN M Sig S hset hA Ω _ _ X y hX hy z hz i μ
  have hNN₂ : N₂ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNc : ⌈(τ⁻¹ + 1) ^ 2 + 2⌉₊ ≤ N :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNK : ⌈(8 * K₁) ^ (1 / 4 : ℝ)⁻¹⌉₊ ≤ N :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNK₀ : ⌈K₀ ^ (3 * εa)⁻¹⌉₊ ≤ N :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hNc' : (τ⁻¹ + 1) ^ 2 + 2 ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hNc)
  have hN3 : (3 : ℝ) ≤ N := by nlinarith
  have hN1r : (1 : ℝ) ≤ N := by linarith
  have hN1 : 1 ≤ N := by exact_mod_cast hN1r
  have hNp : (0 : ℝ) < N := by linarith
  have h8K : 8 * K₁ ≤ (N : ℝ) ^ (1 / 4 : ℝ) :=
    chain_le_rpow (by linarith) (by norm_num) hNK
  have hK₀N : K₀ ≤ (N : ℝ) ^ (3 * εa) := chain_le_rpow hK₀0 (by positivity) hNK₀
  have hSig := hset.sigma.posDef
  have hzD := hset.domain.1 hz
  have hη : 0 < z.im := hzD.1
  have hm := (gen_prop_m_specDomain (chainR_density hset hN1) hzD).2.1
  have hOne := hset.oneXm z hz
  have hΨ := chain_Psi_le hset hN1 hz
  have hΨ0 : 0 ≤ Psi N (specOf Sig) z := by
    have := chain_Psi_ge (σ := specOf Sig) hN1 hτ hzD
    exact le_trans (by positivity) this
  have hlaw := hA Ω X hX z hz
  set u : Fin M ⊕ Fin N → Fin M ⊕ Fin N → ℝ := fun a => SigU (n := Fin N) Sig *ᵥ eI a with hu
  have hun : ∀ a, testNorm (u a) ≤ τ⁻¹ := fun a => by
    have := chainR_testNorm_SigU (N := N) hset.sigma hτ hset.le_one (eI a)
    rwa [chainR_testNorm_eI, mul_one] at this
  let Ev : ((Fin M ⊕ Fin N) × (Fin M ⊕ Fin N)) ⊕ Bool → Set Ω := Sum.elim
    (fun ab => {ω | ‖testBilin (u ab.1) (lawMat Sig (X ω) z) (u ab.2)‖ ≤
      (N : ℝ) ^ εa * (Psi N (specOf Sig) z * testNorm (u ab.1) * testNorm (u ab.2))})
    (fun b => if b then {ω | |y ω| ≤ (N : ℝ) ^ (εa - 1 / 2)}
      else {ω | |X ω i μ| ≤ (N : ℝ) ^ (εa - 1 / 2)})
  have hEv : ∀ ι ∈ (Finset.univ : Finset (((Fin M ⊕ Fin N) × (Fin M ⊕ Fin N)) ⊕ Bool)),
      HighProbAt N (Da - 3 + 3) (Ev ι) := by
    intro ι _
    rw [show Da - 3 + 3 = Da by ring]
    rcases ι with ⟨a, b⟩ | bb
    · have h := hlaw (u a) (u b)
      unfold DomAt at h
      unfold HighProbAt
      refine le_trans (measure_mono fun ω hω => ?_) h
      simp only [Ev, Sum.elim_inl, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω ⊢
      exact hω
    · cases bb
      · have hym : ∀ q : ℕ, Integrable (fun ω => |Real.sqrt N * X ω i μ| ^ q) ∧
            ∫ ω, |Real.sqrt N * X ω i μ| ^ q ≤ C q :=
          fun q => ⟨hX.integrable_moment q i μ, hX.moment q i μ⟩
        exact h₂ N hNN₂ (fun ω => X ω i μ) hym
      · exact hy
  have hcard : ((Finset.univ : Finset (((Fin M ⊕ Fin N) × (Fin M ⊕ Fin N)) ⊕ Bool)).card : ℝ) ≤
      (N : ℝ) ^ (3 : ℝ) := by
    rw [Finset.card_univ, Fintype.card_sum, Fintype.card_prod, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin, Fintype.card_bool,
      show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    push_cast
    have hM : (M : ℝ) ≤ τ⁻¹ * N := (div_le_iff₀ hNp).1 hset.ratio_le
    have hMN : (M : ℝ) + N ≤ (τ⁻¹ + 1) * N := by linarith
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    calc ((M : ℝ) + N) * (M + N) + 2 ≤ ((τ⁻¹ + 1) * N) * ((τ⁻¹ + 1) * N) + 2 := by
          gcongr
      _ = (τ⁻¹ + 1) ^ 2 * N ^ 2 + 2 := by ring
      _ ≤ ((τ⁻¹ + 1) ^ 2 + 2) * N ^ 2 := by
          have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := one_le_pow₀ hN1r
          have e : ((τ⁻¹ + 1) ^ 2 + 2) * (N : ℝ) ^ 2 = (τ⁻¹ + 1) ^ 2 * N ^ 2 + 2 * N ^ 2 := by
            ring
          linarith
      _ ≤ N * N ^ 2 := mul_le_mul_of_nonneg_right hNc' (by positivity)
      _ = N ^ 3 := by ring
  have hall := HighProbAt.biInter Finset.univ hN1 hcard hEv
  refine chain_hp_mono (fun ω hω => ?_) hall
  have hω' : ∀ ι, ω ∈ Ev ι := fun ι => Set.mem_iInter₂.1 hω ι (Finset.mem_univ _)
  have hyω : |y ω| ≤ (N : ℝ) ^ (εa - 1 / 2) := by
    have := hω' (Sum.inr true); simpa [Ev] using this
  have hXω : |X ω i μ| ≤ (N : ℝ) ^ (εa - 1 / 2) := by
    have := hω' (Sum.inr false); simpa [Ev] using this
  refine ⟨hyω, fun s hs n hn => ?_⟩
  have hNe1 : 1 ≤ (N : ℝ) ^ εa := Real.one_le_rpow hN1r hεa.le
  -- entries of `G(X)`
  have hG0 : ∀ a b, ‖G Sig (X ω) z a b‖ ≤ K₁ * (N : ℝ) ^ εa := by
    intro a b
    have hab := hω' (Sum.inl (a, b))
    simp only [Ev, Sum.elim_inl, Set.mem_ofPred_eq] at hab
    rw [← ent_vbar_eq_testBilin hSig, chainR_vbar_SigU hSig, chainR_vbar_SigU hSig,
      ent_eI_eI, Matrix.sub_apply] at hab
    have hPi : ‖PiZ N Sig z a b‖ ≤ κ * τ⁻¹ := by
      have h := chainR_pi_bound hSig hc hm hOne (u a) b
      rw [show u a = SigU (n := Fin N) Sig *ᵥ eI a from rfl, chainR_vbar_SigU hSig,
        ent_eI_eI] at h
      exact h.trans (mul_le_mul_of_nonneg_left (hun a) hκ0)
    have hdiff : ‖G Sig (X ω) z a b - PiZ N Sig z a b‖ ≤
        (N : ℝ) ^ εa * (τ⁻¹ ^ 2 * (Real.sqrt Cm + 1)) := by
      refine hab.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      have ha0 : 0 ≤ testNorm (u a) := Real.sqrt_nonneg _
      have hb0 : 0 ≤ testNorm (u b) := Real.sqrt_nonneg _
      calc Psi N (specOf Sig) z * testNorm (u a) * testNorm (u b)
          ≤ (Real.sqrt Cm + 1) * τ⁻¹ * τ⁻¹ := by
            gcongr
            · exact hun a
            · exact hun b
        _ = τ⁻¹ ^ 2 * (Real.sqrt Cm + 1) := by ring
    have hsplit : ‖G Sig (X ω) z a b‖ ≤
        ‖G Sig (X ω) z a b - PiZ N Sig z a b‖ + ‖PiZ N Sig z a b‖ := by
      have := norm_add_le (G Sig (X ω) z a b - PiZ N Sig z a b) (PiZ N Sig z a b)
      rwa [sub_add_cancel] at this
    have h1 : κ * τ⁻¹ ≤ κ * τ⁻¹ * (N : ℝ) ^ εa :=
      le_mul_of_one_le_right (mul_nonneg hκ0 hT0) hNe1
    have e : K₁ * (N : ℝ) ^ εa = κ * τ⁻¹ * (N : ℝ) ^ εa +
        (N : ℝ) ^ εa * (τ⁻¹ ^ 2 * (Real.sqrt Cm + 1)) := by rw [hK₁]; ring
    linarith
  -- the perturbation
  have hts : |X ω i μ - s| ≤ 2 * (N : ℝ) ^ (εa - 1 / 2) := by
    have := abs_sub (X ω i μ) s
    linarith
  have hsmall : 4 * |X ω i μ - s| * (K₁ * (N : ℝ) ^ εa) ≤ 1 := by
    have e1 : (N : ℝ) ^ (εa - 1 / 2) * (N : ℝ) ^ εa * (N : ℝ) ^ (1 / 4 : ℝ) =
        (N : ℝ) ^ (2 * εa - 1 / 4) := by
      rw [← Real.rpow_add hNp, ← Real.rpow_add hNp]; ring_nf
    have e2 : (N : ℝ) ^ (2 * εa - 1 / 4) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hN1r (by linarith)
    have hK0 : 0 ≤ K₁ * (N : ℝ) ^ εa := by positivity
    calc 4 * |X ω i μ - s| * (K₁ * (N : ℝ) ^ εa)
        ≤ 4 * (2 * (N : ℝ) ^ (εa - 1 / 2)) * (K₁ * (N : ℝ) ^ εa) := by gcongr
      _ = (8 * K₁) * ((N : ℝ) ^ (εa - 1 / 2) * (N : ℝ) ^ εa) := by ring
      _ ≤ (N : ℝ) ^ (1 / 4 : ℝ) * ((N : ℝ) ^ (εa - 1 / 2) * (N : ℝ) ^ εa) := by
          gcongr
      _ = (N : ℝ) ^ (2 * εa - 1 / 4) := by rw [← e1]; ring
      _ ≤ 1 := e2
  have hG1 := chain_pert hSig (X ω) hη i μ s hG0 hsmall
  set B : ℝ := (2 * K₁ + Cm) * (N : ℝ) ^ εa with hB
  have hGB : ∀ q r, ‖G Sig (Xupd (X ω) i μ s) z q r‖ ≤ B := by
    intro q r
    refine (hG1 q r).trans ?_
    have : 0 ≤ Cm * (N : ℝ) ^ εa := by positivity
    have e : B = 2 * (K₁ * (N : ℝ) ^ εa) + Cm * (N : ℝ) ^ εa := by rw [hB]; ring
    linarith
  have hFB : ∀ ν : Fin N, ‖G Sig (Xupd (X ω) i μ s) z (Sum.inr ν) (Sum.inr ν) -
      mFun N (specOf Sig) z‖ ≤ B := by
    intro ν
    refine (norm_sub_le _ _).trans ?_
    have h1 := hG1 (Sum.inr ν) (Sum.inr ν)
    have h2 : Cm ≤ Cm * (N : ℝ) ^ εa := le_mul_of_one_le_right hCm0.le hNe1
    have e : B = 2 * (K₁ * (N : ℝ) ^ εa) + Cm * (N : ℝ) ^ εa := by rw [hB]; ring
    linarith
  have hB1 : 1 ≤ 2 * B := by
    have h1 : 1 ≤ 2 * K₁ + Cm := by linarith
    have h2 := mul_le_mul_of_nonneg_left hNe1 (by linarith : (0 : ℝ) ≤ 2 * K₁ + Cm)
    rw [hB]
    linarith
  have hf := chain_fCoeff_le hSig (Xupd (X ω) i μ s) hη i μ hB1 hGB hFB p n
  refine hf.trans ?_
  have hn1 : (n : ℝ) + 1 ≤ 4 * p + 2 := by
    have : (n : ℝ) ≤ 4 * p + 1 := by exact_mod_cast hn
    linarith
  have h42 : (1 : ℝ) ≤ 4 * p + 2 := by have := (Nat.cast_nonneg p : (0 : ℝ) ≤ p); linarith
  have hpow1 : ((n : ℝ) + 1) ^ p ≤ (4 * (p : ℝ) + 2) ^ (n + p) :=
    (pow_le_pow_left₀ (by positivity) hn1 p).trans (pow_le_pow_right₀ h42 (by omega))
  have hK : (4 * (p : ℝ) + 2) * (2 * B) ≤ (N : ℝ) ^ (4 * εa) := by
    have e : (4 * (p : ℝ) + 2) * (2 * B) = K₀ * (N : ℝ) ^ εa := by rw [hK₀, hB]; ring
    have e2 : (N : ℝ) ^ (3 * εa) * (N : ℝ) ^ εa = (N : ℝ) ^ (4 * εa) := by
      rw [← Real.rpow_add hNp]; ring_nf
    rw [e, ← e2]
    exact mul_le_mul_of_nonneg_right hK₀N (by positivity)
  calc ((n : ℝ) + 1) ^ p * (2 * B) ^ (n + p)
      ≤ (4 * (p : ℝ) + 2) ^ (n + p) * (2 * B) ^ (n + p) :=
        mul_le_mul_of_nonneg_right hpow1 (by positivity)
    _ = ((4 * (p : ℝ) + 2) * (2 * B)) ^ (n + p) := (mul_pow _ _ _).symm
    _ ≤ ((N : ℝ) ^ (4 * εa)) ^ (n + p) := pow_le_pow_left₀ (by positivity) hK _
    _ = (N : ℝ) ^ (4 * εa * ((n : ℝ) + p)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
        push_cast
        ring_nf

/-- The remainder of order `4p + 1` (re-expansion with remainder, exponents of (Taylo_id1)):
`|f_l(t) − ∑_{k ≤ 4p−l} C(l+k, l) t^k f_{l+k}(0)| ≤ N^{l/2−2} Ψ^{2p}` for `|t| ≤ N^{εa − 1/2}`,
`|f_{4p+1}| ≤ N^{4εa(5p+1)}` on `[0, t]` and `Ψ² ≥ (K_m N)⁻¹`. -/
private theorem chain_rem_det {εa : ℝ} {p : ℕ} (hp2 : 2 ≤ p) (hεa : 0 < εa)
    (hεap : 100 * p * εa ≤ 1) {N : ℕ} (hN : 1 ≤ N) {Km : ℝ} (hKm : 0 < Km)
    (hN10 : ((4 * p + 1).factorial : ℝ) * Km ^ p ≤ (N : ℝ) ^ (1 / 10 : ℝ))
    {Ψ : ℝ} (hΨ : (Km * N)⁻¹ ≤ Ψ ^ 2) {a : ℝ → ℕ → ℂ}
    (ha : ∀ k x, HasDerivAt (fun y => a y k) (((k : ℂ) + 1) * a x (k + 1)) x)
    (t : ℝ) (ht : |t| ≤ (N : ℝ) ^ (εa - 1 / 2))
    (hB : ∀ s : ℝ, |s| ≤ |t| → ‖fCoeff p (a s) (4 * p + 1)‖ ≤
      (N : ℝ) ^ (4 * εa * (((4 * p + 1 : ℕ) : ℝ) + p)))
    (l : ℕ) (hl : l ≤ 4 * p) :
    ‖fCoeff p (a t) l - ∑ k ∈ Finset.range (4 * p - l + 1),
        ((l + k).choose l : ℂ) * (t : ℂ) ^ k * fCoeff p (a 0) (l + k)‖ ≤
      (N : ℝ) ^ ((l : ℝ) / 2 - 2) * Ψ ^ (2 * p) := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  set eB : ℝ := 4 * εa * (((4 * p + 1 : ℕ) : ℝ) + p) with heB
  have hidx : l + (4 * p - l) + 1 = 4 * p + 1 := by omega
  have hT := fCoeff_taylor p ha l (4 * p - l) 0 t ((N : ℝ) ^ eB) (fun s hs => by
    rw [zero_add, hidx]
    exact hB s (chain_abs_le_of_mem_uIcc hs))
  rw [zero_add, hidx] at hT
  refine hT.trans ?_
  have ht0 : 0 ≤ |t| := abs_nonneg t
  set et : ℝ := (εa - 1 / 2) * ((4 * p - l + 1 : ℕ) : ℝ) with het
  have htk : |t| ^ (4 * p - l + 1) ≤ (N : ℝ) ^ et := by
    rw [het, Real.rpow_mul hNp.le, Real.rpow_natCast]
    exact pow_le_pow_left₀ ht0 ht _
  have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hL : (l : ℝ) ≤ 4 * p := by exact_mod_cast hl
  have hL0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have hcast : ((4 * p - l + 1 : ℕ) : ℝ) = 4 * p - l + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hl]; push_cast; ring
  have hexp : 1 / 10 + eB + et ≤ (l : ℝ) / 2 - 2 - p := by
    rw [het, hcast, heB]
    push_cast
    have h1 : 200 * εa ≤ 1 := by nlinarith
    have h2 : 0 ≤ εa * l := by positivity
    nlinarith
  have hfac0 : (0 : ℝ) ≤ ((4 * p + 1).factorial : ℝ) := Nat.cast_nonneg _
  have hKp : 0 < Km ^ p := pow_pos hKm p
  have hΨp : ((Km * N)⁻¹) ^ p ≤ Ψ ^ (2 * p) := by
    rw [pow_mul]; exact pow_le_pow_left₀ (by positivity) hΨ p
  calc ((4 * p + 1).factorial : ℝ) * (N : ℝ) ^ eB * |t| ^ (4 * p - l + 1)
      ≤ ((4 * p + 1).factorial : ℝ) * (N : ℝ) ^ eB * (N : ℝ) ^ et := by gcongr
    _ = (((4 * p + 1).factorial : ℝ) * Km ^ p) * (N : ℝ) ^ (eB + et) * (Km ^ p)⁻¹ := by
        rw [Real.rpow_add hNp]; field_simp
    _ ≤ (N : ℝ) ^ (1 / 10 : ℝ) * (N : ℝ) ^ (eB + et) * (Km ^ p)⁻¹ := by gcongr
    _ = (N : ℝ) ^ (1 / 10 + eB + et) * (Km ^ p)⁻¹ := by
        rw [Real.rpow_add hNp, Real.rpow_add hNp, Real.rpow_add hNp]; ring
    _ ≤ (N : ℝ) ^ ((l : ℝ) / 2 - 2 - p) * (Km ^ p)⁻¹ := by gcongr
    _ = (N : ℝ) ^ ((l : ℝ) / 2 - 2) * ((Km * N)⁻¹) ^ p := by
        rw [show (l : ℝ) / 2 - 2 - p = ((l : ℝ) / 2 - 2) + (-(p : ℝ)) by ring,
          Real.rpow_add hNp, Real.rpow_neg hNp.le, Real.rpow_natCast, inv_pow, mul_pow]
        field_simp
    _ ≤ (N : ℝ) ^ ((l : ℝ) / 2 - 2) * Ψ ^ (2 * p) := by gcongr

/-! ## Expectations: independence and Lemma 7.7 -/

/-- `R_l(t) = f_l(t) − ∑_{k ≤ 4p−l} C(l+k, l) t^k f_{l+k}(0)` at the base matrix `A`. -/
private def chainRem (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (i : Fin M) (μ : Fin N) (p l : ℕ) (t : ℝ) : ℂ :=
  fCoeff p (avgCoeff Sig (Xupd A i μ t) z i μ) l -
    ∑ k ∈ Finset.range (4 * p - l + 1), ((l + k).choose l : ℂ) * (t : ℂ) ^ k *
      fCoeff p (avgCoeff Sig (Xupd A i μ 0) z i μ) (l + k)

/-- The constant `(4p+1)^p (2K)^{5p}` of `|f_n| ≤ K₁ (N W)^{5p}`, `n ≤ 4p`. -/
private def chainK1 (τ : ℝ) (p : ℕ) : ℝ := ((4 * p + 1 : ℝ)) ^ p * (2 * chainKr τ) ^ (5 * p)

/-- The constant `K₁ (1 + (4p+1) 2^{4p})` of `|R_l| ≤ K₂ (N W)^{9p}`. -/
private def chainK2 (τ : ℝ) (p : ℕ) : ℝ := chainK1 τ p * (1 + (4 * p + 1) * 2 ^ (4 * p))

private theorem chainK1_nonneg {τ : ℝ} (hτ : 0 < τ) (p : ℕ) : 0 ≤ chainK1 τ p := by
  have := chainKr_ge_one hτ
  unfold chainK1
  have : (0 : ℝ) ≤ 2 * chainKr τ := by linarith
  positivity

/-- `|f_n(A)| ≤ K₁ (N W)^{5p}` for `n ≤ 4p` and `1 + ‖A‖_F² ≤ W`. -/
private theorem chain_rough_f_le {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) {z : ℂ} (hz : z ∈ S)
    (A : Matrix (Fin M) (Fin N) ℝ) (i : Fin M) (μ : Fin N) {p n : ℕ} (hn : n ≤ 4 * p) {W : ℝ}
    (hW : 1 + chainSq A ≤ W) :
    ‖fCoeff p (avgCoeff Sig A z i μ) n‖ ≤ chainK1 τ p * ((N : ℝ) * W) ^ (5 * p) := by
  have h := chain_rough_fCoeff hset hN hz A i μ p n
  have hKr := chainKr_ge_one hset.pos
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs := chainSq_nonneg A
  have hNW : 1 ≤ (N : ℝ) * W := by nlinarith
  have hb1 : 1 ≤ 2 * chainKr τ * ((N : ℝ) * W) := by nlinarith
  have hb : 2 * (chainKr τ * (N * (1 + chainSq A))) ≤ 2 * chainKr τ * ((N : ℝ) * W) := by
    have : (N : ℝ) * (1 + chainSq A) ≤ N * W := mul_le_mul_of_nonneg_left hW (by linarith)
    nlinarith
  have hn1 : (n : ℝ) + 1 ≤ 4 * p + 1 := by
    have : (n : ℝ) ≤ 4 * p := by exact_mod_cast hn
    linarith
  refine h.trans ?_
  calc ((n : ℝ) + 1) ^ p * (2 * (chainKr τ * (N * (1 + chainSq A)))) ^ (n + p)
      ≤ (4 * p + 1 : ℝ) ^ p * (2 * (chainKr τ * (N * (1 + chainSq A)))) ^ (n + p) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hn1 p) (by positivity)
    _ ≤ (4 * p + 1 : ℝ) ^ p * (2 * chainKr τ * ((N : ℝ) * W)) ^ (5 * p) :=
        mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (by positivity) hb _).trans
          (pow_le_pow_right₀ hb1 (by omega))) (by positivity)
    _ = chainK1 τ p * ((N : ℝ) * W) ^ (5 * p) := by unfold chainK1; rw [mul_pow]; ring

/-- `|R_l(t)| ≤ K₂ (N W)^{9p}` for `l ≤ 4p` and `1 + ‖A‖_F² + t² ≤ W`. -/
private theorem chain_rough_R {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) {z : ℂ} (hz : z ∈ S)
    (A : Matrix (Fin M) (Fin N) ℝ) (i : Fin M) (μ : Fin N) {p l : ℕ} (hl : l ≤ 4 * p) (t : ℝ)
    {W : ℝ} (hW : 1 + chainSq A + t ^ 2 ≤ W) :
    ‖chainRem Sig A z i μ p l t‖ ≤ chainK2 τ p * ((N : ℝ) * W) ^ (9 * p) := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs := chainSq_nonneg A
  have hW1 : 1 ≤ W := by nlinarith [sq_nonneg t]
  have hNW : 1 ≤ (N : ℝ) * W := by nlinarith
  have hK1 := chainK1_nonneg hset.pos p
  set Φ : ℝ := (N : ℝ) * W with hΦ
  have hWt : 1 + chainSq (Xupd A i μ t) ≤ W := by
    have := chainSq_Xupd_le A i μ t; linarith
  have hW0 : 1 + chainSq (Xupd A i μ 0) ≤ W := by
    have := chainSq_Xupd_le A i μ 0; nlinarith [sq_nonneg t]
  have ht : |t| ≤ Φ := by
    have h1 : |t| ≤ 1 + t ^ 2 := by nlinarith [abs_nonneg t, sq_abs t, sq_nonneg (|t| - 1)]
    have h2 : W ≤ Φ := le_mul_of_one_le_left (by linarith) hN1r
    nlinarith
  have hterm : ∀ k ∈ Finset.range (4 * p - l + 1),
      ‖((l + k).choose l : ℂ) * (t : ℂ) ^ k *
          fCoeff p (avgCoeff Sig (Xupd A i μ 0) z i μ) (l + k)‖
        ≤ 2 ^ (4 * p) * (chainK1 τ p * Φ ^ (9 * p)) := by
    intro k hk
    have hk' : k ≤ 4 * p - l := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]
    have hc : ((l + k).choose l : ℝ) ≤ 2 ^ (4 * p) := by
      have := Nat.choose_le_two_pow (l + k) l
      have h2 : 2 ^ (l + k) ≤ 2 ^ (4 * p) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact_mod_cast this.trans h2
    have htk : |t| ^ k ≤ Φ ^ (4 * p) :=
      (pow_le_pow_left₀ (abs_nonneg t) ht k).trans (pow_le_pow_right₀ hNW (by omega))
    have hf := chain_rough_f_le hset hN hz (Xupd A i μ 0) i μ (p := p) (n := l + k) (by omega)
      hW0
    have e : Φ ^ (9 * p) = Φ ^ (4 * p) * Φ ^ (5 * p) := by rw [← pow_add]; ring_nf
    rw [e]
    have h0 : 0 ≤ |t| ^ k := by positivity
    calc ((l + k).choose l : ℝ) * |t| ^ k * ‖fCoeff p (avgCoeff Sig (Xupd A i μ 0) z i μ) (l + k)‖
        ≤ 2 ^ (4 * p) * Φ ^ (4 * p) * (chainK1 τ p * Φ ^ (5 * p)) := by
          gcongr
      _ = 2 ^ (4 * p) * (chainK1 τ p * (Φ ^ (4 * p) * Φ ^ (5 * p))) := by ring
  have hsum := (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hfl := chain_rough_f_le hset hN hz (Xupd A i μ t) i μ (p := p) (n := l) hl hWt
  have h59 : Φ ^ (5 * p) ≤ Φ ^ (9 * p) := pow_le_pow_right₀ hNW (by omega)
  have hcard : ((4 * p - l + 1 : ℕ) : ℝ) ≤ 4 * p + 1 := by
    have : 4 * p - l + 1 ≤ 4 * p + 1 := by omega
    exact_mod_cast this
  unfold chainRem
  refine (norm_sub_le _ _).trans ?_
  have hΦ0 : 0 ≤ Φ ^ (9 * p) := by positivity
  have hA0 : 0 ≤ 2 ^ (4 * p) * (chainK1 τ p * Φ ^ (9 * p)) := by positivity
  calc _ ≤ chainK1 τ p * Φ ^ (5 * p) +
        ((4 * p - l + 1 : ℕ) : ℝ) * (2 ^ (4 * p) * (chainK1 τ p * Φ ^ (9 * p))) :=
        add_le_add hfl hsum
    _ ≤ chainK1 τ p * Φ ^ (9 * p) +
        (4 * p + 1) * (2 ^ (4 * p) * (chainK1 τ p * Φ ^ (9 * p))) := by
        gcongr
    _ = chainK2 τ p * Φ ^ (9 * p) := by unfold chainK2; ring

/-- Expectation of the re-expansion: for `y` independent of `X^{(iμ),0}`,
`E f_l(y) = ∑_k C(l+k, l) E y^k E f_{l+k}(0) + E R_l`, and Lemma 7.7 bounds `|E R_l| ≤ 2N^δ Γ`
on the event `|R_l| ≤ Γ`. -/
private theorem chain_expect {τ c : ℝ} {C : ℕ → ℝ} {p : ℕ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    {S : Set ℂ} (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) {z : ℂ} (hz : z ∈ S)
    (i : Fin M) (μ : Fin N)
    {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} {y : Ω → ℝ} (hX : EntryAssumption C X)
    (hy : Measurable y)
    (hym : ∀ q : ℕ, Integrable (fun ω => |Real.sqrt N * y ω| ^ q) ∧
      ∫ ω, |Real.sqrt N * y ω| ^ q ≤ C q)
    (hind : IndepFun (fun ω => Xupd (X ω) i μ 0) y) (l : ℕ) (hl : l ≤ 4 * p)
    {δ D Γ : ℝ} (hδ : 0 ≤ δ) (hD : 3 * (54 * (p : ℝ) + 1) ≤ D)
    (hΓ : (N : ℝ) ^ (-(54 * (p : ℝ) + 1)) ≤ Γ)
    (hK : chainK2 τ p ^ 2 * chainKW τ C (18 * p) ≤ N)
    (hev : HighProbAt N D {ω | ‖chainRem Sig (X ω) z i μ p l (y ω)‖ ≤ Γ}) :
    (∀ n ≤ 4 * p, Integrable fun ω => fCoeff p (avgCoeff Sig (Xupd (X ω) i μ 0) z i μ) n) ∧
    (∫ ω, fCoeff p (avgCoeff Sig (Xupd (X ω) i μ (y ω)) z i μ) l) =
      (∑ k ∈ Finset.range (4 * p - l + 1), ((l + k).choose l : ℂ) * (∫ ω, (y ω : ℂ) ^ k) *
        (∫ ω, fCoeff p (avgCoeff Sig (Xupd (X ω) i μ 0) z i μ) (l + k))) +
        ∫ ω, chainRem Sig (X ω) z i μ p l (y ω) ∧
    ‖∫ ω, chainRem Sig (X ω) z i μ p l (y ω)‖ ≤ 2 * (N : ℝ) ^ δ * Γ := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hSig := hset.sigma.posDef
  have hη : 0 < z.im := (hset.domain.1 hz).1
  have hM : (M : ℝ) ≤ τ⁻¹ * N := by
    have := hset.ratio_le
    rwa [div_le_iff₀ hNp] at this
  have hXm : Measurable X :=
    measurable_pi_iff.2 fun j => measurable_pi_iff.2 fun ν => hX.measurable j ν
  set W : Ω → ℝ := fun ω => 1 + chainSq (X ω) + y ω ^ 2 with hW
  have hW1 : ∀ ω, 1 ≤ W ω := fun ω => by
    have := chainSq_nonneg (X ω); simp only [hW]; nlinarith [sq_nonneg (y ω)]
  have hmom := chain_moment_W hset.pos hX hy hym hN hM
  have hK1 := chainK1_nonneg hset.pos p
  have hint : ∀ (g : Ω → ℂ) (K : ℝ) (q : ℕ), AEStronglyMeasurable g →
      (∀ ω, ‖g ω‖ ≤ K * ((N : ℝ) * W ω) ^ q) → Integrable g := by
    intro g K q hg hb
    refine ((hmom q).1.const_mul (K * (N : ℝ) ^ q)).mono' hg (ae_of_all _ fun ω => ?_)
    refine (hb ω).trans (le_of_eq ?_)
    rw [mul_pow]; ring
  have hcont0 : ∀ n, Continuous fun A : Matrix (Fin M) (Fin N) ℝ =>
      fCoeff p (avgCoeff Sig A z i μ) n :=
    fun n => chain_continuous_fCoeff p n fun k => chain_continuous_avgCoeff hSig hη i μ k
  have hXupd0 : Measurable fun ω => Xupd (X ω) i μ 0 :=
    (chain_continuous_Xupd i μ).measurable.comp (hXm.prodMk measurable_const)
  have hF0m : ∀ n, AEStronglyMeasurable fun ω =>
      fCoeff p (avgCoeff Sig (Xupd (X ω) i μ 0) z i μ) n :=
    fun n => ((hcont0 n).measurable.comp hXupd0).aestronglyMeasurable
  have hFym : AEStronglyMeasurable fun ω =>
      fCoeff p (avgCoeff Sig (Xupd (X ω) i μ (y ω)) z i μ) l :=
    ((chain_continuous_fCoeff_upd hSig hη i μ p l).measurable.comp
      (hXm.prodMk hy)).aestronglyMeasurable
  have hpowm : ∀ k : ℕ, Measurable fun t : ℝ => (t : ℂ) ^ k :=
    fun k => Complex.measurable_ofReal.pow_const k
  have hym' : ∀ k : ℕ, AEStronglyMeasurable fun ω => (y ω : ℂ) ^ k :=
    fun k => ((hpowm k).comp hy).aestronglyMeasurable
  have hW0 : ∀ ω, 1 + chainSq (Xupd (X ω) i μ 0) ≤ W ω := fun ω => by
    have := chainSq_Xupd_le (X ω) i μ 0; simp only [hW]; nlinarith [sq_nonneg (y ω)]
  have hWy : ∀ ω, 1 + chainSq (Xupd (X ω) i μ (y ω)) ≤ W ω := fun ω => by
    have := chainSq_Xupd_le (X ω) i μ (y ω); simp only [hW]; linarith
  have hNW : ∀ ω, 1 ≤ (N : ℝ) * W ω := fun ω => by nlinarith [hW1 ω]
  have hF0i : ∀ n ≤ 4 * p, Integrable fun ω =>
      fCoeff p (avgCoeff Sig (Xupd (X ω) i μ 0) z i μ) n :=
    fun n hn => hint _ _ _ (hF0m n) fun ω =>
      chain_rough_f_le hset hN hz _ i μ hn (hW0 ω)
  have hFyi : Integrable fun ω => fCoeff p (avgCoeff Sig (Xupd (X ω) i μ (y ω)) z i μ) l :=
    hint _ _ _ hFym fun ω => chain_rough_f_le hset hN hz _ i μ hl (hWy ω)
  have hyk : ∀ k ≤ 4 * p, ∀ ω, ‖(y ω : ℂ) ^ k‖ ≤ ((N : ℝ) * W ω) ^ (4 * p) := by
    intro k hk ω
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |y ω| ≤ (N : ℝ) * W ω := by
      have h2 : |y ω| ≤ 1 + y ω ^ 2 := by
        nlinarith [abs_nonneg (y ω), sq_abs (y ω), sq_nonneg (|y ω| - 1)]
      have h3 : W ω ≤ (N : ℝ) * W ω := le_mul_of_one_le_left (by linarith [hW1 ω]) hN1r
      have := chainSq_nonneg (X ω)
      simp only [hW] at h3 ⊢
      linarith
    exact (pow_le_pow_left₀ (abs_nonneg _) h1 k).trans (pow_le_pow_right₀ (hNW ω) hk)
  have hprodi : ∀ k ∈ Finset.range (4 * p - l + 1), Integrable fun ω =>
      (y ω : ℂ) ^ k * fCoeff p (avgCoeff Sig (Xupd (X ω) i μ 0) z i μ) (l + k) := by
    intro k hk
    have hk' : k ≤ 4 * p - l := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    refine hint _ (chainK1 τ p) (4 * p + 5 * p) ((hym' k).mul (hF0m (l + k))) fun ω => ?_
    rw [norm_mul, pow_add]
    have h1 := hyk k (by omega) ω
    have h2 := chain_rough_f_le hset hN hz (Xupd (X ω) i μ 0) i μ (p := p) (n := l + k)
      (by omega) (hW0 ω)
    calc _ ≤ ((N : ℝ) * W ω) ^ (4 * p) * (chainK1 τ p * ((N : ℝ) * W ω) ^ (5 * p)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (pow_nonneg (by linarith [hNW ω]) _)
      _ = _ := by ring
  have hprod : ∀ k : ℕ, ∫ ω, (y ω : ℂ) ^ k *
      fCoeff p (avgCoeff Sig (Xupd (X ω) i μ 0) z i μ) (l + k) =
      (∫ ω, (y ω : ℂ) ^ k) * ∫ ω, fCoeff p (avgCoeff Sig (Xupd (X ω) i μ 0) z i μ) (l + k) :=
    fun k => (hind.symm.comp (hpowm k) (hcont0 (l + k)).measurable).integral_fun_mul_eq_mul_integral
      (hym' k) (hF0m (l + k))
  set Rf : Ω → ℂ := fun ω => chainRem Sig (X ω) z i μ p l (y ω) with hRf
  set Sf : Ω → ℂ := fun ω => ∑ k ∈ Finset.range (4 * p - l + 1), ((l + k).choose l : ℂ) *
      ((y ω : ℂ) ^ k * fCoeff p (avgCoeff Sig (Xupd (X ω) i μ 0) z i μ) (l + k)) with hSf
  have hSi : Integrable Sf := integrable_finsetSum _ fun k hk => (hprodi k hk).const_mul _
  have hdec : ∀ ω, fCoeff p (avgCoeff Sig (Xupd (X ω) i μ (y ω)) z i μ) l = Sf ω + Rf ω := by
    intro ω
    simp only [hSf, hRf, chainRem]
    rw [Finset.sum_congr rfl fun k _ => (mul_assoc ((l + k).choose l : ℂ) ((y ω : ℂ) ^ k)
      (fCoeff p (avgCoeff Sig (Xupd (X ω) i μ 0) z i μ) (l + k))).symm]
    ring
  have hRi : Integrable Rf := by
    have : Rf = fun ω => fCoeff p (avgCoeff Sig (Xupd (X ω) i μ (y ω)) z i μ) l - Sf ω := by
      funext ω; rw [hdec ω]; ring
    rw [this]; exact hFyi.sub hSi
  refine ⟨hF0i, ?_, ?_⟩
  · calc (∫ ω, fCoeff p (avgCoeff Sig (Xupd (X ω) i μ (y ω)) z i μ) l)
        = ∫ ω, (Sf ω + Rf ω) := integral_congr_ae (ae_of_all _ hdec)
      _ = (∫ ω, Sf ω) + ∫ ω, Rf ω := integral_add hSi hRi
      _ = _ := by
          congr 1
          rw [hSf, integral_finsetSum _ fun k hk => (hprodi k hk).const_mul _]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [integral_const_mul, hprod k]
          ring
  · -- Lemma 7.7
    set Cr : ℝ := 54 * (p : ℝ) + 1 with hCr
    have hRb : ∀ ω, ‖Rf ω‖ ≤ chainK2 τ p * ((N : ℝ) * W ω) ^ (9 * p) := fun ω =>
      chain_rough_R hset hN hz (X ω) i μ hl (y ω) le_rfl
    have hK2 : 0 ≤ chainK2 τ p := by
      unfold chainK2; positivity
    have hRm : AEStronglyMeasurable fun ω => ‖Rf ω‖ ^ 2 := hRi.aestronglyMeasurable.norm.pow 2
    have hR2b : ∀ ω, ‖Rf ω‖ ^ 2 ≤ chainK2 τ p ^ 2 * (N : ℝ) ^ (18 * p) * W ω ^ (18 * p) := by
      intro ω
      have h := pow_le_pow_left₀ (norm_nonneg _) (hRb ω) 2
      refine h.trans (le_of_eq ?_)
      rw [mul_pow, ← pow_mul, mul_pow]; ring_nf
    have hR2i : Integrable fun ω => ‖Rf ω‖ ^ 2 :=
      ((hmom (18 * p)).1.const_mul (chainK2 τ p ^ 2 * (N : ℝ) ^ (18 * p))).mono' hRm
        (ae_of_all _ fun ω => by
          rw [Real.norm_of_nonneg (by positivity)]
          refine (hR2b ω).trans (le_of_eq ?_); ring)
    have hR2E : ∫ ω, ‖Rf ω‖ ^ 2 ≤ (N : ℝ) ^ Cr := by
      calc ∫ ω, ‖Rf ω‖ ^ 2 ≤ ∫ ω, chainK2 τ p ^ 2 * (N : ℝ) ^ (18 * p) * W ω ^ (18 * p) :=
            integral_mono hR2i ((hmom (18 * p)).1.const_mul _) hR2b
        _ = chainK2 τ p ^ 2 * (N : ℝ) ^ (18 * p) * ∫ ω, W ω ^ (18 * p) := integral_const_mul _ _
        _ ≤ chainK2 τ p ^ 2 * (N : ℝ) ^ (18 * p) *
            (chainKW τ C (18 * p) * (N : ℝ) ^ (2 * (18 * p))) :=
            mul_le_mul_of_nonneg_left (hmom (18 * p)).2 (by positivity)
        _ = (chainK2 τ p ^ 2 * chainKW τ C (18 * p)) * (N : ℝ) ^ (54 * p) := by
            rw [show 54 * p = 18 * p + 2 * (18 * p) by ring, pow_add]; ring
        _ ≤ (N : ℝ) * (N : ℝ) ^ (54 * p) := by gcongr
        _ = (N : ℝ) ^ Cr := by
            rw [hCr, show (54 * (p : ℝ) + 1) = ((54 * p + 1 : ℕ) : ℝ) by push_cast; ring,
              Real.rpow_natCast, pow_succ]; ring
    have hΓ0 : 0 ≤ Γ := (Real.rpow_nonneg hNp.le _).trans hΓ
    have hdom : DomAt N δ D (fun ω => ‖Rf ω‖) (fun _ => Γ) := by
      unfold DomAt
      unfold HighProbAt at hev
      refine le_trans (measure_mono fun ω hω => ?_) hev
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le] at hω ⊢
      have : Γ ≤ (N : ℝ) ^ δ * Γ := le_mul_of_one_le_left hΓ0 (Real.one_le_rpow hN1r hδ)
      exact lt_of_le_of_lt this hω
    have h77 := integral_le_of_domAt (ξ := fun ω => ‖Rf ω‖) hN hδ (C := Cr) hD
      (by rw [hCr]; exact hΓ) (fun ω => norm_nonneg _) hR2i hR2E hdom
    exact (norm_integral_le_integral_norm _).trans h77

/-- `N^{−(54p+1)} ≤ N^{l/2−2} Ψ^{2p}` on `𝐃(τ, N)` for `N ≥ τ⁻¹`. -/
private theorem chain_Gamma_ge {τ : ℝ} {p l : ℕ} {σ : Fin M → ℝ} {z : ℂ} (hN : 1 ≤ N)
    (hp2 : 2 ≤ p) (hτ : 0 < τ) (hτN : τ⁻¹ ≤ N) (hz : z ∈ specDomain τ N) :
    (N : ℝ) ^ (-(54 * (p : ℝ) + 1)) ≤ (N : ℝ) ^ ((l : ℝ) / 2 - 2) * Psi N σ z ^ (2 * p) := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hΨ := chain_Psi_ge (σ := σ) hN hτ hz
  have h1 : (N : ℝ) ^ (-2 : ℝ) ≤ Psi N σ z := by
    refine le_trans ?_ hΨ
    rw [Real.rpow_neg hNp.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      le_div_iff₀ hNp]
    have hτ' : (N : ℝ)⁻¹ ≤ τ := by
      rw [inv_le_comm₀ hNp hτ]; exact hτN
    calc ((N : ℝ) ^ 2)⁻¹ * N = (N : ℝ)⁻¹ := by field_simp
      _ ≤ τ := hτ'
  have h2 : ((N : ℝ) ^ (-2 : ℝ)) ^ (2 * p) ≤ Psi N σ z ^ (2 * p) :=
    pow_le_pow_left₀ (Real.rpow_nonneg hNp.le _) h1 (2 * p)
  rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le] at h2
  have h3 : (N : ℝ) ^ (-2 : ℝ) ≤ (N : ℝ) ^ ((l : ℝ) / 2 - 2) :=
    Real.rpow_le_rpow_of_exponent_le hN1r (by have := (Nat.cast_nonneg l : (0 : ℝ) ≤ l); linarith)
  have hp0 : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  calc (N : ℝ) ^ (-(54 * (p : ℝ) + 1)) ≤ (N : ℝ) ^ ((-2 : ℝ) + -2 * ((2 * p : ℕ) : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hN1r (by push_cast; linarith)
    _ = (N : ℝ) ^ (-2 : ℝ) * (N : ℝ) ^ (-2 * ((2 * p : ℕ) : ℝ)) := Real.rpow_add hNp _ _
    _ ≤ (N : ℝ) ^ ((l : ℝ) / 2 - 2) * Psi N σ z ^ (2 * p) :=
        mul_le_mul h3 h2 (Real.rpow_nonneg hNp.le _) (Real.rpow_nonneg hNp.le _)

/-- `dPrevTwo τ p ≤ D_a` gives `3 (54p + 1) ≤ D_a − 3`. -/
private theorem chain_D_ge {τ : ℝ} {p : ℕ} {Da : ℝ} (hp2 : 2 ≤ p) (hDa : dPrevTwo τ p ≤ Da) :
    3 * (54 * (p : ℝ) + 1) ≤ Da - 3 := by
  have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hk : (1 : ℝ) ≤ (kTau τ : ℝ) + 1 := by
    have := (Nat.cast_nonneg (kTau τ) : (0 : ℝ) ≤ _); linarith
  have h0 : 0 ≤ dPrev p := by unfold dPrev; positivity
  have h1 : dPrev p ≤ dPrevTwo τ p := by
    unfold dPrevTwo; exact le_mul_of_one_le_right h0 hk
  unfold dPrev at h1
  nlinarith

/-! ## Moment matching -/

/-- (moment_matching) for `F̃^p` without (zero_third_moment): the sum starts at `n = 3`. -/
theorem avg_moment_matching (τ c : ℝ) (C : ℕ → ℝ) (p : ℕ) (εa Da : ℝ) (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (hc : 0 < c) (hp : Even p) (hp2 : 2 ≤ p) (hεa : 0 < εa) (hεaτ : 16 * εa ≤ τ)
    (hεap : 100 * p * εa ≤ 1) (hDa : dPrevTwo τ p ≤ Da) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ),
      CompSetting τ c M N Sig S → AnisoAllAt N C Sig S εa Da →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ) (y : Ω → ℝ), EntryAssumption C X →
        IndepFun X y → Measurable y → ∫ ω, y ω = 0 → ∫ ω, y ω ^ 2 = 1 / (N : ℝ) →
        (∀ q : ℕ, Integrable (fun ω => |Real.sqrt N * y ω| ^ q) ∧
          ∫ ω, |Real.sqrt N * y ω| ^ q ≤ C q) →
        ∀ z ∈ S, ∀ (i : Fin M) (μ : Fin N),
          ‖(∫ ω, (Ft Sig (Xupd (X ω) i μ (y ω)) z : ℂ) ^ p)
              - (∫ ω, (fCoeff p (avgCoeff Sig (Xupd (X ω) i μ 0) z i μ) 0
                  + (N : ℂ)⁻¹ * fCoeff p (avgCoeff Sig (Xupd (X ω) i μ 0) z i μ) 2))
              - ∑ n ∈ Finset.Icc 3 (4 * p),
                  (∫ ω, fCoeff p (avgCoeff Sig (Xupd (X ω) i μ 0) z i μ) n) *
                    ∫ ω, (y ω : ℂ) ^ n‖
            ≤ 2 * (N : ℝ) ^ (-2 : ℝ) * Psi N (specOf Sig) z ^ (2 * p) := by
  have _hεaτ := hεaτ
  obtain ⟨N₁, h₁⟩ := chain_event τ c C p εa Da hτ hτ1 hc hp2 hεa hεap
  obtain ⟨N₂, h₂⟩ := chain_markov C εa Da hεa
  set Km := mBoundConst τ with hKm
  have hKm0 : 0 < Km := mBoundConst_pos hτ
  set K₁ : ℝ := ((4 * p + 1).factorial : ℝ) * Km ^ p with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  set K₃ : ℝ := chainK2 τ p ^ 2 * chainKW τ C (18 * p) with hK₃
  refine ⟨max (max (max N₁ N₂) (max 1 ⌈K₁ ^ (1 / 10 : ℝ)⁻¹⌉₊)) (max ⌈K₃⌉₊ ⌈τ⁻¹⌉₊), ?_⟩
  intro N hN M Sig S hset hA Ω _ _ X y hX hXY hy hy1 hy2 hym z hz i μ
  have hNN₁ : N₁ ≤ N := by omega
  have hNN₂ : N₂ ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hNK₁ : ⌈K₁ ^ (1 / 10 : ℝ)⁻¹⌉₊ ≤ N := by omega
  have hNK₃ : ⌈K₃⌉₊ ≤ N := by omega
  have hNτ : ⌈τ⁻¹⌉₊ ≤ N := by omega
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : (0 : ℝ) < N := by linarith
  have hN10 : ((4 * p + 1).factorial : ℝ) * Km ^ p ≤ (N : ℝ) ^ (1 / 10 : ℝ) :=
    chain_le_rpow hK₁0 (by norm_num) hNK₁
  have hK : K₃ ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hNK₃)
  have hτN : τ⁻¹ ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hNτ)
  have hzD := hset.domain.1 hz
  have hSig := hset.sigma.posDef
  have hyHP := h₂ N hNN₂ y hym
  have hev := h₁ N hNN₁ M Sig S hset hA Ω X y hX hyHP z hz i μ
  set Γ : ℝ := (N : ℝ) ^ (((0 : ℕ) : ℝ) / 2 - 2) * Psi N (specOf Sig) z ^ (2 * p) with hΓ
  have hevR : HighProbAt N (Da - 3)
      {ω | ‖chainRem Sig (X ω) z i μ p 0 (y ω)‖ ≤ Γ} := by
    refine chain_hp_mono (fun ω hω => ?_) hev
    exact chain_rem_det hp2 hεa hεap hN1 hKm0 hN10 (chain_Psi_sq_ge hset hN1 hz)
      (fun k x => chain_hasDerivAt_avgCoeff hSig (X ω) hzD.1 i μ k x) (y ω) hω.1
      (fun s hs => hω.2 s hs (4 * p + 1) le_rfl) 0 (by omega)
  have hind : IndepFun (fun ω => Xupd (X ω) i μ 0) y :=
    hXY.comp (chain_measurable_Xupd i μ 0) measurable_id
  obtain ⟨hF0i, hid, hR⟩ := chain_expect hset hN1 hz i μ hX hy hym hind 0 (Nat.zero_le _)
    le_rfl (chain_D_ge hp2 hDa) (chain_Gamma_ge hN1 hp2 hτ hτN hzD) hK hevR
  simp only [Nat.sub_zero, zero_add, Nat.choose_zero_right, Nat.cast_one, one_mul] at hid
  have hFt : (∫ ω, (Ft Sig (Xupd (X ω) i μ (y ω)) z : ℂ) ^ p) =
      ∫ ω, fCoeff p (avgCoeff Sig (Xupd (X ω) i μ (y ω)) z i μ) 0 :=
    integral_congr_ae (ae_of_all _ fun ω => (fCoeff_avgCoeff_zero hp Sig _ z i μ hN1).symm)
  have hA02 : (∫ ω, (fCoeff p (avgCoeff Sig (Xupd (X ω) i μ 0) z i μ) 0
      + (N : ℂ)⁻¹ * fCoeff p (avgCoeff Sig (Xupd (X ω) i μ 0) z i μ) 2)) =
      (∫ ω, fCoeff p (avgCoeff Sig (Xupd (X ω) i μ 0) z i μ) 0) +
        (N : ℂ)⁻¹ * ∫ ω, fCoeff p (avgCoeff Sig (Xupd (X ω) i μ 0) z i μ) 2 := by
    rw [integral_add (hF0i 0 (by omega)) ((hF0i 2 (by omega)).const_mul _), integral_const_mul]
  have hm0 : ∫ ω, (y ω : ℂ) ^ 0 = 1 := by simp
  have hm1 : ∫ ω, (y ω : ℂ) ^ 1 = 0 := by
    rw [chain_integral_ofReal_pow]; simp [hy1]
  have hm2 : ∫ ω, (y ω : ℂ) ^ 2 = (N : ℂ)⁻¹ := by
    rw [chain_integral_ofReal_pow, hy2]; push_cast; ring
  set a : ℕ → ℂ := fun n => ∫ ω, fCoeff p (avgCoeff Sig (Xupd (X ω) i μ 0) z i μ) n with ha
  set mm : ℕ → ℂ := fun n => ∫ ω, (y ω : ℂ) ^ n with hmm
  have hsplit : ∑ k ∈ Finset.range (4 * p + 1), mm k * a k =
      mm 0 * a 0 + mm 1 * a 1 + mm 2 * a 2 +
        ∑ n ∈ Finset.Icc 3 (4 * p), a n * mm n := by
    rw [← Finset.sum_range_add_sum_Ico _ (show 3 ≤ 4 * p + 1 by omega)]
    have e : Finset.Icc 3 (4 * p) = Finset.Ico 3 (4 * p + 1) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [e]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    congr 1
    exact Finset.sum_congr rfl fun n _ => mul_comm _ _
  have hid' : (∫ ω, fCoeff p (avgCoeff Sig (Xupd (X ω) i μ (y ω)) z i μ) 0) =
      (∑ k ∈ Finset.range (4 * p + 1), mm k * a k) +
        ∫ ω, chainRem Sig (X ω) z i μ p 0 (y ω) := hid
  rw [hFt, hA02, hid', hsplit]
  simp only [hmm, hm0, hm1, hm2, one_mul, zero_mul, add_zero]
  rw [show ∀ (A0 A2 S0 Rr : ℂ), A0 + (N : ℂ)⁻¹ * A2 + S0 + Rr - (A0 + (N : ℂ)⁻¹ * A2) - S0 = Rr
    from fun _ _ _ _ => by ring]
  refine hR.trans (le_of_eq ?_)
  have e : (N : ℝ) ^ (((0 : ℕ) : ℝ) / 2 - 2) = (N : ℝ) ^ (-2 : ℝ) := by norm_num
  rw [e, Real.rpow_zero]
  ring

/-! ## Lemma 7.16 for `F̃^p` -/

/-- Lemma 7.16 for `F̃^p`, `n ∈ [3, 4p]`: bounds at `X` give bounds at `X^{(iμ),0}`. -/
theorem avg_zero_to_theta (τ c : ℝ) (C : ℕ → ℝ) (p : ℕ) (εa Da : ℝ) (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (hc : 0 < c) (hp : Even p) (hp2 : 2 ≤ p) (hεa : 0 < εa) (hεaτ : 16 * εa ≤ τ)
    (hεap : 100 * p * εa ≤ 1) (hDa : dPrevTwo τ p ≤ Da) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (S : Set ℂ), CompSetting τ c M N Sig S → AnisoAllAt N C Sig S εa Da →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption C X →
        ∀ z ∈ S, ∀ B : ℝ, 0 ≤ B →
          (∀ n ∈ Finset.Icc 3 (4 * p), (N : ℝ) ^ (-(n : ℝ) / 2) *
            ∑ i, ∑ μ, ‖∫ ω, fCoeff p (avgCoeff Sig (X ω) z i μ) n‖ ≤ B) →
          ∀ n ∈ Finset.Icc 3 (4 * p), (N : ℝ) ^ (-(n : ℝ) / 2) *
            ∑ i, ∑ μ, ‖∫ ω, fCoeff p (avgCoeff Sig (Xupd (X ω) i μ 0) z i μ) n‖ ≤
              K * (B + Psi N (specOf Sig) z ^ (2 * p)) := by
  have _hpEven := hp
  have _hεaτ := hεaτ
  set L := chainL C p with hLdef
  have hL0 : 0 ≤ L := chainL_nonneg C p
  set Q : ℝ := 1 + 4 * p * L with hQ
  have hQ1 : 1 ≤ Q := by
    have : (0 : ℝ) ≤ 4 * p * L := by positivity
    linarith
  refine ⟨Q ^ (4 * p) * (1 + 2 * τ⁻¹), by positivity, ?_⟩
  obtain ⟨N₁, h₁⟩ := chain_event τ c C p εa Da hτ hτ1 hc hp2 hεa hεap
  obtain ⟨N₂, h₂⟩ := chain_markov C εa Da hεa
  set Km := mBoundConst τ with hKm
  have hKm0 : 0 < Km := mBoundConst_pos hτ
  set K₁ : ℝ := ((4 * p + 1).factorial : ℝ) * Km ^ p with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  set K₃ : ℝ := chainK2 τ p ^ 2 * chainKW τ C (18 * p) with hK₃
  refine ⟨max (max (max N₁ N₂) (max 1 ⌈K₁ ^ (1 / 10 : ℝ)⁻¹⌉₊)) (max ⌈K₃⌉₊ ⌈τ⁻¹⌉₊), ?_⟩
  intro N hN M Sig S hset hA Ω _ _ X hX z hz B hB0 hB
  have hNN₁ : N₁ ≤ N := by omega
  have hNN₂ : N₂ ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hNK₁ : ⌈K₁ ^ (1 / 10 : ℝ)⁻¹⌉₊ ≤ N := by omega
  have hNK₃ : ⌈K₃⌉₊ ≤ N := by omega
  have hNτ : ⌈τ⁻¹⌉₊ ≤ N := by omega
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : (0 : ℝ) < N := by linarith
  have hN10 : ((4 * p + 1).factorial : ℝ) * Km ^ p ≤ (N : ℝ) ^ (1 / 10 : ℝ) :=
    chain_le_rpow hK₁0 (by norm_num) hNK₁
  have hK : K₃ ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hNK₃)
  have hτN : τ⁻¹ ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hNτ)
  have hzD := hset.domain.1 hz
  have hSig := hset.sigma.posDef
  have hD := chain_D_ge hp2 hDa
  have hM : (M : ℝ) ≤ τ⁻¹ * N := by
    have := hset.ratio_le
    rwa [div_le_iff₀ hNp] at this
  set Ψp : ℝ := Psi N (specOf Sig) z ^ (2 * p) with hΨp
  have hΨp0 : 0 ≤ Ψp := by
    have := chain_Psi_ge (σ := specOf Sig) hN1 hτ hzD
    have : 0 ≤ Psi N (specOf Sig) z := le_trans (by positivity) this
    positivity
  set Er : ℝ := 2 * (N : ℝ) ^ (-2 : ℝ) * Ψp with hEr
  set a : Fin M → Fin N → ℕ → ℂ := fun i μ n =>
    ∫ ω, fCoeff p (avgCoeff Sig (Xupd (X ω) i μ 0) z i μ) n with ha
  set b : Fin M → Fin N → ℕ → ℂ := fun i μ n =>
    ∫ ω, fCoeff p (avgCoeff Sig (X ω) z i μ) n with hb
  have hpair : ∀ (i : Fin M) (μ : Fin N) (n : ℕ), n ≤ 4 * p →
      (N : ℝ) ^ (-(n : ℝ) / 2) * ‖a i μ n‖ ≤ (N : ℝ) ^ (-(n : ℝ) / 2) * ‖b i μ n‖ +
        L * ∑ k ∈ Finset.range (4 * p - n),
          (N : ℝ) ^ (-((n + k + 1 : ℕ) : ℝ) / 2) * ‖a i μ (n + k + 1)‖ + Er := by
    intro i μ n hn
    have hym : ∀ q : ℕ, Integrable (fun ω => |Real.sqrt N * X ω i μ| ^ q) ∧
        ∫ ω, |Real.sqrt N * X ω i μ| ^ q ≤ C q :=
      fun q => ⟨hX.integrable_moment q i μ, hX.moment q i μ⟩
    have hyHP := h₂ N hNN₂ (fun ω => X ω i μ) hym
    have hev := h₁ N hNN₁ M Sig S hset hA Ω X (fun ω => X ω i μ) hX hyHP z hz i μ
    have hevR : HighProbAt N (Da - 3) {ω | ‖chainRem Sig (X ω) z i μ p n (X ω i μ)‖ ≤
        (N : ℝ) ^ ((n : ℝ) / 2 - 2) * Ψp} := by
      refine chain_hp_mono (fun ω hω => ?_) hev
      exact chain_rem_det hp2 hεa hεap hN1 hKm0 hN10 (chain_Psi_sq_ge hset hN1 hz)
        (fun k x => chain_hasDerivAt_avgCoeff hSig (X ω) hzD.1 i μ k x) (X ω i μ) hω.1
        (fun s hs => hω.2 s hs (4 * p + 1) le_rfl) n hn
    obtain ⟨-, hid, hR⟩ := chain_expect hset hN1 hz i μ hX (hX.measurable i μ) hym
      (chain_indep_entry hX i μ) n hn le_rfl hD (chain_Gamma_ge hN1 hp2 hτ hτN hzD) hK hevR
    have hb' : b i μ n = ∫ ω, fCoeff p (avgCoeff Sig (Xupd (X ω) i μ (X ω i μ)) z i μ) n := by
      simp only [hb, Xupd_self]
    have hrec := chain_recur_pair hN1 (p := p) (n := n) (a i μ) (b i μ n)
      (∫ ω, chainRem Sig (X ω) z i μ p n (X ω i μ)) (fun k => ∫ ω, (X ω i μ : ℂ) ^ k)
      (fun k => max (C k) 0) L (by rw [hb', hid]) (by simp)
      (fun k => chain_moment_entry hX hN1 i μ k) (fun k hk => chainL_ge (by omega))
    refine hrec.trans (add_le_add le_rfl ?_)
    calc (N : ℝ) ^ (-(n : ℝ) / 2) * ‖∫ ω, chainRem Sig (X ω) z i μ p n (X ω i μ)‖
        ≤ (N : ℝ) ^ (-(n : ℝ) / 2) * (2 * (N : ℝ) ^ (0 : ℝ) *
            ((N : ℝ) ^ ((n : ℝ) / 2 - 2) * Ψp)) :=
          mul_le_mul_of_nonneg_left hR (Real.rpow_nonneg hNp.le _)
      _ = 2 * ((N : ℝ) ^ (-(n : ℝ) / 2) * (N : ℝ) ^ ((n : ℝ) / 2 - 2)) * Ψp := by
          rw [Real.rpow_zero]; ring
      _ = Er := by
          rw [← Real.rpow_add hNp, hEr]
          congr 3
          ring
  set α : ℕ → ℝ := fun n => (N : ℝ) ^ (-(n : ℝ) / 2) * ∑ i, ∑ μ, ‖a i μ n‖ with hα
  have hαsum : ∀ n, α n = ∑ i, ∑ μ, (N : ℝ) ^ (-(n : ℝ) / 2) * ‖a i μ n‖ := by
    intro n; simp only [hα, Finset.mul_sum]
  set E' : ℝ := 2 * τ⁻¹ * Ψp with hE'
  have hE'0 : 0 ≤ E' := by positivity
  have hMN : ∑ _i : Fin M, ∑ _μ : Fin N, Er ≤ E' := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hEr0 : 0 ≤ Er := by positivity
    have e : (N : ℝ) * ((N : ℝ) * (N : ℝ) ^ (-2 : ℝ)) = 1 := by
      rw [Real.rpow_neg hNp.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      field_simp
    calc (M : ℝ) * ((N : ℝ) * Er) ≤ τ⁻¹ * N * ((N : ℝ) * Er) :=
          mul_le_mul_of_nonneg_right hM (by positivity)
      _ = 2 * τ⁻¹ * ((N : ℝ) * ((N : ℝ) * (N : ℝ) ^ (-2 : ℝ))) * Ψp := by rw [hEr]; ring
      _ = E' := by rw [e, hE']; ring
  have hrec : ∀ n, 3 ≤ n → n ≤ 4 * p →
      α n ≤ (B + E') + L * ∑ k ∈ Finset.range (4 * p - n), α (n + k + 1) := by
    intro n h3 hn
    have hβ : (N : ℝ) ^ (-(n : ℝ) / 2) * ∑ i, ∑ μ, ‖b i μ n‖ ≤ B :=
      hB n (Finset.mem_Icc.2 ⟨h3, hn⟩)
    have hs1 : α n ≤ ∑ i, ∑ μ, ((N : ℝ) ^ (-(n : ℝ) / 2) * ‖b i μ n‖ +
        L * ∑ k ∈ Finset.range (4 * p - n),
          (N : ℝ) ^ (-((n + k + 1 : ℕ) : ℝ) / 2) * ‖a i μ (n + k + 1)‖ + Er) := by
      rw [hαsum]
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun μ _ => hpair i μ n hn
    have hs2 : ∑ i, ∑ μ, ((N : ℝ) ^ (-(n : ℝ) / 2) * ‖b i μ n‖ +
        L * ∑ k ∈ Finset.range (4 * p - n),
          (N : ℝ) ^ (-((n + k + 1 : ℕ) : ℝ) / 2) * ‖a i μ (n + k + 1)‖ + Er) =
        (N : ℝ) ^ (-(n : ℝ) / 2) * ∑ i, ∑ μ, ‖b i μ n‖ +
          L * ∑ k ∈ Finset.range (4 * p - n), α (n + k + 1) +
          ∑ _i : Fin M, ∑ _μ : Fin N, Er := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      congr 2
      congr 1
      simp only [hαsum]
      exact (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans Finset.sum_comm
    linarith
  have hind := chain_induct (p := p) α hL0 (by positivity) hrec
  intro n hn
  obtain ⟨h3, hn4⟩ := Finset.mem_Icc.1 hn
  have h1 := hind n h3 hn4
  have h2 : (1 + 4 * (p : ℝ) * L) ^ (4 * p - n) ≤ Q ^ (4 * p) :=
    pow_le_pow_right₀ hQ1 (Nat.sub_le _ _)
  have hBE : 0 ≤ B + E' := by positivity
  have h3' : B + E' ≤ (1 + 2 * τ⁻¹) * (B + Ψp) := by
    have hτ0 : 0 ≤ τ⁻¹ := (inv_pos.2 hτ).le
    rw [hE']
    nlinarith [mul_nonneg hτ0 hB0]
  calc α n ≤ (1 + 4 * (p : ℝ) * L) ^ (4 * p - n) * (B + E') := h1
    _ ≤ Q ^ (4 * p) * ((1 + 2 * τ⁻¹) * (B + Ψp)) :=
        mul_le_mul h2 h3' hBE (by positivity)
    _ = Q ^ (4 * p) * (1 + 2 * τ⁻¹) * (B + Ψp) := by ring

/-! ## Instances

The parameters are `τ = 1/20`, `c = 1/2`, `C(q) = q! + 1`, `p = 2`, `εa = 1/320` (`16 εa = τ`,
`100 p εa = 5/8`), `Da = dPrevTwo (1/20) 2`. The statements are `∃ N₀` statements: the setting,
the a priori law `AnisoAllAt`, the entry conditions, the bound on `y`, the moments and the
independence of `y`, and the bound `B` stay hypotheses (conditional instances). -/

/-- (moment_matching) for `F̃^p` with the `n = 3` term, at the parameters above (conditional
instance). -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ),
      CompSetting (1 / 20) (1 / 2) M N Sig S →
      AnisoAllAt N (fun q => (q.factorial : ℝ) + 1) Sig S (1 / 320) (dPrevTwo (1 / 20) 2) →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ) (y : Ω → ℝ),
        EntryAssumption (fun q => (q.factorial : ℝ) + 1) X →
        IndepFun X y → Measurable y → ∫ ω, y ω = 0 → ∫ ω, y ω ^ 2 = 1 / (N : ℝ) →
        (∀ q : ℕ, Integrable (fun ω => |Real.sqrt N * y ω| ^ q) ∧
          ∫ ω, |Real.sqrt N * y ω| ^ q ≤ (fun q => (q.factorial : ℝ) + 1) q) →
        ∀ z ∈ S, ∀ (i : Fin M) (μ : Fin N),
          ‖(∫ ω, (Ft Sig (Xupd (X ω) i μ (y ω)) z : ℂ) ^ 2)
              - (∫ ω, (fCoeff 2 (avgCoeff Sig (Xupd (X ω) i μ 0) z i μ) 0
                  + (N : ℂ)⁻¹ * fCoeff 2 (avgCoeff Sig (Xupd (X ω) i μ 0) z i μ) 2))
              - ∑ n ∈ Finset.Icc 3 (4 * 2),
                  (∫ ω, fCoeff 2 (avgCoeff Sig (Xupd (X ω) i μ 0) z i μ) n) *
                    ∫ ω, (y ω : ℂ) ^ n‖
            ≤ 2 * (N : ℝ) ^ (-2 : ℝ) * Psi N (specOf Sig) z ^ (2 * 2) :=
  avg_moment_matching (1 / 20) (1 / 2) (fun q => (q.factorial : ℝ) + 1) 2 (1 / 320)
    (dPrevTwo (1 / 20) 2) (by norm_num) (by norm_num) (by norm_num) even_two le_rfl
    (by norm_num) (by norm_num) (by norm_num) le_rfl

/-- Lemma 7.16 for `F̃^p`, `n ∈ [3, 8]`, at the parameters above (conditional instance). -/
example : ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (S : Set ℂ), CompSetting (1 / 20) (1 / 2) M N Sig S →
      AnisoAllAt N (fun q => (q.factorial : ℝ) + 1) Sig S (1 / 320) (dPrevTwo (1 / 20) 2) →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption (fun q => (q.factorial : ℝ) + 1) X →
        ∀ z ∈ S, ∀ B : ℝ, 0 ≤ B →
          (∀ n ∈ Finset.Icc (3 : ℕ) (4 * 2), (N : ℝ) ^ (-(n : ℝ) / 2) *
            ∑ i, ∑ μ, ‖∫ ω, fCoeff 2 (avgCoeff Sig (X ω) z i μ) n‖ ≤ B) →
          ∀ n ∈ Finset.Icc (3 : ℕ) (4 * 2), (N : ℝ) ^ (-(n : ℝ) / 2) *
            ∑ i, ∑ μ, ‖∫ ω, fCoeff 2 (avgCoeff Sig (Xupd (X ω) i μ 0) z i μ) n‖ ≤
              K * (B + Psi N (specOf Sig) z ^ (2 * 2)) :=
  avg_zero_to_theta (1 / 20) (1 / 2) (fun q => (q.factorial : ℝ) + 1) 2 (1 / 320)
    (dPrevTwo (1 / 20) 2) (by norm_num) (by norm_num) (by norm_num) even_two le_rfl
    (by norm_num) (by norm_num) (by norm_num) le_rfl

end Anisotropic
