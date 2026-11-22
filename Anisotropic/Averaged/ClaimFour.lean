module

public import Anisotropic.Averaged.Defs
public import Anisotropic.Comparison.Ladder
public import Anisotropic.Comparison.PrelimBounds
public import Anisotropic.Comparison.WordBounds
public import Anisotropic.Comparison.Words
public import Anisotropic.Entrywise.Defs
public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.Framework.Model

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # (avg_pf_claim) for `n ≥ 4` (§9) -/

/-! ## Linear algebra: `‖XᵀX‖`, `Π`, test vectors -/

private theorem claimF_opNorm_le {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
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
private theorem claimF_XtX_le (A : Matrix (Fin M) (Fin N) ℝ) :
    ‖Aᵀ * A‖ ≤ ∑ α : Fin M × Fin N, A α.1 α.2 ^ 2 := by
  have h1 : ‖Aᵀ * A‖ = ‖A‖ * ‖A‖ := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact l2_opNorm_conjTranspose_mul_self A
  have h2 := claimF_opNorm_le A
  have h0 : 0 ≤ ∑ i, ∑ j, A i j ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [h1, Fintype.sum_prod_type]
  calc ‖A‖ * ‖A‖ ≤ Real.sqrt (∑ i, ∑ j, A i j ^ 2) * Real.sqrt (∑ i, ∑ j, A i j ^ 2) :=
        mul_le_mul h2 h2 (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := Real.mul_self_sqrt h0

private theorem claimF_ent_eq {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (x y : ι → ℝ) :
    ent A x y = ∑ s, ∑ t, (x s : ℂ) * A s t * (y t : ℂ) := by
  simp only [ent, cvec, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

private theorem claimF_ent_eI_right {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (x : ι → ℝ) (r : ι) : ent A x (eI r) = ∑ s, (x s : ℂ) * A s r := by
  rw [claimF_ent_eq]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [eI, Pi.single_apply, apply_ite]

private theorem claimF_diag {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) :
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

private theorem claimF_sum_sq_UT {K : ℕ} {U : Matrix (Fin K) (Fin K) ℝ} (h₂ : U * Uᵀ = 1)
    (x : Fin K → ℝ) : ∑ i, (Uᵀ *ᵥ x) i ^ 2 = ∑ i, x i ^ 2 := by
  have e : (Uᵀ *ᵥ x) ⬝ᵥ (Uᵀ *ᵥ x) = x ⬝ᵥ x := by
    rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, h₂, one_mulVec, dotProduct_comm]
  simpa [dotProduct, sq] using e

private theorem claimF_row_sq {K : ℕ} {U : Matrix (Fin K) (Fin K) ℝ} (h₂ : U * Uᵀ = 1) (i : Fin K) :
    ∑ k, U i k ^ 2 = 1 := by
  have := congrFun (congrFun h₂ i) i
  simpa [Matrix.mul_apply, sq, Matrix.one_apply] using this

/-- `|Σ x|² ≤ τ⁻² |x|²` under (bound_Sigma). -/
private theorem claimF_sumsq_Sig {τ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hS : SigmaAssumption τ Sig) (x : Fin M → ℝ) :
    ∑ l, (Sig *ᵥ x) l ^ 2 ≤ τ⁻¹ ^ 2 * ∑ l, x l ^ 2 := by
  obtain ⟨U, h₂, h₁, hSd, hσ⟩ := claimF_diag hS.posDef
  have hle : ∀ k, specOf Sig k ≤ τ⁻¹ := fun k => by
    rw [specOf_eq hS.posDef.isHermitian]; exact hS.eigenvalues_le k
  have hUU : Uᵀ * Uᵀᵀ = 1 := by rw [transpose_transpose]; exact h₁
  have e : Sig *ᵥ x = Uᵀᵀ *ᵥ (diagonal (specOf Sig) *ᵥ (Uᵀ *ᵥ x)) := by
    rw [transpose_transpose, mulVec_mulVec, mulVec_mulVec]
    exact congrArg (· *ᵥ x) hSd
  rw [e, claimF_sum_sq_UT hUU, ← claimF_sum_sq_UT h₂ x, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [mulVec_diagonal, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hσ k).le (hle k) 2) (sq_nonneg _)

/-- `|Σ̲ y| ≤ τ⁻¹ |y|`. -/
private theorem claimF_testNorm_SigU {τ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hS : SigmaAssumption τ Sig) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (y : Fin M ⊕ Fin N → ℝ) :
    testNorm (SigU (n := Fin N) Sig *ᵥ y) ≤ τ⁻¹ * testNorm y := by
  have hτi : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  have h1 := claimF_sumsq_Sig hS (y ∘ Sum.inl)
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
private theorem claimF_vbar_SigU {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (y : Fin M ⊕ Fin N → ℝ) : vbar Sig (SigU (n := Fin N) Sig *ᵥ y) = y := by
  have hS : Sig⁻¹ * Sig = 1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hSig.isUnit)
  funext s
  rcases s with j | ν
  · simp [vbar, SigU, fromBlocks_mulVec, mulVec_mulVec, hS]
  · simp [vbar, SigU, fromBlocks_mulVec]

/-- `(1 + wΣ)⁻¹_{li} = ∑ₖ U_{lk} (1 + σₖ w)⁻¹ U_{ik}`. -/
private theorem claimF_cinv_entry {Sig U : Matrix (Fin M) (Fin M) ℝ} {σ : Fin M → ℝ}
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

private theorem claimF_abs_le_testNorm {ι : Type*} [Fintype ι] (x : ι → ℝ) (s : ι) :
    |x s| ≤ testNorm x := by
  unfold testNorm
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (fun t _ => sq_nonneg (x t)) (Finset.mem_univ s))

private theorem claimF_sqrt_inl_le (x : Fin M ⊕ Fin N → ℝ) :
    √(∑ j, x (Sum.inl j) ^ 2) ≤ testNorm x := by
  unfold testNorm
  refine Real.sqrt_le_sqrt ?_
  rw [Fintype.sum_sum_type]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- `|⟨v̄, Π e_p⟩| ≤ max(c⁻¹, K) |v|` when `|m| ≤ K` and `|1 + σᵢ m| ≥ c`. -/
private theorem claimF_pi_bound {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {c K : ℝ}
    (hc : 0 < c) {w : ℂ} (hwK : ‖w‖ ≤ K) (hOne : ∀ i, c ≤ ‖1 + (specOf Sig i : ℂ) * w‖)
    (x : Fin M ⊕ Fin N → ℝ) (p : Fin M ⊕ Fin N) :
    ‖ent (piMat (N := N) Sig w) (vbar Sig x) (eI p)‖ ≤ max c⁻¹ K * testNorm x := by
  rw [claimF_ent_eI_right, Fintype.sum_sum_type]
  rcases p with i | μ
  · simp only [piMat, fromBlocks_apply₁₁, fromBlocks_apply₂₁, Matrix.zero_apply, mul_zero,
      Finset.sum_const_zero, add_zero, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib, norm_neg]
    obtain ⟨U, h₂, h₁, hSd, hσ⟩ := claimF_diag hSig
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
      simp only [claimF_cinv_entry h₂ h₁ hSd hw0, Finset.mul_sum]
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
    rw [claimF_sum_sq_UT h₂, claimF_row_sq h₂, Real.sqrt_one, mul_one] at hcs
    have hc0 : 0 ≤ c⁻¹ := (inv_pos.2 hc).le
    calc _ ≤ ∑ k, c⁻¹ * (|(Uᵀ *ᵥ xM) k| * |U i k|) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => hb k)
      _ ≤ c⁻¹ * √(∑ j, xM j ^ 2) := by
          rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hcs hc0
      _ ≤ max c⁻¹ K * testNorm x :=
          mul_le_mul (le_max_left _ _) (claimF_sqrt_inl_le x) (Real.sqrt_nonneg _)
            (hc0.trans (le_max_left _ _))
  · simp only [piMat, fromBlocks_apply₁₂, fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero,
      Finset.sum_const_zero, zero_add, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
      mul_one, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [vbar, Sum.elim_inr, Function.comp_apply]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul (hwK.trans (le_max_right _ _)) (claimF_abs_le_testNorm x _) (abs_nonneg _)
      ((norm_nonneg w).trans (hwK.trans (le_max_right _ _)))

/-- The setting of §7 gives the density assumptions on the eigenvalues of `Σ` (Lemma 4.10
input). -/
private theorem claimF_density {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) : DensityAssumptions τ N (specOf Sig) :=
  (IsModel.diagModel_specOf (Ω := GaussSpace M N)
    ⟨hset.ratio_ge, hset.ratio_le, (gaussX_isGaussianEnsemble M N).entryAssumption hN,
      hset.sigma⟩).densityAssumptions hset.pos

private theorem claimF_testNorm_eI {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι) :
    testNorm (eI p) = 1 := by
  unfold testNorm
  simp [eI, Pi.single_apply, Finset.sum_ite_eq']

/-- `1 ≤ N η` on `𝐃(τ, N)`. -/
private theorem claimF_one_le_N_im {τ : ℝ} {z : ℂ} (hN : 1 ≤ N) (hτ : 0 < τ)
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
private theorem claimF_Psi_ge {τ : ℝ} {σ : Fin M → ℝ} {z : ℂ} (hN : 1 ≤ N) (hτ : 0 < τ)
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

/-- `Ψ ≤ √K_m + 1` on `𝐃(τ, N)` (Lemma 4.10). -/
private theorem claimF_Psi_le {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) {z : ℂ} (hz : z ∈ S) :
    Psi N (specOf Sig) z ≤ Real.sqrt (mBoundConst τ) + 1 := by
  have hzD := hset.domain.1 hz
  have hNη := claimF_one_le_N_im hN hset.pos hzD
  obtain ⟨-, hm2, hm3⟩ := gen_prop_m_specDomain (claimF_density hset hN) hzD
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
private theorem claimF_Psi_sq_ge {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) {z : ℂ} (hz : z ∈ S) :
    (mBoundConst τ * N)⁻¹ ≤ Psi N (specOf Sig) z ^ 2 := by
  have hzD := hset.domain.1 hz
  obtain ⟨-, -, hm3⟩ := gen_prop_m_specDomain (claimF_density hset hN) hzD
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

/-- `v̄ = e_ν` for `v = e_ν`, `ν ∈ 𝓘_N`. -/
private theorem claimF_vbar_inr (Sig : Matrix (Fin M) (Fin M) ℝ) (ν : Fin N) :
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


/-! ## Continuity in `X` -/

private theorem claimF_continuous_G {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {z : ℂ}
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

private theorem claimF_continuous_ent {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    Continuous fun B : Matrix ι ι ℂ => ent B x y := by
  have : (fun B : Matrix ι ι ℂ => ent B x y) =
      fun B => ∑ s, ∑ t, (x s : ℂ) * B s t * (y t : ℂ) := funext fun B => claimF_ent_eq B x y
  rw [this]
  exact continuous_finsetSum _ fun s _ => continuous_finsetSum _ fun t _ =>
    (continuous_const.mul (continuous_id.matrix_elem s t)).mul continuous_const

private theorem claimF_continuous_resCoeff {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    {z : ℂ} (hz : 0 < z.im) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) (k : ℕ) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => resCoeff Sig A z v i μ k := by
  have hG := claimF_continuous_G (N := N) hSig hz
  unfold resCoeff
  refine continuous_const.mul ((claimF_continuous_ent _ _).comp ?_)
  exact (hG.matrix_mul ((continuous_const.matrix_mul hG).pow k)).sub continuous_const

private theorem claimF_continuous_fCoeff {X : Type*} [TopologicalSpace X] (p n : ℕ)
    {a : X → ℕ → ℂ} (ha : ∀ k, Continuous fun x => a x k) :
    Continuous fun x => fCoeff p (a x) n := by
  unfold fCoeff
  refine continuous_finsetSum _ fun κ _ => continuous_finsetProd _ fun r _ => ?_
  split_ifs
  · exact ha _
  · exact Complex.continuous_conj.comp (ha _)


private theorem claimF_continuous_avgCoeff {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    {z : ℂ} (hz : 0 < z.im) (i : Fin M) (μ : Fin N) (k : ℕ) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => avgCoeff Sig A z i μ k := by
  unfold avgCoeff
  exact continuous_const.mul (continuous_finsetSum _ fun ν _ =>
    claimF_continuous_resCoeff hSig hz (eI (Sum.inr ν)) i μ k)


/-! ## Moments of `1 + ‖X‖_F²` -/

/-- `‖A‖_F² = ∑_{jν} A_{jν}²`. -/
private def claimF_sq (A : Matrix (Fin M) (Fin N) ℝ) : ℝ := ∑ α : Fin M × Fin N, A α.1 α.2 ^ 2

private theorem claimF_sq_nonneg (A : Matrix (Fin M) (Fin N) ℝ) : 0 ≤ claimF_sq A :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The moment constant `2^q (1 + τ^{−q}) (1 + C'_{2q})`. -/
private def claimF_KS (τ : ℝ) (C : ℕ → ℝ) (q : ℕ) : ℝ :=
  2 ^ q * (1 + τ⁻¹ ^ q) * (1 + max (C (2 * q)) 0)

/-- `E (1 + ‖X‖_F²)^q ≤ 2^q (1 + τ^{−q}) (1 + C'_{2q}) N^q` for `M ≤ τ⁻¹ N`, from
(moments of X-1). -/
private theorem claimF_moment {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {τ : ℝ} (hτ : 0 < τ) {C : ℕ → ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ}
    (hX : EntryAssumption C X) (hN : 1 ≤ N) (hM : (M : ℝ) ≤ τ⁻¹ * N) (q : ℕ) :
    Integrable (fun ω => (1 + claimF_sq (X ω)) ^ q) ∧
      ∫ ω, (1 + claimF_sq (X ω)) ^ q ≤ claimF_KS τ C q * (N : ℝ) ^ q := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · refine ⟨by simp, ?_⟩
    simp only [pow_zero, integral_const, probReal_univ, smul_eq_mul, mul_one]
    unfold claimF_KS
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
  set g : Ω → ℝ := fun ω => 2 ^ n * (1 + cd ^ n * ∑ α : Fin M × Fin N,
      (X ω α.1 α.2 ^ 2) ^ (n + 1)) with hg
  have hgi : Integrable g := h1i.const_mul _
  have hle : ∀ ω, (1 + claimF_sq (X ω)) ^ (n + 1) ≤ g ω := by
    intro ω
    have h1 := add_pow_le zero_le_one (claimF_sq_nonneg (X ω)) (n + 1)
    have h2 : claimF_sq (X ω) ^ (n + 1) ≤
        cd ^ n * ∑ α : Fin M × Fin N, (X ω α.1 α.2 ^ 2) ^ (n + 1) :=
      pow_sum_le_card_mul_sum_pow (fun _ _ => sq_nonneg _) n
    calc _ ≤ _ := h1
      _ ≤ g ω := by
          simp only [hg, one_pow, Nat.add_sub_cancel]
          gcongr
  have hmeas : Measurable fun ω => (1 + claimF_sq (X ω)) ^ (n + 1) := by
    unfold claimF_sq
    exact (measurable_const.add (Finset.measurable_sum _ fun α _ =>
      (hX.measurable α.1 α.2).pow_const 2)).pow_const _
  have hWi : Integrable fun ω => (1 + claimF_sq (X ω)) ^ (n + 1) :=
    hgi.mono' hmeas.aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (by have := claimF_sq_nonneg (X ω); positivity)]; exact hle ω)
  refine ⟨hWi, ?_⟩
  have hgval : ∫ ω, g ω = 2 ^ n * (1 + cd ^ n * ∑ α : Fin M × Fin N,
      ∫ ω, (X ω α.1 α.2 ^ 2) ^ (n + 1)) := by
    rw [hg, integral_const_mul, integral_add (integrable_const _) hSi',
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
  have hτn : 0 ≤ τ⁻¹ ^ (n + 1) := by positivity
  calc ∫ ω, (1 + claimF_sq (X ω)) ^ (n + 1) ≤ ∫ ω, g ω := integral_mono hWi hgi hle
    _ ≤ 2 ^ n * (1 + τ⁻¹ ^ (n + 1) * (N : ℝ) ^ (n + 1) * C') := by
        rw [hgval]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have := mul_le_mul_of_nonneg_left hsum (pow_nonneg hcd0 n)
        rw [hM1] at this
        have h5 := mul_le_mul_of_nonneg_right hM2 hC'0
        linarith
    _ ≤ claimF_KS τ C (n + 1) * (N : ℝ) ^ (n + 1) := by
        unfold claimF_KS
        rw [← hC']
        set P := (N : ℝ) ^ (n + 1)
        set T := τ⁻¹ ^ (n + 1)
        have h2n : (0 : ℝ) ≤ 2 ^ n := by positivity
        have hA : 1 + T * P * C' ≤ 2 * ((1 + T) * (1 + C') * P) := by
          nlinarith [mul_nonneg hτn hC'0, mul_nonneg (mul_nonneg hτn hC'0) (sub_nonneg.2 hNn)]
        calc 2 ^ n * (1 + T * P * C') ≤ 2 ^ n * (2 * ((1 + T) * (1 + C') * P)) :=
              mul_le_mul_of_nonneg_left hA h2n
          _ = 2 ^ (n + 1) * (1 + T) * (1 + C') * P := by ring

/-! ## Coefficient bounds -/

/-- `y ≤ s y² + (4s)⁻¹` for `s > 0`. -/
private theorem claimF_amgm {s : ℝ} (hs : 0 < s) (y : ℝ) : y ≤ s * y ^ 2 + (4 * s)⁻¹ := by
  have h : s * y ^ 2 + (4 * s)⁻¹ - y = (2 * s * y - 1) ^ 2 / (4 * s) := by
    field_simp
    ring
  have : 0 ≤ (2 * s * y - 1) ^ 2 / (4 * s) := by positivity
  linarith

/-- `|f_n| ≤ (n + 1)^p y^p` when `|a_k| ≤ y` for all `k ≤ n`. -/
private theorem claimF_fCoeff_le (p : ℕ) {a : ℕ → ℂ} {y : ℝ} (hy : 0 ≤ y) (n : ℕ)
    (ha : ∀ k ≤ n, ‖a k‖ ≤ y) : ‖fCoeff p a n‖ ≤ ((n : ℝ) + 1) ^ p * y ^ p := by
  have hcard : ((Finset.Nat.antidiagonalTuple p n).card : ℝ) ≤ ((n : ℝ) + 1) ^ p := by
    have hsub : Finset.Nat.antidiagonalTuple p n ⊆
        Fintype.piFinset fun _ : Fin p => Finset.range (n + 1) := by
      intro κ hκ
      rw [Finset.Nat.mem_antidiagonalTuple] at hκ
      simp only [Fintype.mem_piFinset, Finset.mem_range]
      intro r
      have := Finset.single_le_sum (fun j _ => Nat.zero_le (κ j)) (Finset.mem_univ r)
      omega
    have := Finset.card_le_card hsub
    simp only [Fintype.card_piFinset, Finset.card_range, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at this
    exact_mod_cast this
  unfold fCoeff
  calc _ ≤ ∑ κ ∈ Finset.Nat.antidiagonalTuple p n, ‖∏ r : Fin p,
        (if (r : ℕ) < p / 2 then a (κ r) else starRingEnd ℂ (a (κ r)))‖ := norm_sum_le _ _
    _ ≤ ∑ _κ ∈ Finset.Nat.antidiagonalTuple p n, y ^ p := by
        refine Finset.sum_le_sum fun κ hκ => ?_
        rw [Finset.Nat.mem_antidiagonalTuple] at hκ
        rw [norm_prod]
        calc _ ≤ ∏ _r : Fin p, y := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun r _ => by
                have hk : κ r ≤ n := by
                  have := Finset.single_le_sum (fun j _ => Nat.zero_le (κ j)) (Finset.mem_univ r)
                  omega
                split_ifs
                · exact ha _ hk
                · rw [Complex.norm_conj]; exact ha _ hk
          _ = y ^ p := by simp
    _ = ((Finset.Nat.antidiagonalTuple p n).card : ℝ) * y ^ p := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (pow_nonneg hy p)

/-- (wt_A_estimate) at a fixed matrix: if `|G_{st} − Π_{st}| ≤ b` and `|G_{st}| ≤ B` for all
`s, t`, then `|a_{k+1}| ≤ 2^{k+4} B^k (b² + B²/N)`. The words at `v = e_ν`, `ν ≠ μ`, have both
endpoint factors off the support of `Π`; the word at `ν = μ` carries the weight `N⁻¹`. -/
private theorem claimF_avgCoeff_event {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (i : Fin M) (μ : Fin N) {b B : ℝ}
    (hB : 0 ≤ B) (hGP : ∀ s t, ‖G Sig A z s t - PiZ N Sig z s t‖ ≤ b)
    (hG : ∀ s t, ‖G Sig A z s t‖ ≤ B) (k : ℕ) :
    ‖avgCoeff Sig A z i μ (k + 1)‖ ≤ 2 ^ (k + 4) * B ^ k * (b ^ 2 + B ^ 2 / N) := by
  have hN : 0 < N := Fin.pos μ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hoff : ∀ s t, PiZ N Sig z s t = 0 → ‖G Sig A z s t‖ ≤ b := fun s t h => by
    simpa [h] using hGP s t
  have hPi1 : ∀ ν : Fin N, PiZ N Sig z (Sum.inr ν) (Sum.inl i) = 0 := fun ν => by
    simp [PiZ, piMat]
  have hPi2 : ∀ ν : Fin N, PiZ N Sig z (Sum.inl i) (Sum.inr ν) = 0 := fun ν => by
    simp [PiZ, piMat]
  have hPi3 : ∀ ν ν' : Fin N, ν ≠ ν' → PiZ N Sig z (Sum.inr ν) (Sum.inr ν') = 0 :=
    fun ν ν' h => by simp [PiZ, piMat, h]
  have hword : ∀ (ν : Fin N) (w : Word (k + 1)),
      ‖wordA Sig A z (eI (Sum.inr ν)) i μ (k + 1) w‖ ≤
        8 * (b ^ 2 + if ν = μ then B ^ 2 else 0) * B ^ k := by
    intro ν w
    refine (wordA_le_R A z _ i μ hB (fun _ _ => hG _ _) k w).trans ?_
    rw [claimF_vbar_inr, ent_eI_eI, ent_eI_eI, ent_eI_eI, ent_eI_eI]
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hB k)
    have hi1 := hoff _ _ (hPi1 ν)
    have hi2 := hoff _ _ (hPi2 ν)
    have hRi0 : 0 ≤ ‖G Sig A z (Sum.inr ν) (Sum.inl i)‖ + ‖G Sig A z (Sum.inl i) (Sum.inr ν)‖ :=
      by positivity
    have hRi := pow_le_pow_left₀ hRi0 (add_le_add hi1 hi2) 2
    by_cases hν : ν = μ
    · subst hν
      simp only [↓reduceIte]
      have hm1 := hG (Sum.inr ν) (Sum.inr ν)
      have hRm0 : 0 ≤ ‖G Sig A z (Sum.inr ν) (Sum.inr ν)‖ + ‖G Sig A z (Sum.inr ν) (Sum.inr ν)‖ :=
        by positivity
      have hRm := pow_le_pow_left₀ hRm0 (add_le_add hm1 hm1) 2
      nlinarith
    · simp only [hν, ↓reduceIte, add_zero]
      have h1 := hoff _ _ (hPi3 ν μ hν)
      have h2 := hoff _ _ (hPi3 μ ν (Ne.symm hν))
      have hRm0 : 0 ≤ ‖G Sig A z (Sum.inr ν) (Sum.inr μ)‖ + ‖G Sig A z (Sum.inr μ) (Sum.inr ν)‖ :=
        by positivity
      have hRm := pow_le_pow_left₀ hRm0 (add_le_add h1 h2) 2
      nlinarith
  have hres : ∀ ν : Fin N, ‖resCoeff Sig A z (eI (Sum.inr ν)) i μ (k + 1)‖ ≤
      2 ^ (k + 1) * (8 * (b ^ 2 + if ν = μ then B ^ 2 else 0) * B ^ k) := by
    intro ν
    rw [resCoeff_eq_sum_wordA hSig A hz, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    calc _ ≤ ∑ w : Word (k + 1), ‖wordA Sig A z (eI (Sum.inr ν)) i μ (k + 1) w‖ := norm_sum_le _ _
      _ ≤ ∑ _w : Word (k + 1), 8 * (b ^ 2 + if ν = μ then B ^ 2 else 0) * B ^ k :=
          Finset.sum_le_sum fun w _ => hword ν w
      _ = _ := by simp
  have hsum : ∑ ν : Fin N, 2 ^ (k + 1) * (8 * (b ^ 2 + if ν = μ then B ^ 2 else 0) * B ^ k) =
      2 ^ (k + 4) * B ^ k * ((N : ℝ) * b ^ 2 + B ^ 2) := by
    have e1 : ∀ ν : Fin N, (2 : ℝ) ^ (k + 1) * (8 * (b ^ 2 + if ν = μ then B ^ 2 else 0) * B ^ k) =
        (2 ^ (k + 4) * B ^ k) * (b ^ 2 + if ν = μ then B ^ 2 else 0) := fun ν => by ring
    simp_rw [e1]
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
    simp
  unfold avgCoeff
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (N : ℝ)⁻¹ * ‖∑ ν : Fin N, resCoeff Sig A z (eI (Sum.inr ν)) i μ (k + 1)‖
      ≤ (N : ℝ)⁻¹ * (2 ^ (k + 4) * B ^ k * ((N : ℝ) * b ^ 2 + B ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hNr.le)
        rw [← hsum]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun ν _ => hres ν)
    _ = 2 ^ (k + 4) * B ^ k * (b ^ 2 + B ^ 2 / N) := by
        field_simp

/-- (A_rough) for the coefficients of `m_N − m`: `|a_k| ≤ (2 K (1 + ‖AᵀA‖)/η)^{k+1}`. -/
private theorem claimF_avgCoeff_rough {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) {z : ℂ} (hz : z ∈ S) (A : Matrix (Fin M) (Fin N) ℝ)
    (i : Fin M) (μ : Fin N) (k : ℕ) :
    ‖avgCoeff Sig A z i μ k‖ ≤ (2 * (roughConst τ c * (1 + ‖Aᵀ * A‖) / z.im)) ^ (k + 1) := by
  have hN : 0 < N := Fin.pos μ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hSig := hset.sigma.posDef
  have hη : 0 < z.im := (hset.domain.1 hz).1
  have hτ := hset.pos
  have hCm := mBoundConst_pos hτ
  set Q := roughConst τ c * (1 + ‖Aᵀ * A‖) / z.im with hQ
  have hQ0 : 0 ≤ Q := by
    have : 0 ≤ roughConst τ c := by unfold roughConst; positivity
    have := norm_nonneg (Aᵀ * A)
    rw [hQ]; positivity
  have hres : ∀ ν : Fin N, ‖resCoeff Sig A z (eI (Sum.inr ν)) i μ k‖ ≤ (2 * Q) ^ (k + 1) := by
    intro ν
    rw [resCoeff_eq_sum_wordA hSig A hη, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    calc _ ≤ ∑ w : Word k, ‖wordA Sig A z (eI (Sum.inr ν)) i μ k w‖ := norm_sum_le _ _
      _ ≤ ∑ _w : Word k, Q ^ (k + 1) := Finset.sum_le_sum fun w _ =>
          norm_wordA_rough hset hz A _ (claimF_testNorm_eI _) i μ k w
      _ = 2 ^ k * Q ^ (k + 1) := by simp
      _ ≤ 2 ^ (k + 1) * Q ^ (k + 1) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
      _ = (2 * Q) ^ (k + 1) := (mul_pow _ _ _).symm
  unfold avgCoeff
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (N : ℝ)⁻¹ * ‖∑ ν : Fin N, resCoeff Sig A z (eI (Sum.inr ν)) i μ k‖
      ≤ (N : ℝ)⁻¹ * ((N : ℝ) * (2 * Q) ^ (k + 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hNr.le)
        refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun ν _ => hres ν).trans (le_of_eq ?_))
        simp
    _ = (2 * Q) ^ (k + 1) := by field_simp

/-- Splitting `E|f|` along an event `Ξ`: if `|f| ≤ g` on `Ξ`, then
`|E f| ≤ E g + s E|f|² + P(Ξᶜ)/(4s)` for every `s > 0`. -/
private theorem claimF_split {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {f : Ω → ℂ} {g : Ω → ℝ} {Ξ : Set Ω} {s : ℝ} (hs : 0 < s)
    (hfi : Integrable fun ω => ‖f ω‖) (hf2i : Integrable fun ω => ‖f ω‖ ^ 2) (hgi : Integrable g)
    (hg0 : ∀ ω, 0 ≤ g ω) (hon : ∀ ω ∈ Ξ, ‖f ω‖ ≤ g ω) :
    ‖∫ ω, f ω‖ ≤ (∫ ω, g ω) + s * (∫ ω, ‖f ω‖ ^ 2) + (ℙ Ξᶜ).toReal * (4 * s)⁻¹ := by
  set Bs : Set Ω := toMeasurable ℙ Ξᶜ with hBs
  have hpt : ∀ ω, ‖f ω‖ ≤ g ω + s * ‖f ω‖ ^ 2 + Bs.indicator (fun _ => (4 * s)⁻¹) ω := by
    intro ω
    have hind : 0 ≤ Bs.indicator (fun _ => (4 * s)⁻¹) ω :=
      Set.indicator_nonneg (fun _ _ => by positivity) _
    by_cases hω : ω ∈ Ξ
    · have := hon ω hω
      have : 0 ≤ s * ‖f ω‖ ^ 2 := by positivity
      linarith
    · have hmem : ω ∈ Bs := subset_toMeasurable _ _ hω
      rw [Set.indicator_of_mem hmem]
      have := claimF_amgm hs ‖f ω‖
      linarith [hg0 ω]
  have hI : Integrable fun ω => Bs.indicator (fun _ => (4 * s)⁻¹) ω :=
    (integrable_const _).indicator (measurableSet_toMeasurable _ _)
  have h1 : Integrable fun ω => g ω + s * ‖f ω‖ ^ 2 := hgi.add (hf2i.const_mul s)
  have h2 : Integrable fun ω => g ω + s * ‖f ω‖ ^ 2 + Bs.indicator (fun _ => (4 * s)⁻¹) ω :=
    h1.add hI
  have e1 : ∫ ω, (g ω + s * ‖f ω‖ ^ 2 + Bs.indicator (fun _ => (4 * s)⁻¹) ω) =
      (∫ ω, (g ω + s * ‖f ω‖ ^ 2)) + ∫ ω, Bs.indicator (fun _ => (4 * s)⁻¹) ω :=
    integral_add h1 hI
  have e2 : ∫ ω, (g ω + s * ‖f ω‖ ^ 2) = (∫ ω, g ω) + ∫ ω, s * ‖f ω‖ ^ 2 :=
    integral_add hgi (hf2i.const_mul s)
  have e3 : ∫ ω, Bs.indicator (fun _ => (4 * s)⁻¹) ω = (ℙ Ξᶜ).toReal * (4 * s)⁻¹ := by
    rw [integral_indicator_const _ (measurableSet_toMeasurable _ _), measureReal_def,
      measure_toMeasurable, smul_eq_mul]
  have hint : ∫ ω, ‖f ω‖ ≤ (∫ ω, g ω) + s * (∫ ω, ‖f ω‖ ^ 2) + (ℙ Ξᶜ).toReal * (4 * s)⁻¹ := by
    refine (integral_mono hfi h2 hpt).trans (le_of_eq ?_)
    rw [e1, e2, e3, integral_const_mul]
  exact (norm_integral_le_integral_norm _).trans hint

/-- Rough bounds for `f_n` and `F̃^p` (from (A_rough) and the moments of `X`): integrability of
`|f_n|`, `|f_n|²`, `F̃^p`, and `E|f_n|² ≤ (4p+1)^{2p} (2K)^{10p} K_S N^{20p}` for `n ≤ 4p`. -/
private theorem claimF_rough {τ c : ℝ} {C : ℕ → ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN1 : 1 ≤ N) {z : ℂ} (hz : z ∈ S)
    {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) (i : Fin M) (μ : Fin N)
    {p n : ℕ} (hn : n ≤ 4 * p) :
    Integrable (fun ω => ‖fCoeff p (avgCoeff Sig (X ω) z i μ) n‖) ∧
    Integrable (fun ω => ‖fCoeff p (avgCoeff Sig (X ω) z i μ) n‖ ^ 2) ∧
    Integrable (fun ω => Ft Sig (X ω) z ^ p) ∧
    ∫ ω, ‖fCoeff p (avgCoeff Sig (X ω) z i μ) n‖ ^ 2 ≤
      (4 * (p : ℝ) + 1) ^ (2 * p) * (2 * roughConst τ c) ^ (10 * p) * claimF_KS τ C (10 * p) *
        (N : ℝ) ^ (20 * p) := by
  have hτ := hset.pos
  have hT1 : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hset.le_one
  have hCm0 := mBoundConst_pos hτ
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : (0 : ℝ) < N := by linarith
  have hSig := hset.sigma.posDef
  have hzD := hset.domain.1 hz
  have hη : 0 < z.im := hzD.1
  have hηN : 1 ≤ (N : ℝ) * z.im := claimF_one_le_N_im hN1 hτ hzD
  have hM : (M : ℝ) ≤ τ⁻¹ * N := (div_le_iff₀ hNp).1 hset.ratio_le
  have hXm : Measurable X :=
    measurable_pi_iff.2 fun j => measurable_pi_iff.2 fun ν => hX.measurable j ν
  have hR1 : 1 ≤ roughConst τ c := by
    have h3 : 1 ≤ τ⁻¹ ^ 3 := one_le_pow₀ hT1
    have h4 : 0 ≤ mBoundConst τ * max c⁻¹ 1 :=
      mul_nonneg hCm0.le ((zero_le_one).trans (le_max_right _ _))
    unfold roughConst
    nlinarith
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = roughConst τ c := ⟨_, rfl⟩
  rw [← hR] at hR1 ⊢
  obtain ⟨W, hW⟩ : ∃ W : Ω → ℝ, W = fun ω => (2 * R * N) * (1 + claimF_sq (X ω)) := ⟨_, rfl⟩
  have hWω : ∀ ω, W ω = (2 * R * N) * (1 + claimF_sq (X ω)) := fun ω => by rw [hW]
  obtain ⟨f, hf⟩ : ∃ f : Ω → ℂ, f = fun ω => fCoeff p (avgCoeff Sig (X ω) z i μ) n := ⟨_, rfl⟩
  have hfω : ∀ ω, f ω = fCoeff p (avgCoeff Sig (X ω) z i μ) n := fun ω => by rw [hf]
  have hW1 : ∀ ω, 1 ≤ W ω := fun ω => by
    have := claimF_sq_nonneg (X ω)
    have h2 : 1 ≤ 2 * R * N := by nlinarith
    rw [hWω]; nlinarith
  have hra : ∀ ω k, ‖avgCoeff Sig (X ω) z i μ k‖ ≤ W ω ^ (k + 1) := by
    intro ω k
    have h0 : 0 ≤ 2 * (R * (1 + ‖(X ω)ᵀ * X ω‖) / z.im) := by
      have := norm_nonneg ((X ω)ᵀ * X ω)
      have : 0 ≤ R := by linarith
      positivity
    have h1 : ‖(X ω)ᵀ * X ω‖ ≤ claimF_sq (X ω) := claimF_XtX_le _
    have h2 : (1 + ‖(X ω)ᵀ * X ω‖) / z.im ≤ N * (1 + claimF_sq (X ω)) := by
      rw [div_le_iff₀ hη]
      have h3 : 0 ≤ 1 + ‖(X ω)ᵀ * X ω‖ := by positivity
      nlinarith
    have h4 : 2 * (R * (1 + ‖(X ω)ᵀ * X ω‖) / z.im) ≤ W ω := by
      rw [hWω, mul_div_assoc]
      have := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ R)
      nlinarith
    have h5 := claimF_avgCoeff_rough hset hz (X ω) i μ k
    rw [← hR] at h5
    exact h5.trans (pow_le_pow_left₀ h0 h4 _)
  have hrf : ∀ ω, ‖f ω‖ ≤ (4 * (p : ℝ) + 1) ^ p * W ω ^ (5 * p) := by
    intro ω
    rw [hfω]
    refine (norm_fCoeff_le p (hW1 ω) n fun k _ => hra ω k).trans ?_
    have hn1 : (n : ℝ) + 1 ≤ 4 * p + 1 := by
      have : (n : ℝ) ≤ 4 * p := by exact_mod_cast hn
      linarith
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) hn1 p)
      (pow_le_pow_right₀ (hW1 ω) (by omega)) (pow_nonneg (by linarith [hW1 ω]) _) (by positivity)
  have hF0 : ∀ ω, 0 ≤ Ft Sig (X ω) z := fun ω => norm_nonneg _
  have hrF : ∀ ω, Ft Sig (X ω) z ≤ W ω := by
    intro ω
    have := hra ω 0
    rwa [avgCoeff_zero _ _ _ _ _ hN1, zero_add, pow_one] at this
  have hmom := claimF_moment hτ hX hN1 hM
  have hfm : Measurable f := by
    rw [hf]
    exact (claimF_continuous_fCoeff p n fun k =>
      claimF_continuous_avgCoeff hSig hη i μ k).measurable.comp hXm
  have hFm : Measurable fun ω => Ft Sig (X ω) z :=
    (((measurable_mN Sig z).comp hXm).sub_const _).norm
  have hWpow : ∀ q ω, W ω ^ q = (2 * R * N) ^ q * (1 + claimF_sq (X ω)) ^ q := fun q ω => by
    rw [hWω, mul_pow]
  have hWq : ∀ q, Integrable fun ω => W ω ^ q := fun q => by
    simp_rw [hWpow]
    exact (hmom q).1.const_mul _
  have hfi : Integrable fun ω => ‖f ω‖ :=
    ((hWq (5 * p)).const_mul ((4 * (p : ℝ) + 1) ^ p)).mono' hfm.norm.aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hrf ω)
  have hf2b : ∀ ω, ‖f ω‖ ^ 2 ≤ (4 * (p : ℝ) + 1) ^ (2 * p) * W ω ^ (10 * p) := fun ω => by
    have := pow_le_pow_left₀ (norm_nonneg _) (hrf ω) 2
    refine this.trans (le_of_eq ?_)
    rw [mul_pow, ← pow_mul, ← pow_mul]; ring_nf
  have hf2i : Integrable fun ω => ‖f ω‖ ^ 2 :=
    ((hWq (10 * p)).const_mul ((4 * (p : ℝ) + 1) ^ (2 * p))).mono'
      (hfm.norm.pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_of_nonneg (by positivity)]; exact hf2b ω)
  have hFpi : Integrable fun ω => Ft Sig (X ω) z ^ p :=
    (hWq p).mono' (hFm.pow_const p).aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (pow_nonneg (hF0 ω) p)]
      exact pow_le_pow_left₀ (hF0 ω) (hrF ω) p)
  have hf2 : ∫ ω, ‖f ω‖ ^ 2 ≤ (4 * (p : ℝ) + 1) ^ (2 * p) * (2 * R) ^ (10 * p) *
      claimF_KS τ C (10 * p) * (N : ℝ) ^ (20 * p) := by
    calc ∫ ω, ‖f ω‖ ^ 2 ≤ ∫ ω, (4 * (p : ℝ) + 1) ^ (2 * p) * W ω ^ (10 * p) :=
          integral_mono hf2i ((hWq _).const_mul _) hf2b
      _ = (4 * (p : ℝ) + 1) ^ (2 * p) * (2 * R * N) ^ (10 * p) *
            ∫ ω, (1 + claimF_sq (X ω)) ^ (10 * p) := by
          simp_rw [hWpow]
          rw [integral_const_mul, integral_const_mul]; ring
      _ ≤ (4 * (p : ℝ) + 1) ^ (2 * p) * (2 * R * N) ^ (10 * p) *
            (claimF_KS τ C (10 * p) * (N : ℝ) ^ (10 * p)) :=
          mul_le_mul_of_nonneg_left (hmom _).2 (by positivity)
      _ = _ := by
          rw [mul_pow, show 20 * p = 10 * p + 10 * p by ring, pow_add]; ring
  subst hf
  exact ⟨hfi, hf2i, hFpi, hf2⟩

/-- `dPrevTwo τ p ≤ D_a` gives `24p + 1 ≤ D_a − 3`. -/
private theorem claimF_D_ge {τ : ℝ} {p : ℕ} {Da : ℝ} (hDa : dPrevTwo τ p ≤ Da) :
    (24 * p + 1 : ℝ) ≤ Da - 3 := by
  have hP : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hk : (1 : ℝ) ≤ (kTau τ : ℝ) + 1 := by
    have := (Nat.cast_nonneg (kTau τ) : (0 : ℝ) ≤ _); linarith
  have h0 : 0 ≤ dPrev p := by unfold dPrev; positivity
  have h1 : dPrev p ≤ dPrevTwo τ p := by
    unfold dPrevTwo; exact le_mul_of_one_le_right h0 hk
  unfold dPrev at h1
  nlinarith

/-- On the a priori event `|G_{st} − Π_{st}| ≤ b` (all `s, t`), with `|Π_{st}| ≤ K_Π`,
`K_Π + b ≤ B`, and `2^{k+4} B^k (b² + B²/N) ≤ x` for `k + 1 ≤ n`:
`|f_n| ≤ (n + 1)^p (F̃^p + x^p)`. -/
private theorem claimF_on_event {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (i : Fin M) (μ : Fin N) {p n : ℕ}
    (hN1 : 1 ≤ N) {b B KP x : ℝ} (hB0 : 0 ≤ B) (hx0 : 0 ≤ x)
    (hGP : ∀ s t, ‖G Sig A z s t - PiZ N Sig z s t‖ ≤ b)
    (hPi : ∀ s t, ‖PiZ N Sig z s t‖ ≤ KP) (hKb : KP + b ≤ B)
    (hcoef : ∀ k, k + 1 ≤ n → 2 ^ (k + 4) * B ^ k * (b ^ 2 + B ^ 2 / N) ≤ x) :
    ‖fCoeff p (avgCoeff Sig A z i μ) n‖ ≤ ((n : ℝ) + 1) ^ p * (Ft Sig A z ^ p + x ^ p) := by
  have hF0 : 0 ≤ Ft Sig A z := norm_nonneg _
  have hG : ∀ s t, ‖G Sig A z s t‖ ≤ B := by
    intro s t
    have h1 : ‖G Sig A z s t‖ ≤ ‖G Sig A z s t - PiZ N Sig z s t‖ + ‖PiZ N Sig z s t‖ := by
      have := norm_add_le (G Sig A z s t - PiZ N Sig z s t) (PiZ N Sig z s t)
      rwa [sub_add_cancel] at this
    linarith [hGP s t, hPi s t]
  have hak : ∀ k ≤ n, ‖avgCoeff Sig A z i μ k‖ ≤ max (Ft Sig A z) x := by
    intro k hk
    rcases k with _ | k
    · rw [avgCoeff_zero _ _ _ _ _ hN1]; exact le_max_left _ _
    · exact ((claimF_avgCoeff_event hSig A hz i μ hB0 hGP hG k).trans
        (hcoef k hk)).trans (le_max_right _ _)
  have h := claimF_fCoeff_le p (hF0.trans (le_max_left _ _)) n hak
  have hmx : max (Ft Sig A z) x ^ p ≤ Ft Sig A z ^ p + x ^ p := by
    rcases le_total (Ft Sig A z) x with h' | h'
    · rw [max_eq_right h']; have := pow_nonneg hF0 p; linarith
    · rw [max_eq_left h']; have := pow_nonneg hx0 p; linarith
  exact h.trans (mul_le_mul_of_nonneg_left hmx (by positivity))

/-! ## The claim -/

/-- (avg_pf_claim) for `n ∈ [4, 4p]`: (wt_A_estimate) on the factors with `n(w_r) ≥ 1`, Hölder
and Young on the factors with `n(w_r) = 0`. -/
theorem avg_claim_ge4 (τ c : ℝ) (C : ℕ → ℝ) (p : ℕ) (δ εa Da : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hc : 0 < c) (hp : Even p) (hp2 : 2 ≤ p) (hδ : 0 < δ) (hεa : 0 < εa) (hεaτ : 16 * εa ≤ τ)
    (hεaδ : 20 * p * εa ≤ δ) (hDa : dPrevTwo τ p ≤ Da) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (S : Set ℂ), CompSetting τ c M N Sig S → AnisoAllAt N C Sig S εa Da →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption C X →
        ∀ z ∈ S, ∀ n ∈ Finset.Icc 4 (4 * p),
          (N : ℝ) ^ (-(n : ℝ) / 2) * ∑ i, ∑ μ, ‖∫ ω, fCoeff p (avgCoeff Sig (X ω) z i μ) n‖ ≤
            K * (((N : ℝ) ^ δ * Psi N (specOf Sig) z ^ 2) ^ p + ∫ ω, Ft Sig (X ω) z ^ p) := by
  have _hp := hp
  have _hεaτ := hεaτ
  set Cm := mBoundConst τ with hCm
  have hCm0 : 0 < Cm := mBoundConst_pos hτ
  have hT0 : 0 < τ⁻¹ := inv_pos.2 hτ
  have hT1 : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  set κ := max c⁻¹ Cm with hκ
  have hκ0 : 0 ≤ κ := (inv_pos.2 hc).le.trans (le_max_left _ _)
  set K₁ : ℝ := κ * τ⁻¹ + τ⁻¹ ^ 2 * (Real.sqrt Cm + 1) with hK₁
  have hK₁1 : 1 ≤ K₁ := by
    have : 0 ≤ κ * τ⁻¹ := mul_nonneg hκ0 hT0.le
    have : 1 ≤ τ⁻¹ ^ 2 := one_le_pow₀ hT1
    have : 0 ≤ Real.sqrt Cm := Real.sqrt_nonneg _
    nlinarith
  set L : ℝ := 2 ^ (4 * p + 4) * K₁ ^ (4 * p) * (τ⁻¹ ^ 4 + K₁ ^ 2 * Cm) with hL
  have hL0 : 0 ≤ L := by positivity
  set R := roughConst τ c with hR
  set Kr : ℝ := (4 * (p : ℝ) + 1) ^ (2 * p) * (2 * R) ^ (10 * p) * claimF_KS τ C (10 * p)
    with hKr
  refine ⟨τ⁻¹ * ((4 * (p : ℝ) + 1) ^ p * (L ^ p + 1) + 2 * τ⁻¹ ^ (2 * p)), by positivity, ?_⟩
  obtain ⟨N₁, h₁⟩ := avg_entry_highProb τ c εa Da hτ hτ1 hc
  refine ⟨max (max N₁ 1) ⌈Kr⌉₊, ?_⟩
  intro N hN M Sig S hset hA Ω _ _ X hX z hz n hn
  obtain ⟨hn4, hn4p⟩ := Finset.mem_Icc.1 hn
  have hNN₁ : N₁ ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hNK : ⌈Kr⌉₊ ≤ N := by omega
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : (0 : ℝ) < N := by linarith
  have hKrN : Kr ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hNK)
  have hSig := hset.sigma.posDef
  have hzD := hset.domain.1 hz
  have hη : 0 < z.im := hzD.1
  have hm := (gen_prop_m_specDomain (claimF_density hset hN1) hzD).2.1
  have hOne := hset.oneXm z hz
  have hM : (M : ℝ) ≤ τ⁻¹ * N := (div_le_iff₀ hNp).1 hset.ratio_le
  have hev := h₁ N hNN₁ M Sig S hset Ω X (hA Ω X hX) z hz
  have hΨle := claimF_Psi_le hset hN1 hz
  have hΨge : τ / N ≤ Psi N (specOf Sig) z := claimF_Psi_ge hN1 hτ hzD
  have hΨsq := claimF_Psi_sq_ge hset hN1 hz
  set Ψ := Psi N (specOf Sig) z with hΨdef
  have hΨ0 : 0 ≤ Ψ := le_trans (by positivity) hΨge
  have he1 : 1 ≤ (N : ℝ) ^ εa := Real.one_le_rpow hN1r hεa.le
  set e := (N : ℝ) ^ εa with he
  set b₀ := τ⁻¹ ^ 2 * e * Ψ with hb₀
  set B := K₁ * e with hB
  have hB0 : 0 ≤ B := by positivity
  set x := L * e ^ (4 * p + 1) * Ψ ^ 2 with hx
  have hx0 : 0 ≤ x := by positivity
  -- `|Π_{ab}| ≤ max(c⁻¹, C_m) τ⁻¹`
  have hun : ∀ a, testNorm (SigU (n := Fin N) Sig *ᵥ eI a) ≤ τ⁻¹ := fun a => by
    have := claimF_testNorm_SigU (N := N) hset.sigma hτ hset.le_one (eI a)
    rwa [claimF_testNorm_eI, mul_one] at this
  have hPi : ∀ a b, ‖PiZ N Sig z a b‖ ≤ κ * τ⁻¹ := by
    intro a b
    have h := claimF_pi_bound hSig hc hm hOne (SigU (n := Fin N) Sig *ᵥ eI a) b
    rw [claimF_vbar_SigU hSig, ent_eI_eI] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hun a) hκ0)
  -- the coefficient bound on the a priori event
  have hNinv : 1 / (N : ℝ) ≤ Cm * Ψ ^ 2 := by
    have : (1 : ℝ) / N = Cm * (Cm * N)⁻¹ := by field_simp
    rw [this]; exact mul_le_mul_of_nonneg_left hΨsq hCm0.le
  have hbB : b₀ ^ 2 + B ^ 2 / N ≤ (τ⁻¹ ^ 4 + K₁ ^ 2 * Cm) * e ^ 2 * Ψ ^ 2 := by
    have e1 : b₀ ^ 2 = τ⁻¹ ^ 4 * e ^ 2 * Ψ ^ 2 := by rw [hb₀]; ring
    have e2 : B ^ 2 / N = K₁ ^ 2 * e ^ 2 * (1 / N) := by rw [hB]; ring
    rw [e1, e2]
    have := mul_le_mul_of_nonneg_left hNinv (by positivity : (0 : ℝ) ≤ K₁ ^ 2 * e ^ 2)
    calc τ⁻¹ ^ 4 * e ^ 2 * Ψ ^ 2 + K₁ ^ 2 * e ^ 2 * (1 / N)
        ≤ τ⁻¹ ^ 4 * e ^ 2 * Ψ ^ 2 + K₁ ^ 2 * e ^ 2 * (Cm * Ψ ^ 2) := by linarith
      _ = (τ⁻¹ ^ 4 + K₁ ^ 2 * Cm) * e ^ 2 * Ψ ^ 2 := by ring
  have hcoef : ∀ k, k + 1 ≤ 4 * p → 2 ^ (k + 4) * B ^ k * (b₀ ^ 2 + B ^ 2 / N) ≤ x := by
    intro k hk
    have h2 : (2 : ℝ) ^ (k + 4) ≤ 2 ^ (4 * p + 4) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hK : K₁ ^ k ≤ K₁ ^ (4 * p) := pow_le_pow_right₀ hK₁1 (by omega)
    have hE : e ^ (k + 2) ≤ e ^ (4 * p + 1) := pow_le_pow_right₀ he1 (by omega)
    have hBk : B ^ k = K₁ ^ k * e ^ k := by rw [hB, mul_pow]
    have hc0 : 0 ≤ τ⁻¹ ^ 4 + K₁ ^ 2 * Cm := by positivity
    calc 2 ^ (k + 4) * B ^ k * (b₀ ^ 2 + B ^ 2 / N)
        ≤ 2 ^ (k + 4) * B ^ k * ((τ⁻¹ ^ 4 + K₁ ^ 2 * Cm) * e ^ 2 * Ψ ^ 2) :=
          mul_le_mul_of_nonneg_left hbB (by positivity)
      _ = 2 ^ (k + 4) * K₁ ^ k * (τ⁻¹ ^ 4 + K₁ ^ 2 * Cm) * e ^ (k + 2) * Ψ ^ 2 := by
          rw [hBk]; ring
      _ ≤ 2 ^ (4 * p + 4) * K₁ ^ (4 * p) * (τ⁻¹ ^ 4 + K₁ ^ 2 * Cm) * e ^ (4 * p + 1) * Ψ ^ 2 := by
          gcongr
      _ = x := by rw [hx, hL]
  have hKb : κ * τ⁻¹ + τ⁻¹ ^ 2 * e * Ψ ≤ B := by
    have h2 : τ⁻¹ ^ 2 * e * Ψ ≤ τ⁻¹ ^ 2 * (Real.sqrt Cm + 1) * e := by
      have := mul_le_mul_of_nonneg_left hΨle (by positivity : (0 : ℝ) ≤ τ⁻¹ ^ 2 * e)
      calc τ⁻¹ ^ 2 * e * Ψ ≤ τ⁻¹ ^ 2 * e * (Real.sqrt Cm + 1) := this
        _ = τ⁻¹ ^ 2 * (Real.sqrt Cm + 1) * e := by ring
    have h3 : κ * τ⁻¹ ≤ κ * τ⁻¹ * e := le_mul_of_one_le_right (by positivity) he1
    have e4 : B = κ * τ⁻¹ * e + τ⁻¹ ^ 2 * (Real.sqrt Cm + 1) * e := by rw [hB, hK₁]; ring
    linarith only [h2, h3, e4]
  -- the scale `s` of the off-event part
  set s : ℝ := ((N : ℝ) ^ (22 * p + 1))⁻¹ with hs
  have hs0 : 0 < s := by positivity
  set EF := ∫ ω, Ft Sig (X ω) z ^ p with hEF
  set Ξ : Set Ω := {ω | ∀ s t, ‖G Sig (X ω) z s t - PiZ N Sig z s t‖ ≤ τ⁻¹ ^ 2 * e * Ψ}
    with hΞ
  have hev' : ℙ Ξᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(Da - 3))) := hev
  have hPΞ : (ℙ Ξᶜ).toReal ≤ ((N : ℝ) ^ (24 * p + 1))⁻¹ := by
    refine (ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg hNp.le _) hev').trans ?_
    have hD := claimF_D_ge (τ := τ) hDa
    calc (N : ℝ) ^ (-(Da - 3)) ≤ (N : ℝ) ^ (-((24 * p + 1 : ℕ) : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hN1r (by push_cast; linarith only [hD])
      _ = ((N : ℝ) ^ (24 * p + 1))⁻¹ := by rw [Real.rpow_neg hNp.le, Real.rpow_natCast]
  have hper : ∀ (i : Fin M) (μ : Fin N), ‖∫ ω, fCoeff p (avgCoeff Sig (X ω) z i μ) n‖ ≤
      (4 * (p : ℝ) + 1) ^ p * (EF + x ^ p) + 2 * ((N : ℝ) ^ (2 * p))⁻¹ := by
    intro i μ
    obtain ⟨hfi, hf2i, hFpi, hf2⟩ := claimF_rough hset hN1 hz hX i μ hn4p
    have hF0 : ∀ ω, 0 ≤ Ft Sig (X ω) z := fun ω => norm_nonneg _
    have hon : ∀ ω ∈ Ξ, ‖fCoeff p (avgCoeff Sig (X ω) z i μ) n‖ ≤
        (4 * (p : ℝ) + 1) ^ p * (Ft Sig (X ω) z ^ p + x ^ p) := by
      intro ω hω
      have h := claimF_on_event hSig (X ω) hη i μ (p := p) (n := n) hN1 hB0 hx0 hω hPi hKb
        fun k hk => hcoef k (by omega)
      have hn1 : (n : ℝ) + 1 ≤ 4 * p + 1 := by
        have : (n : ℝ) ≤ 4 * p := by exact_mod_cast hn4p
        linarith only [this]
      have := pow_nonneg (hF0 ω) p
      exact h.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hn1 p)
        (by positivity))
    have hgi : Integrable fun ω => (4 * (p : ℝ) + 1) ^ p * (Ft Sig (X ω) z ^ p + x ^ p) :=
      (hFpi.add (integrable_const _)).const_mul _
    have hg0 : ∀ ω, 0 ≤ (4 * (p : ℝ) + 1) ^ p * (Ft Sig (X ω) z ^ p + x ^ p) := fun ω => by
      have := pow_nonneg (hF0 ω) p
      positivity
    have h := claimF_split hs0 hfi hf2i hgi hg0 hon
    have hEg : ∫ ω, (4 * (p : ℝ) + 1) ^ p * (Ft Sig (X ω) z ^ p + x ^ p) =
        (4 * (p : ℝ) + 1) ^ p * (EF + x ^ p) := by
      rw [integral_const_mul, integral_add hFpi (integrable_const _)]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, hEF]
    have hoff1 : s * ∫ ω, ‖fCoeff p (avgCoeff Sig (X ω) z i μ) n‖ ^ 2 ≤
        ((N : ℝ) ^ (2 * p))⁻¹ := by
      calc s * ∫ ω, ‖fCoeff p (avgCoeff Sig (X ω) z i μ) n‖ ^ 2 ≤ s * (Kr * (N : ℝ) ^ (20 * p)) :=
            mul_le_mul_of_nonneg_left hf2 hs0.le
        _ ≤ s * ((N : ℝ) * (N : ℝ) ^ (20 * p)) := by gcongr
        _ = ((N : ℝ) ^ (2 * p))⁻¹ := by
            rw [hs, show 22 * p + 1 = 2 * p + (20 * p + 1) by ring, pow_add, pow_succ]
            field_simp
    have hoff2 : (ℙ Ξᶜ).toReal * (4 * s)⁻¹ ≤ ((N : ℝ) ^ (2 * p))⁻¹ := by
      calc (ℙ Ξᶜ).toReal * (4 * s)⁻¹ ≤ ((N : ℝ) ^ (24 * p + 1))⁻¹ * (4 * s)⁻¹ :=
            mul_le_mul_of_nonneg_right hPΞ (by positivity)
        _ = ((N : ℝ) ^ (2 * p))⁻¹ / 4 := by
            rw [hs, show 24 * p + 1 = 2 * p + (22 * p + 1) by ring, pow_add]
            field_simp
        _ ≤ ((N : ℝ) ^ (2 * p))⁻¹ := by
            have : 0 ≤ ((N : ℝ) ^ (2 * p))⁻¹ := by positivity
            linarith
    rw [hEg] at h
    linarith
  -- summation over `(i, μ)`
  set T := (4 * (p : ℝ) + 1) ^ p * (EF + x ^ p) + 2 * ((N : ℝ) ^ (2 * p))⁻¹ with hT
  have hEF0 : 0 ≤ EF := integral_nonneg fun ω => pow_nonneg (norm_nonneg _) p
  have hT0' : 0 ≤ T := by positivity
  have hsum : ∑ i : Fin M, ∑ μ : Fin N, ‖∫ ω, fCoeff p (avgCoeff Sig (X ω) z i μ) n‖ ≤
      (M : ℝ) * N * T := by
    calc _ ≤ ∑ _i : Fin M, ∑ _μ : Fin N, T :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun μ _ => hper i μ
      _ = (M : ℝ) * N * T := by simp; ring
  have hpre : (N : ℝ) ^ (-(n : ℝ) / 2) * ((M : ℝ) * N) ≤ τ⁻¹ := by
    have h1 : (M : ℝ) * N ≤ τ⁻¹ * ((N : ℝ) * N) := by
      have := mul_le_mul_of_nonneg_right hM hNp.le
      calc (M : ℝ) * N ≤ τ⁻¹ * N * N := this
        _ = τ⁻¹ * ((N : ℝ) * N) := by ring
    have h2 : (N : ℝ) ^ (-(n : ℝ) / 2) * ((N : ℝ) * N) ≤ 1 := by
      have e1 : (N : ℝ) * N = (N : ℝ) ^ (2 : ℝ) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
      rw [e1, ← Real.rpow_add hNp]
      refine Real.rpow_le_one_of_one_le_of_nonpos hN1r ?_
      have : (4 : ℝ) ≤ n := by exact_mod_cast hn4
      linarith
    have h0 : 0 ≤ (N : ℝ) ^ (-(n : ℝ) / 2) := Real.rpow_nonneg hNp.le _
    calc (N : ℝ) ^ (-(n : ℝ) / 2) * ((M : ℝ) * N)
        ≤ (N : ℝ) ^ (-(n : ℝ) / 2) * (τ⁻¹ * ((N : ℝ) * N)) := mul_le_mul_of_nonneg_left h1 h0
      _ = τ⁻¹ * ((N : ℝ) ^ (-(n : ℝ) / 2) * ((N : ℝ) * N)) := by ring
      _ ≤ τ⁻¹ * 1 := mul_le_mul_of_nonneg_left h2 hT0.le
      _ = τ⁻¹ := mul_one _
  -- the right side
  set Y := ((N : ℝ) ^ δ * Ψ ^ 2) ^ p with hY
  have hNδ : 1 ≤ (N : ℝ) ^ δ := Real.one_le_rpow hN1r hδ.le
  have hY0 : 0 ≤ Y := by positivity
  have hxY : x ^ p ≤ L ^ p * Y := by
    have hE : e ^ (4 * p + 1) ≤ (N : ℝ) ^ δ := by
      rw [he, ← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
      refine Real.rpow_le_rpow_of_exponent_le hN1r ?_
      have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      have h4 : 4 * (p : ℝ) + 1 ≤ 20 * p := by linarith only [hP]
      push_cast
      calc εa * (4 * (p : ℝ) + 1) ≤ εa * (20 * p) := mul_le_mul_of_nonneg_left h4 hεa.le
        _ = 20 * p * εa := by ring
        _ ≤ δ := hεaδ
    have : x ≤ L * ((N : ℝ) ^ δ * Ψ ^ 2) := by
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE hL0) (sq_nonneg Ψ)
      calc x = L * e ^ (4 * p + 1) * Ψ ^ 2 := hx
        _ ≤ L * (N : ℝ) ^ δ * Ψ ^ 2 := this
        _ = L * ((N : ℝ) ^ δ * Ψ ^ 2) := by ring
    calc x ^ p ≤ (L * ((N : ℝ) ^ δ * Ψ ^ 2)) ^ p := pow_le_pow_left₀ hx0 this p
      _ = L ^ p * Y := by rw [hY, mul_pow]
  have hNY : ((N : ℝ) ^ (2 * p))⁻¹ ≤ τ⁻¹ ^ (2 * p) * Y := by
    have h1 : (τ / N) ^ (2 * p) ≤ Ψ ^ (2 * p) := pow_le_pow_left₀ (by positivity) hΨge _
    have h2 : Ψ ^ (2 * p) ≤ Y := by
      rw [hY, mul_pow, ← pow_mul]
      exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ hNδ)
    have e1 : ((N : ℝ) ^ (2 * p))⁻¹ = τ⁻¹ ^ (2 * p) * (τ / N) ^ (2 * p) := by
      rw [div_pow, inv_pow]; field_simp
    rw [e1]
    exact mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
  have hTY : T ≤ ((4 * (p : ℝ) + 1) ^ p * (L ^ p + 1) + 2 * τ⁻¹ ^ (2 * p)) * (Y + EF) := by
    have hA0 : (0 : ℝ) ≤ (4 * (p : ℝ) + 1) ^ p := by positivity
    have hLp : 0 ≤ L ^ p := by positivity
    have hτp : 0 ≤ τ⁻¹ ^ (2 * p) := by positivity
    have h1 : T ≤ (4 * (p : ℝ) + 1) ^ p * (EF + L ^ p * Y) + 2 * (τ⁻¹ ^ (2 * p) * Y) := by
      rw [hT]
      exact add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl hxY) hA0)
        (mul_le_mul_of_nonneg_left hNY (by norm_num))
    have h2 : 0 ≤ (4 * (p : ℝ) + 1) ^ p * Y + (4 * (p : ℝ) + 1) ^ p * L ^ p * EF +
        2 * τ⁻¹ ^ (2 * p) * EF :=
      add_nonneg (add_nonneg (mul_nonneg hA0 hY0) (mul_nonneg (mul_nonneg hA0 hLp) hEF0))
        (mul_nonneg (mul_nonneg (by norm_num) hτp) hEF0)
    have e : ((4 * (p : ℝ) + 1) ^ p * (L ^ p + 1) + 2 * τ⁻¹ ^ (2 * p)) * (Y + EF) =
        (4 * (p : ℝ) + 1) ^ p * (EF + L ^ p * Y) + 2 * (τ⁻¹ ^ (2 * p) * Y) +
          ((4 * (p : ℝ) + 1) ^ p * Y + (4 * (p : ℝ) + 1) ^ p * L ^ p * EF +
            2 * τ⁻¹ ^ (2 * p) * EF) := by ring
    rw [e]
    linarith only [h1, h2]
  calc (N : ℝ) ^ (-(n : ℝ) / 2) * ∑ i, ∑ μ, ‖∫ ω, fCoeff p (avgCoeff Sig (X ω) z i μ) n‖
      ≤ (N : ℝ) ^ (-(n : ℝ) / 2) * ((M : ℝ) * N * T) :=
        mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hNp.le _)
    _ = ((N : ℝ) ^ (-(n : ℝ) / 2) * ((M : ℝ) * N)) * T := by ring
    _ ≤ τ⁻¹ * T := mul_le_mul_of_nonneg_right hpre hT0'
    _ ≤ τ⁻¹ * (((4 * (p : ℝ) + 1) ^ p * (L ^ p + 1) + 2 * τ⁻¹ ^ (2 * p)) * (Y + EF)) :=
        mul_le_mul_of_nonneg_left hTY hT0.le
    _ = _ := by rw [hY, hEF]; ring

/-- `avg_claim_ge4` at `τ = 1/20`, `c = 1`, `C = gaussMoment`, `p = 2`, `δ = 1/10`,
`εa = 1/1000`, `Da = dPrevTwo (1/20) 2` (an `∃ K, ∃ N₀` statement: every parameter hypothesis
is discharged; the setting, the a priori law, the entry assumptions and `z`, `n` stay binders). -/
example : ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (S : Set ℂ), CompSetting (1 / 20) 1 M N Sig S →
      AnisoAllAt N gaussMoment Sig S (1 / 1000) (dPrevTwo (1 / 20) 2) →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption gaussMoment X →
        ∀ z ∈ S, ∀ n ∈ Finset.Icc 4 (4 * 2 : ℕ),
          (N : ℝ) ^ (-(n : ℝ) / 2) * ∑ i, ∑ μ, ‖∫ ω, fCoeff 2 (avgCoeff Sig (X ω) z i μ) n‖ ≤
            K * (((N : ℝ) ^ (1 / 10 : ℝ) * Psi N (specOf Sig) z ^ 2) ^ 2 +
              ∫ ω, Ft Sig (X ω) z ^ 2) :=
  avg_claim_ge4 (1 / 20) 1 gaussMoment 2 (1 / 10) (1 / 1000) (dPrevTwo (1 / 20) 2)
    (by norm_num) (by norm_num) (by norm_num) even_two le_rfl (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) le_rfl

end Anisotropic
