module

public import Anisotropic.Density.Stability.EdgeSqRoot
public import Anisotropic.Density.Stability.EdgeTools
public import Anisotropic.EdgeUniv.Derivative
public import Anisotropic.Endpoints.Main
public import Anisotropic.Framework.Domination

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # Entry bounds at the counting points, the bound on `⟨s_i, G e_i⟩`, entry-change stability and the `m`-difference -/

/-! ## Test vectors `Σ̲ x` -/

/-- The real matrix `Σ̲ = diag(Σ, 1)` of (def_ul_Sigma). -/
private def ebR (Sig : Matrix (Fin M) (Fin M) ℝ) : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℝ :=
  fromBlocks Sig 0 0 1

private lemma eb_ulSigma_eq (Sig : Matrix (Fin M) (Fin M) ℝ) :
    ulSigma N Sig = (ebR (N := N) Sig).map (algebraMap ℝ ℂ) := by
  unfold ulSigma ebR
  rw [Matrix.fromBlocks_map]
  simp

/-- `⟨R x, L R y⟩ = ⟨x, Rᵀ L R y⟩` for a real matrix `R`. -/
private lemma eb_testBilin_mulVec {ι : Type*} [Fintype ι] (R : Matrix ι ι ℝ) (L : Matrix ι ι ℂ)
    (x y : ι → ℝ) :
    testBilin (R *ᵥ x) L (R *ᵥ y) =
      testBilin x ((R.map (algebraMap ℝ ℂ))ᵀ * L * R.map (algebraMap ℝ ℂ)) y := by
  have hc : ∀ v : ι → ℝ, (fun s => ((R *ᵥ v) s : ℂ)) =
      R.map (algebraMap ℝ ℂ) *ᵥ fun s => (v s : ℂ) := by
    intro v
    ext s
    simp [mulVec, dotProduct, Complex.ofReal_sum]
  unfold testBilin
  rw [hc x, hc y, ← mulVec_mulVec, ← mulVec_mulVec,
    dotProduct_mulVec _ (R.map (algebraMap ℝ ℂ))ᵀ, vecMul_transpose]

/-- `⟨Σ̲ x, Σ̲⁻¹ (G − Π) Σ̲⁻¹ Σ̲ y⟩ = ⟨x, (G − Π) y⟩`. -/
private lemma eb_testBilin_lawMat {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (x y : Fin M ⊕ Fin N → ℝ) :
    testBilin (ebR Sig *ᵥ x) (lawMat Sig Xm z) (ebR Sig *ᵥ y) =
      testBilin x (G Sig Xm z - piMat Sig (mFun N (specOf Sig) z)) y := by
  rw [eb_testBilin_mulVec, ← eb_ulSigma_eq]
  have hT : Sigᵀ = Sig := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact hSig.1.eq
  have hS : Sig * Sig⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hSig.isUnit)
  have hS' : Sig⁻¹ * Sig = 1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hSig.isUnit)
  set V : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ := fromBlocks (cplx Sig⁻¹) 0 0 1 with hV
  have h1 : ulSigma N Sig * V = 1 := by
    rw [ulSigma, hV, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one]
    rw [show Sig.map (algebraMap ℝ ℂ) * cplx Sig⁻¹ = 1 by
      rw [cplx, ← Matrix.map_mul, hS, Matrix.map_one _ (map_zero _) (map_one _)]]
    exact fromBlocks_one
  have h2 : V * ulSigma N Sig = 1 := by
    rw [ulSigma, hV, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one]
    rw [show cplx Sig⁻¹ * Sig.map (algebraMap ℝ ℂ) = 1 by
      rw [cplx, ← Matrix.map_mul, hS', Matrix.map_one _ (map_zero _) (map_one _)]]
    exact fromBlocks_one
  have hinv : (ulSigma N Sig)⁻¹ = V := Matrix.inv_eq_right_inv h1
  have htr : (ulSigma N Sig)ᵀ = ulSigma N Sig := by
    rw [ulSigma, fromBlocks_transpose]
    simp [← Matrix.transpose_map, hT]
  unfold lawMat
  rw [htr, hinv]
  congr 1
  calc ulSigma N Sig * (V * (G Sig Xm z - piMat Sig (mFun N (specOf Sig) z)) * V) *
        ulSigma N Sig
      = (ulSigma N Sig * V) * (G Sig Xm z - piMat Sig (mFun N (specOf Sig) z)) *
          (V * ulSigma N Sig) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

/-! ## Spectral calculus for `Σ` -/

private lemma eb_diag {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) :
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

/-- `(Σ (1 + wΣ)⁻¹)_{jl} = ∑ₖ U_{jk} σₖ (1 + σₖ w)⁻¹ U_{lk}` for `Σ = U diag(σ) Uᵀ`. -/
private lemma eb_SigInv_entry {Sig U : Matrix (Fin M) (Fin M) ℝ} {σ : Fin M → ℝ}
    (h₂ : U * Uᵀ = 1) (h₁ : Uᵀ * U = 1) (hS : Sig = U * diagonal σ * Uᵀ) {w : ℂ}
    (hw : ∀ i, 1 + (σ i : ℂ) * w ≠ 0) (j l : Fin M) :
    (cplx Sig * (1 + w • cplx Sig)⁻¹) j l =
      ∑ k, (U j k : ℂ) * ((σ k : ℂ) * (1 + (σ k : ℂ) * w)⁻¹) * (U l k : ℂ) := by
  have c₂ : (cplx Uᵀ)ᵀ * cplx Uᵀ = 1 := by
    simp only [cplx]
    rw [← transpose_map, transpose_transpose, ← Matrix.map_mul, h₂,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have c₁ : cplx Uᵀ * (cplx Uᵀ)ᵀ = 1 := by
    simp only [cplx]
    rw [← transpose_map, transpose_transpose, ← Matrix.map_mul, h₁,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have e1 : cplx Sig = (cplx Uᵀ)ᵀ * diagonal (fun i => (σ i : ℂ)) * cplx Uᵀ := by
    simp only [cplx]
    rw [hS, ← transpose_map, transpose_transpose, Matrix.map_mul, Matrix.map_mul,
      diagonal_map (map_zero _)]
    rfl
  have hT : 1 + w • cplx Sig =
      (cplx Uᵀ)ᵀ * diagonal (fun i => 1 + (σ i : ℂ) * w) * cplx Uᵀ := by
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
  have hprod : cplx Sig * (1 + w • cplx Sig)⁻¹ = (cplx Uᵀ)ᵀ *
      diagonal (fun i => (σ i : ℂ) * (1 + (σ i : ℂ) * w)⁻¹) * cplx Uᵀ := by
    rw [hinv, e1]
    calc (cplx Uᵀ)ᵀ * diagonal (fun i => (σ i : ℂ)) * cplx Uᵀ *
          ((cplx Uᵀ)ᵀ * diagonal (fun i => (1 + (σ i : ℂ) * w)⁻¹) * cplx Uᵀ)
        = (cplx Uᵀ)ᵀ * (diagonal (fun i => (σ i : ℂ)) * (cplx Uᵀ * (cplx Uᵀ)ᵀ) *
            diagonal (fun i => (1 + (σ i : ℂ) * w)⁻¹)) * cplx Uᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [c₁, Matrix.mul_one, diagonal_mul_diagonal]
  rw [hprod]
  simp only [Matrix.mul_apply, cplx, Matrix.diagonal_apply, Matrix.transpose_apply,
    Matrix.map_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Complex.coe_algebraMap]

private lemma eb_row_sq {K : ℕ} {U : Matrix (Fin K) (Fin K) ℝ} (h₂ : U * Uᵀ = 1)
    (i : Fin K) : ∑ k, U i k ^ 2 = 1 := by
  have := congrFun (congrFun h₂ i) i
  simpa [Matrix.mul_apply, sq, Matrix.one_apply] using this

/-- `∑_j Σ_{ji}² ≤ τ⁻²` when every eigenvalue of `Σ > 0` is at most `τ⁻¹`. -/
private lemma eb_col_sq_le {τ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (hle : ∀ k, specOf Sig k ≤ τ⁻¹) (i : Fin M) :
    ∑ j, Sig j i ^ 2 ≤ τ⁻¹ ^ 2 := by
  obtain ⟨U, h₂, h₁, hSd, hσ⟩ := eb_diag hSig
  have hT : Sigᵀ = Sig := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact hSig.1.eq
  have hSS : Sig * Sig = U * diagonal (fun k => specOf Sig k ^ 2) * Uᵀ := by
    conv_lhs => rw [hSd]
    calc U * diagonal (specOf Sig) * Uᵀ * (U * diagonal (specOf Sig) * Uᵀ)
        = U * (diagonal (specOf Sig) * (Uᵀ * U) * diagonal (specOf Sig)) * Uᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [h₁, Matrix.mul_one, diagonal_mul_diagonal]
          congr 3
          funext k
          ring
  have e1 : ∑ j, Sig j i ^ 2 = (Sig * Sig) i i := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : Sig i j = Sig j i := by
      have := congrFun (congrFun hT j) i
      simpa [Matrix.transpose_apply] using this
    rw [this, sq]
  have e2 : (Sig * Sig) i i = ∑ k, U i k ^ 2 * specOf Sig k ^ 2 := by
    rw [hSS]
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply, mul_ite,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e1, e2]
  calc ∑ k, U i k ^ 2 * specOf Sig k ^ 2 ≤ ∑ k, U i k ^ 2 * τ⁻¹ ^ 2 := by
        refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        exact pow_le_pow_left₀ (hσ k).le (hle k) 2
    _ = τ⁻¹ ^ 2 := by rw [← Finset.sum_mul, eb_row_sq h₂, one_mul]

/-- `|Σ̲ e_s| ≤ τ⁻¹` for `τ ≤ 1`. -/
private lemma eb_testNorm_col_le {τ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hle : ∀ k, specOf Sig k ≤ τ⁻¹) (s : Fin M ⊕ Fin N) :
    testNorm (ebR Sig *ᵥ Pi.single s 1) ≤ τ⁻¹ := by
  have hτi : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  rw [mulVec_single_one]
  unfold testNorm
  rw [Real.sqrt_le_left (by positivity)]
  rcases s with i | μ
  · have e : ∑ t, (ebR (N := N) Sig).col (Sum.inl i) t ^ 2 = ∑ j, Sig j i ^ 2 := by
      simp [ebR, Fintype.sum_sum_type, Matrix.col_apply]
    rw [e]
    exact eb_col_sq_le hSig hle i
  · have e : ∑ t, (ebR (N := N) Sig).col (Sum.inr μ) t ^ 2 = 1 := by
      simp [ebR, Fintype.sum_sum_type, Matrix.col_apply, Matrix.one_apply]
    rw [e]
    exact one_le_pow₀ hτi

/-- `Σ̲ (0, s) = (0, s)` and `|(0, s)| = |s|`. -/
private lemma eb_ebR_embN (Sig : Matrix (Fin M) (Fin M) ℝ) (s : Fin N → ℝ) :
    ebR Sig *ᵥ Sum.elim (0 : Fin M → ℝ) s = Sum.elim (0 : Fin M → ℝ) s ∧
      testNorm (Sum.elim (0 : Fin M → ℝ) s) = testNorm s := by
  constructor
  · ext t
    rcases t with j | μ <;> simp [ebR, mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]
  · simp [testNorm, Fintype.sum_sum_type]

private lemma eb_testBilin_single {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (s t : ι) : testBilin (Pi.single s 1) A (Pi.single t 1) = A s t := by
  unfold testBilin
  have h1 : (fun u => (((Pi.single t (1 : ℝ) : ι → ℝ) u : ℝ) : ℂ)) = Pi.single t 1 := by
    ext u; by_cases h : u = t <;> simp [h]
  have h2 : (fun u => (((Pi.single s (1 : ℝ) : ι → ℝ) u : ℝ) : ℂ)) = Pi.single s 1 := by
    ext u; by_cases h : u = s <;> simp [h]
  rw [h1, h2, mulVec_single_one, single_one_dotProduct]
  simp

private lemma eb_testBilin_embN (A : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) (s : Fin N → ℝ)
    (i : Fin M) :
    testBilin (Sum.elim (0 : Fin M → ℝ) s) A (Pi.single (Sum.inl i) 1) =
      ∑ μ, (s μ : ℂ) * A (Sum.inr μ) (Sum.inl i) := by
  unfold testBilin
  have h1 : (fun u => (((Pi.single (Sum.inl i) (1 : ℝ) : Fin M ⊕ Fin N → ℝ) u : ℝ) : ℂ)) =
      Pi.single (Sum.inl i) 1 := by
    ext u; by_cases h : u = Sum.inl i <;> simp [h]
  rw [h1, mulVec_single_one]
  simp [dotProduct, Fintype.sum_sum_type]

/-! ## The deterministic matrix `Π` -/

/-- `|Π_{st}| ≤ A c⁻¹ + C_m` when `0 ≤ σ_k ≤ A`, `|1 + σ_k w| ≥ c` and `|w| ≤ C_m`. -/
private lemma eb_piMat_le {A c Cm : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (hA : 0 ≤ A) (hle : ∀ k, specOf Sig k ≤ A) (hc : 0 < c) (hCm : 0 ≤ Cm) {w : ℂ}
    (hOne : ∀ k, c ≤ ‖1 + (specOf Sig k : ℂ) * w‖) (hw : ‖w‖ ≤ Cm) (s t : Fin M ⊕ Fin N) :
    ‖piMat (N := N) Sig w s t‖ ≤ A * c⁻¹ + Cm := by
  obtain ⟨U, h₂, h₁, hSd, hσ⟩ := eb_diag hSig
  have hw0 : ∀ i, 1 + (specOf Sig i : ℂ) * w ≠ 0 := fun i h0 => by
    have := hOne i
    rw [h0, norm_zero] at this
    linarith
  set d : Fin M → ℂ := fun k => (specOf Sig k : ℂ) * (1 + (specOf Sig k : ℂ) * w)⁻¹ with hd
  have hdle : ∀ k, ‖d k‖ ≤ A * c⁻¹ := fun k => by
    simp only [hd]
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hσ k).le]
    exact mul_le_mul (hle k) (inv_anti₀ hc (hOne k)) (inv_nonneg.2 (norm_nonneg _)) hA
  have hD0 : 0 ≤ A * c⁻¹ := mul_nonneg hA (inv_nonneg.2 hc.le)
  have he := eb_SigInv_entry h₂ h₁ hSd hw0
  rcases s with j | ν <;> rcases t with l | ν'
  · simp only [piMat, fromBlocks_apply₁₁, Matrix.neg_apply, norm_neg]
    rw [he]
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun k => |U j k|) (fun k => |U l k|)
    simp only [sq_abs] at hcs
    rw [eb_row_sq h₂, eb_row_sq h₂, Real.sqrt_one, mul_one] at hcs
    calc ‖∑ k, (U j k : ℂ) * d k * (U l k : ℂ)‖ ≤ ∑ k, A * c⁻¹ * (|U j k| * |U l k|) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs]
          have := mul_le_mul_of_nonneg_left (hdle k) (abs_nonneg (U j k))
          calc |U j k| * ‖d k‖ * |U l k| ≤ |U j k| * (A * c⁻¹) * |U l k| :=
                mul_le_mul_of_nonneg_right this (abs_nonneg _)
            _ = A * c⁻¹ * (|U j k| * |U l k|) := by ring
      _ = A * c⁻¹ * ∑ k, |U j k| * |U l k| := by rw [Finset.mul_sum]
      _ ≤ A * c⁻¹ * 1 := mul_le_mul_of_nonneg_left hcs hD0
      _ ≤ A * c⁻¹ + Cm := by linarith
  · simp [piMat]; positivity
  · simp [piMat]; positivity
  · simp only [piMat, fromBlocks_apply₂₂, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero]
    split_ifs
    · linarith
    · simp only [norm_zero]; positivity

/-- `|w₂ Π_{ii}(w₂) - w₁ Π_{ii}(w₁)| ≤ A c⁻² |w₂ - w₁|` when `0 ≤ σ_k ≤ A` and
`|1 + σ_k w_j| ≥ c`, from `w Π_{ii}(w) = -∑_k U_{ik}² w σ_k (1 + σ_k w)⁻¹` in an eigenbasis `U`
of `Σ`. -/
private lemma eb_mPi_sub {A c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (hA : 0 ≤ A) (hle : ∀ k, specOf Sig k ≤ A) (hc : 0 < c) {w₁ w₂ : ℂ}
    (hOne₁ : ∀ k, c ≤ ‖1 + (specOf Sig k : ℂ) * w₁‖)
    (hOne₂ : ∀ k, c ≤ ‖1 + (specOf Sig k : ℂ) * w₂‖) (i : Fin M) :
    ‖w₂ * piMat (N := N) Sig w₂ (Sum.inl i) (Sum.inl i) -
        w₁ * piMat (N := N) Sig w₁ (Sum.inl i) (Sum.inl i)‖ ≤ A * c⁻¹ ^ 2 * ‖w₂ - w₁‖ := by
  obtain ⟨U, h₂, h₁, hSd, hσ⟩ := eb_diag hSig
  have hne : ∀ (w : ℂ), (∀ k, c ≤ ‖1 + (specOf Sig k : ℂ) * w‖) →
      ∀ k, 1 + (specOf Sig k : ℂ) * w ≠ 0 := fun w hw k h0 => by
    have := hw k
    rw [h0, norm_zero] at this
    linarith
  have hP : ∀ (w : ℂ), (∀ k, c ≤ ‖1 + (specOf Sig k : ℂ) * w‖) →
      w * piMat (N := N) Sig w (Sum.inl i) (Sum.inl i) =
        -∑ k, ((U i k ^ 2 : ℝ) : ℂ) * (w * ((specOf Sig k : ℂ) *
          (1 + (specOf Sig k : ℂ) * w)⁻¹)) := by
    intro w hw
    simp only [piMat, fromBlocks_apply₁₁, Matrix.neg_apply]
    rw [eb_SigInv_entry h₂ h₁ hSd (hne w hw), mul_neg, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
  rw [hP w₂ hOne₂, hP w₁ hOne₁, neg_sub_neg, ← Finset.sum_sub_distrib]
  have hk : ∀ k, ‖((U i k ^ 2 : ℝ) : ℂ) * (w₁ * ((specOf Sig k : ℂ) *
        (1 + (specOf Sig k : ℂ) * w₁)⁻¹)) - ((U i k ^ 2 : ℝ) : ℂ) * (w₂ * ((specOf Sig k : ℂ) *
        (1 + (specOf Sig k : ℂ) * w₂)⁻¹))‖ ≤ U i k ^ 2 * (A * c⁻¹ ^ 2 * ‖w₂ - w₁‖) := by
    intro k
    have h1 := hne w₁ hOne₁ k
    have h2 := hne w₂ hOne₂ k
    have e : ((U i k ^ 2 : ℝ) : ℂ) * (w₁ * ((specOf Sig k : ℂ) *
        (1 + (specOf Sig k : ℂ) * w₁)⁻¹)) - ((U i k ^ 2 : ℝ) : ℂ) * (w₂ * ((specOf Sig k : ℂ) *
        (1 + (specOf Sig k : ℂ) * w₂)⁻¹)) = ((U i k ^ 2 : ℝ) : ℂ) * ((specOf Sig k : ℂ) *
        (w₁ - w₂) * ((1 + (specOf Sig k : ℂ) * w₁)⁻¹ * (1 + (specOf Sig k : ℂ) * w₂)⁻¹)) := by
      have ha := mul_inv_cancel₀ h1
      have hb := mul_inv_cancel₀ h2
      linear_combination
        (-(((U i k ^ 2 : ℝ) : ℂ) * (specOf Sig k : ℂ) * w₁ *
          (1 + (specOf Sig k : ℂ) * w₁)⁻¹)) * hb +
        (((U i k ^ 2 : ℝ) : ℂ) * (specOf Sig k : ℂ) * w₂ *
          (1 + (specOf Sig k : ℂ) * w₂)⁻¹) * ha
    rw [e, norm_mul, norm_mul, norm_mul, norm_mul, norm_inv, norm_inv, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (hσ k).le, norm_sub_rev w₁ w₂]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    have i1 : ‖1 + (specOf Sig k : ℂ) * w₁‖⁻¹ ≤ c⁻¹ := inv_anti₀ hc (hOne₁ k)
    have i2 : ‖1 + (specOf Sig k : ℂ) * w₂‖⁻¹ ≤ c⁻¹ := inv_anti₀ hc (hOne₂ k)
    have i0 : 0 ≤ ‖w₂ - w₁‖ := norm_nonneg _
    calc specOf Sig k * ‖w₂ - w₁‖ * (‖1 + (specOf Sig k : ℂ) * w₁‖⁻¹ *
          ‖1 + (specOf Sig k : ℂ) * w₂‖⁻¹)
        ≤ A * ‖w₂ - w₁‖ * (c⁻¹ * c⁻¹) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right (hle k) i0)
            (mul_le_mul i1 i2 (inv_nonneg.2 (norm_nonneg _)) (inv_nonneg.2 hc.le))
            (by positivity) (mul_nonneg hA i0)
      _ = A * c⁻¹ ^ 2 * ‖w₂ - w₁‖ := by ring
  calc ‖∑ k, (((U i k ^ 2 : ℝ) : ℂ) * (w₁ * ((specOf Sig k : ℂ) *
        (1 + (specOf Sig k : ℂ) * w₁)⁻¹)) - ((U i k ^ 2 : ℝ) : ℂ) * (w₂ * ((specOf Sig k : ℂ) *
        (1 + (specOf Sig k : ℂ) * w₂)⁻¹)))‖
      ≤ ∑ k, U i k ^ 2 * (A * c⁻¹ ^ 2 * ‖w₂ - w₁‖) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => hk k)
    _ = A * c⁻¹ ^ 2 * ‖w₂ - w₁‖ := by rw [← Finset.sum_mul, eb_row_sq h₂, one_mul]

/-! ## Entry-change stability -/

private lemma eb_Delta_smul (i : Fin M) (μ : Fin N) (c : ℝ) :
    Delta i μ c = (c : ℂ) • Delta i μ 1 := by
  ext s t
  simp only [Delta, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

/-- `(B Δ¹ C)_{st} = B_{s i} C_{μ t} + B_{s μ} C_{i t}`. -/
private lemma eb_mul_Delta_mul (B C : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ)
    (i : Fin M) (μ : Fin N) (s t : Fin M ⊕ Fin N) :
    (B * Delta i μ 1 * C) s t = B s (Sum.inl i) * C (Sum.inr μ) t +
      B s (Sum.inr μ) * C (Sum.inl i) t := by
  have hBD : ∀ r, (B * Delta i μ 1) s r =
      (if r = Sum.inr μ then B s (Sum.inl i) else 0) +
        (if r = Sum.inl i then B s (Sum.inr μ) else 0) := by
    intro r
    rw [Matrix.mul_apply]
    rcases r with j | ν
    · by_cases hj : j = i <;> simp [Delta, hj]
    · by_cases hν : ν = μ <;> simp [Delta, hν]
  rw [Matrix.mul_apply]
  simp only [hBD, add_mul, ite_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- Entry-change stability ((res_exp) at order zero, `G' = G + G' Δ G`, restricted to the
block `J = {i, μ}`): if the `J × J` entries of `G` at `X^{u}_{(iμ)}` are bounded by `B` and
`2B|u - u'| ≤ 1/2`, then the `J × J` entries at `X^{u'}_{(iμ)}` differ from them by at most
`4B²|u - u'|`. The bound is deterministic and holds for every `X`, `u`, `u'`. -/
theorem entryBounds_stability {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (i : Fin M) (μ : Fin N)
    (u u' B : ℝ)
    (hB : ∀ a ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
      ∀ b ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)), ‖G Sig (Xupd Xm i μ u) z a b‖ ≤ B)
    (hd : 2 * B * |u - u'| ≤ 1 / 2) :
    ∀ a ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
      ∀ b ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
        ‖G Sig (Xupd Xm i μ u') z a b - G Sig (Xupd Xm i μ u) z a b‖ ≤ 4 * B ^ 2 * |u - u'| := by
  set G0 := G Sig (Xupd Xm i μ u) z with hG0
  set G1 := G Sig (Xupd Xm i μ u') z with hG1
  set J : Set (Fin M ⊕ Fin N) := {Sum.inl i, Sum.inr μ} with hJ
  have hiJ : (Sum.inl i : Fin M ⊕ Fin N) ∈ J := Set.mem_insert _ _
  have hμJ : (Sum.inr μ : Fin M ⊕ Fin N) ∈ J := Set.mem_insert_of_mem _ rfl
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB _ hiJ _ hiJ)
  have hres' : G1 = G0 + G1 * (Delta i μ (u - u') * G0) := by
    have h := res_exp hSig Xm hz i μ u u' 0
    have he : Finset.Icc 1 0 = (∅ : Finset ℕ) := rfl
    rw [he, Finset.sum_empty, add_zero, zero_add, pow_one] at h
    exact h
  have hent : ∀ a b, G1 a b - G0 a b = ((u - u' : ℝ) : ℂ) *
      (G1 a (Sum.inl i) * G0 (Sum.inr μ) b + G1 a (Sum.inr μ) * G0 (Sum.inl i) b) := by
    intro a b
    have h := congrFun (congrFun hres' a) b
    rw [Matrix.add_apply] at h
    rw [eb_Delta_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply, ← Matrix.mul_assoc,
      eb_mul_Delta_mul, smul_eq_mul] at h
    rw [h]
    ring
  set f : Fin M ⊕ Fin N → Fin M ⊕ Fin N → ℝ := fun a b => ‖G1 a b - G0 a b‖ with hf
  set x := max (max (f (Sum.inl i) (Sum.inl i)) (f (Sum.inl i) (Sum.inr μ)))
    (max (f (Sum.inr μ) (Sum.inl i)) (f (Sum.inr μ) (Sum.inr μ))) with hx
  have hmem : ∀ a ∈ J, a = Sum.inl i ∨ a = Sum.inr μ := fun a ha => by
    simpa [hJ] using ha
  have hfx : ∀ a ∈ J, ∀ b ∈ J, f a b ≤ x := by
    intro a ha b hb
    rcases hmem a ha with rfl | rfl <;> rcases hmem b hb with rfl | rfl
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · exact (le_max_right _ _).trans (le_max_left _ _)
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  have hG1 : ∀ a ∈ J, ∀ b ∈ J, ‖G1 a b‖ ≤ B + x := by
    intro a ha b hb
    have : G1 a b = G0 a b + (G1 a b - G0 a b) := by ring
    rw [this]
    exact (norm_add_le _ _).trans (add_le_add (hB a ha b hb) (hfx a ha b hb))
  have hstep : ∀ a ∈ J, ∀ b ∈ J, f a b ≤ |u - u'| * (2 * (B + x) * B) := by
    intro a ha b hb
    simp only [hf]
    rw [hent, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h1 := mul_le_mul (hG1 a ha _ hiJ) (hB _ hμJ b hb) (norm_nonneg _) (by
      linarith [hfx a ha _ hiJ, (norm_nonneg (G1 a (Sum.inl i) - G0 a (Sum.inl i)))])
    have h2 := mul_le_mul (hG1 a ha _ hμJ) (hB _ hiJ b hb) (norm_nonneg _) (by
      linarith [hfx a ha _ hiJ, (norm_nonneg (G1 a (Sum.inl i) - G0 a (Sum.inl i)))])
    linarith
  have hx0 : 0 ≤ x := (norm_nonneg _).trans (hfx _ hiJ _ hiJ)
  have hxle : x ≤ 4 * B ^ 2 * |u - u'| := by
    have hxs : x ≤ |u - u'| * (2 * (B + x) * B) := by
      simp only [hx]
      refine max_le (max_le ?_ ?_) (max_le ?_ ?_)
      · exact hstep _ hiJ _ hiJ
      · exact hstep _ hiJ _ hμJ
      · exact hstep _ hμJ _ hiJ
      · exact hstep _ hμJ _ hμJ
    have e1 : |u - u'| * (2 * (B + x) * B) = 2 * B ^ 2 * |u - u'| + (2 * B * |u - u'|) * x := by
      ring
    have e2 : (2 * B * |u - u'|) * x ≤ (1 / 2) * x := mul_le_mul_of_nonneg_right hd hx0
    linarith
  intro a ha b hb
  exact (hfx a ha b hb).trans hxle

/-- Entry-change stability around a reference matrix `P` (for instance `Π`): if the `J × J`
entries of `G` at `X^{u}_{(iμ)}` are within `δ ≤ 1` of `P`, `|P_{ab}| ≤ K` on `J × J`, and
`2(K + 1)|u - u'| ≤ 1/2`, then the entries at `X^{u'}_{(iμ)}` are within
`δ + 4(K + 1)²|u - u'|` of `P`. -/
theorem entryBounds_stability_ref {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (i : Fin M) (μ : Fin N)
    (u u' K δ : ℝ) (P : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ)
    (hδ : ∀ a ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
      ∀ b ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
        ‖G Sig (Xupd Xm i μ u) z a b - P a b‖ ≤ δ)
    (hP : ∀ a ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
      ∀ b ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)), ‖P a b‖ ≤ K)
    (hδ1 : δ ≤ 1) (hd : 2 * (K + 1) * |u - u'| ≤ 1 / 2) :
    ∀ a ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
      ∀ b ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
        ‖G Sig (Xupd Xm i μ u') z a b - P a b‖ ≤ δ + 4 * (K + 1) ^ 2 * |u - u'| := by
  have hB : ∀ a ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
      ∀ b ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
        ‖G Sig (Xupd Xm i μ u) z a b‖ ≤ K + 1 := by
    intro a ha b hb
    have e : G Sig (Xupd Xm i μ u) z a b =
        P a b + (G Sig (Xupd Xm i μ u) z a b - P a b) := by ring
    rw [e]
    exact (norm_add_le _ _).trans (by linarith [hP a ha b hb, hδ a ha b hb])
  have hs := entryBounds_stability hSig Xm hz i μ u u' (K + 1) hB hd
  intro a ha b hb
  have e : G Sig (Xupd Xm i μ u') z a b - P a b =
      (G Sig (Xupd Xm i μ u') z a b - G Sig (Xupd Xm i μ u) z a b) +
        (G Sig (Xupd Xm i μ u) z a b - P a b) := by ring
  rw [e]
  exact (norm_add_le _ _).trans (by linarith [hs a ha b hb, hδ a ha b hb])

/-! ## The `m`-difference -/

/-- (z-a_taylor) in square-root form: for a regular edge `k`, `Im z ≥ 0` and
`|z - a_k| ≤ τ'₀`, `|m(z) - x_k| ≤ (4|z - a_k|/c₂)^{1/2}`, with `m` extended to the real axis. -/
theorem entryBounds_mExt_sub_xCrit {τ : ℝ} {σ : Fin M → ℝ} {k : ℕ}
    (h : DensityAssumptions τ N σ) (hk : RegularEdge τ N σ k) {z : ℂ} (hz : 0 ≤ z.im)
    (hza : ‖z - edgeVal N σ k‖ ≤ edgeTau0 τ) :
    ‖mExt N σ z - xCrit N σ k‖ ≤ √(4 * ‖z - edgeVal N σ k‖ / edgec2 τ) := by
  obtain ⟨-, -, h3, -⟩ := z_a_taylor h hk hz hza
  have hc2 := edgec2_pos h.pos
  have hsq : ‖mExt N σ z - xCrit N σ k‖ ^ 2 ≤ 4 * ‖z - edgeVal N σ k‖ / edgec2 τ := by
    rw [le_div_iff₀ hc2]
    calc ‖mExt N σ z - xCrit N σ k‖ ^ 2 * edgec2 τ =
          4 * (edgec2 τ / 4 * ‖mExt N σ z - xCrit N σ k‖ ^ 2) := by ring
      _ ≤ 4 * ‖z - edgeVal N σ k‖ := by linarith
  have := Real.abs_le_sqrt hsq
  rwa [abs_of_nonneg (norm_nonneg _)] at this

/-- The same bound for `Im z > 0`, where `m` is the Stieltjes transform `mFun`. -/
theorem entryBounds_mFun_sub_xCrit {τ : ℝ} {σ : Fin M → ℝ} {k : ℕ}
    (h : DensityAssumptions τ N σ) (hk : RegularEdge τ N σ k) {z : ℂ} (hz : 0 < z.im)
    (hza : ‖z - edgeVal N σ k‖ ≤ edgeTau0 τ) :
    ‖mFun N σ z - xCrit N σ k‖ ≤ √(4 * ‖z - edgeVal N σ k‖ / edgec2 τ) := by
  have hm : mExt N σ z = mFun N σ z := by simp [mExt, hz]
  rw [← hm]
  exact entryBounds_mExt_sub_xCrit h hk hz.le hza

/-! ## Window points `E + iη` -/

/-- `N^y ≤ c` eventually, for `y < 0` and `c > 0`. -/
private lemma eb_ev_small {y c : ℝ} (hy : y < 0) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ y ≤ c := by
  have h := (tendsto_rpow_neg_atTop (neg_pos.2 hy)).comp tendsto_natCast_atTop_atTop
  have h' : Tendsto (fun N : ℕ => (N : ℝ) ^ y) atTop (𝓝 0) := by
    refine h.congr fun N => ?_
    simp
  exact (h'.eventually (ge_mem_nhds hc))

/-- `A ≤ N^y` eventually, for `y > 0`. -/
private lemma eb_ev_large {y : ℝ} (hy : 0 < y) (A : ℝ) :
    ∀ᶠ N : ℕ in atTop, A ≤ (N : ℝ) ^ y :=
  ((tendsto_rpow_atTop hy).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop A

/-- The law parameter `τ₂ = min(τ/2, 1/6, (2τ⁻¹(1+τ⁻¹)+1)⁻¹)`. -/
private def ebTau (τ : ℝ) : ℝ := min (τ / 2) (min (1 / 6) ((2 * τ⁻¹ * (1 + τ⁻¹) + 1)⁻¹))

/-- The window parameter `τ'' = min(τ'(τ₂), τ₂/2)`. -/
private def ebTau'' (τ : ℝ) : ℝ := min (edgeTau' (ebTau τ)) (ebTau τ / 2)

private lemma eb_tau_facts {τ : ℝ} (hτ : 0 < τ) :
    0 < ebTau τ ∧ ebTau τ ≤ τ / 2 ∧ ebTau τ ≤ 1 / 6 ∧
      2 * τ⁻¹ * (1 + τ⁻¹) + 1 ≤ (ebTau τ)⁻¹ ∧
      0 < ebTau'' τ ∧ ebTau'' τ ≤ edgeTau' (ebTau τ) ∧ ebTau'' τ ≤ ebTau τ / 2 := by
  have hA : 0 < 2 * τ⁻¹ * (1 + τ⁻¹) + 1 := by positivity
  have h0 : 0 < ebTau τ := lt_min (half_pos hτ) (lt_min (by norm_num) (inv_pos.2 hA))
  have h3 : ebTau τ ≤ (2 * τ⁻¹ * (1 + τ⁻¹) + 1)⁻¹ :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨h0, min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _), ?_,
    lt_min (edgeTau'_pos h0) (half_pos h0), min_le_left _ _, min_le_right _ _⟩
  rw [le_inv_comm₀ hA h0]
  exact h3

private lemma eb_facts {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) :
    0 < N ∧ τ ≤ 1 ∧ (posVals σ).Nonempty := by
  have hτ := h.pos
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · exfalso
      have := h.phi_lower
      simp [phiRatio, h0] at this
      linarith
    · exact h0
  have hτ1 : τ ≤ 1 := by
    have h1 : τ ≤ τ⁻¹ := h.phi_lower.trans h.phi_upper
    by_contra hc
    exact absurd h1 (not_le.mpr ((inv_lt_one_of_one_lt₀ (not_le.mp hc)).trans (not_le.mp hc)))
  refine ⟨hN, hτ1, ?_⟩
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have hM : M ≠ 0 := by
    rintro rfl
    have := h.phi_lower
    simp [phiRatio] at this
    linarith
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

/-- At a window point `z = E + iη`, `η = N^{-2/3-9ε}`, `|E - a_k| ≤ 3N^{-2/3+ε}`: `z` lies in
`𝐃^e_k(τ₂, τ'', N)`, `Ψ(z) ≤ 2N^{-1/3+9ε}`, and `|z - a_k| ≤ 4N^{-2/3+ε} ≤ τ'₀`. -/
private lemma eb_window {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) :
    ∀ᶠ N : ℕ in atTop, ∀ (M : ℕ) (σ : Fin M → ℝ) (k : ℕ), DensityAssumptions τ N σ →
      RegularEdge τ N σ k → ∀ E : ℝ, |E - edgeVal N σ k| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) →
      ((E : ℂ) + etaE N ε * Complex.I) ∈ edgeDomain (ebTau τ) (ebTau'' τ) N σ k ∧
      Psi N σ ((E : ℂ) + etaE N ε * Complex.I) ≤ 2 * (N : ℝ) ^ (-1 / 3 + 9 * ε) ∧
      ‖(E : ℂ) + etaE N ε * Complex.I - edgeVal N σ k‖ ≤ 4 * (N : ℝ) ^ (-2 / 3 + ε) ∧
      4 * (N : ℝ) ^ (-2 / 3 + ε) ≤ edgeTau0 τ := by
  obtain ⟨hτ₂, hτ₂a, hτ₂b, hτ₂c, hτ'', hτ''a, hτ''b⟩ := eb_tau_facts hτ
  set τ₂ := ebTau τ with hτ₂def
  set τ'' := ebTau'' τ with hτ''def
  set S := sqUpper τ₂ with hSdef
  have ht0 : 0 < edgeTau0 τ := by
    have := edgeTau'_pos hτ
    unfold edgeTau' at this
    linarith
  filter_upwards [eventually_ge_atTop 1,
    eb_ev_small (y := -2 / 3 + ε) (by linarith) (by positivity : 0 < τ'' / 3),
    eb_ev_large (y := 17 * ε) (by positivity) (4 * S ^ 2),
    eb_ev_small (y := -2 / 3 + ε) (by linarith) (by positivity : 0 < edgeTau0 τ / 4)]
    with N hN1 hN2 hN3 hN4
  intro M σ k h hk E hE
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hn : (0 : ℝ) < N := by linarith
  set n : ℝ := (N : ℝ) with hndef
  set c : ℝ := n ^ (-2 / 3 + ε) with hcdef
  set η : ℝ := etaE N ε with hηdef
  have hηe : η = n ^ (-2 / 3 - 9 * ε) := rfl
  have hηpos : 0 < η := by rw [hηe]; exact Real.rpow_pos_of_pos hn _
  have hηc : η ≤ c := by
    rw [hηe]; exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hη1 : η ≤ 1 := by
    rw [hηe]; exact Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
  have hc0 : 0 < c := Real.rpow_pos_of_pos hn _
  obtain ⟨hN0, hτ1, hS⟩ := eb_facts h
  have ha := edgeVal_mem_Icc N σ h.nonneg hN0 hS hτ h.phi_lower h.phi_upper h.bound_Sigma
    hk.1 hk.2.1
  have haτ : τ ≤ edgeVal N σ k := hk.2.2.1
  set a := edgeVal N σ k with hadef
  obtain ⟨hE1, hE2⟩ := abs_le.1 hE
  have hre : ((E : ℂ) + η * Complex.I).re = E := by simp
  have him : ((E : ℂ) + η * Complex.I).im = η := by simp
  set z : ℂ := (E : ℂ) + η * Complex.I with hzdef
  have hτinv : 0 ≤ 2 * τ⁻¹ * (1 + τ⁻¹) := by positivity
  have hEpos : 0 ≤ E := by linarith [ha.1]
  have hdom : z ∈ edgeDomain τ₂ τ'' N σ k := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [him]; exact hηpos
    · refine le_trans ?_ (Complex.abs_re_le_norm z)
      rw [hre, abs_of_nonneg hEpos]
      linarith
    · rw [hre, abs_of_nonneg hEpos]
      linarith [ha.2]
    · rw [him, hηe]
      exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    · rw [him]; linarith
    · rw [hre]; linarith
    · rw [hre]; linarith
  have h2 : DensityAssumptions τ₂ N σ := h.mono hτ₂ (by linarith)
  have hk2 : RegularEdge τ₂ N σ k := regularEdge_mono hk (by linarith)
  have hκ := kappa_edgeDomain h2 hk2 hτ''b hdom
  have hsq := m_sq_root_edge h2 hk2 hτ''a hdom
  rw [hκ, hre, him] at hsq
  have hκη0 : 0 < |E - a| + η := by positivity
  have hsq0 : 0 < √(|E - a| + η) := Real.sqrt_pos.2 hκη0
  have hS0 : 0 ≤ S := by
    rw [hSdef, sqUpper]
    exact le_trans (div_nonneg (mBoundConst_pos hτ₂).le (Real.sqrt_nonneg _))
      (le_trans (le_max_right _ _) (le_max_left _ _))
  have hmim : (mFun N σ z).im ≤ S * √(|E - a| + η) := by
    by_cases hsup : z.re ∈ (varrho N σ).support
    · rw [hre] at hsup
      exact (hsq.1 hsup).2
    · rw [hre] at hsup
      refine (hsq.2 hsup).2.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hS0
      rw [div_le_iff₀ hsq0, Real.mul_self_sqrt hκη0.le]
      linarith [abs_nonneg (E - a)]
  have hκη : |E - a| + η ≤ 4 * c := by linarith
  have hm2 : (mFun N σ z).im ≤ S * √(4 * c) :=
    hmim.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hκη) hS0)
  set b : ℝ := -1 / 3 + 9 * ε with hbdef
  have hb0 : 0 < n ^ b := Real.rpow_pos_of_pos hn _
  have hbb : n ^ b * n ^ b = n ^ (-2 / 3 + 18 * ε) := by
    rw [← Real.rpow_add hn]; congr 1; rw [hbdef]; ring
  have hc17 : c * n ^ (17 * ε) = n ^ (-2 / 3 + 18 * ε) := by
    rw [hcdef, ← Real.rpow_add hn]; congr 1; ring
  have hmb : (mFun N σ z).im ≤ n ^ b := by
    refine hm2.trans ?_
    have hl : 0 ≤ S * √(4 * c) := by positivity
    rw [← sq_le_sq₀ hl hb0.le, mul_pow, Real.sq_sqrt (by positivity), sq (n ^ b), hbb, ← hc17]
    calc S ^ 2 * (4 * c) = c * (4 * S ^ 2) := by ring
      _ ≤ c * n ^ (17 * ε) := mul_le_mul_of_nonneg_left hN3 hc0.le
  have hNη : n * η = n ^ (1 / 3 - 9 * ε) := by
    rw [hηe]
    have e := Real.rpow_add hn 1 (-2 / 3 - 9 * ε)
    rw [Real.rpow_one] at e
    rw [← e]; congr 1; ring
  have hNη0 : 0 < n * η := by positivity
  have h1N : 1 / (n * η) = n ^ b := by
    rw [hNη, one_div, ← Real.rpow_neg hn.le]; congr 1; rw [hbdef]; ring
  have hbb' : n ^ b * n ^ b * (n * η) = n ^ b := by
    rw [hbb, hNη, ← Real.rpow_add hn]; congr 1; rw [hbdef]; ring
  have hsqrt : √((mFun N σ z).im / (n * η)) ≤ n ^ b := by
    rw [Real.sqrt_le_left hb0.le, div_le_iff₀ hNη0, sq, hbb']
    exact hmb
  refine ⟨hdom, ?_, ?_, ?_⟩
  · unfold Psi
    rw [him]
    linarith
  · have e : z - (a : ℂ) = ((E - a : ℝ) : ℂ) + η * Complex.I := by
      rw [hzdef]; push_cast; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hηpos]
    linarith
  · linarith

/-- The constant of (1+xm) on `𝐃^e_k(τ₂, τ'', N)`. -/
private def ebC (τ : ℝ) : ℝ := oneXmConst (edgeMz (ebTau τ)) (mBoundConst (ebTau τ))

private lemma eb_C_pos {τ : ℝ} (hτ : 0 < τ) : 0 < ebC τ := by
  obtain ⟨hτ₂, -⟩ := eb_tau_facts hτ
  have hC : 0 < mBoundConst (ebTau τ) := mBoundConst_pos hτ₂
  have hmz : 0 < edgeMz (ebTau τ) := lt_min (half_pos hτ₂) (div_pos (edgeTau'_pos hτ₂) hC)
  exact lt_min (by norm_num) (div_pos hmz (by linarith))

/-- At a window point: (1+xm) with constant `c(τ)` and `|m| ≤ C_m(τ₂)`. -/
private lemma eb_window_m {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) :
    ∀ᶠ N : ℕ in atTop, ∀ (M : ℕ) (σ : Fin M → ℝ) (k : ℕ), DensityAssumptions τ N σ →
      RegularEdge τ N σ k → ∀ E : ℝ, |E - edgeVal N σ k| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) →
      (∀ i, ebC τ ≤ ‖1 + (σ i : ℂ) * mFun N σ ((E : ℂ) + etaE N ε * Complex.I)‖) ∧
      ‖mFun N σ ((E : ℂ) + etaE N ε * Complex.I)‖ ≤ mBoundConst (ebTau τ) := by
  obtain ⟨hτ₂, hτ₂a, -, -, -, hτ''a, -⟩ := eb_tau_facts hτ
  filter_upwards [eb_window hτ hε hε1] with N hN
  intro M σ k h hk E hE
  have hdom := (hN M σ k h hk E hE).1
  have h2 : DensityAssumptions (ebTau τ) N σ := h.mono hτ₂ (by linarith)
  have hk2 : RegularEdge (ebTau τ) N σ k := regularEdge_mono hk (by linarith)
  exact ⟨one_add_mul_mFun_edge h2 hk2 hτ''a hdom, (gen_prop_m_specDomain h2 hdom.1).2.1⟩

/-- Deterministic bounds at the window points `z = E + iη` of a regular edge `k`, with
`η = N^{-2/3-9ε}` and `|E - a_k| ≤ 3N^{-2/3+ε}`: `Ψ(z) ≤ 2N^{-1/3+9ε}`, `|m(z)| ≤ K` and
`|Π_{st}(z)| ≤ K` for all `s, t ∈ 𝓘_M ⊔ 𝓘_N`, where `K` depends only on `τ` (Theorem 3.14 (i)
setting, (m_sq_root) and (1+xm)). -/
theorem entryBounds_det (τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (k : ℕ),
      Sig.PosDef → DensityAssumptions τ N (specOf Sig) → RegularEdge τ N (specOf Sig) k →
      ∀ E : ℝ, |E - edgeVal N (specOf Sig) k| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) →
        Psi N (specOf Sig) ((E : ℂ) + etaE N ε * Complex.I) ≤
            2 * (N : ℝ) ^ (-1 / 3 + 9 * ε) ∧
          ‖mFun N (specOf Sig) ((E : ℂ) + etaE N ε * Complex.I)‖ ≤ K ∧
          ∀ s t : Fin M ⊕ Fin N,
            ‖piMat Sig (mFun N (specOf Sig) ((E : ℂ) + etaE N ε * Complex.I)) s t‖ ≤ K := by
  obtain ⟨hτ₂, -⟩ := eb_tau_facts hτ
  have hc := eb_C_pos hτ
  have hCm := mBoundConst_pos hτ₂
  refine ⟨τ⁻¹ * (ebC τ)⁻¹ + mBoundConst (ebTau τ), by positivity, ?_⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 ((eb_window hτ hε hε1).and (eb_window_m hτ hε hε1))
  refine ⟨N₀, fun N hN M Sig k hSig h hk E hE => ?_⟩
  obtain ⟨hw1, hw2⟩ := hN₀ N hN
  obtain ⟨-, hPsi, -⟩ := hw1 M (specOf Sig) k h hk E hE
  obtain ⟨hOne, hm⟩ := hw2 M (specOf Sig) k h hk E hE
  refine ⟨hPsi, by linarith [mul_nonneg (inv_nonneg.2 hτ.le) (inv_nonneg.2 hc.le)], ?_⟩
  exact eb_piMat_le hSig (inv_nonneg.2 hτ.le) h.bound_Sigma hc hCm.le hOne hm

/-- `Ψ ≥ 0` for `Im z > 0`. -/
private lemma eb_Psi_nonneg {σ : Fin M → ℝ} {z : ℂ} (hz : 0 < z.im)
    (hN : 0 < N) : 0 ≤ Psi N σ z := by
  unfold Psi
  have : (0 : ℝ) < N := by exact_mod_cast hN
  positivity

/-- The anisotropic law at the window points, with the test vectors `Σ̲ x`, `Σ̲ y`. -/
private lemma eb_law (τ : ℝ) (C : ℕ → ℝ) (ε ε' D : ℝ) (hτ : 0 < τ) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 200) (hε' : 0 < ε') :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (k : ℕ),
      IsModel τ C M N Sig X → RegularEdge τ N (specOf Sig) k →
      ∀ E : ℝ, |E - edgeVal N (specOf Sig) k| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) →
      ∀ x y : Fin M ⊕ Fin N → ℝ, DomAt N ε' D
        (fun ω => ‖testBilin x (G Sig (X ω) ((E : ℂ) + etaE N ε * Complex.I) -
          piMat Sig (mFun N (specOf Sig) ((E : ℂ) + etaE N ε * Complex.I))) y‖)
        (fun _ => Psi N (specOf Sig) ((E : ℂ) + etaE N ε * Complex.I) *
          testNorm (ebR Sig *ᵥ x) * testNorm (ebR Sig *ᵥ y)) := by
  obtain ⟨hτ₂, hτ₂a, -, -, hτ'', hτ''a, -⟩ := eb_tau_facts hτ
  obtain ⟨N₁, h₁⟩ := edge_law (ebTau τ) (ebTau'' τ) C ε' D hτ₂ hτ'' hτ''a hε'
  obtain ⟨N₂, h₂⟩ := eventually_atTop.1 (eb_window hτ hε hε1)
  refine ⟨max N₁ N₂, fun N hN Ω _ _ M Sig X k hm hk E hE x y => ?_⟩
  have hm2 : IsModel (ebTau τ) C M N Sig X := hm.mono hτ₂ (by linarith)
  have hk2 : RegularEdge (ebTau τ) N (specOf Sig) k := regularEdge_mono hk (by linarith)
  have hlaw := (h₁ N (le_of_max_le_left hN) M Sig X k hm2 hk2).1
  have hda : DensityAssumptions τ N (specOf Sig) := hm.diagModel_specOf.densityAssumptions hτ
  have hdom := (h₂ N (le_of_max_le_right hN) M (specOf Sig) k hda hk E hE).1
  have h := hlaw _ hdom (ebR Sig *ᵥ x) (ebR Sig *ᵥ y)
  simp only [eb_testBilin_lawMat hm.sigma.posDef] at h
  exact h

/-- Entry bounds at the window points of a regular edge (Theorem 3.14 (i) with the test vectors
`Σ̲ e_s`, `Σ̲ e_t`, `|Σ̲ e_s| ≤ τ⁻¹`): at `z = E + iη`, `η = N^{-2/3-9ε}`,
`|E - a_k| ≤ 3N^{-2/3+ε}`, every entry satisfies `|G_{st}(z) - Π_{st}(z)| ≺ τ⁻² Ψ(z)`, at fixed `N`
with `N₀` uniform in the model, the edge `k`, the point `E` and the entry. -/
theorem entryBounds_entry (τ : ℝ) (C : ℕ → ℝ) (ε ε' D : ℝ) (hτ : 0 < τ) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 200) (hε' : 0 < ε') :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (k : ℕ),
      IsModel τ C M N Sig X → RegularEdge τ N (specOf Sig) k →
      ∀ E : ℝ, |E - edgeVal N (specOf Sig) k| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) →
      ∀ s t : Fin M ⊕ Fin N, DomAt N ε' D
        (fun ω => ‖G Sig (X ω) ((E : ℂ) + etaE N ε * Complex.I) s t -
          piMat Sig (mFun N (specOf Sig) ((E : ℂ) + etaE N ε * Complex.I)) s t‖)
        (fun _ => τ⁻¹ ^ 2 * Psi N (specOf Sig) ((E : ℂ) + etaE N ε * Complex.I)) := by
  obtain ⟨N₀, h₀⟩ := eb_law τ C ε ε' D hτ hε hε1 hε'
  refine ⟨max N₀ 1, fun N hN Ω _ _ M Sig X k hm hk E hE s t => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have h := h₀ N (le_of_max_le_left hN) M Sig X k hm hk E hE (Pi.single s 1) (Pi.single t 1)
  have hda : DensityAssumptions τ N (specOf Sig) := hm.diagModel_specOf.densityAssumptions hτ
  obtain ⟨-, hτ1, -⟩ := eb_facts hda
  have hSig := hm.sigma.posDef
  have hv := eb_testNorm_col_le (N := N) hSig hτ hτ1 hda.bound_Sigma s
  have hw := eb_testNorm_col_le (N := N) hSig hτ hτ1 hda.bound_Sigma t
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hz : 0 < ((E : ℂ) + etaE N ε * Complex.I).im := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_zero, zero_add, mul_one]
    rw [add_zero]
    exact Real.rpow_pos_of_pos hNr _
  have hP := eb_Psi_nonneg (σ := specOf Sig) hz hN1
  refine DomAt.mono hN1 (fun ω => le_of_eq ?_) (fun _ => ?_) (fun _ => by positivity) le_rfl
    le_rfl h
  · rw [eb_testBilin_single, Matrix.sub_apply]
  · have h0v : 0 ≤ testNorm (ebR (N := N) Sig *ᵥ Pi.single s 1) := Real.sqrt_nonneg _
    have h0w : 0 ≤ testNorm (ebR (N := N) Sig *ᵥ Pi.single t 1) := Real.sqrt_nonneg _
    calc Psi N (specOf Sig) ((E : ℂ) + etaE N ε * Complex.I) *
          testNorm (ebR (N := N) Sig *ᵥ Pi.single s 1) *
          testNorm (ebR (N := N) Sig *ᵥ Pi.single t 1)
        ≤ Psi N (specOf Sig) ((E : ℂ) + etaE N ε * Complex.I) * τ⁻¹ * τ⁻¹ := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hv hP) hw h0w
          exact mul_nonneg hP (inv_nonneg.2 hτ.le)
      _ = τ⁻¹ ^ 2 * Psi N (specOf Sig) ((E : ℂ) + etaE N ε * Complex.I) := by ring

/-- The bound on `⟨s, G e_i⟩` for a deterministic `s ∈ ℝ^{𝓘_N}` at the window points of a
regular edge: since `⟨s, Π e_i⟩ = 0`, `|∑_μ s_μ G_{μi}(z)| ≺ τ⁻¹ Ψ(z) |s|` (Theorem 3.14 (i)
with the test vectors `(0, s)` and `Σ̲ e_i`), at fixed `N` with `N₀` uniform in the model, the
edge `k`, the point `E`, the vector `s` and the index `i`. -/
theorem entryBounds_sG (τ : ℝ) (C : ℕ → ℝ) (ε ε' D : ℝ) (hτ : 0 < τ) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 200) (hε' : 0 < ε') :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (k : ℕ),
      IsModel τ C M N Sig X → RegularEdge τ N (specOf Sig) k →
      ∀ E : ℝ, |E - edgeVal N (specOf Sig) k| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) →
      ∀ (s : Fin N → ℝ) (i : Fin M), DomAt N ε' D
        (fun ω => ‖∑ μ, (s μ : ℂ) *
          G Sig (X ω) ((E : ℂ) + etaE N ε * Complex.I) (Sum.inr μ) (Sum.inl i)‖)
        (fun _ => τ⁻¹ * Psi N (specOf Sig) ((E : ℂ) + etaE N ε * Complex.I) * testNorm s) := by
  obtain ⟨N₀, h₀⟩ := eb_law τ C ε ε' D hτ hε hε1 hε'
  refine ⟨max N₀ 1, fun N hN Ω _ _ M Sig X k hm hk E hE s i => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have h := h₀ N (le_of_max_le_left hN) M Sig X k hm hk E hE (Sum.elim (0 : Fin M → ℝ) s)
    (Pi.single (Sum.inl i) 1)
  have hda : DensityAssumptions τ N (specOf Sig) := hm.diagModel_specOf.densityAssumptions hτ
  obtain ⟨-, hτ1, -⟩ := eb_facts hda
  have hSig := hm.sigma.posDef
  have hw := eb_testNorm_col_le (N := N) hSig hτ hτ1 hda.bound_Sigma (Sum.inl i)
  obtain ⟨hv1, hv2⟩ := eb_ebR_embN (N := N) Sig s
  rw [hv1, hv2] at h
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hz : 0 < ((E : ℂ) + etaE N ε * Complex.I).im := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_zero, zero_add, mul_one]
    rw [add_zero]
    exact Real.rpow_pos_of_pos hNr _
  have hP := eb_Psi_nonneg (σ := specOf Sig) hz hN1
  have h0s : 0 ≤ testNorm s := Real.sqrt_nonneg _
  refine DomAt.mono hN1 (fun ω => le_of_eq ?_) (fun _ => ?_) (fun _ => by positivity) le_rfl
    le_rfl h
  · rw [eb_testBilin_embN]
    congr 1
    refine Finset.sum_congr rfl fun μ _ => ?_
    simp [piMat]
  · calc Psi N (specOf Sig) ((E : ℂ) + etaE N ε * Complex.I) * testNorm s *
          testNorm (ebR (N := N) Sig *ᵥ Pi.single (Sum.inl i) 1)
        ≤ Psi N (specOf Sig) ((E : ℂ) + etaE N ε * Complex.I) * testNorm s * τ⁻¹ :=
          mul_le_mul_of_nonneg_left hw (mul_nonneg hP h0s)
      _ = τ⁻¹ * Psi N (specOf Sig) ((E : ℂ) + etaE N ε * Complex.I) * testNorm s := by ring

/-- A vector `s ∈ ℝ^{𝓘_N}` with entries bounded by `S` has `|s| ≤ S √N`. -/
theorem entryBounds_testNorm_le {S : ℝ} (s : Fin N → ℝ) (hs : ∀ μ, |s μ| ≤ S) :
    testNorm s ≤ S * √N := by
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · subst h0
    simp [testNorm]
  have hS : 0 ≤ S := (abs_nonneg _).trans (hs ⟨0, h0⟩)
  unfold testNorm
  have hsum : ∑ μ, s μ ^ 2 ≤ (N : ℝ) * S ^ 2 := by
    calc ∑ μ, s μ ^ 2 ≤ ∑ _μ : Fin N, S ^ 2 := by
          refine Finset.sum_le_sum fun μ _ => ?_
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hs μ) 2
      _ = (N : ℝ) * S ^ 2 := by simp
  calc √(∑ μ, s μ ^ 2) ≤ √((N : ℝ) * S ^ 2) := Real.sqrt_le_sqrt hsum
    _ = S * √N := by rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hS, mul_comm]

/-- On the event `|G_{ab} - Π_{ab}| ≤ δ ≤ 1` for `a, b ∈ {i, μ}`: `|G_{ab}| ≤ K + 1`,
`|G_{iμ}|, |G_{μi}| ≤ δ`, and `|G_{ii} G_{μμ} - m Π_{ii}| ≤ (2K + 1) δ`. -/
private lemma eb_consequences {G P : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ} {m : ℂ}
    {K δ : ℝ} (i : Fin M) (μ : Fin N) (hPK : ∀ s t, ‖P s t‖ ≤ K)
    (hP1 : P (Sum.inl i) (Sum.inr μ) = 0) (hP2 : P (Sum.inr μ) (Sum.inl i) = 0)
    (hP3 : P (Sum.inr μ) (Sum.inr μ) = m) (hδ1 : δ ≤ 1)
    (h : ∀ a ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
      ∀ b ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)), ‖G a b - P a b‖ ≤ δ) :
    (∀ a ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
      ∀ b ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
        ‖G a b - P a b‖ ≤ δ ∧ ‖G a b‖ ≤ K + 1) ∧
      ‖G (Sum.inl i) (Sum.inr μ)‖ ≤ δ ∧ ‖G (Sum.inr μ) (Sum.inl i)‖ ≤ δ ∧
      ‖G (Sum.inl i) (Sum.inl i) * G (Sum.inr μ) (Sum.inr μ) -
          m * P (Sum.inl i) (Sum.inl i)‖ ≤ (2 * K + 1) * δ := by
  have hiJ : (Sum.inl i : Fin M ⊕ Fin N) ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)) :=
    Set.mem_insert _ _
  have hμJ : (Sum.inr μ : Fin M ⊕ Fin N) ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)) :=
    Set.mem_insert_of_mem _ rfl
  have hGK : ∀ a ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
      ∀ b ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)), ‖G a b‖ ≤ K + 1 := by
    intro a ha b hb
    have e : G a b = P a b + (G a b - P a b) := by ring
    rw [e]
    exact (norm_add_le _ _).trans (by linarith [hPK a b, h a ha b hb])
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (h _ hiJ _ hiJ)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hPK (Sum.inl i) (Sum.inl i))
  refine ⟨fun a ha b hb => ⟨h a ha b hb, hGK a ha b hb⟩, ?_, ?_, ?_⟩
  · have := h _ hiJ _ hμJ
    rwa [hP1, sub_zero] at this
  · have := h _ hμJ _ hiJ
    rwa [hP2, sub_zero] at this
  · have e : G (Sum.inl i) (Sum.inl i) * G (Sum.inr μ) (Sum.inr μ) -
        m * P (Sum.inl i) (Sum.inl i) =
        (G (Sum.inl i) (Sum.inl i) - P (Sum.inl i) (Sum.inl i)) * G (Sum.inr μ) (Sum.inr μ) +
          P (Sum.inl i) (Sum.inl i) * (G (Sum.inr μ) (Sum.inr μ) - P (Sum.inr μ) (Sum.inr μ)) := by
      rw [hP3]; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h1 := mul_le_mul (h _ hiJ _ hiJ) (hGK _ hμJ _ hμJ) (norm_nonneg _) hδ0
    have h2 := mul_le_mul (hPK (Sum.inl i) (Sum.inl i)) (h _ hμJ _ hμJ) (norm_nonneg _) hK0
    calc _ ≤ δ * (K + 1) + K * δ := add_le_add h1 h2
      _ = (2 * K + 1) * δ := by ring

/-- The high-probability event at a window point `z = E + iη` of a regular edge and an entry
`(i, μ)`, `J = {i, μ}`, `δ = N^{ε'} τ⁻² Ψ(z)` with `ε' ≤ ε`: on an event of probability
`≥ 1 - N^{-D}`, `|G_{ab} - Π_{ab}| ≤ δ` and `|G_{ab}| ≤ K + 1` for `a, b ∈ J`,
`|G_{iμ}|, |G_{μi}| ≤ δ`, and `|G_{ii} G_{μμ} - m Π_{ii}| ≤ (2K + 1) δ`; here `δ ≤ 1`,
`K` depends only on `τ`, and `N₀` is uniform in the model, `k`, `E` and `(i, μ)`. -/
theorem entryBounds_event (τ : ℝ) (C : ℕ → ℝ) (ε ε' D : ℝ) (hτ : 0 < τ) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 200) (hε' : 0 < ε') (hε'ε : ε' ≤ ε) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (k : ℕ),
      IsModel τ C M N Sig X → RegularEdge τ N (specOf Sig) k →
      ∀ E : ℝ, |E - edgeVal N (specOf Sig) k| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) →
      ∀ (i : Fin M) (μ : Fin N),
        (N : ℝ) ^ ε' * (τ⁻¹ ^ 2 * Psi N (specOf Sig) ((E : ℂ) + etaE N ε * Complex.I)) ≤ 1 ∧
        HighProbAt N D {ω |
          (∀ a ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
            ∀ b ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
              ‖G Sig (X ω) ((E : ℂ) + etaE N ε * Complex.I) a b -
                  piMat Sig (mFun N (specOf Sig) ((E : ℂ) + etaE N ε * Complex.I)) a b‖ ≤
                (N : ℝ) ^ ε' * (τ⁻¹ ^ 2 * Psi N (specOf Sig) ((E : ℂ) + etaE N ε * Complex.I)) ∧
              ‖G Sig (X ω) ((E : ℂ) + etaE N ε * Complex.I) a b‖ ≤ K + 1) ∧
          ‖G Sig (X ω) ((E : ℂ) + etaE N ε * Complex.I) (Sum.inl i) (Sum.inr μ)‖ ≤
            (N : ℝ) ^ ε' * (τ⁻¹ ^ 2 * Psi N (specOf Sig) ((E : ℂ) + etaE N ε * Complex.I)) ∧
          ‖G Sig (X ω) ((E : ℂ) + etaE N ε * Complex.I) (Sum.inr μ) (Sum.inl i)‖ ≤
            (N : ℝ) ^ ε' * (τ⁻¹ ^ 2 * Psi N (specOf Sig) ((E : ℂ) + etaE N ε * Complex.I)) ∧
          ‖G Sig (X ω) ((E : ℂ) + etaE N ε * Complex.I) (Sum.inl i) (Sum.inl i) *
                G Sig (X ω) ((E : ℂ) + etaE N ε * Complex.I) (Sum.inr μ) (Sum.inr μ) -
              mFun N (specOf Sig) ((E : ℂ) + etaE N ε * Complex.I) *
                piMat (N := N) Sig (mFun N (specOf Sig) ((E : ℂ) + etaE N ε * Complex.I))
                  (Sum.inl i) (Sum.inl i)‖ ≤
            (2 * K + 1) *
              ((N : ℝ) ^ ε' * (τ⁻¹ ^ 2 *
                Psi N (specOf Sig) ((E : ℂ) + etaE N ε * Complex.I)))} := by
  obtain ⟨K, hK, N₁, hdet⟩ := entryBounds_det τ ε hτ hε hε1
  obtain ⟨N₂, hent⟩ := entryBounds_entry τ C ε ε' (D + 2) hτ hε hε1 hε'
  have hτ2 : 0 < (2 * τ⁻¹ ^ 2)⁻¹ := by positivity
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.1 (eb_ev_small (y := -1 / 3 + 10 * ε) (by linarith) hτ2)
  refine ⟨K, hK, max (max N₁ N₂) (max N₃ 2), fun N hN Ω _ _ M Sig X k hm hk E hE i μ => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_max_left _ _) (le_of_max_le_left hN)
  have hN2 : N₂ ≤ N := le_trans (le_max_right _ _) (le_of_max_le_left hN)
  have hN3 : N₃ ≤ N := le_trans (le_max_left _ _) (le_of_max_le_right hN)
  have hN4 : 2 ≤ N := le_trans (le_max_right _ _) (le_of_max_le_right hN)
  have hda : DensityAssumptions τ N (specOf Sig) := hm.diagModel_specOf.densityAssumptions hτ
  set z : ℂ := (E : ℂ) + etaE N ε * Complex.I with hzdef
  obtain ⟨hPsi, hmK, hPK⟩ := hdet N hN1 M Sig k hm.sigma.posDef hda hk E hE
  have hn2 : (2 : ℝ) ≤ N := by exact_mod_cast hN4
  have hn : (0 : ℝ) < N := by linarith
  have hn1 : (1 : ℝ) ≤ N := by linarith
  set δ : ℝ := (N : ℝ) ^ ε' * (τ⁻¹ ^ 2 * Psi N (specOf Sig) z) with hδdef
  have hδ1 : δ ≤ 1 := by
    have e1 : (N : ℝ) ^ ε' ≤ (N : ℝ) ^ ε := Real.rpow_le_rpow_of_exponent_le hn1 hε'ε
    have e2 : (N : ℝ) ^ ε * (N : ℝ) ^ (-1 / 3 + 9 * ε) = (N : ℝ) ^ (-1 / 3 + 10 * ε) := by
      rw [← Real.rpow_add hn]; congr 1; ring
    have e3 := hN₃ N hN3
    have hz : 0 < z.im := by
      rw [hzdef]
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, mul_zero, zero_add, mul_one, add_zero]
      exact Real.rpow_pos_of_pos hn _
    have hP0 : 0 ≤ Psi N (specOf Sig) z := eb_Psi_nonneg hz (by omega)
    have hτi : 0 ≤ τ⁻¹ ^ 2 := by positivity
    calc δ ≤ (N : ℝ) ^ ε * (τ⁻¹ ^ 2 * (2 * (N : ℝ) ^ (-1 / 3 + 9 * ε))) := by
          apply mul_le_mul e1 (mul_le_mul_of_nonneg_left hPsi hτi) (by positivity)
            (by positivity)
      _ = 2 * τ⁻¹ ^ 2 * ((N : ℝ) ^ ε * (N : ℝ) ^ (-1 / 3 + 9 * ε)) := by ring
      _ = 2 * τ⁻¹ ^ 2 * (N : ℝ) ^ (-1 / 3 + 10 * ε) := by rw [e2]
      _ ≤ 2 * τ⁻¹ ^ 2 * (2 * τ⁻¹ ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_left e3 (by positivity)
      _ = 1 := mul_inv_cancel₀ (by positivity)
  refine ⟨hδ1, ?_⟩
  have h1 := hent N hN2 M Sig X k hm hk E hE (Sum.inl i) (Sum.inl i)
  have h2 := hent N hN2 M Sig X k hm hk E hE (Sum.inl i) (Sum.inr μ)
  have h3 := hent N hN2 M Sig X k hm hk E hE (Sum.inr μ) (Sum.inl i)
  have h4 := hent N hN2 M Sig X k hm hk E hE (Sum.inr μ) (Sum.inr μ)
  unfold DomAt at h1 h2 h3 h4
  unfold HighProbAt
  set m := mFun N (specOf Sig) z with hmdef
  have hP1 : piMat (N := N) Sig m (Sum.inl i) (Sum.inr μ) = 0 := by simp [piMat]
  have hP2 : piMat (N := N) Sig m (Sum.inr μ) (Sum.inl i) = 0 := by simp [piMat]
  have hP3 : piMat (N := N) Sig m (Sum.inr μ) (Sum.inr μ) = m := by simp [piMat]
  have hsub : {ω | (∀ a ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
            ∀ b ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
              ‖G Sig (X ω) z a b - piMat (N := N) Sig m a b‖ ≤ δ ∧ ‖G Sig (X ω) z a b‖ ≤ K + 1) ∧
          ‖G Sig (X ω) z (Sum.inl i) (Sum.inr μ)‖ ≤ δ ∧
          ‖G Sig (X ω) z (Sum.inr μ) (Sum.inl i)‖ ≤ δ ∧
          ‖G Sig (X ω) z (Sum.inl i) (Sum.inl i) * G Sig (X ω) z (Sum.inr μ) (Sum.inr μ) -
              m * piMat (N := N) Sig m (Sum.inl i) (Sum.inl i)‖ ≤ (2 * K + 1) * δ}ᶜ ⊆
      {ω | (N : ℝ) ^ ε' * (τ⁻¹ ^ 2 * Psi N (specOf Sig) z) <
          ‖G Sig (X ω) z (Sum.inl i) (Sum.inl i) - piMat (N := N) Sig m (Sum.inl i) (Sum.inl i)‖} ∪
        {ω | (N : ℝ) ^ ε' * (τ⁻¹ ^ 2 * Psi N (specOf Sig) z) <
          ‖G Sig (X ω) z (Sum.inl i) (Sum.inr μ) - piMat (N := N) Sig m (Sum.inl i) (Sum.inr μ)‖} ∪
        {ω | (N : ℝ) ^ ε' * (τ⁻¹ ^ 2 * Psi N (specOf Sig) z) <
          ‖G Sig (X ω) z (Sum.inr μ) (Sum.inl i) - piMat (N := N) Sig m (Sum.inr μ) (Sum.inl i)‖} ∪
        {ω | (N : ℝ) ^ ε' * (τ⁻¹ ^ 2 * Psi N (specOf Sig) z) <
          ‖G Sig (X ω) z (Sum.inr μ) (Sum.inr μ) -
            piMat (N := N) Sig m (Sum.inr μ) (Sum.inr μ)‖} := by
    intro ω hω
    by_contra hc
    apply hω
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hc
    obtain ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩ := hc
    refine eb_consequences i μ hPK hP1 hP2 hP3 hδ1 ?_
    intro a ha b hb
    have hma : a = Sum.inl i ∨ a = Sum.inr μ := by simpa using ha
    have hmb : b = Sum.inl i ∨ b = Sum.inr μ := by simpa using hb
    rcases hma with rfl | rfl <;> rcases hmb with rfl | rfl
    · exact c1
    · exact c2
    · exact c3
    · exact c4
  have hx0 : (0 : ℝ) ≤ (N : ℝ) ^ (-(D + 2)) := Real.rpow_nonneg hn.le _
  refine (measure_mono hsub).trans ?_
  refine ((measure_union_le _ _).trans (add_le_add_left ((measure_union_le _ _).trans
    (add_le_add_left (measure_union_le _ _) _)) _)).trans ?_
  refine (add_le_add (add_le_add (add_le_add h1 h2) h3) h4).trans ?_
  rw [← ENNReal.ofReal_add hx0 hx0, ← ENNReal.ofReal_add (by positivity) hx0,
    ← ENNReal.ofReal_add (by positivity) hx0]
  apply ENNReal.ofReal_le_ofReal
  have e : (N : ℝ) ^ (-D) = (N : ℝ) ^ (-(D + 2)) * (N : ℝ) ^ (2 : ℝ) := by
    rw [← Real.rpow_add hn]; congr 1; ring
  rw [e, Real.rpow_two]
  have hsq : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hn2 2
    norm_num at this
    linarith
  calc (N : ℝ) ^ (-(D + 2)) + (N : ℝ) ^ (-(D + 2)) + (N : ℝ) ^ (-(D + 2)) +
        (N : ℝ) ^ (-(D + 2)) = (N : ℝ) ^ (-(D + 2)) * 4 := by ring
    _ ≤ (N : ℝ) ^ (-(D + 2)) * (N : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hsq hx0

/-- The `m`-difference at the window points of a regular edge (from (z-a_taylor)): for
`|E_j - a_k| ≤ 3N^{-2/3+ε}` and `z_j = E_j + iη`, `|m(z_1) - x_k| ≤ 4 c₂^{-1/2} N^{-1/3+ε/2}`,
`|m(z_2) - m(z_1)| ≤ 8 c₂^{-1/2} N^{-1/3+ε/2}`, and
`|m(z_2) Π_{ii}(z_2) - m(z_1) Π_{ii}(z_1)| ≤ K N^{-1/3+ε/2}` for every `i ∈ 𝓘_M`, with `K` depending
only on `τ`. -/
theorem entryBounds_mPi_window (τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (k : ℕ),
      Sig.PosDef → DensityAssumptions τ N (specOf Sig) → RegularEdge τ N (specOf Sig) k →
      ∀ E₁ E₂ : ℝ, |E₁ - edgeVal N (specOf Sig) k| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) →
        |E₂ - edgeVal N (specOf Sig) k| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) →
        ‖mFun N (specOf Sig) ((E₁ : ℂ) + etaE N ε * Complex.I) - xCrit N (specOf Sig) k‖ ≤
            4 / √(edgec2 τ) * (N : ℝ) ^ (-1 / 3 + ε / 2) ∧
          ‖mFun N (specOf Sig) ((E₂ : ℂ) + etaE N ε * Complex.I) -
              mFun N (specOf Sig) ((E₁ : ℂ) + etaE N ε * Complex.I)‖ ≤
            8 / √(edgec2 τ) * (N : ℝ) ^ (-1 / 3 + ε / 2) ∧
          ∀ i : Fin M,
            ‖mFun N (specOf Sig) ((E₂ : ℂ) + etaE N ε * Complex.I) *
                piMat (N := N) Sig (mFun N (specOf Sig) ((E₂ : ℂ) + etaE N ε * Complex.I))
                  (Sum.inl i) (Sum.inl i) -
              mFun N (specOf Sig) ((E₁ : ℂ) + etaE N ε * Complex.I) *
                piMat (N := N) Sig (mFun N (specOf Sig) ((E₁ : ℂ) + etaE N ε * Complex.I))
                  (Sum.inl i) (Sum.inl i)‖ ≤ K * (N : ℝ) ^ (-1 / 3 + ε / 2) := by
  have hc := eb_C_pos hτ
  have hc2 := edgec2_pos hτ
  have hsc2 : 0 < √(edgec2 τ) := Real.sqrt_pos.2 hc2
  refine ⟨τ⁻¹ * (ebC τ)⁻¹ ^ 2 * (8 / √(edgec2 τ)), by positivity, ?_⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1
    (((eb_window hτ hε hε1).and (eb_window_m hτ hε hε1)).and (eventually_ge_atTop 1))
  refine ⟨N₀, fun N hN M Sig k hSig h hk E₁ E₂ hE₁ hE₂ => ?_⟩
  obtain ⟨⟨hw1, hw2⟩, hN1⟩ := hN₀ N hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hn : (0 : ℝ) < N := by linarith
  set b : ℝ := -1 / 3 + ε / 2 with hbdef
  have hbb : (N : ℝ) ^ b * (N : ℝ) ^ b = (N : ℝ) ^ (-2 / 3 + ε) := by
    rw [← Real.rpow_add hn]; congr 1; rw [hbdef]; ring
  have hb0 : 0 < (N : ℝ) ^ b := Real.rpow_pos_of_pos hn _
  have hpt : ∀ E : ℝ, |E - edgeVal N (specOf Sig) k| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) →
      ‖mFun N (specOf Sig) ((E : ℂ) + etaE N ε * Complex.I) - xCrit N (specOf Sig) k‖ ≤
        4 / √(edgec2 τ) * (N : ℝ) ^ b := by
    intro E hE
    obtain ⟨hdom, -, hza, hza'⟩ := hw1 M (specOf Sig) k h hk E hE
    have hz : 0 < ((E : ℂ) + etaE N ε * Complex.I).im := hdom.1.1
    refine (entryBounds_mFun_sub_xCrit h hk hz (hza.trans hza')).trans ?_
    rw [Real.sqrt_le_left (by positivity), mul_pow, div_pow, Real.sq_sqrt hc2.le, sq ((N : ℝ) ^ b),
      hbb, div_le_iff₀ hc2]
    have e : (4 : ℝ) ^ 2 / edgec2 τ * (N : ℝ) ^ (-2 / 3 + ε) * edgec2 τ =
        16 * (N : ℝ) ^ (-2 / 3 + ε) := by
      field_simp; norm_num
    rw [e]
    linarith
  have hm1 := hpt E₁ hE₁
  have hm2 := hpt E₂ hE₂
  have hdiff : ‖mFun N (specOf Sig) ((E₂ : ℂ) + etaE N ε * Complex.I) -
      mFun N (specOf Sig) ((E₁ : ℂ) + etaE N ε * Complex.I)‖ ≤
      8 / √(edgec2 τ) * (N : ℝ) ^ b := by
    have e : mFun N (specOf Sig) ((E₂ : ℂ) + etaE N ε * Complex.I) -
        mFun N (specOf Sig) ((E₁ : ℂ) + etaE N ε * Complex.I) =
        (mFun N (specOf Sig) ((E₂ : ℂ) + etaE N ε * Complex.I) - xCrit N (specOf Sig) k) -
          (mFun N (specOf Sig) ((E₁ : ℂ) + etaE N ε * Complex.I) - xCrit N (specOf Sig) k) := by
      ring
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have e8 : 8 / √(edgec2 τ) * (N : ℝ) ^ b =
        4 / √(edgec2 τ) * (N : ℝ) ^ b + 4 / √(edgec2 τ) * (N : ℝ) ^ b := by ring
    rw [e8]
    exact add_le_add hm2 hm1
  refine ⟨hm1, hdiff, fun i => ?_⟩
  have hO1 := (hw2 M (specOf Sig) k h hk E₁ hE₁).1
  have hO2 := (hw2 M (specOf Sig) k h hk E₂ hE₂).1
  refine (eb_mPi_sub hSig (inv_nonneg.2 hτ.le) h.bound_Sigma hc hO1 hO2 i).trans ?_
  have hA : 0 ≤ τ⁻¹ * (ebC τ)⁻¹ ^ 2 := by positivity
  calc τ⁻¹ * (ebC τ)⁻¹ ^ 2 * ‖mFun N (specOf Sig) ((E₂ : ℂ) + etaE N ε * Complex.I) -
        mFun N (specOf Sig) ((E₁ : ℂ) + etaE N ε * Complex.I)‖
      ≤ τ⁻¹ * (ebC τ)⁻¹ ^ 2 * (8 / √(edgec2 τ) * (N : ℝ) ^ b) :=
        mul_le_mul_of_nonneg_left hdiff hA
    _ = τ⁻¹ * (ebC τ)⁻¹ ^ 2 * (8 / √(edgec2 τ)) * (N : ℝ) ^ b := by ring

/-! ## Compiled instances

The test-vector bound is instantiated at the vector `(1, …, 1)` of `ℝ^{2n}`. -/

section Instances

example (n : ℕ) : testNorm (fun _ : Fin (2 * n) => (1 : ℝ)) ≤ 1 * √((2 * n : ℕ) : ℝ) :=
  entryBounds_testNorm_le _ fun _ => by norm_num

end Instances

end Anisotropic

#print axioms Anisotropic.entryBounds_stability
#print axioms Anisotropic.entryBounds_stability_ref
#print axioms Anisotropic.entryBounds_mExt_sub_xCrit
#print axioms Anisotropic.entryBounds_mFun_sub_xCrit
#print axioms Anisotropic.entryBounds_det
#print axioms Anisotropic.entryBounds_entry
#print axioms Anisotropic.entryBounds_sG
#print axioms Anisotropic.entryBounds_testNorm_le
#print axioms Anisotropic.entryBounds_event
#print axioms Anisotropic.entryBounds_mPi_window
