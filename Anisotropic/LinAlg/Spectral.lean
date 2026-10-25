import Anisotropic.LinAlg.Blocks

open Matrix ComplexOrder
set_option linter.unusedSectionVars false
namespace Anisotropic
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
open scoped Matrix.Norms.L2Operator
open Sum

/-! ### Spectral decompositions -/

/-- `Xᵀ Σ X` is symmetric for a symmetric real `Σ` (Section 4, (GN_spec)). -/
theorem XSX_isHermitian {Sig : Matrix m m ℝ} (hSig : Sig.IsHermitian) (X : Matrix m n ℝ) :
    (Xᵀ * Sig * X).IsHermitian := by
  have hT : Sigᵀ = Sig := by
    have h := hSig
    rwa [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] at h
  unfold Matrix.IsHermitian
  rw [conjTranspose_eq_transpose_of_trivial, transpose_mul, transpose_mul, transpose_transpose, hT,
    Matrix.mul_assoc]

/-- Completeness of a real orthonormal eigenbasis: `∑_k ζ_k ζ_kᵀ = 1`, entrywise. -/
private theorem spectral_sum_eig_mul {A : Matrix n n ℝ} (hA : A.IsHermitian) (μ ν : n) :
    ∑ k, (hA.eigenvectorBasis k).ofLp μ * (hA.eigenvectorBasis k).ofLp ν
      = (1 : Matrix n n ℝ) μ ν := by
  have h := congrFun (congrFun (Unitary.coe_mul_star_self hA.eigenvectorUnitary) μ) ν
  rw [Unitary.coe_star, Matrix.mul_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [star_apply, hA.eigenvectorUnitary_apply, hA.eigenvectorUnitary_apply, star_trivial]

/-- The resolvent of a real symmetric matrix as a sum over its eigenbasis. -/
private theorem spectral_resolvent {A : Matrix n n ℝ} (hA : A.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) :
    (cplx A - z • (1 : Matrix n n ℂ))⁻¹ = ∑ k, ((hA.eigenvalues k : ℂ) - z)⁻¹ •
      vecMulVec (cvec (hA.eigenvectorBasis k).ofLp) (cvec (hA.eigenvectorBasis k).ofLp) := by
  refine Matrix.inv_eq_right_inv ?_
  have hne : ∀ k, (hA.eigenvalues k : ℂ) - z ≠ 0 := fun k h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  have hev : ∀ k, (cplx A - z • (1 : Matrix n n ℂ)) *ᵥ cvec (hA.eigenvectorBasis k).ofLp
      = ((hA.eigenvalues k : ℂ) - z) • cvec (hA.eigenvectorBasis k).ofLp := by
    intro k
    funext μ
    have h := congrFun (hA.mulVec_eigenvectorBasis k) μ
    have h' := congrArg (algebraMap ℝ ℂ) h
    rw [RingHom.map_mulVec] at h'
    rw [sub_mulVec, Pi.sub_apply, smul_mulVec, one_mulVec]
    simp only [Pi.smul_apply, smul_eq_mul] at h' ⊢
    rw [show cvec (hA.eigenvectorBasis k).ofLp
      = ⇑(algebraMap ℝ ℂ) ∘ (hA.eigenvectorBasis k).ofLp from rfl, h']
    simp only [Complex.coe_algebraMap, Complex.ofReal_mul, Function.comp_apply]
    ring
  rw [Matrix.mul_sum]
  calc ∑ k, (cplx A - z • (1 : Matrix n n ℂ)) * (((hA.eigenvalues k : ℂ) - z)⁻¹ •
        vecMulVec (cvec (hA.eigenvectorBasis k).ofLp) (cvec (hA.eigenvectorBasis k).ofLp))
      = ∑ k, vecMulVec (cvec (hA.eigenvectorBasis k).ofLp) (cvec (hA.eigenvectorBasis k).ofLp) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Matrix.mul_smul, mul_vecMulVec, hev, smul_vecMulVec, smul_smul,
          inv_mul_cancel₀ (hne k), one_smul]
    _ = 1 := by
        ext μ ν
        simp only [Matrix.sum_apply, vecMulVec_apply, cvec]
        have h := congrArg (fun x : ℝ => (x : ℂ)) (spectral_sum_eig_mul hA μ ν)
        simp only [Complex.ofReal_sum, Complex.ofReal_mul] at h
        rw [h]
        by_cases hμν : μ = ν <;> simp [one_apply, hμν]

/-- (GN_spec), with `ζ_k`, `λ_k` the eigenvectors and eigenvalues of `Xᵀ Σ X`. -/
theorem GN_spec {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (X : Matrix m n ℝ) {z : ℂ}
    (hz : 0 < z.im) (μ ν : n) :
    GN Sig X z μ ν = ∑ k, (((XSX_isHermitian hSig.1 X).eigenvectorBasis k).ofLp μ
        * ((XSX_isHermitian hSig.1 X).eigenvectorBasis k).ofLp ν : ℝ)
        / (((XSX_isHermitian hSig.1 X).eigenvalues k : ℂ) - z) := by
  rw [GN, spectral_resolvent (XSX_isHermitian hSig.1 X) hz, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, div_eq_inv_mul, Complex.ofReal_mul]

/-- Complexification commutes with `*ᵥ`. -/
private theorem spectral_cvec_mulVec {p q : Type*} [Fintype q] (M : Matrix p q ℝ) (v : q → ℝ) :
    cvec (M *ᵥ v) = cplx M *ᵥ cvec v := by
  funext i
  exact RingHom.map_mulVec (algebraMap ℝ ℂ) M v i

/-- `Σ̲ = Σ ⊕ 1` is symmetric when `Σ` is. -/
private theorem spectral_SigU_transpose {Sig : Matrix m m ℝ} (hSig : Sig.IsHermitian) :
    (SigU (n := n) Sig)ᵀ = SigU (n := n) Sig := by
  have hT : Sigᵀ = Sig := by
    have h := hSig
    rwa [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] at h
  rw [SigU, fromBlocks_transpose, hT]
  simp

/-- (decompfullG) as a spectral sum, `u_k ↔ Σ̲ J ζ_k`. -/
theorem decompfullG_spec {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (X : Matrix m n ℝ) {z : ℂ}
    (hz : 0 < z.im) :
    G Sig X z = -cplx (fromBlocks Sig 0 0 (0 : Matrix n n ℝ))
      + ∑ k, (((XSX_isHermitian hSig.1 X).eigenvalues k : ℂ) - z)⁻¹ • vecMulVec
        (cvec (SigU (n := n) Sig *ᵥ Jmat X *ᵥ ((XSX_isHermitian hSig.1 X).eigenvectorBasis k).ofLp))
        (cvec (SigU (n := n) Sig *ᵥ Jmat X *ᵥ ((XSX_isHermitian hSig.1 X).eigenvectorBasis k).ofLp)) := by
  rw [decompfullG hSig X hz]
  congr 1
  have hGN : GN Sig X z = (cplx (Xᵀ * Sig * X) - z • (1 : Matrix n n ℂ))⁻¹ := rfl
  rw [hGN, spectral_resolvent (XSX_isHermitian hSig.1 X) hz]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec,
    vecMulVec_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  set w := ((XSX_isHermitian hSig.1 X).eigenvectorBasis k).ofLp
  have hl : (cplx (SigU (n := n) Sig) * cplx (Jmat X)) *ᵥ cvec w
      = cvec (SigU (n := n) Sig *ᵥ Jmat X *ᵥ w) := by
    rw [spectral_cvec_mulVec, spectral_cvec_mulVec, mulVec_mulVec]
  have hr : (cvec w ᵥ* cplx (Jmat X)ᵀ) ᵥ* cplx (SigU (n := n) Sig)
      = cvec (SigU (n := n) Sig *ᵥ Jmat X *ᵥ w) := by
    rw [← hl, vecMul_vecMul, ← vecMul_transpose, Matrix.transpose_mul]
    congr 2
    rw [cplx, ← transpose_map, spectral_SigU_transpose hSig.1]
  rw [hl, hr]

end Anisotropic

#print axioms Anisotropic.XSX_isHermitian
#print axioms Anisotropic.GN_spec
#print axioms Anisotropic.decompfullG_spec
