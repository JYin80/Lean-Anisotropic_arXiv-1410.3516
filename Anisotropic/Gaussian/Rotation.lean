import Anisotropic.LinAlg.Basic

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! # The rotation identity (deterministic) -/

/-- The real block matrix `diag(O_M, O_N)`. -/
def blockQ {N : ℕ} (OM : Matrix (Fin M) (Fin M) ℝ) (ON : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℝ :=
  fromBlocks OM 0 0 ON

/-- `Q = diag(O_M, O_N)` of (rotation of matrix), complexified. -/
def rotQ {N : ℕ} (OM : Matrix (Fin M) (Fin M) ℝ) (ON : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ :=
  cplx (blockQ OM ON)

theorem blockQ_mem {N : ℕ} {OM : Matrix (Fin M) (Fin M) ℝ} {ON : Matrix (Fin N) (Fin N) ℝ}
    (hOM : OM ∈ Matrix.orthogonalGroup (Fin M) ℝ) (hON : ON ∈ Matrix.orthogonalGroup (Fin N) ℝ) :
    blockQ OM ON ∈ Matrix.orthogonalGroup (Fin M ⊕ Fin N) ℝ := by
  have h₁ : OM * OMᵀ = 1 := (Matrix.mem_orthogonalGroup_iff _ _).1 hOM
  have h₂ : ON * ONᵀ = 1 := (Matrix.mem_orthogonalGroup_iff _ _).1 hON
  rw [Matrix.mem_orthogonalGroup_iff, blockQ, fromBlocks_transpose, fromBlocks_multiply]
  simp [h₁, h₂]

/-- `(O A Oᵀ)⁻¹ = O A⁻¹ Oᵀ` for orthogonal `O` (no invertibility hypothesis on `A`). -/
theorem inv_conj_orth {K : ℕ} {O : Matrix (Fin K) (Fin K) ℝ}
    (hO : O ∈ Matrix.orthogonalGroup (Fin K) ℝ) (A : Matrix (Fin K) (Fin K) ℝ) :
    (O * A * Oᵀ)⁻¹ = O * A⁻¹ * Oᵀ := by
  have hOi : O⁻¹ = Oᵀ := Matrix.inv_eq_right_inv ((Matrix.mem_orthogonalGroup_iff _ _).1 hO)
  have hOti : Oᵀ⁻¹ = O := Matrix.inv_eq_right_inv ((Matrix.mem_orthogonalGroup_iff' _ _).1 hO)
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hOi, hOti]
  exact (Matrix.mul_assoc _ _ _).symm

theorem cplx_mul {p q r : Type*} [Fintype q] (A : Matrix p q ℝ) (B : Matrix q r ℝ) :
    cplx (A * B) = cplx A * cplx B := Matrix.map_mul

theorem cplx_transpose {p q : Type*} (A : Matrix p q ℝ) : cplx Aᵀ = (cplx A)ᵀ :=
  transpose_map

theorem cplx_one {p : Type*} [DecidableEq p] : cplx (1 : Matrix p p ℝ) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem rotQ_eq {N : ℕ} (OM : Matrix (Fin M) (Fin M) ℝ) (ON : Matrix (Fin N) (Fin N) ℝ) :
    rotQ OM ON = fromBlocks (cplx OM) 0 0 (cplx ON) := by
  simp [rotQ, blockQ, cplx, fromBlocks_map]

/-- `Q H Qᵀ` is the linearization at `(O_M A O_Mᵀ, O_M X O_Nᵀ)`. -/
theorem linH_rotate {N : ℕ} {OM : Matrix (Fin M) (Fin M) ℝ} {ON : Matrix (Fin N) (Fin N) ℝ}
    (hON : ON ∈ Matrix.orthogonalGroup (Fin N) ℝ) (A : Matrix (Fin M) (Fin M) ℝ)
    (X : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) :
    rotQ OM ON * linH A X z * (rotQ OM ON)ᵀ = linH (OM * A * OMᵀ) (OM * X * ONᵀ) z := by
  have h₂ : ON * ONᵀ = 1 := (Matrix.mem_orthogonalGroup_iff _ _).1 hON
  have hc : cplx ON * (cplx ON)ᵀ = 1 := by
    rw [← cplx_transpose, ← cplx_mul, h₂, cplx_one]
  rw [rotQ_eq, linH, linH, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, transpose_zero]
  congr 1
  · rw [cplx_mul, cplx_mul, cplx_transpose, Matrix.mul_neg, Matrix.neg_mul]
  · rw [cplx_mul, cplx_mul, cplx_transpose]
  · rw [transpose_mul, transpose_mul, transpose_transpose, cplx_mul, cplx_mul, Matrix.mul_assoc,
      ← cplx_transpose OM]
  · rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hc]

/-- (rotation of matrix): `Q G^Σ(X) Qᵀ = G^{O_M Σ O_Mᵀ}(O_M X O_Nᵀ)`, for all `Σ, X, z`. -/
theorem G_rotate {N : ℕ} {OM : Matrix (Fin M) (Fin M) ℝ} {ON : Matrix (Fin N) (Fin N) ℝ}
    (hOM : OM ∈ Matrix.orthogonalGroup (Fin M) ℝ) (hON : ON ∈ Matrix.orthogonalGroup (Fin N) ℝ)
    (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) :
    rotQ OM ON * G Sig X z * (rotQ OM ON)ᵀ = G (OM * Sig * OMᵀ) (OM * X * ONᵀ) z := by
  have hQ : rotQ OM ON * (rotQ OM ON)ᵀ = 1 := by
    rw [rotQ, ← cplx_transpose, ← cplx_mul,
      (Matrix.mem_orthogonalGroup_iff _ _).1 (blockQ_mem hOM hON), cplx_one]
  have hQ' : (rotQ OM ON)ᵀ * rotQ OM ON = 1 := by
    rw [rotQ, ← cplx_transpose, ← cplx_mul,
      (Matrix.mem_orthogonalGroup_iff' _ _).1 (blockQ_mem hOM hON), cplx_one]
  have key : ∀ L : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ,
      (rotQ OM ON * L * (rotQ OM ON)ᵀ)⁻¹ = rotQ OM ON * L⁻¹ * (rotQ OM ON)ᵀ := by
    intro L
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.inv_eq_right_inv hQ,
      Matrix.inv_eq_right_inv hQ']
    exact (Matrix.mul_assoc _ _ _).symm
  rw [G, GA, G, GA, ← key, linH_rotate hON, inv_conj_orth hOM]

/-! ## Instances at `M = N = 2`, `O_M = O_N = 1` -/

example : blockQ (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ) ∈
    Matrix.orthogonalGroup (Fin 2 ⊕ Fin 2) ℝ :=
  blockQ_mem (Submonoid.one_mem _) (Submonoid.one_mem _)

example (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ((1 : Matrix (Fin 2) (Fin 2) ℝ) * A * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ)⁻¹ =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) * A⁻¹ * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ :=
  inv_conj_orth (Submonoid.one_mem _) A

example (A : Matrix (Fin 2) (Fin 2) ℝ) (X : Matrix (Fin 2) (Fin 2) ℝ) (z : ℂ) :
    rotQ (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ) * linH A X z *
        (rotQ (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ))ᵀ =
      linH ((1 : Matrix (Fin 2) (Fin 2) ℝ) * A * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ)
        ((1 : Matrix (Fin 2) (Fin 2) ℝ) * X * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ) z :=
  linH_rotate (Submonoid.one_mem _) A X z

example (Sig : Matrix (Fin 2) (Fin 2) ℝ) (X : Matrix (Fin 2) (Fin 2) ℝ) (z : ℂ) :
    rotQ (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ) * G Sig X z *
        (rotQ (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ))ᵀ =
      G ((1 : Matrix (Fin 2) (Fin 2) ℝ) * Sig * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ)
        ((1 : Matrix (Fin 2) (Fin 2) ℝ) * X * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ) z :=
  G_rotate (Submonoid.one_mem _) (Submonoid.one_mem _) Sig X z

end Anisotropic
