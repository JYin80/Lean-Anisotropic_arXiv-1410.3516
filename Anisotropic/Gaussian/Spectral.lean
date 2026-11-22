module

public import Anisotropic.Gaussian.Ensemble
public import Anisotropic.LinAlg.Basic
public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.Framework.Domination
public import Anisotropic.Density.Stability.Domains

@[expose] public section

/-! Eigenvalue lists and the orthogonal diagonalization. -/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! # The eigenvalue list under rotation, the diagonalization, test vectors

`specOf` is invariant under orthogonal conjugation, a symmetric matrix is orthogonally
diagonalized by `Σ = U D Uᵀ` with `D = diag(specOf Σ)` ((def_D_Sigma)), Assumption 2.1 for `Σ`
gives Assumption 2.1 for `D`, and bilinear test forms are compatible with real rotations. -/

/-- The eigenvalue list is invariant under orthogonal conjugation, as a function. -/
theorem specOf_conj {K : ℕ} {O : Matrix (Fin K) (Fin K) ℝ}
    (hO : O ∈ Matrix.orthogonalGroup (Fin K) ℝ) (A : Matrix (Fin K) (Fin K) ℝ) :
    specOf (O * A * Oᵀ) = specOf A := by
  have h₁ : Oᵀ * O = 1 := (Matrix.mem_orthogonalGroup_iff' _ _).1 hO
  have h₂ : O * Oᵀ = 1 := (Matrix.mem_orthogonalGroup_iff _ _).1 hO
  have key : ∀ B : Matrix (Fin K) (Fin K) ℝ, Oᵀ * (O * B * Oᵀ) * O = B := by
    intro B
    rw [Matrix.mul_assoc O B, ← Matrix.mul_assoc Oᵀ O, h₁, Matrix.one_mul, Matrix.mul_assoc, h₁,
      Matrix.mul_one]
  have ht : ∀ B : Matrix (Fin K) (Fin K) ℝ, (O * B * Oᵀ)ᵀ = O * Bᵀ * Oᵀ := by
    intro B
    rw [transpose_mul, transpose_mul, transpose_transpose, Matrix.mul_assoc]
  have hiff : (O * A * Oᵀ).IsHermitian ↔ A.IsHermitian := by
    simp only [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial]
    constructor
    · intro h
      rw [ht] at h
      have := congrArg (fun B => Oᵀ * B * O) h
      simpa only [key] using this
    · intro h
      rw [ht, h]
  by_cases hA : A.IsHermitian
  · have hB : (O * A * Oᵀ).IsHermitian := hiff.2 hA
    simp only [specOf, dite_eq_left hA, dite_eq_left hB]
    rw [Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff, Matrix.charpoly_mul_comm,
      ← Matrix.mul_assoc, h₁, Matrix.one_mul]
  · have hB : ¬ (O * A * Oᵀ).IsHermitian := fun h => hA (hiff.1 h)
    simp only [specOf, dite_eq_right hA, dite_eq_right hB]

/-- `D(Σ) = diag(specOf Σ)` has the eigenvalue list of `Σ`. -/
theorem specOf_diagonal_specOf {K : ℕ} (A : Matrix (Fin K) (Fin K) ℝ) :
    specOf (diagonal (specOf A)) = specOf A := by
  have hD : ∀ v : Fin K → ℝ, (diagonal v).IsHermitian := fun v => isHermitian_diagonal v
  by_cases hA : A.IsHermitian
  · rw [show specOf A = hA.eigenvalues from dite_eq_left hA,
      show specOf (diagonal hA.eigenvalues) = (hD _).eigenvalues from dite_eq_left (hD _)]
    rw [Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff, hA.charpoly_eq, charpoly_diagonal]
    simp
  · rw [show specOf A = 0 from dite_eq_right hA,
      show specOf (diagonal (0 : Fin K → ℝ)) = (hD 0).eigenvalues from dite_eq_left (hD _)]
    exact (Matrix.IsHermitian.eigenvalues_eq_zero_iff (hD 0)).2 diagonal_zero

/-- (def_D_Sigma): `Σ = U D Uᵀ` with `U` orthogonal and `D = diag(specOf Σ)`. -/
theorem exists_orth_diag {K : ℕ} {A : Matrix (Fin K) (Fin K) ℝ} (hA : A.IsHermitian) :
    ∃ U ∈ Matrix.orthogonalGroup (Fin K) ℝ, Uᵀ * A * U = diagonal (specOf A) := by
  refine ⟨hA.eigenvectorUnitary, hA.eigenvectorUnitary.2, ?_⟩
  have h := hA.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_star_apply] at h
  rw [show specOf A = hA.eigenvalues from dite_eq_left hA]
  simpa [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using h

/-- Assumption 2.1 for `Σ` gives Assumption 2.1 for `D(Σ) = diag(specOf Σ)`. -/
theorem IsModel.diagModel_specOf {Ω : Type*} [MeasureSpace Ω] {τ : ℝ} {C : ℕ → ℝ} {N : ℕ}
    {Sig : Matrix (Fin M) (Fin M) ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ}
    (h : IsModel τ C M N Sig X) : DiagModel τ C M N (specOf Sig) X := by
  have hS := h.sigma
  have he : specOf Sig = hS.posDef.isHermitian.eigenvalues := dite_eq_left hS.posDef.isHermitian
  refine ⟨h.ratio_ge, h.ratio_le, h.entries, fun i => ?_, fun i => ?_, ?_⟩
  · rw [he]; exact hS.posDef.eigenvalues_pos i
  · rw [he]; exact hS.eigenvalues_le i
  · rw [he]; exact hS.gap

/-- Entries of `Qᵀ B Q` are bilinear forms of `B` at the rotated vectors. -/
theorem testBilin_conj {ι : Type*} [Fintype ι] (Q : Matrix ι ι ℝ) (B : Matrix ι ι ℂ)
    (v w : ι → ℝ) : testBilin v ((cplx Q)ᵀ * B * cplx Q) w = testBilin (Q *ᵥ v) B (Q *ᵥ w) := by
  have hc : ∀ u : ι → ℝ, cplx Q *ᵥ (fun t => (u t : ℂ)) = fun s => ((Q *ᵥ u) s : ℂ) := by
    intro u
    ext s
    simp [cplx, Matrix.mulVec, dotProduct]
  have hv : ∀ u : ι → ℝ, (fun s => (u s : ℂ)) ᵥ* (cplx Q)ᵀ = fun s => ((Q *ᵥ u) s : ℂ) := by
    intro u
    rw [Matrix.vecMul_transpose]
    exact hc u
  unfold testBilin
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hv, hc]

/-- Orthogonal maps preserve the Euclidean norm of a test vector. -/
theorem testNorm_orth {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι ℝ}
    (hQ : Q ∈ Matrix.orthogonalGroup ι ℝ) (v : ι → ℝ) : testNorm (Q *ᵥ v) = testNorm v := by
  have h₁ : Qᵀ * Q = 1 := (Matrix.mem_orthogonalGroup_iff' _ _).1 hQ
  unfold testNorm
  congr 1
  have h : (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v) = v ⬝ᵥ v := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, h₁,
      Matrix.one_mulVec]
  simpa [dotProduct, sq] using h

end Anisotropic
