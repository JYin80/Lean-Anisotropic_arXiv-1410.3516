import Anisotropic.Gaussian.Rotation
import Anisotropic.Gaussian.Spectral
import Anisotropic.Entrywise.Defs

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! # Rotation of `Π`, `Σ̲`, `lawMat`, `m_N`; sign flips -/

/-- Inverse of a conjugate by a complex matrix `O` with `O Oᵀ = Oᵀ O = 1`. -/
private theorem inv_conj_complex {K : Type*} [Fintype K] [DecidableEq K]
    {O : Matrix K K ℂ} (h₁ : O * Oᵀ = 1) (h₂ : Oᵀ * O = 1) (A : Matrix K K ℂ) :
    (O * A * Oᵀ)⁻¹ = O * A⁻¹ * Oᵀ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.inv_eq_right_inv h₁,
    Matrix.inv_eq_right_inv h₂]
  exact (Matrix.mul_assoc _ _ _).symm

private theorem cplx_orth {K : Type*} [Fintype K] [DecidableEq K] {O : Matrix K K ℝ}
    (hO : O ∈ Matrix.orthogonalGroup K ℝ) :
    cplx O * (cplx O)ᵀ = 1 ∧ (cplx O)ᵀ * cplx O = 1 := by
  constructor
  · rw [← cplx_transpose, ← cplx_mul, (Matrix.mem_orthogonalGroup_iff _ _).1 hO, cplx_one]
  · rw [← cplx_transpose, ← cplx_mul, (Matrix.mem_orthogonalGroup_iff' _ _).1 hO, cplx_one]

private theorem rotQ_orth {N : ℕ} {OM : Matrix (Fin M) (Fin M) ℝ} {ON : Matrix (Fin N) (Fin N) ℝ}
    (hOM : OM ∈ Matrix.orthogonalGroup (Fin M) ℝ) (hON : ON ∈ Matrix.orthogonalGroup (Fin N) ℝ) :
    rotQ OM ON * (rotQ OM ON)ᵀ = 1 ∧ (rotQ OM ON)ᵀ * rotQ OM ON = 1 :=
  cplx_orth (blockQ_mem hOM hON)

/-- `Q Π^Σ(w) Qᵀ = Π^{O_M Σ O_Mᵀ}(w)` for every value `w` of `m`. -/
theorem piMat_rotate {N : ℕ} {OM : Matrix (Fin M) (Fin M) ℝ} {ON : Matrix (Fin N) (Fin N) ℝ}
    (hOM : OM ∈ Matrix.orthogonalGroup (Fin M) ℝ) (hON : ON ∈ Matrix.orthogonalGroup (Fin N) ℝ)
    (Sig : Matrix (Fin M) (Fin M) ℝ) (w : ℂ) :
    rotQ OM ON * piMat (N := N) Sig w * (rotQ OM ON)ᵀ = piMat (OM * Sig * OMᵀ) w := by
  obtain ⟨hM₁, hM₂⟩ := cplx_orth hOM
  obtain ⟨hN₁, hN₂⟩ := cplx_orth hON
  have e : cplx (OM * Sig * OMᵀ) = cplx OM * cplx Sig * (cplx OM)ᵀ := by
    rw [cplx_mul, cplx_mul, cplx_transpose]
  have h1 : (1 : Matrix (Fin M) (Fin M) ℂ) + w • (cplx OM * cplx Sig * (cplx OM)ᵀ) =
      cplx OM * (1 + w • cplx Sig) * (cplx OM)ᵀ := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hM₁, Matrix.mul_smul, Matrix.smul_mul]
  rw [rotQ_eq, piMat, piMat, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, transpose_zero]
  congr 1
  · rw [e, h1, inv_conj_complex hM₁ hM₂, Matrix.mul_neg, Matrix.neg_mul]
    congr 1
    calc cplx OM * (cplx Sig * (1 + w • cplx Sig)⁻¹) * (cplx OM)ᵀ
        = cplx OM * cplx Sig * 1 * (1 + w • cplx Sig)⁻¹ * (cplx OM)ᵀ := by
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = cplx OM * cplx Sig * ((cplx OM)ᵀ * cplx OM) * (1 + w • cplx Sig)⁻¹ * (cplx OM)ᵀ := by
          rw [hM₂]
      _ = _ := by simp only [Matrix.mul_assoc]
  · rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hN₁]

/-- `Q Σ̲ Qᵀ` is `Σ̲` of `O_M Σ O_Mᵀ`. -/
theorem ulSigma_rotate {N : ℕ} {OM : Matrix (Fin M) (Fin M) ℝ} {ON : Matrix (Fin N) (Fin N) ℝ}
    (hON : ON ∈ Matrix.orthogonalGroup (Fin N) ℝ) (Sig : Matrix (Fin M) (Fin M) ℝ) :
    rotQ OM ON * ulSigma N Sig * (rotQ OM ON)ᵀ = ulSigma N (OM * Sig * OMᵀ) := by
  obtain ⟨hN₁, -⟩ := cplx_orth hON
  have e : cplx (OM * Sig * OMᵀ) = cplx OM * cplx Sig * (cplx OM)ᵀ := by
    rw [cplx_mul, cplx_mul, cplx_transpose]
  rw [rotQ_eq, ulSigma, ulSigma, fromBlocks_transpose, fromBlocks_multiply,
    fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, transpose_zero,
    Matrix.mul_one, hN₁]
  rw [← cplx, ← cplx, e]

/-- `Q Σ̲⁻¹(G − Π)Σ̲⁻¹ Qᵀ` is the same matrix for `(O_M Σ O_Mᵀ, O_M X O_Nᵀ)`. -/
theorem lawMat_rotate {N : ℕ} {OM : Matrix (Fin M) (Fin M) ℝ} {ON : Matrix (Fin N) (Fin N) ℝ}
    (hOM : OM ∈ Matrix.orthogonalGroup (Fin M) ℝ) (hON : ON ∈ Matrix.orthogonalGroup (Fin N) ℝ)
    (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) :
    rotQ OM ON * lawMat Sig X z * (rotQ OM ON)ᵀ = lawMat (OM * Sig * OMᵀ) (OM * X * ONᵀ) z :=
  by
  obtain ⟨hQ, hQ'⟩ := rotQ_orth hOM hON
  have split : ∀ A B C : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ,
      rotQ OM ON * (A * B * C) * (rotQ OM ON)ᵀ =
        (rotQ OM ON * A * (rotQ OM ON)ᵀ) * (rotQ OM ON * B * (rotQ OM ON)ᵀ) *
          (rotQ OM ON * C * (rotQ OM ON)ᵀ) := by
    intro A B C
    calc rotQ OM ON * (A * B * C) * (rotQ OM ON)ᵀ
        = rotQ OM ON * A * ((rotQ OM ON)ᵀ * rotQ OM ON) * B * ((rotQ OM ON)ᵀ * rotQ OM ON) * C *
            (rotQ OM ON)ᵀ := by
          rw [hQ', Matrix.mul_one, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  have key : ∀ L : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ,
      (rotQ OM ON * L * (rotQ OM ON)ᵀ)⁻¹ = rotQ OM ON * L⁻¹ * (rotQ OM ON)ᵀ :=
    fun L => inv_conj_complex hQ hQ' L
  unfold lawMat
  rw [specOf_conj hOM, ← ulSigma_rotate hON, ← G_rotate hOM hON, ← piMat_rotate hOM hON, key,
    split, Matrix.mul_sub, Matrix.sub_mul]

/-- `m_N` is the same for `(Σ, X)` and `(O_M Σ O_Mᵀ, O_M X O_Nᵀ)`. -/
theorem mN_rotate {N : ℕ} {OM : Matrix (Fin M) (Fin M) ℝ} {ON : Matrix (Fin N) (Fin N) ℝ}
    (hOM : OM ∈ Matrix.orthogonalGroup (Fin M) ℝ) (hON : ON ∈ Matrix.orthogonalGroup (Fin N) ℝ)
    (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) :
    mN (OM * Sig * OMᵀ) (OM * X * ONᵀ) z = mN Sig X z := by
  obtain ⟨hN₁, hN₂⟩ := cplx_orth hON
  have blk : ∀ L : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ,
      (rotQ OM ON * L * (rotQ OM ON)ᵀ).toBlocks₂₂ = cplx ON * L.toBlocks₂₂ * (cplx ON)ᵀ := by
    intro L
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks L, rotQ_eq, fromBlocks_transpose,
      fromBlocks_multiply, fromBlocks_multiply]
    simp [Matrix.toBlocks_fromBlocks₂₂]
  unfold mN
  rw [← G_rotate hOM hON]
  congr 1
  have : ∑ μ, (rotQ OM ON * G Sig X z * (rotQ OM ON)ᵀ) (Sum.inr μ) (Sum.inr μ) =
      Matrix.trace (rotQ OM ON * G Sig X z * (rotQ OM ON)ᵀ).toBlocks₂₂ := rfl
  rw [this, blk, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hN₂, Matrix.one_mul]
  rfl

/-- `diag(±1)` with `-1` exactly on `S`. -/
def signMat {K : ℕ} (S : Finset (Fin K)) : Matrix (Fin K) (Fin K) ℝ :=
  diagonal fun i => if i ∈ S then -1 else 1

theorem signMat_mem {K : ℕ} (S : Finset (Fin K)) :
    signMat S ∈ Matrix.orthogonalGroup (Fin K) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff, signMat, diagonal_transpose, diagonal_mul_diagonal,
    ← diagonal_one]
  congr 1
  funext i
  split_ifs <;> norm_num

/-- The signs `ε_s` of the joint flip `diag(R_M, R_N)`. -/
def signVec {N : ℕ} (SM : Finset (Fin M)) (SN : Finset (Fin N)) : Fin M ⊕ Fin N → ℝ :=
  Sum.elim (fun i => if i ∈ SM then -1 else 1) fun μ => if μ ∈ SN then -1 else 1

/-- Under `X ↦ R_M X R_N`, the entry `B_{st}` of `Σ̲⁻¹(G − Π)Σ̲⁻¹`, `Σ = diag(σ)`, becomes
`ε_s ε_t B_{st}`. -/
theorem lawMat_signFlip {N : ℕ} (σ : Fin M → ℝ) (SM : Finset (Fin M)) (SN : Finset (Fin N))
    (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (s t : Fin M ⊕ Fin N) :
    lawMat (diagonal σ) (signMat SM * Xm * (signMat SN)ᵀ) z s t =
      signVec SM SN s * signVec SM SN t * lawMat (diagonal σ) Xm z s t := by
  have hd : signMat SM * diagonal σ * (signMat SM)ᵀ = diagonal σ := by
    rw [signMat, diagonal_transpose, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    split_ifs <;> ring
  have hQ : rotQ (signMat SM) (signMat SN) = diagonal fun s => ((signVec SM SN s : ℝ) : ℂ) := by
    have c : ∀ {K : ℕ} (S : Finset (Fin K)), cplx (signMat S) =
        diagonal fun i => ((if i ∈ S then -1 else 1 : ℝ) : ℂ) := by
      intro K S
      ext i j
      by_cases h : i = j <;> simp [signMat, h]
    rw [rotQ_eq, c, c, fromBlocks_diagonal]
    congr 1
    funext s
    cases s <;> simp [signVec]
  have := lawMat_rotate (signMat_mem SM) (signMat_mem SN) (diagonal σ) Xm z
  rw [hd, hQ, diagonal_transpose] at this
  rw [← this, mul_diagonal, diagonal_mul]
  ring

/-- `lawMat_signFlip` at `M = N = 2`, `σ ≡ 1`, `S_M = {0}`, `S_N = ∅`, `X` the all-ones matrix,
`z = i`, `(s, t) = (inl 0, inr 0)`. -/
example :
    lawMat (diagonal fun _ : Fin 2 => (1 : ℝ))
        (signMat ({0} : Finset (Fin 2)) * (Matrix.of fun _ _ : Fin 2 => (1 : ℝ)) *
          (signMat (∅ : Finset (Fin 2)))ᵀ) Complex.I (Sum.inl 0) (Sum.inr 0) =
      signVec ({0} : Finset (Fin 2)) (∅ : Finset (Fin 2)) (Sum.inl 0) *
        signVec ({0} : Finset (Fin 2)) (∅ : Finset (Fin 2)) (Sum.inr 0) *
        lawMat (diagonal fun _ : Fin 2 => (1 : ℝ)) (Matrix.of fun _ _ : Fin 2 => (1 : ℝ))
          Complex.I (Sum.inl 0) (Sum.inr 0) :=
  lawMat_signFlip _ _ _ _ _ _ _

/-- The sign `ε_s ε_t` of the flipped entry in the example above is `-1`. -/
example : signVec ({0} : Finset (Fin 2)) (∅ : Finset (Fin 2)) (Sum.inl 0) *
    signVec ({0} : Finset (Fin 2)) (∅ : Finset (Fin 2)) (Sum.inr 0) = -1 := by
  simp [signVec]

#print axioms Anisotropic.piMat_rotate
#print axioms Anisotropic.ulSigma_rotate
#print axioms Anisotropic.lawMat_rotate
#print axioms Anisotropic.mN_rotate
#print axioms Anisotropic.signMat
#print axioms Anisotropic.signMat_mem
#print axioms Anisotropic.signVec
#print axioms Anisotropic.lawMat_signFlip

end Anisotropic
