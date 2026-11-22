module

public import Anisotropic.LinAlg.Basic

@[expose] public section

open Matrix ComplexOrder
set_option linter.unusedSectionVars false
namespace Anisotropic
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
open scoped Matrix.Norms.L2Operator
open Sum

/-- `Σ` and `Σ⁻¹` are mutually inverse after complexification. -/
private theorem blocks_cplx_mul_inv {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) :
    cplx Sig * cplx Sig⁻¹ = 1 ∧ cplx Sig⁻¹ * cplx Sig = 1 := by
  have hS : Sig * Sig⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hSig.isUnit)
  have hS' : Sig⁻¹ * Sig = 1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hSig.isUnit)
  refine ⟨?_, ?_⟩
  · rw [← Matrix.map_mul, hS, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [← Matrix.map_mul, hS', Matrix.map_one _ (map_zero _) (map_one _)]

/-- Block identity behind the first form of (G=G): with `S' S = 1` and
`(Y S X - z) G_N = 1`, the displayed block matrix is a right inverse of `fromBlocks (-S') X Y (-z)`. -/
private theorem blocks_first {S S' : Matrix m m ℂ} {X : Matrix m n ℂ} {Y : Matrix n m ℂ}
    {Gn : Matrix n n ℂ} {z : ℂ} (h1 : S' * S = 1)
    (h3 : (Y * S * X - z • 1) * Gn = 1) :
    fromBlocks (-S') X Y (-(z • (1 : Matrix n n ℂ))) *
      fromBlocks (S * X * Gn * Y * S - S) (S * X * Gn) (Gn * Y * S) Gn = 1 := by
  rw [fromBlocks_multiply, ← fromBlocks_one]
  congr 1
  · simp only [Matrix.neg_mul, Matrix.mul_sub, Matrix.mul_assoc]
    simp only [← Matrix.mul_assoc, h1]
    simp [Matrix.mul_assoc]
  · simp only [Matrix.neg_mul, Matrix.mul_assoc]
    simp only [← Matrix.mul_assoc, h1]
    simp
  · have : Y * (S * X * Gn * Y * S - S) + -(z • (1 : Matrix n n ℂ)) * (Gn * Y * S)
        = (Y * S * X - z • 1) * Gn * Y * S - Y * S := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.neg_mul,
        Matrix.smul_mul, Matrix.one_mul]
      abel
    rw [this, h3]; simp
  · have : Y * (S * X * Gn) + -(z • (1 : Matrix n n ℂ)) * Gn = (Y * S * X - z • 1) * Gn := by
      simp only [Matrix.sub_mul, Matrix.mul_assoc, Matrix.neg_mul, Matrix.smul_mul, Matrix.one_mul]
      abel
    rw [this, h3]

/-- Block identity behind the second form of (G=G): with `(-S' + z⁻¹ X Y) G_M = 1` and `z ≠ 0`,
the displayed block matrix is a right inverse of `fromBlocks (-S') X Y (-z)`. -/
private theorem blocks_second {S' : Matrix m m ℂ} {X : Matrix m n ℂ} {Y : Matrix n m ℂ}
    {Gm : Matrix m m ℂ} {z : ℂ} (hz : z ≠ 0) (h3 : (-S' + z⁻¹ • (X * Y)) * Gm = 1) :
    fromBlocks (-S') X Y (-(z • (1 : Matrix n n ℂ))) *
      fromBlocks Gm (z⁻¹ • (Gm * X)) (z⁻¹ • (Y * Gm))
        (z⁻¹ ^ 2 • (Y * Gm * X) - z⁻¹ • 1) = 1 := by
  rw [fromBlocks_multiply, ← fromBlocks_one]
  congr 1
  · have : -S' * Gm + X * (z⁻¹ • (Y * Gm)) = (-S' + z⁻¹ • (X * Y)) * Gm := by
      simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
    rw [this, h3]
  · have : -S' * (z⁻¹ • (Gm * X)) + X * (z⁻¹ ^ 2 • (Y * Gm * X) - z⁻¹ • 1)
        = z⁻¹ • ((-S' + z⁻¹ • (X * Y)) * Gm * X) - z⁻¹ • X := by
      simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc,
        Matrix.mul_sub, Matrix.neg_mul, smul_add, smul_smul, Matrix.mul_one, pow_two, smul_neg]
      abel
    rw [this, h3]; simp
  · have : Y * Gm + -(z • (1 : Matrix n n ℂ)) * (z⁻¹ • (Y * Gm)) = 0 := by
      simp [Matrix.smul_mul, smul_smul, hz]
    rw [this]
  · have : Y * (z⁻¹ • (Gm * X)) + -(z • (1 : Matrix n n ℂ)) * (z⁻¹ ^ 2 • (Y * Gm * X) - z⁻¹ • 1)
        = 1 := by
      simp only [Matrix.mul_sub, Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        smul_smul, Matrix.mul_assoc, smul_neg, neg_sub_neg]
      have e1 : z⁻¹ ^ 2 * z = z⁻¹ := by field_simp
      have e2 : z⁻¹ * z = 1 := by field_simp
      rw [e1, e2]; simp
    rw [this]

/-- Complexification is multiplicative. -/
private theorem blocks_cplx_mul {p q r : Type*} [Fintype q] (A : Matrix p q ℝ) (B : Matrix q r ℝ) :
    cplx (A * B) = cplx A * cplx B := by
  exact Matrix.map_mul (f := algebraMap ℝ ℂ)

/-- `(XᵀΣX - z) G_N = 1`, written with complexified factors. -/
private theorem blocks_GN_mul {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (X : Matrix m n ℝ) {z : ℂ}
    (hz : 0 < z.im) :
    (cplx Xᵀ * cplx Sig * cplx X - z • (1 : Matrix n n ℂ)) * GN Sig X z = 1 := by
  have h := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 (GN_isUnit hSig X hz))
  rw [blocks_cplx_mul, blocks_cplx_mul] at h
  have e : GN Sig X z = (cplx Xᵀ * cplx Sig * cplx X - z • (1 : Matrix n n ℂ))⁻¹ := by
    unfold GN; rw [blocks_cplx_mul, blocks_cplx_mul]
  rw [e]; exact h

/-- `(-Σ⁻¹ + z⁻¹ X Xᵀ) G_M = 1`, written with complexified factors. -/
private theorem blocks_GM_mul {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (X : Matrix m n ℝ) {z : ℂ}
    (hz : 0 < z.im) :
    (-cplx Sig⁻¹ + z⁻¹ • (cplx X * cplx Xᵀ)) * GM Sig X z = 1 := by
  have h := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 (GM_isUnit hSig X hz))
  rw [blocks_cplx_mul] at h
  have e : GM Sig X z = (-cplx Sig⁻¹ + z⁻¹ • (cplx X * cplx Xᵀ))⁻¹ := by
    unfold GM; rw [blocks_cplx_mul]
  rw [e]; exact h

/-- `H(z)` as an explicit block matrix. -/
private theorem blocks_H_eq (Sig : Matrix m m ℝ) (X : Matrix m n ℝ) (z : ℂ) :
    H Sig X z = fromBlocks (-cplx Sig⁻¹) (cplx X) (cplx Xᵀ) (-(z • (1 : Matrix n n ℂ))) := rfl

section L44
variable {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (X : Matrix m n ℝ) {z : ℂ} (hz : 0 < z.im)
include hSig hz

/-- (G=G), both forms. -/
theorem GeqG :
    G Sig X z = fromBlocks
      (cplx Sig * cplx X * GN Sig X z * cplx Xᵀ * cplx Sig - cplx Sig)
      (cplx Sig * cplx X * GN Sig X z) (GN Sig X z * cplx Xᵀ * cplx Sig) (GN Sig X z) ∧
    G Sig X z = fromBlocks (GM Sig X z) (z⁻¹ • (GM Sig X z * cplx X))
      (z⁻¹ • (cplx Xᵀ * GM Sig X z)) (z⁻¹ ^ 2 • (cplx Xᵀ * GM Sig X z * cplx X) - z⁻¹ • 1) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  refine ⟨?_, ?_⟩
  · rw [G_def]
    refine Matrix.inv_eq_right_inv ?_
    rw [blocks_H_eq]
    exact blocks_first (blocks_cplx_mul_inv hSig).2 (blocks_GN_mul hSig X hz)
  · rw [G_def]
    refine Matrix.inv_eq_right_inv ?_
    rw [blocks_H_eq]
    exact blocks_second hz0 (blocks_GM_mul hSig X hz)

end L44

/-- Second form of (defGM), without square roots: `G_M = z Σ (X Xᵀ Σ - z)⁻¹`. -/
theorem GM_eq {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (X : Matrix m n ℝ) {z : ℂ}
    (hz : 0 < z.im) :
    GM Sig X z = z • (cplx Sig * (cplx (X * Xᵀ * Sig) - z • 1)⁻¹) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  obtain ⟨hS, hS'⟩ := blocks_cplx_mul_inv hSig
  have hM := blocks_GM_mul hSig X hz
  have hW : cplx (X * Xᵀ * Sig) - z • (1 : Matrix m m ℂ)
      = z • ((-cplx Sig⁻¹ + z⁻¹ • (cplx X * cplx Xᵀ)) * cplx Sig) := by
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.neg_mul, hS', smul_add, smul_smul,
      mul_inv_cancel₀ hz0, one_smul, smul_neg, blocks_cplx_mul, Matrix.mul_assoc]
    abel
  have hinv : (cplx (X * Xᵀ * Sig) - z • (1 : Matrix m m ℂ))⁻¹
      = z⁻¹ • (cplx Sig⁻¹ * GM Sig X z) := by
    refine Matrix.inv_eq_right_inv ?_
    rw [hW]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hz0, one_smul,
      Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (cplx Sig), hS, Matrix.one_mul]
    exact hM
  rw [hinv]
  simp only [Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hz0, one_smul, ← Matrix.mul_assoc, hS,
    Matrix.one_mul]

/-- Complexification commutes with `fromBlocks`. -/
private theorem blocks_cplx_fromBlocks {p q r s : Type*} (A : Matrix p r ℝ) (B : Matrix p s ℝ)
    (C : Matrix q r ℝ) (D : Matrix q s ℝ) :
    cplx (fromBlocks A B C D) = fromBlocks (cplx A) (cplx B) (cplx C) (cplx D) :=
  fromBlocks_map _ _ _ _ _

/-- `cplx` of `Σ̲ = Σ ⊕ 1` as a block matrix. -/
private theorem blocks_cplx_SigU (Sig : Matrix m m ℝ) :
    cplx (SigU (n := n) Sig) = fromBlocks (cplx Sig) 0 0 1 := by
  rw [SigU, blocks_cplx_fromBlocks]
  congr 1
  simp [cplx]

/-- `cplx` of `J = [X; 1]` as a row-partitioned matrix. -/
private theorem blocks_cplx_Jmat (X : Matrix m n ℝ) :
    cplx (Jmat X) = fromRows (cplx X) 1 := by
  rw [Jmat, cplx, fromRows_map]
  congr 1
  simp

/-- `cplx` of `Jᵀ` as a column-partitioned matrix. -/
private theorem blocks_cplx_Jmat_transpose (X : Matrix m n ℝ) :
    cplx (Jmat X)ᵀ = fromCols (cplx Xᵀ) 1 := by
  rw [Jmat, transpose_fromRows, cplx, fromCols_map]
  congr 1
  simp

/-- (decompfullG) without the singular value decomposition, with the constant term `-(Σ ⊕ 0)`
in place of `-Σ̲`: `G = -(Σ ⊕ 0) + Σ̲ J G_N Jᵀ Σ̲`. -/
theorem decompfullG {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (X : Matrix m n ℝ) {z : ℂ}
    (hz : 0 < z.im) :
    G Sig X z = -cplx (fromBlocks Sig 0 0 (0 : Matrix n n ℝ))
      + cplx (SigU (n := n) Sig) * cplx (Jmat X) * GN Sig X z * cplx (Jmat X)ᵀ * cplx (SigU (n := n) Sig) := by
  rw [(GeqG hSig X hz).1, blocks_cplx_SigU, blocks_cplx_Jmat, blocks_cplx_Jmat_transpose,
    blocks_cplx_fromBlocks, fromBlocks_mul_fromRows, fromRows_mul, fromRows_mul_fromCols,
    fromBlocks_multiply]
  simp [fromBlocks_neg, fromBlocks_add]
  abel

/-! ### `∂_z G` -/

/-- `H(w) = H₀ - w P_N` with `H₀` independent of `w`. -/
private theorem blocks_H_affine (Sig : Matrix m m ℝ) (X : Matrix m n ℝ) (w : ℂ) :
    H Sig X w = fromBlocks (-cplx Sig⁻¹) (cplx X) (cplx Xᵀ) (0 : Matrix n n ℂ)
      + w • (-(PN : Matrix (m ⊕ n) (m ⊕ n) ℂ)) := by
  rw [blocks_H_eq, PN, fromBlocks_neg, fromBlocks_smul, fromBlocks_add]
  congr 1
  · simp
  · simp
  · simp
  · simp

/-- `∂_z G = G P_N G`, entrywise. -/
theorem hasDerivAt_G {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (X : Matrix m n ℝ) {z : ℂ}
    (hz : 0 < z.im) (s t : m ⊕ n) :
    HasDerivAt (fun w => G Sig X w s t) ((G Sig X z * (PN : Matrix (m ⊕ n) (m ⊕ n) ℂ) * G Sig X z) s t) z := by
  have hH : HasDerivAt (fun w => H Sig X w) (-(PN : Matrix (m ⊕ n) (m ⊕ n) ℂ)) z := by
    have h := ((hasDerivAt_id z).smul_const (-(PN : Matrix (m ⊕ n) (m ⊕ n) ℂ))).const_add
      (fromBlocks (-cplx Sig⁻¹) (cplx X) (cplx Xᵀ) (0 : Matrix n n ℂ))
    simp only [one_smul] at h
    convert h using 1
    funext w
    exact blocks_H_affine Sig X w
  have hu := H_isUnit hSig X hz
  have hR := hasFDerivAt_ringInverse (𝕜 := ℂ) hu.unit
  have hcomp := hR.comp_hasDerivAt z (by simpa using hH)
  have hinv : ((hu.unit⁻¹ : (Matrix (m ⊕ n) (m ⊕ n) ℂ)ˣ) : Matrix (m ⊕ n) (m ⊕ n) ℂ)
      = G Sig X z := by
    rw [← Ring.inverse_unit, hu.unit_spec, ← Matrix.nonsing_inv_eq_ringInverse, G_def]
  have hfun : (Ring.inverse ∘ fun w => H Sig X w) = fun w => G Sig X w := by
    funext w
    simp only [Function.comp_apply, G_def, Matrix.nonsing_inv_eq_ringInverse]
  rw [hfun] at hcomp
  have hval : (-((ContinuousLinearMap.mulLeftRight ℂ (Matrix (m ⊕ n) (m ⊕ n) ℂ))
      ((hu.unit⁻¹ : (Matrix (m ⊕ n) (m ⊕ n) ℂ)ˣ) : Matrix (m ⊕ n) (m ⊕ n) ℂ))
      ((hu.unit⁻¹ : (Matrix (m ⊕ n) (m ⊕ n) ℂ)ˣ) : Matrix (m ⊕ n) (m ⊕ n) ℂ))
      (-(PN : Matrix (m ⊕ n) (m ⊕ n) ℂ)) = G Sig X z * PN * G Sig X z := by
    simp [hinv]
  rw [hval] at hcomp
  let L : Matrix (m ⊕ n) (m ⊕ n) ℂ →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ s t)
  exact (L.hasFDerivAt.comp_hasDerivAt z hcomp)

end Anisotropic
