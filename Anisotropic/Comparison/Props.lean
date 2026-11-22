module

public import Anisotropic.Comparison.Ensemble
public import Anisotropic.Comparison.Notation
public import Anisotropic.Comparison.Ladder
public import Anisotropic.Framework.DominationMoment
public import Anisotropic.LinAlg.OpBound
public import Anisotropic.Gaussian.Spectral

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # (A_m), (C_m); Lemma 7.3; the Markov reduction; constants; Lemma 7.8 -/

/-! ## Bilinear forms of `G`, `Σ̲⁻¹` and `Π` at `v̄` -/

/-- `(SigU Σ)⁻¹ = diag(Σ⁻¹, 1)`. -/
private theorem props_SigU_inv {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) :
    (SigU (n := Fin N) Sig)⁻¹ = fromBlocks Sig⁻¹ 0 0 1 := by
  have hS : Sig * Sig⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hSig.isUnit)
  apply Matrix.inv_eq_right_inv
  rw [SigU, fromBlocks_multiply]
  simp [hS, fromBlocks_one]

private theorem props_SigU_inv_mul {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) :
    (SigU (n := Fin N) Sig)⁻¹ * SigU (n := Fin N) Sig = 1 := by
  have hS : Sig⁻¹ * Sig = 1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hSig.isUnit)
  rw [props_SigU_inv hSig, SigU, fromBlocks_multiply]
  simp [hS, fromBlocks_one]

private theorem props_SigU_inv_transpose {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) :
    ((SigU (n := Fin N) Sig)⁻¹)ᵀ = (SigU (n := Fin N) Sig)⁻¹ := by
  have hS : Sigᵀ = Sig := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact hSig.1.eq
  rw [props_SigU_inv hSig, fromBlocks_transpose, transpose_nonsing_inv, hS]
  simp

private theorem props_SigU_inv_mulVec {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (v : Fin M ⊕ Fin N → ℝ) : (SigU (n := Fin N) Sig)⁻¹ *ᵥ v = vbar Sig v := by
  rw [props_SigU_inv hSig]
  funext s
  rcases s with i | j
  · simp [vbar, fromBlocks_mulVec]
  · simp [vbar, fromBlocks_mulVec]

private theorem props_ent_add {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (v w : ι → ℝ) :
    ent (A + B) v w = ent A v w + ent B v w := by
  simp [ent, add_mulVec, dotProduct_add]

private theorem props_ent_sub {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (v w : ι → ℝ) :
    ent (A - B) v w = ent A v w - ent B v w := by
  simp [ent, sub_mulVec, dotProduct_sub]

private theorem props_ent_cplx {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (v w : ι → ℝ) :
    ent (cplx A) v w = ((v ⬝ᵥ A *ᵥ w : ℝ) : ℂ) := by
  simp [ent, cplx, dotProduct, mulVec, Complex.ofReal_sum, Complex.ofReal_mul]

/-- `Σ̲⁻¹(G + Σ̲)Σ̲⁻¹` tested at `v` is `G_{v̄v̄} + ⟨v, Σ̲⁻¹ v⟩`. -/
private theorem props_ent_K {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (v : Fin M ⊕ Fin N → ℝ) :
    ent (cplx (SigU (n := Fin N) Sig)⁻¹ * (G Sig A z + cplx (SigU (n := Fin N) Sig)) *
        cplx (SigU (n := Fin N) Sig)⁻¹) v v =
      ent (G Sig A z) (vbar Sig v) (vbar Sig v) +
        ((v ⬝ᵥ (SigU (n := Fin N) Sig)⁻¹ *ᵥ v : ℝ) : ℂ) := by
  set B := (SigU (n := Fin N) Sig)⁻¹ with hB
  have hBSB : B * SigU (n := Fin N) Sig * B = B := by
    rw [props_SigU_inv_mul hSig, Matrix.one_mul]
  have e : cplx B * (G Sig A z + cplx (SigU (n := Fin N) Sig)) * cplx B =
      (cplx B)ᵀ * G Sig A z * cplx B + cplx B := by
    rw [Matrix.mul_add, Matrix.add_mul, ← transpose_map, props_SigU_inv_transpose hSig]
    congr 1
    rw [cplx, cplx, ← Matrix.map_mul, ← Matrix.map_mul, hBSB]
  rw [e, props_ent_add, props_ent_cplx]
  congr 1
  change testBilin v ((cplx B)ᵀ * G Sig A z * cplx B) v = _
  rw [testBilin_conj, hB, props_SigU_inv_mulVec hSig]
  rfl

private theorem props_sqrt_dot (v : Fin M ⊕ Fin N → ℝ) : Real.sqrt (v ⬝ᵥ v) = testNorm v := by
  unfold testNorm
  congr 1
  simp [dotProduct, sq]

/-- `Im G_{v̄v̄} ≤ ((1 + ‖XᵀX‖)/η + 1)|v|²`. -/
private theorem props_ImGvv_le {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (v : Fin M ⊕ Fin N → ℝ) :
    ImGvv Sig A z v ≤ ((1 + ‖Aᵀ * A‖) / z.im + 1) * testNorm v * testNorm v := by
  have h := opnorm_G hSig A hz v v
  rw [props_ent_K hSig, props_sqrt_dot] at h
  unfold ImGvv
  have h2 := Complex.im_le_norm (ent (G Sig A z) (vbar Sig v) (vbar Sig v) +
    ((v ⬝ᵥ (SigU (n := Fin N) Sig)⁻¹ *ᵥ v : ℝ) : ℂ))
  simp only [Complex.add_im, Complex.ofReal_im, add_zero] at h2
  linarith

/-! ## Eigenbasis coordinates of `Π_{v̄v̄}` and `⟨v, Σ̲⁻¹ v⟩` -/

/-- `Σ = U diag(σ) Uᵀ` with `U` orthogonal and `σ = specOf Σ > 0`. -/
private theorem props_diag {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) :
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

private theorem props_inv_eq {Sig U : Matrix (Fin M) (Fin M) ℝ} {σ : Fin M → ℝ}
    (h₂ : U * Uᵀ = 1) (h₁ : Uᵀ * U = 1) (hS : Sig = U * diagonal σ * Uᵀ)
    (hσ : ∀ i, σ i ≠ 0) : Sig⁻¹ = U * diagonal (fun i => (σ i)⁻¹) * Uᵀ := by
  apply Matrix.inv_eq_right_inv
  rw [hS]
  have hd : diagonal σ * diagonal (fun i => (σ i)⁻¹) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hσ i)
  calc U * diagonal σ * Uᵀ * (U * diagonal (fun i => (σ i)⁻¹) * Uᵀ)
      = U * (diagonal σ * (Uᵀ * U) * diagonal (fun i => (σ i)⁻¹)) * Uᵀ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h₁, Matrix.mul_one, hd, Matrix.mul_one, h₂]

/-- `(1 + w Σ)⁻¹ = U diag((1 + σᵢ w)⁻¹) Uᵀ` when every `1 + σᵢ w ≠ 0`. -/
private theorem props_cinv_eq {Sig U : Matrix (Fin M) (Fin M) ℝ} {σ : Fin M → ℝ}
    (h₂ : U * Uᵀ = 1) (h₁ : Uᵀ * U = 1) (hS : Sig = U * diagonal σ * Uᵀ) {w : ℂ}
    (hw : ∀ i, 1 + (σ i : ℂ) * w ≠ 0) :
    (1 + w • cplx Sig)⁻¹ =
      (cplx Uᵀ)ᵀ * diagonal (fun i => (1 + (σ i : ℂ) * w)⁻¹) * cplx Uᵀ := by
  have c₁ : cplx Uᵀ * (cplx Uᵀ)ᵀ = 1 := by
    simp only [cplx]
    rw [← transpose_map, transpose_transpose, ← Matrix.map_mul, h₁,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have c₂ : (cplx Uᵀ)ᵀ * cplx Uᵀ = 1 := by
    simp only [cplx]
    rw [← transpose_map, transpose_transpose, ← Matrix.map_mul, h₂,
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


private theorem props_cplx_eq {Sig U : Matrix (Fin M) (Fin M) ℝ} {σ : Fin M → ℝ}
    (hS : Sig = U * diagonal σ * Uᵀ) :
    cplx Sig = (cplx Uᵀ)ᵀ * diagonal (fun i => (σ i : ℂ)) * cplx Uᵀ := by
  simp only [cplx]
  rw [hS, ← transpose_map, transpose_transpose, Matrix.map_mul, Matrix.map_mul,
    diagonal_map (map_zero _)]
  rfl

/-- The block `−Σ(1 + wΣ)⁻¹` of `Π` in the eigenbasis. -/
private theorem props_piBlock_eq {Sig U : Matrix (Fin M) (Fin M) ℝ} {σ : Fin M → ℝ}
    (h₂ : U * Uᵀ = 1) (h₁ : Uᵀ * U = 1) (hS : Sig = U * diagonal σ * Uᵀ) {w : ℂ}
    (hw : ∀ i, 1 + (σ i : ℂ) * w ≠ 0) :
    -(cplx Sig * (1 + w • cplx Sig)⁻¹) =
      (cplx Uᵀ)ᵀ * diagonal (fun i => -((σ i : ℂ) * (1 + (σ i : ℂ) * w)⁻¹)) * cplx Uᵀ := by
  have c₁ : cplx Uᵀ * (cplx Uᵀ)ᵀ = 1 := by
    simp only [cplx]
    rw [← transpose_map, transpose_transpose, ← Matrix.map_mul, h₁,
      Matrix.map_one _ (map_zero _) (map_one _)]
  rw [props_cinv_eq h₂ h₁ hS hw, props_cplx_eq hS]
  calc -((cplx Uᵀ)ᵀ * diagonal (fun i => (σ i : ℂ)) * cplx Uᵀ *
        ((cplx Uᵀ)ᵀ * diagonal (fun i => (1 + (σ i : ℂ) * w)⁻¹) * cplx Uᵀ))
      = -((cplx Uᵀ)ᵀ * (diagonal (fun i => (σ i : ℂ)) * (cplx Uᵀ * (cplx Uᵀ)ᵀ) *
          diagonal (fun i => (1 + (σ i : ℂ) * w)⁻¹)) * cplx Uᵀ) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [c₁, Matrix.mul_one, diagonal_mul_diagonal, ← Matrix.neg_mul, ← Matrix.mul_neg,
          ← diagonal_neg]

/-- `⟨x, Qᵀ diag(d) Q x⟩ = ∑ᵢ (Qx)ᵢ² dᵢ` for real `x`. -/
private theorem props_testBilin_diag (Q : Matrix (Fin M) (Fin M) ℝ) (d : Fin M → ℂ)
    (x : Fin M → ℝ) :
    testBilin x ((cplx Q)ᵀ * diagonal d * cplx Q) x =
      ∑ i, ((((Q *ᵥ x) i : ℝ)) : ℂ) ^ 2 * d i := by
  rw [testBilin_conj]
  simp only [testBilin, mulVec_diagonal, dotProduct]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `⟨a, diag(A, B) b⟩ = ⟨a_M, A b_M⟩ + ⟨a_N, B b_N⟩`. -/
private theorem props_ent_blocks (A : Matrix (Fin M) (Fin M) ℂ) (B : Matrix (Fin N) (Fin N) ℂ)
    (a b : Fin M ⊕ Fin N → ℝ) :
    ent (fromBlocks A 0 0 B) a b = ent A (a ∘ Sum.inl) (b ∘ Sum.inl) +
      ent B (a ∘ Sum.inr) (b ∘ Sum.inr) := by
  simp only [ent, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, zero_mulVec, add_zero, zero_add]
  rfl

/-- `Uᵀ Σ⁻¹ x = diag(σ⁻¹) Uᵀ x`. -/
private theorem props_UT_inv {Sig U : Matrix (Fin M) (Fin M) ℝ} {σ : Fin M → ℝ}
    (h₂ : U * Uᵀ = 1) (h₁ : Uᵀ * U = 1) (hS : Sig = U * diagonal σ * Uᵀ)
    (hσ : ∀ i, σ i ≠ 0) (x : Fin M → ℝ) (i : Fin M) :
    (Uᵀ *ᵥ (Sig⁻¹ *ᵥ x)) i = (σ i)⁻¹ * (Uᵀ *ᵥ x) i := by
  rw [props_inv_eq h₂ h₁ hS hσ, mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h₁,
    Matrix.one_mul, ← mulVec_mulVec, mulVec_diagonal]

/-- `Π_{v̄v̄}` in the eigenbasis of `Σ`: `∑ᵢ (σᵢ⁻¹uᵢ)² (−σᵢ/(1 + σᵢw)) + w |v_N|²`,
`u = Uᵀ v_M`. -/
private theorem props_Pi_coord {Sig U : Matrix (Fin M) (Fin M) ℝ} {σ : Fin M → ℝ}
    (h₂ : U * Uᵀ = 1) (h₁ : Uᵀ * U = 1) (hS : Sig = U * diagonal σ * Uᵀ)
    (hσ : ∀ i, σ i ≠ 0) {w : ℂ} (hw : ∀ i, 1 + (σ i : ℂ) * w ≠ 0)
    (v : Fin M ⊕ Fin N → ℝ) :
    ent (piMat (N := N) Sig w) (vbar Sig v) (vbar Sig v) =
      ∑ i, ((((σ i)⁻¹ * (Uᵀ *ᵥ (v ∘ Sum.inl)) i : ℝ)) : ℂ) ^ 2 *
          (-((σ i : ℂ) * (1 + (σ i : ℂ) * w)⁻¹)) +
        w * ∑ μ, ((v (Sum.inr μ) : ℝ) : ℂ) ^ 2 := by
  rw [piMat, props_ent_blocks, props_piBlock_eq h₂ h₁ hS hw]
  have hM : (vbar Sig v) ∘ Sum.inl = Sig⁻¹ *ᵥ (v ∘ Sum.inl) := rfl
  have hN : (vbar (N := N) Sig v) ∘ Sum.inr = v ∘ Sum.inr := rfl
  rw [hM, hN]
  congr 1
  · change testBilin _ _ _ = _
    rw [props_testBilin_diag]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [props_UT_inv h₂ h₁ hS hσ]
  · simp only [ent, smul_mulVec, one_mulVec, dotProduct, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun μ _ => by simp only [cvec, Function.comp_apply]; ring

/-- `⟨v, Σ̲⁻¹ v⟩ = ∑ᵢ uᵢ² σᵢ⁻¹ + |v_N|²`, `u = Uᵀ v_M`. -/
private theorem props_Q_coord {Sig U : Matrix (Fin M) (Fin M) ℝ} {σ : Fin M → ℝ}
    (hSig : Sig.PosDef) (h₂ : U * Uᵀ = 1) (h₁ : Uᵀ * U = 1) (hS : Sig = U * diagonal σ * Uᵀ)
    (hσ : ∀ i, σ i ≠ 0) (v : Fin M ⊕ Fin N → ℝ) :
    v ⬝ᵥ (SigU (n := Fin N) Sig)⁻¹ *ᵥ v =
      ∑ i, (Uᵀ *ᵥ (v ∘ Sum.inl)) i ^ 2 * (σ i)⁻¹ + ∑ μ, v (Sum.inr μ) ^ 2 := by
  rw [props_SigU_inv hSig, fromBlocks_mulVec]
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, zero_mulVec,
    add_zero, zero_add, one_mulVec]
  congr 1
  · have e : (v ∘ Sum.inl) ⬝ᵥ Sig⁻¹ *ᵥ (v ∘ Sum.inl) =
        (Uᵀ *ᵥ (v ∘ Sum.inl)) ⬝ᵥ diagonal (fun i => (σ i)⁻¹) *ᵥ (Uᵀ *ᵥ (v ∘ Sum.inl)) := by
      rw [props_inv_eq h₂ h₁ hS hσ, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec,
        ← mulVec_transpose]
    simp only [dotProduct] at e
    refine e.trans ?_
    simp only [mulVec_diagonal]
    exact Finset.sum_congr rfl fun i _ => by ring
  · exact Finset.sum_congr rfl fun μ _ => by simp [sq]

/-- `|Uᵀ x| = |x|` for orthogonal `U`. -/
private theorem props_sum_sq_UT {U : Matrix (Fin M) (Fin M) ℝ} (h₂ : U * Uᵀ = 1)
    (x : Fin M → ℝ) : ∑ i, (Uᵀ *ᵥ x) i ^ 2 = ∑ i, x i ^ 2 := by
  have e : (Uᵀ *ᵥ x) ⬝ᵥ (Uᵀ *ᵥ x) = x ⬝ᵥ x := by
    rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, h₂, one_mulVec, dotProduct_comm]
  simpa [dotProduct, sq] using e


/-! ## Deterministic bounds on `Im Π_{v̄v̄}` and `F_v` -/

/-- One eigen-coordinate of `Im Π_{v̄v̄}`: `Im(−σ⁻¹ s² (1 + σw)⁻¹) = s² Im w / |1 + σw|²`. -/
private theorem props_term_im {σ s c : ℝ} {w : ℂ} (hσ : 0 < σ) (hc : 0 < c)
    (hw : 0 ≤ w.im) (h : c ≤ ‖1 + (σ : ℂ) * w‖) :
    (((((σ⁻¹ * s : ℝ)) : ℂ)) ^ 2 * (-((σ : ℂ) * (1 + (σ : ℂ) * w)⁻¹))).im ≤
      c⁻¹ ^ 2 * w.im * s ^ 2 := by
  set a : ℂ := 1 + (σ : ℂ) * w with ha
  have hapos : 0 < ‖a‖ := hc.trans_le h
  have e : ((((σ⁻¹ * s : ℝ)) : ℂ)) ^ 2 * (-((σ : ℂ) * a⁻¹)) =
      ((-((σ⁻¹ * s) ^ 2 * σ) : ℝ) : ℂ) * a⁻¹ := by
    push_cast; ring
  have him : a.im = σ * w.im := by simp [ha]
  rw [e, Complex.im_ofReal_mul, Complex.inv_im, him, Complex.normSq_eq_norm_sq]
  have e2 : -((σ⁻¹ * s) ^ 2 * σ) * (-(σ * w.im) / ‖a‖ ^ 2) = s ^ 2 * w.im / ‖a‖ ^ 2 := by
    field_simp
  rw [e2, div_le_iff₀ (by positivity)]
  have hca : c ^ 2 ≤ ‖a‖ ^ 2 := pow_le_pow_left₀ hc.le h 2
  have hs : 0 ≤ s ^ 2 * w.im := mul_nonneg (sq_nonneg _) hw
  calc s ^ 2 * w.im = c⁻¹ ^ 2 * w.im * s ^ 2 * c ^ 2 := by field_simp
    _ ≤ c⁻¹ ^ 2 * w.im * s ^ 2 * ‖a‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hca (by positivity)

/-- One eigen-coordinate of `Π_{v̄v̄} + ⟨v, Σ̲⁻¹v⟩`: `s² w / (1 + σw)`. -/
private theorem props_term_norm {σ s c : ℝ} {w : ℂ} (hσ : 0 < σ) (hc : 0 < c)
    (h : c ≤ ‖1 + (σ : ℂ) * w‖) :
    ‖((((σ⁻¹ * s : ℝ)) : ℂ)) ^ 2 * (-((σ : ℂ) * (1 + (σ : ℂ) * w)⁻¹)) +
        (((s ^ 2 * σ⁻¹ : ℝ)) : ℂ)‖ ≤ s ^ 2 * (‖w‖ * c⁻¹) := by
  set a : ℂ := 1 + (σ : ℂ) * w with ha
  have hapos : 0 < ‖a‖ := hc.trans_le h
  have ha0 : a ≠ 0 := norm_pos_iff.1 hapos
  have hσ0 : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  have e : ((((σ⁻¹ * s : ℝ)) : ℂ)) ^ 2 * (-((σ : ℂ) * a⁻¹)) + (((s ^ 2 * σ⁻¹ : ℝ)) : ℂ) =
      (((s ^ 2 : ℝ)) : ℂ) * (w * a⁻¹) := by
    have hw : w = (a - 1) / σ := by rw [ha]; field_simp; ring
    rw [hw]
    push_cast
    field_simp
    ring
  rw [e, norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) (sq_nonneg _)
  exact inv_anti₀ hc h

private theorem props_sum_norm (v : Fin M ⊕ Fin N → ℝ) (hv : testNorm v = 1) :
    ∑ i, v (Sum.inl i) ^ 2 + ∑ μ, v (Sum.inr μ) ^ 2 = 1 := by
  unfold testNorm at hv
  rw [Real.sqrt_eq_one, Fintype.sum_sum_type] at hv
  exact hv

/-- `Im Π_{v̄v̄} ≤ max(c⁻², 1) Im m` for `|v| = 1` under (1+xm). -/
private theorem props_ImPi_le {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {c : ℝ}
    (hc : 0 < c) {z : ℂ} (hz : 0 < z.im)
    (hOne : ∀ i, c ≤ ‖1 + (specOf Sig i : ℂ) * mFun N (specOf Sig) z‖)
    (v : Fin M ⊕ Fin N → ℝ) (hv : testNorm v = 1) :
    (ent (PiZ N Sig z) (vbar Sig v) (vbar Sig v)).im ≤
      max (c⁻¹ ^ 2) 1 * (mFun N (specOf Sig) z).im := by
  obtain ⟨U, h₂, h₁, hS, hσ⟩ := props_diag hSig
  set σ := specOf Sig with hσdef
  set w := mFun N σ z with hwdef
  have hwim : 0 < w.im := (mFun_spec N σ (fun i => (hσ i).le) hz).1
  have hw0 : ∀ i, 1 + (σ i : ℂ) * w ≠ 0 := fun i h0 => by
    have := hOne i
    rw [h0, norm_zero] at this
    linarith
  have hP := props_Pi_coord (N := N) h₂ h₁ hS (fun i => (hσ i).ne') hw0 v
  have hUT := props_sum_sq_UT h₂ (v ∘ Sum.inl)
  simp only [Function.comp_apply] at hUT
  have hsum : ∑ i, (Uᵀ *ᵥ (v ∘ Sum.inl)) i ^ 2 + ∑ μ, v (Sum.inr μ) ^ 2 = 1 := by
    rw [hUT]; exact props_sum_norm v hv
  change (ent (piMat (N := N) Sig w) (vbar Sig v) (vbar Sig v)).im ≤ _
  rw [hP, Complex.add_im, Complex.im_sum]
  have hN : (w * ∑ μ, ((v (Sum.inr μ) : ℝ) : ℂ) ^ 2).im = w.im * ∑ μ, v (Sum.inr μ) ^ 2 := by
    have e : (∑ μ, ((v (Sum.inr μ) : ℝ) : ℂ) ^ 2) = (((∑ μ, v (Sum.inr μ) ^ 2 : ℝ)) : ℂ) := by
      push_cast; rfl
    rw [e, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re]
    ring
  rw [hN]
  have hK : c⁻¹ ^ 2 ≤ max (c⁻¹ ^ 2) 1 := le_max_left _ _
  have hK1 : 1 ≤ max (c⁻¹ ^ 2) 1 := le_max_right _ _
  have h1 : ∑ i, (((((σ i)⁻¹ * (Uᵀ *ᵥ (v ∘ Sum.inl)) i : ℝ)) : ℂ) ^ 2 *
        (-((σ i : ℂ) * (1 + (σ i : ℂ) * w)⁻¹))).im ≤
      ∑ i, max (c⁻¹ ^ 2) 1 * w.im * (Uᵀ *ᵥ (v ∘ Sum.inl)) i ^ 2 := by
    refine Finset.sum_le_sum fun i _ => (props_term_im (hσ i) hc hwim.le (hOne i)).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK hwim.le) (sq_nonneg _)
  have h2 : w.im * ∑ μ, v (Sum.inr μ) ^ 2 ≤
      max (c⁻¹ ^ 2) 1 * w.im * ∑ μ, v (Sum.inr μ) ^ 2 := by
    have : 0 ≤ ∑ μ, v (Sum.inr μ) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hK1) hwim.le) this]
  calc _ ≤ ∑ i, max (c⁻¹ ^ 2) 1 * w.im * (Uᵀ *ᵥ (v ∘ Sum.inl)) i ^ 2 +
        max (c⁻¹ ^ 2) 1 * w.im * ∑ μ, v (Sum.inr μ) ^ 2 := add_le_add h1 h2
    _ = max (c⁻¹ ^ 2) 1 * w.im * (∑ i, (Uᵀ *ᵥ (v ∘ Sum.inl)) i ^ 2 +
        ∑ μ, v (Sum.inr μ) ^ 2) := by rw [← Finset.mul_sum]; ring
    _ = _ := by rw [hsum, mul_one]

/-- `|Π_{v̄v̄} + ⟨v, Σ̲⁻¹v⟩| ≤ |m| c⁻¹ + 1 + |m|` for `|v| = 1` under (1+xm). -/
private theorem props_PQ_le {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {c : ℝ}
    (hc : 0 < c) {z : ℂ}
    (hOne : ∀ i, c ≤ ‖1 + (specOf Sig i : ℂ) * mFun N (specOf Sig) z‖)
    (v : Fin M ⊕ Fin N → ℝ) (hv : testNorm v = 1) :
    ‖ent (PiZ N Sig z) (vbar Sig v) (vbar Sig v) +
        ((v ⬝ᵥ (SigU (n := Fin N) Sig)⁻¹ *ᵥ v : ℝ) : ℂ)‖ ≤
      ‖mFun N (specOf Sig) z‖ * c⁻¹ + 1 + ‖mFun N (specOf Sig) z‖ := by
  obtain ⟨U, h₂, h₁, hS, hσ⟩ := props_diag hSig
  set σ := specOf Sig with hσdef
  set w := mFun N σ z with hwdef
  have hw0 : ∀ i, 1 + (σ i : ℂ) * w ≠ 0 := fun i h0 => by
    have := hOne i
    rw [h0, norm_zero] at this
    linarith
  have hP := props_Pi_coord (N := N) h₂ h₁ hS (fun i => (hσ i).ne') hw0 v
  have hQ := props_Q_coord (N := N) hSig h₂ h₁ hS (fun i => (hσ i).ne') v
  have hUT := props_sum_sq_UT h₂ (v ∘ Sum.inl)
  simp only [Function.comp_apply] at hUT
  have hsum : ∑ i, (Uᵀ *ᵥ (v ∘ Sum.inl)) i ^ 2 + ∑ μ, v (Sum.inr μ) ^ 2 = 1 := by
    rw [hUT]; exact props_sum_norm v hv
  set t : ℝ := ∑ μ, v (Sum.inr μ) ^ 2 with ht
  have ht0 : 0 ≤ t := Finset.sum_nonneg fun _ _ => sq_nonneg _
  change ‖ent (piMat (N := N) Sig w) (vbar Sig v) (vbar Sig v) + _‖ ≤ _
  rw [hP, hQ]
  have e : ∑ i, (((((σ i)⁻¹ * (Uᵀ *ᵥ (v ∘ Sum.inl)) i : ℝ)) : ℂ) ^ 2 *
        (-((σ i : ℂ) * (1 + (σ i : ℂ) * w)⁻¹))) + w * ∑ μ, ((v (Sum.inr μ) : ℝ) : ℂ) ^ 2 +
      (((∑ i, (Uᵀ *ᵥ (v ∘ Sum.inl)) i ^ 2 * (σ i)⁻¹ + t : ℝ)) : ℂ) =
      ∑ i, ((((((σ i)⁻¹ * (Uᵀ *ᵥ (v ∘ Sum.inl)) i : ℝ)) : ℂ) ^ 2 *
        (-((σ i : ℂ) * (1 + (σ i : ℂ) * w)⁻¹))) +
          ((((Uᵀ *ᵥ (v ∘ Sum.inl)) i ^ 2 * (σ i)⁻¹ : ℝ)) : ℂ)) + (w + 1) * (t : ℂ) := by
    rw [ht]
    push_cast
    rw [Finset.sum_add_distrib]
    ring
  rw [e]
  have h1 : ‖∑ i, ((((((σ i)⁻¹ * (Uᵀ *ᵥ (v ∘ Sum.inl)) i : ℝ)) : ℂ) ^ 2 *
        (-((σ i : ℂ) * (1 + (σ i : ℂ) * w)⁻¹))) +
          ((((Uᵀ *ᵥ (v ∘ Sum.inl)) i ^ 2 * (σ i)⁻¹ : ℝ)) : ℂ))‖ ≤
      ∑ i, (Uᵀ *ᵥ (v ∘ Sum.inl)) i ^ 2 * (‖w‖ * c⁻¹) :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => props_term_norm (hσ i) hc (hOne i))
  have h2 : ‖(w + 1) * (t : ℂ)‖ ≤ (‖w‖ + 1) * t := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
    exact mul_le_mul_of_nonneg_right ((norm_add_le _ _).trans (by simp)) ht0
  have hs0 : 0 ≤ ∑ i, (Uᵀ *ᵥ (v ∘ Sum.inl)) i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsum' : ∑ i, (Uᵀ *ᵥ (v ∘ Sum.inl)) i ^ 2 + t = 1 := hsum
  have hwc : 0 ≤ ‖w‖ * c⁻¹ := mul_nonneg (norm_nonneg _) (inv_nonneg.2 hc.le)
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ ∑ i, (Uᵀ *ᵥ (v ∘ Sum.inl)) i ^ 2 * (‖w‖ * c⁻¹) + (‖w‖ + 1) * t := add_le_add h1 h2
    _ ≤ ‖w‖ * c⁻¹ + 1 + ‖w‖ := by
        rw [← Finset.sum_mul]
        nlinarith [norm_nonneg w]


/-- `F_v ≤ ((1 + ‖XᵀX‖)/η + 1) + (|m| c⁻¹ + 1 + |m|)` for `|v| = 1` under (1+xm). -/
private theorem props_Fv_le {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {c : ℝ}
    (hc : 0 < c) {z : ℂ} (hz : 0 < z.im)
    (hOne : ∀ i, c ≤ ‖1 + (specOf Sig i : ℂ) * mFun N (specOf Sig) z‖)
    (v : Fin M ⊕ Fin N → ℝ) (hv : testNorm v = 1) (A : Matrix (Fin M) (Fin N) ℝ) :
    Fv Sig A z v ≤ ((1 + ‖Aᵀ * A‖) / z.im + 1) +
      (‖mFun N (specOf Sig) z‖ * c⁻¹ + 1 + ‖mFun N (specOf Sig) z‖) := by
  have hK := opnorm_G hSig A hz v v
  rw [props_ent_K hSig, props_sqrt_dot, hv, mul_one, mul_one] at hK
  have hPQ := props_PQ_le hSig hc hOne v hv
  unfold Fv
  rw [props_ent_sub]
  calc _ = ‖(ent (G Sig A z) (vbar Sig v) (vbar Sig v) +
          ((v ⬝ᵥ (SigU (n := Fin N) Sig)⁻¹ *ᵥ v : ℝ) : ℂ)) -
        (ent (PiZ N Sig z) (vbar Sig v) (vbar Sig v) +
          ((v ⬝ᵥ (SigU (n := Fin N) Sig)⁻¹ *ᵥ v : ℝ) : ℂ))‖ := by
        congr 1; ring
    _ ≤ _ := norm_sub_le _ _
    _ ≤ _ := add_le_add hK hPQ

/-- `Im G_{v̄v̄} ≤ Im Π_{v̄v̄} + F_v`. -/
private theorem props_ImGvv_le_Fv (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (v : Fin M ⊕ Fin N → ℝ) :
    ImGvv Sig A z v ≤ (ent (PiZ N Sig z) (vbar Sig v) (vbar Sig v)).im + Fv Sig A z v := by
  have e : ent (G Sig A z) (vbar Sig v) (vbar Sig v) =
      ent (G Sig A z - PiZ N Sig z) (vbar Sig v) (vbar Sig v) +
        ent (PiZ N Sig z) (vbar Sig v) (vbar Sig v) := by
    rw [props_ent_sub]; ring
  unfold ImGvv Fv
  rw [e, Complex.add_im]
  linarith [Complex.im_le_norm (ent (G Sig A z - PiZ N Sig z) (vbar Sig v) (vbar Sig v))]

/-- The `L²` operator norm is at most the Frobenius norm. -/
private theorem props_opNorm_le {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
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
private theorem props_XtX_le (A : Matrix (Fin M) (Fin N) ℝ) :
    ‖Aᵀ * A‖ ≤ ∑ α : Fin M × Fin N, A α.1 α.2 ^ 2 := by
  have h1 : ‖Aᵀ * A‖ = ‖A‖ * ‖A‖ := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact l2_opNorm_conjTranspose_mul_self A
  have h2 := props_opNorm_le A
  have h0 : 0 ≤ ∑ i, ∑ j, A i j ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [h1, Fintype.sum_prod_type]
  calc ‖A‖ * ‖A‖ ≤ Real.sqrt (∑ i, ∑ j, A i j ^ 2) * Real.sqrt (∑ i, ∑ j, A i j ^ 2) :=
        mul_le_mul h2 h2 (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := Real.mul_self_sqrt h0

private theorem props_continuous_linH (Sig : Matrix (Fin M) (Fin M) ℝ) (z : ℂ) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => linH Sig⁻¹ A z := by
  unfold linH cplx
  refine Continuous.matrix_fromBlocks continuous_const ?_ ?_ continuous_const
  · exact Continuous.matrix_map continuous_id Complex.continuous_ofReal
  · exact Continuous.matrix_map continuous_id.matrix_transpose Complex.continuous_ofReal

/-- Every entry of `G` is a measurable function of the matrix. -/
private theorem props_measurable_G (Sig : Matrix (Fin M) (Fin M) ℝ) (z : ℂ)
    (s t : Fin M ⊕ Fin N) : Measurable fun A : Matrix (Fin M) (Fin N) ℝ => G Sig A z s t := by
  have hc := props_continuous_linH (N := N) Sig z
  have hdet : Measurable fun A : Matrix (Fin M) (Fin N) ℝ => (linH Sig⁻¹ A z).det :=
    (hc.matrix_det).measurable
  have hadj : Measurable fun A : Matrix (Fin M) (Fin N) ℝ => (linH Sig⁻¹ A z).adjugate s t :=
    (Matrix.measurable_iff.1 (hc.matrix_adjugate).measurable) s t
  have h : (fun A : Matrix (Fin M) (Fin N) ℝ => G Sig A z s t) =
      fun A => (linH Sig⁻¹ A z).det⁻¹ * (linH Sig⁻¹ A z).adjugate s t := by
    funext A
    change (linH Sig⁻¹ A z)⁻¹ s t = _
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
    simp
  rw [h]
  exact hdet.inv.mul hadj

/-- `F_v` is a measurable function of the matrix. -/
private theorem props_measurable_Fv (Sig : Matrix (Fin M) (Fin M) ℝ) (z : ℂ)
    (v : Fin M ⊕ Fin N → ℝ) : Measurable fun A : Matrix (Fin M) (Fin N) ℝ => Fv Sig A z v := by
  have h : (fun A : Matrix (Fin M) (Fin N) ℝ =>
      ent (G Sig A z - PiZ N Sig z) (vbar Sig v) (vbar Sig v)) =
      fun A => ∑ s, ((vbar Sig v s : ℝ) : ℂ) *
        ∑ t, (G Sig A z s t - PiZ N Sig z s t) * ((vbar Sig v t : ℝ) : ℂ) := by
    funext A
    simp only [ent, cvec, dotProduct, mulVec, Matrix.sub_apply]
  unfold Fv
  refine Measurable.norm ?_
  rw [h]
  refine Finset.measurable_sum _ fun s _ => (Finset.measurable_sum _ fun t _ => ?_).const_mul _
  exact ((props_measurable_G Sig z s t).sub_const _).mul_const _

private theorem props_Psi_pos {σ : Fin M → ℝ} {z : ℂ} (hN : 1 ≤ N) (hz : 0 < z.im) :
    0 < Psi N σ z := by
  unfold Psi
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have : 0 < 1 / ((N : ℝ) * z.im) := by positivity
  linarith [Real.sqrt_nonneg ((mFun N σ z).im / (N * z.im))]

private theorem props_mBoundConst_pos {τ : ℝ} (hτ : 0 < τ) : 0 < mBoundConst τ := by
  unfold mBoundConst genPropConst
  positivity



/-- Property (A_m) at fixed `N`, for the class `P` with moment function `C`. -/
def PropA (N : ℕ) (C : ℕ → ℝ) (P : ModelClass M N) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ)
    (C₀ δ : ℝ) (m : ℕ) (ε D : ℝ) : Prop :=
  ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption C X → P Ω X →
    ∀ z ∈ levelSet N δ S m, ∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 →
      DomAt N ε D (fun ω => ImGvv Sig (X ω) z v)
        (fun _ => (mFun N (specOf Sig) z).im + (N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z)

/-- Property (C_m) at fixed `N`, for the class `P` with moment function `C`. -/
def PropC (N : ℕ) (C : ℕ → ℝ) (P : ModelClass M N) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ)
    (C₀ δ : ℝ) (m : ℕ) (ε D : ℝ) : Prop :=
  ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption C X → P Ω X →
    ∀ z ∈ levelSet N δ S m, ∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 →
      ODomAt N ε D (fun ω => ent (G Sig (X ω) z - PiZ N Sig z) (vbar Sig v) (vbar Sig v))
        (fun _ => (N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z)

theorem PropA.mono {τ c : ℝ} {C : ℕ → ℝ} {P : ModelClass M N} {Sig : Matrix (Fin M) (Fin M) ℝ}
    {S : Set ℂ} {C₀ δ ε ε' D D' : ℝ} {m : ℕ} (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N)
    (hε : ε ≤ ε') (hD : D' ≤ D) (h : PropA N C P Sig S C₀ δ m ε D) :
    PropA N C P Sig S C₀ δ m ε' D' := by
  intro Ω _ _ X hX hP z hz v hv
  have hzim : 0 < z.im := (hset.domain.1 hz.1).1
  obtain ⟨-, -, -, -, hσ⟩ := props_diag hset.sigma.posDef
  have hm : 0 < (mFun N (specOf Sig) z).im := (mFun_spec N _ (fun i => (hσ i).le) hzim).1
  have hb : 0 ≤ (N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (props_Psi_pos hN hzim).le
  exact DomAt.mono hN (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => by linarith) hε hD
    (h Ω X hX hP z hz v hv)

/-- Lemma 7.3 (`lem:start_induction`): (A_0) holds. -/
theorem propA_zero (τ c : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hc : 0 < c)
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ)
      (P : ModelClass M N) (C₀ δ : ℝ), CompSetting τ c M N Sig S → 0 ≤ C₀ → 0 ≤ δ →
      PropA N C P Sig S C₀ δ 0 ε D := by
  obtain ⟨Cn, hCn⟩ := norm_XtX_le hτ hτ1
  obtain ⟨N₁, hN₁⟩ := hCn C D
  set Km := mBoundConst τ with hKm
  have hKm0 : 0 < Km := props_mBoundConst_pos hτ
  set KA : ℝ := (max Cn 0 + 2) * Km with hKA
  have hKA0 : 0 ≤ KA := by positivity
  refine ⟨max (max N₁ ⌈KA ^ ε⁻¹⌉₊) 1, fun N hN M Sig S P C₀ δ hset _ _ => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNN₁ : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  have hNε : KA ≤ (N : ℝ) ^ ε := by
    have h0 : ⌈KA ^ ε⁻¹⌉₊ ≤ N := le_trans (le_trans (le_max_right N₁ _) (le_max_left _ 1)) hN
    have h1 : KA ^ ε⁻¹ ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast h0)
    calc KA = (KA ^ ε⁻¹) ^ ε := (Real.rpow_inv_rpow hKA0 hε.ne').symm
      _ ≤ (N : ℝ) ^ ε := Real.rpow_le_rpow (Real.rpow_nonneg hKA0 _) h1 hε.le
  have hM : (M : ℝ) ≤ τ⁻¹ * N := by
    have := hset.ratio_le
    rwa [div_le_iff₀ hNpos] at this
  intro Ω _ _ X hX hP z hz v hv
  have hE := hN₁ N hNN₁ M X hX hM
  unfold HighProbAt at hE
  unfold DomAt
  refine le_trans (measure_mono fun ω hω => ?_) hE
  simp only [Set.mem_ofPred_eq] at hω
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
  by_contra hle
  rw [not_lt] at hle
  have hSig := hset.sigma.posDef
  have hzD := hset.domain.1 hz.1
  have hzim : 0 < z.im := hzD.1
  have hη : 1 ≤ z.im := by
    have := hz.2
    simpa using this
  have hdens : DensityAssumptions τ N (specOf Sig) :=
    (IsModel.diagModel_specOf ⟨hset.ratio_ge, hset.ratio_le, hX, hset.sigma⟩).densityAssumptions
      hset.pos
  have hm := (gen_prop_m_specDomain hdens hzD).2.2
  have hmK : Km⁻¹ ≤ (mFun N (specOf Sig) z).im :=
    le_trans (le_mul_of_one_le_right (inv_nonneg.2 hKm0.le) hη) hm
  have hG := props_ImGvv_le hSig (X ω) hzim v
  rw [hv, mul_one, mul_one] at hG
  have hnorm0 : 0 ≤ ‖(X ω)ᵀ * X ω‖ := norm_nonneg _
  have h1 : (1 + ‖(X ω)ᵀ * X ω‖) / z.im ≤ 1 + max Cn 0 := by
    rw [div_le_iff₀ hzim]
    nlinarith [le_max_left Cn 0]
  have h2 : max Cn 0 + 2 ≤ KA * (mFun N (specOf Sig) z).im := by
    have e : max Cn 0 + 2 = KA * Km⁻¹ := by
      rw [hKA, mul_assoc, mul_inv_cancel₀ hKm0.ne', mul_one]
    rw [e]
    exact mul_le_mul_of_nonneg_left hmK hKA0
  have hb : 0 ≤ (N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z :=
    mul_nonneg (Real.rpow_nonneg hNpos.le _) (props_Psi_pos hN1 hzim).le
  have hm0 : 0 ≤ (mFun N (specOf Sig) z).im := le_trans (by positivity) hmK
  have h3 : KA * (mFun N (specOf Sig) z).im ≤ (N : ℝ) ^ ε * (mFun N (specOf Sig) z).im :=
    mul_le_mul_of_nonneg_right hNε hm0
  have h4 : 0 ≤ (N : ℝ) ^ ε * ((N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z) :=
    mul_nonneg (Real.rpow_nonneg hNpos.le _) hb
  have hlt := hω
  rw [mul_add] at hlt
  linarith

/-- (C_m) implies (A_m) (Section 7, after Lemma 7.4), via `Im Π_{v̄v̄} ≤ max(c⁻², 1) Im m`. -/
theorem propA_of_propC {τ c : ℝ} {C : ℕ → ℝ} {P : ModelClass M N}
    {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ} {C₀ δ ε D : ℝ} {m : ℕ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) (hε : max (c⁻¹ ^ 2) 1 ≤ (N : ℝ) ^ ε)
    (h : PropC N C P Sig S C₀ δ m ε D) : PropA N C P Sig S C₀ δ m ε D := by
  intro Ω _ _ X hX hP z hz v hv
  have hzim : 0 < z.im := (hset.domain.1 hz.1).1
  have hSig := hset.sigma.posDef
  obtain ⟨-, -, -, -, hσ⟩ := props_diag hSig
  have hm : 0 < (mFun N (specOf Sig) z).im := (mFun_spec N _ (fun i => (hσ i).le) hzim).1
  have hPi := props_ImPi_le (N := N) hSig hset.c_pos hzim (hset.oneXm z hz.1) v hv
  have hK : max (c⁻¹ ^ 2) 1 * (mFun N (specOf Sig) z).im ≤
      (N : ℝ) ^ ε * (mFun N (specOf Sig) z).im :=
    mul_le_mul_of_nonneg_right hε hm.le
  have hC := h Ω X hX hP z hz v hv
  unfold ODomAt DomAt at hC
  unfold DomAt
  refine le_trans (measure_mono fun ω hω => ?_) hC
  simp only [Set.mem_ofPred_eq] at hω ⊢
  have hG := props_ImGvv_le_Fv Sig (X ω) z v
  unfold Fv at hG
  rw [mul_add] at hω
  linarith

/-- Markov's inequality turns the moment bound of Lemma 7.5 into (C_m). -/
theorem propC_of_moment {τ c : ℝ} {C : ℕ → ℝ} {P : ModelClass M N}
    {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ} {C₀ δ ε ε' D Kp : ℝ} {m p : ℕ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) (hp : D ≤ (ε' - ε) * p)
    (hK : Kp ≤ (N : ℝ) ^ (p * ε))
    (hmom : ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption C X → P Ω X →
      ∀ z ∈ levelSet N δ S m, ∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 →
        Integrable (fun ω => Fv Sig (X ω) z v ^ p) ∧
          ∫ ω, Fv Sig (X ω) z v ^ p ≤ Kp * ((N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z) ^ p) :
    PropC N C P Sig S C₀ δ m ε' D := by
  intro Ω _ _ X hX hP z hz v hv
  have hzim : 0 < z.im := (hset.domain.1 hz.1).1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hb : 0 < (N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z :=
    mul_pos (Real.rpow_pos_of_pos hNpos _) (props_Psi_pos hN hzim)
  obtain ⟨hint, hmom'⟩ := hmom Ω X hX hP z hz v hv
  refine DomAt.of_moment (ε := ε) p hN hp (fun ω => norm_nonneg _) hb hint (hmom'.trans ?_)
  have e : ((N : ℝ) ^ ε * ((N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z)) ^ p =
      (N : ℝ) ^ ((p : ℝ) * ε) * ((N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z) ^ p := by
    rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ ε), ← Real.rpow_mul hNpos.le, mul_comm ε]
  rw [e]
  exact mul_le_mul_of_nonneg_right hK (pow_nonneg hb.le p)

/-- The exponent `δ = min(ε, τ)/(4 C₀)` with `C₀ = 25`. -/
def deltaOf (ε τ : ℝ) : ℝ := min ε τ / 100

/-- The Markov moment `p = 2 max(1, ⌈8D/δ⌉)`, so that `D ≤ (δ/8 − δ/16) p`. -/
def markovPow (δ D : ℝ) : ℕ := 2 * max 1 ⌈8 * D / δ⌉₊

/-- The level `D_{m−1} = 100 (p + 1)²` of (A_{m−1}) needed for the step at moment `p`. -/
def dPrev (p : ℕ) : ℝ := 100 * ((p : ℝ) + 1) ^ 2

/-- The Gaussian level `D₁ = 12 p + 3 = 3(4p + 1)` of Lemma 7.8. -/
def gaussD (p : ℕ) : ℝ := 12 * (p : ℝ) + 3

/-- The top step `m* = max(1, ⌈(1 − τ)/δ⌉)`, so that `S_{m*} = S`. -/
def topLevel (τ δ : ℝ) : ℕ := max 1 ⌈(1 - τ) / δ⌉₊

/-- Rough moment bound: `E F_v^q ≤ N^{2q+1}` (proof of Lemma 7.8, (A_rough)). -/
theorem integral_Fv_pow_le (τ c : ℝ) (C : ℕ → ℝ) (q : ℕ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hc : 0 < c) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (S : Set ℂ),
      IsModel τ C M N Sig X → SpectralDomain τ N S → OneXmOn c N (specOf Sig) S →
      ∀ z ∈ S, ∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 →
        Integrable (fun ω => Fv Sig (X ω) z v ^ q) ∧
          ∫ ω, Fv Sig (X ω) z v ^ q ≤ (N : ℝ) ^ (2 * (q : ℝ) + 1) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · refine ⟨1, fun N hN Ω _ _ M Sig X S _ _ _ z _ v _ => ⟨by simp, ?_⟩⟩
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    simpa using hN1
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  set Km := mBoundConst τ with hKm
  have hKm0 : 0 < Km := props_mBoundConst_pos hτ
  set a : ℝ := 3 + Km * (c⁻¹ + 1) with ha
  have ha0 : 0 ≤ a := by positivity
  set C' : ℝ := max (C (2 * (n + 1))) 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set Kq : ℝ := 2 ^ n * (a ^ (n + 1) + τ⁻¹ ^ (n + 1) * C') with hKq
  refine ⟨max ⌈Kq⌉₊ 1, fun N hN Ω _ _ M Sig X S hmod hS hOne z hz v hv => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  have hKqN0 : ⌈Kq⌉₊ ≤ N := le_trans (le_max_left _ 1) hN
  have hKqN : Kq ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hKqN0)
  have hSig := hmod.sigma.posDef
  have hdens := (hmod.diagModel_specOf).densityAssumptions hτ
  have hzD := hS.1 hz
  have hzim : 0 < z.im := hzD.1
  have hm := (gen_prop_m_specDomain hdens hzD).2.1
  have hη : 1 ≤ (N : ℝ) * z.im := by
    have h1 : (N : ℝ) ^ (-1 + τ) ≤ z.im := hzD.2.2.2.1
    have h2 : (N : ℝ) ^ (-1 : ℝ) ≤ (N : ℝ) ^ (-1 + τ) :=
      Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
    rw [Real.rpow_neg_one] at h2
    have h3 : (N : ℝ)⁻¹ ≤ z.im := h2.trans h1
    calc (1 : ℝ) = N * (N : ℝ)⁻¹ := (mul_inv_cancel₀ hNpos.ne').symm
      _ ≤ N * z.im := mul_le_mul_of_nonneg_left h3 hNpos.le
  set Y : Ω → ℝ := fun ω => ∑ α : Fin M × Fin N, X ω α.1 α.2 ^ 2 with hY
  have hY0 : ∀ ω, 0 ≤ Y ω := fun ω => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hF0 : ∀ ω, 0 ≤ Fv Sig (X ω) z v := fun ω => norm_nonneg _
  have hpt : ∀ ω, Fv Sig (X ω) z v ≤ N * (a + Y ω) := by
    intro ω
    have h1 := props_Fv_le hSig hc hzim (hOne z hz) v hv (X ω)
    have h2 : ‖(X ω)ᵀ * X ω‖ ≤ Y ω := props_XtX_le (X ω)
    have h3 : (1 + ‖(X ω)ᵀ * X ω‖) / z.im ≤ N * (1 + Y ω) := by
      rw [div_le_iff₀ hzim]
      have h0 : 0 ≤ 1 + Y ω := by linarith [hY0 ω]
      nlinarith [norm_nonneg ((X ω)ᵀ * X ω)]
    have h4 : ‖mFun N (specOf Sig) z‖ * c⁻¹ + 1 + ‖mFun N (specOf Sig) z‖ ≤
        Km * (c⁻¹ + 1) + 1 := by
      have hc' : 0 ≤ c⁻¹ := inv_nonneg.2 hc.le
      nlinarith [norm_nonneg (mFun N (specOf Sig) z)]
    have h5 : 0 ≤ 2 + Km * (c⁻¹ + 1) := by positivity
    have h6 := mul_nonneg (sub_nonneg.2 hNr) h5
    have h7 : (N : ℝ) * (a + Y ω) = N * (1 + Y ω) + N * (2 + Km * (c⁻¹ + 1)) := by
      rw [ha]; ring
    rw [h7]
    nlinarith
  have hXm : Measurable X :=
    measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun μ => hmod.entries.measurable i μ
  have hFm : Measurable fun ω => Fv Sig (X ω) z v := (props_measurable_Fv Sig z v).comp hXm
  have hent : ∀ α : Fin M × Fin N, (fun ω => (X ω α.1 α.2 ^ 2) ^ (n + 1)) =
      fun ω => ((N : ℝ) ^ (n + 1))⁻¹ * |Real.sqrt N * X ω α.1 α.2| ^ (2 * (n + 1)) := by
    intro α
    funext ω
    rw [pow_mul, sq_abs, mul_pow, Real.sq_sqrt hNpos.le, mul_pow, ← mul_assoc,
      inv_mul_cancel₀ (pow_pos hNpos _).ne', one_mul]
  have hint : ∀ α : Fin M × Fin N, Integrable fun ω => (X ω α.1 α.2 ^ 2) ^ (n + 1) := by
    intro α
    rw [hent α]
    exact (hmod.entries.integrable_moment (2 * (n + 1)) α.1 α.2).const_mul _
  have hintle : ∀ α : Fin M × Fin N,
      ∫ ω, (X ω α.1 α.2 ^ 2) ^ (n + 1) ≤ ((N : ℝ) ^ (n + 1))⁻¹ * C' := by
    intro α
    rw [hent α, integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      ((hmod.entries.moment (2 * (n + 1)) α.1 α.2).trans (le_max_left _ _))
      (inv_nonneg.2 (pow_nonneg hNpos.le _))
  set card : ℝ := ((Finset.univ : Finset (Fin M × Fin N)).card : ℝ) with hcard
  have hcardMN : card = (M : ℝ) * N := by
    rw [hcard, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    push_cast; ring
  set g : Ω → ℝ := fun ω => (N : ℝ) ^ (n + 1) * (2 ^ n * (a ^ (n + 1) +
      card ^ n * ∑ α : Fin M × Fin N, (X ω α.1 α.2 ^ 2) ^ (n + 1))) with hg
  have hgint : Integrable g :=
    (((integrable_const _).add ((integrable_finsetSum _ fun α _ => hint α).const_mul _)).const_mul
      _).const_mul _
  have hle : ∀ ω, Fv Sig (X ω) z v ^ (n + 1) ≤ g ω := by
    intro ω
    have h1 : Fv Sig (X ω) z v ^ (n + 1) ≤ (N : ℝ) ^ (n + 1) * (a + Y ω) ^ (n + 1) := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (hF0 ω) (hpt ω) _
    have h2 : (a + Y ω) ^ (n + 1) ≤ 2 ^ n * (a ^ (n + 1) + Y ω ^ (n + 1)) := by
      simpa using add_pow_le ha0 (hY0 ω) (n + 1)
    have h3 : Y ω ^ (n + 1) ≤ card ^ n * ∑ α : Fin M × Fin N, (X ω α.1 α.2 ^ 2) ^ (n + 1) :=
      pow_sum_le_card_mul_sum_pow (fun _ _ => sq_nonneg _) n
    calc _ ≤ _ := h1
      _ ≤ _ := mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left
          (add_le_add_right h3 _) (by positivity))) (by positivity)
  have hFint : Integrable fun ω => Fv Sig (X ω) z v ^ (n + 1) :=
    hgint.mono' (hFm.pow_const _).aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (pow_nonneg (hF0 ω) _)]; exact hle ω)
  refine ⟨hFint, ?_⟩
  have hgval : ∫ ω, g ω = (N : ℝ) ^ (n + 1) * (2 ^ n * (a ^ (n + 1) +
      card ^ n * ∑ α : Fin M × Fin N, ∫ ω, (X ω α.1 α.2 ^ 2) ^ (n + 1))) := by
    rw [hg, integral_const_mul, integral_const_mul,
      integral_add (integrable_const _) ((integrable_finsetSum _ fun α _ => hint α).const_mul _),
      integral_const, integral_const_mul, integral_finsetSum _ fun α _ => hint α]
    simp
  have hsum : ∑ α : Fin M × Fin N, ∫ ω, (X ω α.1 α.2 ^ 2) ^ (n + 1) ≤
      card * (((N : ℝ) ^ (n + 1))⁻¹ * C') := by
    calc _ ≤ ∑ α : Fin M × Fin N, ((N : ℝ) ^ (n + 1))⁻¹ * C' :=
          Finset.sum_le_sum fun α _ => hintle α
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hMr : (M : ℝ) ≤ τ⁻¹ * N := by
    have := hmod.ratio_le
    rwa [div_le_iff₀ hNpos] at this
  have hP1 : (1 : ℝ) ≤ (N : ℝ) ^ (n + 1) := one_le_pow₀ hNr
  have hcard0 : 0 ≤ card := by rw [hcardMN]; positivity
  have hstep1 : card ^ n * ∑ α : Fin M × Fin N, ∫ ω, (X ω α.1 α.2 ^ 2) ^ (n + 1) ≤
      (M : ℝ) ^ (n + 1) * C' := by
    calc _ ≤ card ^ n * (card * (((N : ℝ) ^ (n + 1))⁻¹ * C')) :=
          mul_le_mul_of_nonneg_left hsum (pow_nonneg hcard0 _)
      _ = (M : ℝ) ^ (n + 1) * C' := by
          rw [hcardMN]
          field_simp
          ring
  have hstep2 : (M : ℝ) ^ (n + 1) * C' ≤ τ⁻¹ ^ (n + 1) * (N : ℝ) ^ (n + 1) * C' := by
    rw [← mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hMr _) hC'0
  have hstep3 : a ^ (n + 1) + τ⁻¹ ^ (n + 1) * (N : ℝ) ^ (n + 1) * C' ≤
      (N : ℝ) ^ (n + 1) * (a ^ (n + 1) + τ⁻¹ ^ (n + 1) * C') := by
    have : a ^ (n + 1) ≤ (N : ℝ) ^ (n + 1) * a ^ (n + 1) :=
      le_mul_of_one_le_left (pow_nonneg ha0 _) hP1
    nlinarith
  have hfin : (N : ℝ) ^ (2 * ((n + 1 : ℕ) : ℝ) + 1) =
      (N : ℝ) ^ (n + 1) * (N : ℝ) ^ (n + 1) * N := by
    rw [show 2 * ((n + 1 : ℕ) : ℝ) + 1 = ((2 * (n + 1) + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
    ring
  calc ∫ ω, Fv Sig (X ω) z v ^ (n + 1) ≤ ∫ ω, g ω :=
        integral_mono hFint hgint hle
    _ ≤ (N : ℝ) ^ (n + 1) * (2 ^ n * ((N : ℝ) ^ (n + 1) * (a ^ (n + 1) +
        τ⁻¹ ^ (n + 1) * C'))) := by
        rw [hgval]
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity))
          (by positivity)
        linarith
    _ = (N : ℝ) ^ (n + 1) * (N : ℝ) ^ (n + 1) * Kq := by rw [hKq]; ring
    _ ≤ (N : ℝ) ^ (n + 1) * (N : ℝ) ^ (n + 1) * N :=
        mul_le_mul_of_nonneg_left hKqN (by positivity)
    _ = _ := hfin.symm

/-- Lemma 7.8 (`lem:comparison_0`): the Gaussian law at `(ε₁, D₁)` with `D₁ ≥ 3(4p+1)` gives
`E F_v^p(X⁰) ≤ 2 N^{p ε₁} Ψ^p`. -/
theorem comparison_zero (τ c : ℝ) (p : ℕ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hc : 0 < c) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ) (ε₁ D₁ : ℝ),
      τ ≤ (M : ℝ) / N → (M : ℝ) / N ≤ τ⁻¹ → SigmaAssumption τ Sig → SpectralDomain τ N S →
      OneXmOn c N (specOf Sig) S → 0 ≤ ε₁ → 3 * (4 * (p : ℝ) + 1) ≤ D₁ →
      AnisotropicLawAt N ε₁ D₁ Sig (gaussX M N) S →
      ∀ z ∈ S, ∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 →
        ∫ ω, Fv Sig (gaussX M N ω) z v ^ p ≤
          2 * (N : ℝ) ^ ((p : ℝ) * ε₁) * Psi N (specOf Sig) z ^ p := by
  obtain ⟨N₁, hN₁⟩ := integral_Fv_pow_le τ c gaussMoment (2 * p) hτ hτ1 hc
  refine ⟨max (max N₁ ⌈τ⁻¹⌉₊) 1,
    fun N hN M Sig S ε₁ D₁ hr1 hr2 hsig hS hOne hε₁ hD₁ hlaw z hz v hv => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNN₁ : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  have hNτ0 : ⌈τ⁻¹⌉₊ ≤ N := le_trans (le_trans (le_max_right N₁ _) (le_max_left _ 1)) hN
  have hNτ : τ⁻¹ ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hNτ0)
  have hmod := isModel_gaussX hN1 hr1 hr2 hsig
  obtain ⟨hint, hbound⟩ := hN₁ N hNN₁ M Sig (gaussX M N) S hmod hS hOne z hz v hv
  have hzD := hS.1 hz
  have hzim : 0 < z.im := hzD.1
  have hzim' : z.im ≤ τ⁻¹ := hzD.2.2.2.2
  have hΨpos := props_Psi_pos (σ := specOf Sig) hN1 hzim
  have hΨ : (N : ℝ) ^ (-(2 : ℝ)) ≤ Psi N (specOf Sig) z := by
    have h1 : 1 / ((N : ℝ) * z.im) ≤ Psi N (specOf Sig) z := by
      unfold Psi
      linarith [Real.sqrt_nonneg ((mFun N (specOf Sig) z).im / (N * z.im))]
    have h2 : (N : ℝ) ^ (-(2 : ℝ)) = 1 / ((N : ℝ) * N) := by
      rw [Real.rpow_neg hNpos.le, Real.rpow_two, sq, one_div]
    rw [h2]
    refine le_trans (one_div_le_one_div_of_le (by positivity) ?_) h1
    exact mul_le_mul_of_nonneg_left (hzim'.trans hNτ) hNpos.le
  have hΓ : (N : ℝ) ^ (-(4 * (p : ℝ) + 1)) ≤ Psi N (specOf Sig) z ^ p := by
    calc (N : ℝ) ^ (-(4 * (p : ℝ) + 1)) ≤ (N : ℝ) ^ (-(2 : ℝ) * p) :=
          Real.rpow_le_rpow_of_exponent_le hNr (by
            have : (0 : ℝ) ≤ p := Nat.cast_nonneg _
            linarith)
      _ = ((N : ℝ) ^ (-(2 : ℝ))) ^ p := by
          rw [Real.rpow_mul hNpos.le, Real.rpow_natCast]
      _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hNpos.le _) hΨ _
  have hpow : (fun ω => (Fv Sig (gaussX M N ω) z v ^ p) ^ 2) =
      fun ω => Fv Sig (gaussX M N ω) z v ^ (2 * p) := by
    funext ω; rw [← pow_mul, mul_comm]
  have hint2 : Integrable fun ω => (Fv Sig (gaussX M N ω) z v ^ p) ^ 2 := by
    rw [hpow]; exact hint
  have h2 : ∫ ω, (Fv Sig (gaussX M N ω) z v ^ p) ^ 2 ≤ (N : ℝ) ^ (4 * (p : ℝ) + 1) := by
    rw [hpow]
    refine hbound.trans (le_of_eq ?_)
    congr 1
    push_cast
    ring
  have hdom : DomAt N ((p : ℝ) * ε₁) D₁ (fun ω => Fv Sig (gaussX M N ω) z v ^ p)
      (fun _ => Psi N (specOf Sig) z ^ p) := by
    have hl := hlaw z hz v v
    unfold DomAt at hl ⊢
    refine le_trans (measure_mono fun ω hω => ?_) hl
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [hv, mul_one, mul_one, ← ent_vbar_eq_testBilin hsig.posDef]
    have e : (N : ℝ) ^ ((p : ℝ) * ε₁) * Psi N (specOf Sig) z ^ p =
        ((N : ℝ) ^ ε₁ * Psi N (specOf Sig) z) ^ p := by
      rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ ε₁), ← Real.rpow_mul hNpos.le, mul_comm ε₁]
    rw [e] at hω
    exact lt_of_pow_lt_pow_left₀ p (norm_nonneg _) hω
  exact integral_le_of_domAt (C := 4 * (p : ℝ) + 1) hN1 (mul_nonneg (Nat.cast_nonneg _) hε₁)
    hD₁ hΓ (fun ω => pow_nonneg (norm_nonneg _) _) hint2 h2 hdom


/-! ## Instances -/

/-- `PropA.mono` at `τ = 1/2`, `c = 1`, `M = N = 2`, `Σ = 1`, `C = 2`, `C₀ = 25`, `δ = 1/100`,
`m = 0`, from `(ε, D) = (1/8, 2)` to `(1/4, 1)`. The setting and (A_0) at `(1/8, 2)` are
hypotheses (conditional example). -/
example (S : Set ℂ) (P : ModelClass 2 2)
    (hset : CompSetting (1 / 2) 1 2 2 (1 : Matrix (Fin 2) (Fin 2) ℝ) S)
    (h : PropA 2 (fun _ => 2) P 1 S 25 (1 / 100) 0 (1 / 8) 2) :
    PropA 2 (fun _ => 2) P 1 S 25 (1 / 100) 0 (1 / 4) 1 :=
  PropA.mono hset (by norm_num) (by norm_num) (by norm_num) h

/-- Lemma 7.3 at `τ = 1/2`, `c = 1`, `C = 2`, `ε = 1`, `D = 1`. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ)
      (P : ModelClass M N) (C₀ δ : ℝ), CompSetting (1 / 2) 1 M N Sig S → 0 ≤ C₀ → 0 ≤ δ →
      PropA N (fun _ => 2) P Sig S C₀ δ 0 1 1 :=
  propA_zero (1 / 2) 1 (fun _ => 2) 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- (C_m) ⇒ (A_m) at `τ = 1/2`, `c = 1`, `M = N = 2`, `Σ = 1`, `C₀ = 25`, `δ = 1/100`, `m = 1`,
`ε = D = 1`, where `max(c⁻², 1) = 1 ≤ 2 = N^ε`. The setting and (C_1) are hypotheses
(conditional example). -/
example (S : Set ℂ) (P : ModelClass 2 2)
    (hset : CompSetting (1 / 2) 1 2 2 (1 : Matrix (Fin 2) (Fin 2) ℝ) S)
    (h : PropC 2 (fun _ => 2) P 1 S 25 (1 / 100) 1 1 1) :
    PropA 2 (fun _ => 2) P 1 S 25 (1 / 100) 1 1 1 :=
  propA_of_propC hset (by norm_num) (by norm_num) h

/-- The Markov step at `τ = 1/2`, `c = 1`, `M = N = 2`, `Σ = 1`, `C₀ = 25`, `δ = 1/100`, `m = 1`,
`p = 16`, `(ε, ε') = (1/16, 1/8)`, `D = 1 = (ε' − ε) p` and `K_p = 1 ≤ 2 = N^{pε}`. The setting
and the moment bound are hypotheses (conditional example). -/
example (S : Set ℂ) (P : ModelClass 2 2)
    (hset : CompSetting (1 / 2) 1 2 2 (1 : Matrix (Fin 2) (Fin 2) ℝ) S)
    (hmom : ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (X : Ω → Matrix (Fin 2) (Fin 2) ℝ), EntryAssumption (fun _ => 2) X → P Ω X →
      ∀ z ∈ levelSet 2 (1 / 100) S 1, ∀ v : Fin 2 ⊕ Fin 2 → ℝ, testNorm v = 1 →
        Integrable (fun ω => Fv (1 : Matrix (Fin 2) (Fin 2) ℝ) (X ω) z v ^ 16) ∧
          ∫ ω, Fv (1 : Matrix (Fin 2) (Fin 2) ℝ) (X ω) z v ^ 16 ≤
            1 * (((2 : ℕ) : ℝ) ^ ((25 : ℝ) * (1 / 100)) *
              Psi 2 (specOf (1 : Matrix (Fin 2) (Fin 2) ℝ)) z) ^ 16) :
    PropC 2 (fun _ => 2) P 1 S 25 (1 / 100) 1 (1 / 8) 1 :=
  propC_of_moment (ε := 1 / 16) hset (by norm_num) (by norm_num) (by norm_num) hmom

/-- The rough moment bound at `τ = 1/2`, `c = 1`, `C = 2`, `q = 2`. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)] (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (X : Ω → Matrix (Fin M) (Fin N) ℝ) (S : Set ℂ),
      IsModel (1 / 2) (fun _ => 2) M N Sig X → SpectralDomain (1 / 2) N S →
      OneXmOn 1 N (specOf Sig) S → ∀ z ∈ S, ∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 →
        Integrable (fun ω => Fv Sig (X ω) z v ^ 2) ∧
          ∫ ω, Fv Sig (X ω) z v ^ 2 ≤ (N : ℝ) ^ (2 * ((2 : ℕ) : ℝ) + 1) :=
  integral_Fv_pow_le (1 / 2) 1 (fun _ => 2) 2 (by norm_num) (by norm_num) (by norm_num)

/-- Lemma 7.8 at `τ = 1/2`, `c = 1`, `p = 2` (so `D₁ ≥ 27`). -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ)
      (ε₁ D₁ : ℝ), (1 / 2 : ℝ) ≤ (M : ℝ) / N → (M : ℝ) / N ≤ (1 / 2 : ℝ)⁻¹ →
      SigmaAssumption (1 / 2) Sig → SpectralDomain (1 / 2) N S → OneXmOn 1 N (specOf Sig) S →
      0 ≤ ε₁ → 3 * (4 * ((2 : ℕ) : ℝ) + 1) ≤ D₁ →
      AnisotropicLawAt N ε₁ D₁ Sig (gaussX M N) S →
      ∀ z ∈ S, ∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 →
        ∫ ω, Fv Sig (gaussX M N ω) z v ^ 2 ≤
          2 * (N : ℝ) ^ (((2 : ℕ) : ℝ) * ε₁) * Psi N (specOf Sig) z ^ 2 :=
  comparison_zero (1 / 2) 1 2 (by norm_num) (by norm_num) (by norm_num)

end Anisotropic

#print axioms Anisotropic.PropA
#print axioms Anisotropic.PropC
#print axioms Anisotropic.PropA.mono
#print axioms Anisotropic.propA_zero
#print axioms Anisotropic.propA_of_propC
#print axioms Anisotropic.propC_of_moment
#print axioms Anisotropic.deltaOf
#print axioms Anisotropic.markovPow
#print axioms Anisotropic.dPrev
#print axioms Anisotropic.gaussD
#print axioms Anisotropic.topLevel
#print axioms Anisotropic.integral_Fv_pow_le
#print axioms Anisotropic.comparison_zero
