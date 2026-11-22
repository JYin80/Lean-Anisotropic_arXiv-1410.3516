module

public import Anisotropic.Entrywise.Defs
public import Anisotropic.LinAlg.Expansion
public import Anisotropic.Probability.NormBound.Main

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # Notation for §7: `v̄`, `Π`, `F_v`, `Im G_{v̄v̄}`; polarization; `Xupd` -/

/-- `v̄ = Σ̲⁻¹ v` (def_bar_v). -/
def vbar (Sig : Matrix (Fin M) (Fin M) ℝ) (v : Fin M ⊕ Fin N → ℝ) : Fin M ⊕ Fin N → ℝ :=
  Sum.elim (Sig⁻¹ *ᵥ (v ∘ Sum.inl)) (v ∘ Sum.inr)

/-- `Π(z)` with `m = m(z)` of the eigenvalues of `Σ`. -/
abbrev PiZ (N : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (z : ℂ) :
    Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ :=
  piMat (N := N) Sig (mFun N (specOf Sig) z)

/-- (def_Fp): `F_v(X, z) = |G_{v̄v̄}(z) − Π_{v̄v̄}(z)|`. -/
def Fv (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (v : Fin M ⊕ Fin N → ℝ) : ℝ :=
  ‖ent (G Sig A z - PiZ N Sig z) (vbar Sig v) (vbar Sig v)‖

/-- `Im G_{v̄v̄}(z)`. -/
def ImGvv (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (v : Fin M ⊕ Fin N → ℝ) : ℝ :=
  (ent (G Sig A z) (vbar Sig v) (vbar Sig v)).im

/-- `Σ̲⁻¹ = diag(Σ⁻¹, 1)` for invertible `Σ`. -/
private theorem comparison_ulSigma_inv {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) :
    (ulSigma N Sig)⁻¹ = fromBlocks (cplx Sig⁻¹) 0 0 1 := by
  have hS : Sig * Sig⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hSig.isUnit)
  apply Matrix.inv_eq_right_inv
  rw [ulSigma, fromBlocks_multiply]
  have h1 : cplx Sig * cplx Sig⁻¹ = 1 := by
    rw [cplx, cplx, ← Matrix.map_mul, hS, Matrix.map_one _ (map_zero _) (map_one _)]
  simp only [Complex.coe_algebraMap, Matrix.mul_zero, add_zero, Matrix.mul_one, Matrix.zero_mul,
    mul_one, zero_add]
  rw [show Sig.map Complex.ofReal * cplx Sig⁻¹ = 1 from h1]
  exact fromBlocks_one

/-- `Σ̲⁻¹` is symmetric. -/
private theorem comparison_ulSigma_inv_transpose {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hSig : Sig.PosDef) : ((ulSigma N Sig)⁻¹)ᵀ = (ulSigma N Sig)⁻¹ := by
  have hS : Sigᵀ = Sig := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact hSig.1.eq
  rw [comparison_ulSigma_inv hSig, fromBlocks_transpose]
  simp only [transpose_zero, transpose_one]
  congr 1
  rw [cplx, ← transpose_map, transpose_nonsing_inv, hS]

/-- `Π` is symmetric for every value of `m`. -/
private theorem comparison_piMat_transpose {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hSig : Sig.PosDef) (w : ℂ) : (piMat (N := N) Sig w)ᵀ = piMat (N := N) Sig w := by
  have hS : Sigᵀ = Sig := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact hSig.1.eq
  have hC : (cplx Sig)ᵀ = cplx Sig := by
    rw [cplx, ← transpose_map, hS]
  have hcomm : Commute (cplx Sig) (1 + w • cplx Sig) := by
    refine Commute.add_right (Commute.one_right _) ?_
    exact (Commute.refl _).smul_right _
  rw [piMat, fromBlocks_transpose]
  simp only [transpose_zero, transpose_neg, transpose_smul, transpose_one]
  congr 2
  rw [transpose_mul, transpose_nonsing_inv, transpose_add, transpose_one, transpose_smul, hC]
  by_cases hu : IsUnit (1 + w • cplx Sig).det
  · have hB := mul_nonsing_inv _ hu
    calc (1 + w • cplx Sig)⁻¹ * cplx Sig
        = (1 + w • cplx Sig)⁻¹ * cplx Sig * ((1 + w • cplx Sig) * (1 + w • cplx Sig)⁻¹) := by
          rw [hB, Matrix.mul_one]
      _ = (1 + w • cplx Sig)⁻¹ * (cplx Sig * (1 + w • cplx Sig)) * (1 + w • cplx Sig)⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = (1 + w • cplx Sig)⁻¹ * ((1 + w • cplx Sig) * cplx Sig) * (1 + w • cplx Sig)⁻¹ := by
          rw [hcomm.eq]
      _ = cplx Sig * (1 + w • cplx Sig)⁻¹ := by
          rw [← Matrix.mul_assoc _ (1 + w • cplx Sig) (cplx Sig), nonsing_inv_mul _ hu,
            Matrix.one_mul]
  · rw [nonsing_inv_apply_not_isUnit _ hu]
    simp

/-- `cvec v̄ = Σ̲⁻¹ cvec v`. -/
private theorem comparison_cvec_vbar {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (v : Fin M ⊕ Fin N → ℝ) : cvec (vbar Sig v) = (ulSigma N Sig)⁻¹ *ᵥ cvec v := by
  rw [comparison_ulSigma_inv hSig]
  funext s
  rcases s with i | j
  · simp [vbar, cvec, cplx, mulVec, dotProduct]
  · simp [vbar, cvec, fromBlocks_mulVec]

/-- `⟨v̄, (G − Π) w̄⟩ = ⟨v, Σ̲⁻¹(G − Π)Σ̲⁻¹ w⟩`. -/
theorem ent_vbar_eq_testBilin {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (v w : Fin M ⊕ Fin N → ℝ) :
    ent (G Sig A z - PiZ N Sig z) (vbar Sig v) (vbar Sig w) = testBilin v (lawMat Sig A z) w :=
  by
  have hT := comparison_ulSigma_inv_transpose (N := N) hSig
  have key : ∀ (S B : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ), Sᵀ = S →
      ∀ a b : Fin M ⊕ Fin N → ℂ, (S *ᵥ a) ⬝ᵥ (B *ᵥ (S *ᵥ b)) = a ⬝ᵥ ((S * B * S) *ᵥ b) := by
    intro S B hS a b
    rw [← vecMul_transpose, hS, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  unfold ent testBilin lawMat
  rw [comparison_cvec_vbar hSig v, comparison_cvec_vbar hSig w]
  exact key _ _ hT _ _

/-- `Σ̲⁻¹(G − Π)Σ̲⁻¹` is complex symmetric. -/
theorem lawMat_transpose {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) :
    (lawMat Sig A z)ᵀ = lawMat Sig A z := by
  have hT := comparison_ulSigma_inv_transpose (N := N) hSig
  unfold lawMat
  rw [transpose_mul, transpose_mul, hT, transpose_sub, G_transpose hSig A hz,
    comparison_piMat_transpose hSig, Matrix.mul_assoc]

/-- Polarization for a complex symmetric matrix and real test vectors. -/
theorem testBilin_polar {ι : Type*} [Fintype ι] (B : Matrix ι ι ℂ) (hB : Bᵀ = B)
    (v w : ι → ℝ) :
    testBilin v B w = (testBilin (v + w) B (v + w) - testBilin (v - w) B (v - w)) / 4 := by
  have hsym : (fun s => (w s : ℂ)) ⬝ᵥ (B *ᵥ fun t => (v t : ℂ)) =
      (fun s => (v s : ℂ)) ⬝ᵥ (B *ᵥ fun t => (w t : ℂ)) := by
    rw [dotProduct_mulVec, ← vecMul_transpose, hB, dotProduct_comm]
  have h1 : (fun s => (((v + w) s : ℝ) : ℂ)) =
      (fun s => (v s : ℂ)) + (fun s => (w s : ℂ)) := by
    funext s; simp
  have h2 : (fun s => (((v - w) s : ℝ) : ℂ)) =
      (fun s => (v s : ℂ)) - (fun s => (w s : ℂ)) := by
    funext s; simp
  unfold testBilin
  rw [h1, h2]
  simp only [mulVec_add, mulVec_sub, add_dotProduct, dotProduct_add, sub_dotProduct,
    dotProduct_sub]
  rw [hsym]
  ring

theorem Xupd_self (A : Matrix (Fin M) (Fin N) ℝ) (i : Fin M) (μ : Fin N) :
    Xupd A i μ (A i μ) = A := by
  funext j ν
  by_cases h : j = i ∧ ν = μ
  · obtain ⟨rfl, rfl⟩ := h
    simp [Xupd]
  · simp [Xupd, h]

theorem Xupd_eq_updEntry (A : Matrix (Fin M) (Fin N) ℝ) (i : Fin M) (μ : Fin N) (t : ℝ) :
    Xupd A i μ t = updEntry A i μ t := by
  funext j ν
  by_cases hj : j = i
  · subst hj
    by_cases hν : ν = μ
    · subst hν
      simp [Xupd, updEntry]
    · simp [Xupd, updEntry, hν]
  · simp [Xupd, updEntry, hj]

/-- `⟨v̄, (G − Π) w̄⟩ = ⟨v, Σ̲⁻¹(G − Π)Σ̲⁻¹ w⟩` at `M = N = 2`, `Σ = 1`, `z = i`. -/
example (A : Matrix (Fin 2) (Fin 2) ℝ) (v w : Fin 2 ⊕ Fin 2 → ℝ) :
    ent (G (1 : Matrix (Fin 2) (Fin 2) ℝ) A Complex.I - PiZ 2 (1 : Matrix (Fin 2) (Fin 2) ℝ)
        Complex.I) (vbar (1 : Matrix (Fin 2) (Fin 2) ℝ) v) (vbar (1 : Matrix (Fin 2) (Fin 2) ℝ) w) =
      testBilin v (lawMat (1 : Matrix (Fin 2) (Fin 2) ℝ) A Complex.I) w :=
  ent_vbar_eq_testBilin (N := 2) Matrix.PosDef.one A Complex.I v w

/-- `Σ̲⁻¹(G − Π)Σ̲⁻¹` is symmetric at `M = N = 2`, `Σ = 1`, `z = i` (`0 < Im z`). -/
example (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (lawMat (1 : Matrix (Fin 2) (Fin 2) ℝ) A Complex.I)ᵀ =
      lawMat (1 : Matrix (Fin 2) (Fin 2) ℝ) A Complex.I :=
  lawMat_transpose (N := 2) Matrix.PosDef.one A (by simp)

/-- Polarization at `B = 1` on `Fin 2`, `v = w = e₀`. -/
example :
    testBilin (eI (0 : Fin 2)) (1 : Matrix (Fin 2) (Fin 2) ℂ) (eI 0) =
      (testBilin (eI 0 + eI 0) (1 : Matrix (Fin 2) (Fin 2) ℂ) (eI 0 + eI 0) -
        testBilin (eI 0 - eI 0) (1 : Matrix (Fin 2) (Fin 2) ℂ) (eI 0 - eI 0)) / 4 :=
  testBilin_polar 1 transpose_one _ _

/-- `Xupd_self` at the `2 × 2` matrix `[[1, 2], [3, 4]]`, entry `(0, 1)`. -/
example : Xupd (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ) 0 1 2 = !![1, 2; 3, 4] :=
  Xupd_self (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ) 0 1

/-- `Xupd_eq_updEntry` at the `2 × 2` matrix `[[1, 2], [3, 4]]`, entry `(0, 1)`, value `5`. -/
example : Xupd (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ) 0 1 5 =
    updEntry (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ) 0 1 5 :=
  Xupd_eq_updEntry (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ) 0 1 5

end Anisotropic
