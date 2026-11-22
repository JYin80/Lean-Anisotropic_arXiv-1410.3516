module

public import Anisotropic.Density.GenProp
public import Anisotropic.Density.Stability.Domains
public import Anisotropic.Endpoints.Main
public import Anisotropic.Entrywise.Defs
public import Anisotropic.Framework.Domination
public import Anisotropic.Framework.Model
public import Anisotropic.Gaussian.Ensemble
public import Anisotropic.GeneralT.Main
public import Anisotropic.GeneralT.Model
public import Anisotropic.Instances.MarchenkoPasturTwo
public import Anisotropic.Instances.Models
public import Anisotropic.Probability.NormBound.GaussianLower
public import Anisotropic.Qdot.Defs

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # Theorem 11.2: the local laws for `Ġ`, under (T_diag) and for general `T` -/

section Algebra

/-- The all-ones `N × N` matrix `J = N e eᵀ`. -/
private abbrev llJ (N : ℕ) : Matrix (Fin N) (Fin N) ℂ := Matrix.of fun _ _ => 1

private theorem ll_cplx_piBar (N : ℕ) : cplx (piBar N) = 1 - (N : ℂ)⁻¹ • llJ N := by
  ext i j
  by_cases h : i = j <;> simp [piBar, cplx, llJ, h]

private theorem ll_J_mul_J (N : ℕ) : llJ N * llJ N = (N : ℂ) • llJ N := by
  ext i j
  simp [llJ, Matrix.mul_apply]

private theorem ll_P_mul_J {N : ℕ} (hN : N ≠ 0) : cplx (piBar N) * llJ N = 0 := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  rw [ll_cplx_piBar, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, ll_J_mul_J,
    smul_smul, inv_mul_cancel₀ hN', one_smul, sub_self]

private theorem ll_J_mul_P {N : ℕ} (hN : N ≠ 0) : llJ N * cplx (piBar N) = 0 := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  rw [ll_cplx_piBar, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, ll_J_mul_J,
    smul_smul, inv_mul_cancel₀ hN', one_smul, sub_self]

private theorem ll_transpose_P (N : ℕ) : (cplx (piBar N))ᵀ = cplx (piBar N) := by
  ext i j
  simp [piBar, cplx, Matrix.one_apply, eq_comm]

private theorem ll_J_mul_mul_J (R : Matrix (Fin N) (Fin N) ℂ) :
    llJ N * R * llJ N = ((fun _ => (1 : ℂ)) ⬝ᵥ (R *ᵥ fun _ => 1)) • llJ N := by
  ext i j
  simp only [llJ, Matrix.mul_apply, Matrix.of_apply, mul_one, one_mul,
    Matrix.smul_apply, smul_eq_mul, dotProduct, Matrix.mulVec]
  rw [Finset.sum_comm]

/-- The compression formula: if `(B − z) R = 1` and `g = 1ᵀ R 1 ≠ 0`, then
`(π̄ B π̄ − z)⁻¹ = R − g⁻¹ R J R − (zN)⁻¹ J`. -/
private theorem ll_compress {B R : Matrix (Fin N) (Fin N) ℂ} {z : ℂ} (hz : z ≠ 0) (hN : N ≠ 0)
    (hBR : (B - z • 1) * R = 1) (hg : (fun _ => (1 : ℂ)) ⬝ᵥ (R *ᵥ fun _ => 1) ≠ 0) :
    (cplx (piBar N) * B * cplx (piBar N) - z • 1)⁻¹ =
      R - ((fun _ => (1 : ℂ)) ⬝ᵥ (R *ᵥ fun _ => 1))⁻¹ • (R * llJ N * R) -
        (z * N)⁻¹ • llJ N := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  set g := (fun _ => (1 : ℂ)) ⬝ᵥ (R *ᵥ fun _ => 1) with hgdef
  set J := llJ N
  set P := cplx (piBar N) with hP
  set K := R - g⁻¹ • (R * J * R) with hK
  have hJRJ : J * R * J = g • J := ll_J_mul_mul_J R
  have hBR' : B * R = 1 + z • R := by
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul] at hBR
    rw [← hBR]; abel
  have hJK : J * K = 0 := by
    rw [hK, Matrix.mul_sub, Matrix.mul_smul]
    have : J * (R * J * R) = (J * R * J) * R := by simp only [Matrix.mul_assoc]
    rw [this, hJRJ, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hg, one_smul, sub_self]
  have hKJ : K * J = 0 := by
    rw [hK, Matrix.sub_mul, Matrix.smul_mul]
    have : R * J * R * J = R * (J * R * J) := by simp only [Matrix.mul_assoc]
    rw [this, hJRJ, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hg, one_smul, sub_self]
  have hPK : P * K = K := by
    rw [hP, ll_cplx_piBar, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, hJK, smul_zero,
      sub_zero]
  have hPJ : P * J = 0 := ll_P_mul_J hN
  have hBK : B * K = 1 - g⁻¹ • (J * R) + z • K := by
    have e : B * K = B * R - g⁻¹ • ((B * R) * J * R) := by
      rw [hK, Matrix.mul_sub, Matrix.mul_smul]; simp only [Matrix.mul_assoc]
    rw [e, hBR', hK]
    simp only [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, smul_add, smul_sub, smul_smul,
      Matrix.mul_assoc]
    rw [mul_comm g⁻¹ z]
    abel
  refine Matrix.inv_eq_right_inv ?_
  have e1 : (P * B * P - z • 1) * (K - (z * N)⁻¹ • J) =
      P * (B * (P * K)) - (z * N)⁻¹ • (P * (B * (P * J))) - z • K + ((z * N)⁻¹ * z) • J := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_assoc, smul_sub, smul_smul]
    abel
  rw [e1, hPK, hBK, hPJ]
  simp only [Matrix.mul_zero, smul_zero, sub_zero, Matrix.mul_add, Matrix.mul_sub,
    Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc, hPJ, Matrix.zero_mul, hPK]
  have hc : (z * N)⁻¹ * z = (N : ℂ)⁻¹ := by field_simp
  rw [hc, hP, ll_cplx_piBar]
  abel

end Algebra

section Resolvent

variable {K : ℕ}

private theorem ll_cplx_mul {p q r : Type*} [Fintype q] (A : Matrix p q ℝ) (B : Matrix q r ℝ) :
    cplx (A * B) = cplx A * cplx B := Matrix.map_mul

private theorem ll_cplx_transpose {p q : Type*} (A : Matrix p q ℝ) : cplx Aᵀ = (cplx A)ᵀ := by
  ext i j; rfl

/-- `XᵀTᵀTX = (TX)ᵀ(TX)` over `ℂ`. -/
private theorem ll_cplx_B (T : Matrix (Fin M) (Fin K) ℝ) (X : Matrix (Fin K) (Fin N) ℝ) :
    cplx (Xᵀ * Tᵀ * T * X) = (cplx (T * X))ᵀ * cplx (T * X) := by
  rw [← ll_cplx_transpose, ← ll_cplx_mul, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

/-- `TXXᵀTᵀ = (TX)(TX)ᵀ` over `ℂ`. -/
private theorem ll_cplx_BM (T : Matrix (Fin M) (Fin K) ℝ) (X : Matrix (Fin K) (Fin N) ℝ) :
    cplx (T * X * Xᵀ * Tᵀ) = cplx (T * X) * (cplx (T * X))ᵀ := by
  rw [← ll_cplx_transpose, ← ll_cplx_mul, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

private theorem ll_RN_isUnit (T : Matrix (Fin M) (Fin K) ℝ) (X : Matrix (Fin K) (Fin N) ℝ)
    {z : ℂ} (hz : 0 < z.im) :
    IsUnit (cplx (Xᵀ * Tᵀ * T * X) - z • (1 : Matrix (Fin N) (Fin N) ℂ)) := by
  have h := GN_isUnit (Matrix.PosDef.one : (1 : Matrix (Fin M) (Fin M) ℝ).PosDef) (T * X) hz
  rw [Matrix.mul_one, Matrix.transpose_mul, Matrix.mul_assoc] at h
  simpa only [Matrix.mul_assoc] using h

/-- `(XᵀTᵀTX − z) R_N = 1`. -/
private theorem ll_RN_mul (T : Matrix (Fin M) (Fin K) ℝ) (X : Matrix (Fin K) (Fin N) ℝ)
    {z : ℂ} (hz : 0 < z.im) :
    (cplx (Xᵀ * Tᵀ * T * X) - z • (1 : Matrix (Fin N) (Fin N) ℂ)) * RN T X z = 1 :=
  mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 (ll_RN_isUnit T X hz))

/-- `R_M = z⁻¹ (TX R_N (TX)ᵀ − 1)`. -/
private theorem ll_RM_eq (T : Matrix (Fin M) (Fin K) ℝ) (X : Matrix (Fin K) (Fin N) ℝ)
    {z : ℂ} (hz : 0 < z.im) :
    RM T X z = z⁻¹ • (cplx (T * X) * RN T X z * (cplx (T * X))ᵀ - 1) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hR := ll_RN_mul T X hz
  rw [ll_cplx_B, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul] at hR
  have hR' : (cplx (T * X))ᵀ * cplx (T * X) * RN T X z = 1 + z • RN T X z := by
    rw [← hR]; abel
  unfold RM
  refine Matrix.inv_eq_right_inv ?_
  rw [ll_cplx_BM]
  set Y := cplx (T * X)
  set R := RN T X z
  have e : (Y * Yᵀ - z • (1 : Matrix (Fin M) (Fin M) ℂ)) * (z⁻¹ • (Y * R * Yᵀ - 1)) =
      z⁻¹ • (Y * (Yᵀ * Y * R) * Yᵀ - Y * Yᵀ - z • (Y * R * Yᵀ) + z • 1) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, Matrix.mul_assoc, smul_sub, smul_add]
    abel
  rw [e, hR']
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul]
  rw [show Y * Yᵀ + z • (Y * R * Yᵀ) - Y * Yᵀ - z • (Y * R * Yᵀ) + z • (1 : Matrix _ _ ℂ) =
    z • 1 by abel, smul_smul, inv_mul_cancel₀ hz0, one_smul]

/-- `(TẊ) = (TX) π̄` over `ℂ`. -/
private theorem ll_cplx_TXdot (T : Matrix (Fin M) (Fin K) ℝ) (X : Matrix (Fin K) (Fin N) ℝ) :
    cplx (T * Xdot X) = cplx (T * X) * cplx (piBar N) := by
  rw [Xdot, ← Matrix.mul_assoc, ll_cplx_mul]

/-- `ẊᵀTᵀTẊ = π̄ XᵀTᵀTX π̄` over `ℂ`. -/
private theorem ll_cplx_Bdot (T : Matrix (Fin M) (Fin K) ℝ) (X : Matrix (Fin K) (Fin N) ℝ) :
    cplx ((Xdot X)ᵀ * Tᵀ * T * Xdot X) =
      cplx (piBar N) * cplx (Xᵀ * Tᵀ * T * X) * cplx (piBar N) := by
  rw [ll_cplx_B, ll_cplx_B, ll_cplx_TXdot, Matrix.transpose_mul, ll_transpose_P]
  simp only [Matrix.mul_assoc]

/-- `R_N(Ẋ) = R_N − g⁻¹ R_N J R_N − (zN)⁻¹ J`, `g = 1ᵀ R_N 1`. -/
private theorem ll_RN_dot (T : Matrix (Fin M) (Fin K) ℝ) (X : Matrix (Fin K) (Fin N) ℝ)
    {z : ℂ} (hz : 0 < z.im) (hN : N ≠ 0)
    (hg : (fun _ => (1 : ℂ)) ⬝ᵥ (RN T X z *ᵥ fun _ => 1) ≠ 0) :
    RN T (Xdot X) z = RN T X z -
      ((fun _ => (1 : ℂ)) ⬝ᵥ (RN T X z *ᵥ fun _ => 1))⁻¹ • (RN T X z * llJ N * RN T X z) -
        (z * N)⁻¹ • llJ N := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  unfold RN
  rw [ll_cplx_Bdot]
  exact ll_compress hz0 hN (ll_RN_mul T X hz) hg

end Resolvent

section BlockDot

variable {K : ℕ}

/-- The vector `(0, 1, …, 1) = √N (0, e)` of `ℂ^{𝓘}`. -/
private def llE (M N : ℕ) : Fin M ⊕ Fin N → ℂ := Sum.elim 0 fun _ => 1

private theorem ll_sigPow_transpose (Sig : Matrix (Fin M) (Fin M) ℝ) (r : ℝ) :
    (sigPow Sig r)ᵀ = sigPow Sig r := by
  rw [← conjTranspose_eq_transpose_of_trivial]
  exact (cfc_predicate (fun x : ℝ => if 0 < x then x ^ r else 0) Sig : IsSelfAdjoint _).star_eq

/-- The rank-one corrections in block form. -/
private theorem ll_fromBlocks_rankOne (A : Matrix (Fin M) (Fin M) ℂ) (B : Matrix (Fin M) (Fin N) ℂ)
    (C : Matrix (Fin N) (Fin M) ℂ) (D : Matrix (Fin N) (Fin N) ℂ) (g c : ℂ) :
    fromBlocks A B C D - g • vecMulVec (fromBlocks A B C D *ᵥ llE M N)
        (llE M N ᵥ* fromBlocks A B C D) - c • vecMulVec (llE M N) (llE M N) =
      fromBlocks (A - g • (B * llJ N * C)) (B - g • (B * llJ N * D)) (C - g • (D * llJ N * C))
        (D - g • (D * llJ N * D) - c • llJ N) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [llE, llJ, vecMulVec_apply, fromBlocks_mulVec, vecMul_fromBlocks, Matrix.mul_apply,
      Matrix.mulVec, Matrix.vecMul, dotProduct, Finset.sum_mul, Finset.mul_sum]

/-- `π̄ K = K = K π̄` for `K = R − g⁻¹ R J R`, `g = 1ᵀ R 1 ≠ 0`. -/
private theorem ll_P_K {R : Matrix (Fin N) (Fin N) ℂ}
    (hg : (fun _ => (1 : ℂ)) ⬝ᵥ (R *ᵥ fun _ => 1) ≠ 0) :
    cplx (piBar N) * (R - ((fun _ => (1 : ℂ)) ⬝ᵥ (R *ᵥ fun _ => 1))⁻¹ • (R * llJ N * R)) =
        R - ((fun _ => (1 : ℂ)) ⬝ᵥ (R *ᵥ fun _ => 1))⁻¹ • (R * llJ N * R) ∧
      (R - ((fun _ => (1 : ℂ)) ⬝ᵥ (R *ᵥ fun _ => 1))⁻¹ • (R * llJ N * R)) * cplx (piBar N) =
        R - ((fun _ => (1 : ℂ)) ⬝ᵥ (R *ᵥ fun _ => 1))⁻¹ • (R * llJ N * R) := by
  set g := (fun _ => (1 : ℂ)) ⬝ᵥ (R *ᵥ fun _ => 1)
  have hJRJ : llJ N * R * llJ N = g • llJ N := ll_J_mul_mul_J R
  constructor
  · rw [ll_cplx_piBar, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_sub,
      Matrix.mul_smul]
    have : llJ N * (R * llJ N * R) = (llJ N * R * llJ N) * R := by simp only [Matrix.mul_assoc]
    rw [this, hJRJ, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hg, one_smul, sub_self,
      smul_zero, sub_zero]
  · rw [ll_cplx_piBar, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, Matrix.sub_mul,
      Matrix.smul_mul]
    have : R * llJ N * R * llJ N = R * (llJ N * R * llJ N) := by simp only [Matrix.mul_assoc]
    rw [this, hJRJ, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hg, one_smul, sub_self,
      smul_zero, sub_zero]

/-- The Schur identity for `G(Ẋ)` of (def_block_G):
`G(Ẋ) = G − g⁻¹ (G ε)(εᵀ G) − (zN)⁻¹ ε εᵀ` with `ε = (0, 1, …, 1)` and `g = εᵀ G ε = 1ᵀ R_N 1`
(the three block identities in the proof of Theorem 11.2). -/
private theorem ll_blockG_dot (T : Matrix (Fin M) (Fin K) ℝ) (X : Matrix (Fin K) (Fin N) ℝ)
    {z : ℂ} (hz : 0 < z.im) (hN : N ≠ 0)
    (hg : (fun _ => (1 : ℂ)) ⬝ᵥ (RN T X z *ᵥ fun _ => 1) ≠ 0) :
    blockG T (Xdot X) z = blockG T X z -
      ((fun _ => (1 : ℂ)) ⬝ᵥ (RN T X z *ᵥ fun _ => 1))⁻¹ •
        vecMulVec (blockG T X z *ᵥ llE M N) (llE M N ᵥ* blockG T X z) -
      (z * N)⁻¹ • vecMulVec (llE M N) (llE M N) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  set g := (fun _ => (1 : ℂ)) ⬝ᵥ (RN T X z *ᵥ fun _ => 1) with hgdef
  set R := RN T X z with hR
  set Kd := R - g⁻¹ • (R * llJ N * R) with hKd
  obtain ⟨hPK, hKP⟩ := ll_P_K (R := R) hg
  rw [← hgdef, ← hKd] at hPK hKP
  have hPJ := ll_P_mul_J hN
  have hJP := ll_J_mul_P hN
  have hRd : RN T (Xdot X) z = Kd - (z * N)⁻¹ • llJ N := ll_RN_dot T X hz hN hg
  set Sq := sigPow (T * Tᵀ) (1 / 2) with hSq
  have hSt : Sqᵀ = Sq := ll_sigPow_transpose _ _
  set P := cplx (piBar N) with hP
  have hPt : Pᵀ = P := ll_transpose_P N
  set Y := cplx (T * X) with hY
  set S := cplx Sq with hS
  have hSYt : cplx (Sq * T * X)ᵀ = Yᵀ * S := by
    rw [Matrix.mul_assoc, Matrix.transpose_mul, ll_cplx_mul, ll_cplx_transpose, hSt]
  have hSY : cplx (Sq * T * X) = S * Y := by rw [Matrix.mul_assoc, ll_cplx_mul]
  have hSYd : cplx (Sq * T * Xdot X) = S * Y * P := by
    rw [Matrix.mul_assoc, ll_cplx_mul, ll_cplx_TXdot, Matrix.mul_assoc]
  have hSYdt : cplx (Sq * T * Xdot X)ᵀ = P * (Yᵀ * S) := by
    rw [Matrix.mul_assoc, Matrix.transpose_mul, ll_cplx_mul, ll_cplx_transpose, hSt,
      ll_cplx_TXdot, Matrix.transpose_mul, hPt, Matrix.mul_assoc]
  have hPRP : P * RN T (Xdot X) z * P = Kd := by
    rw [hRd, Matrix.mul_sub, Matrix.sub_mul, hPK, hKP, Matrix.mul_smul, hPJ, smul_zero,
      Matrix.zero_mul, sub_zero]
  have hM0 : z • (S * RM T X z * S) = S * (Y * R * Yᵀ) * S - S * S := by
    rw [ll_RM_eq T X hz, ← hR, ← hY]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hz0, one_smul,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  have hM1 : z • (S * RM T (Xdot X) z * S) = S * (Y * Kd * Yᵀ) * S - S * S := by
    rw [ll_RM_eq T (Xdot X) hz, ll_cplx_TXdot, ← hY, ← hP]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hz0, one_smul,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.transpose_mul, hPt]
    rw [show Y * P * RN T (Xdot X) z * (P * Yᵀ) = Y * (P * RN T (Xdot X) z * P) * Yᵀ by
      simp only [Matrix.mul_assoc], hPRP]
  have e0 : blockG T X z = fromBlocks (z • (S * RM T X z * S)) (S * Y * R) (R * (Yᵀ * S)) R := by
    simp only [blockG, ← hSq, ← hS, hSY, hSYt, ← hR]
  rw [e0, ll_fromBlocks_rankOne]
  simp only [blockG, ← hSq, ← hS, hSYd, hSYdt]
  rw [hM1, hM0, fromBlocks_inj]
  have hPK' : ∀ {p : Type} (A : Matrix p (Fin N) ℂ), A * P * Kd = A * Kd := fun A => by
    rw [Matrix.mul_assoc, hPK]
  have hPJ' : ∀ {p : Type} (A : Matrix p (Fin N) ℂ), A * P * llJ N = 0 := fun A => by
    rw [Matrix.mul_assoc, hPJ, Matrix.mul_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hKd]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    abel
  · rw [hRd, Matrix.mul_sub, Matrix.mul_smul, hPK', hPJ', smul_zero, sub_zero, hKd]
    simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_assoc]
  · rw [hRd, Matrix.sub_mul, Matrix.smul_mul, ← Matrix.mul_assoc Kd P, hKP,
      ← Matrix.mul_assoc (llJ N) P, hJP, Matrix.zero_mul, smul_zero, sub_zero, hKd]
    simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc]
  · rw [hRd]

/-- `R_N` is complex symmetric. -/
private theorem ll_RN_transpose (T : Matrix (Fin M) (Fin K) ℝ) (X : Matrix (Fin K) (Fin N) ℝ)
    (z : ℂ) : (RN T X z)ᵀ = RN T X z := by
  unfold RN
  rw [Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_one, ← ll_cplx_transpose]
  congr 3
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

/-- The Ward identity for `w = R_N 1`: `Im (1ᵀ R_N 1) = η |w|²`; and `1ᵀ R_N² 1 = tr (R_N J R_N)
= ∑ w_μ²`. -/
private theorem ll_ward (T : Matrix (Fin M) (Fin K) ℝ) (X : Matrix (Fin K) (Fin N) ℝ)
    {z : ℂ} (hz : 0 < z.im) :
    ((fun _ => (1 : ℂ)) ⬝ᵥ (RN T X z *ᵥ fun _ => 1)).im =
        z.im * ∑ i, ‖(RN T X z *ᵥ fun _ => (1 : ℂ)) i‖ ^ 2 ∧
      trace (RN T X z * llJ N * RN T X z) = ∑ i, (RN T X z *ᵥ fun _ => (1 : ℂ)) i ^ 2 ∧
      (N ≠ 0 → 0 < ∑ i, ‖(RN T X z *ᵥ fun _ => (1 : ℂ)) i‖ ^ 2) := by
  set R := RN T X z with hR
  set w : Fin N → ℂ := R *ᵥ fun _ => 1 with hw
  set B := cplx (Xᵀ * Tᵀ * T * X) with hB
  have hBh : B.IsHermitian := by
    have h : (Xᵀ * Tᵀ * T * X).IsHermitian := by
      have := Matrix.isHermitian_conjTranspose_mul_self (T * X)
      simp only [conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul] at this
      simpa only [Matrix.mul_assoc] using this
    exact h.map _ (fun x => by simp)
  have hBw : (B - z • (1 : Matrix (Fin N) (Fin N) ℂ)) *ᵥ w = fun _ => 1 := by
    rw [hw, Matrix.mulVec_mulVec, hR, ll_RN_mul T X hz, Matrix.one_mulVec]
  have hBw' : B *ᵥ w = (fun _ => (1 : ℂ)) + z • w := by
    have := hBw
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at this
    rw [← this]
    abel
  have hww : star w ⬝ᵥ w = ((∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ) := by
    simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RCLike.star_def, Complex.conj_mul']
  have e1 : star w ⬝ᵥ (fun _ => (1 : ℂ)) = star w ⬝ᵥ (B *ᵥ w) - z * (star w ⬝ᵥ w) := by
    rw [hBw', dotProduct_add, dotProduct_smul, smul_eq_mul]
    ring
  have e2 : star w ⬝ᵥ (fun _ => (1 : ℂ)) = star ((fun _ => (1 : ℂ)) ⬝ᵥ w) := by
    simp [dotProduct, star_sum]
  have him : (star w ⬝ᵥ (B *ᵥ w)).im = 0 := hBh.im_star_dotProduct_mulVec_self w
  refine ⟨?_, ?_, ?_⟩
  · have h := congrArg Complex.im (e2.symm.trans e1)
    rw [Complex.sub_im, him, Complex.mul_im, hww, Complex.ofReal_re, Complex.ofReal_im] at h
    have hst : (star ((fun _ => (1 : ℂ)) ⬝ᵥ w)).im = -((fun _ => (1 : ℂ)) ⬝ᵥ w).im := by
      rw [RCLike.star_def, Complex.conj_im]
    rw [hst] at h
    linarith
  · have hRt : Rᵀ = R := ll_RN_transpose T X z
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, llJ, Matrix.of_apply, mul_one, hw,
      Matrix.mulVec, dotProduct, sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    have : R k i = R i k := congrFun (congrFun hRt i) k
    rw [this, mul_comm]
  · intro hN
    by_contra hneg
    have h0 : ∑ i, ‖w i‖ ^ 2 = 0 :=
      le_antisymm (not_lt.mp hneg) (Finset.sum_nonneg fun i _ => by positivity)
    have hw0 : w = 0 := by
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1 h0 i
        (Finset.mem_univ _)
      simpa using this
    have := congrFun hBw ⟨0, Nat.pos_of_ne_zero hN⟩
    rw [hw0, Matrix.mulVec_zero] at this
    simp at this

/-- `g = 1ᵀ R_N 1 ≠ 0` for `N ≥ 1`. -/
private theorem ll_g_ne_zero (T : Matrix (Fin M) (Fin K) ℝ) (X : Matrix (Fin K) (Fin N) ℝ)
    {z : ℂ} (hz : 0 < z.im) (hN : N ≠ 0) :
    (fun _ => (1 : ℂ)) ⬝ᵥ (RN T X z *ᵥ fun _ => 1) ≠ 0 := by
  obtain ⟨h1, -, h3⟩ := ll_ward T X hz
  intro h
  rw [h, Complex.zero_im] at h1
  have := mul_pos hz (h3 hN)
  linarith

end BlockDot

section Bilin

variable {K : ℕ}

/-- The real vector `(0, 1, …, 1)` of `ℝ^{𝓘}`. -/
private def llEr (M N : ℕ) : Fin M ⊕ Fin N → ℝ := Sum.elim 0 fun _ => 1

private theorem ll_E_cast : (fun s => ((llEr M N s : ℝ) : ℂ)) = llE M N := by
  funext s; cases s <;> simp [llEr, llE]

private theorem ll_testBilin_vecMulVec {ι : Type*} [Fintype ι] (v u : ι → ℝ) (p q : ι → ℂ) :
    testBilin v (vecMulVec p q) u =
      ((fun s => (v s : ℂ)) ⬝ᵥ p) * (q ⬝ᵥ fun t => (u t : ℂ)) := by
  unfold testBilin
  simp only [dotProduct, Matrix.mulVec, vecMulVec_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem ll_testBilin_sub {ι : Type*} [Fintype ι] (v u : ι → ℝ) (A B : Matrix ι ι ℂ) :
    testBilin v (A - B) u = testBilin v A u - testBilin v B u := by
  simp [testBilin, Matrix.sub_mulVec, dotProduct_sub]

private theorem ll_testBilin_add {ι : Type*} [Fintype ι] (v u : ι → ℝ) (A B : Matrix ι ι ℂ) :
    testBilin v (A + B) u = testBilin v A u + testBilin v B u := by
  simp [testBilin, Matrix.add_mulVec, dotProduct_add]

private theorem ll_testBilin_smul {ι : Type*} [Fintype ι] (v u : ι → ℝ) (c : ℂ)
    (A : Matrix ι ι ℂ) : testBilin v (c • A) u = c * testBilin v A u := by
  simp [testBilin, Matrix.smul_mulVec, dotProduct_smul]

/-- `⟨v, (0, 1)⟩ = ∑_μ v_μ`. -/
private theorem ll_dot_E (v : Fin M ⊕ Fin N → ℝ) :
    (fun s => (v s : ℂ)) ⬝ᵥ llE M N = ∑ μ, (v (Sum.inr μ) : ℂ) := by
  simp [dotProduct, llE, Fintype.sum_sum_type]

private theorem ll_E_dot (v : Fin M ⊕ Fin N → ℝ) :
    llE M N ⬝ᵥ (fun s => (v s : ℂ)) = ∑ μ, (v (Sum.inr μ) : ℂ) := by
  simp [dotProduct, llE, Fintype.sum_sum_type]

private theorem ll_piMat_E (Sig : Matrix (Fin M) (Fin M) ℝ) (w : ℂ) :
    piMat (N := N) Sig w *ᵥ llE M N = w • llE M N ∧
      llE M N ᵥ* piMat (N := N) Sig w = w • llE M N := by
  constructor <;> (funext s; cases s) <;>
    simp [piMat, llE, Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.one_apply]

/-- `fromBlocks 0 0 0 (1 − π̄) = N⁻¹ ε εᵀ`. -/
private theorem ll_F_eq (N : ℕ) :
    fromBlocks (0 : Matrix (Fin M) (Fin M) ℂ) 0 0 (cplx (1 - piBar N)) =
      (N : ℂ)⁻¹ • vecMulVec (llE M N) (llE M N) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [llE, vecMulVec_apply, piBar, cplx]

/-- `εᵀ G ε = 1ᵀ R_N 1`. -/
private theorem ll_g_eq (T : Matrix (Fin M) (Fin K) ℝ) (X : Matrix (Fin K) (Fin N) ℝ) (z : ℂ) :
    llE M N ⬝ᵥ (blockG T X z *ᵥ llE M N) = (fun _ => (1 : ℂ)) ⬝ᵥ (RN T X z *ᵥ fun _ => 1) := by
  simp [blockG, llE, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type, Function.comp_def]
  simp only [show (fun _ : Fin M => (0 : ℂ)) = 0 from rfl, Matrix.mulVec_zero, Pi.zero_apply,
    zero_add]

/-- The bilinear form of Theorem 11.2's Schur identity: with `ℓ(x, y) = ⟨x, (G − Π) y⟩`,
`α = ⟨v, ε⟩`, `β = ⟨ε, u⟩` and `g = ℓ(ε, ε) + mN`,
`⟨v, (Ġ − Π̇) u⟩ = ℓ(v, u) − g⁻¹ (ℓ(v, ε) + mα)(ℓ(ε, u) + mβ) + (m/N) αβ`. -/
private theorem ll_testBilin_dot (T : Matrix (Fin M) (Fin K) ℝ) (X : Matrix (Fin K) (Fin N) ℝ)
    {z : ℂ} (hz : 0 < z.im) (hN : N ≠ 0) (m : ℂ) (v u : Fin M ⊕ Fin N → ℝ) :
    testBilin v (blockG T (Xdot X) z - piMatDot (T * Tᵀ) m z) u =
      testBilin v (blockG T X z - piMat (T * Tᵀ) m) u -
        (testBilin (llEr M N) (blockG T X z - piMat (T * Tᵀ) m) (llEr M N) + m * N)⁻¹ *
          (testBilin v (blockG T X z - piMat (T * Tᵀ) m) (llEr M N) +
            m * ∑ μ, (v (Sum.inr μ) : ℂ)) *
          (testBilin (llEr M N) (blockG T X z - piMat (T * Tᵀ) m) u +
            m * ∑ μ, (u (Sum.inr μ) : ℂ)) +
        m / N * (∑ μ, (v (Sum.inr μ) : ℂ)) * ∑ μ, (u (Sum.inr μ) : ℂ) := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hg := ll_g_ne_zero T X hz hN
  obtain ⟨hPie, hePi⟩ := ll_piMat_E (N := N) (T * Tᵀ) m
  set G0 := blockG T X z
  set Pi0 := piMat (N := N) (T * Tᵀ) m
  set α := ∑ μ, (v (Sum.inr μ) : ℂ)
  set β := ∑ μ, (u (Sum.inr μ) : ℂ)
  have hEE : llE M N ⬝ᵥ llE M N = N := by simp [llE, dotProduct, Fintype.sum_sum_type]
  have h1 : testBilin v G0 (llEr M N) = (fun s => (v s : ℂ)) ⬝ᵥ (G0 *ᵥ llE M N) := by
    rw [testBilin, ll_E_cast]
  have h2 : testBilin (llEr M N) G0 u = (llE M N ᵥ* G0) ⬝ᵥ (fun t => (u t : ℂ)) := by
    rw [testBilin, ll_E_cast, Matrix.dotProduct_mulVec]
  have h3 : testBilin v Pi0 (llEr M N) = m * α := by
    rw [testBilin, ll_E_cast, hPie, dotProduct_smul, ll_dot_E, smul_eq_mul]
  have h4 : testBilin (llEr M N) Pi0 u = m * β := by
    rw [testBilin, ll_E_cast, Matrix.dotProduct_mulVec, hePi, smul_dotProduct, ll_E_dot,
      smul_eq_mul]
  have h5 : testBilin (llEr M N) G0 (llEr M N) =
      (fun _ => (1 : ℂ)) ⬝ᵥ (RN T X z *ᵥ fun _ => 1) := by
    rw [testBilin, ll_E_cast, ll_g_eq]
  have h6 : testBilin (llEr M N) Pi0 (llEr M N) = m * N := by
    rw [testBilin, ll_E_cast, hPie, dotProduct_smul, hEE, smul_eq_mul]
  have hEv : testBilin v (vecMulVec (llE M N) (llE M N)) u = α * β := by
    rw [ll_testBilin_vecMulVec, ll_dot_E, ll_E_dot]
  have hdot : blockG T (Xdot X) z - piMatDot (T * Tᵀ) m z =
      (G0 - Pi0) - ((fun _ => (1 : ℂ)) ⬝ᵥ (RN T X z *ᵥ fun _ => 1))⁻¹ •
          vecMulVec (G0 *ᵥ llE M N) (llE M N ᵥ* G0) +
        (m / N) • vecMulVec (llE M N) (llE M N) := by
    rw [ll_blockG_dot T X hz hN hg, piMatDot, ll_F_eq, smul_smul]
    have : (m + z⁻¹) * (N : ℂ)⁻¹ = (z * N)⁻¹ + m / N := by field_simp; ring
    rw [this, add_smul]
    abel
  rw [hdot, ll_testBilin_add, ll_testBilin_sub, ll_testBilin_smul, ll_testBilin_smul,
    ll_testBilin_vecMulVec, hEv, ← h1, ← h2]
  simp only [ll_testBilin_sub, h3, h4, h5, h6, sub_add_cancel]
  ring

/-- The trace form: `ṁ_N = m_N − N⁻¹ (g⁻¹ tr (R_N J R_N) + z⁻¹)` for a general `T`. -/
private theorem ll_mNT_dot (T : Matrix (Fin M) (Fin K) ℝ) (X : Matrix (Fin K) (Fin N) ℝ)
    {z : ℂ} (hz : 0 < z.im) (hN : N ≠ 0) :
    mNT T (Xdot X) z = mNT T X z - (N : ℂ)⁻¹ *
      (((fun _ => (1 : ℂ)) ⬝ᵥ (RN T X z *ᵥ fun _ => 1))⁻¹ * trace (RN T X z * llJ N * RN T X z) +
        z⁻¹) := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hJ : trace (llJ N) = N := by simp [Matrix.trace, llJ]
  unfold mNT
  rw [ll_RN_dot T X hz hN (ll_g_ne_zero T X hz hN), Matrix.trace_sub, Matrix.trace_sub,
    Matrix.trace_smul, Matrix.trace_smul, hJ, smul_eq_mul, smul_eq_mul]
  field_simp
  ring

/-- `|ṁ_N − m_N| ≤ N⁻¹ (η⁻¹ + |z|⁻¹)`, deterministically (the Ward identity). -/
private theorem ll_mNT_dot_le (T : Matrix (Fin M) (Fin K) ℝ) (X : Matrix (Fin K) (Fin N) ℝ)
    {z : ℂ} (hz : 0 < z.im) (hN : N ≠ 0) :
    ‖mNT T (Xdot X) z - mNT T X z‖ ≤ (z.im⁻¹ + ‖z‖⁻¹) / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  obtain ⟨hIm, htr, hW⟩ := ll_ward T X hz
  set g := (fun _ => (1 : ℂ)) ⬝ᵥ (RN T X z *ᵥ fun _ => 1)
  set W := ∑ i, ‖(RN T X z *ᵥ fun _ => (1 : ℂ)) i‖ ^ 2
  have hW0 : 0 < W := hW hN
  have hg : g ≠ 0 := ll_g_ne_zero T X hz hN
  have hgn : z.im * W ≤ ‖g‖ := by rw [← hIm]; exact Complex.im_le_norm g
  have htr' : ‖trace (RN T X z * llJ N * RN T X z)‖ ≤ W := by
    rw [htr]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp only [norm_pow]
    rfl
  have h1 : ‖g⁻¹ * trace (RN T X z * llJ N * RN T X z)‖ ≤ z.im⁻¹ := by
    rw [norm_mul, norm_inv]
    have hgpos : 0 < ‖g‖ := norm_pos_iff.mpr hg
    rw [inv_mul_le_iff₀ hgpos]
    calc ‖trace (RN T X z * llJ N * RN T X z)‖ ≤ W := htr'
      _ = z.im⁻¹ * (z.im * W) := by field_simp
      _ ≤ ‖g‖ * z.im⁻¹ := by
        rw [mul_comm ‖g‖]; exact mul_le_mul_of_nonneg_left hgn (inv_nonneg.mpr hz.le)
  rw [ll_mNT_dot T X hz hN, sub_sub_cancel_left, norm_neg, norm_mul, norm_inv,
    Complex.norm_natCast, inv_mul_eq_div]
  refine div_le_div_of_nonneg_right ?_ hN0.le
  refine (norm_add_le _ _).trans (add_le_add h1 (le_of_eq (norm_inv z)))

/-- The scalar estimate behind the anisotropic law for `Ġ`. -/
private theorem ll_scalar_bound {lvu lve leu lee m α β : ℂ} {δ a b s Cm : ℝ} (hs : 0 < s)
    (hδ0 : 0 ≤ δ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hCm : 0 < Cm)
    (h1 : ‖lvu‖ ≤ δ * a * b) (h2 : ‖lve‖ ≤ δ * a * s) (h3 : ‖leu‖ ≤ δ * s * b)
    (h4 : ‖lee‖ ≤ δ * s * s) (hα : ‖α‖ ≤ s * a) (hβ : ‖β‖ ≤ s * b) (hm1 : Cm⁻¹ ≤ ‖m‖)
    (hm2 : ‖m‖ ≤ Cm) (hδ : δ ≤ Cm⁻¹ / 2) :
    ‖lvu - (lee + m * ((s * s : ℝ) : ℂ))⁻¹ * (lve + m * α) * (leu + m * β) +
        m / ((s * s : ℝ) : ℂ) * α * β‖ ≤ (2 + 6 * Cm ^ 2) * δ * a * b := by
  set n : ℝ := s * s with hn
  have hn0 : 0 < n := mul_pos hs hs
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  set g := lee + m * (n : ℂ) with hg
  have hgl : n / (2 * Cm) ≤ ‖g‖ := by
    have e1 : ‖m * (n : ℂ)‖ = ‖m‖ * n := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hn0.le]
    have e2 : ‖m * (n : ℂ)‖ ≤ ‖g‖ + ‖lee‖ := by
      have : m * (n : ℂ) = g - lee := by rw [hg]; ring
      rw [this]; exact norm_sub_le _ _
    have e3 : Cm⁻¹ * n ≤ ‖m‖ * n := mul_le_mul_of_nonneg_right hm1 hn0.le
    have e4 : δ * n ≤ Cm⁻¹ / 2 * n := mul_le_mul_of_nonneg_right hδ hn0.le
    have e5 : n / (2 * Cm) = Cm⁻¹ * n - Cm⁻¹ / 2 * n := by field_simp; ring
    rw [e5]
    have : ‖lee‖ ≤ δ * n := by rw [hn]; linarith [h4]
    linarith
  have hgpos : 0 < ‖g‖ := lt_of_lt_of_le (by positivity) hgl
  have hg0 : g ≠ 0 := norm_pos_iff.mp hgpos
  have hginv : ‖g⁻¹‖ ≤ 2 * Cm / n := by
    rw [norm_inv]
    rw [inv_le_comm₀ hgpos (by positivity)]
    calc (2 * Cm / n)⁻¹ = n / (2 * Cm) := by rw [inv_div]
      _ ≤ ‖g‖ := hgl
  have e : lvu - g⁻¹ * (lve + m * α) * (leu + m * β) + m / (n : ℂ) * α * β =
      lvu - g⁻¹ * lve * leu - g⁻¹ * m * α * leu - g⁻¹ * m * β * lve +
        g⁻¹ * (n : ℂ)⁻¹ * m * α * β * lee := by
    field_simp
    rw [hg]
    ring
  rw [e]
  have hCm2 : 2 * Cm * δ ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hδ (by positivity : (0 : ℝ) ≤ 2 * Cm)
    rwa [show 2 * Cm * (Cm⁻¹ / 2) = 1 by field_simp] at this
  have t1 : ‖g⁻¹ * lve * leu‖ ≤ δ * a * b := by
    rw [norm_mul, norm_mul]
    calc ‖g⁻¹‖ * ‖lve‖ * ‖leu‖ ≤ (2 * Cm / n) * (δ * a * s) * (δ * s * b) := by
          gcongr
      _ = (2 * Cm * δ) * (δ * a * b) := by rw [hn]; field_simp
      _ ≤ 1 * (δ * a * b) := by gcongr
      _ = δ * a * b := one_mul _
  have t2 : ‖g⁻¹ * m * α * leu‖ ≤ 2 * Cm ^ 2 * δ * a * b := by
    rw [norm_mul, norm_mul, norm_mul]
    calc ‖g⁻¹‖ * ‖m‖ * ‖α‖ * ‖leu‖ ≤ (2 * Cm / n) * Cm * (s * a) * (δ * s * b) := by
          gcongr
      _ = 2 * Cm ^ 2 * δ * a * b := by rw [hn]; field_simp
  have t3 : ‖g⁻¹ * m * β * lve‖ ≤ 2 * Cm ^ 2 * δ * a * b := by
    rw [norm_mul, norm_mul, norm_mul]
    calc ‖g⁻¹‖ * ‖m‖ * ‖β‖ * ‖lve‖ ≤ (2 * Cm / n) * Cm * (s * b) * (δ * a * s) := by
          gcongr
      _ = 2 * Cm ^ 2 * δ * a * b := by rw [hn]; field_simp
  have t4 : ‖g⁻¹ * (n : ℂ)⁻¹ * m * α * β * lee‖ ≤ 2 * Cm ^ 2 * δ * a * b := by
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_inv (n : ℂ), Complex.norm_real,
      Real.norm_of_nonneg hn0.le]
    calc ‖g⁻¹‖ * n⁻¹ * ‖m‖ * ‖α‖ * ‖β‖ * ‖lee‖ ≤
        (2 * Cm / n) * n⁻¹ * Cm * (s * a) * (s * b) * (δ * s * s) := by gcongr
      _ = 2 * Cm ^ 2 * δ * a * b := by rw [hn]; field_simp
  calc ‖lvu - g⁻¹ * lve * leu - g⁻¹ * m * α * leu - g⁻¹ * m * β * lve +
        g⁻¹ * (n : ℂ)⁻¹ * m * α * β * lee‖
      ≤ ‖lvu‖ + ‖g⁻¹ * lve * leu‖ + ‖g⁻¹ * m * α * leu‖ + ‖g⁻¹ * m * β * lve‖ +
          ‖g⁻¹ * (n : ℂ)⁻¹ * m * α * β * lee‖ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
        exact norm_sub_le _ _
    _ ≤ δ * a * b + δ * a * b + 2 * Cm ^ 2 * δ * a * b + 2 * Cm ^ 2 * δ * a * b +
          2 * Cm ^ 2 * δ * a * b := by gcongr
    _ = (2 + 6 * Cm ^ 2) * δ * a * b := by ring

end Bilin

section Estimates

/-- `|∑_μ v_μ| ≤ √N |Σ̲ v|`. -/
private theorem ll_alpha_le (Sig : Matrix (Fin M) (Fin M) ℝ) (v : Fin M ⊕ Fin N → ℝ) :
    ‖∑ μ, (v (Sum.inr μ) : ℂ)‖ ≤ √(N : ℝ) * testNorm (SigU (n := Fin N) Sig *ᵥ v) := by
  have hy : ∀ μ, (SigU (n := Fin N) Sig *ᵥ v) (Sum.inr μ) = v (Sum.inr μ) := by
    intro μ
    simp [SigU, Matrix.mulVec, dotProduct, Matrix.one_apply]
  have e : ‖∑ μ, (v (Sum.inr μ) : ℂ)‖ = |∑ μ, v (Sum.inr μ)| := by
    rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
  rw [e]
  have hcs : (∑ μ, v (Sum.inr μ)) ^ 2 ≤ (N : ℝ) * ∑ μ, v (Sum.inr μ) ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin N => (1 : ℝ))
      (fun μ => v (Sum.inr μ))
    simpa using this
  have hsub : ∑ μ, v (Sum.inr μ) ^ 2 ≤ ∑ s, (SigU (n := Fin N) Sig *ᵥ v) s ^ 2 := by
    rw [Fintype.sum_sum_type]
    simp only [hy]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun i _ => sq_nonneg _)
  rw [testNorm, ← Real.sqrt_mul (Nat.cast_nonneg N), ← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt (hcs.trans ?_)
  exact mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg N)

private theorem ll_SigU_E (Sig : Matrix (Fin M) (Fin M) ℝ) :
    SigU (n := Fin N) Sig *ᵥ llEr M N = llEr M N := by
  funext s
  cases s <;> simp [SigU, llEr, Matrix.mulVec, dotProduct, Matrix.one_apply]

private theorem ll_testNorm_E : testNorm (llEr M N) = √(N : ℝ) := by
  simp [testNorm, llEr, Fintype.sum_sum_type]

/-- `A ≤ N^a` once `⌈A^{1/a}⌉ ≤ N`. -/
private theorem ll_le_rpow {A a : ℝ} (hA : 0 ≤ A) (ha : 0 < a) {N : ℕ}
    (hN : ⌈A ^ (1 / a)⌉₊ ≤ N) : A ≤ (N : ℝ) ^ a := by
  have h1 : A ^ (1 / a) ≤ (N : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hN)
  calc A = (A ^ (1 / a)) ^ a := by
        rw [← Real.rpow_mul hA, one_div_mul_cancel ha.ne', Real.rpow_one]
    _ ≤ (N : ℝ) ^ a := Real.rpow_le_rpow (Real.rpow_nonneg hA _) h1 ha.le

/-- The denominator row: `N^{ε₁} Ψ ≤ c_m / 2` on `𝐃(τ, N)` once `N^{τ/4} ≥ 2 C_m (√C_m + 1)`. -/
private theorem ll_delta_le {N : ℕ} (hN : 1 ≤ N) {τ ε₁ Cm η mi : ℝ} (hτ : 0 < τ)
    (hε₁ : ε₁ ≤ τ / 4) (hCm : 0 < Cm) (hη0 : 0 < η) (hη : (N : ℝ) ^ (-1 + τ) ≤ η)
    (hmi : mi ≤ Cm) (hq : 2 * Cm * (√Cm + 1) ≤ (N : ℝ) ^ (τ / 4)) :
    (N : ℝ) ^ ε₁ * (√(mi / (N * η)) + 1 / (N * η)) ≤ Cm⁻¹ / 2 := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set q := (N : ℝ) ^ (τ / 4) with hqdef
  have hq1 : 1 ≤ q := Real.one_le_rpow hN1 (by positivity)
  have hq0 : 0 < q := by linarith
  have hNε : (N : ℝ) ^ ε₁ ≤ q := Real.rpow_le_rpow_of_exponent_le hN1 hε₁
  have hq4 : q ^ 4 ≤ N * η := by
    have e : q ^ 4 = (N : ℝ) * (N : ℝ) ^ (-1 + τ) := by
      rw [hqdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le,
        show (N : ℝ) * (N : ℝ) ^ (-1 + τ) = (N : ℝ) ^ ((1 : ℝ) + (-1 + τ)) by
          rw [Real.rpow_add hN0 (1 : ℝ) (-1 + τ), Real.rpow_one]]
      congr 1; push_cast; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hη hN0.le
  have hNη : 0 < (N : ℝ) * η := mul_pos hN0 hη0
  have hs1 : √(mi / (N * η)) ≤ √Cm / q ^ 2 := by
    rw [show √Cm / q ^ 2 = √(Cm / q ^ 4) by
      rw [Real.sqrt_div' _ (by positivity : (0 : ℝ) ≤ q ^ 4),
        show q ^ 4 = (q ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]]
    refine Real.sqrt_le_sqrt ?_
    calc mi / (N * η) ≤ Cm / (N * η) := div_le_div_of_nonneg_right hmi hNη.le
      _ ≤ Cm / q ^ 4 := div_le_div_of_nonneg_left hCm.le (by positivity) hq4
  have hs2 : 1 / (N * η) ≤ 1 / q ^ 2 := by
    calc 1 / (N * η) ≤ 1 / q ^ 4 := div_le_div_of_nonneg_left zero_le_one (by positivity) hq4
      _ ≤ 1 / q ^ 2 := by
        apply div_le_div_of_nonneg_left zero_le_one (by positivity)
        have : 1 ≤ q ^ 2 := one_le_pow₀ hq1
        nlinarith
  have hΨ : √(mi / (N * η)) + 1 / (N * η) ≤ (√Cm + 1) / q ^ 2 := by
    rw [add_div]; linarith
  have hΨ0 : 0 ≤ √(mi / (N * η)) + 1 / (N * η) := by positivity
  calc (N : ℝ) ^ ε₁ * (√(mi / (N * η)) + 1 / (N * η)) ≤ q * ((√Cm + 1) / q ^ 2) :=
        mul_le_mul hNε hΨ hΨ0 hq0.le
    _ = (√Cm + 1) / q := by field_simp
    _ ≤ (√Cm + 1) / (2 * Cm * (√Cm + 1)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hq
    _ = Cm⁻¹ / 2 := by field_simp

/-- Four events of probability `≤ N^{−D−2}` cover an event of probability `≤ N^{−D}`. -/
private theorem ll_four {Ω : Type*} [MeasureSpace Ω] {N : ℕ} (hN : 2 ≤ N) {D : ℝ}
    {A E₁ E₂ E₃ E₄ : Set Ω} (hA : A ⊆ E₁ ∪ E₂ ∪ E₃ ∪ E₄)
    (h₁ : ℙ E₁ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))))
    (h₂ : ℙ E₂ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))))
    (h₃ : ℙ E₃ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))))
    (h₄ : ℙ E₄ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 2)))) :
    ℙ A ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : (0 : ℝ) < N := by linarith
  set x := (N : ℝ) ^ (-(D + 2)) with hxdef
  have hx : 0 ≤ x := Real.rpow_nonneg hpos.le _
  have hx4 : x + x + x + x ≤ (N : ℝ) ^ (-D) := by
    have e : x = (N : ℝ) ^ (-D) * ((N : ℝ) ^ 2)⁻¹ := by
      rw [hxdef, show -(D + 2) = -D + (-2 : ℝ) by ring, Real.rpow_add hpos (-D) (-2),
        Real.rpow_neg hpos.le (2 : ℝ), Real.rpow_two]
    have h4 : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have hND : 0 ≤ (N : ℝ) ^ (-D) := Real.rpow_nonneg hpos.le _
    have : 4 * ((N : ℝ) ^ 2)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one (by positivity)]; exact h4
    rw [e]
    nlinarith
  calc ℙ A ≤ ℙ (E₁ ∪ E₂ ∪ E₃ ∪ E₄) := measure_mono hA
    _ ≤ ℙ E₁ + ℙ E₂ + ℙ E₃ + ℙ E₄ := by
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal x + ENNReal.ofReal x + ENNReal.ofReal x + ENNReal.ofReal x := by
        gcongr
    _ = ENNReal.ofReal (x + x + x + x) := by
        rw [ENNReal.ofReal_add (by positivity) hx, ENNReal.ofReal_add (by positivity) hx,
          ENNReal.ofReal_add hx hx]
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal hx4

/-- The averaged row: `(N^{ε₁} + 1 + τ⁻²)/(Nη) ≤ N^ε/(Nη)`. -/
private theorem ll_avg_step {N : ℕ} (hN : 1 ≤ N) {τ ε ε₁ Kc : ℝ} (hτ : 0 < τ) {z a b c : ℂ}
    (hz : 0 < z.im) (hzn : τ ≤ ‖z‖) (hη : z.im ≤ τ⁻¹)
    (hK : 2 + τ⁻¹ ^ 2 ≤ Kc) (hKc : Kc ≤ (N : ℝ) ^ (ε - ε₁)) (hε₁ : 0 ≤ ε₁)
    (h₁ : ‖b - c‖ ≤ (N : ℝ) ^ ε₁ * (1 / (N * z.im)))
    (h₂ : ‖a - b‖ ≤ (z.im⁻¹ + ‖z‖⁻¹) / N) :
    ‖a - c‖ ≤ (N : ℝ) ^ ε * (1 / (N * z.im)) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hzn0 : 0 < ‖z‖ := lt_of_lt_of_le hτ hzn
  set t := 1 / ((N : ℝ) * z.im) with ht
  have ht0 : 0 < t := by positivity
  have hNε₁ : 1 ≤ (N : ℝ) ^ ε₁ := Real.one_le_rpow hN1 hε₁
  have hsplit : (N : ℝ) ^ ε = (N : ℝ) ^ ε₁ * (N : ℝ) ^ (ε - ε₁) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have hzi : ‖z‖⁻¹ ≤ τ⁻¹ := inv_anti₀ hτ hzn
  have e2 : (z.im⁻¹ + ‖z‖⁻¹) / N = (1 + z.im * ‖z‖⁻¹) * t := by
    rw [ht]; field_simp
  have h3 : z.im * ‖z‖⁻¹ ≤ τ⁻¹ ^ 2 := by
    rw [sq]
    exact mul_le_mul hη hzi (inv_nonneg.mpr hzn0.le) (inv_nonneg.mpr hτ.le)
  calc ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := norm_sub_le_norm_sub_add_norm_sub a b c
    _ ≤ (1 + τ⁻¹ ^ 2) * t + (N : ℝ) ^ ε₁ * t := by
        rw [e2] at h₂
        have : (1 + z.im * ‖z‖⁻¹) * t ≤ (1 + τ⁻¹ ^ 2) * t :=
          mul_le_mul_of_nonneg_right (by linarith) ht0.le
        linarith
    _ ≤ (N : ℝ) ^ ε₁ * (2 + τ⁻¹ ^ 2) * t := by
        have := mul_le_mul_of_nonneg_right hNε₁ (by positivity : 0 ≤ (1 + τ⁻¹ ^ 2) * t)
        linarith
    _ ≤ (N : ℝ) ^ ε₁ * Kc * t := by gcongr
    _ ≤ (N : ℝ) ^ ε₁ * (N : ℝ) ^ (ε - ε₁) * t := by gcongr
    _ = (N : ℝ) ^ ε * t := by rw [hsplit]

/-- Theorem 11.2 at fixed `N` for a general `T`, in the weighted form. -/
private theorem ll_core (τ : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)] (M K : ℕ) (T : Matrix (Fin M) (Fin K) ℝ)
      (X : Ω → Matrix (Fin K) (Fin N) ℝ) (S : Set ℂ),
      IsModelT τ C M K N T X → SpectralDomain τ N S →
      AnisotropicLawTAt N ε₁ D₁ T X S → AveragedLawTAt N ε₁ D₁ T X S →
      AnisotropicLawDotTAt N ε D T X S ∧ AveragedLawDotTAt N ε D T X S := by
  set Cm := mBoundConst τ with hCm
  have hCm0 : 0 < Cm := by
    rw [hCm, mBoundConst, genPropConst]; positivity
  set ε₁ := min ε τ / 4 with hε₁
  have hε₁0 : 0 < ε₁ := by positivity
  have hε₁τ : ε₁ ≤ τ / 4 := by rw [hε₁]; linarith [min_le_right ε τ]
  have hε₁ε : ε₁ ≤ ε / 4 := by rw [hε₁]; linarith [min_le_left ε τ]
  have hεε₁ : 0 < ε - ε₁ := by linarith
  set A₁ := 2 * Cm * (√Cm + 1) with hA₁
  set Kc := 2 + 6 * Cm ^ 2 + τ⁻¹ ^ 2 with hKc
  refine ⟨ε₁, D + 2, hε₁0, max 2 (max ⌈A₁ ^ (1 / (τ / 4))⌉₊ ⌈Kc ^ (1 / (ε - ε₁))⌉₊), ?_⟩
  intro N hN Ω _ _ M K T X S hm hS hA hAv
  have hN2 : 2 ≤ N := le_of_max_le_left hN
  have hN1 : 1 ≤ N := by omega
  have hN0 : N ≠ 0 := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
  have hq : A₁ ≤ (N : ℝ) ^ (τ / 4) :=
    ll_le_rpow (by positivity) (by positivity) (le_of_max_le_left (le_of_max_le_right hN))
  have hKN : Kc ≤ (N : ℝ) ^ (ε - ε₁) :=
    ll_le_rpow (by positivity) hεε₁ (le_of_max_le_right (le_of_max_le_right hN))
  have hDA := hm.densityAssumptions hτ
  have hsN : √(N : ℝ) * √(N : ℝ) = N := Real.mul_self_sqrt hNr.le
  have hsN0 : 0 < √(N : ℝ) := Real.sqrt_pos.mpr hNr
  have hsplit : (N : ℝ) ^ ε = (N : ℝ) ^ ε₁ * (N : ℝ) ^ (ε - ε₁) := by
    rw [← Real.rpow_add hNr]; congr 1; ring
  constructor
  · intro z hz v u
    have hzD := hS.1 hz
    obtain ⟨hzim, -, -, hlow, -⟩ := hS.1 hz
    obtain ⟨hm1, hm2, -⟩ := gen_prop_m_specDomain hDA hzD
    rw [← hCm] at hm1 hm2
    have hΨ0 : 0 ≤ Psi N (specOf (T * Tᵀ)) z := by rw [Psi]; positivity
    have hδ : (N : ℝ) ^ ε₁ * Psi N (specOf (T * Tᵀ)) z ≤ Cm⁻¹ / 2 := by
      rw [Psi]
      exact ll_delta_le hN1 hτ hε₁τ hCm0 hzim hlow ((Complex.im_le_norm _).trans hm2) hq
    have hE : testNorm (SigU (n := Fin N) (T * Tᵀ) *ᵥ llEr M N) = √(N : ℝ) := by
      rw [ll_SigU_E, ll_testNorm_E]
    have h₁ := hA z hz v u
    have h₂ := hA z hz v (llEr M N)
    have h₃ := hA z hz (llEr M N) u
    have h₄ := hA z hz (llEr M N) (llEr M N)
    rw [hE] at h₂ h₃ h₄
    unfold DomAt at h₁ h₂ h₃ h₄ ⊢
    refine ll_four hN2 ?_ h₁ h₂ h₃ h₄
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
    by_contra hc
    simp only [not_or, not_lt] at hc
    obtain ⟨⟨⟨c₁, c₂⟩, c₃⟩, c₄⟩ := hc
    have hcast : ((N : ℕ) : ℂ) = ((√(N : ℝ) * √(N : ℝ) : ℝ) : ℂ) := by rw [hsN]; rfl
    rw [ll_testBilin_dot T (X ω) hzim hN0 _ v u, hcast] at hω
    have hα := ll_alpha_le (N := N) (T * Tᵀ) v
    have hβ := ll_alpha_le (N := N) (T * Tᵀ) u
    set Ψ := Psi N (specOf (T * Tᵀ)) z
    set a := testNorm (SigU (n := Fin N) (T * Tᵀ) *ᵥ v)
    set b := testNorm (SigU (n := Fin N) (T * Tᵀ) *ᵥ u)
    set sN := √(N : ℝ)
    have ha : 0 ≤ a := Real.sqrt_nonneg _
    have hb : 0 ≤ b := Real.sqrt_nonneg _
    have key := ll_scalar_bound (δ := (N : ℝ) ^ ε₁ * Ψ) (a := a) (b := b) hsN0
      (mul_nonneg (Real.rpow_nonneg hNr.le _) hΨ0) ha hb hCm0
      (c₁.trans_eq (by ring)) (c₂.trans_eq (by ring)) (c₃.trans_eq (by ring))
      (c₄.trans_eq (by ring))
      hα hβ hm1 hm2 hδ
    have hfin : (2 + 6 * Cm ^ 2) * ((N : ℝ) ^ ε₁ * Ψ) * a * b ≤ (N : ℝ) ^ ε * (Ψ * a * b) := by
      rw [hsplit]
      have h0 : 0 ≤ (N : ℝ) ^ ε₁ * Ψ * a * b := by
        have := Real.rpow_nonneg hNr.le ε₁; positivity
      have : 2 + 6 * Cm ^ 2 ≤ (N : ℝ) ^ (ε - ε₁) := by
        refine le_trans ?_ hKN; rw [hKc]; nlinarith [sq_nonneg τ⁻¹]
      nlinarith
    linarith
  · intro z hz
    obtain ⟨hzim, hzn, -, -, hup⟩ := hS.1 hz
    have h₁ := hAv z hz
    unfold ODomAt DomAt at h₁ ⊢
    refine (measure_mono ?_).trans (h₁.trans (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by linarith))))
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    by_contra hc
    rw [not_lt] at hc
    have := ll_avg_step hN1 hτ hzim hzn hup (by rw [hKc]; nlinarith [sq_nonneg Cm]) hKN
      hε₁0.le hc (ll_mNT_dot_le T (X ω) hzim hN0)
    linarith

end Estimates

section Diag

/-- The real vector `A v`, complexified, is `cplx A` applied to the complexified `v`. -/
private theorem ll_cvec_mulVec {p q : Type*} [Fintype q] (A : Matrix p q ℝ) (v : q → ℝ) :
    (fun s => (((A *ᵥ v) s : ℝ) : ℂ)) = cplx A *ᵥ fun t => ((v t : ℝ) : ℂ) := by
  funext i
  exact RingHom.map_mulVec (algebraMap ℝ ℂ) A v i

/-- `⟨P v, P⁻¹ B P⁻¹ P w⟩ = ⟨v, B w⟩` for a real symmetric invertible `P`. -/
private theorem ll_testBilin_conj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hPt : Pᵀ = P) (hP : IsUnit P) (B : Matrix ι ι ℂ) (v w : ι → ℝ) :
    testBilin (P *ᵥ v) ((cplx P)⁻¹ * B * (cplx P)⁻¹) (P *ᵥ w) = testBilin v B w := by
  have hu : IsUnit (cplx P) := hP.map (algebraMap ℝ ℂ).mapMatrix
  have hud : IsUnit (cplx P).det := (isUnit_iff_isUnit_det _).1 hu
  have hQt : (cplx P)ᵀ = cplx P := by
    rw [cplx, ← Matrix.transpose_map, hPt]
  unfold testBilin
  rw [ll_cvec_mulVec, ll_cvec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec _ (cplx P)⁻¹ (cplx P), nonsing_inv_mul _ hud, Matrix.one_mulVec,
    Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, hQt, Matrix.vecMul_vecMul,
    Matrix.mul_nonsing_inv _ hud, Matrix.vecMul_one]

private theorem ll_ulSigma_eq (Sig : Matrix (Fin M) (Fin M) ℝ) :
    ulSigma N Sig = cplx (SigU (n := Fin N) Sig) := by
  unfold ulSigma SigU cplx
  rw [fromBlocks_map]
  simp

private theorem ll_SigU_isUnit {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) :
    IsUnit (SigU (n := Fin N) Sig) := by
  rw [isUnit_iff_isUnit_det, SigU, det_fromBlocks_zero₂₁]
  simpa using (isUnit_iff_isUnit_det _).1 hSig.isUnit

/-- Under (T_diag), `⟨Σ̲ v, Σ̲⁻¹ (Ġ − Π̇) Σ̲⁻¹ Σ̲ w⟩ = ⟨v, (Ġ − Π̇) w⟩`. -/
private theorem ll_testBilin_lawMatDot {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (X : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (v w : Fin M ⊕ Fin N → ℝ) :
    testBilin (SigU Sig *ᵥ v) (lawMatDot Sig X z) (SigU Sig *ᵥ w) =
      testBilin v (G Sig (Xdot X) z - piMatDot Sig (mFun N (specOf Sig) z) z) w := by
  have hSt : (SigU (n := Fin N) Sig)ᵀ = SigU Sig := by
    have : Sigᵀ = Sig := by
      rw [← conjTranspose_eq_transpose_of_trivial]
      exact hSig.1.eq
    unfold SigU
    rw [fromBlocks_transpose]
    simp [this]
  unfold lawMatDot
  rw [ll_ulSigma_eq]
  exact ll_testBilin_conj _ hSt (ll_SigU_isUnit hSig) _ v w

private theorem ll_SigU_surj {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (u : Fin M ⊕ Fin N → ℝ) : ∃ v, SigU Sig *ᵥ v = u := by
  have hd : IsUnit (SigU (n := Fin N) Sig).det :=
    (isUnit_iff_isUnit_det _).1 (ll_SigU_isUnit hSig)
  exact ⟨(SigU Sig)⁻¹ *ᵥ u, by rw [Matrix.mulVec_mulVec, mul_nonsing_inv _ hd, one_mulVec]⟩

end Diag

/-- Theorem 11.2 at fixed `N`, under (T_diag): the anisotropic and averaged laws for `G` on a
spectral domain `S` at `(ε₁, D₁)` give (isotropic law dot) and (averaged law dot) on `S` at
`(ε, D)`; `m` and `Π` are those of `φ = M/N`. -/
theorem local_laws_dot (τ : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)] (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (X : Ω → Matrix (Fin M) (Fin N) ℝ) (S : Set ℂ),
      IsModel τ C M N Sig X → SpectralDomain τ N S →
      AnisotropicLawAt N ε₁ D₁ Sig X S → AveragedLawAt N ε₁ D₁ Sig X S →
      AnisotropicLawDotAt N ε D Sig X S ∧ AveragedLawDotAt N ε D Sig X S := by
  obtain ⟨ε₁, D₁, hε₁, N₀, h⟩ := ll_core τ C ε D hτ hε
  refine ⟨ε₁, D₁, hε₁, N₀, fun N hN Ω _ _ M Sig X S hm hS hA hAv => ?_⟩
  have hSig := hm.sigma.posDef
  have hSim : ∀ z ∈ S, 0 < z.im := fun z hz => (hS.1 hz).1
  obtain ⟨hTT, hTt⟩ := sigPow_half hSig
  have hSS : sigPow Sig (1 / 2) * (sigPow Sig (1 / 2))ᵀ = Sig := by rw [hTt, hTT]
  obtain ⟨h1, h2⟩ := h N hN M M (sigPow Sig (1 / 2)) X S ((isModelT_sqrt_iff hSig).2 hm) hS
    ((anisoT_iff_aniso hSig hSim).1.2 hA) ((anisoT_iff_aniso hSig hSim).2.2 hAv)
  refine ⟨fun z hz v' w' => ?_, (anisoT_iff_aniso (X := fun ω => Xdot (X ω)) hSig hSim).2.1 h2⟩
  obtain ⟨v, rfl⟩ := ll_SigU_surj (N := N) hSig v'
  obtain ⟨w, rfl⟩ := ll_SigU_surj (N := N) hSig w'
  have := h1 z hz v w
  simp only [hSS, blockG_sqrt hSig _ (hSim z hz)] at this
  simp only [ll_testBilin_lawMatDot hSig _ z v w]
  exact this

/-- Theorem 11.2 at fixed `N` for a general `T` (§11.1), in the weighted form. -/
theorem local_laws_dot_gen (τ : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)] (M K : ℕ) (T : Matrix (Fin M) (Fin K) ℝ)
      (X : Ω → Matrix (Fin K) (Fin N) ℝ) (S : Set ℂ),
      IsModelT τ C M K N T X → SpectralDomain τ N S →
      AnisotropicLawTAt N ε₁ D₁ T X S → AveragedLawTAt N ε₁ D₁ T X S →
      AnisotropicLawDotTAt N ε D T X S ∧ AveragedLawDotTAt N ε D T X S :=
  ll_core τ C ε D hτ hε

/-- Theorem 11.2 at the Marchenko–Pastur family (`Σ = I_n`, `N = 2n`, Gaussian `X`, `τ = 1/5`) on
`𝐃(τ, N)`: the hypotheses come from Theorem 3.6 and the regularity of the family; the only binder
left is `2n ≥ N₀`. -/
example : ∃ N₀ : ℕ, ∀ n : ℕ, 1 ≤ n → N₀ ≤ 2 * n →
    AnisotropicLawDotAt (Ω := GaussSpace n (2 * n)) (2 * n) 1 1 (1 : Matrix (Fin n) (Fin n) ℝ)
        (gaussX n (2 * n)) (specDomain (1 / 5) (2 * n)) ∧
      AveragedLawDotAt (Ω := GaussSpace n (2 * n)) (2 * n) 1 1 (1 : Matrix (Fin n) (Fin n) ℝ)
        (gaussX n (2 * n)) (specDomain (1 / 5) (2 * n)) := by
  obtain ⟨ε₁, D₁, hε₁, N₁, h₁⟩ := local_laws_dot (1 / 5) gaussMoment 1 1 (by norm_num) one_pos
  obtain ⟨N₂, h₂⟩ := LL_G (1 / 5) gaussMoment (fun t => min t 1 / 50) ε₁ D₁ (by norm_num) hε₁
  refine ⟨max N₁ N₂, fun n hn hN => ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : (n : ℝ) / ((2 * n : ℕ) : ℝ) = 1 / 2 := by push_cast; field_simp
  have hm : IsModel (1 / 5) gaussMoment n (2 * n) (1 : Matrix (Fin n) (Fin n) ℝ)
      (gaussX n (2 * n)) :=
    isModel_gaussX (by omega) (by rw [hr]; norm_num) (by rw [hr]; norm_num)
      (sigmaAssumption_one (by norm_num) (by norm_num) n)
  have hσ := specOf_one_eq n
  obtain ⟨he, hb⟩ := mp_hyps (n := n) (by omega)
  have hl := h₂ (2 * n) (le_of_max_le_right hN) n 1 (gaussX n (2 * n)) hm
    (by rw [hσ]; exact he) (by rw [hσ]; exact hb)
  exact h₁ (2 * n) (le_of_max_le_left hN) n 1 (gaussX n (2 * n)) _ hm
    (spectralDomain_specDomain _ _) hl.1 hl.2

/-- Theorem 11.2 for a general `T` at `T = (I_n; 0)` (`M = 2n`, `K = n`, `N = 2n`, `Σ = T Tᵀ`
singular of rank `n`, Rademacher `X`, `τ = 1/5`) on `𝐃(τ, N)`: the hypotheses come from the
weighted local laws of §11.1 and the regularity of the family; the only binder left is
`2n ≥ N₀`. -/
example : ∃ N₀ : ℕ, ∀ n : ℕ, 1 ≤ n → N₀ ≤ 2 * n →
    AnisotropicLawDotTAt (Ω := SignSpace (Fin n × Fin (2 * n))) (2 * n) 1 1 (tPad n) (radXn n)
        (specDomain (1 / 5) (2 * n)) ∧
      AveragedLawDotTAt (Ω := SignSpace (Fin n × Fin (2 * n))) (2 * n) 1 1 (tPad n) (radXn n)
        (specDomain (1 / 5) (2 * n)) := by
  obtain ⟨ε₁, D₁, hε₁, N₁, h₁⟩ :=
    local_laws_dot_gen (1 / 5) (fun _ => 1) 1 1 (by norm_num) one_pos
  obtain ⟨N₂, h₂⟩ := LL_G_gen (1 / 5) (fun _ => 1) (fun t => min t 1 / 50) ε₁ D₁ (by norm_num) hε₁
  refine ⟨max N₁ N₂, fun n hn hN => ?_⟩
  have hm := isModelT_tPad (n := n) (by omega)
  obtain ⟨he, hb, -, -⟩ := mpT_hyps (n := n) (by omega)
  have hl := h₂ (2 * n) (le_of_max_le_right hN) (2 * n) n (tPad n) (radXn n) hm he hb
  exact h₁ (2 * n) (le_of_max_le_left hN) (2 * n) n (tPad n) (radXn n) _ hm
    (spectralDomain_specDomain _ _) hl.1 hl.2

end Anisotropic

#print axioms Anisotropic.local_laws_dot
#print axioms Anisotropic.local_laws_dot_gen
