module

public import Anisotropic.MainDefs
public import Anisotropic.Density.SelfConsistent
public import Anisotropic.Entrywise.Defs
public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.Framework.Domination
public import Anisotropic.Framework.Model
public import Anisotropic.LinAlg.Basic
public import Anisotropic.LinAlg.Blocks

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # `R_N`, `R_M`, (G_N_ident), (G_M_ident) and the laws for `R_N`, `R_M` -/

/-! ## Spectral powers of `Σ > 0` -/

/-- The spectrum of `Σ > 0` lies in `(0, ∞)`. -/
private theorem res_spec_pos {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) :
    ∀ x ∈ spectrum ℝ Sig, 0 < x := by
  rw [hSig.1.spectrum_real_eq_range_eigenvalues]
  rintro _ ⟨i, rfl⟩
  exact hSig.eigenvalues_pos i

/-- Every real function is continuous on the (finite) spectrum of a symmetric matrix. -/
private theorem res_contOn {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.IsHermitian)
    (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ Sig) := by
  rw [hSig.spectrum_real_eq_range_eigenvalues]
  exact (Set.finite_range _).continuousOn f

/-- `Σ^r Σ^s = Σ^{r+s}` for `Σ > 0`. -/
private theorem res_sigPow_mul {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) (r s : ℝ) :
    sigPow Sig r * sigPow Sig s = sigPow Sig (r + s) := by
  unfold sigPow
  rw [← cfc_mul _ _ Sig (res_contOn hSig.1 _) (res_contOn hSig.1 _)]
  refine cfc_congr fun x hx => ?_
  have hx0 := res_spec_pos hSig x hx
  simp only [hx0, ↓reduceIte]
  rw [Real.rpow_add hx0]

/-- `Σ^1 = Σ` for `Σ > 0`. -/
private theorem res_sigPow_one {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) :
    sigPow Sig 1 = Sig := by
  unfold sigPow
  rw [cfc_congr (g := id) fun x hx => by
    simp only [res_spec_pos hSig x hx, ↓reduceIte, Real.rpow_one, id]]
  exact cfc_id ℝ Sig hSig.1

/-- `Σ^0 = 1` for `Σ > 0`. -/
private theorem res_sigPow_zero {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) :
    sigPow Sig 0 = 1 := by
  unfold sigPow
  rw [cfc_congr (g := fun _ => 1) fun x hx => by
    simp only [res_spec_pos hSig x hx, ↓reduceIte, Real.rpow_zero]]
  exact cfc_const_one ℝ Sig hSig.1

/-- `(Σ^r)ᵀ = Σ^r`. -/
private theorem res_sigPow_transpose (Sig : Matrix (Fin M) (Fin M) ℝ) (r : ℝ) :
    (sigPow Sig r)ᵀ = sigPow Sig r := by
  rw [← conjTranspose_eq_transpose_of_trivial]
  exact (cfc_predicate (fun x : ℝ => if 0 < x then x ^ r else 0) Sig : IsSelfAdjoint _).star_eq

/-- `Σ^r` commutes with `Σ^s`. -/
private theorem res_sigPow_comm (Sig : Matrix (Fin M) (Fin M) ℝ) (r s : ℝ) :
    sigPow Sig r * sigPow Sig s = sigPow Sig s * sigPow Sig r :=
  (cfc_commute_cfc _ _ Sig).eq

/-- `Σ^{1/2} Σ^{1/2} = Σ` and `(Σ^{1/2})ᵀ = Σ^{1/2}` for `Σ > 0`. -/
theorem sigPow_half {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) :
    sigPow Sig (1 / 2) * sigPow Sig (1 / 2) = Sig ∧ (sigPow Sig (1 / 2))ᵀ = sigPow Sig (1 / 2) :=
  ⟨by rw [res_sigPow_mul hSig]; norm_num; exact res_sigPow_one hSig,
    res_sigPow_transpose Sig _⟩

/-- `Σ^{−1/2} Σ^{1/2} = Σ^{1/2} Σ^{−1/2} = 1` for `Σ > 0`. -/
theorem sigPow_neg_half {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) :
    sigPow Sig (-(1 / 2)) * sigPow Sig (1 / 2) = 1 ∧
      sigPow Sig (1 / 2) * sigPow Sig (-(1 / 2)) = 1 := by
  have h : sigPow Sig (-(1 / 2)) * sigPow Sig (1 / 2) = 1 := by
    rw [res_sigPow_mul hSig, neg_add_cancel, res_sigPow_zero hSig]
  exact ⟨h, by rw [res_sigPow_comm]; exact h⟩

/-! ## (G_N_ident) and (G_M_ident) -/

/-- Complexification is multiplicative. -/
private theorem res_cplx_mul {p q r : Type*} [Fintype q] (A : Matrix p q ℝ) (B : Matrix q r ℝ) :
    cplx (A * B) = cplx A * cplx B := Matrix.map_mul

/-- Complexification of `1`. -/
private theorem res_cplx_one {p : Type*} [DecidableEq p] : cplx (1 : Matrix p p ℝ) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

/-- `T X Xᵀ Tᵀ − z` is invertible for `Im z > 0`, for every real `M × K` matrix `T`. -/
private theorem res_RM_isUnit {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ)
    (X : Matrix (Fin K) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) :
    IsUnit (cplx (T * X * Xᵀ * Tᵀ) - z • (1 : Matrix (Fin M) (Fin M) ℂ)) := by
  have h := GN_isUnit (Matrix.PosDef.one : (1 : Matrix (Fin N) (Fin N) ℝ).PosDef) (T * X)ᵀ hz
  rwa [transpose_transpose, Matrix.mul_one, transpose_mul, ← Matrix.mul_assoc] at h

/-- `R_N = G_N` with `T = Σ^{1/2}`. -/
private theorem res_RN_eq {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (X : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) : RN (sigPow Sig (1 / 2)) X z = GN Sig X z := by
  obtain ⟨hTT, hTt⟩ := sigPow_half hSig
  rw [RN, hTt, Matrix.mul_assoc Xᵀ, hTT]
  rfl

/-- (G_N_ident): `G_{μν} = (R_N)_{μν}` with `T = Σ^{1/2}`. -/
theorem G_N_ident {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (X : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (μ ν : Fin N) :
    G Sig X z (Sum.inr μ) (Sum.inr ν) = RN (sigPow Sig (1 / 2)) X z μ ν := by
  rw [(GeqG hSig X hz).1, fromBlocks_apply₂₂, res_RN_eq hSig]

/-- The `𝓘_M` block of `G` with `T = Σ^{1/2}`: `G_M = z Σ^{1/2} R_M Σ^{1/2}`. -/
private theorem res_GM_eq {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (X : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) :
    GM Sig X z = z • (cplx (sigPow Sig (1 / 2)) * RM (sigPow Sig (1 / 2)) X z *
        cplx (sigPow Sig (1 / 2))) := by
  obtain ⟨hTT, hTt⟩ := sigPow_half hSig
  obtain ⟨hIT, hTI⟩ := sigPow_neg_half hSig
  set T := sigPow Sig (1 / 2)
  set Ti := sigPow Sig (-(1 / 2))
  set B := cplx (T * X * Xᵀ * Tᵀ) - z • (1 : Matrix (Fin M) (Fin M) ℂ)
  set A := cplx (X * Xᵀ * Sig) - z • (1 : Matrix (Fin M) (Fin M) ℂ)
  have hB := res_RM_isUnit T X hz
  have hBdet : IsUnit B.det := (isUnit_iff_isUnit_det _).1 hB
  -- `A Σ^{−1/2} = Σ^{−1/2} B`
  have hAB : A * cplx Ti = cplx Ti * B := by
    have h1 : X * Xᵀ * Sig * Ti = Ti * (T * X * Xᵀ * Tᵀ) := by
      rw [hTt, ← hTT, show Ti * (T * X * Xᵀ * T) = Ti * T * (X * Xᵀ * T) by
        simp only [Matrix.mul_assoc], hIT, Matrix.one_mul]
      simp only [Matrix.mul_assoc, hTI, Matrix.mul_one]
    simp only [A, B, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, ← res_cplx_mul, h1]
  have hAinv : A⁻¹ = cplx Ti * B⁻¹ * cplx T := by
    refine Matrix.inv_eq_right_inv ?_
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hAB, Matrix.mul_assoc (cplx Ti),
      mul_nonsing_inv _ hBdet, Matrix.mul_one, ← res_cplx_mul, hIT, res_cplx_one]
  rw [GM_eq hSig X hz]
  change z • (cplx Sig * A⁻¹) = z • (cplx T * B⁻¹ * cplx T)
  rw [hAinv, ← hTT, res_cplx_mul, show cplx T * cplx T * (cplx Ti * B⁻¹ * cplx T)
      = cplx T * (cplx T * cplx Ti) * B⁻¹ * cplx T by simp only [Matrix.mul_assoc],
    ← res_cplx_mul T Ti, hTI, res_cplx_one, Matrix.mul_one]

/-- (G_M_ident): `G_{ij} = (z Σ^{1/2} R_M Σ^{1/2})_{ij}` with `T = Σ^{1/2}`. -/
theorem G_M_ident {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (X : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (i j : Fin M) :
    G Sig X z (Sum.inl i) (Sum.inl j) =
      (z • (cplx (sigPow Sig (1 / 2)) * RM (sigPow Sig (1 / 2)) X z *
        cplx (sigPow Sig (1 / 2)))) i j := by
  rw [(GeqG hSig X hz).2, fromBlocks_apply₁₁, res_GM_eq hSig X hz]

/-! ## The laws (R_N_edge) and (R_M_edge) -/

/-- `⟨(v, 0), A (w, 0)⟩ = ⟨v, A_{MM} w⟩`. -/
private theorem res_testBilin_embM (A : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ)
    (v w : Fin M → ℝ) :
    testBilin (embM (n := Fin N) v) A (embM w) = testBilin v A.toBlocks₁₁ w :=
  ent_embM_embM A v w

/-- `⟨(0, v), A (0, w)⟩ = ⟨v, A_{NN} w⟩`. -/
private theorem res_testBilin_embN (A : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ)
    (v w : Fin N → ℝ) :
    testBilin (embN (m := Fin M) v) A (embN w) = testBilin v A.toBlocks₂₂ w :=
  ent_embN_embN A v w

/-- `|(v, 0)| = |v|`. -/
private theorem res_testNorm_embM (v : Fin M → ℝ) :
    testNorm (embM (n := Fin N) v) = testNorm v := by
  simp [testNorm, embM, Fintype.sum_sum_type]

/-- `|(0, v)| = |v|`. -/
private theorem res_testNorm_embN (v : Fin N → ℝ) :
    testNorm (embN (m := Fin M) v) = testNorm v := by
  simp [testNorm, embN, Fintype.sum_sum_type]

/-- `⟨v, c A w⟩ = c ⟨v, A w⟩`. -/
private theorem res_testBilin_smul {ι : Type*} [Fintype ι] (v w : ι → ℝ) (c : ℂ)
    (A : Matrix ι ι ℂ) : testBilin v (c • A) w = c * testBilin v A w := by
  simp [testBilin, Matrix.smul_mulVec, dotProduct_smul]

/-- `Σ̲⁻¹ = diag(Σ⁻¹, 1)` for `Σ > 0`. -/
private theorem res_ulSigma_inv {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) :
    (ulSigma N Sig)⁻¹ = fromBlocks (cplx Sig)⁻¹ 0 0 1 := by
  have hu : IsUnit (cplx Sig) := hSig.isUnit.map (algebraMap ℝ ℂ).mapMatrix
  rw [ulSigma, inv_fromBlocks_zero₂₁_of_isUnit_iff _ _ _ (iff_of_true hu isUnit_one)]
  simp

/-- The diagonal blocks of `diag(S, 1) K diag(S, 1)`. -/
private theorem res_blocks_conj (Si : Matrix (Fin M) (Fin M) ℂ)
    (K : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) :
    (fromBlocks Si 0 0 1 * K * fromBlocks Si 0 0 1).toBlocks₁₁ = Si * K.toBlocks₁₁ * Si ∧
      (fromBlocks Si 0 0 1 * K * fromBlocks Si 0 0 1).toBlocks₂₂ = K.toBlocks₂₂ := by
  rw [← fromBlocks_toBlocks K]
  simp [fromBlocks_multiply]

/-- The diagonal blocks of `Σ̲⁻¹ (G − Π) Σ̲⁻¹`. -/
private theorem res_lawMat_blocks {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (X : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) :
    (lawMat Sig X z).toBlocks₁₁ = (cplx Sig)⁻¹ * (GM Sig X z + cplx Sig *
      (1 + mFun N (specOf Sig) z • cplx Sig)⁻¹) * (cplx Sig)⁻¹ ∧
    (lawMat Sig X z).toBlocks₂₂ = GN Sig X z - mFun N (specOf Sig) z • 1 := by
  obtain ⟨h1, h2⟩ := res_blocks_conj (N := N) (cplx Sig)⁻¹
    (G Sig X z - piMat Sig (mFun N (specOf Sig) z))
  unfold lawMat
  rw [res_ulSigma_inv hSig, h1, h2]
  constructor
  · congr 2
    ext i j
    simp [toBlocks₁₁, piMat, (GeqG hSig X hz).2, sub_eq_add_neg]
  · ext i j
    simp [toBlocks₂₂, piMat, (GeqG hSig X hz).1]

/-- `P⁻¹ Q = Q P⁻¹` for commuting square matrices `P`, `Q`. -/
private theorem res_inv_comm {P Q : Matrix (Fin M) (Fin M) ℂ} (h : Q * P = P * Q) :
    P⁻¹ * Q = Q * P⁻¹ := by
  by_cases hP : IsUnit P.det
  · calc P⁻¹ * Q = P⁻¹ * (Q * P) * P⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hP, Matrix.mul_one]
      _ = Q * P⁻¹ := by
          rw [h, ← Matrix.mul_assoc, nonsing_inv_mul _ hP, Matrix.one_mul]
  · rw [nonsing_inv_apply_not_isUnit _ hP, Matrix.zero_mul, Matrix.mul_zero]

/-- `(z P)⁻¹ = z⁻¹ P⁻¹` for `z ≠ 0`. -/
private theorem res_inv_smul {z : ℂ} (hz : z ≠ 0) (P : Matrix (Fin M) (Fin M) ℂ) :
    (z • P)⁻¹ = z⁻¹ • P⁻¹ := by
  by_cases hP : IsUnit P.det
  · refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hz, one_smul,
      nonsing_inv_mul _ hP]
  · have hzP : ¬IsUnit (z • P).det := by
      rw [det_smul, IsUnit.mul_iff, not_and_or]
      exact Or.inr hP
    rw [nonsing_inv_apply_not_isUnit _ hP, nonsing_inv_apply_not_isUnit _ hzP, smul_zero]

/-- `Σ^{−1/2}(R_M + (z(1 + mΣ))⁻¹)Σ^{−1/2} = z⁻¹ (Σ̲⁻¹ (G − Π) Σ̲⁻¹)_{MM}` with `T = Σ^{1/2}`. -/
private theorem res_RM_lawMat {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (X : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) :
    cplx (sigPow Sig (-(1 / 2))) *
      (RM (sigPow Sig (1 / 2)) X z + (z • (1 + mFun N (specOf Sig) z • cplx Sig))⁻¹) *
      cplx (sigPow Sig (-(1 / 2))) = z⁻¹ • (lawMat Sig X z).toBlocks₁₁ := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  obtain ⟨hTT, -⟩ := sigPow_half hSig
  obtain ⟨hIT, hTI⟩ := sigPow_neg_half hSig
  rw [(res_lawMat_blocks hSig X hz).1, res_GM_eq hSig X hz, res_inv_smul hz0]
  set T := sigPow Sig (1 / 2)
  set Ti := sigPow Sig (-(1 / 2))
  set m := mFun N (specOf Sig) z
  set R := RM T X z
  have cIT : cplx Ti * cplx T = 1 := by rw [← res_cplx_mul, hIT, res_cplx_one]
  have cTI : cplx T * cplx Ti = 1 := by rw [← res_cplx_mul, hTI, res_cplx_one]
  have cS : cplx Sig = cplx T * cplx T := by rw [← hTT, res_cplx_mul]
  have cSi : (cplx Sig)⁻¹ = cplx Ti * cplx Ti := by
    refine Matrix.inv_eq_left_inv ?_
    rw [cS, show cplx Ti * cplx Ti * (cplx T * cplx T) = cplx Ti * (cplx Ti * cplx T) * cplx T by
      simp only [Matrix.mul_assoc], cIT, Matrix.mul_one, cIT]
  set P := (1 : Matrix (Fin M) (Fin M) ℂ) + m • cplx Sig
  have hcomm : cplx Ti * P = P * cplx Ti := by
    have : cplx Ti * cplx Sig = cplx Sig * cplx Ti := by
      rw [cS, ← Matrix.mul_assoc, cIT, Matrix.one_mul, Matrix.mul_assoc, cTI, Matrix.mul_one]
    simp only [P, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_smul, Matrix.smul_mul, this]
  have hPi : P⁻¹ * cplx Ti = cplx Ti * P⁻¹ := res_inv_comm hcomm
  rw [cSi]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add,
    smul_smul, inv_mul_cancel₀ hz0, one_smul]
  congr 1
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (cplx Ti) (cplx T), cIT, Matrix.one_mul,
      ← Matrix.mul_assoc (cplx T) (cplx Ti), cTI, Matrix.one_mul]
  · rw [cS]
    congr 1
    calc cplx Ti * P⁻¹ * cplx Ti = P⁻¹ * (cplx Ti * cplx Ti) := by
          rw [← hPi, Matrix.mul_assoc]
      _ = _ := by
          rw [show cplx Ti * cplx Ti * (cplx T * cplx T * P⁻¹) * (cplx Ti * cplx Ti)
              = cplx Ti * (cplx Ti * cplx T) * cplx T * P⁻¹ * (cplx Ti * cplx Ti) by
            simp only [Matrix.mul_assoc], cIT, Matrix.mul_one, cIT, Matrix.one_mul]

/-- From the law at `ε/2`: `c ξ ≺ ζ` at `ε` once `c ≤ N^{ε/2}` and `ξ ≥ 0`. -/
private theorem res_domAt_half {Ω : Type*} [MeasureSpace Ω] {N : ℕ} (hN : 1 ≤ N)
    {ε D c : ℝ} (hc : c ≤ (N : ℝ) ^ (ε / 2)) {ξ ζ : Ω → ℝ} (hξ : ∀ ω, 0 ≤ ξ ω)
    (h : DomAt N (ε / 2) D ξ ζ) : DomAt N ε D (fun ω => c * ξ ω) ζ := by
  unfold DomAt at *
  refine (measure_mono ?_).trans h
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have ha : 0 < (N : ℝ) ^ (ε / 2) := Real.rpow_pos_of_pos hN0 _
  have hsq : (N : ℝ) ^ ε = (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) := by
    rw [← Real.rpow_add hN0]; ring_nf
  have h1 : c * ξ ω ≤ (N : ℝ) ^ (ε / 2) * ξ ω := mul_le_mul_of_nonneg_right hc (hξ ω)
  rw [hsq] at hω
  have h2 : (N : ℝ) ^ (ε / 2) * ((N : ℝ) ^ (ε / 2) * ζ ω) < (N : ℝ) ^ (ε / 2) * ξ ω := by
    rw [← mul_assoc]; linarith
  exact lt_of_mul_lt_mul_left h2 ha.le

/-- The anisotropic law at `(ε/2, D)` gives (R_N_edge) and (R_M_edge) at `(ε, D)` with
`T = Σ^{1/2}`, once `τ⁻¹ ≤ N^{ε/2}` (from (G_N_ident), (G_M_ident), (def_Pi), `|z| ≥ τ`). -/
theorem rLaws_of_aniso {Ω : Type*} [MeasureSpace Ω] {τ : ℝ} (hτ : 0 < τ) {N : ℕ} (hN : 1 ≤ N)
    {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {X : Ω → Matrix (Fin M) (Fin N) ℝ}
    {S : Set ℂ} (hS : S ⊆ specDomain τ N) {ε D : ℝ} (hNτ : τ⁻¹ ≤ (N : ℝ) ^ (ε / 2))
    (h : AnisotropicLawAt N (ε / 2) D Sig X S) :
    RNLawAt N ε D Sig (sigPow Sig (1 / 2)) X S ∧ RMLawAt N ε D Sig (sigPow Sig (1 / 2)) X S := by
  constructor
  · intro z hz v w
    obtain ⟨hzim, -, -, hlow, hup⟩ := hS hz
    have hτ1 : τ ≤ 1 := by
      by_contra hlt
      push Not at hlt
      have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (-1 + τ) :=
        Real.one_le_rpow (by exact_mod_cast hN) (by linarith)
      have h2 : τ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hlt
      linarith
    have hc : (1 : ℝ) ≤ (N : ℝ) ^ (ε / 2) := le_trans ((one_le_inv₀ hτ).2 hτ1) hNτ
    have key := res_domAt_half hN hc (fun ω => norm_nonneg _) (h z hz (embN v) (embN w))
    convert key using 2
    · rename_i ω
      beta_reduce
      rw [one_mul, res_testBilin_embN, (res_lawMat_blocks hSig (X ω) hzim).2, res_RN_eq hSig]
    · beta_reduce
      rw [res_testNorm_embN, res_testNorm_embN]
  · intro z hz v w
    obtain ⟨hzim, hτz, -, -, -⟩ := hS hz
    have hc : ‖z‖⁻¹ ≤ (N : ℝ) ^ (ε / 2) := le_trans (inv_anti₀ hτ hτz) hNτ
    have key := res_domAt_half hN hc (fun ω => norm_nonneg _) (h z hz (embM v) (embM w))
    convert key using 2
    · rename_i ω
      beta_reduce
      rw [res_RM_lawMat hSig (X ω) hzim, res_testBilin_smul, norm_mul, norm_inv,
        res_testBilin_embM]
    · beta_reduce
      rw [res_testNorm_embM, res_testNorm_embM]

/-- `τ⁻¹ ≤ N^{ε/2}` for `N ≥ ⌈τ^{−2/ε}⌉`. -/
theorem inv_le_rpow_of_ge {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) {N : ℕ}
    (hN : ⌈τ⁻¹ ^ (2 / ε)⌉₊ ≤ N) : τ⁻¹ ≤ (N : ℝ) ^ (ε / 2) := by
  have h1 : τ⁻¹ ^ (2 / ε) ≤ (N : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hN)
  have h0 : 0 ≤ τ⁻¹ ^ (2 / ε) := Real.rpow_nonneg (inv_nonneg.2 hτ.le) _
  calc τ⁻¹ = (τ⁻¹ ^ (2 / ε)) ^ (ε / 2) := by
        rw [← Real.rpow_mul (inv_nonneg.2 hτ.le), show 2 / ε * (ε / 2) = 1 by field_simp,
          Real.rpow_one]
    _ ≤ (N : ℝ) ^ (ε / 2) := Real.rpow_le_rpow h0 h1 (by positivity)

/-! ## Instances -/

/-- `Σ = diag(4, 9)`: `Σ^{1/2} Σ^{1/2} = Σ` and `Σ^{1/2}` is symmetric. -/
example : sigPow (diagonal ![(4 : ℝ), 9]) (1 / 2) * sigPow (diagonal ![(4 : ℝ), 9]) (1 / 2) =
      diagonal ![(4 : ℝ), 9] ∧
    (sigPow (diagonal ![(4 : ℝ), 9]) (1 / 2))ᵀ = sigPow (diagonal ![(4 : ℝ), 9]) (1 / 2) :=
  sigPow_half (posDef_diagonal_iff.2 fun i => by fin_cases i <;> norm_num)

/-- `Σ = diag(4, 9)`: `Σ^{−1/2}` is the two-sided inverse of `Σ^{1/2}`. -/
example : sigPow (diagonal ![(4 : ℝ), 9]) (-(1 / 2)) * sigPow (diagonal ![(4 : ℝ), 9]) (1 / 2) = 1 ∧
    sigPow (diagonal ![(4 : ℝ), 9]) (1 / 2) * sigPow (diagonal ![(4 : ℝ), 9]) (-(1 / 2)) = 1 :=
  sigPow_neg_half (posDef_diagonal_iff.2 fun i => by fin_cases i <;> norm_num)

/-- Marchenko–Pastur, `M = 1`, `N = 2`, `Σ = 1`, `X = (1, 1)`, `z = i`: (G_N_ident). -/
example (μ ν : Fin 2) :
    G (1 : Matrix (Fin 1) (Fin 1) ℝ) !![(1 : ℝ), 1] Complex.I (Sum.inr μ) (Sum.inr ν) =
      RN (sigPow (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 / 2)) !![(1 : ℝ), 1] Complex.I μ ν :=
  G_N_ident Matrix.PosDef.one _ (by simp) μ ν

/-- Marchenko–Pastur, `M = 1`, `N = 2`, `Σ = 1`, `X = (1, 1)`, `z = i`: (G_M_ident). -/
example (i j : Fin 1) :
    G (1 : Matrix (Fin 1) (Fin 1) ℝ) !![(1 : ℝ), 1] Complex.I (Sum.inl i) (Sum.inl j) =
      (Complex.I • (cplx (sigPow (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 / 2)) *
        RM (sigPow (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 / 2)) !![(1 : ℝ), 1] Complex.I *
        cplx (sigPow (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 / 2)))) i j :=
  G_M_ident Matrix.PosDef.one _ (by simp) i j

/-- `τ = 1/20`, `ε = 1`, `N = 400 = ⌈20²⌉`: `20 ≤ 400^{1/2}`. -/
example : ((1 : ℝ) / 20)⁻¹ ≤ ((400 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) :=
  inv_le_rpow_of_ge (by norm_num) (by norm_num) (by
    rw [show ((1 : ℝ) / 20)⁻¹ ^ ((2 : ℝ) / 1) = ((400 : ℕ) : ℝ) by
      rw [show (2 : ℝ) / 1 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num,
      Nat.ceil_natCast])

end Anisotropic

#print axioms Anisotropic.sigPow
#print axioms Anisotropic.RN
#print axioms Anisotropic.RM
#print axioms Anisotropic.sigPow_half
#print axioms Anisotropic.sigPow_neg_half
#print axioms Anisotropic.G_N_ident
#print axioms Anisotropic.G_M_ident
#print axioms Anisotropic.RNLawAt
#print axioms Anisotropic.RMLawAt
#print axioms Anisotropic.rLaws_of_aniso
#print axioms Anisotropic.inv_le_rpow_of_ge
