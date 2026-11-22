module

public import Anisotropic.MainDefs
public import Anisotropic.Density.GenProp
public import Anisotropic.Density.SelfConsistent
public import Anisotropic.Endpoints.Resolvents
public import Anisotropic.Entrywise.Defs
public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.Framework.Domination
public import Anisotropic.Framework.Model
public import Anisotropic.LinAlg.Basic
public import Anisotropic.LinAlg.Blocks

@[expose] public section

/-!
# Assumption 2.1 for a general `T`, the block matrix `G` of (def_block_G)

Assumption 2.1 without (T_diag) for a deterministic `M × M̂` matrix `T` and `Σ = T Tᵀ`
(Section 2.1), the block matrix `G` of (def_block_G) with the off-diagonal blocks
`Σ^{1/2} T X R_N` and `R_N Xᵀ Tᵀ Σ^{1/2}`, the weighted forms of (edge_G_result) and
(edge_G_avg_result) for a general `T`, their relation to the case `T = Σ^{1/2}`, and the
laws (R_N_edge), (R_M_edge) obtained from them. Two compiled instances with singular `Σ`
(`M̂ < M`) and with `M̂ > M`.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # The model with a general `T` (Assumption 2.1 without (T_diag)), the block matrix `G` of (def_block_G), the laws for a general `T`, and two instances -/

section ModelT

variable {Ω : Type*} [MeasureSpace Ω]

/-- (T_diag) is the case `K = M`, `T = Σ^{1/2}`, `Σ > 0`. -/
theorem isModelT_sqrt_iff {τ : ℝ} {C : ℕ → ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hSig : Sig.PosDef) {X : Ω → Matrix (Fin M) (Fin N) ℝ} :
    IsModelT τ C M M N (sigPow Sig (1 / 2)) X ↔ IsModel τ C M N Sig X := by
  obtain ⟨hTT, hTt⟩ := sigPow_half hSig
  have hS : sigPow Sig (1 / 2) * (sigPow Sig (1 / 2))ᵀ = Sig := by rw [hTt, hTT]
  have he : specOf Sig = hSig.isHermitian.eigenvalues := specOf_eq hSig.isHermitian
  constructor
  · intro h
    refine ⟨h.ratio_ge, h.ratio_le, h.entries, ⟨hSig, fun i => ?_, ?_⟩⟩
    · have := h.eig_le i
      rwa [hS, he] at this
    · have := h.gap
      rwa [hS, he] at this
  · intro h
    refine ⟨h.ratio_ge, h.ratio_le, h.ratio_ge, h.ratio_le, h.entries, fun i => ?_, ?_⟩
    · rw [hS, he]; exact h.sigma.eigenvalues_le i
    · rw [hS, he]; exact h.sigma.gap

/-- `π(s) = M⁻¹ #{i : σ_i ∈ s}` for a measurable set `s`, with `π` of (def_pi). -/
private lemma modelT_empMeasure_apply_card (σ : Fin M → ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    empMeasure σ s = (M : ℝ≥0∞)⁻¹ * ((Finset.univ.filter fun i => σ i ∈ s).card : ℝ≥0∞) := by
  simp only [empMeasure, Measure.smul_apply, Measure.finsetSum_apply,
    Measure.dirac_apply' _ hs, smul_eq_mul]
  congr 1
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Set.indicator]

/-- Assumption 2.1 for general `T` gives the density assumptions for the eigenvalues of `T Tᵀ`. -/
theorem IsModelT.densityAssumptions {τ : ℝ} {C : ℕ → ℝ} {K : ℕ}
    {T : Matrix (Fin M) (Fin K) ℝ} {X : Ω → Matrix (Fin K) (Fin N) ℝ} (hτ : 0 < τ)
    (h : IsModelT τ C M K N T X) : DensityAssumptions τ N (specOf (T * Tᵀ)) := by
  have hM : (0 : ℝ) < M := by
    rcases (Nat.cast_nonneg M : (0 : ℝ) ≤ M).lt_or_eq with hM | hM
    · exact hM
    · have h0 := h.ratio_ge
      rw [← hM, zero_div] at h0
      linarith
  have hP : (T * Tᵀ).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose T
  have hspec : specOf (T * Tᵀ) = hP.isHermitian.eigenvalues := specOf_eq hP.isHermitian
  refine ⟨hτ, fun i => ?_, h.ratio_ge, h.ratio_le, h.eig_le, ?_⟩
  · rw [hspec]
    exact hP.eigenvalues_nonneg i
  · rw [modelT_empMeasure_apply_card _ measurableSet_Icc, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, ENNReal.toReal_natCast]
    rw [inv_mul_le_iff₀ hM]
    refine le_trans (le_of_eq ?_) (h.gap.trans_eq (mul_comm _ _))
    rw [← Set.ncard_coe_finset]
    congr 2
    ext i
    simp

/-- Assumption 2.1 for general `T` is monotone in `τ`. -/
theorem IsModelT.mono {τ τ₂ : ℝ} {C : ℕ → ℝ} {K : ℕ}
    {T : Matrix (Fin M) (Fin K) ℝ} {X : Ω → Matrix (Fin K) (Fin N) ℝ}
    (h : IsModelT τ C M K N T X) (h₀ : 0 < τ₂) (h₂ : τ₂ ≤ τ) : IsModelT τ₂ C M K N T X := by
  have hτ : 0 < τ := h₀.trans_le h₂
  have hinv : τ⁻¹ ≤ τ₂⁻¹ := inv_anti₀ h₀ h₂
  refine ⟨h₂.trans h.ratio_ge, h.ratio_le.trans hinv, h₂.trans h.ratioK_ge,
    h.ratioK_le.trans hinv, h.entries, fun i => (h.eig_le i).trans hinv, ?_⟩
  have hsub : {i | specOf (T * Tᵀ) i ∈ Set.Icc 0 τ₂} ⊆ {i | specOf (T * Tᵀ) i ∈ Set.Icc 0 τ} :=
    fun i hi => ⟨hi.1, hi.2.trans h₂⟩
  have hc := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  calc ({i | specOf (T * Tᵀ) i ∈ Set.Icc 0 τ₂}.ncard : ℝ)
      ≤ ({i | specOf (T * Tᵀ) i ∈ Set.Icc 0 τ}.ncard : ℝ) := by exact_mod_cast hc
    _ ≤ (1 - τ) * M := h.gap
    _ ≤ (1 - τ₂) * M := by nlinarith

end ModelT

section LawsT

variable {Ω : Type*} [MeasureSpace Ω]

end LawsT

/-- Complexification is multiplicative. -/
private theorem modelT_cplx_mul {p q r : Type*} [Fintype q] (A : Matrix p q ℝ)
    (B : Matrix q r ℝ) : cplx (A * B) = cplx A * cplx B := Matrix.map_mul

/-- Under (T_diag), `G` of (def_block_G) is `G` of (def_G). -/
theorem blockG_sqrt {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (X : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) :
    blockG (sigPow Sig (1 / 2)) X z = G Sig X z := by
  obtain ⟨hTT, hTt⟩ := sigPow_half hSig
  have hSigT : Sigᵀ = Sig := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact hSig.1.eq
  have hG1 := (GeqG hSig X hz).1
  have hGN : GN Sig X z = RN (sigPow Sig (1 / 2)) X z := by
    ext μ ν
    have := G_N_ident hSig X hz μ ν
    rwa [hG1, fromBlocks_apply₂₂] at this
  have h11 := fun i j => G_M_ident hSig X hz i j
  simp only [hG1, fromBlocks_apply₁₁] at h11
  rw [hG1]
  simp only [blockG, hTt, hTT, hGN] at h11 ⊢
  rw [fromBlocks_inj]
  refine ⟨?_, ?_, ?_, rfl⟩
  · ext i j
    exact (h11 i j).symm
  · rw [modelT_cplx_mul, Matrix.mul_assoc]
  · rw [Matrix.transpose_mul, hSigT, modelT_cplx_mul, Matrix.mul_assoc]

/-- `R_N = G_N` with `T = Σ^{1/2}`. -/
private theorem modelT_RN_eq {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (X : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) : RN (sigPow Sig (1 / 2)) X z = GN Sig X z := by
  obtain ⟨hTT, hTt⟩ := sigPow_half hSig
  rw [RN, hTt, Matrix.mul_assoc Xᵀ, hTT]
  rfl

/-- The real vector `A v`, complexified, is `cplx A` applied to the complexified `v`. -/
private theorem modelT_cvec_mulVec {p q : Type*} [Fintype q] (A : Matrix p q ℝ) (v : q → ℝ) :
    (fun s => (((A *ᵥ v) s : ℝ) : ℂ)) = cplx A *ᵥ fun t => ((v t : ℝ) : ℂ) := by
  funext i
  exact RingHom.map_mulVec (algebraMap ℝ ℂ) A v i

/-- `⟨P v, Q⁻¹ B Q⁻¹ P w⟩ = ⟨v, B w⟩` for a real symmetric invertible `P`, `Q = P` over `ℂ`. -/
private theorem modelT_testBilin_conj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hPt : Pᵀ = P) (hP : IsUnit P) (B : Matrix ι ι ℂ) (v w : ι → ℝ) :
    testBilin (P *ᵥ v) ((cplx P)⁻¹ * B * (cplx P)⁻¹) (P *ᵥ w) = testBilin v B w := by
  have hu : IsUnit (cplx P) := hP.map (algebraMap ℝ ℂ).mapMatrix
  have hud : IsUnit (cplx P).det := (isUnit_iff_isUnit_det _).1 hu
  have hQt : (cplx P)ᵀ = cplx P := by
    rw [cplx, ← Matrix.transpose_map, hPt]
  unfold testBilin
  rw [modelT_cvec_mulVec, modelT_cvec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec _ (cplx P)⁻¹ (cplx P), nonsing_inv_mul _ hud, Matrix.one_mulVec,
    Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, hQt, Matrix.vecMul_vecMul,
    Matrix.mul_nonsing_inv _ hud, Matrix.vecMul_one]

/-- `Σ̲ = diag(Σ, 1)` over `ℂ` is the complexification of the real `diag(Σ, 1)`. -/
private theorem modelT_ulSigma_eq (Sig : Matrix (Fin M) (Fin M) ℝ) :
    ulSigma N Sig = cplx (SigU (n := Fin N) Sig) := by
  unfold ulSigma SigU cplx
  rw [fromBlocks_map]
  simp

/-- `Σ̲⁻¹ (G − Π) Σ̲⁻¹` tested against `Σ̲ v`, `Σ̲ w` is `G − Π` tested against `v`, `w`. -/
private theorem modelT_testBilin_lawMat {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (X : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (v w : Fin M ⊕ Fin N → ℝ) :
    testBilin (SigU Sig *ᵥ v) (lawMat Sig X z) (SigU Sig *ᵥ w) =
      testBilin v (G Sig X z - piMat Sig (mFun N (specOf Sig) z)) w := by
  have hSU : IsUnit (SigU (n := Fin N) Sig) := by
    rw [isUnit_iff_isUnit_det, SigU, det_fromBlocks_zero₂₁]
    simpa using (isUnit_iff_isUnit_det _).1 hSig.isUnit
  have hSt : (SigU (n := Fin N) Sig)ᵀ = SigU Sig := by
    have : Sigᵀ = Sig := by
      rw [← conjTranspose_eq_transpose_of_trivial]
      exact hSig.1.eq
    unfold SigU
    rw [fromBlocks_transpose]
    simp [this]
  unfold lawMat
  rw [modelT_ulSigma_eq]
  exact modelT_testBilin_conj _ hSt hSU _ v w

/-- A real matrix `Σ̲` of the form `diag(Σ, 1)` with `Σ > 0` acts surjectively on test vectors. -/
private theorem modelT_SigU_surj {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (u : Fin M ⊕ Fin N → ℝ) : ∃ v, SigU Sig *ᵥ v = u := by
  have hSU : IsUnit (SigU (n := Fin N) Sig) := by
    rw [isUnit_iff_isUnit_det, SigU, det_fromBlocks_zero₂₁]
    simpa using (isUnit_iff_isUnit_det _).1 hSig.isUnit
  have hd : IsUnit (SigU (n := Fin N) Sig).det := (isUnit_iff_isUnit_det _).1 hSU
  exact ⟨(SigU Sig)⁻¹ *ᵥ u, by rw [Matrix.mulVec_mulVec, mul_nonsing_inv _ hd, one_mulVec]⟩

/-- Under (T_diag), the weighted laws for `T = Σ^{1/2}` are the laws (edge_G_result),
(edge_G_avg_result) (substitute `v ↦ Σ̲⁻¹ v`). -/
theorem anisoT_iff_aniso {Ω : Type*} [MeasureSpace Ω] {N : ℕ} {ε D : ℝ}
    {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {X : Ω → Matrix (Fin M) (Fin N) ℝ}
    {S : Set ℂ} (hS : ∀ z ∈ S, 0 < z.im) :
    (AnisotropicLawTAt N ε D (sigPow Sig (1 / 2)) X S ↔ AnisotropicLawAt N ε D Sig X S) ∧
      (AveragedLawTAt N ε D (sigPow Sig (1 / 2)) X S ↔ AveragedLawAt N ε D Sig X S) := by
  obtain ⟨hTT, hTt⟩ := sigPow_half hSig
  have hSS : sigPow Sig (1 / 2) * (sigPow Sig (1 / 2))ᵀ = Sig := by rw [hTt, hTT]
  constructor
  · unfold AnisotropicLawTAt AnisotropicLawAt ODomMatAt
    refine forall₂_congr fun z hz => ?_
    have hzim := hS z hz
    simp only [hSS, blockG_sqrt hSig _ hzim]
    constructor
    · intro h u u'
      obtain ⟨v, rfl⟩ := modelT_SigU_surj hSig u
      obtain ⟨w, rfl⟩ := modelT_SigU_surj hSig u'
      simp only [modelT_testBilin_lawMat hSig _ z v w]
      exact h v w
    · intro h v w
      have := h (SigU Sig *ᵥ v) (SigU Sig *ᵥ w)
      simp only [modelT_testBilin_lawMat hSig _ z v w] at this
      exact this
  · unfold AveragedLawTAt AveragedLawAt
    refine forall₂_congr fun z hz => ?_
    have hzim := hS z hz
    have e : ∀ x : Matrix (Fin M) (Fin N) ℝ, mNT (sigPow Sig (1 / 2)) x z = mN Sig x z :=
      fun x => by rw [mNT, modelT_RN_eq hSig, ← mN_eq_trace_GN hSig x hzim]
    simp only [e, hSS]

/-- The spectrum of a positive semidefinite matrix lies in `[0, ∞)`. -/
private theorem modelT_spec_nonneg {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosSemidef) :
    ∀ x ∈ spectrum ℝ Sig, 0 ≤ x := by
  rw [hSig.1.spectrum_real_eq_range_eigenvalues]
  rintro _ ⟨i, rfl⟩
  exact hSig.eigenvalues_nonneg i

/-- Every real function is continuous on the (finite) spectrum of a symmetric matrix. -/
private theorem modelT_contOn {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.IsHermitian)
    (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ Sig) := by
  rw [hSig.spectrum_real_eq_range_eigenvalues]
  exact (Set.finite_range _).continuousOn f

/-- Products of spectral calculi. -/
private theorem modelT_cfc_mul {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.IsHermitian)
    (f g h : ℝ → ℝ) (hfg : ∀ x ∈ spectrum ℝ Sig, f x * g x = h x) :
    cfc f Sig * cfc g Sig = cfc h Sig := by
  rw [← cfc_mul f g Sig (modelT_contOn hSig f) (modelT_contOn hSig g)]
  exact cfc_congr fun x hx => hfg x hx

/-- `(Σ^r)ᵀ = Σ^r`. -/
private theorem modelT_sigPow_transpose (Sig : Matrix (Fin M) (Fin M) ℝ) (r : ℝ) :
    (sigPow Sig r)ᵀ = sigPow Sig r := by
  rw [← conjTranspose_eq_transpose_of_trivial]
  exact (cfc_predicate (fun x : ℝ => if 0 < x then x ^ r else 0) Sig : IsSelfAdjoint _).star_eq

/-- `x^{1/2} x^{−1/2} = 1` and `x^{1/2} x^{1/2} = x` for `x > 0`. -/
private theorem modelT_rpow_half {x : ℝ} (hx : 0 < x) :
    x ^ (1 / 2 : ℝ) * x ^ (-(1 / 2) : ℝ) = 1 ∧ x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
  constructor
  · rw [← Real.rpow_add hx]
    norm_num
  · rw [← Real.rpow_add hx]
    norm_num

/-- `Σ^{1/2} Σ^{1/2} = Σ` for `Σ ≥ 0`. -/
private theorem modelT_sigPow_half_mul {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosSemidef) :
    sigPow Sig (1 / 2) * sigPow Sig (1 / 2) = Sig := by
  have h := modelT_cfc_mul hSig.1 (fun x : ℝ => if 0 < x then x ^ (1 / 2 : ℝ) else 0)
    (fun x : ℝ => if 0 < x then x ^ (1 / 2 : ℝ) else 0) id fun x hx => by
    by_cases h0 : 0 < x
    · simp only [h0, ↓reduceIte, id]
      exact (modelT_rpow_half h0).2
    · have : x = 0 := le_antisymm (not_lt.1 h0) (modelT_spec_nonneg hSig x hx)
      simp [this]
  have hid : cfc (id : ℝ → ℝ) Sig = Sig := cfc_id ℝ Sig hSig.1
  rw [hid] at h
  exact h

/-- `Σ^{1/2} (Σ^{−1/2} Σ^{−1/2}) = Σ^{−1/2}` for `Σ ≥ 0`. -/
private theorem modelT_sigPow_cancel {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosSemidef) :
    sigPow Sig (1 / 2) * (sigPow Sig (-(1 / 2)) * sigPow Sig (-(1 / 2))) =
      sigPow Sig (-(1 / 2)) := by
  have h1 := modelT_cfc_mul hSig.1 (fun x : ℝ => if 0 < x then x ^ (-(1 / 2) : ℝ) else 0)
    (fun x : ℝ => if 0 < x then x ^ (-(1 / 2) : ℝ) else 0)
    (fun x : ℝ => (if 0 < x then x ^ (-(1 / 2) : ℝ) else 0) *
      (if 0 < x then x ^ (-(1 / 2) : ℝ) else 0)) fun x _ => rfl
  have h2 := modelT_cfc_mul hSig.1 (fun x : ℝ => if 0 < x then x ^ (1 / 2 : ℝ) else 0)
    (fun x : ℝ => (if 0 < x then x ^ (-(1 / 2) : ℝ) else 0) *
      (if 0 < x then x ^ (-(1 / 2) : ℝ) else 0))
    (fun x : ℝ => if 0 < x then x ^ (-(1 / 2) : ℝ) else 0) fun x hx => by
    by_cases h0 : 0 < x
    · simp only [h0, ↓reduceIte]
      obtain ⟨h3, -⟩ := modelT_rpow_half h0
      linear_combination x ^ (-(1 / 2) : ℝ) * h3
    · simp [h0]
  unfold sigPow
  rw [h1]
  exact h2

/-- `Σ Σ^{−1/2} Σ^{−1/2}` is a symmetric idempotent matrix, the projection on `ran Σ`. -/
private theorem modelT_proj {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosSemidef) :
    (Sig * (sigPow Sig (-(1 / 2)) * sigPow Sig (-(1 / 2))))ᵀ =
        Sig * (sigPow Sig (-(1 / 2)) * sigPow Sig (-(1 / 2))) ∧
      (Sig * (sigPow Sig (-(1 / 2)) * sigPow Sig (-(1 / 2)))) *
        (Sig * (sigPow Sig (-(1 / 2)) * sigPow Sig (-(1 / 2)))) =
        Sig * (sigPow Sig (-(1 / 2)) * sigPow Sig (-(1 / 2))) := by
  have h1 := modelT_cfc_mul hSig.1 (fun x : ℝ => if 0 < x then x ^ (-(1 / 2) : ℝ) else 0)
    (fun x : ℝ => if 0 < x then x ^ (-(1 / 2) : ℝ) else 0)
    (fun x : ℝ => (if 0 < x then x ^ (-(1 / 2) : ℝ) else 0) *
      (if 0 < x then x ^ (-(1 / 2) : ℝ) else 0)) fun x _ => rfl
  have h2 := modelT_cfc_mul hSig.1 id
    (fun x : ℝ => (if 0 < x then x ^ (-(1 / 2) : ℝ) else 0) *
      (if 0 < x then x ^ (-(1 / 2) : ℝ) else 0))
    (fun x : ℝ => if 0 < x then (1 : ℝ) else 0) fun x hx => by
    by_cases h0 : 0 < x
    · simp only [h0, ↓reduceIte, id]
      obtain ⟨h3, h4⟩ := modelT_rpow_half h0
      calc x * (x ^ (-(1 / 2) : ℝ) * x ^ (-(1 / 2) : ℝ))
          = (x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) * (x ^ (-(1 / 2) : ℝ) * x ^ (-(1 / 2) : ℝ)) := by
            rw [h4]
        _ = (x ^ (1 / 2 : ℝ) * x ^ (-(1 / 2) : ℝ)) * (x ^ (1 / 2 : ℝ) * x ^ (-(1 / 2) : ℝ)) := by
            ring
        _ = 1 := by rw [h3]; norm_num
    · simp [h0]
  have h3 := modelT_cfc_mul hSig.1 (fun x : ℝ => if 0 < x then (1 : ℝ) else 0)
    (fun x : ℝ => if 0 < x then (1 : ℝ) else 0) (fun x : ℝ => if 0 < x then (1 : ℝ) else 0)
    fun x _ => by by_cases h0 : 0 < x <;> simp [h0]
  have hid : cfc (id : ℝ → ℝ) Sig = Sig := cfc_id ℝ Sig hSig.1
  rw [hid] at h2
  unfold sigPow
  rw [h1, h2]
  refine ⟨?_, h3⟩
  rw [← conjTranspose_eq_transpose_of_trivial]
  exact (cfc_predicate (fun x : ℝ => if 0 < x then (1 : ℝ) else 0) Sig : IsSelfAdjoint _).star_eq

/-- A symmetric idempotent real matrix does not increase the Euclidean norm. -/
private theorem modelT_testNorm_proj_le {ι : Type*} [Fintype ι]
    (P : Matrix ι ι ℝ) (hPt : Pᵀ = P) (hPP : P * P = P) (x : ι → ℝ) :
    testNorm (P *ᵥ x) ≤ testNorm x := by
  have hnn : ∀ y : ι → ℝ, 0 ≤ y ⬝ᵥ y := fun y => Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hk : (P *ᵥ x) ⬝ᵥ (P *ᵥ x) = (P *ᵥ x) ⬝ᵥ x := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, hPt, Matrix.vecMul_vecMul, hPP]
  have hd : (x - P *ᵥ x) ⬝ᵥ (x - P *ᵥ x) = x ⬝ᵥ x - (P *ᵥ x) ⬝ᵥ (P *ᵥ x) := by
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, dotProduct_comm x (P *ᵥ x), hk]
    ring
  have hle : (P *ᵥ x) ⬝ᵥ (P *ᵥ x) ≤ x ⬝ᵥ x := by
    have := hnn (x - P *ᵥ x)
    rw [hd] at this
    linarith
  unfold testNorm
  apply Real.sqrt_le_sqrt
  simpa [dotProduct, sq] using hle

/-- `P⁻¹ Q = Q P⁻¹` for commuting square matrices `P`, `Q`. -/
private theorem modelT_inv_comm {P Q : Matrix (Fin M) (Fin M) ℂ} (h : Q * P = P * Q) :
    P⁻¹ * Q = Q * P⁻¹ := by
  by_cases hP : IsUnit P.det
  · calc P⁻¹ * Q = P⁻¹ * (Q * P) * P⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hP, Matrix.mul_one]
      _ = Q * P⁻¹ := by
          rw [h, ← Matrix.mul_assoc, nonsing_inv_mul _ hP, Matrix.one_mul]
  · rw [nonsing_inv_apply_not_isUnit _ hP, Matrix.zero_mul, Matrix.mul_zero]

/-- `(z P)⁻¹ = z⁻¹ P⁻¹` for `z ≠ 0`. -/
private theorem modelT_inv_smul {z : ℂ} (hz : z ≠ 0) (P : Matrix (Fin M) (Fin M) ℂ) :
    (z • P)⁻¹ = z⁻¹ • P⁻¹ := by
  by_cases hP : IsUnit P.det
  · refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hz, one_smul,
      nonsing_inv_mul _ hP]
  · have hzP : ¬IsUnit (z • P).det := by
      rw [det_smul, IsUnit.mul_iff, not_and_or]
      exact Or.inr hP
    rw [nonsing_inv_apply_not_isUnit _ hP, nonsing_inv_apply_not_isUnit _ hzP, smul_zero]

/-- The `𝓘_M` block of `G − Π` for a general `T`, with `Σ = T Tᵀ`:
`z Σ^{1/2} (R_M + (z(1 + mΣ))⁻¹) Σ^{1/2}`. -/
private theorem modelT_blockG_MM {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ)
    (X : Matrix (Fin K) (Fin N) ℝ) {z : ℂ} (hz : z ≠ 0) (m : ℂ) :
    (blockG T X z - piMat (T * Tᵀ) m).toBlocks₁₁ =
      z • (cplx (sigPow (T * Tᵀ) (1 / 2)) *
        (RM T X z + (z • (1 + m • cplx (T * Tᵀ)))⁻¹) * cplx (sigPow (T * Tᵀ) (1 / 2))) := by
  have hP : (T * Tᵀ).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose T
  have hSS : cplx (T * Tᵀ) = cplx (sigPow (T * Tᵀ) (1 / 2)) * cplx (sigPow (T * Tᵀ) (1 / 2)) := by
    rw [← modelT_cplx_mul, modelT_sigPow_half_mul hP]
  set cS := cplx (sigPow (T * Tᵀ) (1 / 2)) with hcS
  set Q : Matrix (Fin M) (Fin M) ℂ := 1 + m • cplx (T * Tᵀ) with hQ
  have hcomm : Q * cS = cS * Q := by
    have h2 : cplx (T * Tᵀ) * cS = cS * cplx (T * Tᵀ) := by
      rw [hSS]
      exact Matrix.mul_assoc _ _ _
    simp only [hQ, Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.one_mul,
      Matrix.smul_mul, Matrix.mul_smul, h2]
  have hQi : cS * Q⁻¹ = Q⁻¹ * cS := (modelT_inv_comm hcomm.symm).symm
  have hL : (blockG T X z - piMat (T * Tᵀ) m).toBlocks₁₁ =
      z • (cS * RM T X z * cS) + cplx (T * Tᵀ) * Q⁻¹ := by
    ext i j
    simp [blockG, piMat, Matrix.toBlocks₁₁, sub_eq_add_neg, hQ, hcS]
  rw [hL, modelT_inv_smul hz, Matrix.mul_add, Matrix.add_mul, smul_add]
  congr 1
  rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hz, one_smul, hSS,
    Matrix.mul_assoc, Matrix.mul_assoc, ← hQi]

/-- `⟨v, R A Rᵀ w⟩ = ⟨Rᵀ v, A Rᵀ w⟩` for a real matrix `R`. -/
private theorem modelT_testBilin_cplx {ι : Type*} [Fintype ι] (R : Matrix ι ι ℝ)
    (A : Matrix ι ι ℂ) (v w : ι → ℝ) :
    testBilin v (cplx R * A * cplx Rᵀ) w = testBilin (Rᵀ *ᵥ v) A (Rᵀ *ᵥ w) := by
  unfold testBilin
  have ht : cplx Rᵀ = (cplx R)ᵀ := by ext; rfl
  rw [modelT_cvec_mulVec, modelT_cvec_mulVec]
  have e1 : (cplx R * A * cplx Rᵀ) *ᵥ (fun t => ((w t : ℝ) : ℂ)) =
      cplx R *ᵥ (A *ᵥ (cplx Rᵀ *ᵥ fun t => ((w t : ℝ) : ℂ))) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [e1, Matrix.dotProduct_mulVec, ht]
  simp only [Matrix.mulVec_transpose]

/-- `⟨v, R A R w⟩ = ⟨R v, A R w⟩` for a symmetric real matrix `R`. -/
private theorem modelT_testBilin_cplx_sym {ι : Type*} [Fintype ι] {R : Matrix ι ι ℝ}
    (A : Matrix ι ι ℂ) (hR : Rᵀ = R) (v w : ι → ℝ) :
    testBilin v (cplx R * A * cplx R) w = testBilin (R *ᵥ v) A (R *ᵥ w) := by
  have := modelT_testBilin_cplx R A v w
  rwa [hR] at this

/-- `⟨v, c A w⟩ = c ⟨v, A w⟩`. -/
private theorem modelT_testBilin_smul {ι : Type*} [Fintype ι] (v w : ι → ℝ) (c : ℂ)
    (A : Matrix ι ι ℂ) : testBilin v (c • A) w = c * testBilin v A w := by
  simp [testBilin, Matrix.smul_mulVec, dotProduct_smul]

/-- `Σ̲ (v, 0) = (Σ v, 0)`. -/
private theorem modelT_SigU_embM (Sig : Matrix (Fin M) (Fin M) ℝ) (v : Fin M → ℝ) :
    SigU (n := Fin N) Sig *ᵥ embM v = embM (Sig *ᵥ v) := by
  unfold SigU embM
  rw [fromBlocks_mulVec]
  ext i
  cases i <;> simp

/-- `Σ̲ (0, w) = (0, w)`. -/
private theorem modelT_SigU_embN (Sig : Matrix (Fin M) (Fin M) ℝ) (w : Fin N → ℝ) :
    SigU (n := Fin N) Sig *ᵥ embN w = embN w := by
  unfold SigU embN
  rw [fromBlocks_mulVec]
  ext i
  cases i <;> simp

/-- `|(v, 0)| = |v|`. -/
private theorem modelT_testNorm_embM (v : Fin M → ℝ) :
    testNorm (embM (n := Fin N) v) = testNorm v := by
  simp [testNorm, embM, Fintype.sum_sum_type]

/-- `|(0, v)| = |v|`. -/
private theorem modelT_testNorm_embN (v : Fin N → ℝ) :
    testNorm (embN (m := Fin M) v) = testNorm v := by
  simp [testNorm, embN, Fintype.sum_sum_type]

/-- `⟨(0, v), A (0, w)⟩ = ⟨v, A_{NN} w⟩`. -/
private theorem modelT_testBilin_embN (A : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ)
    (v w : Fin N → ℝ) :
    testBilin (embN (m := Fin M) v) A (embN w) = testBilin v A.toBlocks₂₂ w :=
  ent_embN_embN A v w

/-- The `𝓘_N` block of `G − Π` for a general `T`: `R_N − m`. -/
private theorem modelT_blockG_NN {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ)
    (X : Matrix (Fin K) (Fin N) ℝ) (z m : ℂ) :
    (blockG T X z - piMat (T * Tᵀ) m).toBlocks₂₂ = RN T X z - m • (1 : Matrix (Fin N) (Fin N) ℂ) := by
  ext μ ν
  simp [blockG, piMat, Matrix.toBlocks₂₂]

/-- From the law at `ε/2`: `c ξ ≺ ζ` at `ε` once `c ≤ N^{ε/2}` and `ξ ≥ 0`. -/
private theorem modelT_domAt_half {Ω : Type*} [MeasureSpace Ω] {N : ℕ} (hN : 1 ≤ N)
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

/-- The `𝓘_M` block of `G − Π` tested against `(Σ^{−1} v', 0)`, `(Σ^{−1} w', 0)`, where
`Σ^{−1} = Σ^{−1/2} Σ^{−1/2}`, is `z ⟨v', Σ^{−1/2} (R_M + (z(1 + mΣ))⁻¹) Σ^{−1/2} w'⟩`. -/
private theorem modelT_bilin_MM {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ)
    (X : Matrix (Fin K) (Fin N) ℝ) {z : ℂ} (hz : z ≠ 0) (m : ℂ) (v' w' : Fin M → ℝ)
    (hP : (T * Tᵀ).PosSemidef) :
    testBilin (embM (n := Fin N) (sigPow (T * Tᵀ) (-(1 / 2)) *ᵥ
        (sigPow (T * Tᵀ) (-(1 / 2)) *ᵥ v'))) (blockG T X z - piMat (T * Tᵀ) m)
      (embM (sigPow (T * Tᵀ) (-(1 / 2)) *ᵥ (sigPow (T * Tᵀ) (-(1 / 2)) *ᵥ w'))) =
    z * testBilin v' (cplx (sigPow (T * Tᵀ) (-(1 / 2))) *
      (RM T X z + (z • (1 + m • cplx (T * Tᵀ)))⁻¹) * cplx (sigPow (T * Tᵀ) (-(1 / 2)))) w' := by
  have hSpt := modelT_sigPow_transpose (T * Tᵀ) (1 / 2)
  have hSit := modelT_sigPow_transpose (T * Tᵀ) (-(1 / 2))
  have hcancel := modelT_sigPow_cancel hP
  have hSv : ∀ x : Fin M → ℝ, sigPow (T * Tᵀ) (1 / 2) *ᵥ (sigPow (T * Tᵀ) (-(1 / 2)) *ᵥ
      (sigPow (T * Tᵀ) (-(1 / 2)) *ᵥ x)) = sigPow (T * Tᵀ) (-(1 / 2)) *ᵥ x := fun x => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, hcancel]
  have e1 : ∀ (A : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) (a b : Fin M → ℝ),
      testBilin (embM (n := Fin N) a) A (embM b) = testBilin a A.toBlocks₁₁ b :=
    fun A a b => ent_embM_embM A a b
  rw [e1, modelT_blockG_MM T X hz m, modelT_testBilin_smul, modelT_testBilin_cplx_sym _ hSpt,
    hSv, hSv, ← modelT_testBilin_cplx_sym _ hSit]

/-- `|Σ̲ (Σ^{−1} v', 0)| ≤ |v'|` for `Σ^{−1} = Σ^{−1/2} Σ^{−1/2}`, since `Σ Σ^{−1}` is an
orthogonal projection. -/
private theorem modelT_testNorm_SigU_le (Sig : Matrix (Fin M) (Fin M) ℝ) (hSig : Sig.PosSemidef)
    (v' : Fin M → ℝ) :
    testNorm (SigU (n := Fin N) Sig *ᵥ embM (sigPow Sig (-(1 / 2)) *ᵥ
      (sigPow Sig (-(1 / 2)) *ᵥ v'))) ≤ testNorm v' := by
  obtain ⟨hPt, hPP⟩ := modelT_proj hSig
  rw [modelT_SigU_embM, modelT_testNorm_embM]
  have : Sig *ᵥ (sigPow Sig (-(1 / 2)) *ᵥ (sigPow Sig (-(1 / 2)) *ᵥ v')) =
      (Sig * (sigPow Sig (-(1 / 2)) * sigPow Sig (-(1 / 2)))) *ᵥ v' := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [this]
  exact modelT_testNorm_proj_le _ hPt hPP v'

/-- The real inequality chain of the `R_M` part. -/
private theorem modelT_ineq {t Ψ a a' b b' q nz : ℝ} (ht : 0 < t) (hΨ : 0 ≤ Ψ)
    (ha'0 : 0 ≤ a') (hab : a ≤ b) (hab' : a' ≤ b') (hb0 : 0 ≤ b) (hzt : 1 ≤ nz * t)
    (hnz : 0 < nz) (hq : t * t * (Ψ * b * b') < q) : t * (Ψ * a * a') < nz * q := by
  have h1 : Ψ * a * a' ≤ Ψ * b * b' :=
    mul_le_mul (mul_le_mul_of_nonneg_left hab hΨ) hab' ha'0 (mul_nonneg hΨ hb0)
  have hX : 0 ≤ Ψ * b * b' := mul_nonneg (mul_nonneg hΨ hb0) (ha'0.trans hab')
  calc t * (Ψ * a * a') ≤ t * (Ψ * b * b') := mul_le_mul_of_nonneg_left h1 ht.le
    _ ≤ (nz * t) * (t * (Ψ * b * b')) := le_mul_of_one_le_left (mul_nonneg ht.le hX) hzt
    _ = nz * (t * t * (Ψ * b * b')) := by ring
    _ < nz * q := mul_lt_mul_of_pos_left hq hnz

/-- The weighted law at `ε/2` gives (R_N_edge) and (R_M_edge) (pseudo-inverse form) at `ε` for a
general `T`, once `τ⁻¹ ≤ N^{ε/2}`. -/
theorem rLawsT_of_anisoT {Ω : Type*} [MeasureSpace Ω] {τ : ℝ} (hτ : 0 < τ) {N : ℕ} (hN : 1 ≤ N)
    {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ) {X : Ω → Matrix (Fin K) (Fin N) ℝ} {S : Set ℂ}
    (hS : S ⊆ specDomain τ N) {ε D : ℝ} (hNτ : τ⁻¹ ≤ (N : ℝ) ^ (ε / 2))
    (h : AnisotropicLawTAt N (ε / 2) D T X S) :
    RNLawAt N ε D (T * Tᵀ) T X S ∧ RMLawAt N ε D (T * Tᵀ) T X S := by
  have hP : (T * Tᵀ).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose T
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
    have key := modelT_domAt_half hN hc (fun ω => norm_nonneg _) (h z hz (embN v) (embN w))
    convert key using 2
    · rename_i ω
      beta_reduce
      rw [one_mul, modelT_testBilin_embN, modelT_blockG_NN]
    · beta_reduce
      rw [modelT_SigU_embN, modelT_SigU_embN, modelT_testNorm_embN, modelT_testNorm_embN]
  · intro z hz v' w'
    obtain ⟨hzim, hτz, -, -, -⟩ := hS hz
    have hz0 : z ≠ 0 := fun h0 => by simp [h0] at hzim
    have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz0
    have hc : ‖z‖⁻¹ ≤ (N : ℝ) ^ (ε / 2) := le_trans (inv_anti₀ hτ hτz) hNτ
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have ht : 0 < (N : ℝ) ^ (ε / 2) := Real.rpow_pos_of_pos hN0 _
    have hzt : 1 ≤ ‖z‖ * (N : ℝ) ^ (ε / 2) := by
      have := mul_le_mul_of_nonneg_left hc hzn.le
      rwa [mul_inv_cancel₀ hzn.ne'] at this
    have hsq : (N : ℝ) ^ ε = (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) := by
      rw [← Real.rpow_add hN0]; ring_nf
    have hΨ : 0 ≤ Psi N (specOf (T * Tᵀ)) z := by
      unfold Psi
      have : 0 < (N : ℝ) * z.im := mul_pos hN0 hzim
      positivity
    have hkey := h z hz (embM (sigPow (T * Tᵀ) (-(1 / 2)) *ᵥ (sigPow (T * Tᵀ) (-(1 / 2)) *ᵥ v')))
      (embM (sigPow (T * Tᵀ) (-(1 / 2)) *ᵥ (sigPow (T * Tᵀ) (-(1 / 2)) *ᵥ w')))
    have ha := modelT_testNorm_SigU_le (N := N) (T * Tᵀ) hP v'
    have hb := modelT_testNorm_SigU_le (N := N) (T * Tᵀ) hP w'
    unfold DomAt at hkey ⊢
    refine le_trans (measure_mono ?_) hkey
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [modelT_bilin_MM T (X ω) hz0 _ v' w' hP, norm_mul]
    have hq := hω
    rw [hsq] at hq
    exact modelT_ineq ht hΨ (Real.sqrt_nonneg _) ha hb
      (Real.sqrt_nonneg _) hzt hzn hq

/-- Singular `Σ = diag(1, 0)` (`T = (1; 0)`, `M = 2`, `M̂ = 1`): `T Tᵀ = Σ`. -/
example : !![(1 : ℝ); 0] * (!![(1 : ℝ); 0])ᵀ = diagonal ![1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

#print axioms Anisotropic.IsModelT
#print axioms Anisotropic.isModelT_sqrt_iff
#print axioms Anisotropic.IsModelT.densityAssumptions
#print axioms Anisotropic.IsModelT.mono
#print axioms Anisotropic.blockG
#print axioms Anisotropic.mNT
#print axioms Anisotropic.AnisotropicLawTAt
#print axioms Anisotropic.AveragedLawTAt
#print axioms Anisotropic.blockG_sqrt
#print axioms Anisotropic.anisoT_iff_aniso
#print axioms Anisotropic.rLawsT_of_anisoT
end Anisotropic
