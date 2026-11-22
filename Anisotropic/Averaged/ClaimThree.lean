module

public import Anisotropic.Averaged.Column
public import Anisotropic.Averaged.Defs
public import Anisotropic.Comparison.Ladder
public import Anisotropic.Comparison.PrelimBounds
public import Anisotropic.Comparison.TaggedWords
public import Anisotropic.Comparison.WordBounds
public import Anisotropic.Comparison.Words
public import Anisotropic.Entrywise.Defs
public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.Framework.Model
public import Anisotropic.LinAlg.Basic
public import Anisotropic.Probability.LDE.Conditional

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # (avg_step 1): (avg_pf_claim) for `n = 3` at one tagged tuple, `ν ≠ μ` (§9) -/

/-! ## The deterministic matrix `Π` -/

private theorem claimT_diag {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) :
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

/-- `(Σ (1 + wΣ)⁻¹)_{jl} = ∑ₖ U_{jk} σₖ (1 + σₖ w)⁻¹ U_{lk}` for `Σ = U diag(σ) Uᵀ`. -/
private theorem claimT_SigInv_entry {Sig U : Matrix (Fin M) (Fin M) ℝ} {σ : Fin M → ℝ}
    (h₂ : U * Uᵀ = 1) (h₁ : Uᵀ * U = 1) (hS : Sig = U * diagonal σ * Uᵀ) {w : ℂ}
    (hw : ∀ i, 1 + (σ i : ℂ) * w ≠ 0) (j l : Fin M) :
    (cplx Sig * (1 + w • cplx Sig)⁻¹) j l =
      ∑ k, (U j k : ℂ) * ((σ k : ℂ) * (1 + (σ k : ℂ) * w)⁻¹) * (U l k : ℂ) := by
  have c₂ : (cplx Uᵀ)ᵀ * cplx Uᵀ = 1 := by
    simp only [cplx]
    rw [← transpose_map, transpose_transpose, ← Matrix.map_mul, h₂,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have c₁ : cplx Uᵀ * (cplx Uᵀ)ᵀ = 1 := by
    simp only [cplx]
    rw [← transpose_map, transpose_transpose, ← Matrix.map_mul, h₁,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have e1 : cplx Sig = (cplx Uᵀ)ᵀ * diagonal (fun i => (σ i : ℂ)) * cplx Uᵀ := by
    simp only [cplx]
    rw [hS, ← transpose_map, transpose_transpose, Matrix.map_mul, Matrix.map_mul,
      diagonal_map (map_zero _)]
    rfl
  have hT : 1 + w • cplx Sig =
      (cplx Uᵀ)ᵀ * diagonal (fun i => 1 + (σ i : ℂ) * w) * cplx Uᵀ := by
    have e2 : diagonal (fun i => 1 + (σ i : ℂ) * w) =
        1 + w • diagonal (fun i => (σ i : ℂ)) := by
      rw [← diagonal_one, ← diagonal_smul, diagonal_add]
      congr 1
      funext i
      simp [mul_comm]
    rw [e2, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, c₂, Matrix.mul_smul,
      Matrix.smul_mul, e1]
  have hinv : (1 + w • cplx Sig)⁻¹ =
      (cplx Uᵀ)ᵀ * diagonal (fun i => (1 + (σ i : ℂ) * w)⁻¹) * cplx Uᵀ := by
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
  have hprod : cplx Sig * (1 + w • cplx Sig)⁻¹ = (cplx Uᵀ)ᵀ *
      diagonal (fun i => (σ i : ℂ) * (1 + (σ i : ℂ) * w)⁻¹) * cplx Uᵀ := by
    rw [hinv, e1]
    calc (cplx Uᵀ)ᵀ * diagonal (fun i => (σ i : ℂ)) * cplx Uᵀ *
          ((cplx Uᵀ)ᵀ * diagonal (fun i => (1 + (σ i : ℂ) * w)⁻¹) * cplx Uᵀ)
        = (cplx Uᵀ)ᵀ * (diagonal (fun i => (σ i : ℂ)) * (cplx Uᵀ * (cplx Uᵀ)ᵀ) *
            diagonal (fun i => (1 + (σ i : ℂ) * w)⁻¹)) * cplx Uᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [c₁, Matrix.mul_one, diagonal_mul_diagonal]
  rw [hprod]
  simp only [Matrix.mul_apply, cplx, Matrix.diagonal_apply, Matrix.transpose_apply,
    Matrix.map_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Complex.coe_algebraMap]

/-- `∑_l |(U a)_l|² = ∑_k |a_k|²` for `Uᵀ U = 1`. -/
private theorem claimT_sum_normSq {U : Matrix (Fin M) (Fin M) ℝ} (h₁ : Uᵀ * U = 1)
    (a : Fin M → ℂ) :
    ∑ l, ‖∑ k, (U l k : ℂ) * a k‖ ^ 2 = ∑ k, ‖a k‖ ^ 2 := by
  have hU : ∀ x : Fin M → ℝ, ∑ l, (U *ᵥ x) l ^ 2 = ∑ l, x l ^ 2 := by
    intro x
    have e : (U *ᵥ x) ⬝ᵥ (U *ᵥ x) = x ⬝ᵥ x := by
      rw [dotProduct_mulVec, vecMul_mulVec, ← Matrix.mulVec_transpose, transpose_mul,
        transpose_transpose, h₁, one_mulVec]
    simpa [dotProduct, sq] using e
  have hre : ∀ l, (∑ k, (U l k : ℂ) * a k).re = (U *ᵥ fun k => (a k).re) l := by
    intro l
    simp [mulVec, dotProduct, Complex.re_sum]
  have him : ∀ l, (∑ k, (U l k : ℂ) * a k).im = (U *ᵥ fun k => (a k).im) l := by
    intro l
    simp [mulVec, dotProduct, Complex.im_sum]
  have hn : ∀ x : ℂ, ‖x‖ ^ 2 = x.re ^ 2 + x.im ^ 2 := fun x => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  simp only [hn, Finset.sum_add_distrib, hre, him, hU]

private theorem claimT_row_sq {K : ℕ} {U : Matrix (Fin K) (Fin K) ℝ} (h₂ : U * Uᵀ = 1)
    (i : Fin K) : ∑ k, U i k ^ 2 = 1 := by
  have := congrFun (congrFun h₂ i) i
  simpa [Matrix.mul_apply, sq, Matrix.one_apply] using this

private theorem claimT_col_sq {K : ℕ} {U : Matrix (Fin K) (Fin K) ℝ} (h₁ : Uᵀ * U = 1)
    (k : Fin K) : ∑ j, U j k ^ 2 = 1 := by
  have := congrFun (congrFun h₁ k) k
  simpa [Matrix.mul_apply, sq, Matrix.one_apply] using this

/-- The `𝓘_M × 𝓘_M` block of `Π`: `|Π_{jl}| ≤ τ⁻¹c⁻¹`, `∑_l |Π_{jl}|² ≤ (τ⁻¹c⁻¹)²`, and
`∑_j Π_{jj} = −∑_k σ_k (1 + σ_k w)⁻¹`, under (bound_Sigma) and `|1 + σ_k w| ≥ c`. -/
private theorem claimT_PiM {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} (hS : SigmaAssumption τ Sig)
    (hτ : 0 < τ) (hc : 0 < c) {w : ℂ} (hOne : ∀ i, c ≤ ‖1 + (specOf Sig i : ℂ) * w‖) :
    (∀ j l, ‖(cplx Sig * (1 + w • cplx Sig)⁻¹) j l‖ ≤ τ⁻¹ * c⁻¹) ∧
    (∀ j, ∑ l, ‖(cplx Sig * (1 + w • cplx Sig)⁻¹) j l‖ ^ 2 ≤ (τ⁻¹ * c⁻¹) ^ 2) ∧
    ∑ j, (cplx Sig * (1 + w • cplx Sig)⁻¹) j j =
      ∑ k, (specOf Sig k : ℂ) * (1 + (specOf Sig k : ℂ) * w)⁻¹ ∧
    (∀ j l, (cplx Sig * (1 + w • cplx Sig)⁻¹) j l = (cplx Sig * (1 + w • cplx Sig)⁻¹) l j) := by
  obtain ⟨U, h₂, h₁, hSd, hσ⟩ := claimT_diag hS.posDef
  have hw : ∀ i, 1 + (specOf Sig i : ℂ) * w ≠ 0 := fun i h0 => by
    have := hOne i
    rw [h0, norm_zero] at this
    linarith
  have hle : ∀ k, specOf Sig k ≤ τ⁻¹ := fun k => by
    rw [specOf_eq hS.posDef.isHermitian]; exact hS.eigenvalues_le k
  set d : Fin M → ℂ := fun k => (specOf Sig k : ℂ) * (1 + (specOf Sig k : ℂ) * w)⁻¹ with hd
  have hdle : ∀ k, ‖d k‖ ≤ τ⁻¹ * c⁻¹ := fun k => by
    simp only [hd]
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hσ k).le]
    exact mul_le_mul (hle k) (inv_anti₀ hc (hOne k)) (inv_nonneg.2 (norm_nonneg _))
      ((hσ k).le.trans (hle k))
  have hD0 : 0 ≤ τ⁻¹ * c⁻¹ := by have := hτ.le; positivity
  have he := claimT_SigInv_entry h₂ h₁ hSd hw
  refine ⟨fun j l => ?_, fun j => ?_, ?_, fun j l => ?_⟩
  · rw [he]
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun k => |U j k|) (fun k => |U l k|)
    simp only [sq_abs] at hcs
    rw [claimT_row_sq h₂, claimT_row_sq h₂, Real.sqrt_one, mul_one] at hcs
    calc ‖∑ k, (U j k : ℂ) * d k * (U l k : ℂ)‖ ≤ ∑ k, τ⁻¹ * c⁻¹ * (|U j k| * |U l k|) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs]
          have := mul_le_mul_of_nonneg_left (hdle k) (abs_nonneg (U j k))
          nlinarith [abs_nonneg (U l k), abs_nonneg (U j k)]
      _ = τ⁻¹ * c⁻¹ * ∑ k, |U j k| * |U l k| := by rw [Finset.mul_sum]
      _ ≤ τ⁻¹ * c⁻¹ * 1 := mul_le_mul_of_nonneg_left hcs hD0
      _ = τ⁻¹ * c⁻¹ := mul_one _
  · have e1 : ∀ l, (cplx Sig * (1 + w • cplx Sig)⁻¹) j l =
        ∑ k, (U l k : ℂ) * ((U j k : ℂ) * d k) := fun l => by
      rw [he]; exact Finset.sum_congr rfl fun k _ => by ring
    simp only [e1]
    rw [claimT_sum_normSq h₁]
    calc ∑ k, ‖(U j k : ℂ) * d k‖ ^ 2 ≤ ∑ k, U j k ^ 2 * (τ⁻¹ * c⁻¹) ^ 2 := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hdle k) 2)
            (sq_nonneg _)
      _ = (τ⁻¹ * c⁻¹) ^ 2 := by rw [← Finset.sum_mul, claimT_row_sq h₂, one_mul]
  · simp only [he]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := claimT_col_sq h₁ k
    have e : ∑ j, (U j k : ℂ) * d k * (U j k : ℂ) = ((∑ j, U j k ^ 2 : ℝ) : ℂ) * d k := by
      push_cast
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e, this]
    simp [hd]
  · rw [he, he]
    exact Finset.sum_congr rfl fun k _ => by ring

/-- The setting of §7 gives the density assumptions on the eigenvalues of `Σ`. -/
private theorem claimT_density {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) : DensityAssumptions τ N (specOf Sig) :=
  (IsModel.diagModel_specOf (Ω := GaussSpace M N)
    ⟨hset.ratio_ge, hset.ratio_le, (gaussX_isGaussianEnsemble M N).entryAssumption hN,
      hset.sigma⟩).densityAssumptions hset.pos

/-- `Π` on `S`: `|Π_{st}| ≤ τ⁻¹c⁻¹ + C_m`, `∑_l |Π_{jl}|² ≤ (τ⁻¹c⁻¹)²` on `𝓘_M`, and
`N⁻¹ ∑_{j ∈ 𝓘_M} Π_{jj} = −z − m⁻¹` (m_sc_eq). -/
private theorem claimT_Pi {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) {z : ℂ} (hz : z ∈ S) :
    (∀ s t, ‖PiZ N Sig z s t‖ ≤ τ⁻¹ * c⁻¹ + mBoundConst τ) ∧
    (∀ j, ∑ l, ‖PiZ N Sig z (Sum.inl j) (Sum.inl l)‖ ^ 2 ≤ (τ⁻¹ * c⁻¹) ^ 2) ∧
    (∀ j, ∑ l, ‖PiZ N Sig z (Sum.inl l) (Sum.inl j)‖ ^ 2 ≤ (τ⁻¹ * c⁻¹) ^ 2) ∧
    (N : ℂ)⁻¹ * ∑ j, PiZ N Sig z (Sum.inl j) (Sum.inl j) = -z - (mFun N (specOf Sig) z)⁻¹ := by
  have hτ := hset.pos
  have hc := hset.c_pos
  have hzD := hset.domain.1 hz
  obtain ⟨-, hm2, -⟩ := gen_prop_m_specDomain (claimT_density hset hN) hzD
  have hCm := mBoundConst_pos hτ
  have hD0 : 0 ≤ τ⁻¹ * c⁻¹ := by positivity
  obtain ⟨h1, h2, h3, h4⟩ := claimT_PiM hset.sigma hτ hc (hset.oneXm z hz)
  refine ⟨fun s t => ?_, fun j => ?_, fun j => ?_, ?_⟩
  · rcases s with j | ν <;> rcases t with l | ν'
    · simp only [PiZ, piMat, fromBlocks_apply₁₁, Matrix.neg_apply, norm_neg]
      linarith [h1 j l]
    · simp [PiZ, piMat]; positivity
    · simp [PiZ, piMat]; positivity
    · simp only [PiZ, piMat, fromBlocks_apply₂₂, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
        mul_ite, mul_one, mul_zero]
      split_ifs
      · linarith
      · simp only [norm_zero]; positivity
  · simpa [PiZ, piMat] using h2 j
  · have := h2 j
    simp only [PiZ, piMat, fromBlocks_apply₁₁, Matrix.neg_apply, norm_neg]
    simpa only [h4] using this
  · have hσ : ∀ i, 0 ≤ specOf Sig i := fun i => by
      rw [specOf_eq hset.sigma.posDef.isHermitian]
      exact (hset.sigma.posDef.eigenvalues_pos i).le
    have hf := (mFun_spec N (specOf Sig) hσ hzD.1).2
    unfold fC at hf
    set m := mFun N (specOf Sig) z
    have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    have e : ∑ i, (specOf Sig i : ℂ) / (N * (1 + specOf Sig i * m)) =
        (N : ℂ)⁻¹ * ∑ k, (specOf Sig k : ℂ) * (1 + (specOf Sig k : ℂ) * m)⁻¹ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [div_eq_mul_inv, mul_inv]; ring
    have e2 : ∑ j, PiZ N Sig z (Sum.inl j) (Sum.inl j) =
        -∑ j, (cplx Sig * (1 + m • cplx Sig)⁻¹) j j := by
      simp [PiZ, piMat, m, Finset.sum_neg_distrib]
    rw [e2, h3, mul_neg, ← e]
    linear_combination -hf

/-- `Σ_{jj} ≤ τ⁻¹` under (bound_Sigma). -/
private theorem claimT_Sig_diag_le {τ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hS : SigmaAssumption τ Sig) (j : Fin M) : Sig j j ≤ τ⁻¹ := by
  obtain ⟨U, h₂, -, hSd, hσ⟩ := claimT_diag hS.posDef
  have hle : ∀ k, specOf Sig k ≤ τ⁻¹ := fun k => by
    rw [specOf_eq hS.posDef.isHermitian]; exact hS.eigenvalues_le k
  have e : Sig j j = ∑ k, U j k ^ 2 * specOf Sig k := by
    conv_lhs => rw [hSd]
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply, mul_ite,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e]
  calc ∑ k, U j k ^ 2 * specOf Sig k ≤ ∑ k, U j k ^ 2 * τ⁻¹ :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hle k) (sq_nonneg _)
    _ = τ⁻¹ := by rw [← Finset.sum_mul, claimT_row_sq h₂, one_mul]

/-- The rough bound `|G_{st}| ≤ (1 + 5|z|) τ⁻¹ / η` (opbound). -/
private theorem claimT_G_rough {τ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hS : SigmaAssumption τ Sig) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (A : Matrix (Fin M) (Fin N) ℝ)
    {z : ℂ} (hz : 0 < z.im) (s t : Fin M ⊕ Fin N) :
    ‖G Sig A z s t‖ ≤ (1 + 5 * ‖z‖) / z.im * τ⁻¹ := by
  have hτi : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  have hq : ∀ u : Fin M ⊕ Fin N, eI u ⬝ᵥ SigU (n := Fin N) Sig *ᵥ eI u ≤ τ⁻¹ := by
    intro u
    have e : eI u ⬝ᵥ SigU (n := Fin N) Sig *ᵥ eI u = SigU (n := Fin N) Sig u u := by
      simp [eI, dotProduct, mulVec, Pi.single_apply]
    rw [e]
    rcases u with j | ν
    · simpa [SigU] using claimT_Sig_diag_le hS j
    · simpa [SigU] using hτi
  have h := opbound hS.posDef A hz (eI s) (eI t)
  rw [ent_eI_eI] at h
  have hs := Real.sqrt_le_sqrt (hq s)
  have ht := Real.sqrt_le_sqrt (hq t)
  have hsq : Real.sqrt τ⁻¹ * Real.sqrt τ⁻¹ = τ⁻¹ := Real.mul_self_sqrt (by positivity)
  have hK : 0 ≤ (1 + 5 * ‖z‖) / z.im := by positivity
  calc ‖G Sig A z s t‖ ≤ _ := h
    _ ≤ (1 + 5 * ‖z‖) / z.im * Real.sqrt τ⁻¹ * Real.sqrt τ⁻¹ := by
        rw [mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul hs ht (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)) hK
    _ = (1 + 5 * ‖z‖) / z.im * τ⁻¹ := by rw [mul_assoc, hsq]

/-! ## The column forms and the minor `G^{(μ)}` -/

private theorem claimT_Gmu_row (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (μ : Fin N) (t : Fin M ⊕ Fin N) : Gmu Sig A z μ (Sum.inr μ) t = 0 := by
  simp [Gmu, G1, Gm]

private theorem claimT_Gmu_col (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (μ : Fin N) (s : Fin M ⊕ Fin N) : Gmu Sig A z μ s (Sum.inr μ) = 0 := by
  simp [Gmu, G1, Gm]

private theorem claimT_linForm_colC (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (μ : Fin N) (s : Fin M ⊕ Fin N) (y : Fin M → ℝ) :
    linForm (colC Sig A z (eI s) μ) y = ∑ j, Gmu Sig A z μ s (Sum.inl j) * (y j : ℂ) := by
  simp only [linForm, colC, ent_eI_eI]

private theorem claimT_linForm_rowC (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (μ : Fin N) (s : Fin M ⊕ Fin N) (y : Fin M → ℝ) :
    linForm (rowC Sig A z (eI s) μ) y = ∑ j, Gmu Sig A z μ (Sum.inl j) s * (y j : ℂ) := by
  simp only [linForm, rowC, ent_eI_eI]

/-- (Gia), (Gij): `G_{sμ} = −G_μμ (G^{(μ)} X)_{sμ}` for `s ≠ μ`. -/
private theorem claimT_G_col {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (μ : Fin N) (s : Fin M ⊕ Fin N)
    (hs : s ≠ Sum.inr μ) :
    G Sig A z s (Sum.inr μ) = -G Sig A z (Sum.inr μ) (Sum.inr μ) *
      linForm (colC Sig A z (eI s) μ) (fun j => A j μ) := by
  have hGX : ∀ u, (G1 Sig A z (Sum.inr μ) * Xhat A) u (Sum.inr μ) =
      ∑ j, G1 Sig A z (Sum.inr μ) u (Sum.inl j) * (A j μ : ℂ) := by
    intro u; simp [Matrix.mul_apply, Fintype.sum_sum_type, Xhat, cplx]
  rw [claimT_linForm_colC]
  rcases s with j | ν
  · rw [(Gia hSig A hz j μ).1, hGX]
  · have hν : ν ≠ μ := fun h => hs (by rw [h])
    rw [(Gij hSig A hz ν μ hν).2.1, hGX]

/-- (Gia), (Gij): `G_{μs} = −G_μμ (X^* G^{(μ)})_{μs}` for `s ≠ μ`. -/
private theorem claimT_G_row {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (μ : Fin N) (s : Fin M ⊕ Fin N)
    (hs : s ≠ Sum.inr μ) :
    G Sig A z (Sum.inr μ) s = -G Sig A z (Sum.inr μ) (Sum.inr μ) *
      linForm (rowC Sig A z (eI s) μ) (fun j => A j μ) := by
  have hXG : ∀ u, ((Xhat A)ᵀ * G1 Sig A z (Sum.inr μ)) (Sum.inr μ) u =
      ∑ j, G1 Sig A z (Sum.inr μ) (Sum.inl j) u * (A j μ : ℂ) := by
    intro u; simp [Matrix.mul_apply, Fintype.sum_sum_type, Xhat, cplx, mul_comm]
  rw [claimT_linForm_rowC]
  rcases s with j | ν
  · rw [(Gia hSig A hz j μ).2, hXG]
  · have hν : μ ≠ ν := fun h => hs (by rw [h])
    rw [(Gij hSig A hz μ ν hν).1, hXG]

/-- `G^{(μ)}_{st} = G_{st}` of the matrix with column `μ` set to zero, `s, t ≠ μ`. -/
private theorem claimT_Gmu_eq {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (μ : Fin N) (s t : Fin M ⊕ Fin N)
    (hs : s ≠ Sum.inr μ) (ht : t ≠ Sum.inr μ) :
    Gmu Sig A z μ s t = G Sig (updCol A μ 0) z s t := by
  rw [← Gmu_updCol Sig A z μ 0, Gmu, Gstu hSig _ hz _ s t hs ht, claimT_G_col hSig _ hz μ s hs]
  have h0 : (fun j => updCol A μ 0 j μ) = 0 := by funext j; simp [updCol]
  rw [h0]
  simp [linForm]

/-- The rough bound `|G^{(μ)}_{st}| ≤ (1 + 5|z|) τ⁻¹ / η`. -/
private theorem claimT_Gmu_rough {τ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hS : SigmaAssumption τ Sig) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (A : Matrix (Fin M) (Fin N) ℝ)
    {z : ℂ} (hz : 0 < z.im) (μ : Fin N) (s t : Fin M ⊕ Fin N) :
    ‖Gmu Sig A z μ s t‖ ≤ (1 + 5 * ‖z‖) / z.im * τ⁻¹ := by
  by_cases hs : s = Sum.inr μ
  · rw [hs, claimT_Gmu_row]; simp only [norm_zero]; positivity
  by_cases ht : t = Sum.inr μ
  · rw [ht, claimT_Gmu_col]; simp only [norm_zero]; positivity
  rw [claimT_Gmu_eq hS.posDef A hz μ s t hs ht]
  exact claimT_G_rough hS hτ hτ1 _ hz s t

/-- `v̄ = e_ν` for `v = e_ν`, `ν ∈ 𝓘_N`. -/
private theorem claimT_vbar_inr (Sig : Matrix (Fin M) (Fin M) ℝ) (ν : Fin N) :
    vbar Sig (eI (Sum.inr ν) : Fin M ⊕ Fin N → ℝ) = eI (Sum.inr ν) := by
  funext s
  rcases s with i | j
  · have h0 : ((eI (Sum.inr ν) : Fin M ⊕ Fin N → ℝ) ∘ Sum.inl) = 0 := by
      funext k
      simp [eI]
    simp only [vbar, Sum.elim_inl]
    rw [h0, mulVec_zero]
    simp [eI]
  · simp [vbar]

/-- `ℤ₂` tags: `|σ|_v = 0` means no tag `2`. -/
private theorem claimT_ne_two {n : ℕ} {σ : Fin (n + 1) → Fin 3} (hv : tagV σ = 0)
    (l : Fin (n + 1)) :
    σ l ≠ 2 := by
  intro h
  have := (Finset.sum_eq_zero_iff.1 hv) l (Finset.mem_univ l)
  simp [h] at this

/-- The empty word with tag `0` at `v = e_ν`, `ν ≠ μ`: `A⁰ = G^{(μ)}_{νν} − Π_{νν}`. -/
private theorem claimT_emptyScal_zero (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) {ν μ : Fin N} (hν : ν ≠ μ) :
    emptyScal Sig A z (eI (Sum.inr ν)) μ 0 =
      Gmu Sig A z μ (Sum.inr ν) (Sum.inr ν) - PiZ N Sig z (Sum.inr ν) (Sum.inr ν) := by
  simp only [emptyScal, ite_true, claimT_vbar_inr, ent_eI_eI]
  simp [eI, hν.symm]

/-- The scalar of one bracket at `v = e_ν`: at most `K` when every entry of `G^{(μ)}` is. -/
private theorem claimT_brackScal_le (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (ν : Fin N) (i : Fin M) (μ : Fin N) {K : ℝ}
    (hK1 : 1 ≤ K) (hK : ∀ s t, ‖Gmu Sig A z μ s t‖ ≤ K) (x y : Letter) (s : Fin 3) :
    ‖brackScal Sig A z (eI (Sum.inr ν)) i μ x y s‖ ≤ K := by
  have hl : ∀ x : Letter, ∃ u, letVec Sig (eI (Sum.inr ν)) i μ x = eI u := by
    intro x
    cases x
    · exact ⟨Sum.inr ν, claimT_vbar_inr Sig ν⟩
    · exact ⟨Sum.inl i, rfl⟩
    · exact ⟨Sum.inr μ, rfl⟩
  obtain ⟨u, hu⟩ := hl x
  obtain ⟨u', hu'⟩ := hl y
  unfold brackScal
  split_ifs <;> first
    | (rw [hu, hu', ent_eI_eI]; exact hK u u')
    | (simp only [norm_one, norm_neg, norm_zero]; linarith)

/-- The scalar of the first bracket `[G_{v̄ y}]^0`, `y ≠ V`, at `v = e_ν`: `G^{(μ)}_{νi}` or `0`. -/
private theorem claimT_brackScal_V_left (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (ν : Fin N) (i : Fin M) (μ : Fin N) {b : ℝ}
    (hb0 : 0 ≤ b) (hb : ‖Gmu Sig A z μ (Sum.inr ν) (Sum.inl i)‖ ≤ b) (y : Letter) (hy : y ≠ .V) :
    ‖brackScal Sig A z (eI (Sum.inr ν)) i μ .V y 0‖ ≤ b := by
  cases y
  · exact absurd rfl hy
  · simp only [brackScal, ite_true, letVec, claimT_vbar_inr, ent_eI_eI]; exact hb
  · simp only [brackScal, ite_true, letVec, claimT_vbar_inr, ent_eI_eI, claimT_Gmu_col,
      norm_zero]
    exact hb0

/-- The scalar of the last bracket `[G_{x v̄}]^0`, `x ≠ V`, at `v = e_ν`: `G^{(μ)}_{iν}` or `0`. -/
private theorem claimT_brackScal_V_right (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (ν : Fin N) (i : Fin M) (μ : Fin N) {b : ℝ}
    (hb0 : 0 ≤ b) (hb : ‖Gmu Sig A z μ (Sum.inl i) (Sum.inr ν)‖ ≤ b) (x : Letter) (hx : x ≠ .V) :
    ‖brackScal Sig A z (eI (Sum.inr ν)) i μ x .V 0‖ ≤ b := by
  cases x
  · exact absurd rfl hx
  · simp only [brackScal, ite_true, letVec, claimT_vbar_inr, ent_eI_eI]; exact hb
  · simp only [brackScal, ite_true, letVec, claimT_vbar_inr, ent_eI_eI, claimT_Gmu_row,
      norm_zero]
    exact hb0

private theorem claimT_ofT_ne (b : Bool) : Letter.ofT b ≠ .V := by
  cases b <;> simp [Letter.ofT]

private theorem claimT_ofS_ne (b : Bool) : Letter.ofS b ≠ .V := by
  cases b <;> simp [Letter.ofS]

/-- `deg [G_{xy}]^1 ≥ 1` when one letter is `V`. -/
private theorem claimT_degTab_one (x y : Letter) (h : x = .V ∨ y = .V) : 1 ≤ degTab x y 1 := by
  rcases h with rfl | rfl
  · cases y <;> simp [degTab]
  · cases x <;> simp [degTab]

/-- (A+_avg_3) for the scalar factor: for `n(w) ≥ 1`, `ℤ₂` tags and `v = e_ν`,
`|A⁰(w, σ)| ≤ K^{n+1} b^{(2 − deg A(w, σ))_+}` when `|G^{(μ)}_{st}| ≤ K` and
`|G^{(μ)}_{νi}|, |G^{(μ)}_{iν}| ≤ b ≤ 1 ≤ K`. -/
private theorem claimT_tagScal_le (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (ν : Fin N) (i : Fin M) (μ : Fin N) {K b : ℝ}
    (hK1 : 1 ≤ K) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hK : ∀ s t, ‖Gmu Sig A z μ s t‖ ≤ K)
    (hbl : ‖Gmu Sig A z μ (Sum.inr ν) (Sum.inl i)‖ ≤ b)
    (hbr : ‖Gmu Sig A z μ (Sum.inl i) (Sum.inr ν)‖ ≤ b) (k : ℕ) (w : Word (k + 1))
    (σ : Fin (k + 2) → Fin 3) (hv : tagV σ = 0) :
    ‖tagScal Sig A z (eI (Sum.inr ν)) i μ (k + 1) w σ‖ ≤
      K ^ (k + 2) * b ^ (2 - tagDeg (k + 1) w σ) := by
  have h2 := claimT_ne_two hv
  have hK0 : 0 ≤ K := zero_le_one.trans hK1
  have hbK : b ≤ K := hb1.trans hK1
  set f : Fin (k + 2) → ℂ := fun l =>
    brackScal Sig A z (eI (Sum.inr ν)) i μ (factorX w l) (factorY w l) (σ l) with hf
  set g : Fin (k + 2) → ℕ := fun l => degTab (factorX w l) (factorY w l) (σ l) with hg
  have hx0 : factorX w 0 = .V := by simp [factorX]
  have hy0 : factorY w 0 = Letter.ofT (w 0) := by simp [factorY]
  have hxl : factorX w (Fin.last k).succ = Letter.ofS (w (Fin.last k)) := by
    simp [factorX]; try rfl
  have hyl : factorY w (Fin.last k).succ = .V := by simp [factorY]
  have hT : tagScal Sig A z (eI (Sum.inr ν)) i μ (k + 1) w σ =
      f 0 * ((∏ l : Fin k, f l.castSucc.succ) * f (Fin.last k).succ) := by
    simp only [tagScal]
    rw [Fin.prod_univ_succ, Fin.prod_univ_castSucc]
  have hD : g 0 + g (Fin.last k).succ ≤ tagDeg (k + 1) w σ := by
    simp only [tagDeg]
    change g 0 + g (Fin.last k).succ ≤ ∑ l, g l
    rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
    omega
  have hmid : ‖∏ l : Fin k, f l.castSucc.succ‖ ≤ K ^ k := by
    rw [norm_prod]
    calc ∏ l : Fin k, ‖f l.castSucc.succ‖ ≤ ∏ _l : Fin k, K :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun l _ =>
            claimT_brackScal_le Sig A z ν i μ hK1 hK _ _ _
      _ = K ^ k := by simp
  -- the two endpoint factors
  have he0 : ‖f 0‖ ≤ (if σ 0 = 0 then b else K) := by
    split_ifs with h
    · simp only [hf, h, hx0, hy0]
      exact claimT_brackScal_V_left Sig A z ν i μ hb0 hbl _ (claimT_ofT_ne _)
    · exact claimT_brackScal_le Sig A z ν i μ hK1 hK _ _ _
  have hel : ‖f (Fin.last k).succ‖ ≤ (if σ (Fin.last k).succ = 0 then b else K) := by
    split_ifs with h
    · simp only [hf, h, hxl, hyl]
      exact claimT_brackScal_V_right Sig A z ν i μ hb0 hbr _ (claimT_ofS_ne _)
    · exact claimT_brackScal_le Sig A z ν i μ hK1 hK _ _ _
  have hg0 : σ 0 ≠ 0 → 1 ≤ g 0 := fun h => by
    have : σ 0 = 1 := by
      have := h2 0
      revert h this; generalize σ 0 = t; intro h h'; fin_cases t <;> simp_all
    simp only [hg, this]
    exact claimT_degTab_one _ _ (Or.inl hx0)
  have hgl : σ (Fin.last k).succ ≠ 0 → 1 ≤ g (Fin.last k).succ := fun h => by
    have : σ (Fin.last k).succ = 1 := by
      have := h2 (Fin.last k).succ
      revert h this; generalize σ (Fin.last k).succ = t; intro h h'; fin_cases t <;> simp_all
    simp only [hg, this]
    exact claimT_degTab_one _ _ (Or.inr hyl)
  rw [hT, norm_mul, norm_mul]
  have hKk : 0 ≤ K ^ k := pow_nonneg hK0 k
  have hbpow : ∀ a c : ℕ, a ≤ c → b ^ c ≤ b ^ a := fun a c h => pow_le_pow_of_le_one hb0 hb1 h
  by_cases h0 : σ 0 = 0 <;> by_cases hl : σ (Fin.last k).succ = 0
  · simp only [h0, hl, ite_true] at he0 hel
    have : b ^ 2 ≤ b ^ (2 - tagDeg (k + 1) w σ) := hbpow _ _ (by omega)
    calc ‖f 0‖ * (‖∏ l : Fin k, f l.castSucc.succ‖ * ‖f (Fin.last k).succ‖)
        ≤ b * (K ^ k * b) := mul_le_mul he0 (mul_le_mul hmid hel (norm_nonneg _) hKk)
          (by positivity) hb0
      _ = K ^ k * b ^ 2 := by ring
      _ ≤ K ^ (k + 2) * b ^ (2 - tagDeg (k + 1) w σ) :=
          mul_le_mul (pow_le_pow_right₀ hK1 (by omega)) this (by positivity) (by positivity)
  · simp only [h0, hl, ite_true, ite_false] at he0 hel
    have h1 := hgl hl
    have : b ≤ b ^ (2 - tagDeg (k + 1) w σ) := by
      have := hbpow (2 - tagDeg (k + 1) w σ) 1 (by omega); simpa using this
    calc ‖f 0‖ * (‖∏ l : Fin k, f l.castSucc.succ‖ * ‖f (Fin.last k).succ‖)
        ≤ b * (K ^ k * K) := mul_le_mul he0 (mul_le_mul hmid hel (norm_nonneg _) hKk)
          (by positivity) hb0
      _ = K ^ (k + 1) * b := by ring
      _ ≤ K ^ (k + 2) * b ^ (2 - tagDeg (k + 1) w σ) :=
          mul_le_mul (pow_le_pow_right₀ hK1 (by omega)) this hb0 (by positivity)
  · simp only [h0, hl, ite_true, ite_false] at he0 hel
    have h1 := hg0 h0
    have : b ≤ b ^ (2 - tagDeg (k + 1) w σ) := by
      have := hbpow (2 - tagDeg (k + 1) w σ) 1 (by omega); simpa using this
    calc ‖f 0‖ * (‖∏ l : Fin k, f l.castSucc.succ‖ * ‖f (Fin.last k).succ‖)
        ≤ K * (K ^ k * b) := mul_le_mul he0 (mul_le_mul hmid hel (norm_nonneg _) hKk)
          (by positivity) hK0
      _ = K ^ (k + 1) * b := by ring
      _ ≤ K ^ (k + 2) * b ^ (2 - tagDeg (k + 1) w σ) :=
          mul_le_mul (pow_le_pow_right₀ hK1 (by omega)) this hb0 (by positivity)
  · simp only [h0, hl, ite_false] at he0 hel
    have h1 := hg0 h0
    have h1' := hgl hl
    have : 2 - tagDeg (k + 1) w σ = 0 := by omega
    rw [this, pow_zero, mul_one]
    calc ‖f 0‖ * (‖∏ l : Fin k, f l.castSucc.succ‖ * ‖f (Fin.last k).succ‖)
        ≤ K * (K ^ k * K) := mul_le_mul he0 (mul_le_mul hmid hel (norm_nonneg _) hKk)
          (by positivity) hK0
      _ = K ^ (k + 2) := by ring

/-- The letters `V`, `I` give unit vectors `e_s`, `s ≠ μ`, at `v = e_ν`, `ν ≠ μ`. -/
private theorem claimT_letVec (Sig : Matrix (Fin M) (Fin M) ℝ) {ν μ : Fin N} (hν : ν ≠ μ)
    (i : Fin M) (x : Letter) (hx : x ≠ .M) :
    ∃ s, s ≠ Sum.inr μ ∧ letVec Sig (eI (Sum.inr ν)) i μ x = eI s := by
  cases x
  · exact ⟨Sum.inr ν, fun h => hν (Sum.inr_injective h), claimT_vbar_inr Sig ν⟩
  · exact ⟨Sum.inl i, Sum.inl_ne_inr, rfl⟩
  · exact absurd rfl hx

/-- The coefficient vectors of `[G_{xy}]^s` are `colC(x)` with `x ≠ M` or `rowC(y)` with
`y ≠ M`. -/
private theorem claimT_brackForms_mem (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N)
    (x y : Letter) (s : Fin 3) (c : Fin M → ℂ) (hc : c ∈ brackForms Sig A z v i μ x y s) :
    (x ≠ .M ∧ c = colC Sig A z (letVec Sig v i μ x) μ) ∨
      (y ≠ .M ∧ c = rowC Sig A z (letVec Sig v i μ y) μ) := by
  fin_cases s <;> cases x <;> cases y <;> simp [brackForms] at hc ⊢ <;> tauto

/-- Every coefficient vector of `A⁺(w, σ)` at `v = e_ν`, `ν ≠ μ`, `ℤ₂` tags, is `colC(e_s)` or
`rowC(e_s)` with `s ≠ μ`. -/
private theorem claimT_tagForms_mem (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) {ν μ : Fin N} (hν : ν ≠ μ) (i : Fin M) (n : ℕ)
    (w : Word n) (σ : Fin (n + 1) → Fin 3) (hv : tagV σ = 0) (c : Fin M → ℂ)
    (hc : c ∈ tagForms Sig A z (eI (Sum.inr ν)) i μ n w σ) :
    ∃ s, s ≠ Sum.inr μ ∧ (c = colC Sig A z (eI s) μ ∨ c = rowC Sig A z (eI s) μ) := by
  cases n with
  | zero =>
    have h2 := claimT_ne_two hv 0
    simp only [tagForms, emptyForms] at hc
    split_ifs at hc with h0 h1
    · simp at hc
    · rw [claimT_vbar_inr] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      exact ⟨Sum.inr ν, fun h => hν (Sum.inr_injective h), hc⟩
    · exact absurd (by revert h0 h1 h2; generalize σ 0 = t; fin_cases t <;> simp) h2
  | succ k =>
    simp only [tagForms, List.mem_flatten, List.mem_ofFn] at hc
    obtain ⟨L, ⟨l, rfl⟩, hcL⟩ := hc
    rcases claimT_brackForms_mem Sig A z _ i μ _ _ _ c hcL with ⟨hx, rfl⟩ | ⟨hy, rfl⟩
    · obtain ⟨s, hs, he⟩ := claimT_letVec Sig hν i _ hx
      exact ⟨s, hs, Or.inl (by rw [he])⟩
    · obtain ⟨s, hs, he⟩ := claimT_letVec Sig hν i _ hy
      exact ⟨s, hs, Or.inr (by rw [he])⟩

/-- `|∏_{c ∈ L} ⟨c, y⟩| ≤ a^{|L|}` when every factor is at most `a`. -/
private theorem claimT_list_prod_le (L : List (Fin M → ℂ)) (y : Fin M → ℝ) {a : ℝ}
    (h : ∀ c ∈ L, ‖linForm c y‖ ≤ a) :
    ‖(L.map fun c => linForm c y).prod‖ ≤ a ^ L.length := by
  induction L with
  | nil => simp
  | cons c L ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, norm_mul]
    have hc := h c (by simp)
    have ha : 0 ≤ a := (norm_nonneg _).trans hc
    rw [pow_succ, mul_comm (a ^ L.length)]
    exact mul_le_mul hc (ih fun c' hc' => h c' (by simp [hc'])) (norm_nonneg _) ha

/-- `Π_{sμ} = Π_{μs} = 0` for `s ≠ μ`. -/
private theorem claimT_Pi_off (Sig : Matrix (Fin M) (Fin M) ℝ) (z : ℂ) (μ : Fin N)
    (s : Fin M ⊕ Fin N) (hs : s ≠ Sum.inr μ) :
    PiZ N Sig z s (Sum.inr μ) = 0 ∧ PiZ N Sig z (Sum.inr μ) s = 0 := by
  rcases s with j | ν
  · simp [PiZ, piMat]
  · have hν : ν ≠ μ := fun h => hs (by rw [h])
    simp [PiZ, piMat, hν, Ne.symm hν]

/-- On the a priori event: `|(G^{(μ)}X)_{sμ}|, |(X^*G^{(μ)})_{μs}| ≤ L b` for `s ≠ μ`. -/
private theorem claimT_form_event {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (μ : Fin N) {b L : ℝ}
    (hG : ∀ s t, ‖G Sig A z s t - PiZ N Sig z s t‖ ≤ b)
    (hμ : 1 ≤ L * ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖) (s : Fin M ⊕ Fin N) (hs : s ≠ Sum.inr μ) :
    ‖linForm (colC Sig A z (eI s) μ) (fun j => A j μ)‖ ≤ L * b ∧
      ‖linForm (rowC Sig A z (eI s) μ) (fun j => A j μ)‖ ≤ L * b := by
  obtain ⟨h1, h2⟩ := claimT_Pi_off Sig z μ s hs
  have hc := hG s (Sum.inr μ)
  have hr := hG (Sum.inr μ) s
  rw [h1, sub_zero, claimT_G_col hSig A hz μ s hs, norm_mul, norm_neg] at hc
  rw [h2, sub_zero, claimT_G_row hSig A hz μ s hs, norm_mul, norm_neg] at hr
  have hL : 0 ≤ L := by
    by_contra h
    have h' := lt_of_not_ge h
    nlinarith [norm_nonneg (G Sig A z (Sum.inr μ) (Sum.inr μ))]
  constructor
  · calc ‖linForm (colC Sig A z (eI s) μ) (fun j => A j μ)‖
        ≤ L * ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖ *
            ‖linForm (colC Sig A z (eI s) μ) (fun j => A j μ)‖ :=
          le_mul_of_one_le_left (norm_nonneg _) hμ
      _ ≤ L * b := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hc hL
  · calc ‖linForm (rowC Sig A z (eI s) μ) (fun j => A j μ)‖
        ≤ L * ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖ *
            ‖linForm (rowC Sig A z (eI s) μ) (fun j => A j μ)‖ :=
          le_mul_of_one_le_left (norm_nonneg _) hμ
      _ ≤ L * b := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hr hL

/-- On the a priori event: the column part `A⁺(w, σ)` at `v = e_ν`, `ν ≠ μ`, is at most
`(L b)^{deg A(w, σ)}`. -/
private theorem claimT_tagForms_event {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) {ν μ : Fin N} (hν : ν ≠ μ)
    (i : Fin M) {b L : ℝ} (hG : ∀ s t, ‖G Sig A z s t - PiZ N Sig z s t‖ ≤ b)
    (hμ : 1 ≤ L * ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖) (n : ℕ) (w : Word n)
    (σ : Fin (n + 1) → Fin 3) (hv : tagV σ = 0) :
    ‖((tagForms Sig A z (eI (Sum.inr ν)) i μ n w σ).map
        fun c => linForm c fun j => A j μ).prod‖ ≤ (L * b) ^ tagDeg n w σ := by
  rw [← tagForms_length Sig A z (eI (Sum.inr ν)) i μ]
  refine claimT_list_prod_le _ _ fun c hc => ?_
  obtain ⟨s, hs, hc'⟩ := claimT_tagForms_mem Sig A z hν i n w σ hv c hc
  have := claimT_form_event hSig A hz μ hG hμ s hs
  rcases hc' with rfl | rfl
  · exact this.1
  · exact this.2

/-! ## The a priori event and its `X^{(μ)}`-measurable part -/

/-- `Â⁰ = N⁻¹ ∑_{ν ≠ μ} (G^{(μ)}_{νν} − Π_{νν})`: the averaged empty word with tag `0`. -/
private def claimT_Shat (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (μ : Fin N) : ℂ :=
  (N : ℂ)⁻¹ * ∑ ν ∈ Finset.univ.erase μ, emptyScal Sig A z (eI (Sum.inr ν)) μ 0

/-- (A+_avg_2) on the a priori event: `|Â⁰| ≤ F̃ + N⁻¹ b + L b²`. -/
private theorem claimT_Shat_event {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (μ : Fin N) {b L : ℝ}
    (hG : ∀ s t, ‖G Sig A z s t - PiZ N Sig z s t‖ ≤ b)
    (hμ : 1 ≤ L * ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖) :
    ‖claimT_Shat Sig A z μ‖ ≤ Ft Sig A z + (N : ℝ)⁻¹ * b + L * b ^ 2 := by
  have hN : 0 < N := Fin.pos μ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  set g := G Sig A z (Sum.inr μ) (Sum.inr μ) with hg
  set m := mFun N (specOf Sig) z with hm
  have hg0 : g ≠ 0 := G_diag_ne_zero hSig A hz _
  have hgn : 0 < ‖g‖ := norm_pos_iff.2 hg0
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hG (Sum.inr μ) (Sum.inr μ))
  have hL : 0 ≤ L := by
    by_contra h
    have h' := lt_of_not_ge h
    nlinarith
  have hPi : ∀ ν : Fin N, PiZ N Sig z (Sum.inr ν) (Sum.inr ν) = m := fun ν => by
    simp [PiZ, piMat, hm]
  have hterm : ∀ ν ∈ Finset.univ.erase μ, emptyScal Sig A z (eI (Sum.inr ν)) μ 0 =
      (G Sig A z (Sum.inr ν) (Sum.inr ν) - m) -
        G Sig A z (Sum.inr ν) (Sum.inr μ) * G Sig A z (Sum.inr μ) (Sum.inr ν) / g := by
    intro ν hν
    have hν' : ν ≠ μ := Finset.ne_of_mem_erase hν
    have hne : (Sum.inr ν : Fin M ⊕ Fin N) ≠ Sum.inr μ := fun h => hν' (Sum.inr_injective h)
    rw [claimT_emptyScal_zero Sig A z hν', hPi, Gmu, Gstu hSig A hz _ _ _ hne hne]
    ring
  have hsplit : ∑ ν ∈ Finset.univ.erase μ, (G Sig A z (Sum.inr ν) (Sum.inr ν) - m) =
      (∑ ν, (G Sig A z (Sum.inr ν) (Sum.inr ν) - m)) - (g - m) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ μ)]
    ring
  have hmN : (N : ℂ)⁻¹ * ∑ ν, (G Sig A z (Sum.inr ν) (Sum.inr ν) - m) =
      mN Sig A z - m := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_sub, ← mul_assoc, inv_mul_cancel₀ hN0, one_mul]
    rfl
  have hcorr : ‖∑ ν ∈ Finset.univ.erase μ,
      G Sig A z (Sum.inr ν) (Sum.inr μ) * G Sig A z (Sum.inr μ) (Sum.inr ν) / g‖ ≤
        (N : ℝ) * (L * b ^ 2) := by
    calc _ ≤ ∑ ν ∈ Finset.univ.erase μ, L * b ^ 2 := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ν hν => ?_)
          have hν' : ν ≠ μ := Finset.ne_of_mem_erase hν
          have hne : (Sum.inr ν : Fin M ⊕ Fin N) ≠ Sum.inr μ := fun h => hν' (Sum.inr_injective h)
          obtain ⟨h1, h2⟩ := claimT_Pi_off Sig z μ _ hne
          have hc := hG (Sum.inr ν) (Sum.inr μ)
          have hr := hG (Sum.inr μ) (Sum.inr ν)
          rw [h1, sub_zero] at hc
          rw [h2, sub_zero] at hr
          rw [norm_div, norm_mul, div_le_iff₀ hgn]
          have hp := mul_le_mul hc hr (norm_nonneg _) hb0
          nlinarith [mul_nonneg hL (sq_nonneg b)]
      _ ≤ ∑ _ν : Fin N, L * b ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            fun _ _ _ => by positivity
      _ = (N : ℝ) * (L * b ^ 2) := by simp
  have he : claimT_Shat Sig A z μ = (mN Sig A z - m) - (N : ℂ)⁻¹ * (g - m) -
      (N : ℂ)⁻¹ * ∑ ν ∈ Finset.univ.erase μ,
        G Sig A z (Sum.inr ν) (Sum.inr μ) * G Sig A z (Sum.inr μ) (Sum.inr ν) / g := by
    unfold claimT_Shat
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, hsplit, ← hmN]
    ring
  have hgm : ‖g - m‖ ≤ b := by
    have := hG (Sum.inr μ) (Sum.inr μ); rwa [hPi] at this
  rw [he]
  calc ‖(mN Sig A z - m) - (N : ℂ)⁻¹ * (g - m) - (N : ℂ)⁻¹ * ∑ ν ∈ Finset.univ.erase μ,
        G Sig A z (Sum.inr ν) (Sum.inr μ) * G Sig A z (Sum.inr μ) (Sum.inr ν) / g‖
      ≤ ‖mN Sig A z - m‖ + ‖(N : ℂ)⁻¹ * (g - m)‖ + ‖(N : ℂ)⁻¹ * ∑ ν ∈ Finset.univ.erase μ,
        G Sig A z (Sum.inr ν) (Sum.inr μ) * G Sig A z (Sum.inr μ) (Sum.inr ν) / g‖ :=
        norm_sub_le_of_le (norm_sub_le _ _) le_rfl
    _ ≤ Ft Sig A z + (N : ℝ)⁻¹ * b + (N : ℝ)⁻¹ * ((N : ℝ) * (L * b ^ 2)) := by
        rw [norm_mul, norm_mul, norm_inv, Complex.norm_natCast]
        refine add_le_add (add_le_add le_rfl ?_) ?_
        · exact mul_le_mul_of_nonneg_left hgm (by positivity)
        · exact mul_le_mul_of_nonneg_left hcorr (by positivity)
    _ = Ft Sig A z + (N : ℝ)⁻¹ * b + L * b ^ 2 := by field_simp

/-- The `X^{(μ)}`-measurable event of §9: `|G^{(μ)}_{st} − Π_{st}| ≤ β` for `s, t ≠ μ`. -/
private def claimT_Good (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (μ : Fin N) (β : ℝ) : Prop :=
  ∀ s t, s ≠ Sum.inr μ → t ≠ Sum.inr μ → ‖Gmu Sig A z μ s t - PiZ N Sig z s t‖ ≤ β

private theorem claimT_Good_updCol (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (μ : Fin N) (β : ℝ) (y : Fin M → ℝ) :
    claimT_Good Sig (updCol A μ y) z μ β ↔ claimT_Good Sig A z μ β := by
  unfold claimT_Good
  rw [Gmu_updCol]

/-- The a priori event implies the `X^{(μ)}`-measurable event at `β = (1 + L) b`. -/
private theorem claimT_Good_of_event {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (μ : Fin N) {b L : ℝ} (hb1 : b ≤ 1)
    (hL : 0 ≤ L) (hG : ∀ s t, ‖G Sig A z s t - PiZ N Sig z s t‖ ≤ b)
    (hμ : 1 ≤ L * ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖) :
    claimT_Good Sig A z μ ((1 + L) * b) := by
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hG (Sum.inr μ) (Sum.inr μ))
  exact minor_entry_bound hSig A hz μ hb0 hb1 hL hG hμ

/-- On the `X^{(μ)}`-measurable event: `|Â⁰| ≤ β`. -/
private theorem claimT_Shat_good {Sig : Matrix (Fin M) (Fin M) ℝ}
    {A : Matrix (Fin M) (Fin N) ℝ} {z : ℂ} {μ : Fin N} {β : ℝ}
    (hGood : claimT_Good Sig A z μ β) (hβ : 0 ≤ β) : ‖claimT_Shat Sig A z μ‖ ≤ β := by
  have hN : 0 < N := Fin.pos μ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  unfold claimT_Shat
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (N : ℝ)⁻¹ * ‖∑ ν ∈ Finset.univ.erase μ, emptyScal Sig A z (eI (Sum.inr ν)) μ 0‖
      ≤ (N : ℝ)⁻¹ * ∑ _ν : Fin N, β := by
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (by positivity)
        refine (Finset.sum_le_sum fun ν hν => ?_).trans
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            fun _ _ _ => hβ)
        have hν' : ν ≠ μ := Finset.ne_of_mem_erase hν
        have hne : (Sum.inr ν : Fin M ⊕ Fin N) ≠ Sum.inr μ := fun h => hν' (Sum.inr_injective h)
        rw [claimT_emptyScal_zero Sig A z hν']
        exact hGood _ _ hne hne
    _ = β := by simp; field_simp

/-- The entries of `G^{(μ)}` on the `X^{(μ)}`-measurable event. -/
private theorem claimT_good_entries {Sig : Matrix (Fin M) (Fin M) ℝ}
    {A : Matrix (Fin M) (Fin N) ℝ} {z : ℂ} {μ : Fin N} {β KP : ℝ}
    (hGood : claimT_Good Sig A z μ β) (hβ : 0 ≤ β) (hPi : ∀ s t, ‖PiZ N Sig z s t‖ ≤ KP) :
    (∀ s t, ‖Gmu Sig A z μ s t‖ ≤ KP + β) ∧
    (∀ ν, ν ≠ μ → ∀ j, ‖Gmu Sig A z μ (Sum.inr ν) (Sum.inl j)‖ ≤ β ∧
      ‖Gmu Sig A z μ (Sum.inl j) (Sum.inr ν)‖ ≤ β) := by
  have hKP : 0 ≤ KP := (norm_nonneg _).trans (hPi (Sum.inr μ) (Sum.inr μ))
  refine ⟨fun s t => ?_, fun ν hν j => ?_⟩
  · by_cases hs : s = Sum.inr μ
    · rw [hs, claimT_Gmu_row]; simp only [norm_zero]; linarith
    by_cases ht : t = Sum.inr μ
    · rw [ht, claimT_Gmu_col]; simp only [norm_zero]; linarith
    have h1 := hGood s t hs ht
    have h2 := norm_add_le (Gmu Sig A z μ s t - PiZ N Sig z s t) (PiZ N Sig z s t)
    rw [sub_add_cancel] at h2
    linarith [hPi s t]
  · have hne : (Sum.inr ν : Fin M ⊕ Fin N) ≠ Sum.inr μ := fun h => hν (Sum.inr_injective h)
    have h1 := hGood _ _ hne (Sum.inl_ne_inr (a := j) (b := μ))
    have h2 := hGood _ _ (Sum.inl_ne_inr (a := j) (b := μ)) hne
    have e1 : PiZ N Sig z (Sum.inr ν) (Sum.inl j) = 0 := by simp [PiZ, piMat]
    have e2 : PiZ N Sig z (Sum.inl j) (Sum.inr ν) = 0 := by simp [PiZ, piMat]
    rw [e1, sub_zero] at h1
    rw [e2, sub_zero] at h2
    exact ⟨h1, h2⟩

/-- `|x|² ≤ 2|x − p|² + 2|p|²`. -/
private theorem claimT_sq_le (x p : ℂ) : ‖x‖ ^ 2 ≤ 2 * ‖x - p‖ ^ 2 + 2 * ‖p‖ ^ 2 := by
  have h := norm_add_le (x - p) p
  rw [sub_add_cancel] at h
  have h0 := norm_nonneg (x - p)
  have h1 := norm_nonneg p
  have h2 := pow_le_pow_left₀ (norm_nonneg x) h 2
  nlinarith [sq_nonneg (‖x - p‖ - ‖p‖)]

/-- The row sums of `G^{(μ)}` on the `X^{(μ)}`-measurable event, in the form of (A+_avg):
`∑_j |G^{(μ)}_{ij}|^a ≤ N b^a` (`a = 1, 2`, both orders) when `2τ⁻¹β ≤ b` and
`4τ⁻¹ D² ≤ N b²`, `D² ≥ ∑_j |Π_{ij}|²`. -/
private theorem claimT_good_sums {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    {Sig : Matrix (Fin M) (Fin M) ℝ} {A : Matrix (Fin M) (Fin N) ℝ} {z : ℂ} {μ : Fin N}
    {β D b : ℝ} (hGood : claimT_Good Sig A z μ β) (hβ : 0 ≤ β) (hb : 2 * τ⁻¹ * β ≤ b)
    (hM : (M : ℝ) ≤ τ⁻¹ * N) (hDb : 4 * τ⁻¹ * D ^ 2 ≤ N * b ^ 2)
    (hrow : ∀ j, ∑ l, ‖PiZ N Sig z (Sum.inl j) (Sum.inl l)‖ ^ 2 ≤ D ^ 2)
    (hcol : ∀ j, ∑ l, ‖PiZ N Sig z (Sum.inl l) (Sum.inl j)‖ ^ 2 ≤ D ^ 2) (i : Fin M) :
    (∑ j, ‖Gmu Sig A z μ (Sum.inl i) (Sum.inl j)‖ ≤ N * b) ∧
    (∑ j, ‖Gmu Sig A z μ (Sum.inl j) (Sum.inl i)‖ ≤ N * b) ∧
    (∑ j, ‖Gmu Sig A z μ (Sum.inl i) (Sum.inl j)‖ ^ 2 ≤ N * b ^ 2) ∧
    (∑ j, ‖Gmu Sig A z μ (Sum.inl j) (Sum.inl i)‖ ^ 2 ≤ N * b ^ 2) := by
  have hτi : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  have hb0 : 0 ≤ b := le_trans (by positivity) hb
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hb2 : 4 * τ⁻¹ * β ^ 2 ≤ b ^ 2 := by
    have h1 : (2 * τ⁻¹ * β) ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ (by positivity) hb 2
    have h2 : 4 * τ⁻¹ * β ^ 2 ≤ (2 * τ⁻¹ * β) ^ 2 := by
      have : τ⁻¹ ≤ τ⁻¹ ^ 2 := by nlinarith
      nlinarith [sq_nonneg β]
    linarith
  -- a generic row: `∑ |x_j|² ≤ 2 D² + 2 M β²`
  have key : ∀ x p : Fin M → ℂ, (∀ j, ‖x j - p j‖ ≤ β) → ∑ j, ‖p j‖ ^ 2 ≤ D ^ 2 →
      (∑ j, ‖x j‖ ≤ N * b) ∧ ∑ j, ‖x j‖ ^ 2 ≤ N * b ^ 2 := by
    intro x p hx hp
    have hs2 : ∑ j, ‖x j‖ ^ 2 ≤ 2 * D ^ 2 + 2 * M * β ^ 2 := by
      calc ∑ j, ‖x j‖ ^ 2 ≤ ∑ j, (2 * β ^ 2 + 2 * ‖p j‖ ^ 2) := by
            refine Finset.sum_le_sum fun j _ => (claimT_sq_le (x j) (p j)).trans ?_
            have := pow_le_pow_left₀ (norm_nonneg _) (hx j) 2
            linarith
        _ = 2 * M * β ^ 2 + 2 * ∑ j, ‖p j‖ ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul, Finset.mul_sum]; ring
        _ ≤ 2 * D ^ 2 + 2 * M * β ^ 2 := by linarith
    have hD2 : 4 * D ^ 2 ≤ N * b ^ 2 := le_trans (by nlinarith [sq_nonneg D]) hDb
    have hMβ : 2 * M * β ^ 2 ≤ N * b ^ 2 / 2 := by
      have := mul_le_mul_of_nonneg_left hb2 hN0
      have h3 : 2 * (M : ℝ) * β ^ 2 ≤ 2 * (τ⁻¹ * N) * β ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
      nlinarith
    have hsq : ∑ j, ‖x j‖ ^ 2 ≤ N * b ^ 2 := by linarith
    refine ⟨?_, hsq⟩
    have hcs : (∑ j, ‖x j‖) ^ 2 ≤ (M : ℝ) * ∑ j, ‖x j‖ ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin M)))
        (f := fun j => ‖x j‖)
      simpa using this
    have h4 : (M : ℝ) * ∑ j, ‖x j‖ ^ 2 ≤ (N * b) ^ 2 := by
      have h5 : (M : ℝ) * ∑ j, ‖x j‖ ^ 2 ≤ (τ⁻¹ * N) * (2 * D ^ 2 + 2 * M * β ^ 2) :=
        mul_le_mul hM hs2 (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
      have h6 : (τ⁻¹ * N) * (2 * M * β ^ 2) ≤ (τ⁻¹ * N) * (2 * (τ⁻¹ * N) * β ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))
          (by positivity)
      have h7 : (τ⁻¹ * N) * (2 * D ^ 2) ≤ N * (N * b ^ 2) / 2 := by
        have := mul_le_mul_of_nonneg_left hDb hN0
        nlinarith
      have h8 : (τ⁻¹ * N) * (2 * (τ⁻¹ * N) * β ^ 2) ≤ N * (N * b ^ 2) / 2 := by
        have h9 : 2 * τ⁻¹ ^ 2 * β ^ 2 ≤ b ^ 2 / 2 := by
          have : (2 * τ⁻¹ * β) ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ (by positivity) hb 2
          nlinarith
        have := mul_le_mul_of_nonneg_left h9 (mul_nonneg hN0 hN0)
        nlinarith
      nlinarith
    exact (abs_le_of_sq_le_sq' (hcs.trans h4) (by positivity)).2
  have hrowx : ∀ j, ‖Gmu Sig A z μ (Sum.inl i) (Sum.inl j) - PiZ N Sig z (Sum.inl i) (Sum.inl j)‖
      ≤ β := fun j => hGood _ _ Sum.inl_ne_inr Sum.inl_ne_inr
  have hcolx : ∀ j, ‖Gmu Sig A z μ (Sum.inl j) (Sum.inl i) - PiZ N Sig z (Sum.inl j) (Sum.inl i)‖
      ≤ β := fun j => hGood _ _ Sum.inl_ne_inr Sum.inl_ne_inr
  obtain ⟨r1, r2⟩ := key _ _ hrowx (hrow i)
  obtain ⟨c1, c2⟩ := key _ _ hcolx (hcol i)
  exact ⟨r1, c1, r2, c2⟩

/-- `Y_μ = −z − m⁻¹ + O(τ⁻¹ β)` on the `X^{(μ)}`-measurable event (m_sc_eq). -/
private theorem claimT_good_Y {τ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    {A : Matrix (Fin M) (Fin N) ℝ} {z : ℂ} {μ : Fin N} {β : ℝ}
    (hGood : claimT_Good Sig A z μ β) (hβ : 0 ≤ β) (hM : (M : ℝ) ≤ τ⁻¹ * N)
    (htr : (N : ℂ)⁻¹ * ∑ j, PiZ N Sig z (Sum.inl j) (Sum.inl j) =
      -z - (mFun N (specOf Sig) z)⁻¹) :
    ‖Ymu Sig A z μ - (-z - (mFun N (specOf Sig) z)⁻¹)‖ ≤ τ⁻¹ * β := by
  have hN : 0 < N := Fin.pos μ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← htr, Ymu, ← mul_sub, ← Finset.sum_sub_distrib, norm_mul, norm_inv, Complex.norm_natCast]
  calc (N : ℝ)⁻¹ * ‖∑ j, (Gmu Sig A z μ (Sum.inl j) (Sum.inl j) -
        PiZ N Sig z (Sum.inl j) (Sum.inl j))‖ ≤ (N : ℝ)⁻¹ * (M * β) := by
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (by positivity)
        calc _ ≤ ∑ _j : Fin M, β :=
              Finset.sum_le_sum fun j _ => hGood _ _ Sum.inl_ne_inr Sum.inl_ne_inr
          _ = M * β := by simp
    _ ≤ (N : ℝ)⁻¹ * (τ⁻¹ * N * β) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hM hβ) (by positivity)
    _ = τ⁻¹ * β := by field_simp

/-- `|calY z Y K k| ≤ (K + 1)(a + 1)^{K+1} 2^K (B + 1)^K` for `|(−z − Y)⁻¹| ≤ a`, `|Y| ≤ B`. -/
private theorem claimT_calY_le {z Y : ℂ} {a B : ℝ} (ha : ‖(-z - Y)⁻¹‖ ≤ a) (hB : ‖Y‖ ≤ B)
    (K k : ℕ) :
    ‖calY z Y K k‖ ≤ (K + 1) * (a + 1) ^ (K + 1) * 2 ^ K * (B + 1) ^ K := by
  have ha0 : 0 ≤ a := (norm_nonneg _).trans ha
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hB
  unfold calY
  calc ‖∑ t ∈ Finset.Icc k K, (-z - Y)⁻¹ ^ (t + 1) * (t.choose k : ℂ) * (-Y) ^ (t - k)‖
      ≤ ∑ t ∈ Finset.Icc k K, (a + 1) ^ (K + 1) * 2 ^ K * (B + 1) ^ K := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t ht => ?_)
        obtain ⟨_, htK⟩ := Finset.mem_Icc.1 ht
        rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_neg, Complex.norm_natCast]
        have h1 : ‖(-z - Y)⁻¹‖ ^ (t + 1) ≤ (a + 1) ^ (K + 1) :=
          (pow_le_pow_left₀ (norm_nonneg _) (ha.trans (by linarith)) _).trans
            (pow_le_pow_right₀ (by linarith) (by omega))
        have h2 : ((t.choose k : ℕ) : ℝ) ≤ 2 ^ K := by
          have := Nat.choose_le_two_pow t k
          have h3 : (2 : ℕ) ^ t ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) htK
          exact_mod_cast this.trans h3
        have h3 : ‖Y‖ ^ (t - k) ≤ (B + 1) ^ K :=
          (pow_le_pow_left₀ (norm_nonneg _) (hB.trans (by linarith)) _).trans
            (pow_le_pow_right₀ (by linarith) (by omega))
        exact mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity)) h3 (by positivity)
          (by positivity)
    _ ≤ ∑ _t ∈ Finset.range (K + 1), (a + 1) ^ (K + 1) * 2 ^ K * (B + 1) ^ K := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
        intro t ht
        simp only [Finset.mem_Icc, Finset.mem_range] at ht ⊢
        omega
    _ = (K + 1) * (a + 1) ^ (K + 1) * 2 ^ K * (B + 1) ^ K := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

/-! ## Polynomials in the column have all moments -/

section Mom

variable {ρ : Fin M → Measure ℝ} [∀ j, IsProbabilityMeasure (ρ j)]

/-- `f` is continuous and `|f|^n` is integrable for the column law, for every `n`. -/
private def claimT_Mom (ρ : Fin M → Measure ℝ) (f : (Fin M → ℝ) → ℂ) : Prop :=
  Continuous f ∧ ∀ n : ℕ, Integrable (fun y => ‖f y‖ ^ n) (Measure.pi ρ)

omit [∀ j, IsProbabilityMeasure (ρ j)] in
private theorem claimT_Mom.integrable {f : (Fin M → ℝ) → ℂ} (h : claimT_Mom ρ f) :
    Integrable f (Measure.pi ρ) :=
  (h.2 1).mono' h.1.aestronglyMeasurable (ae_of_all _ fun y => by simp)

private theorem claimT_Mom_const (c : ℂ) : claimT_Mom ρ fun _ => c :=
  ⟨continuous_const, fun _ => integrable_const _⟩

private theorem claimT_Mom_coord (hρ : ∀ j (n : ℕ), Integrable (fun y => |y| ^ n) (ρ j))
    (j : Fin M) : claimT_Mom ρ fun y => ((y j : ℝ) : ℂ) := by
  refine ⟨Complex.continuous_ofReal.comp (continuous_apply j), fun n => ?_⟩
  have h := (measurePreserving_eval ρ j).integrable_comp_of_integrable (hρ j n)
  refine h.congr (ae_of_all _ fun y => ?_)
  simp [Function.comp, Complex.norm_real]

omit [∀ j, IsProbabilityMeasure (ρ j)] in
private theorem claimT_Mom_mul {f g : (Fin M → ℝ) → ℂ} (hf : claimT_Mom ρ f)
    (hg : claimT_Mom ρ g) : claimT_Mom ρ fun y => f y * g y := by
  refine ⟨hf.1.mul hg.1, fun n => ?_⟩
  refine ((hf.2 (2 * n)).add (hg.2 (2 * n))).mono'
    ((hf.1.mul hg.1).norm.pow n).aestronglyMeasurable (ae_of_all _ fun y => ?_)
  rw [norm_mul, mul_pow, Real.norm_of_nonneg (by positivity)]
  have hu := pow_nonneg (norm_nonneg (f y)) n
  have hv := pow_nonneg (norm_nonneg (g y)) n
  have e1 : ‖f y‖ ^ (2 * n) = (‖f y‖ ^ n) ^ 2 := by rw [← pow_mul, mul_comm]
  have e2 : ‖g y‖ ^ (2 * n) = (‖g y‖ ^ n) ^ 2 := by rw [← pow_mul, mul_comm]
  simp only [Pi.add_apply, e1, e2]
  nlinarith [sq_nonneg (‖f y‖ ^ n - ‖g y‖ ^ n)]

private theorem claimT_pow_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (n : ℕ) :
    (x + y) ^ n ≤ 2 ^ n * (x ^ n + y ^ n) := by
  have h2 : (0 : ℝ) ≤ 2 ^ n := by positivity
  have hxn := pow_nonneg hx n
  have hyn := pow_nonneg hy n
  rcases le_total x y with h | h
  · calc (x + y) ^ n ≤ (2 * y) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
      _ = 2 ^ n * y ^ n := mul_pow _ _ _
      _ ≤ 2 ^ n * (x ^ n + y ^ n) := mul_le_mul_of_nonneg_left (by linarith) h2
  · calc (x + y) ^ n ≤ (2 * x) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
      _ = 2 ^ n * x ^ n := mul_pow _ _ _
      _ ≤ 2 ^ n * (x ^ n + y ^ n) := mul_le_mul_of_nonneg_left (by linarith) h2

omit [∀ j, IsProbabilityMeasure (ρ j)] in
private theorem claimT_Mom_add {f g : (Fin M → ℝ) → ℂ} (hf : claimT_Mom ρ f)
    (hg : claimT_Mom ρ g) : claimT_Mom ρ fun y => f y + g y := by
  refine ⟨hf.1.add hg.1, fun n => ?_⟩
  refine (((hf.2 n).add (hg.2 n)).const_mul (2 ^ n)).mono'
    ((hf.1.add hg.1).norm.pow n).aestronglyMeasurable (ae_of_all _ fun y => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) n).trans
    (claimT_pow_add_le (norm_nonneg _) (norm_nonneg _) n)

private theorem claimT_Mom_sum {ι : Type*} (s : Finset ι) {f : ι → (Fin M → ℝ) → ℂ}
    (hf : ∀ a ∈ s, claimT_Mom ρ (f a)) : claimT_Mom ρ fun y => ∑ a ∈ s, f a y := by
  induction s using Finset.induction_on with
  | empty => simpa using claimT_Mom_const (ρ := ρ) 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact claimT_Mom_add (hf a (by simp)) (ih fun b hb => hf b (by simp [hb]))

private theorem claimT_Mom_prod {ι : Type*} (s : Finset ι) {f : ι → (Fin M → ℝ) → ℂ}
    (hf : ∀ a ∈ s, claimT_Mom ρ (f a)) : claimT_Mom ρ fun y => ∏ a ∈ s, f a y := by
  induction s using Finset.induction_on with
  | empty => simpa using claimT_Mom_const (ρ := ρ) 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact claimT_Mom_mul (hf a (by simp)) (ih fun b hb => hf b (by simp [hb]))

omit [∀ j, IsProbabilityMeasure (ρ j)] in
private theorem claimT_Mom_conjIf (c : Bool) {f : (Fin M → ℝ) → ℂ} (hf : claimT_Mom ρ f) :
    claimT_Mom ρ fun y => conjIf c (f y) := by
  cases c
  · simpa [conjIf] using hf
  · refine ⟨Complex.continuous_conj.comp hf.1, fun n => ?_⟩
    simpa [conjIf, Complex.norm_conj] using hf.2 n

private theorem claimT_Mom_linForm (hρ : ∀ j (n : ℕ), Integrable (fun y => |y| ^ n) (ρ j))
    (c : Fin M → ℂ) : claimT_Mom ρ fun y => linForm c y :=
  claimT_Mom_sum _ fun j _ => claimT_Mom_mul (claimT_Mom_const _) (claimT_Mom_coord hρ j)

private theorem claimT_Mom_listProd (hρ : ∀ j (n : ℕ), Integrable (fun y => |y| ^ n) (ρ j))
    (L : List (Fin M → ℂ)) : claimT_Mom ρ fun y => (L.map fun c => linForm c y).prod := by
  induction L with
  | nil => simpa using claimT_Mom_const (ρ := ρ) 1
  | cons c L ih =>
    simp only [List.map_cons, List.prod_cons]
    exact claimT_Mom_mul (claimT_Mom_linForm hρ c) ih

private theorem claimT_Mom_Qmu (hρ : ∀ j (n : ℕ), Integrable (fun y => |y| ^ n) (ρ j))
    (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (μ : Fin N) :
    claimT_Mom ρ fun y => Qmu Sig (updCol A μ y) z μ := by
  simp only [Qmu_updCol]
  exact claimT_Mom_sum _ fun j _ => claimT_Mom_sum _ fun j' _ =>
    claimT_Mom_mul (claimT_Mom_mul (claimT_Mom_coord hρ j) (claimT_Mom_const _))
      (claimT_Mom_coord hρ j')

end Mom

/-! ## The column expectation of the expanded product (A+_avg) -/

/-- `∏_r (x or x̄)^{t_r} = x^{d₀} x̄^{d₁}`. -/
private theorem claimT_Gam_eq {p : ℕ} (cs : Fin p → Bool) (t : Fin p → ℕ) (x : ℂ) :
    ∏ r, conjIf (cs r) x ^ t r =
      x ^ (∑ r, if cs r then 0 else t r) * starRingEnd ℂ x ^ (∑ r, if cs r then t r else 0) := by
  have h : ∀ r, conjIf (cs r) x ^ t r =
      x ^ (if cs r then 0 else t r) * starRingEnd ℂ x ^ (if cs r then t r else 0) := by
    intro r; cases cs r <;> simp [conjIf]
  simp only [h, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

/-- `(∑_{k ≤ K} c_k Q^k)^d = ∑_κ ∏_l c_{κ_l} Q^{|κ|}`. -/
private theorem claimT_pow_sum (c : ℕ → ℂ) (Q : ℂ) (K d : ℕ) :
    (∑ k ∈ Finset.range (K + 1), c k * Q ^ k) ^ d =
      ∑ κ ∈ Fintype.piFinset (fun _ : Fin d => Finset.range (K + 1)),
        (∏ l, c (κ l)) * Q ^ (∑ l, κ l) := by
  rw [← Fin.prod_const, Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

/-- `Q^a Q̄^b = ∏_{t < a + b} (Q or Q̄)`. -/
private theorem claimT_QQ (Q : ℂ) (a b : ℕ) :
    Q ^ a * starRingEnd ℂ Q ^ b = ∏ t : Fin (a + b), conjIf (decide (a ≤ t.val)) Q := by
  rw [Fin.prod_univ_add]
  have h1 : ∀ t : Fin a, conjIf (decide (a ≤ (Fin.castAdd b t).val)) Q = Q := by
    intro t
    simp [conjIf]
  have h2 : ∀ t : Fin b, conjIf (decide (a ≤ (Fin.natAdd a t).val)) Q = starRingEnd ℂ Q := by
    intro t
    simp [conjIf]
  simp only [h1, h2, Fin.prod_const]

/-- `∏_r N⁻¹ ∑_{ν ∈ s} f_r(ν) = ∑_{νs ∈ s^p} N^{−p} ∏_r f_r(νs_r)`. -/
private theorem claimT_prod_avg {p : ℕ} (s : Finset (Fin N)) (f : Fin p → Fin N → ℂ) :
    ∏ r, ((N : ℂ)⁻¹ * ∑ ν ∈ s, f r ν) =
      ∑ νs ∈ Fintype.piFinset (fun _ : Fin p => s), (N : ℂ)⁻¹ ^ p * ∏ r, f r (νs r) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.prod_univ_sum, Finset.mul_sum]

/-- `|σ|_μ ≤ n + 1`. -/
private theorem claimT_tagMu_le {n : ℕ} (σ : Fin (n + 1) → Fin 3) : tagMu σ ≤ n + 1 := by
  unfold tagMu
  calc ∑ l, (if σ l = 0 then 0 else 1) ≤ ∑ _l : Fin (n + 1), 1 :=
        Finset.sum_le_sum fun l _ => by split_ifs <;> omega
    _ = n + 1 := by simp

private theorem claimT_degTab_le (x y : Letter) (s : Fin 3) : degTab x y s ≤ 2 := by
  revert x y s; decide

/-- `deg A(w, σ) ≤ 2 (n(w) + 1)`. -/
private theorem claimT_tagDeg_le (n : ℕ) (w : Word n) (σ : Fin (n + 1) → Fin 3) :
    tagDeg n w σ ≤ 2 * (n + 1) := by
  cases n with
  | zero => simp only [tagDeg]; split_ifs <;> omega
  | succ k =>
    simp only [tagDeg]
    calc ∑ l, degTab (factorX w l) (factorY w l) (σ l) ≤ ∑ _l : Fin (k + 2), 2 :=
          Finset.sum_le_sum fun l _ => claimT_degTab_le _ _ _
      _ = 2 * (k + 1 + 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring

/-- (A+_avg) for the expanded product: the column expectation of
`Γ(P) ∏_r N⁻¹ ∑_{ν ≠ μ} a_r(ν) A⁺_r(ν)`, with `P = ∑_{k ≤ K} 𝒴_k Q_μ^k` the expansion of
`G_μμ` (Gmumu_exp2) and `Γ(x) = ∏_r (x or x̄)^{|σ_r|_μ}`, is at most
`K' ((K + 1) C_Y)^{p+3} K_g^{(K+2)(p+3)} ∏_r α_r N^{−1/2} b^{d_X − [d_{X,i} = 3]}`
when `|a_r(ν)| ≤ α_r`, `|𝒴_k| ≤ C_Y` and the a priori bounds of `lem87_avg` hold. -/
private theorem claimT_main (C : ℕ → ℝ) (τ : ℝ) (hτ : 0 < τ) (p Kx : ℕ) :
    ∃ K' : ℝ, 0 ≤ K' ∧ ∀ (M N : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (i : Fin M) (μ : Fin N)
      (ρ : Fin M → Measure ℝ) [∀ j, IsProbabilityMeasure (ρ j)] (Kg b CY : ℝ),
      1 ≤ N → (M : ℝ) ≤ τ⁻¹ * N → 1 ≤ Kg → 0 ≤ b → b ≤ 1 → 1 ≤ CY →
      (∀ j, ∫ y, y ∂(ρ j) = 0) →
      (∀ j (n : ℕ), Integrable (fun y => |y| ^ n) (ρ j) ∧
        ∫ y, |Real.sqrt N * y| ^ n ∂(ρ j) ≤ C n) →
      (∀ ν, ν ≠ μ → ∀ j, ‖Gmu Sig A z μ (Sum.inr ν) (Sum.inl j)‖ ≤ b ∧
        ‖Gmu Sig A z μ (Sum.inl j) (Sum.inr ν)‖ ≤ b) →
      (∀ j j', ‖Gmu Sig A z μ (Sum.inl j) (Sum.inl j')‖ ≤ Kg) →
      (∑ j, ‖Gmu Sig A z μ (Sum.inl i) (Sum.inl j)‖ ≤ N * b) →
      (∑ j, ‖Gmu Sig A z μ (Sum.inl j) (Sum.inl i)‖ ≤ N * b) →
      (∑ j, ‖Gmu Sig A z μ (Sum.inl i) (Sum.inl j)‖ ^ 2 ≤ N * b ^ 2) →
      (∑ j, ‖Gmu Sig A z μ (Sum.inl j) (Sum.inl i)‖ ^ 2 ≤ N * b ^ 2) →
      (∀ k, ‖calY z (Ymu Sig A z μ) Kx k‖ ≤ CY) →
      ∀ (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r)) (σs : ∀ r, Fin (ns r + 1) → Fin 3)
        (cs : Fin p → Bool) (a : Fin p → Fin N → ℂ) (α : Fin p → ℝ), ∑ r, ns r = 3 →
        (∀ r, tagNZ (ns r) (ws r) (σs r) = true) → (∀ r, tagV (σs r) = 0) →
        (∀ r, 0 ≤ α r) → (∀ r ν, ν ≠ μ → ‖a r ν‖ ≤ α r) →
        ‖∫ y, (∏ r, conjIf (cs r) (∑ k ∈ Finset.range (Kx + 1),
              calY z (Ymu Sig A z μ) Kx k * Qmu Sig (updCol A μ y) z μ ^ k) ^ tagMu (σs r)) *
            ∏ r, ((N : ℂ)⁻¹ * ∑ ν ∈ Finset.univ.erase μ, a r ν *
              conjIf (cs r) (((tagForms Sig A z (eI (Sum.inr ν)) i μ (ns r) (ws r)
                (σs r)).map fun c => linForm c y).prod)) ∂(Measure.pi ρ)‖ ≤
          K' * (((Kx : ℝ) + 1) * CY) ^ (p + 3) * Kg ^ ((Kx + 2) * (p + 3)) * (∏ r, α r) *
            (N : ℝ) ^ (-(1 : ℝ) / 2) *
            b ^ (dXof ns ws σs - if dXIof ns ws σs = 3 then 1 else 0) := by
  choose Kf hKf0 hKf using fun k : ℕ => lem87_avg C τ hτ p k
  set Ks : ℝ := ∑ k ∈ Finset.range (Kx * (p + 3) + 1), Kf k with hKs
  have hKs0 : 0 ≤ Ks := Finset.sum_nonneg fun k _ => hKf0 k
  refine ⟨Ks, hKs0, ?_⟩
  intro M N Sig A z i μ ρ _ Kg b CY hN hM hKg hb0 hb1 hCY hmean hρ hGν hGjj hS1 hS1' hS2 hS2' hY
    ns ws σs cs a α hns hnz hv hα0 ha
  have hρi : ∀ j (n : ℕ), Integrable (fun y => |y| ^ n) (ρ j) := fun j n => (hρ j n).1
  set t : Fin p → ℕ := fun r => tagMu (σs r) with ht
  set d₀ : ℕ := ∑ r, if cs r then 0 else t r with hd₀
  set d₁ : ℕ := ∑ r, if cs r then t r else 0 with hd₁
  have hd : d₀ + d₁ ≤ p + 3 := by
    have e : d₀ + d₁ = ∑ r, t r := by
      rw [hd₀, hd₁, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun r _ => by split_ifs <;> simp
    rw [e]
    calc ∑ r, t r ≤ ∑ r, (ns r + 1) := Finset.sum_le_sum fun r _ => claimT_tagMu_le _
      _ = p + 3 := by rw [Finset.sum_add_distrib, hns]; simp; ring
  set Yc : ℕ → ℂ := fun k => calY z (Ymu Sig A z μ) Kx k with hYc
  set Q : (Fin M → ℝ) → ℂ := fun y => Qmu Sig (updCol A μ y) z μ with hQ
  set Φ : Fin p → Fin N → (Fin M → ℝ) → ℂ := fun r ν y =>
    ((tagForms Sig A z (eI (Sum.inr ν)) i μ (ns r) (ws r) (σs r)).map fun c => linForm c y).prod
    with hΦ
  set T₀ := Fintype.piFinset (fun _ : Fin d₀ => Finset.range (Kx + 1)) with hT₀
  set T₁ := Fintype.piFinset (fun _ : Fin d₁ => Finset.range (Kx + 1)) with hT₁
  set T₂ := Fintype.piFinset (fun _ : Fin p => (Finset.univ : Finset (Fin N)).erase μ) with hT₂
  set Cf : (Fin d₀ → ℕ) → (Fin d₁ → ℕ) → (Fin p → Fin N) → ℂ := fun κ κ' νs =>
    (∏ l, Yc (κ l)) * (∏ l, starRingEnd ℂ (Yc (κ' l))) * ((N : ℂ)⁻¹ ^ p * ∏ r, a r (νs r))
    with hCf
  set Mon : (Fin d₀ → ℕ) → (Fin d₁ → ℕ) → (Fin p → Fin N) → (Fin M → ℝ) → ℂ := fun κ κ' νs y =>
    (∏ r, conjIf (cs r) (Φ r (νs r) y)) *
      ∏ u : Fin ((∑ l, κ l) + ∑ l, κ' l), conjIf (decide ((∑ l, κ l) ≤ u.val)) (Q y) with hMon
  -- the pointwise expansion
  have hexp : ∀ y, (∏ r, conjIf (cs r) (∑ k ∈ Finset.range (Kx + 1), Yc k * Q y ^ k) ^ t r) *
      ∏ r, ((N : ℂ)⁻¹ * ∑ ν ∈ Finset.univ.erase μ, a r ν * conjIf (cs r) (Φ r ν y)) =
      ∑ κ ∈ T₀, ∑ κ' ∈ T₁, ∑ νs ∈ T₂, Cf κ κ' νs * Mon κ κ' νs y := by
    intro y
    rw [claimT_Gam_eq, claimT_pow_sum, map_sum, claimT_prod_avg]
    have hc : ∀ k ∈ Finset.range (Kx + 1), starRingEnd ℂ (Yc k * Q y ^ k) =
        starRingEnd ℂ (Yc k) * starRingEnd ℂ (Q y) ^ k := fun k _ => by
      rw [map_mul, map_pow]
    rw [Finset.sum_congr rfl hc, claimT_pow_sum, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun κ' _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun νs _ => ?_
    simp only [hCf, hMon]
    rw [← claimT_QQ, Finset.prod_mul_distrib]
    ring
  -- integrability of the monomials
  have hMonI : ∀ κ κ' νs, Integrable (Mon κ κ' νs) (Measure.pi ρ) := by
    intro κ κ' νs
    refine claimT_Mom.integrable (claimT_Mom_mul (claimT_Mom_prod _ fun r _ =>
      claimT_Mom_conjIf _ (claimT_Mom_listProd hρi _)) (claimT_Mom_prod _ fun u _ =>
        claimT_Mom_conjIf _ (claimT_Mom_Qmu hρi Sig A z μ)))
  -- the bound for one monomial
  set Bd : ℝ := Ks * Kg ^ ((Kx + 2) * (p + 3)) * (N : ℝ) ^ (-(1 : ℝ) / 2) *
    b ^ (dXof ns ws σs - if dXIof ns ws σs = 3 then 1 else 0) with hBd
  have hκ : ∀ {d : ℕ} (κ : Fin d → ℕ),
      κ ∈ Fintype.piFinset (fun _ : Fin d => Finset.range (Kx + 1)) →
      ∑ l, κ l ≤ Kx * d := by
    intro d κ hκ
    rw [Fintype.mem_piFinset] at hκ
    calc ∑ l, κ l ≤ ∑ _l : Fin d, Kx := Finset.sum_le_sum fun l _ => by
          have := Finset.mem_range.1 (hκ l); omega
      _ = Kx * d := by simp [mul_comm]
  have hMonB : ∀ κ ∈ T₀, ∀ κ' ∈ T₁, ∀ νs ∈ T₂, ‖∫ y, Mon κ κ' νs y ∂(Measure.pi ρ)‖ ≤ Bd := by
    intro κ hκ0 κ' hκ1 νs hνs
    set k := (∑ l, κ l) + ∑ l, κ' l with hk
    have hkle : k ≤ Kx * (p + 3) := by
      have h0 := hκ κ hκ0
      have h1 := hκ κ' hκ1
      have : Kx * d₀ + Kx * d₁ ≤ Kx * (p + 3) := by rw [← mul_add]; exact Nat.mul_le_mul_left _ hd
      omega
    have hνμ : ∀ r, νs r ≠ μ := fun r => by
      rw [hT₂, Fintype.mem_piFinset] at hνs
      exact Finset.ne_of_mem_erase (hνs r)
    have h := hKf k M N Sig A z i μ νs ρ Kg b hN hM hKg hb0 hb1 hmean hρ hνμ
      (fun r j => hGν (νs r) (hνμ r) j) hGjj hS1 hS1' hS2 hS2' ns ws σs cs
      (fun u => decide ((∑ l, κ l) ≤ u.val)) hns hnz hv
    have hdX : dXof ns ws σs ≤ 2 * p + 6 := by
      calc dXof ns ws σs = ∑ r, tagDeg (ns r) (ws r) (σs r) := rfl
        _ ≤ ∑ r, 2 * (ns r + 1) := Finset.sum_le_sum fun r _ => claimT_tagDeg_le _ _ _
        _ = 2 * p + 6 := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib, hns, Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, smul_eq_mul]; ring
    have hKfle : Kf k ≤ Ks := Finset.single_le_sum (fun k _ => hKf0 k)
      (Finset.mem_range.2 (by omega))
    calc ‖∫ y, Mon κ κ' νs y ∂(Measure.pi ρ)‖
        ≤ Kf k * Kg ^ (dXof ns ws σs + k) * (N : ℝ) ^ (-(1 : ℝ) / 2) *
            b ^ (dXof ns ws σs - if dXIof ns ws σs = 3 then 1 else 0) := h
      _ ≤ Bd := by
          rw [hBd]
          have hN0 : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul hKfle (pow_le_pow_right₀ hKg ?_) (by positivity) hKs0) hN0)
            (pow_nonneg hb0 _)
          nlinarith
  -- the coefficients
  have hCfB : ∀ κ ∈ T₀, ∀ κ' ∈ T₁, ∀ νs ∈ T₂,
      ‖Cf κ κ' νs‖ ≤ CY ^ (d₀ + d₁) * (((N : ℝ) ^ p)⁻¹ * ∏ r, α r) := by
    intro κ _ κ' _ νs hνs
    have hνμ : ∀ r, νs r ≠ μ := fun r => by
      rw [hT₂, Fintype.mem_piFinset] at hνs
      exact Finset.ne_of_mem_erase (hνs r)
    simp only [hCf]
    rw [norm_mul, norm_mul, norm_mul, norm_prod, norm_prod, norm_pow, norm_inv,
      Complex.norm_natCast, norm_prod, pow_add, inv_pow]
    have h1 : ∏ l, ‖Yc (κ l)‖ ≤ CY ^ d₀ := by
      calc ∏ l, ‖Yc (κ l)‖ ≤ ∏ _l : Fin d₀, CY :=
            Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun l _ => hY _
        _ = CY ^ d₀ := by simp
    have h2 : ∏ l, ‖starRingEnd ℂ (Yc (κ' l))‖ ≤ CY ^ d₁ := by
      calc ∏ l, ‖starRingEnd ℂ (Yc (κ' l))‖ ≤ ∏ _l : Fin d₁, CY :=
            Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun l _ => by
              rw [Complex.norm_conj]; exact hY _
        _ = CY ^ d₁ := by simp
    have h3 : ∏ r, ‖a r (νs r)‖ ≤ ∏ r, α r :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun r _ => ha r _ (hνμ r)
    have hCY0 : 0 ≤ CY := zero_le_one.trans hCY
    exact mul_le_mul (mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      (pow_nonneg hCY0 _)) (mul_le_mul_of_nonneg_left h3 (by positivity))
      (mul_nonneg (by positivity) (Finset.prod_nonneg fun _ _ => norm_nonneg _)) (by positivity)
  have hcard0 : (T₀.card : ℝ) = ((Kx : ℝ) + 1) ^ d₀ := by
    rw [hT₀, Fintype.card_piFinset_const, Finset.card_range]; push_cast; ring
  have hcard1 : (T₁.card : ℝ) = ((Kx : ℝ) + 1) ^ d₁ := by
    rw [hT₁, Fintype.card_piFinset_const, Finset.card_range]; push_cast; ring
  have hcard2 : (T₂.card : ℝ) ≤ (N : ℝ) ^ p := by
    rw [hT₂, Fintype.card_piFinset_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
    push_cast
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le N 1) p
  have hNp : (0 : ℝ) < (N : ℝ) ^ p := pow_pos (by exact_mod_cast hN) p
  have hBd0 : 0 ≤ Bd := by
    rw [hBd]
    have := Real.rpow_nonneg (Nat.cast_nonneg N) (-(1 : ℝ) / 2)
    have := pow_nonneg hb0 (dXof ns ws σs - if dXIof ns ws σs = 3 then 1 else 0)
    positivity
  have hα : 0 ≤ ∏ r, α r := Finset.prod_nonneg fun r _ => hα0 r
  have hCY0 : 0 ≤ CY := zero_le_one.trans hCY
  have hbase : 1 ≤ ((Kx : ℝ) + 1) * CY := by
    have : (1 : ℝ) ≤ (Kx : ℝ) + 1 := by have := (Nat.cast_nonneg Kx : (0 : ℝ) ≤ Kx); linarith
    nlinarith
  calc ‖∫ y, (∏ r, conjIf (cs r) (∑ k ∈ Finset.range (Kx + 1), Yc k * Q y ^ k) ^ t r) *
          ∏ r, ((N : ℂ)⁻¹ * ∑ ν ∈ Finset.univ.erase μ, a r ν * conjIf (cs r) (Φ r ν y))
          ∂(Measure.pi ρ)‖
      = ‖∫ y, ∑ κ ∈ T₀, ∑ κ' ∈ T₁, ∑ νs ∈ T₂, Cf κ κ' νs * Mon κ κ' νs y
          ∂(Measure.pi ρ)‖ := by
        rw [integral_congr_ae (ae_of_all _ hexp)]
    _ = ‖∑ κ ∈ T₀, ∑ κ' ∈ T₁, ∑ νs ∈ T₂, Cf κ κ' νs * ∫ y, Mon κ κ' νs y ∂(Measure.pi ρ)‖ := by
        rw [integral_finsetSum _ fun κ _ => integrable_finsetSum _ fun κ' _ =>
          integrable_finsetSum _ fun νs _ => (hMonI κ κ' νs).const_mul _]
        congr 1
        refine Finset.sum_congr rfl fun κ _ => ?_
        rw [integral_finsetSum _ fun κ' _ => integrable_finsetSum _ fun νs _ =>
          (hMonI κ κ' νs).const_mul _]
        refine Finset.sum_congr rfl fun κ' _ => ?_
        rw [integral_finsetSum _ fun νs _ => (hMonI κ κ' νs).const_mul _]
        exact Finset.sum_congr rfl fun νs _ => integral_const_mul _ _
    _ ≤ ∑ κ ∈ T₀, ∑ κ' ∈ T₁, ∑ νs ∈ T₂,
          CY ^ (d₀ + d₁) * (((N : ℝ) ^ p)⁻¹ * ∏ r, α r) * Bd := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun κ hκ0 => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun κ' hκ1 => (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun νs hνs => ?_)))
        rw [norm_mul]
        exact mul_le_mul (hCfB κ hκ0 κ' hκ1 νs hνs) (hMonB κ hκ0 κ' hκ1 νs hνs) (norm_nonneg _)
          (by positivity)
    _ = (T₀.card : ℝ) * ((T₁.card : ℝ) * ((T₂.card : ℝ) *
          (CY ^ (d₀ + d₁) * (((N : ℝ) ^ p)⁻¹ * ∏ r, α r) * Bd))) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((Kx : ℝ) + 1) ^ d₀ * (((Kx : ℝ) + 1) ^ d₁ * ((N : ℝ) ^ p *
          (CY ^ (d₀ + d₁) * (((N : ℝ) ^ p)⁻¹ * ∏ r, α r) * Bd))) := by
        rw [hcard0, hcard1]
        gcongr
    _ = (((Kx : ℝ) + 1) * CY) ^ (d₀ + d₁) * (∏ r, α r) * Bd := by
        rw [mul_pow, pow_add, pow_add]
        field_simp
    _ ≤ (((Kx : ℝ) + 1) * CY) ^ (p + 3) * (∏ r, α r) * Bd := by
        gcongr
    _ = _ := by rw [hBd]; ring

/-! ## Continuity in the matrix -/

section Cont

variable {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {z : ℂ} (hz : 0 < z.im)
include hSig hz

private theorem claimT_cont_G : Continuous fun A : Matrix (Fin M) (Fin N) ℝ => G Sig A z := by
  have hc : Continuous fun A : Matrix (Fin M) (Fin N) ℝ => linH Sig⁻¹ A z := by
    unfold linH cplx
    refine Continuous.matrix_fromBlocks continuous_const ?_ ?_ continuous_const
    · exact Continuous.matrix_map continuous_id Complex.continuous_ofReal
    · exact Continuous.matrix_map continuous_id.matrix_transpose Complex.continuous_ofReal
  have h : (fun A : Matrix (Fin M) (Fin N) ℝ => G Sig A z) =
      fun A => (linH Sig⁻¹ A z).det⁻¹ • (linH Sig⁻¹ A z).adjugate := by
    funext A
    change (linH Sig⁻¹ A z)⁻¹ = _
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  refine Continuous.smul ((hc.matrix_det).inv₀ fun A => ?_) hc.matrix_adjugate
  exact ((isUnit_iff_isUnit_det _).1 (H_isUnit hSig A hz)).ne_zero

private theorem claimT_cont_Gent (s t : Fin M ⊕ Fin N) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => G Sig A z s t :=
  (claimT_cont_G hSig hz).matrix_elem s t

private theorem claimT_cont_Gmu (μ : Fin N) (s t : Fin M ⊕ Fin N) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => Gmu Sig A z μ s t := by
  by_cases hs : s = Sum.inr μ
  · subst hs; simp only [claimT_Gmu_row]; exact continuous_const
  by_cases ht : t = Sum.inr μ
  · subst ht; simp only [claimT_Gmu_col]; exact continuous_const
  have e : (fun A : Matrix (Fin M) (Fin N) ℝ => Gmu Sig A z μ s t) =
      fun A => G Sig (updCol A μ 0) z s t := funext fun A => claimT_Gmu_eq hSig A hz μ s t hs ht
  rw [e]
  have hu : Continuous fun A : Matrix (Fin M) (Fin N) ℝ => updCol A μ 0 := by
    refine continuous_pi fun j => continuous_pi fun ν => ?_
    by_cases h : ν = μ
    · simp only [updCol, h, ite_true]; exact continuous_const
    · simp only [updCol, h, ite_false]; exact (continuous_apply ν).comp (continuous_apply j)
  exact (claimT_cont_Gent hSig hz s t).comp hu

private theorem claimT_cont_entGmu (μ : Fin N) (x y : Fin M ⊕ Fin N → ℝ) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => ent (Gmu Sig A z μ) x y := by
  have e : (fun A : Matrix (Fin M) (Fin N) ℝ => ent (Gmu Sig A z μ) x y) =
      fun A => ∑ s, ∑ t, (x s : ℂ) * Gmu Sig A z μ s t * (y t : ℂ) := by
    funext A; simp only [ent, cvec, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  rw [e]
  exact continuous_finsetSum _ fun s _ => continuous_finsetSum _ fun t _ =>
    (continuous_const.mul (claimT_cont_Gmu hSig hz μ s t)).mul continuous_const

omit hSig hz in
private theorem claimT_cont_col (μ : Fin N) (j : Fin M) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => ((A j μ : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp ((continuous_apply μ).comp (continuous_apply j))

private theorem claimT_cont_colC (μ : Fin N) (x : Fin M ⊕ Fin N → ℝ) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => linForm (colC Sig A z x μ) fun j => A j μ :=
  continuous_finsetSum _ fun j _ =>
    (claimT_cont_entGmu hSig hz μ x _).mul (claimT_cont_col μ j)

private theorem claimT_cont_rowC (μ : Fin N) (x : Fin M ⊕ Fin N → ℝ) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => linForm (rowC Sig A z x μ) fun j => A j μ :=
  continuous_finsetSum _ fun j _ =>
    (claimT_cont_entGmu hSig hz μ _ x).mul (claimT_cont_col μ j)

private theorem claimT_cont_brack (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N)
    (x y : Letter) (s : Fin 3) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => brack Sig A z v i μ x y s := by
  have h1 := claimT_cont_colC hSig hz μ (letVec Sig v i μ x)
  have h2 := claimT_cont_rowC hSig hz μ (letVec Sig v i μ y)
  have h3 := claimT_cont_entGmu hSig hz μ (letVec Sig v i μ x) (letVec Sig v i μ y)
  unfold brack brackScal brackForms
  split_ifs <;>
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, List.cons_append,
      List.nil_append, mul_one, one_mul] <;>
    first
    | exact continuous_const
    | exact h3
    | exact h1
    | exact h2
    | exact h1.mul h2
    | exact continuous_const.mul h1
    | exact continuous_const.mul h2
    | exact continuous_const.mul (h1.mul h2)

private theorem claimT_cont_tagA (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) (n : ℕ)
    (w : Word n) (σ : Fin (n + 1) → Fin 3) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => tagA Sig A z v i μ n w σ := by
  cases n with
  | zero =>
    have h1 := claimT_cont_colC hSig hz μ (vbar Sig v)
    have h2 := claimT_cont_rowC hSig hz μ (vbar Sig v)
    have h3 := claimT_cont_entGmu hSig hz μ (vbar Sig v) (vbar Sig v)
    simp only [tagA, emptyScal, emptyForms]
    split_ifs <;>
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] <;>
      first
      | exact h3.sub continuous_const
      | exact continuous_const.mul (h1.mul h2)
      | exact continuous_const.mul (by
          simp only [linForm, Pi.add_apply, add_mul, Finset.sum_add_distrib]
          exact h1.add h2)
  | succ k =>
    simp only [tagA]
    exact continuous_finsetProd _ fun l _ => claimT_cont_brack hSig hz v i μ _ _ _

private theorem claimT_cont_Ymu (μ : Fin N) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => Ymu Sig A z μ :=
  continuous_const.mul (continuous_finsetSum _ fun _ _ => claimT_cont_Gmu hSig hz μ _ _)

private theorem claimT_cont_Qmu (μ : Fin N) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => Qmu Sig A z μ := by
  have e : (fun A : Matrix (Fin M) (Fin N) ℝ => Qmu Sig A z μ) = fun A =>
      ∑ j, ∑ j', ((A j μ : ℝ) : ℂ) * Gmu Sig A z μ (Sum.inl j) (Sum.inl j') *
        ((A j' μ : ℝ) : ℂ) := by
    funext A
    have hA : updCol A μ (fun j => A j μ) = A := by
      funext j ν; by_cases h : ν = μ <;> simp [updCol, h]
    conv_lhs => rw [← hA]
    rw [Qmu_updCol]
  rw [e]
  exact continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun j' _ =>
    ((claimT_cont_col μ j).mul (claimT_cont_Gmu hSig hz μ _ _)).mul (claimT_cont_col μ j')

private theorem claimT_Y_ne (A : Matrix (Fin M) (Fin N) ℝ) (μ : Fin N) :
    -z - Ymu Sig A z μ ≠ 0 := by
  intro h
  have := (calY_rough hSig A hz μ).1
  rw [h, Complex.zero_im] at this
  linarith

private theorem claimT_cont_calY (μ : Fin N) (K k : ℕ) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => calY z (Ymu Sig A z μ) K k := by
  unfold calY
  have hY := claimT_cont_Ymu hSig hz μ
  refine continuous_finsetSum _ fun t _ => ?_
  exact ((((continuous_const.sub hY).inv₀ fun A => claimT_Y_ne hSig hz A μ).pow _).mul
    continuous_const).mul (hY.neg.pow _)

end Cont

/-! ## The integrand of (avg_step 1) -/

private theorem claimT_conjIf_mul (c : Bool) (x y : ℂ) :
    conjIf c (x * y) = conjIf c x * conjIf c y := by
  cases c <;> simp [conjIf]

private theorem claimT_conjIf_pow (c : Bool) (x : ℂ) (n : ℕ) :
    conjIf c (x ^ n) = conjIf c x ^ n := by
  cases c <;> simp [conjIf]

private theorem claimT_conjIf_sum {ι : Type*} (c : Bool) (s : Finset ι) (f : ι → ℂ) :
    conjIf c (∑ a ∈ s, f a) = ∑ a ∈ s, conjIf c (f a) := by
  cases c <;> simp [conjIf]

private theorem claimT_conjIf_one (c : Bool) : conjIf c 1 = 1 := by
  cases c <;> simp [conjIf]

private theorem claimT_norm_conjIf (c : Bool) (x : ℂ) : ‖conjIf c x‖ = ‖x‖ := by
  cases c <;> simp [conjIf]

/-- `Γ(x) = ∏_r (x or x̄)^{|σ_r|_μ}`. -/
private def claimT_Gam {p : ℕ} (ns : Fin p → ℕ) (σs : ∀ r, Fin (ns r + 1) → Fin 3)
    (cs : Fin p → Bool) (x : ℂ) : ℂ :=
  ∏ r, conjIf (cs r) x ^ tagMu (σs r)

/-- `H_r = N⁻¹ ∑_{ν ≠ μ} A_{e_ν, i, μ}(w_r, σ_r)` (or its conjugate). -/
private def claimT_H (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (i : Fin M) (μ : Fin N) {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r))
    (σs : ∀ r, Fin (ns r + 1) → Fin 3) (cs : Fin p → Bool) (r : Fin p) : ℂ :=
  (N : ℂ)⁻¹ * ∑ ν ∈ Finset.univ.erase μ,
    conjIf (cs r) (tagA Sig A z (eI (Sum.inr ν)) i μ (ns r) (ws r) (σs r))

/-- The integrand of (avg_step 1) at one tagged tuple. -/
private def claimT_F (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (i : Fin M) (μ : Fin N) {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r))
    (σs : ∀ r, Fin (ns r + 1) → Fin 3) (cs : Fin p → Bool) : ℂ :=
  (N : ℂ)⁻¹ ^ p * ∑ νs ∈ Fintype.piFinset (fun _ : Fin p => Finset.univ.erase μ),
    ∏ r, conjIf (cs r) (tagA Sig A z (eI (Sum.inr (νs r))) i μ (ns r) (ws r) (σs r) *
      G Sig A z (Sum.inr μ) (Sum.inr μ) ^ tagMu (σs r))

/-- The `ν`-sums factorize: the integrand is `Γ(G_μμ) ∏_r H_r`. -/
private theorem claimT_F_eq (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (i : Fin M) (μ : Fin N) {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r))
    (σs : ∀ r, Fin (ns r + 1) → Fin 3) (cs : Fin p → Bool) :
    claimT_F Sig A z i μ ns ws σs cs = claimT_Gam ns σs cs (G Sig A z (Sum.inr μ) (Sum.inr μ)) *
      ∏ r, claimT_H Sig A z i μ ns ws σs cs r := by
  unfold claimT_F claimT_H claimT_Gam
  rw [claimT_prod_avg, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun νs _ => ?_
  simp only [claimT_conjIf_mul, claimT_conjIf_pow, Finset.prod_mul_distrib]
  ring

/-- For `n(w) = 0` and `|σ|_μ = 0`: no forms and `A⁰ = A(w₀, 0)`. -/
private theorem claimT_empty_zero (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) (n : ℕ) (hn : n = 0) (w : Word n)
    (σ : Fin (n + 1) → Fin 3) (hσ : tagMu σ = 0) :
    tagForms Sig A z v i μ n w σ = [] ∧ tagScal Sig A z v i μ n w σ = emptyScal Sig A z v μ 0 := by
  subst hn
  have h0 : σ 0 = 0 := by
    by_contra h
    have : tagMu σ = 1 := by simp [tagMu, h]
    omega
  simp [tagForms, tagScal, emptyForms, h0]

/-- For `n(w) = 0` and `ℤ₂` tags with `|σ|_μ ≠ 0`: `A⁰ = 1`. -/
private theorem claimT_empty_one (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) (n : ℕ) (hn : n = 0) (w : Word n)
    (σ : Fin (n + 1) → Fin 3) (hσ : tagMu σ ≠ 0) (hv : tagV σ = 0) :
    tagScal Sig A z v i μ n w σ = 1 := by
  subst hn
  have h2 := claimT_ne_two hv 0
  have h0 : σ 0 ≠ 0 := by
    intro h
    exact hσ (by simp [tagMu, h])
  have h1 : σ 0 = 1 := by
    revert h0 h2; generalize σ 0 = t; intro h0 h2; fin_cases t <;> simp_all
  simp [tagScal, emptyScal, h1]

/-- (A+_avg_3) for the scalar factor, any `n(w) ≥ 1`. -/
private theorem claimT_tagScal_le' (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (ν : Fin N) (i : Fin M) (μ : Fin N) {K b : ℝ}
    (hK1 : 1 ≤ K) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hK : ∀ s t, ‖Gmu Sig A z μ s t‖ ≤ K)
    (hbl : ‖Gmu Sig A z μ (Sum.inr ν) (Sum.inl i)‖ ≤ b)
    (hbr : ‖Gmu Sig A z μ (Sum.inl i) (Sum.inr ν)‖ ≤ b) (n : ℕ) (hn : 1 ≤ n) (w : Word n)
    (σ : Fin (n + 1) → Fin 3) (hv : tagV σ = 0) :
    ‖tagScal Sig A z (eI (Sum.inr ν)) i μ n w σ‖ ≤ K ^ (n + 1) * b ^ (2 - tagDeg n w σ) := by
  cases n with
  | zero => omega
  | succ k => exact claimT_tagScal_le Sig A z ν i μ hK1 hb0 hb1 hK hbl hbr k w σ hv

/-- The rough bound `|A⁰(w, σ)| ≤ (K + K')^{n+1}` for `|G^{(μ)}_{st}| ≤ K`, `|Π_{st}| ≤ K'`. -/
private theorem claimT_tagScal_rough (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) {ν μ : Fin N} (hν : ν ≠ μ) (i : Fin M) {K K' : ℝ}
    (hK1 : 1 ≤ K) (hK'0 : 0 ≤ K') (hK : ∀ s t, ‖Gmu Sig A z μ s t‖ ≤ K)
    (hK' : ∀ s t, ‖PiZ N Sig z s t‖ ≤ K') (n : ℕ) (w : Word n) (σ : Fin (n + 1) → Fin 3) :
    ‖tagScal Sig A z (eI (Sum.inr ν)) i μ n w σ‖ ≤ (K + K') ^ (n + 1) := by
  cases n with
  | zero =>
    simp only [tagScal, zero_add, pow_one]
    by_cases h0 : σ 0 = 0
    · rw [h0, claimT_emptyScal_zero Sig A z hν]
      exact (norm_sub_le _ _).trans (add_le_add (hK _ _) (hK' _ _))
    · simp only [emptyScal, h0, ite_false]
      split_ifs <;> simp <;> linarith
  | succ k =>
    simp only [tagScal, norm_prod]
    calc ∏ l : Fin (k + 2), ‖brackScal Sig A z (eI (Sum.inr ν)) i μ (factorX w l) (factorY w l)
          (σ l)‖ ≤ ∏ _l : Fin (k + 2), (K + K') :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun l _ =>
            (claimT_brackScal_le Sig A z ν i μ hK1 hK _ _ _).trans (by linarith)
      _ = (K + K') ^ (k + 1 + 1) := by simp

private theorem claimT_ent_eq {ι : Type*} [Fintype ι] (B : Matrix ι ι ℂ) (x y : ι → ℝ) :
    ent B x y = ∑ s, ∑ t, (x s : ℂ) * B s t * (y t : ℂ) := by
  simp only [ent, cvec, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

private theorem claimT_ent_eI_left {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ)
    (y : ι → ℝ) (r : ι) : ent B (eI r) y = ∑ t, B r t * (y t : ℂ) := by
  rw [claimT_ent_eq]
  simp [eI, Pi.single_apply, apply_ite, ite_mul, Finset.sum_ite_eq']

private theorem claimT_ent_eI_right {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ)
    (x : ι → ℝ) (r : ι) : ent B x (eI r) = ∑ s, (x s : ℂ) * B s r := by
  rw [claimT_ent_eq]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [eI, Pi.single_apply, apply_ite]

/-- The identically vanishing brackets have scalar `0`. -/
private theorem claimT_brackScal_zero (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N)
    (x y : Letter) (s : Fin 3) (h : zeroTab x y s = true) :
    brackScal Sig A z v i μ x y s = 0 := by
  have hl : ∀ y', ent (Gmu Sig A z μ) (eI (Sum.inr μ)) y' = 0 := fun y' => by
    rw [claimT_ent_eI_left]; simp [claimT_Gmu_row]
  have hr : ∀ x', ent (Gmu Sig A z μ) x' (eI (Sum.inr μ)) = 0 := fun x' => by
    rw [claimT_ent_eI_right]; simp [claimT_Gmu_col]
  fin_cases s <;> cases x <;> cases y <;> simp [zeroTab] at h <;>
    simp [brackScal, letVec, hl, hr]

/-- A tagged word with an identically vanishing bracket vanishes. -/
private theorem claimT_tagA_zero (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) (n : ℕ) (w : Word n)
    (σ : Fin (n + 1) → Fin 3) (h : tagNZ n w σ = false) : tagA Sig A z v i μ n w σ = 0 := by
  cases n with
  | zero => simp [tagNZ] at h
  | succ k =>
    rw [tagA_eq_scal_mul]
    simp only [tagNZ, List.all_eq_false, List.mem_finRange, true_and, Bool.not_eq_true'] at h
    obtain ⟨l, hl⟩ := h
    have : tagScal Sig A z v i μ (k + 1) w σ = 0 := by
      simp only [tagScal]
      exact Finset.prod_eq_zero (Finset.mem_univ l)
        (claimT_brackScal_zero Sig A z v i μ _ _ _ (by simpa using hl))
    rw [this, zero_mul]

/-- `H_r` with the column `μ` replaced by `y`: `N⁻¹ ∑_{ν ≠ μ} A⁰(ν) A⁺(ν)(y)`. -/
private theorem claimT_H_updCol (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (i : Fin M) (μ : Fin N) {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r))
    (σs : ∀ r, Fin (ns r + 1) → Fin 3) (cs : Fin p → Bool) (y : Fin M → ℝ) (r : Fin p) :
    claimT_H Sig (updCol A μ y) z i μ ns ws σs cs r = (N : ℂ)⁻¹ * ∑ ν ∈ Finset.univ.erase μ,
      conjIf (cs r) (tagScal Sig A z (eI (Sum.inr ν)) i μ (ns r) (ws r) (σs r)) *
        conjIf (cs r) (((tagForms Sig A z (eI (Sum.inr ν)) i μ (ns r) (ws r) (σs r)).map
          fun c => linForm c y).prod) := by
  unfold claimT_H
  congr 1
  refine Finset.sum_congr rfl fun ν _ => ?_
  have hy : (fun j => updCol A μ y j μ) = y := funext fun j => by simp [updCol]
  rw [tagA_eq_scal_mul, (tagScal_updCol Sig A z _ i μ y _ _ _).1,
    (tagScal_updCol Sig A z _ i μ y _ _ _).2, hy, claimT_conjIf_mul]

/-- `|N⁻¹ ∑_{ν ≠ μ} f(ν)| ≤ B` when every `|f(ν)| ≤ B`. -/
private theorem claimT_avg_le {μ : Fin N} {f : Fin N → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ ν, ν ≠ μ → ‖f ν‖ ≤ B) : ‖(N : ℂ)⁻¹ * ∑ ν ∈ Finset.univ.erase μ, f ν‖ ≤ B := by
  have hN : 0 < N := Fin.pos μ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (N : ℝ)⁻¹ * ‖∑ ν ∈ Finset.univ.erase μ, f ν‖ ≤ (N : ℝ)⁻¹ * ∑ _ν : Fin N, B := by
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (by positivity)
        exact (Finset.sum_le_sum fun ν hν => h ν (Finset.ne_of_mem_erase hν)).trans
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun _ _ _ => hB)
    _ = B := by simp; field_simp

/-- `conjIf c (N⁻¹ x) = N⁻¹ conjIf c x`. -/
private theorem claimT_conjIf_inv_mul (c : Bool) (x : ℂ) :
    conjIf c ((N : ℂ)⁻¹ * x) = (N : ℂ)⁻¹ * conjIf c x := by
  cases c <;> simp [conjIf]

/-- `deg A(w₀, σ) = 2` for the empty word with tag `1`. -/
private theorem claimT_empty_deg (n : ℕ) (hn : n = 0) (w : Word n) (σ : Fin (n + 1) → Fin 3)
    (hσ : tagMu σ ≠ 0) (hv : tagV σ = 0) : tagDeg n w σ = 2 := by
  subst hn
  have h2 := claimT_ne_two hv 0
  have h0 : σ 0 ≠ 0 := by
    intro h
    exact hσ (by simp [tagMu, h])
  have h1 : σ 0 = 1 := by
    revert h0 h2; generalize σ 0 = t; intro h0 h2; fin_cases t <;> simp_all
  simp [tagDeg, h1]

/-- (A+_avg_3) for every word that is not the empty word with tag `0`:
`|A⁰(w, σ)| ≤ K^{n+1} b^{(2 − deg A(w, σ))_+}`. -/
private theorem claimT_scal_bound (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (ν : Fin N) (i : Fin M) (μ : Fin N) {K b : ℝ}
    (hK1 : 1 ≤ K) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hK : ∀ s t, ‖Gmu Sig A z μ s t‖ ≤ K)
    (hbl : ‖Gmu Sig A z μ (Sum.inr ν) (Sum.inl i)‖ ≤ b)
    (hbr : ‖Gmu Sig A z μ (Sum.inl i) (Sum.inr ν)‖ ≤ b) (n : ℕ) (w : Word n)
    (σ : Fin (n + 1) → Fin 3) (hv : tagV σ = 0) (h0 : ¬(n = 0 ∧ tagMu σ = 0)) :
    ‖tagScal Sig A z (eI (Sum.inr ν)) i μ n w σ‖ ≤ K ^ (n + 1) * b ^ (2 - tagDeg n w σ) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have hσ : tagMu σ ≠ 0 := fun h => h0 ⟨hn, h⟩
    rw [claimT_empty_one Sig A z _ i μ n hn w σ hσ hv, claimT_empty_deg n hn w σ hσ hv]
    simp only [norm_one, Nat.sub_self, pow_zero, mul_one]
    exact one_le_pow₀ hK1
  · exact claimT_tagScal_le' Sig A z ν i μ hK1 hb0 hb1 hK hbl hbr n hn w σ hv

/-- On the a priori event: `H_r = (Â⁰ or its conjugate)` for the empty word with tag `0`, and
`|H_r| ≤ K⁴ b²` otherwise (`n(w_r) ≤ 3`). -/
private theorem claimT_H_event {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (i : Fin M) (μ : Fin N)
    {b₀ L Kg b : ℝ} (hG : ∀ s t, ‖G Sig A z s t - PiZ N Sig z s t‖ ≤ b₀)
    (hμ : 1 ≤ L * ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖) (hKg : 1 ≤ Kg) (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1) (hLb : L * b₀ ≤ b) (hK : ∀ s t, ‖Gmu Sig A z μ s t‖ ≤ Kg)
    (hGν : ∀ ν, ν ≠ μ → ∀ j, ‖Gmu Sig A z μ (Sum.inr ν) (Sum.inl j)‖ ≤ b ∧
      ‖Gmu Sig A z μ (Sum.inl j) (Sum.inr ν)‖ ≤ b)
    {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r)) (σs : ∀ r, Fin (ns r + 1) → Fin 3)
    (cs : Fin p → Bool) (r : Fin p) (hn3 : ns r ≤ 3) (hv : tagV (σs r) = 0) :
    (ns r = 0 ∧ tagMu (σs r) = 0 →
      claimT_H Sig A z i μ ns ws σs cs r = conjIf (cs r) (claimT_Shat Sig A z μ)) ∧
    (¬(ns r = 0 ∧ tagMu (σs r) = 0) → ‖claimT_H Sig A z i μ ns ws σs cs r‖ ≤ Kg ^ 4 * b ^ 2) := by
  constructor
  · rintro ⟨hn, hm⟩
    unfold claimT_H claimT_Shat
    rw [claimT_conjIf_inv_mul, claimT_conjIf_sum]
    congr 1
    refine Finset.sum_congr rfl fun ν _ => ?_
    obtain ⟨h1, h2⟩ := claimT_empty_zero Sig A z (eI (Sum.inr ν)) i μ (ns r) hn (ws r) (σs r) hm
    rw [tagA_eq_scal_mul, h1, h2]
    simp
  · intro h0
    refine claimT_avg_le (by positivity) fun ν hν => ?_
    rw [claimT_norm_conjIf, tagA_eq_scal_mul, norm_mul]
    have hs := claimT_scal_bound Sig A z ν i μ hKg hb0 hb1 hK (hGν ν hν i).1 (hGν ν hν i).2
      (ns r) (ws r) (σs r) hv h0
    have hf := claimT_tagForms_event hSig A hz hν i hG hμ (ns r) (ws r) (σs r) hv
    have hLb0 : 0 ≤ L * b₀ := by
      have := (norm_nonneg _).trans (hG (Sum.inr μ) (Sum.inr μ))
      have hL : 0 ≤ L := by
        by_contra hc
        have := lt_of_not_ge hc
        nlinarith [norm_nonneg (G Sig A z (Sum.inr μ) (Sum.inr μ))]
      positivity
    have hf' := hf.trans (pow_le_pow_left₀ hLb0 hLb _)
    have hexp : b ^ (2 - tagDeg (ns r) (ws r) (σs r)) * b ^ tagDeg (ns r) (ws r) (σs r) ≤
        b ^ 2 := by
      rw [← pow_add]; exact pow_le_pow_of_le_one hb0 hb1 (by omega)
    calc ‖tagScal Sig A z (eI (Sum.inr ν)) i μ (ns r) (ws r) (σs r)‖ *
          ‖((tagForms Sig A z (eI (Sum.inr ν)) i μ (ns r) (ws r) (σs r)).map
            fun c => linForm c fun j => A j μ).prod‖
        ≤ Kg ^ (ns r + 1) * b ^ (2 - tagDeg (ns r) (ws r) (σs r)) *
            b ^ tagDeg (ns r) (ws r) (σs r) :=
          mul_le_mul hs hf' (norm_nonneg _) (by positivity)
      _ ≤ Kg ^ 4 * b ^ 2 := by
          rw [mul_assoc]
          exact mul_le_mul (pow_le_pow_right₀ hKg (by omega)) hexp (by positivity)
            (by positivity)

/-- `|x^n − y^n| ≤ n B^n δ` for `|x|, |y| ≤ B`, `B ≥ 1`, `|x − y| ≤ δ`. -/
private theorem claimT_pow_sub_le {x y : ℂ} {B δ : ℝ} (hB : 1 ≤ B) (hx : ‖x‖ ≤ B) (hy : ‖y‖ ≤ B)
    (hxy : ‖x - y‖ ≤ δ) (n : ℕ) : ‖x ^ n - y ^ n‖ ≤ n * B ^ n * δ := by
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hxy
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  induction n with
  | zero => simp
  | succ n ih =>
    have e : x ^ (n + 1) - y ^ (n + 1) = (x - y) * x ^ n + y * (x ^ n - y ^ n) := by ring
    rw [e]
    have h1 : ‖(x - y) * x ^ n‖ ≤ δ * B ^ n := by
      rw [norm_mul, norm_pow]
      exact mul_le_mul hxy (pow_le_pow_left₀ (norm_nonneg _) hx n) (by positivity) hδ
    have h2 : ‖y * (x ^ n - y ^ n)‖ ≤ B * (n * B ^ n * δ) := by
      rw [norm_mul]; exact mul_le_mul hy ih (norm_nonneg _) hB0
    have h3 : δ * B ^ n ≤ δ * B ^ (n + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB (by omega)) hδ
    calc ‖(x - y) * x ^ n + y * (x ^ n - y ^ n)‖ ≤ δ * B ^ n + B * (n * B ^ n * δ) :=
          (norm_add_le _ _).trans (add_le_add h1 h2)
      _ ≤ ((n + 1 : ℕ) : ℝ) * B ^ (n + 1) * δ := by
          push_cast
          rw [pow_succ] at h3 ⊢
          nlinarith

/-- `|∏_r u_r^{t_r} − ∏_r v_r^{t_r}| ≤ (∑ t) B^{∑ t} δ`. -/
private theorem claimT_prodpow_sub {ι : Type*} (s : Finset ι) (u v : ι → ℂ) (t : ι → ℕ)
    {B δ : ℝ} (hB : 1 ≤ B) (hu : ∀ r, ‖u r‖ ≤ B) (hv : ∀ r, ‖v r‖ ≤ B)
    (huv : ∀ r, ‖u r - v r‖ ≤ δ) :
    ‖∏ r ∈ s, u r ^ t r - ∏ r ∈ s, v r ^ t r‖ ≤ (∑ r ∈ s, t r) * B ^ (∑ r ∈ s, t r) * δ := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hδ : ∀ r, 0 ≤ δ := fun r => (norm_nonneg _).trans (huv r)
  have hpv : ∀ (s' : Finset ι), ‖∏ r ∈ s', v r ^ t r‖ ≤ B ^ (∑ r ∈ s', t r) := by
    intro s'
    rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun r _ => by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hv r) _
  have hpu : ∀ (s' : Finset ι), ‖∏ r ∈ s', u r ^ t r‖ ≤ B ^ (∑ r ∈ s', t r) := by
    intro s'
    rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun r _ => by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hu r) _
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have e : u a ^ t a * ∏ r ∈ s, u r ^ t r - v a ^ t a * ∏ r ∈ s, v r ^ t r =
        (u a ^ t a - v a ^ t a) * ∏ r ∈ s, u r ^ t r +
          v a ^ t a * (∏ r ∈ s, u r ^ t r - ∏ r ∈ s, v r ^ t r) := by ring
    rw [e]
    have h1 := claimT_pow_sub_le hB (hu a) (hv a) (huv a) (t a)
    have h2 : ‖v a ^ t a‖ ≤ B ^ t a := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hv a) _
    set S := ∑ r ∈ s, t r
    have hδa := hδ a
    calc ‖(u a ^ t a - v a ^ t a) * ∏ r ∈ s, u r ^ t r +
          v a ^ t a * (∏ r ∈ s, u r ^ t r - ∏ r ∈ s, v r ^ t r)‖
        ≤ (t a * B ^ t a * δ) * B ^ S + B ^ t a * (S * B ^ S * δ) := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [norm_mul]; exact mul_le_mul h1 (hpu s) (norm_nonneg _) (by positivity)
          · rw [norm_mul]; exact mul_le_mul h2 ih (norm_nonneg _) (by positivity)
      _ = ((t a + S : ℕ) : ℝ) * B ^ (t a + S) * δ := by push_cast; rw [pow_add]; ring

/-- `x^{p−j} y^j ≤ x^p + y^p` for `x, y ≥ 0`, `j ≤ p`. -/
private theorem claimT_young {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) {p j : ℕ} (hj : j ≤ p) :
    x ^ (p - j) * y ^ j ≤ x ^ p + y ^ p := by
  have hxp := pow_nonneg hx p
  have hyp := pow_nonneg hy p
  rcases le_total x y with h | h
  · calc x ^ (p - j) * y ^ j ≤ y ^ (p - j) * y ^ j :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx h _) (pow_nonneg hy _)
      _ = y ^ p := by rw [← pow_add]; congr 1; omega
      _ ≤ x ^ p + y ^ p := by linarith
  · calc x ^ (p - j) * y ^ j ≤ x ^ (p - j) * x ^ j :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy h _) (pow_nonneg hx _)
      _ = x ^ p := by rw [← pow_add]; congr 1; omega
      _ ≤ x ^ p + y ^ p := by linarith

/-! ## The exponent count (cond_avg_pf) -/

/-- (cond_avg_pf) in the form used for (avg_step 1): with `R₀` the empty words with tag `0` and
`D = ∑_{n(w_r) ≥ 1} (2 − d_{X,r})_+`, `2 (p − |R₀|) ≤ d_X − [d_{X,i} = 3] + D`. -/
private theorem claimT_count {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r))
    (σs : ∀ r, Fin (ns r + 1) → Fin 3) (hn : ∑ r, ns r = 3)
    (hnz : ∀ r, tagNZ (ns r) (ws r) (σs r) = true) (hv : ∀ r, tagV (σs r) = 0) :
    2 * (p - (Finset.univ.filter fun r => ns r = 0 ∧ tagMu (σs r) = 0).card) ≤
      (dXof ns ws σs - if dXIof ns ws σs = 3 then 1 else 0) +
        ∑ r ∈ Finset.univ.filter (fun r => 1 ≤ ns r), (2 - tagDeg (ns r) (ws r) (σs r)) := by
  have hc := cond_avg_pf ns ws σs hn hnz hv
  set S1 := Finset.univ.filter fun r => 1 ≤ ns r with hS1
  set S0 := Finset.univ.filter fun r => ns r = 0 with hS0
  set R0 := Finset.univ.filter fun r => ns r = 0 ∧ tagMu (σs r) = 0 with hR0
  have hp : S1.card + S0.card = p := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin p)))
      (fun r => 1 ≤ ns r)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    have e : (Finset.univ.filter fun a => ¬1 ≤ ns a) = S0 := by
      ext r; simp only [hS0, Finset.mem_filter, Finset.mem_univ, true_and]; omega
    rw [e] at this
    exact this
  have hS0c : S0.card = R0.card + ∑ r ∈ S0, tagMu (σs r) := by
    have h1 : ∀ r ∈ S0, 1 = (if tagMu (σs r) = 0 then 1 else 0) + tagMu (σs r) := by
      intro r hr
      have hr0 : ns r = 0 := (Finset.mem_filter.1 hr).2
      have := claimT_tagMu_le (σs r)
      split_ifs with h <;> omega
    have h2 : ∑ r ∈ S0, (if tagMu (σs r) = 0 then 1 else 0) = R0.card := by
      rw [Finset.sum_boole, hR0, hS0, Finset.filter_filter]
      simp
    rw [Finset.card_eq_sum_ones, Finset.sum_congr rfl h1, Finset.sum_add_distrib, h2]
  omega

/-! ## The main part (A+_avg), (A+_avg_2), (A+_avg_3) -/

/-- The integrand with `G_μμ` replaced by `P = ∑_{k ≤ K} 𝒴_k Q_μ^k` (Gmumu_exp2). -/
private def claimT_FP (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (i : Fin M) (μ : Fin N) (Kx : ℕ) {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r))
    (σs : ∀ r, Fin (ns r + 1) → Fin 3) (cs : Fin p → Bool) : ℂ :=
  claimT_Gam ns σs cs
      (∑ k ∈ Finset.range (Kx + 1), calY z (Ymu Sig A z μ) Kx k * Qmu Sig A z μ ^ k) *
    ∏ r, claimT_H Sig A z i μ ns ws σs cs r

private theorem claimT_Ymu_updCol (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (μ : Fin N) (y : Fin M → ℝ) :
    Ymu Sig (updCol A μ y) z μ = Ymu Sig A z μ := by
  unfold Ymu; rw [Gmu_updCol]

/-- (A+_avg_2): for the empty word with tag `0`, the sum over `ν` does not involve the column,
and may be replaced by its average. -/
private theorem claimT_avg_R0 (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (i : Fin M) (μ : Fin N) (hN2 : 2 ≤ N) (n : ℕ) (hn : n = 0) (w : Word n)
    (σ : Fin (n + 1) → Fin 3) (hσ : tagMu σ = 0) (c : Bool) (y : Fin M → ℝ) :
    (N : ℂ)⁻¹ * ∑ ν ∈ Finset.univ.erase μ,
        conjIf c (tagScal Sig A z (eI (Sum.inr ν)) i μ n w σ) *
          conjIf c (((tagForms Sig A z (eI (Sum.inr ν)) i μ n w σ).map
            fun c' => linForm c' y).prod) =
      (N : ℂ)⁻¹ * ∑ ν ∈ Finset.univ.erase μ,
        (((N : ℂ) - 1)⁻¹ * ∑ ν' ∈ Finset.univ.erase μ,
          conjIf c (tagScal Sig A z (eI (Sum.inr ν')) i μ n w σ)) *
          conjIf c (((tagForms Sig A z (eI (Sum.inr ν)) i μ n w σ).map
            fun c' => linForm c' y).prod) := by
  have hF : ∀ ν : Fin N, tagForms Sig A z (eI (Sum.inr ν)) i μ n w σ = [] :=
    fun ν => (claimT_empty_zero Sig A z _ i μ n hn w σ hσ).1
  simp only [hF, List.map_nil, List.prod_nil, claimT_conjIf_one, mul_one]
  congr 1
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← mul_assoc]
  have h1 : ((N - 1 : ℕ) : ℂ) = (N : ℂ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
  have h2 : (N : ℂ) - 1 ≠ 0 := by
    rw [← h1]; exact_mod_cast (show N - 1 ≠ 0 by omega)
  rw [h1, mul_inv_cancel₀ h2, one_mul]

/-- `|(N − 1)⁻¹ ∑_{ν ≠ μ} A⁰(ν)| ≤ 2 |Â⁰|` for the empty word with tag `0`, `N ≥ 2`. -/
private theorem claimT_avg_R0_le (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (i : Fin M) (μ : Fin N) (hN2 : 2 ≤ N) (n : ℕ) (hn : n = 0) (w : Word n)
    (σ : Fin (n + 1) → Fin 3) (hσ : tagMu σ = 0) (c : Bool) :
    ‖((N : ℂ) - 1)⁻¹ * ∑ ν' ∈ Finset.univ.erase μ,
        conjIf c (tagScal Sig A z (eI (Sum.inr ν')) i μ n w σ)‖ ≤
      2 * ‖claimT_Shat Sig A z μ‖ := by
  have hS : ∀ ν : Fin N, tagScal Sig A z (eI (Sum.inr ν)) i μ n w σ =
      emptyScal Sig A z (eI (Sum.inr ν)) μ 0 :=
    fun ν => (claimT_empty_zero Sig A z _ i μ n hn w σ hσ).2
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have e : ∑ ν' ∈ Finset.univ.erase μ, emptyScal Sig A z (eI (Sum.inr ν')) μ 0 =
      (N : ℂ) * claimT_Shat Sig A z μ := by
    unfold claimT_Shat; rw [← mul_assoc, mul_inv_cancel₀ hN0, one_mul]
  simp only [hS]
  rw [← claimT_conjIf_sum, e, norm_mul, claimT_norm_conjIf, norm_mul, Complex.norm_natCast,
    norm_inv]
  have h1 : ‖(N : ℂ) - 1‖ = (N : ℝ) - 1 := by
    have : (N : ℂ) - 1 = (((N : ℝ) - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  rw [h1]
  have h2 : ((N : ℝ) - 1)⁻¹ * N ≤ 2 := by
    rw [inv_mul_le_iff₀ (by linarith)]; linarith
  have := norm_nonneg (claimT_Shat Sig A z μ)
  calc ((N : ℝ) - 1)⁻¹ * (N * ‖claimT_Shat Sig A z μ‖)
      = (((N : ℝ) - 1)⁻¹ * N) * ‖claimT_Shat Sig A z μ‖ := by ring
    _ ≤ 2 * ‖claimT_Shat Sig A z μ‖ := mul_le_mul_of_nonneg_right h2 this

/-- (avg_step 1) on the `X^{(μ)}`-measurable event, at a fixed `X^{(μ)}`: the column expectation
of the integrand with `G_μμ → P` is at most
`C₁ C_Y^{p+3} K_g^{(K+3)(p+3)} (2|Â⁰|)^{|R₀|} N^{−1/2} b^{2(p − |R₀|)}`. -/
private theorem claimT_point_main (C : ℕ → ℝ) (τ : ℝ) (hτ : 0 < τ) (p Kx : ℕ) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ (M N : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (i : Fin M) (μ : Fin N)
      (ρ : Fin M → Measure ℝ) [∀ j, IsProbabilityMeasure (ρ j)] (Kg b CY : ℝ),
      2 ≤ N → (M : ℝ) ≤ τ⁻¹ * N → 1 ≤ Kg → 0 ≤ b → b ≤ 1 → 1 ≤ CY →
      (∀ j, ∫ y, y ∂(ρ j) = 0) →
      (∀ j (n : ℕ), Integrable (fun y => |y| ^ n) (ρ j) ∧
        ∫ y, |Real.sqrt N * y| ^ n ∂(ρ j) ≤ C n) →
      (∀ ν, ν ≠ μ → ∀ j, ‖Gmu Sig A z μ (Sum.inr ν) (Sum.inl j)‖ ≤ b ∧
        ‖Gmu Sig A z μ (Sum.inl j) (Sum.inr ν)‖ ≤ b) →
      (∀ s t, ‖Gmu Sig A z μ s t‖ ≤ Kg) →
      (∑ j, ‖Gmu Sig A z μ (Sum.inl i) (Sum.inl j)‖ ≤ N * b) →
      (∑ j, ‖Gmu Sig A z μ (Sum.inl j) (Sum.inl i)‖ ≤ N * b) →
      (∑ j, ‖Gmu Sig A z μ (Sum.inl i) (Sum.inl j)‖ ^ 2 ≤ N * b ^ 2) →
      (∑ j, ‖Gmu Sig A z μ (Sum.inl j) (Sum.inl i)‖ ^ 2 ≤ N * b ^ 2) →
      (∀ k, ‖calY z (Ymu Sig A z μ) Kx k‖ ≤ CY) →
      ∀ (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r)) (σs : ∀ r, Fin (ns r + 1) → Fin 3)
        (cs : Fin p → Bool), ∑ r, ns r = 3 →
        (∀ r, tagNZ (ns r) (ws r) (σs r) = true) → (∀ r, tagV (σs r) = 0) →
        ‖∫ y, claimT_FP Sig (updCol A μ y) z i μ Kx ns ws σs cs ∂(Measure.pi ρ)‖ ≤
          C₁ * CY ^ (p + 3) * Kg ^ ((Kx + 3) * (p + 3)) *
            (2 * ‖claimT_Shat Sig A z μ‖) ^
              (Finset.univ.filter fun r => ns r = 0 ∧ tagMu (σs r) = 0).card *
            (N : ℝ) ^ (-(1 : ℝ) / 2) *
            b ^ (2 * (p - (Finset.univ.filter fun r => ns r = 0 ∧ tagMu (σs r) = 0).card)) := by
  obtain ⟨K', hK'0, hmain⟩ := claimT_main C τ hτ p Kx
  refine ⟨K' * ((Kx : ℝ) + 1) ^ (p + 3), by positivity, ?_⟩
  intro M N Sig A z i μ ρ _ Kg b CY hN2 hM hKg hb0 hb1 hCY hmean hρ hGν hK hS1 hS1' hS2 hS2' hY
    ns ws σs cs hns hnz hv
  have hN : 1 ≤ N := by omega
  set R0 := Finset.univ.filter fun r => ns r = 0 ∧ tagMu (σs r) = 0 with hR0
  set Sh := claimT_Shat Sig A z μ with hSh
  set a : Fin p → Fin N → ℂ := fun r ν =>
    if ns r = 0 ∧ tagMu (σs r) = 0 then ((N : ℂ) - 1)⁻¹ * ∑ ν' ∈ Finset.univ.erase μ,
      conjIf (cs r) (tagScal Sig A z (eI (Sum.inr ν')) i μ (ns r) (ws r) (σs r))
    else conjIf (cs r) (tagScal Sig A z (eI (Sum.inr ν)) i μ (ns r) (ws r) (σs r)) with ha
  set α : Fin p → ℝ := fun r =>
    if ns r = 0 ∧ tagMu (σs r) = 0 then 2 * ‖Sh‖
    else Kg ^ (ns r + 1) * b ^ (2 - tagDeg (ns r) (ws r) (σs r)) with hα
  have hα0 : ∀ r, 0 ≤ α r := fun r => by
    simp only [hα]; split_ifs <;> positivity
  have haα : ∀ r ν, ν ≠ μ → ‖a r ν‖ ≤ α r := by
    intro r ν hν
    simp only [ha, hα]
    split_ifs with h
    · exact claimT_avg_R0_le Sig A z i μ hN2 (ns r) h.1 (ws r) (σs r) h.2 (cs r)
    · rw [claimT_norm_conjIf]
      exact claimT_scal_bound Sig A z ν i μ hKg hb0 hb1 hK (hGν ν hν i).1 (hGν ν hν i).2
        (ns r) (ws r) (σs r) (hv r) h
  -- the integrand in the form of `claimT_main`
  have hrw : ∀ y, claimT_FP Sig (updCol A μ y) z i μ Kx ns ws σs cs =
      (∏ r, conjIf (cs r) (∑ k ∈ Finset.range (Kx + 1),
          calY z (Ymu Sig A z μ) Kx k * Qmu Sig (updCol A μ y) z μ ^ k) ^ tagMu (σs r)) *
        ∏ r, ((N : ℂ)⁻¹ * ∑ ν ∈ Finset.univ.erase μ, a r ν *
          conjIf (cs r) (((tagForms Sig A z (eI (Sum.inr ν)) i μ (ns r) (ws r)
            (σs r)).map fun c => linForm c y).prod)) := by
    intro y
    unfold claimT_FP claimT_Gam
    rw [claimT_Ymu_updCol]
    congr 1
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [claimT_H_updCol]
    by_cases h : ns r = 0 ∧ tagMu (σs r) = 0
    · simp only [ha, h, and_self, ite_true]
      exact claimT_avg_R0 Sig A z i μ hN2 (ns r) h.1 (ws r) (σs r) h.2 (cs r) y
    · simp only [ha, h, ite_false]
  have hmb := hmain M N Sig A z i μ ρ Kg b CY hN hM hKg hb0 hb1 hCY hmean hρ hGν
    (fun j j' => hK _ _) hS1 hS1' hS2 hS2' hY ns ws σs cs a α hns hnz hv hα0 haα
  rw [integral_congr_ae (ae_of_all _ hrw)]
  refine hmb.trans ?_
  -- the product of the `α_r`
  set D := ∑ r ∈ Finset.univ.filter (fun r => 1 ≤ ns r), (2 - tagDeg (ns r) (ws r) (σs r))
    with hD
  have hprod : ∏ r, α r ≤ (2 * ‖Sh‖) ^ R0.card * (Kg ^ (p + 3) * b ^ D) := by
    simp only [hα]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      Finset.prod_pow_eq_pow_sum]
    refine mul_le_mul_of_nonneg_left (mul_le_mul ?_ (le_of_eq ?_) (by positivity)
      (by positivity)) (by positivity)
    · refine pow_le_pow_right₀ hKg ?_
      calc ∑ r ∈ Finset.univ.filter (fun r => ¬(ns r = 0 ∧ tagMu (σs r) = 0)), (ns r + 1)
          ≤ ∑ r, (ns r + 1) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun _ _ _ => Nat.zero_le _
        _ = p + 3 := by rw [Finset.sum_add_distrib, hns]; simp; ring
    · rw [hD]
      congr 1
      symm
      refine Finset.sum_subset (fun r hr => ?_) fun r hr hr' => ?_
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
        omega
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and] at hr hr'
        have hn0 : ns r = 0 := by omega
        have hm : tagMu (σs r) ≠ 0 := hr hn0
        rw [claimT_empty_deg (ns r) hn0 (ws r) (σs r) hm (hv r), Nat.sub_self]
  have hcount : 2 * (p - R0.card) ≤
      (dXof ns ws σs - if dXIof ns ws σs = 3 then 1 else 0) + D :=
    claimT_count ns ws σs hns hnz hv
  have hbexp : b ^ D * b ^ (dXof ns ws σs - if dXIof ns ws σs = 3 then 1 else 0) ≤
      b ^ (2 * (p - R0.card)) := by
    rw [← pow_add]; exact pow_le_pow_of_le_one hb0 hb1 (by omega)
  have hN0 : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hCY0 : 0 ≤ CY := zero_le_one.trans hCY
  have hKg0 : 0 ≤ Kg := zero_le_one.trans hKg
  calc K' * (((Kx : ℝ) + 1) * CY) ^ (p + 3) * Kg ^ ((Kx + 2) * (p + 3)) * (∏ r, α r) *
        (N : ℝ) ^ (-(1 : ℝ) / 2) * b ^ (dXof ns ws σs - if dXIof ns ws σs = 3 then 1 else 0)
      ≤ K' * (((Kx : ℝ) + 1) * CY) ^ (p + 3) * Kg ^ ((Kx + 2) * (p + 3)) *
          ((2 * ‖Sh‖) ^ R0.card * (Kg ^ (p + 3) * b ^ D)) *
          (N : ℝ) ^ (-(1 : ℝ) / 2) * b ^ (dXof ns ws σs - if dXIof ns ws σs = 3 then 1 else 0) := by
        gcongr
    _ = K' * ((Kx : ℝ) + 1) ^ (p + 3) * CY ^ (p + 3) * (Kg ^ ((Kx + 2) * (p + 3)) * Kg ^ (p + 3)) *
          (2 * ‖Sh‖) ^ R0.card * (N : ℝ) ^ (-(1 : ℝ) / 2) *
          (b ^ D * b ^ (dXof ns ws σs - if dXIof ns ws σs = 3 then 1 else 0)) := by
        rw [mul_pow]; ring
    _ ≤ K' * ((Kx : ℝ) + 1) ^ (p + 3) * CY ^ (p + 3) * Kg ^ ((Kx + 3) * (p + 3)) *
          (2 * ‖Sh‖) ^ R0.card * (N : ℝ) ^ (-(1 : ℝ) / 2) * b ^ (2 * (p - R0.card)) := by
        rw [← pow_add, show (Kx + 2) * (p + 3) + (p + 3) = (Kx + 3) * (p + 3) by ring]
        gcongr

/-! ## The remainder of `G_μμ → P` on the a priori event -/

/-- `|(−z − Y)⁻¹| ≤ 2 C_m` and `|Y| ≤ |z| + C_m + (2C_m)⁻¹` when `|Y − (−z − m⁻¹)| ≤ ε ≤ (2C_m)⁻¹`
and `C_m⁻¹ ≤ |m| ≤ C_m`. -/
private theorem claimT_inv_bound {z Y m : ℂ} {Cm ε : ℝ} (hCm : 0 < Cm) (hm1 : Cm⁻¹ ≤ ‖m‖)
    (hm2 : ‖m‖ ≤ Cm) (hY : ‖Y - (-z - m⁻¹)‖ ≤ ε) (hε : ε ≤ (2 * Cm)⁻¹) :
    ‖(-z - Y)⁻¹‖ ≤ 2 * Cm ∧ ‖Y‖ ≤ ‖z‖ + Cm + (2 * Cm)⁻¹ := by
  have hm0 : 0 < ‖m‖ := lt_of_lt_of_le (inv_pos.2 hCm) hm1
  have hmi1 : Cm⁻¹ ≤ ‖m⁻¹‖ := by rw [norm_inv]; exact inv_anti₀ hm0 hm2
  have hmi2 : ‖m⁻¹‖ ≤ Cm := by
    rw [norm_inv]; calc ‖m‖⁻¹ ≤ (Cm⁻¹)⁻¹ := inv_anti₀ (inv_pos.2 hCm) hm1
      _ = Cm := inv_inv Cm
  have e : -z - Y = m⁻¹ - (Y - (-z - m⁻¹)) := by ring
  have hlow : (2 * Cm)⁻¹ ≤ ‖-z - Y‖ := by
    rw [e]
    have := norm_sub_norm_le m⁻¹ (Y - (-z - m⁻¹))
    have h2 : (2 * Cm)⁻¹ = Cm⁻¹ - (2 * Cm)⁻¹ := by field_simp; ring
    linarith
  constructor
  · rw [norm_inv]
    calc ‖-z - Y‖⁻¹ ≤ ((2 * Cm)⁻¹)⁻¹ := inv_anti₀ (by positivity) hlow
      _ = 2 * Cm := inv_inv _
  · have e2 : Y = (-z - m⁻¹) + (Y - (-z - m⁻¹)) := by ring
    rw [e2]
    calc ‖(-z - m⁻¹) + (Y - (-z - m⁻¹))‖ ≤ ‖-z - m⁻¹‖ + ε := (norm_add_le _ _).trans
          (add_le_add le_rfl hY)
      _ ≤ (‖z‖ + ‖m⁻¹‖) + ε := by
          gcongr; exact (norm_sub_le _ _).trans (by rw [norm_neg])
      _ ≤ ‖z‖ + Cm + (2 * Cm)⁻¹ := by linarith

/-- (Gmumu_exp2) on the a priori event: with `P = ∑_{k ≤ K} 𝒴_k Q_μ^k`, `|G_μμ| ≤ C_m + 1`,
`|P| ≤ 2(C_m + 1)` and `|G_μμ − P| ≤ (C_m + 1) θ^{K+1}`, `θ = 2C_m (2C_m² b + ε) ≤ 1`. -/
private theorem claimT_gP {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (μ : Fin N) (Kx : ℕ)
    {b₀ Cm ε : ℝ} (hCm : 0 < Cm) (hG : ∀ s t, ‖G Sig A z s t - PiZ N Sig z s t‖ ≤ b₀)
    (hm1 : Cm⁻¹ ≤ ‖mFun N (specOf Sig) z‖) (hm2 : ‖mFun N (specOf Sig) z‖ ≤ Cm)
    (hb₀1 : b₀ ≤ 1) (hb₀ : b₀ ≤ (2 * Cm)⁻¹)
    (hY : ‖Ymu Sig A z μ - (-z - (mFun N (specOf Sig) z)⁻¹)‖ ≤ ε) (hε : ε ≤ (2 * Cm)⁻¹)
    (hθ : 2 * Cm * (2 * Cm ^ 2 * b₀ + ε) ≤ 1) :
    ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖ ≤ Cm + 1 ∧
    ‖∑ k ∈ Finset.range (Kx + 1), calY z (Ymu Sig A z μ) Kx k * Qmu Sig A z μ ^ k‖ ≤
      2 * (Cm + 1) ∧
    ‖G Sig A z (Sum.inr μ) (Sum.inr μ) -
        ∑ k ∈ Finset.range (Kx + 1), calY z (Ymu Sig A z μ) Kx k * Qmu Sig A z μ ^ k‖ ≤
      (Cm + 1) * (2 * Cm * (2 * Cm ^ 2 * b₀ + ε)) ^ (Kx + 1) := by
  set g := G Sig A z (Sum.inr μ) (Sum.inr μ) with hg
  set m := mFun N (specOf Sig) z with hm
  set Y := Ymu Sig A z μ with hYdef
  set Q := Qmu Sig A z μ with hQ
  have hb0 : 0 ≤ b₀ := (norm_nonneg _).trans (hG (Sum.inr μ) (Sum.inr μ))
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hY
  have hgm : ‖g - m‖ ≤ b₀ := by
    have := hG (Sum.inr μ) (Sum.inr μ)
    simpa [PiZ, piMat, hg, hm] using this
  have hm0 : 0 < ‖m‖ := lt_of_lt_of_le (inv_pos.2 hCm) hm1
  have hgle : ‖g‖ ≤ Cm + 1 := by
    have := norm_le_norm_add_norm_sub' g m
    linarith [norm_sub_rev g m]
  have hglow : (2 * Cm)⁻¹ ≤ ‖g‖ := by
    have := norm_sub_norm_le m g
    have h2 : (2 * Cm)⁻¹ = Cm⁻¹ - (2 * Cm)⁻¹ := by field_simp; ring
    rw [norm_sub_rev] at this
    linarith
  have hg0 : 0 < ‖g‖ := lt_of_lt_of_le (by positivity) hglow
  have hgne : g ≠ 0 := norm_pos_iff.1 hg0
  have hmne : m ≠ 0 := norm_pos_iff.1 hm0
  -- `Q = −z − 1/G_μμ` (Gii)
  have hii := Gii hSig A hz μ
  have hQe : Q = -z - g⁻¹ := by
    have : ((Xhat A)ᵀ * G1 Sig A z (Sum.inr μ) * Xhat A) (Sum.inr μ) (Sum.inr μ) = Q := rfl
    rw [this, one_div] at hii
    rw [← hg] at hii
    linear_combination hii
  obtain ⟨hinv, -⟩ := claimT_inv_bound hCm hm1 hm2 hY hε
  have hQY : ‖Q - Y‖ ≤ 2 * Cm ^ 2 * b₀ + ε := by
    have e : Q - Y = (m⁻¹ - g⁻¹) - (Y - (-z - m⁻¹)) := by rw [hQe]; ring
    rw [e]
    have h1 : ‖m⁻¹ - g⁻¹‖ ≤ 2 * Cm ^ 2 * b₀ := by
      have e1 : m⁻¹ - g⁻¹ = (g - m) * (g⁻¹ * m⁻¹) := by field_simp
      rw [e1, norm_mul, norm_mul, norm_inv, norm_inv]
      have hgi : ‖g‖⁻¹ ≤ 2 * Cm := by
        calc ‖g‖⁻¹ ≤ ((2 * Cm)⁻¹)⁻¹ := inv_anti₀ (by positivity) hglow
          _ = 2 * Cm := inv_inv _
      have hmi : ‖m‖⁻¹ ≤ Cm := by
        calc ‖m‖⁻¹ ≤ (Cm⁻¹)⁻¹ := inv_anti₀ (inv_pos.2 hCm) hm1
          _ = Cm := inv_inv _
      calc ‖g - m‖ * (‖g‖⁻¹ * ‖m‖⁻¹) ≤ b₀ * (2 * Cm * Cm) :=
            mul_le_mul hgm (mul_le_mul hgi hmi (by positivity) (by positivity)) (by positivity) hb0
        _ = 2 * Cm ^ 2 * b₀ := by ring
    exact (norm_sub_le _ _).trans (add_le_add h1 hY)
  set θ := 2 * Cm * (2 * Cm ^ 2 * b₀ + ε) with hθdef
  have hζ : ‖(Q - Y) * (-z - Y)⁻¹‖ ≤ θ := by
    rw [norm_mul, hθdef]
    calc ‖Q - Y‖ * ‖(-z - Y)⁻¹‖ ≤ (2 * Cm ^ 2 * b₀ + ε) * (2 * Cm) :=
          mul_le_mul hQY hinv (norm_nonneg _) (by positivity)
      _ = 2 * Cm * (2 * Cm ^ 2 * b₀ + ε) := by ring
  have hθ0 : 0 ≤ θ := by positivity
  have hexp := gmumu_exp hSig A hz μ Kx (claimT_Y_ne hSig hz A μ)
  rw [← hg, ← hYdef, ← hQ] at hexp
  set P := ∑ k ∈ Finset.range (Kx + 1), calY z Y Kx k * Q ^ k with hP
  have hgP : g - P = g * ((Q - Y) * (-z - Y)⁻¹) ^ (Kx + 1) := by
    conv_lhs => rw [hexp]
    ring
  have hpow : ‖((Q - Y) * (-z - Y)⁻¹) ^ (Kx + 1)‖ ≤ θ ^ (Kx + 1) := by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hζ _
  have hrem : ‖g - P‖ ≤ (Cm + 1) * θ ^ (Kx + 1) := by
    rw [hgP, norm_mul]
    exact mul_le_mul hgle hpow (norm_nonneg _) (by linarith)
  refine ⟨hgle, ?_, hrem⟩
  have hθp : θ ^ (Kx + 1) ≤ 1 := pow_le_one₀ hθ0 hθ
  have := norm_sub_norm_le g P
  have h3 : ‖P‖ ≤ ‖g‖ + ‖g - P‖ := by
    have := norm_sub_le g (g - P)
    simpa using this
  nlinarith

private theorem claimT_conjIf_sub (c : Bool) (x y : ℂ) :
    conjIf c x - conjIf c y = conjIf c (x - y) := by
  cases c <;> simp [conjIf]

/-- `∏_r |H_r| ≤ |Â⁰|^{|R₀|} (K⁴ b²)^{p − |R₀|}` on the a priori event. -/
private theorem claimT_prodH_event {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (i : Fin M) (μ : Fin N)
    {b₀ L Kg b : ℝ} (hG : ∀ s t, ‖G Sig A z s t - PiZ N Sig z s t‖ ≤ b₀)
    (hμ : 1 ≤ L * ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖) (hKg : 1 ≤ Kg) (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1) (hLb : L * b₀ ≤ b) (hK : ∀ s t, ‖Gmu Sig A z μ s t‖ ≤ Kg)
    (hGν : ∀ ν, ν ≠ μ → ∀ j, ‖Gmu Sig A z μ (Sum.inr ν) (Sum.inl j)‖ ≤ b ∧
      ‖Gmu Sig A z μ (Sum.inl j) (Sum.inr ν)‖ ≤ b)
    {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r)) (σs : ∀ r, Fin (ns r + 1) → Fin 3)
    (cs : Fin p → Bool) (hns : ∑ r, ns r = 3) (hv : ∀ r, tagV (σs r) = 0) :
    ∏ r, ‖claimT_H Sig A z i μ ns ws σs cs r‖ ≤
      ‖claimT_Shat Sig A z μ‖ ^ (Finset.univ.filter fun r => ns r = 0 ∧ tagMu (σs r) = 0).card *
        (Kg ^ 4 * b ^ 2) ^
          (p - (Finset.univ.filter fun r => ns r = 0 ∧ tagMu (σs r) = 0).card) := by
  have hn3 : ∀ r, ns r ≤ 3 := fun r =>
    hns ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
  have hb : ∀ r, ‖claimT_H Sig A z i μ ns ws σs cs r‖ ≤
      if ns r = 0 ∧ tagMu (σs r) = 0 then ‖claimT_Shat Sig A z μ‖ else Kg ^ 4 * b ^ 2 := by
    intro r
    have h := claimT_H_event hSig A hz i μ hG hμ hKg hb0 hb1 hLb hK hGν ns ws σs cs r (hn3 r) (hv r)
    split_ifs with h0
    · rw [h.1 h0, claimT_norm_conjIf]
    · exact h.2 h0
  calc ∏ r, ‖claimT_H Sig A z i μ ns ws σs cs r‖
      ≤ ∏ r, (if ns r = 0 ∧ tagMu (σs r) = 0 then ‖claimT_Shat Sig A z μ‖ else Kg ^ 4 * b ^ 2) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun r _ => hb r
    _ = _ := by
        rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
        congr 2
        have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin p)))
          (fun r => ns r = 0 ∧ tagMu (σs r) = 0)
        simp only [Finset.card_univ, Fintype.card_fin] at this
        omega

/-- The remainder of `G_μμ → P` at a point of the a priori event:
`|F − F_P| ≤ (p + 3) B^{p+3} |G_μμ − P| ∏_r |H_r|`. -/
private theorem claimT_rem_point (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (i : Fin M) (μ : Fin N) (Kx : ℕ) {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r))
    (σs : ∀ r, Fin (ns r + 1) → Fin 3) (cs : Fin p → Bool) (hns : ∑ r, ns r = 3) {B : ℝ}
    (hB : 1 ≤ B) (hg : ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖ ≤ B)
    (hP : ‖∑ k ∈ Finset.range (Kx + 1), calY z (Ymu Sig A z μ) Kx k * Qmu Sig A z μ ^ k‖ ≤ B) :
    ‖claimT_F Sig A z i μ ns ws σs cs - claimT_FP Sig A z i μ Kx ns ws σs cs‖ ≤
      (p + 3) * B ^ (p + 3) * ‖G Sig A z (Sum.inr μ) (Sum.inr μ) -
        ∑ k ∈ Finset.range (Kx + 1), calY z (Ymu Sig A z μ) Kx k * Qmu Sig A z μ ^ k‖ *
      ∏ r, ‖claimT_H Sig A z i μ ns ws σs cs r‖ := by
  rw [claimT_F_eq, claimT_FP, ← sub_mul, norm_mul, norm_prod]
  refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  unfold claimT_Gam
  set g := G Sig A z (Sum.inr μ) (Sum.inr μ)
  set P := ∑ k ∈ Finset.range (Kx + 1), calY z (Ymu Sig A z μ) Kx k * Qmu Sig A z μ ^ k
  have h := claimT_prodpow_sub Finset.univ (fun r => conjIf (cs r) g) (fun r => conjIf (cs r) P)
    (fun r => tagMu (σs r)) hB (fun r => by rw [claimT_norm_conjIf]; exact hg)
    (fun r => by rw [claimT_norm_conjIf]; exact hP)
    (fun r => by rw [claimT_conjIf_sub, claimT_norm_conjIf])
  refine h.trans ?_
  have hd : ∑ r, tagMu (σs r) ≤ p + 3 := by
    calc ∑ r, tagMu (σs r) ≤ ∑ r, (ns r + 1) := Finset.sum_le_sum fun r _ => claimT_tagMu_le _
      _ = p + 3 := by rw [Finset.sum_add_distrib, hns]; simp; ring
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  refine mul_le_mul_of_nonneg_right (mul_le_mul ?_ (pow_le_pow_right₀ hB hd) (by positivity)
    (by positivity)) (norm_nonneg _)
  exact_mod_cast hd

/-! ## Rough bounds -/

/-- `‖A‖_F² = ∑_{jν} A_{jν}²`. -/
private def claimT_sq (A : Matrix (Fin M) (Fin N) ℝ) : ℝ := ∑ α : Fin M × Fin N, A α.1 α.2 ^ 2

private theorem claimT_sq_nonneg (A : Matrix (Fin M) (Fin N) ℝ) : 0 ≤ claimT_sq A :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The moment constant `2^q (1 + τ^{−q}) (1 + C'_{2q})`. -/
private def claimT_KS (τ : ℝ) (C : ℕ → ℝ) (q : ℕ) : ℝ :=
  2 ^ q * (1 + τ⁻¹ ^ q) * (1 + max (C (2 * q)) 0)

/-- `E (1 + ‖X‖_F²)^q ≤ 2^q (1 + τ^{−q}) (1 + C'_{2q}) N^q` for `M ≤ τ⁻¹ N`, from
(moments of X-1). -/
private theorem claimT_moment {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {τ : ℝ} (hτ : 0 < τ) {C : ℕ → ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ}
    (hX : EntryAssumption C X) (hN : 1 ≤ N) (hM : (M : ℝ) ≤ τ⁻¹ * N) (q : ℕ) :
    Integrable (fun ω => (1 + claimT_sq (X ω)) ^ q) ∧
      ∫ ω, (1 + claimT_sq (X ω)) ^ q ≤ claimT_KS τ C q * (N : ℝ) ^ q := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · refine ⟨by simp, ?_⟩
    simp only [pow_zero, integral_const, probReal_univ, smul_eq_mul, mul_one]
    unfold claimT_KS
    have : 0 ≤ max (C (2 * 0)) 0 := le_max_right _ _
    simp only [pow_zero, one_mul]
    nlinarith
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  set C' := max (C (2 * (n + 1))) 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hpow : ∀ t : ℝ, (t ^ 2) ^ (n + 1) =
      ((N : ℝ) ^ (n + 1))⁻¹ * |Real.sqrt N * t| ^ (2 * (n + 1)) := by
    intro t
    rw [pow_mul, sq_abs, mul_pow, Real.sq_sqrt hNp.le, mul_pow, ← mul_assoc,
      inv_mul_cancel₀ (pow_pos hNp _).ne', one_mul]
  have hXi : ∀ α : Fin M × Fin N, Integrable fun ω => (X ω α.1 α.2 ^ 2) ^ (n + 1) := by
    intro α
    simp_rw [hpow]
    exact (hX.integrable_moment (2 * (n + 1)) α.1 α.2).const_mul _
  have hXle : ∀ α : Fin M × Fin N,
      ∫ ω, (X ω α.1 α.2 ^ 2) ^ (n + 1) ≤ ((N : ℝ) ^ (n + 1))⁻¹ * C' := by
    intro α
    simp_rw [hpow]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left ((hX.moment (2 * (n + 1)) α.1 α.2).trans (le_max_left _ _))
      (by positivity)
  set cd : ℝ := ((Finset.univ : Finset (Fin M × Fin N)).card : ℝ) with hcd
  have hcdMN : cd = (M : ℝ) * N := by
    rw [hcd, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    push_cast; ring
  have hcd0 : 0 ≤ cd := by rw [hcdMN]; positivity
  have hSi : Integrable fun ω => ∑ α : Fin M × Fin N, (X ω α.1 α.2 ^ 2) ^ (n + 1) :=
    integrable_finsetSum _ fun α _ => hXi α
  have hSi' : Integrable fun ω => cd ^ n * ∑ α : Fin M × Fin N, (X ω α.1 α.2 ^ 2) ^ (n + 1) :=
    hSi.const_mul _
  have h1i : Integrable fun ω => 1 + cd ^ n * ∑ α : Fin M × Fin N, (X ω α.1 α.2 ^ 2) ^ (n + 1) :=
    (integrable_const _).add hSi'
  set g : Ω → ℝ := fun ω => 2 ^ n * (1 + cd ^ n * ∑ α : Fin M × Fin N,
      (X ω α.1 α.2 ^ 2) ^ (n + 1)) with hg
  have hgi : Integrable g := h1i.const_mul _
  have hle : ∀ ω, (1 + claimT_sq (X ω)) ^ (n + 1) ≤ g ω := by
    intro ω
    have h1 := add_pow_le zero_le_one (claimT_sq_nonneg (X ω)) (n + 1)
    have h2 : claimT_sq (X ω) ^ (n + 1) ≤
        cd ^ n * ∑ α : Fin M × Fin N, (X ω α.1 α.2 ^ 2) ^ (n + 1) :=
      pow_sum_le_card_mul_sum_pow (fun _ _ => sq_nonneg _) n
    calc _ ≤ _ := h1
      _ ≤ g ω := by
          simp only [hg, one_pow, Nat.add_sub_cancel]
          gcongr
  have hmeas : Measurable fun ω => (1 + claimT_sq (X ω)) ^ (n + 1) := by
    unfold claimT_sq
    exact (measurable_const.add (Finset.measurable_sum _ fun α _ =>
      (hX.measurable α.1 α.2).pow_const 2)).pow_const _
  have hWi : Integrable fun ω => (1 + claimT_sq (X ω)) ^ (n + 1) :=
    hgi.mono' hmeas.aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (by have := claimT_sq_nonneg (X ω); positivity)]; exact hle ω)
  refine ⟨hWi, ?_⟩
  have hgval : ∫ ω, g ω = 2 ^ n * (1 + cd ^ n * ∑ α : Fin M × Fin N,
      ∫ ω, (X ω α.1 α.2 ^ 2) ^ (n + 1)) := by
    rw [hg, integral_const_mul, integral_add (integrable_const _) hSi',
      integral_const_mul, integral_finsetSum _ fun α _ => hXi α]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hsum : ∑ α : Fin M × Fin N, ∫ ω, (X ω α.1 α.2 ^ 2) ^ (n + 1) ≤
      cd * (((N : ℝ) ^ (n + 1))⁻¹ * C') := by
    calc _ ≤ ∑ _α : Fin M × Fin N, ((N : ℝ) ^ (n + 1))⁻¹ * C' :=
          Finset.sum_le_sum fun α _ => hXle α
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hM1 : cd ^ n * (cd * (((N : ℝ) ^ (n + 1))⁻¹ * C')) = (M : ℝ) ^ (n + 1) * C' := by
    rw [hcdMN]
    field_simp
    ring
  have hM2 : (M : ℝ) ^ (n + 1) ≤ τ⁻¹ ^ (n + 1) * (N : ℝ) ^ (n + 1) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) hM _
  have hNn : (1 : ℝ) ≤ (N : ℝ) ^ (n + 1) := one_le_pow₀ hN1r
  have hτn : 0 ≤ τ⁻¹ ^ (n + 1) := by positivity
  calc ∫ ω, (1 + claimT_sq (X ω)) ^ (n + 1) ≤ ∫ ω, g ω := integral_mono hWi hgi hle
    _ ≤ 2 ^ n * (1 + τ⁻¹ ^ (n + 1) * (N : ℝ) ^ (n + 1) * C') := by
        rw [hgval]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have := mul_le_mul_of_nonneg_left hsum (pow_nonneg hcd0 n)
        rw [hM1] at this
        have h5 := mul_le_mul_of_nonneg_right hM2 hC'0
        linarith
    _ ≤ claimT_KS τ C (n + 1) * (N : ℝ) ^ (n + 1) := by
        unfold claimT_KS
        rw [← hC']
        set P := (N : ℝ) ^ (n + 1)
        set T := τ⁻¹ ^ (n + 1)
        have h2n : (0 : ℝ) ≤ 2 ^ n := by positivity
        have hA : 1 + T * P * C' ≤ 2 * ((1 + T) * (1 + C') * P) := by
          nlinarith [mul_nonneg hτn hC'0, mul_nonneg (mul_nonneg hτn hC'0) (sub_nonneg.2 hNn)]
        calc 2 ^ n * (1 + T * P * C') ≤ 2 ^ n * (2 * ((1 + T) * (1 + C') * P)) :=
              mul_le_mul_of_nonneg_left hA h2n
          _ = 2 ^ (n + 1) * (1 + T) * (1 + C') * P := by ring

/-- `V = ∑_j |X_{jμ}|`, the `ℓ¹` norm of the column `μ`. -/
private def claimT_V (A : Matrix (Fin M) (Fin N) ℝ) (μ : Fin N) : ℝ := ∑ j, |A j μ|

private theorem claimT_V_nonneg (A : Matrix (Fin M) (Fin N) ℝ) (μ : Fin N) : 0 ≤ claimT_V A μ :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- `1 + V ≤ (1 + M)(1 + ‖X‖_F²)`. -/
private theorem claimT_V_le (A : Matrix (Fin M) (Fin N) ℝ) (μ : Fin N) :
    1 + claimT_V A μ ≤ (1 + M) * (1 + claimT_sq A) := by
  have h1 : claimT_V A μ ≤ ∑ j : Fin M, (1 + A j μ ^ 2) :=
    Finset.sum_le_sum fun j _ => by nlinarith [sq_abs (A j μ), abs_nonneg (A j μ)]
  have h2 : ∑ j : Fin M, A j μ ^ 2 ≤ claimT_sq A := by
    unfold claimT_sq
    rw [Fintype.sum_prod_type]
    exact Finset.sum_le_sum fun j _ => Finset.single_le_sum (fun ν _ => sq_nonneg (A j ν))
      (Finset.mem_univ μ)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at h1
  have := claimT_sq_nonneg A
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  nlinarith

/-- `|⟨c, X_μ⟩| ≤ R V` for the coefficient vectors of `A⁺(w, σ)` when `|G^{(μ)}_{st}| ≤ R`. -/
private theorem claimT_form_rough (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) {ν μ : Fin N} (hν : ν ≠ μ) (i : Fin M) {R : ℝ}
    (hR : ∀ s t, ‖Gmu Sig A z μ s t‖ ≤ R) (n : ℕ) (w : Word n) (σ : Fin (n + 1) → Fin 3)
    (hv : tagV σ = 0) :
    ‖((tagForms Sig A z (eI (Sum.inr ν)) i μ n w σ).map
        fun c => linForm c fun j => A j μ).prod‖ ≤ (R * claimT_V A μ) ^ tagDeg n w σ := by
  rw [← tagForms_length Sig A z (eI (Sum.inr ν)) i μ]
  refine claimT_list_prod_le _ _ fun c hc => ?_
  obtain ⟨s, -, hc'⟩ := claimT_tagForms_mem Sig A z hν i n w σ hv c hc
  have key : ∀ f : Fin M → ℂ, (∀ j, ‖f j‖ ≤ R) →
      ‖∑ j, f j * ((A j μ : ℝ) : ℂ)‖ ≤ R * claimT_V A μ := by
    intro f hf
    unfold claimT_V
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hf j) (abs_nonneg _)
  rcases hc' with rfl | rfl
  · rw [claimT_linForm_colC]; exact key _ fun j => hR _ _
  · rw [claimT_linForm_rowC]; exact key _ fun j => hR _ _

/-- The rough bound `|A_{e_ν, i, μ}(w, σ)| ≤ W^{3(n+1)}`, `W = (R + K')(1 + R)(1 + V)`, when
`|G^{(μ)}_{st}| ≤ R`, `|Π_{st}| ≤ K'`. -/
private theorem claimT_tagA_rough (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) {ν μ : Fin N} (hν : ν ≠ μ) (i : Fin M) {R K' : ℝ}
    (hR1 : 1 ≤ R) (hK'0 : 0 ≤ K') (hR : ∀ s t, ‖Gmu Sig A z μ s t‖ ≤ R)
    (hK' : ∀ s t, ‖PiZ N Sig z s t‖ ≤ K') (n : ℕ) (w : Word n) (σ : Fin (n + 1) → Fin 3)
    (hv : tagV σ = 0) :
    ‖tagA Sig A z (eI (Sum.inr ν)) i μ n w σ‖ ≤
      ((R + K') * (1 + R) * (1 + claimT_V A μ)) ^ (3 * (n + 1)) := by
  have hV := claimT_V_nonneg A μ
  set W := (R + K') * (1 + R) * (1 + claimT_V A μ) with hW
  have hRK : 1 ≤ R + K' := by linarith
  have hW1 : 1 ≤ W := by
    have h2 : 1 ≤ 1 + R := by linarith
    have h3 : 1 ≤ 1 + claimT_V A μ := by linarith
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ W := by rw [hW]; gcongr
  rw [tagA_eq_scal_mul, norm_mul]
  have hs := claimT_tagScal_rough Sig A z hν i hR1 hK'0 hR hK' n w σ
  have hf := claimT_form_rough Sig A z hν i hR n w σ hv
  have hd := claimT_tagDeg_le n w σ
  have hRV : R * claimT_V A μ ≤ W := by
    have : R * claimT_V A μ ≤ (1 + R) * (1 + claimT_V A μ) := by nlinarith
    calc R * claimT_V A μ ≤ (1 + R) * (1 + claimT_V A μ) := this
      _ ≤ (R + K') * ((1 + R) * (1 + claimT_V A μ)) :=
          le_mul_of_one_le_left (by positivity) hRK
      _ = W := by rw [hW]; ring
  have hRW : R + K' ≤ W := by
    rw [hW, mul_assoc]
    refine le_mul_of_one_le_right (by linarith) ?_
    nlinarith
  have h1 : (R + K') ^ (n + 1) ≤ W ^ (n + 1) := pow_le_pow_left₀ (by linarith) hRW _
  have h2 : (R * claimT_V A μ) ^ tagDeg n w σ ≤ W ^ (2 * (n + 1)) :=
    (pow_le_pow_left₀ (by positivity) hRV _).trans (pow_le_pow_right₀ hW1 hd)
  calc ‖tagScal Sig A z (eI (Sum.inr ν)) i μ n w σ‖ *
        ‖((tagForms Sig A z (eI (Sum.inr ν)) i μ n w σ).map fun c => linForm c fun j => A j μ).prod‖
      ≤ W ^ (n + 1) * W ^ (2 * (n + 1)) :=
        mul_le_mul (hs.trans h1) (hf.trans h2) (norm_nonneg _) (by positivity)
    _ = W ^ (3 * (n + 1)) := by rw [← pow_add]; ring_nf

/-- `|Γ(x)| ≤ B^{p+3}` for `|x| ≤ B`, `B ≥ 1`, `∑_r n(w_r) = 3`. -/
private theorem claimT_Gam_le {p : ℕ} (ns : Fin p → ℕ) (σs : ∀ r, Fin (ns r + 1) → Fin 3)
    (cs : Fin p → Bool) (hns : ∑ r, ns r = 3) {x : ℂ} {B : ℝ} (hB : 1 ≤ B) (hx : ‖x‖ ≤ B) :
    ‖claimT_Gam ns σs cs x‖ ≤ B ^ (p + 3) := by
  unfold claimT_Gam
  rw [norm_prod]
  calc ∏ r, ‖conjIf (cs r) x ^ tagMu (σs r)‖ ≤ ∏ r, B ^ tagMu (σs r) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun r _ => by
          rw [norm_pow, claimT_norm_conjIf]; exact pow_le_pow_left₀ (norm_nonneg _) hx _
    _ = B ^ (∑ r, tagMu (σs r)) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ B ^ (p + 3) := by
        refine pow_le_pow_right₀ hB ?_
        calc ∑ r, tagMu (σs r) ≤ ∑ r, (ns r + 1) := Finset.sum_le_sum fun r _ => claimT_tagMu_le _
          _ = p + 3 := by rw [Finset.sum_add_distrib, hns]; simp; ring

/-- `∏_r |H_r| ≤ W^{3(p+3)}` from the rough bound of the tagged words. -/
private theorem claimT_prodH_rough (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (i : Fin M) (μ : Fin N) {R K' : ℝ}
    (hR1 : 1 ≤ R) (hK'0 : 0 ≤ K') (hR : ∀ s t, ‖Gmu Sig A z μ s t‖ ≤ R)
    (hK' : ∀ s t, ‖PiZ N Sig z s t‖ ≤ K') {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r))
    (σs : ∀ r, Fin (ns r + 1) → Fin 3) (cs : Fin p → Bool) (hns : ∑ r, ns r = 3)
    (hv : ∀ r, tagV (σs r) = 0) :
    ‖∏ r, claimT_H Sig A z i μ ns ws σs cs r‖ ≤
      ((R + K') * (1 + R) * (1 + claimT_V A μ)) ^ (3 * (p + 3)) := by
  rw [norm_prod]
  calc ∏ r, ‖claimT_H Sig A z i μ ns ws σs cs r‖
      ≤ ∏ r, ((R + K') * (1 + R) * (1 + claimT_V A μ)) ^ (3 * (ns r + 1)) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun r _ =>
          claimT_avg_le (by have := claimT_V_nonneg A μ; positivity) fun ν hν => by
            rw [claimT_norm_conjIf]
            exact claimT_tagA_rough Sig A z hν i hR1 hK'0 hR hK' _ _ _ (hv r)
    _ = ((R + K') * (1 + R) * (1 + claimT_V A μ)) ^ (3 * (p + 3)) := by
        rw [Finset.prod_pow_eq_pow_sum]
        congr 1
        rw [← Finset.mul_sum, Finset.sum_add_distrib, hns, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul, mul_one]
        ring

/-- `Q_μ = ∑_{j,j'} X_{jμ} G^{(μ)}_{jj'} X_{j'μ}`. -/
private theorem claimT_Qmu_eq (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (μ : Fin N) :
    Qmu Sig A z μ = ∑ j, ∑ j', ((A j μ : ℝ) : ℂ) * Gmu Sig A z μ (Sum.inl j) (Sum.inl j') *
      ((A j' μ : ℝ) : ℂ) := by
  have hA : updCol A μ (fun j => A j μ) = A := by
    funext j ν; by_cases h : ν = μ <;> simp [updCol, h]
  conv_lhs => rw [← hA]
  rw [Qmu_updCol]

/-- `|Q_μ| ≤ K V²` for `|G^{(μ)}_{jj'}| ≤ K`. -/
private theorem claimT_Qmu_le (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (μ : Fin N) {K : ℝ} (hK : ∀ s t, ‖Gmu Sig A z μ s t‖ ≤ K) :
    ‖Qmu Sig A z μ‖ ≤ K * claimT_V A μ ^ 2 := by
  rw [claimT_Qmu_eq]
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK (Sum.inr μ) (Sum.inr μ))
  calc ‖∑ j, ∑ j', ((A j μ : ℝ) : ℂ) * Gmu Sig A z μ (Sum.inl j) (Sum.inl j') *
        ((A j' μ : ℝ) : ℂ)‖ ≤ ∑ j, ∑ j', |A j μ| * K * |A j' μ| := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun j' _ => ?_))
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs]
        gcongr
        exact hK _ _
    _ = K * claimT_V A μ ^ 2 := by
        unfold claimT_V
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j' _ => by ring

/-- The rough bound of the integrand: `|F| ≤ W^{4(p+3)}` when `|G_{st}|, |G^{(μ)}_{st}| ≤ R`. -/
private theorem claimT_F_rough (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (i : Fin M) (μ : Fin N) {R K' : ℝ} (hR1 : 1 ≤ R) (hK'0 : 0 ≤ K')
    (hR : ∀ s t, ‖Gmu Sig A z μ s t‖ ≤ R) (hRG : ∀ s t, ‖G Sig A z s t‖ ≤ R)
    (hK' : ∀ s t, ‖PiZ N Sig z s t‖ ≤ K') {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r))
    (σs : ∀ r, Fin (ns r + 1) → Fin 3) (cs : Fin p → Bool) (hns : ∑ r, ns r = 3)
    (hv : ∀ r, tagV (σs r) = 0) :
    ‖claimT_F Sig A z i μ ns ws σs cs‖ ≤
      ((R + K') * (1 + R) * (1 + claimT_V A μ)) ^ (4 * (p + 3)) := by
  have hV := claimT_V_nonneg A μ
  set W := (R + K') * (1 + R) * (1 + claimT_V A μ) with hW
  have hRW : R ≤ W := by
    rw [hW, mul_assoc]
    calc R ≤ R + K' := by linarith
      _ ≤ (R + K') * ((1 + R) * (1 + claimT_V A μ)) :=
          le_mul_of_one_le_right (by linarith) (by nlinarith)
  rw [claimT_F_eq, norm_mul]
  have h1 := claimT_Gam_le ns σs cs hns (hR1.trans hRW)
    ((hRG (Sum.inr μ) (Sum.inr μ)).trans hRW)
  have h2 := claimT_prodH_rough Sig A z i μ hR1 hK'0 hR hK' ns ws σs cs hns hv
  calc ‖claimT_Gam ns σs cs (G Sig A z (Sum.inr μ) (Sum.inr μ))‖ *
        ‖∏ r, claimT_H Sig A z i μ ns ws σs cs r‖ ≤ W ^ (p + 3) * W ^ (3 * (p + 3)) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by have := hR1.trans hRW; positivity)
    _ = W ^ (4 * (p + 3)) := by rw [← pow_add]; ring_nf

/-- The bound of the integrand with `G_μμ → P` on the `X^{(μ)}`-measurable event. -/
private theorem claimT_FP_good (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (i : Fin M) (μ : Fin N) (Kx : ℕ) {Kg K' CY : ℝ} (hKg : 1 ≤ Kg) (hK'0 : 0 ≤ K')
    (hCY : 1 ≤ CY) (hK : ∀ s t, ‖Gmu Sig A z μ s t‖ ≤ Kg) (hK' : ∀ s t, ‖PiZ N Sig z s t‖ ≤ K')
    (hY : ∀ k, ‖calY z (Ymu Sig A z μ) Kx k‖ ≤ CY) {p : ℕ} (ns : Fin p → ℕ)
    (ws : ∀ r, Word (ns r)) (σs : ∀ r, Fin (ns r + 1) → Fin 3) (cs : Fin p → Bool)
    (hns : ∑ r, ns r = 3) (hv : ∀ r, tagV (σs r) = 0) :
    ‖claimT_FP Sig A z i μ Kx ns ws σs cs‖ ≤
      (((Kx : ℝ) + 1) * CY * ((1 + Kg) * (1 + claimT_V A μ) ^ 2) ^ Kx) ^ (p + 3) *
        ((Kg + K') * (1 + Kg) * (1 + claimT_V A μ)) ^ (3 * (p + 3)) := by
  have hV := claimT_V_nonneg A μ
  have hQ := claimT_Qmu_le Sig A z μ hK
  set U := (1 + Kg) * (1 + claimT_V A μ) ^ 2 with hU
  have hU1 : 1 ≤ U := by
    have : 1 ≤ (1 + claimT_V A μ) ^ 2 := one_le_pow₀ (by linarith)
    nlinarith
  have hQU : 1 + ‖Qmu Sig A z μ‖ ≤ U := by
    have : Kg * claimT_V A μ ^ 2 ≤ Kg * (1 + claimT_V A μ) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hV (by linarith) 2) (by linarith)
    have h2 : 1 ≤ (1 + claimT_V A μ) ^ 2 := one_le_pow₀ (by linarith)
    rw [hU]; nlinarith
  have hP : ‖∑ k ∈ Finset.range (Kx + 1), calY z (Ymu Sig A z μ) Kx k * Qmu Sig A z μ ^ k‖ ≤
      ((Kx : ℝ) + 1) * CY * U ^ Kx := by
    calc _ ≤ ∑ k ∈ Finset.range (Kx + 1), CY * U ^ Kx := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
          rw [norm_mul, norm_pow]
          have hk' : k ≤ Kx := by have := Finset.mem_range.1 hk; omega
          refine mul_le_mul (hY k) ?_ (by positivity) (by linarith)
          calc ‖Qmu Sig A z μ‖ ^ k ≤ U ^ k := pow_le_pow_left₀ (norm_nonneg _) (by linarith) k
            _ ≤ U ^ Kx := pow_le_pow_right₀ hU1 hk'
      _ = ((Kx : ℝ) + 1) * CY * U ^ Kx := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  have hB1 : 1 ≤ ((Kx : ℝ) + 1) * CY * U ^ Kx := by
    have h1 : (1 : ℝ) ≤ (Kx : ℝ) + 1 := by have := (Nat.cast_nonneg Kx : (0 : ℝ) ≤ Kx); linarith
    have h2 : 1 ≤ U ^ Kx := one_le_pow₀ hU1
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  unfold claimT_FP
  rw [norm_mul]
  have h1 := claimT_Gam_le ns σs cs hns hB1 hP
  have h2 := claimT_prodH_rough Sig A z i μ hKg hK'0 hK hK' ns ws σs cs hns hv
  exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)

/-! ## Measurability in the matrix -/

private theorem claimT_cont_conjIf {X : Type*} [TopologicalSpace X] (c : Bool) {f : X → ℂ}
    (hf : Continuous f) : Continuous fun x => conjIf c (f x) := by
  cases c
  · simpa [conjIf] using hf
  · simp only [conjIf, ite_true]
    exact Complex.continuous_conj.comp hf

section Meas

variable {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {z : ℂ} (hz : 0 < z.im)
  (i : Fin M) (μ : Fin N) {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r))
  (σs : ∀ r, Fin (ns r + 1) → Fin 3) (cs : Fin p → Bool)
include hSig hz

private theorem claimT_cont_F :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => claimT_F Sig A z i μ ns ws σs cs := by
  unfold claimT_F
  exact continuous_const.mul (continuous_finsetSum _ fun νs _ => continuous_finsetProd _
    fun r _ => claimT_cont_conjIf _ ((claimT_cont_tagA hSig hz _ i μ _ _ _).mul
      ((claimT_cont_Gent hSig hz _ _).pow _)))

private theorem claimT_cont_H (r : Fin p) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => claimT_H Sig A z i μ ns ws σs cs r := by
  unfold claimT_H
  exact continuous_const.mul (continuous_finsetSum _ fun ν _ =>
    claimT_cont_conjIf _ (claimT_cont_tagA hSig hz _ i μ _ _ _))

private theorem claimT_cont_FP (Kx : ℕ) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => claimT_FP Sig A z i μ Kx ns ws σs cs := by
  unfold claimT_FP claimT_Gam
  refine (continuous_finsetProd _ fun r _ => (claimT_cont_conjIf _ ?_).pow _).mul
    (continuous_finsetProd _ fun r _ => claimT_cont_H hSig hz i μ ns ws σs cs r)
  exact continuous_finsetSum _ fun k _ =>
    (claimT_cont_calY hSig hz μ Kx k).mul ((claimT_cont_Qmu hSig hz μ).pow _)

omit i ns ws σs cs in
private theorem claimT_cont_Shat :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => claimT_Shat Sig A z μ := by
  unfold claimT_Shat
  refine continuous_const.mul (continuous_finsetSum _ fun ν _ => ?_)
  simp only [emptyScal, ite_true]
  exact (claimT_cont_entGmu hSig hz μ _ _).sub continuous_const

omit i ns ws σs cs in
private theorem claimT_meas_Good (β : ℝ) :
    MeasurableSet {A : Matrix (Fin M) (Fin N) ℝ | claimT_Good Sig A z μ β} := by
  have e : {A : Matrix (Fin M) (Fin N) ℝ | claimT_Good Sig A z μ β} =
      ⋂ s : Fin M ⊕ Fin N, ⋂ t : Fin M ⊕ Fin N,
        {A | s ≠ Sum.inr μ → t ≠ Sum.inr μ → ‖Gmu Sig A z μ s t - PiZ N Sig z s t‖ ≤ β} := by
    ext A; simp [claimT_Good]
  rw [e]
  refine MeasurableSet.iInter fun s => MeasurableSet.iInter fun t => ?_
  by_cases h : s ≠ Sum.inr μ ∧ t ≠ Sum.inr μ
  · have e2 : {A : Matrix (Fin M) (Fin N) ℝ | s ≠ Sum.inr μ → t ≠ Sum.inr μ →
        ‖Gmu Sig A z μ s t - PiZ N Sig z s t‖ ≤ β} =
        {A | ‖Gmu Sig A z μ s t - PiZ N Sig z s t‖ ≤ β} := by
      ext A; simp [h.1, h.2]
    rw [e2]
    exact measurableSet_le ((claimT_cont_Gmu hSig hz μ s t).sub continuous_const).norm.measurable
      measurable_const
  · have e2 : {A : Matrix (Fin M) (Fin N) ℝ | s ≠ Sum.inr μ → t ≠ Sum.inr μ →
        ‖Gmu Sig A z μ s t - PiZ N Sig z s t‖ ≤ β} = Set.univ := by
      ext A
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      intro hs ht; exact absurd ⟨hs, ht⟩ h
    rw [e2]; exact MeasurableSet.univ

end Meas

/-! ## The column law, the split along an event, `Ψ` -/

/-- The law of the column `μ` has mean `0` and the moments bounded by (moments of X-1). -/
private theorem claimT_colLaw {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {C : ℕ → ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) (μ : Fin N)
    (hN : 1 ≤ N) (j : Fin M) :
    IsProbabilityMeasure (entryLaw X (j, μ)) ∧ ∫ y, y ∂(entryLaw X (j, μ)) = 0 ∧
    ∀ n : ℕ, Integrable (fun y => |y| ^ n) (entryLaw X (j, μ)) ∧
      ∫ y, |Real.sqrt N * y| ^ n ∂(entryLaw X (j, μ)) ≤ C n := by
  have hm := hX.measurable j μ
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNp
  have e : entryLaw X (j, μ) = (ℙ : Measure Ω).map fun ω => X ω j μ := rfl
  rw [e]
  refine ⟨(Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance, ?_,
    fun n => ⟨?_, ?_⟩⟩
  · rw [integral_map hm.aemeasurable (by fun_prop)]
    exact hX.mean j μ
  · rw [integrable_map_measure (by fun_prop) hm.aemeasurable]
    have h := (hX.integrable_moment n j μ).const_mul ((Real.sqrt N)⁻¹ ^ n)
    refine h.congr (ae_of_all _ fun ω => ?_)
    simp only [Function.comp, abs_mul, abs_of_pos hs, mul_pow, ← mul_assoc]
    rw [← mul_pow, inv_mul_cancel₀ hs.ne', one_pow, one_mul]
  · rw [integral_map hm.aemeasurable (by fun_prop)]
    exact hX.moment n j μ

/-- `y ≤ s y² + (4s)⁻¹` for `s > 0`. -/
private theorem claimT_amgm {s : ℝ} (hs : 0 < s) (y : ℝ) : y ≤ s * y ^ 2 + (4 * s)⁻¹ := by
  have h : s * y ^ 2 + (4 * s)⁻¹ - y = (2 * s * y - 1) ^ 2 / (4 * s) := by
    field_simp
    ring
  have : 0 ≤ (2 * s * y - 1) ^ 2 / (4 * s) := by positivity
  linarith

/-- Splitting `E|f|` along an event `Ξ`: if `|f| ≤ g` on `Ξ`, then
`|E f| ≤ E g + s E|f|² + P(Ξᶜ)/(4s)` for every `s > 0`. -/
private theorem claimT_split {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {f : Ω → ℂ} {g : Ω → ℝ} {Ξ : Set Ω} {s : ℝ} (hs : 0 < s)
    (hfi : Integrable fun ω => ‖f ω‖) (hf2i : Integrable fun ω => ‖f ω‖ ^ 2) (hgi : Integrable g)
    (hg0 : ∀ ω, 0 ≤ g ω) (hon : ∀ ω ∈ Ξ, ‖f ω‖ ≤ g ω) :
    ‖∫ ω, f ω‖ ≤ (∫ ω, g ω) + s * (∫ ω, ‖f ω‖ ^ 2) + (ℙ Ξᶜ).toReal * (4 * s)⁻¹ := by
  set Bs : Set Ω := toMeasurable ℙ Ξᶜ with hBs
  have hpt : ∀ ω, ‖f ω‖ ≤ g ω + s * ‖f ω‖ ^ 2 + Bs.indicator (fun _ => (4 * s)⁻¹) ω := by
    intro ω
    have hind : 0 ≤ Bs.indicator (fun _ => (4 * s)⁻¹) ω :=
      Set.indicator_nonneg (fun _ _ => by positivity) _
    by_cases hω : ω ∈ Ξ
    · have := hon ω hω
      have : 0 ≤ s * ‖f ω‖ ^ 2 := by positivity
      linarith
    · have hmem : ω ∈ Bs := subset_toMeasurable _ _ hω
      rw [Set.indicator_of_mem hmem]
      have := claimT_amgm hs ‖f ω‖
      linarith [hg0 ω]
  have hI : Integrable fun ω => Bs.indicator (fun _ => (4 * s)⁻¹) ω :=
    (integrable_const _).indicator (measurableSet_toMeasurable _ _)
  have h1 : Integrable fun ω => g ω + s * ‖f ω‖ ^ 2 := hgi.add (hf2i.const_mul s)
  have h2 : Integrable fun ω => g ω + s * ‖f ω‖ ^ 2 + Bs.indicator (fun _ => (4 * s)⁻¹) ω :=
    h1.add hI
  have e1 : ∫ ω, (g ω + s * ‖f ω‖ ^ 2 + Bs.indicator (fun _ => (4 * s)⁻¹) ω) =
      (∫ ω, (g ω + s * ‖f ω‖ ^ 2)) + ∫ ω, Bs.indicator (fun _ => (4 * s)⁻¹) ω :=
    integral_add h1 hI
  have e2 : ∫ ω, (g ω + s * ‖f ω‖ ^ 2) = (∫ ω, g ω) + ∫ ω, s * ‖f ω‖ ^ 2 :=
    integral_add hgi (hf2i.const_mul s)
  have e3 : ∫ ω, Bs.indicator (fun _ => (4 * s)⁻¹) ω = (ℙ Ξᶜ).toReal * (4 * s)⁻¹ := by
    rw [integral_indicator_const _ (measurableSet_toMeasurable _ _), measureReal_def,
      measure_toMeasurable, smul_eq_mul]
  have hint : ∫ ω, ‖f ω‖ ≤ (∫ ω, g ω) + s * (∫ ω, ‖f ω‖ ^ 2) + (ℙ Ξᶜ).toReal * (4 * s)⁻¹ := by
    refine (integral_mono hfi h2 hpt).trans (le_of_eq ?_)
    rw [e1, e2, e3, integral_const_mul]
  exact (norm_integral_le_integral_norm _).trans hint

private theorem claimT_one_le_N_im {τ : ℝ} {z : ℂ} (hN : 1 ≤ N) (hτ : 0 < τ)
    (hz : z ∈ specDomain τ N) : 1 ≤ (N : ℝ) * z.im := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have h1 : (N : ℝ) * (N : ℝ) ^ (-1 + τ) = (N : ℝ) ^ τ := by
    rw [mul_comm, ← Real.rpow_add_one hNp.ne']; ring_nf
  have h2 : 1 ≤ (N : ℝ) ^ τ := Real.one_le_rpow hN1r hτ.le
  calc (1 : ℝ) ≤ (N : ℝ) ^ τ := h2
    _ = (N : ℝ) * (N : ℝ) ^ (-1 + τ) := h1.symm
    _ ≤ (N : ℝ) * z.im := mul_le_mul_of_nonneg_left hz.2.2.2.1 hNp.le

/-- `Ψ ≥ 1/(Nη) ≥ τ/N` on `𝐃(τ, N)`. -/
private theorem claimT_Psi_ge {τ : ℝ} {σ : Fin M → ℝ} {z : ℂ} (hN : 1 ≤ N) (hτ : 0 < τ)
    (hz : z ∈ specDomain τ N) : τ / N ≤ Psi N σ z := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hη : 0 < z.im := hz.1
  have hητ : z.im ≤ τ⁻¹ := hz.2.2.2.2
  unfold Psi
  have h1 : τ / N ≤ 1 / (N * z.im) := by
    rw [div_le_div_iff₀ hNp (by positivity), one_mul]
    calc τ * (N * z.im) ≤ τ * (N * τ⁻¹) := by gcongr
      _ = N := by field_simp
  linarith [Real.sqrt_nonneg ((mFun N σ z).im / (N * z.im))]

/-- `Ψ² ≥ Im m/(Nη) ≥ (K_m N)⁻¹` on `𝐃(τ, N)` (Lemma 4.10). -/
private theorem claimT_Psi_sq_ge {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) {z : ℂ} (hz : z ∈ S) :
    (mBoundConst τ * N)⁻¹ ≤ Psi N (specOf Sig) z ^ 2 := by
  have hzD := hset.domain.1 hz
  obtain ⟨-, -, hm3⟩ := gen_prop_m_specDomain (claimT_density hset hN) hzD
  have hC := mBoundConst_pos hset.pos
  have hη : 0 < z.im := hzD.1
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : 0 < (N : ℝ) * z.im := by positivity
  have ha0 : 0 ≤ (mFun N (specOf Sig) z).im := le_trans (by positivity) hm3
  set x := Real.sqrt ((mFun N (specOf Sig) z).im / (N * z.im)) with hx
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hsq : x ^ 2 = (mFun N (specOf Sig) z).im / (N * z.im) := Real.sq_sqrt (by positivity)
  have hle : x ≤ Psi N (specOf Sig) z := by
    unfold Psi
    have : 0 ≤ 1 / ((N : ℝ) * z.im) := by positivity
    linarith
  have h1 : (mBoundConst τ * N)⁻¹ ≤ (mFun N (specOf Sig) z).im / (N * z.im) := by
    rw [le_div_iff₀ hpos]
    calc (mBoundConst τ * N)⁻¹ * (N * z.im) = (mBoundConst τ)⁻¹ * z.im := by
          field_simp
      _ ≤ (mFun N (specOf Sig) z).im := hm3
  calc (mBoundConst τ * N)⁻¹ ≤ x ^ 2 := by rw [hsq]; exact h1
    _ ≤ Psi N (specOf Sig) z ^ 2 := pow_le_pow_left₀ hx0 hle 2


/-- `Ψ ≤ (√C_m + 1) N^{−τ/2}` on `S` (Lemma 4.10, `N η ≥ N^τ`). -/
private theorem claimT_Psi_decay {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) {z : ℂ} (hz : z ∈ S) :
    Psi N (specOf Sig) z ≤ (Real.sqrt (mBoundConst τ) + 1) * (N : ℝ) ^ (-τ / 2) := by
  have hτ := hset.pos
  have hzD := hset.domain.1 hz
  obtain ⟨-, hm2, hm3⟩ := gen_prop_m_specDomain (claimT_density hset hN) hzD
  have hC := mBoundConst_pos hτ
  have hη : 0 < z.im := hzD.1
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have ha0 : 0 ≤ (mFun N (specOf Sig) z).im := le_trans (by positivity) hm3
  have haC : (mFun N (specOf Sig) z).im ≤ mBoundConst τ := le_trans (Complex.im_le_norm _) hm2
  have hNη : (N : ℝ) ^ τ ≤ N * z.im := by
    have h1 : (N : ℝ) * (N : ℝ) ^ (-1 + τ) = (N : ℝ) ^ τ := by
      rw [mul_comm, ← Real.rpow_add_one hNp.ne']; ring_nf
    rw [← h1]; exact mul_le_mul_of_nonneg_left hzD.2.2.2.1 hNp.le
  have hNτ : 0 < (N : ℝ) ^ τ := Real.rpow_pos_of_pos hNp τ
  have hpos : 0 < (N : ℝ) * z.im := lt_of_lt_of_le hNτ hNη
  have hh : ((N : ℝ) ^ (-τ / 2)) ^ 2 = ((N : ℝ) ^ τ)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le, ← Real.rpow_neg hNp.le]; ring_nf
  have hh0 : 0 ≤ (N : ℝ) ^ (-τ / 2) := Real.rpow_nonneg hNp.le _
  have hh1 : (N : ℝ) ^ (-τ / 2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1r (by linarith)
  unfold Psi
  have h1 : Real.sqrt ((mFun N (specOf Sig) z).im / (N * z.im)) ≤
      Real.sqrt (mBoundConst τ) * (N : ℝ) ^ (-τ / 2) := by
    rw [← Real.sqrt_sq hh0, ← Real.sqrt_mul hC.le]
    refine Real.sqrt_le_sqrt ?_
    rw [hh, div_le_iff₀ hpos]
    calc (mFun N (specOf Sig) z).im ≤ mBoundConst τ := haC
      _ = mBoundConst τ * ((N : ℝ) ^ τ)⁻¹ * (N : ℝ) ^ τ := by field_simp
      _ ≤ mBoundConst τ * ((N : ℝ) ^ τ)⁻¹ * (N * z.im) := by gcongr
  have h2 : 1 / ((N : ℝ) * z.im) ≤ (N : ℝ) ^ (-τ / 2) := by
    calc 1 / ((N : ℝ) * z.im) ≤ ((N : ℝ) ^ τ)⁻¹ := by
          rw [one_div]; exact inv_anti₀ hNτ hNη
      _ = ((N : ℝ) ^ (-τ / 2)) ^ 2 := hh.symm
      _ ≤ (N : ℝ) ^ (-τ / 2) := by nlinarith
  linarith

/-- `F̃ ≤ |m_N| + |m| ≤ R + C_m` when `|G_{νν}| ≤ R`. -/
private theorem claimT_Ft_le {Sig : Matrix (Fin M) (Fin M) ℝ} (A : Matrix (Fin M) (Fin N) ℝ)
    {z : ℂ} {R Cm : ℝ} (hN : 1 ≤ N) (hR : ∀ s t, ‖G Sig A z s t‖ ≤ R)
    (hm : ‖mFun N (specOf Sig) z‖ ≤ Cm) : Ft Sig A z ≤ R + Cm := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  unfold Ft mN
  refine (norm_sub_le _ _).trans (add_le_add ?_ hm)
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (N : ℝ)⁻¹ * ‖∑ ν, G Sig A z (Sum.inr ν) (Sum.inr ν)‖ ≤ (N : ℝ)⁻¹ * ∑ _ν : Fin N, R :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun ν _ => hR _ _))
          (by positivity)
    _ = R := by simp; field_simp

/-! ## The main part after the column expectation -/

/-- (avg_step 1), main part: `E 1_{Ξ_μ} F_P` through `E = E^{(μ)} E_μ` (`integral_colSplit`). -/
private theorem claimT_T1 {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {C : ℕ → ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X)
    {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {z : ℂ} (hz : 0 < z.im) (i : Fin M)
    (μ : Fin N) (Kx : ℕ) {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r))
    (σs : ∀ r, Fin (ns r + 1) → Fin 3) (cs : Fin p → Bool) {β b b₀ c₂ Cpt PΞ : ℝ}
    (Ξ : Set Ω) (Env : Matrix (Fin M) (Fin N) ℝ → ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hb₀ : 0 ≤ b₀) (hbb : b₀ ≤ b) (hc₂ : 0 ≤ c₂) (hCpt : 0 ≤ Cpt)
    (hmain : ∀ A, claimT_Good Sig A z μ β →
      ‖∫ y, claimT_FP Sig (updCol A μ y) z i μ Kx ns ws σs cs ∂(colLaw X μ)‖ ≤
        Cpt * (2 * ‖claimT_Shat Sig A z μ‖) ^
          (Finset.univ.filter fun r => ns r = 0 ∧ tagMu (σs r) = 0).card *
        (N : ℝ) ^ (-(1 : ℝ) / 2) *
        b ^ (2 * (p - (Finset.univ.filter fun r => ns r = 0 ∧ tagMu (σs r) = 0).card)))
    (hShat1 : ∀ A, claimT_Good Sig A z μ β → ‖claimT_Shat Sig A z μ‖ ≤ 1)
    (hΞ : ∀ ω ∈ Ξ, claimT_Good Sig (X ω) z μ β ∧
      ‖claimT_Shat Sig (X ω) z μ‖ ≤ Ft Sig (X ω) z + c₂ * b₀ ^ 2)
    (hPΞ : (ℙ Ξᶜ).toReal ≤ PΞ)
    (hEnvI : Integrable fun ω => Env (X ω)) (hEnv0 : ∀ A, 0 ≤ Env A)
    (hEnv : ∀ A, claimT_Good Sig A z μ β → ‖claimT_FP Sig A z i μ Kx ns ws σs cs‖ ≤ Env A)
    (hFtI : Integrable fun ω => Ft Sig (X ω) z ^ p) :
    ‖∫ ω, (if claimT_Good Sig (X ω) z μ β then claimT_FP Sig (X ω) z i μ Kx ns ws σs cs else 0)‖
      ≤ Cpt * (N : ℝ) ^ (-(1 : ℝ) / 2) * ((1 + (4 * c₂) ^ p) * (b ^ 2) ^ p +
          4 ^ p * ∫ ω, Ft Sig (X ω) z ^ p) + Cpt * 2 ^ p * PΞ := by
  have hN : 0 < N := Fin.pos μ
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set R0 := Finset.univ.filter fun r => ns r = 0 ∧ tagMu (σs r) = 0 with hR0
  set j := R0.card with hj
  have hjp : j ≤ p := by
    calc j ≤ (Finset.univ : Finset (Fin p)).card := Finset.card_filter_le _ _
      _ = p := by simp
  set F₁ : Matrix (Fin M) (Fin N) ℝ → ℂ := fun A =>
    if claimT_Good Sig A z μ β then claimT_FP Sig A z i μ Kx ns ws σs cs else 0 with hF₁
  have hXm : Measurable X :=
    measurable_pi_iff.2 fun j => measurable_pi_iff.2 fun ν => hX.measurable j ν
  have hGm := claimT_meas_Good (N := N) hSig hz μ β
  have hF₁m : Measurable F₁ :=
    Measurable.ite hGm (claimT_cont_FP hSig hz i μ ns ws σs cs Kx).measurable measurable_const
  have hF₁i : Integrable fun ω => F₁ (X ω) := by
    refine hEnvI.mono' (hF₁m.comp hXm).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    simp only [hF₁]
    split_ifs with h
    · exact hEnv _ h
    · rw [norm_zero]; exact hEnv0 _
  have hsplit := integral_colSplit hX μ hF₁m hF₁i
  set e := (N : ℝ) ^ (-(1 : ℝ) / 2) with he
  have he0 : 0 ≤ e := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have he1 : e ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1r (by norm_num)
  set B₁ : Matrix (Fin M) (Fin N) ℝ → ℝ := fun A =>
    if claimT_Good Sig A z μ β then
      Cpt * (2 * ‖claimT_Shat Sig A z μ‖) ^ j * e * b ^ (2 * (p - j)) else 0 with hB₁
  have hpt : ∀ A, ‖∫ y, F₁ (updCol A μ y) ∂(colLaw X μ)‖ ≤ B₁ A := by
    intro A
    by_cases hA : claimT_Good Sig A z μ β
    · have e1 : (fun y => F₁ (updCol A μ y)) =
          fun y => claimT_FP Sig (updCol A μ y) z i μ Kx ns ws σs cs := by
        funext y; simp only [hF₁, claimT_Good_updCol, hA, ite_true]
      rw [e1]; simp only [hB₁, hA, ite_true]; exact hmain A hA
    · have e1 : (fun y => F₁ (updCol A μ y)) = fun _ => 0 := by
        funext y; simp only [hF₁, claimT_Good_updCol, hA, ite_false]
      rw [e1]; simp [hB₁, hA]
  have hB₁m : Measurable fun ω => B₁ (X ω) := by
    have h : Measurable B₁ := by
      refine Measurable.ite hGm ?_ measurable_const
      exact ((((continuous_const.mul (claimT_cont_Shat hSig hz μ).norm).pow j).const_mul
        Cpt).mul continuous_const |>.mul continuous_const).measurable
    exact h.comp hXm
  have hB₁b : ∀ A, B₁ A ≤ Cpt * 2 ^ p := by
    intro A
    simp only [hB₁]
    split_ifs with hA
    · have h1 : (2 * ‖claimT_Shat Sig A z μ‖) ^ j ≤ 2 ^ p := by
        calc (2 * ‖claimT_Shat Sig A z μ‖) ^ j ≤ 2 ^ j :=
              pow_le_pow_left₀ (by positivity) (by linarith [hShat1 A hA]) _
          _ ≤ 2 ^ p := pow_le_pow_right₀ (by norm_num) hjp
      have h2 : b ^ (2 * (p - j)) ≤ 1 := pow_le_one₀ hb0 hb1
      calc Cpt * (2 * ‖claimT_Shat Sig A z μ‖) ^ j * e * b ^ (2 * (p - j))
          ≤ Cpt * 2 ^ p * 1 * 1 := by gcongr
        _ = Cpt * 2 ^ p := by ring
    · positivity
  have hB₁0 : ∀ A, 0 ≤ B₁ A := fun A => by simp only [hB₁]; split_ifs <;> positivity
  have hB₁i : Integrable fun ω => B₁ (X ω) :=
    (integrable_const (Cpt * 2 ^ p)).mono' hB₁m.aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (hB₁0 _)]; exact hB₁b _)
  set Bs : Set Ω := toMeasurable ℙ Ξᶜ with hBs
  set Gf : Ω → ℝ := fun ω => Cpt * e * ((1 + (4 * c₂) ^ p) * (b ^ 2) ^ p +
    4 ^ p * Ft Sig (X ω) z ^ p) + Cpt * 2 ^ p * Bs.indicator (fun _ => (1 : ℝ)) ω with hGf
  have hF0 : ∀ ω, 0 ≤ Ft Sig (X ω) z := fun ω => norm_nonneg _
  have hle : ∀ ω, B₁ (X ω) ≤ Gf ω := by
    intro ω
    have hind : 0 ≤ Bs.indicator (fun _ => (1 : ℝ)) ω :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have hfirst :
        0 ≤ Cpt * e * ((1 + (4 * c₂) ^ p) * (b ^ 2) ^ p + 4 ^ p * Ft Sig (X ω) z ^ p) := by
      have := hF0 ω; positivity
    by_cases hω : ω ∈ Ξ
    · obtain ⟨hG, hS⟩ := hΞ ω hω
      simp only [hB₁, hG, ite_true, hGf]
      have hS0 := norm_nonneg (claimT_Shat Sig (X ω) z μ)
      have hy : (b ^ 2) ^ (p - j) * (2 * ‖claimT_Shat Sig (X ω) z μ‖) ^ j ≤
          (b ^ 2) ^ p + (2 * ‖claimT_Shat Sig (X ω) z μ‖) ^ p := claimT_young (by positivity)
            (by positivity) hjp
      have h2 : (2 * ‖claimT_Shat Sig (X ω) z μ‖) ^ p ≤
          4 ^ p * Ft Sig (X ω) z ^ p + (4 * c₂) ^ p * (b ^ 2) ^ p := by
        have hb2 : b₀ ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ hb₀ hbb 2
        calc (2 * ‖claimT_Shat Sig (X ω) z μ‖) ^ p
            ≤ (2 * Ft Sig (X ω) z + 2 * c₂ * b₀ ^ 2) ^ p :=
              pow_le_pow_left₀ (by positivity) (by linarith) _
          _ ≤ 2 ^ p * ((2 * Ft Sig (X ω) z) ^ p + (2 * c₂ * b₀ ^ 2) ^ p) :=
              claimT_pow_add_le (by have := hF0 ω; positivity) (by positivity) p
          _ ≤ 2 ^ p * ((2 * Ft Sig (X ω) z) ^ p + (2 * c₂ * b ^ 2) ^ p) := by gcongr
          _ = 4 ^ p * Ft Sig (X ω) z ^ p + (4 * c₂) ^ p * (b ^ 2) ^ p := by
              have h4 : (4 : ℝ) ^ p = 2 ^ p * 2 ^ p := by rw [← mul_pow]; norm_num
              rw [mul_pow, mul_pow, mul_pow, mul_pow, h4]; ring
      calc Cpt * (2 * ‖claimT_Shat Sig (X ω) z μ‖) ^ j * e * b ^ (2 * (p - j))
          = Cpt * e * ((b ^ 2) ^ (p - j) * (2 * ‖claimT_Shat Sig (X ω) z μ‖) ^ j) := by
            rw [pow_mul]; ring
        _ ≤ Cpt * e * ((1 + (4 * c₂) ^ p) * (b ^ 2) ^ p + 4 ^ p * Ft Sig (X ω) z ^ p) := by
            gcongr
            nlinarith
        _ ≤ _ := le_add_of_nonneg_right (by positivity)
    · have hmem : ω ∈ Bs := subset_toMeasurable _ _ hω
      rw [hGf]
      simp only [Set.indicator_of_mem hmem, mul_one]
      exact (hB₁b _).trans (le_add_of_nonneg_left hfirst)
  have hGfi : Integrable Gf :=
    (((integrable_const _).add (hFtI.const_mul _)).const_mul _).add
      (((integrable_const _).indicator (measurableSet_toMeasurable _ _)).const_mul _)
  have hGfv : ∫ ω, Gf ω = Cpt * e * ((1 + (4 * c₂) ^ p) * (b ^ 2) ^ p +
      4 ^ p * ∫ ω, Ft Sig (X ω) z ^ p) + Cpt * 2 ^ p * (ℙ Ξᶜ).toReal := by
    have hi1 : Integrable fun ω => Cpt * e * ((1 + (4 * c₂) ^ p) * (b ^ 2) ^ p +
        4 ^ p * Ft Sig (X ω) z ^ p) := ((integrable_const _).add (hFtI.const_mul _)).const_mul _
    have hi2 : Integrable fun ω => Cpt * 2 ^ p * Bs.indicator (fun _ => (1 : ℝ)) ω :=
      ((integrable_const _).indicator (measurableSet_toMeasurable _ _)).const_mul _
    have e1 : ∫ ω, Gf ω = (∫ ω, Cpt * e * ((1 + (4 * c₂) ^ p) * (b ^ 2) ^ p +
        4 ^ p * Ft Sig (X ω) z ^ p)) + ∫ ω, Cpt * 2 ^ p * Bs.indicator (fun _ => (1 : ℝ)) ω :=
      integral_add hi1 hi2
    rw [e1, integral_const_mul, integral_const_mul, integral_add (integrable_const _)
      (hFtI.const_mul _), integral_const_mul,
      integral_indicator_const _ (measurableSet_toMeasurable _ _), measureReal_def,
      measure_toMeasurable]
    simp [integral_const_mul]
  calc ‖∫ ω, F₁ (X ω)‖ = ‖∫ ω, ∫ y, F₁ (updCol (X ω) μ y) ∂(colLaw X μ)‖ := by rw [hsplit]
    _ ≤ ∫ ω, ‖∫ y, F₁ (updCol (X ω) μ y) ∂(colLaw X μ)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, B₁ (X ω) := integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hB₁i
        (ae_of_all _ fun ω => hpt _)
    _ ≤ ∫ ω, Gf ω := integral_mono hB₁i hGfi hle
    _ = _ := hGfv
    _ ≤ _ := by
        gcongr

/-! ## The exponent rows -/

/-- `D_a ≥ dPrevTwo τ p` leaves room for the off-event part: `4 q_e + 4p + 4 ≤ D_a − 3`,
`q_e = (2K_τ + 15)(p + 3)`. -/
private theorem claimT_Da {τ : ℝ} {p : ℕ} {Da : ℝ} (hp2 : 2 ≤ p) (hDa : dPrevTwo τ p ≤ Da) :
    (4 * (((2 * kTau τ + 15) * (p + 3) : ℕ) : ℝ) + 4 * p + 4) ≤ Da - 3 := by
  have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hk : (0 : ℝ) ≤ (kTau τ : ℝ) := Nat.cast_nonneg _
  unfold dPrevTwo dPrev at hDa
  push_cast
  nlinarith [mul_nonneg hk (sub_nonneg.2 hP), mul_nonneg (mul_nonneg hk (sub_nonneg.2 hP))
    (sub_nonneg.2 hP)]

/-- `(K_τ + 1) τ ≥ 24`. -/
private theorem claimT_kTau {τ : ℝ} (hτ : 0 < τ) : 24 ≤ ((kTau τ : ℝ) + 1) * τ := by
  have h : 24 / τ ≤ kTau τ := Nat.le_ceil _
  have : 24 ≤ (kTau τ : ℝ) * τ := by rwa [div_le_iff₀ hτ] at h
  nlinarith

/-! ## The envelopes and the event bundles -/

/-- The rough envelope of the integrand: `|F| ≤ Λ_e N^{q_e} (1 + ‖X‖_F²)^{q_e}`. -/
private theorem claimT_envF {τ : ℝ} (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (i : Fin M) (μ : Fin N) {p : ℕ} (ns : Fin p → ℕ)
    (ws : ∀ r, Word (ns r)) (σs : ∀ r, Fin (ns r + 1) → Fin 3) (cs : Fin p → Bool)
    (hns : ∑ r, ns r = 3) (hv : ∀ r, tagV (σs r) = 0) {R KP cR Λe : ℝ} {qe : ℕ}
    (hR1 : 1 ≤ R) (hKP0 : 0 ≤ KP) (hcR0 : 0 ≤ cR) (hτ0 : 0 ≤ τ⁻¹) (hN1r : (1 : ℝ) ≤ N)
    (hRGmu : ∀ s t, ‖Gmu Sig A z μ s t‖ ≤ R) (hRG : ∀ s t, ‖G Sig A z s t‖ ≤ R)
    (hPi : ∀ s t, ‖PiZ N Sig z s t‖ ≤ KP) (hRN : R ≤ cR * N)
    (hsqV : 1 + claimT_V A μ ≤ 2 * τ⁻¹ * N * (1 + claimT_sq A))
    (hqe1 : 4 * (p + 3) ≤ qe) (hqe2 : 12 * (p + 3) ≤ qe)
    (hΛe : ((cR + KP) * (1 + cR) * (2 * τ⁻¹)) ^ (4 * (p + 3)) ≤ Λe) :
    ‖claimT_F Sig A z i μ ns ws σs cs‖ ≤ Λe * (N : ℝ) ^ qe * (1 + claimT_sq A) ^ qe := by
  have h := claimT_F_rough Sig A z i μ hR1 hKP0 hRGmu hRG hPi ns ws σs cs hns hv
  have hV := claimT_V_nonneg A μ
  have hsq := claimT_sq_nonneg A
  have hNp : (0 : ℝ) < N := by linarith
  set ΛW := (cR + KP) * (1 + cR) * (2 * τ⁻¹) with hΛW
  have hW : (R + KP) * (1 + R) * (1 + claimT_V A μ) ≤ ΛW * (N : ℝ) ^ 3 * (1 + claimT_sq A) := by
    have h1 : R + KP ≤ (cR + KP) * N := by nlinarith only [hRN, hN1r, hKP0, hcR0]
    have h2 : 1 + R ≤ (1 + cR) * N := by nlinarith only [hRN, hN1r, hcR0]
    calc (R + KP) * (1 + R) * (1 + claimT_V A μ)
        ≤ ((cR + KP) * N) * ((1 + cR) * N) * (2 * τ⁻¹ * N * (1 + claimT_sq A)) := by
          gcongr
      _ = ΛW * (N : ℝ) ^ 3 * (1 + claimT_sq A) := by rw [hΛW]; ring
  have hW0 : 0 ≤ (R + KP) * (1 + R) * (1 + claimT_V A μ) := by positivity
  have hΛW0 : 0 ≤ ΛW := by positivity
  have hsq1 : 0 ≤ 1 + claimT_sq A := by linarith only [hsq]
  have hN3 : (N : ℝ) ^ (3 * (4 * (p + 3))) ≤ (N : ℝ) ^ qe := pow_le_pow_right₀ hN1r (by omega)
  have hs1 : (1 + claimT_sq A) ^ (4 * (p + 3)) ≤ (1 + claimT_sq A) ^ qe :=
    pow_le_pow_right₀ (by linarith only [hsq]) hqe1
  calc ‖claimT_F Sig A z i μ ns ws σs cs‖
      ≤ ((R + KP) * (1 + R) * (1 + claimT_V A μ)) ^ (4 * (p + 3)) := h
    _ ≤ (ΛW * (N : ℝ) ^ 3 * (1 + claimT_sq A)) ^ (4 * (p + 3)) := pow_le_pow_left₀ hW0 hW _
    _ = ΛW ^ (4 * (p + 3)) * (N : ℝ) ^ (3 * (4 * (p + 3))) *
          (1 + claimT_sq A) ^ (4 * (p + 3)) := by rw [mul_pow, mul_pow, ← pow_mul]
    _ ≤ Λe * (N : ℝ) ^ qe * (1 + claimT_sq A) ^ qe :=
        mul_le_mul (mul_le_mul hΛe hN3 (by positivity) ((pow_nonneg hΛW0 _).trans hΛe)) hs1
          (by positivity) (mul_nonneg ((pow_nonneg hΛW0 _).trans hΛe) (by positivity))

/-- The envelope of the integrand with `G_μμ → P` on the `X^{(μ)}`-measurable event. -/
private theorem claimT_envFP {τ : ℝ} (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (i : Fin M) (μ : Fin N) (Kx : ℕ) {p : ℕ}
    (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r)) (σs : ∀ r, Fin (ns r + 1) → Fin 3)
    (cs : Fin p → Bool) (hns : ∑ r, ns r = 3) (hv : ∀ r, tagV (σs r) = 0)
    {Kg KP CY Λe : ℝ} {qe : ℕ} (hKg1 : 1 ≤ Kg) (hKP0 : 0 ≤ KP) (hCY1 : 1 ≤ CY)
    (hτ0 : 0 ≤ τ⁻¹) (hN1r : (1 : ℝ) ≤ N) (hK : ∀ s t, ‖Gmu Sig A z μ s t‖ ≤ Kg)
    (hPi : ∀ s t, ‖PiZ N Sig z s t‖ ≤ KP) (hY : ∀ k, ‖calY z (Ymu Sig A z μ) Kx k‖ ≤ CY)
    (hsqV : 1 + claimT_V A μ ≤ 2 * τ⁻¹ * N * (1 + claimT_sq A))
    (hqe3 : (2 * Kx + 3) * (p + 3) ≤ qe)
    (hΛe : (((Kx : ℝ) + 1) * CY * (1 + Kg) ^ Kx) ^ (p + 3) *
      ((Kg + KP) * (1 + Kg)) ^ (3 * (p + 3)) * (2 * τ⁻¹) ^ ((2 * Kx + 3) * (p + 3)) ≤ Λe) :
    ‖claimT_FP Sig A z i μ Kx ns ws σs cs‖ ≤ Λe * (N : ℝ) ^ qe * (1 + claimT_sq A) ^ qe := by
  have h := claimT_FP_good Sig A z i μ Kx hKg1 hKP0 hCY1 hK hPi hY ns ws σs cs hns hv
  have hV := claimT_V_nonneg A μ
  have hsq := claimT_sq_nonneg A
  have hNp : (0 : ℝ) < N := by linarith
  have hsq1 : 0 ≤ 1 + claimT_sq A := by linarith only [hsq]
  have hV1 : 0 ≤ 1 + claimT_V A μ := by linarith only [hV]
  obtain ⟨Λ₁, hΛ₁⟩ : ∃ Λ₁ : ℝ, Λ₁ = (((Kx : ℝ) + 1) * CY * (1 + Kg) ^ Kx) ^ (p + 3) *
      ((Kg + KP) * (1 + Kg)) ^ (3 * (p + 3)) := ⟨_, rfl⟩
  obtain ⟨q₁, hq₁⟩ : ∃ q₁ : ℕ, q₁ = (2 * Kx + 3) * (p + 3) := ⟨_, rfl⟩
  have e1 : (((Kx : ℝ) + 1) * CY * ((1 + Kg) * (1 + claimT_V A μ) ^ 2) ^ Kx) ^ (p + 3) *
      ((Kg + KP) * (1 + Kg) * (1 + claimT_V A μ)) ^ (3 * (p + 3)) =
      Λ₁ * (1 + claimT_V A μ) ^ q₁ := by
    have h1 : ((1 + Kg) * (1 + claimT_V A μ) ^ 2) ^ Kx =
        (1 + Kg) ^ Kx * (1 + claimT_V A μ) ^ (2 * Kx) := by rw [mul_pow, ← pow_mul]
    have h2 : (((Kx : ℝ) + 1) * CY * ((1 + Kg) ^ Kx * (1 + claimT_V A μ) ^ (2 * Kx))) ^ (p + 3) =
        (((Kx : ℝ) + 1) * CY * (1 + Kg) ^ Kx) ^ (p + 3) *
          (1 + claimT_V A μ) ^ (2 * Kx * (p + 3)) := by
      rw [← mul_assoc, mul_pow, ← pow_mul]
    have h3 : ((Kg + KP) * (1 + Kg) * (1 + claimT_V A μ)) ^ (3 * (p + 3)) =
        ((Kg + KP) * (1 + Kg)) ^ (3 * (p + 3)) * (1 + claimT_V A μ) ^ (3 * (p + 3)) :=
      mul_pow _ _ _
    rw [h1, h2, h3, mul_mul_mul_comm, ← pow_add, hΛ₁, hq₁]
    congr 2
    ring
  rw [← hΛ₁, ← hq₁] at hΛe
  rw [← hq₁] at hqe3
  have hΛ₁0 : 0 ≤ Λ₁ := by rw [hΛ₁]; positivity
  have hNq1 : (N : ℝ) ^ q₁ ≤ (N : ℝ) ^ qe := pow_le_pow_right₀ hN1r hqe3
  have hsq2 : (1 + claimT_sq A) ^ q₁ ≤ (1 + claimT_sq A) ^ qe :=
    pow_le_pow_right₀ (by linarith only [hsq]) hqe3
  have hΛ₁t : 0 ≤ Λ₁ * (2 * τ⁻¹) ^ q₁ := by positivity
  calc ‖claimT_FP Sig A z i μ Kx ns ws σs cs‖ ≤ _ := h
    _ = Λ₁ * (1 + claimT_V A μ) ^ q₁ := e1
    _ ≤ Λ₁ * (2 * τ⁻¹ * N * (1 + claimT_sq A)) ^ q₁ :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hV1 hsqV _) hΛ₁0
    _ = Λ₁ * (2 * τ⁻¹) ^ q₁ * (N : ℝ) ^ q₁ * (1 + claimT_sq A) ^ q₁ := by
        rw [mul_pow, mul_pow]; ring
    _ ≤ Λe * (N : ℝ) ^ qe * (1 + claimT_sq A) ^ qe :=
        mul_le_mul (mul_le_mul hΛe hNq1 (by positivity) (hΛ₁t.trans hΛe)) hsq2
          (by positivity) (mul_nonneg (hΛ₁t.trans hΛe) (by positivity))

/-- The consequences of the `X^{(μ)}`-measurable event used below. -/
private theorem claimT_good_bundle {τ c : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    {Sig : Matrix (Fin M) (Fin M) ℝ} {z : ℂ} (μ : Fin N) (A : Matrix (Fin M) (Fin N) ℝ)
    (Kx : ℕ) {Cm β b : ℝ} (hCm : 0 < Cm)
    (hm1 : Cm⁻¹ ≤ ‖mFun N (specOf Sig) z‖) (hm2 : ‖mFun N (specOf Sig) z‖ ≤ Cm)
    (hM : (M : ℝ) ≤ τ⁻¹ * N)
    (htr : (N : ℂ)⁻¹ * ∑ j, PiZ N Sig z (Sum.inl j) (Sum.inl j) =
      -z - (mFun N (specOf Sig) z)⁻¹)
    (hPi : ∀ s t, ‖PiZ N Sig z s t‖ ≤ τ⁻¹ * c⁻¹ + Cm)
    (hrow : ∀ j, ∑ l, ‖PiZ N Sig z (Sum.inl j) (Sum.inl l)‖ ^ 2 ≤ (τ⁻¹ * c⁻¹) ^ 2)
    (hcol : ∀ j, ∑ l, ‖PiZ N Sig z (Sum.inl l) (Sum.inl j)‖ ^ 2 ≤ (τ⁻¹ * c⁻¹) ^ 2)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hβb : 2 * τ⁻¹ * β ≤ b)
    (hNb : 4 * τ⁻¹ * (τ⁻¹ * c⁻¹) ^ 2 ≤ N * b ^ 2) (hεm : τ⁻¹ * β ≤ (2 * Cm)⁻¹)
    (hz2 : ‖z‖ ≤ 2 * τ⁻¹) (hG : claimT_Good Sig A z μ β) :
    (∀ s t, ‖Gmu Sig A z μ s t‖ ≤ τ⁻¹ * c⁻¹ + Cm + 1) ∧
    (∀ ν, ν ≠ μ → ∀ j, ‖Gmu Sig A z μ (Sum.inr ν) (Sum.inl j)‖ ≤ b ∧
      ‖Gmu Sig A z μ (Sum.inl j) (Sum.inr ν)‖ ≤ b) ∧
    (∀ i, (∑ j, ‖Gmu Sig A z μ (Sum.inl i) (Sum.inl j)‖ ≤ N * b) ∧
      (∑ j, ‖Gmu Sig A z μ (Sum.inl j) (Sum.inl i)‖ ≤ N * b) ∧
      (∑ j, ‖Gmu Sig A z μ (Sum.inl i) (Sum.inl j)‖ ^ 2 ≤ N * b ^ 2) ∧
      (∑ j, ‖Gmu Sig A z μ (Sum.inl j) (Sum.inl i)‖ ^ 2 ≤ N * b ^ 2)) ∧
    (∀ k, ‖calY z (Ymu Sig A z μ) Kx k‖ ≤ ((Kx : ℝ) + 1) * (2 * Cm + 1) ^ (Kx + 1) * 2 ^ Kx *
      (2 * τ⁻¹ + Cm + (2 * Cm)⁻¹ + 1) ^ Kx) ∧
    ‖claimT_Shat Sig A z μ‖ ≤ 1 ∧
    ‖Ymu Sig A z μ - (-z - (mFun N (specOf Sig) z)⁻¹)‖ ≤ τ⁻¹ * β := by
  have hτi : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  obtain ⟨he1, he2⟩ := claimT_good_entries hG hβ0 hPi
  have hY := claimT_good_Y hG hβ0 hM htr
  obtain ⟨hinv, hYb⟩ := claimT_inv_bound hCm hm1 hm2 hY hεm
  have hβb' : β ≤ b := (le_mul_of_one_le_left hβ0 (by linarith only [hτi])).trans hβb
  have hYb' : ‖Ymu Sig A z μ‖ ≤ 2 * τ⁻¹ + Cm + (2 * Cm)⁻¹ :=
    hYb.trans (by linarith only [hz2])
  exact ⟨fun s t => (he1 s t).trans (by linarith only [hβ1]), fun ν hν j =>
    ⟨((he2 ν hν j).1).trans hβb', ((he2 ν hν j).2).trans hβb'⟩,
    fun i => claimT_good_sums hτ hτ1 hG hβ0 hβb hM hNb hrow hcol i,
    fun k => claimT_calY_le hinv hYb' Kx k, (claimT_Shat_good hG hβ0).trans hβ1, hY⟩

/-- The consequences of the a priori event used below. -/
private theorem claimT_event_bundle {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (μ : Fin N) {Cm b₀ : ℝ}
    (hCm : 0 < Cm) (hm1 : Cm⁻¹ ≤ ‖mFun N (specOf Sig) z‖) (hb₀1 : b₀ ≤ 1)
    (hb₀m : b₀ ≤ (2 * Cm)⁻¹) (hNi : (N : ℝ)⁻¹ * b₀ ≤ Cm * b₀ ^ 2)
    (hG : ∀ s t, ‖G Sig A z s t - PiZ N Sig z s t‖ ≤ b₀) :
    1 ≤ 2 * Cm * ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖ ∧
    claimT_Good Sig A z μ ((1 + 2 * Cm) * b₀) ∧
    ‖claimT_Shat Sig A z μ‖ ≤ Ft Sig A z + (Cm + 2 * Cm) * b₀ ^ 2 := by
  have hgm : ‖G Sig A z (Sum.inr μ) (Sum.inr μ) - mFun N (specOf Sig) z‖ ≤ b₀ := by
    simpa [PiZ, piMat] using hG (Sum.inr μ) (Sum.inr μ)
  have hμ : 1 ≤ 2 * Cm * ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖ := by
    have h1 := norm_sub_norm_le (mFun N (specOf Sig) z) (G Sig A z (Sum.inr μ) (Sum.inr μ))
    rw [norm_sub_rev] at h1
    have h2 : (2 * Cm)⁻¹ = Cm⁻¹ - (2 * Cm)⁻¹ := by field_simp; ring
    have h3 : (2 * Cm)⁻¹ ≤ ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖ := by
      linarith only [h1, h2, hm1, hgm, hb₀m]
    calc (1 : ℝ) = 2 * Cm * (2 * Cm)⁻¹ := by field_simp
      _ ≤ 2 * Cm * ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖ :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
  refine ⟨hμ, claimT_Good_of_event hSig A hz μ hb₀1 (by positivity) hG hμ, ?_⟩
  have h := claimT_Shat_event hSig A hz μ hG hμ
  nlinarith only [h, hNi]

/-! ## (avg_step 1) at one `(i, μ)` -/

/-- (avg_step 1) at one `(i, μ)`: the main part (A+_avg), the remainder of `G_μμ → P` on the a
priori event, and the off-event part. -/
private theorem claimT_per {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {C : ℕ → ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X)
    {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {z : ℂ} (hz : 0 < z.im) (i : Fin M)
    (μ : Fin N) (Kx : ℕ) {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r))
    (σs : ∀ r, Fin (ns r + 1) → Fin 3) (cs : Fin p → Bool) (hns : ∑ r, ns r = 3)
    (hv : ∀ r, tagV (σs r) = 0) {Cm β b b₀ c₂ Cpt PΞ Kg ε s : ℝ} {Dr : ℕ}
    (Ξ : Set Ω) (Env : Matrix (Fin M) (Fin N) ℝ → ℝ)
    (hCm : 0 < Cm) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hb₀ : 0 ≤ b₀) (hbb : b₀ ≤ b) (hb₀1 : b₀ ≤ 1)
    (hb₀m : b₀ ≤ (2 * Cm)⁻¹) (hLb : 2 * Cm * b₀ ≤ b) (hKg1 : 1 ≤ Kg) (hc₂ : 0 ≤ c₂)
    (hCpt : 0 ≤ Cpt) (hs : 0 < s)
    (hm1 : Cm⁻¹ ≤ ‖mFun N (specOf Sig) z‖) (hm2 : ‖mFun N (specOf Sig) z‖ ≤ Cm)
    (hε : ε ≤ (2 * Cm)⁻¹) (hθ : 2 * Cm * (2 * Cm ^ 2 * b₀ + ε) ≤ 1)
    (hrem : ((p : ℝ) + 3) * (2 * (Cm + 1)) ^ (p + 3) * (Cm + 1) *
      (2 * Cm * (2 * Cm ^ 2 * b₀ + ε)) ^ (Kx + 1) ≤ (N : ℝ) ^ (-(1 : ℝ) / 2))
    (hPΞ : (ℙ Ξᶜ).toReal ≤ PΞ)
    (hΞ : ∀ ω ∈ Ξ, (∀ s t, ‖G Sig (X ω) z s t - PiZ N Sig z s t‖ ≤ b₀) ∧
      1 ≤ 2 * Cm * ‖G Sig (X ω) z (Sum.inr μ) (Sum.inr μ)‖ ∧ claimT_Good Sig (X ω) z μ β ∧
      ‖claimT_Shat Sig (X ω) z μ‖ ≤ Ft Sig (X ω) z + c₂ * b₀ ^ 2)
    (hgood : ∀ A, claimT_Good Sig A z μ β → (∀ s t, ‖Gmu Sig A z μ s t‖ ≤ Kg) ∧
      (∀ ν, ν ≠ μ → ∀ j, ‖Gmu Sig A z μ (Sum.inr ν) (Sum.inl j)‖ ≤ b ∧
        ‖Gmu Sig A z μ (Sum.inl j) (Sum.inr ν)‖ ≤ b) ∧
      ‖claimT_Shat Sig A z μ‖ ≤ 1 ∧
      ‖Ymu Sig A z μ - (-z - (mFun N (specOf Sig) z)⁻¹)‖ ≤ ε)
    (hmain : ∀ A, claimT_Good Sig A z μ β →
      ‖∫ y, claimT_FP Sig (updCol A μ y) z i μ Kx ns ws σs cs ∂(colLaw X μ)‖ ≤
        Cpt * (2 * ‖claimT_Shat Sig A z μ‖) ^
          (Finset.univ.filter fun r => ns r = 0 ∧ tagMu (σs r) = 0).card *
        (N : ℝ) ^ (-(1 : ℝ) / 2) *
        b ^ (2 * (p - (Finset.univ.filter fun r => ns r = 0 ∧ tagMu (σs r) = 0).card)))
    (hEnvI : Integrable fun ω => Env (X ω)) (hEnv0 : ∀ A, 0 ≤ Env A)
    (hEnvF : ∀ A, ‖claimT_F Sig A z i μ ns ws σs cs‖ ≤ Env A)
    (hEnvFP : ∀ A, claimT_Good Sig A z μ β → ‖claimT_FP Sig A z i μ Kx ns ws σs cs‖ ≤ Env A)
    (hEnv2I : Integrable fun ω => (2 * Env (X ω)) ^ 2)
    (hEnv2 : ∫ ω, (2 * Env (X ω)) ^ 2 ≤ (N : ℝ) ^ Dr)
    (hFtI : Integrable fun ω => Ft Sig (X ω) z ^ p) :
    ‖∫ ω, claimT_F Sig (X ω) z i μ ns ws σs cs‖ ≤
      Cpt * (N : ℝ) ^ (-(1 : ℝ) / 2) * ((1 + (4 * c₂) ^ p) * (b ^ 2) ^ p +
          4 ^ p * ∫ ω, Ft Sig (X ω) z ^ p) + Cpt * 2 ^ p * PΞ +
        ((N : ℝ) ^ (-(1 : ℝ) / 2) * Kg ^ (4 * p) * ((b ^ 2) ^ p +
          2 ^ p * ((∫ ω, Ft Sig (X ω) z ^ p) + (c₂ * b₀ ^ 2) ^ p)) +
          s * (N : ℝ) ^ Dr + PΞ * (4 * s)⁻¹) := by
  set e := (N : ℝ) ^ (-(1 : ℝ) / 2) with he
  have he0 : 0 ≤ e := Real.rpow_nonneg (Nat.cast_nonneg _) _
  set R0 := Finset.univ.filter fun r => ns r = 0 ∧ tagMu (σs r) = 0 with hR0
  set j := R0.card with hj
  have hjp : j ≤ p := by
    calc j ≤ (Finset.univ : Finset (Fin p)).card := Finset.card_filter_le _ _
      _ = p := by simp
  have hXm : Measurable X :=
    measurable_pi_iff.2 fun j => measurable_pi_iff.2 fun ν => hX.measurable j ν
  -- the two parts
  set F₁ : Ω → ℂ := fun ω => if claimT_Good Sig (X ω) z μ β then
    claimT_FP Sig (X ω) z i μ Kx ns ws σs cs else 0 with hF₁
  have hT1 := claimT_T1 hX hSig hz i μ Kx ns ws σs cs Ξ Env hb0 hb1 hb₀ hbb hc₂ hCpt hmain
    (fun A hA => (hgood A hA).2.2.1) (fun ω hω => ⟨(hΞ ω hω).2.2.1, (hΞ ω hω).2.2.2⟩) hPΞ
    hEnvI hEnv0 hEnvFP hFtI
  have hGm := claimT_meas_Good (N := N) hSig hz μ β
  have hFm : Measurable fun ω => claimT_F Sig (X ω) z i μ ns ws σs cs :=
    (claimT_cont_F hSig hz i μ ns ws σs cs).measurable.comp hXm
  have hF₁m : Measurable F₁ :=
    (Measurable.ite hGm (claimT_cont_FP hSig hz i μ ns ws σs cs Kx).measurable
      measurable_const).comp hXm
  have hFi : Integrable fun ω => claimT_F Sig (X ω) z i μ ns ws σs cs :=
    hEnvI.mono' hFm.aestronglyMeasurable (ae_of_all _ fun ω => hEnvF _)
  have hF₁b : ∀ ω, ‖F₁ ω‖ ≤ Env (X ω) := fun ω => by
    simp only [hF₁]
    split_ifs with h
    · exact hEnvFP _ h
    · rw [norm_zero]; exact hEnv0 _
  have hF₁i : Integrable F₁ :=
    hEnvI.mono' hF₁m.aestronglyMeasurable (ae_of_all _ hF₁b)
  set Rf : Ω → ℂ := fun ω => claimT_F Sig (X ω) z i μ ns ws σs cs - F₁ ω with hRf
  have hRi : Integrable Rf := hFi.sub hF₁i
  have hRb : ∀ ω, ‖Rf ω‖ ≤ 2 * Env (X ω) := fun ω => by
    simp only [hRf]
    calc _ ≤ ‖claimT_F Sig (X ω) z i μ ns ws σs cs‖ + ‖F₁ ω‖ := norm_sub_le _ _
      _ ≤ Env (X ω) + Env (X ω) := add_le_add (hEnvF _) (hF₁b ω)
      _ = 2 * Env (X ω) := by ring
  have hR2i : Integrable fun ω => ‖Rf ω‖ ^ 2 :=
    hEnv2I.mono' (hRi.1.norm.pow 2) (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hRb ω) 2)
  have hR2 : ∫ ω, ‖Rf ω‖ ^ 2 ≤ (N : ℝ) ^ Dr :=
    (integral_mono hR2i hEnv2I fun ω => pow_le_pow_left₀ (norm_nonneg _) (hRb ω) 2).trans hEnv2
  -- the remainder on the a priori event
  set g : Ω → ℝ := fun ω => e * Kg ^ (4 * p) * ((b ^ 2) ^ p +
    2 ^ p * (Ft Sig (X ω) z ^ p + (c₂ * b₀ ^ 2) ^ p)) with hg
  have hF0 : ∀ ω, 0 ≤ Ft Sig (X ω) z := fun ω => norm_nonneg _
  have hg0 : ∀ ω, 0 ≤ g ω := fun ω => by have := hF0 ω; simp only [hg]; positivity
  have hgi : Integrable g :=
    ((integrable_const _).add ((hFtI.add (integrable_const _)).const_mul _)).const_mul _
  have hon : ∀ ω ∈ Ξ, ‖Rf ω‖ ≤ g ω := by
    intro ω hω
    obtain ⟨hG, hμ, hGood, hS⟩ := hΞ ω hω
    obtain ⟨hK, hGν, -, hY⟩ := hgood _ hGood
    have hR : Rf ω = claimT_F Sig (X ω) z i μ ns ws σs cs -
        claimT_FP Sig (X ω) z i μ Kx ns ws σs cs := by
      simp only [hRf, hF₁, hGood, ite_true]
    obtain ⟨hgB, hPB, hgP⟩ := claimT_gP hSig (X ω) hz μ Kx hCm hG hm1 hm2 hb₀1 hb₀m hY hε hθ
    have hB1 : 1 ≤ 2 * (Cm + 1) := by linarith only [hCm]
    have h1 := claimT_rem_point Sig (X ω) z i μ Kx ns ws σs cs hns hB1
      (hgB.trans (by linarith only [hCm])) hPB
    have h2 := claimT_prodH_event hSig (X ω) hz i μ hG hμ hKg1 hb0 hb1 hLb hK hGν ns ws σs cs
      hns hv
    have hS0 := norm_nonneg (claimT_Shat Sig (X ω) z μ)
    have hprod0 : 0 ≤ ∏ r, ‖claimT_H Sig (X ω) z i μ ns ws σs cs r‖ :=
      Finset.prod_nonneg fun _ _ => norm_nonneg _
    have hε0 : 0 ≤ ε := (norm_nonneg _).trans hY
    have hθ0 : 0 ≤ 2 * Cm * (2 * Cm ^ 2 * b₀ + ε) := by positivity
    have hy : ‖claimT_Shat Sig (X ω) z μ‖ ^ j * (Kg ^ 4 * b ^ 2) ^ (p - j) ≤
        Kg ^ (4 * p) * ((b ^ 2) ^ p + (Ft Sig (X ω) z + c₂ * b₀ ^ 2) ^ p) := by
      have hx0 : 0 ≤ Ft Sig (X ω) z + c₂ * b₀ ^ 2 := by have := hF0 ω; positivity
      calc ‖claimT_Shat Sig (X ω) z μ‖ ^ j * (Kg ^ 4 * b ^ 2) ^ (p - j)
          ≤ (Ft Sig (X ω) z + c₂ * b₀ ^ 2) ^ j * (Kg ^ 4 * b ^ 2) ^ (p - j) := by
            gcongr
        _ = Kg ^ (4 * (p - j)) * ((b ^ 2) ^ (p - j) * (Ft Sig (X ω) z + c₂ * b₀ ^ 2) ^ j) := by
            rw [mul_pow, ← pow_mul]; ring
        _ ≤ Kg ^ (4 * p) * ((b ^ 2) ^ p + (Ft Sig (X ω) z + c₂ * b₀ ^ 2) ^ p) :=
            mul_le_mul (pow_le_pow_right₀ hKg1 (by omega))
              (claimT_young (by positivity) hx0 hjp) (by positivity) (by positivity)
    have hy2 : (Ft Sig (X ω) z + c₂ * b₀ ^ 2) ^ p ≤
        2 ^ p * (Ft Sig (X ω) z ^ p + (c₂ * b₀ ^ 2) ^ p) :=
      claimT_pow_add_le (hF0 ω) (by positivity) p
    rw [hR]
    calc ‖claimT_F Sig (X ω) z i μ ns ws σs cs - claimT_FP Sig (X ω) z i μ Kx ns ws σs cs‖
        ≤ ((p : ℝ) + 3) * (2 * (Cm + 1)) ^ (p + 3) *
            ‖G Sig (X ω) z (Sum.inr μ) (Sum.inr μ) - ∑ k ∈ Finset.range (Kx + 1),
              calY z (Ymu Sig (X ω) z μ) Kx k * Qmu Sig (X ω) z μ ^ k‖ *
            ∏ r, ‖claimT_H Sig (X ω) z i μ ns ws σs cs r‖ := h1
      _ ≤ ((p : ℝ) + 3) * (2 * (Cm + 1)) ^ (p + 3) *
            ((Cm + 1) * (2 * Cm * (2 * Cm ^ 2 * b₀ + ε)) ^ (Kx + 1)) *
            (‖claimT_Shat Sig (X ω) z μ‖ ^ j * (Kg ^ 4 * b ^ 2) ^ (p - j)) := by
          gcongr
      _ = (((p : ℝ) + 3) * (2 * (Cm + 1)) ^ (p + 3) * (Cm + 1) *
            (2 * Cm * (2 * Cm ^ 2 * b₀ + ε)) ^ (Kx + 1)) *
            (‖claimT_Shat Sig (X ω) z μ‖ ^ j * (Kg ^ 4 * b ^ 2) ^ (p - j)) := by ring
      _ ≤ e * (Kg ^ (4 * p) * ((b ^ 2) ^ p + (Ft Sig (X ω) z + c₂ * b₀ ^ 2) ^ p)) :=
          mul_le_mul hrem hy (by positivity) he0
      _ ≤ g ω := by
          simp only [hg]
          have : 0 ≤ Kg ^ (4 * p) := by positivity
          calc e * (Kg ^ (4 * p) * ((b ^ 2) ^ p + (Ft Sig (X ω) z + c₂ * b₀ ^ 2) ^ p))
              ≤ e * (Kg ^ (4 * p) * ((b ^ 2) ^ p +
                  2 ^ p * (Ft Sig (X ω) z ^ p + (c₂ * b₀ ^ 2) ^ p))) := by gcongr
            _ = _ := by ring
  have hsplit := claimT_split hs hRi.norm hR2i hgi hg0 hon
  have hgv : ∫ ω, g ω = e * Kg ^ (4 * p) * ((b ^ 2) ^ p +
      2 ^ p * ((∫ ω, Ft Sig (X ω) z ^ p) + (c₂ * b₀ ^ 2) ^ p)) := by
    simp only [hg]
    rw [integral_const_mul]
    congr 1
    have hI : Integrable fun ω => (2 : ℝ) ^ p * (Ft Sig (X ω) z ^ p + (c₂ * b₀ ^ 2) ^ p) :=
      (hFtI.add (integrable_const _)).const_mul _
    rw [integral_add (integrable_const _) hI, integral_const_mul,
      integral_add hFtI (integrable_const _)]
    simp
  have hFeq : (fun ω => claimT_F Sig (X ω) z i μ ns ws σs cs) = fun ω => F₁ ω + Rf ω := by
    funext ω; simp only [hRf]; ring
  rw [hFeq, integral_add hF₁i hRi]
  refine (norm_add_le _ _).trans (add_le_add hT1 ?_)
  refine hsplit.trans ?_
  rw [hgv]
  gcongr

/-! ## The choice of `N₀` and the scalar conditions -/

/-- Eventually `A ≤ N^{τ/16}`, `B ≤ N` and `2 ≤ N`. -/
private theorem claimT_large {τ : ℝ} (hτ : 0 < τ) (A B : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, A ≤ (N : ℝ) ^ (τ / 16) ∧ B ≤ N ∧ 2 ≤ N := by
  refine ⟨⌈max A 0 ^ (16 / τ)⌉₊ + ⌈B⌉₊ + 2, fun N hN => ⟨?_, ?_, by omega⟩⟩
  · have hA0 : 0 ≤ max A 0 := le_max_right _ _
    have h1 : max A 0 ^ (16 / τ) ≤ (N : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈max A 0 ^ (16 / τ)⌉₊ ≤ N by omega))
    have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hA0 _) h1 (by positivity : 0 ≤ τ / 16)
    rw [← Real.rpow_mul hA0, show 16 / τ * (τ / 16) = 1 by field_simp, Real.rpow_one] at h2
    exact (le_max_left _ _).trans h2
  · exact (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈B⌉₊ ≤ N by omega))

/-- The scalar conditions of (avg_step 1) at one `N ≥ N₀`, for `b₀ = τ⁻² N^{ε_a} Ψ`,
`b = K_b b₀`, `β = (1 + 2C_m) b₀` and `ε = τ⁻¹ β`: `b ≤ 1`, the conditions of the expansion of
`G_μμ` with remainder `≤ N^{−1/2}`, `N⁻¹ ≤ C_m b₀`, `N b² ≥ 4τ⁻³c⁻²` and `b₀² ≤ τ⁻⁴ N^δ Ψ²`. -/
private theorem claimT_scal {τ c εa δ Cm Kb Kθ Kc B₀ Crem Ψ b₀ : ℝ} {p N : ℕ} (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (hc : 0 < c) (hp2 : 2 ≤ p) (hεa : 0 < εa) (hεaτ : 16 * εa ≤ τ)
    (hεaδ : 20 * p * εa ≤ δ) (hcm : 0 < Cm) (hCm1 : 1 ≤ Cm)
    (hKb : Kb = 2 * τ⁻¹ * (1 + 2 * Cm) + 2 * Cm + 1 + 2 * (Cm + 1) * c⁻¹)
    (hKθ : Kθ = 2 * Cm * (2 * Cm ^ 2 + τ⁻¹ * (1 + 2 * Cm)))
    (hKc : Kc = Kb + 2 * Cm * (τ⁻¹ * (1 + 2 * Cm)) + Kθ + (1 + 2 * Cm))
    (hB₀ : B₀ = τ⁻¹ ^ 2 * (Real.sqrt Cm + 1))
    (hCrem : Crem = ((p : ℝ) + 3) * (2 * (Cm + 1)) ^ (p + 3) * (Cm + 1))
    (hN2 : 2 ≤ N) (hNa : Kc * B₀ ≤ (N : ℝ) ^ (τ / 16)) (hNb : Crem ≤ N)
    (hΨge : τ / N ≤ Ψ) (hΨdec : Ψ ≤ (Real.sqrt Cm + 1) * (N : ℝ) ^ (-τ / 2))
    (hΨsq : (Cm * N)⁻¹ ≤ Ψ ^ 2) (hb₀ : b₀ = τ⁻¹ ^ 2 * (N : ℝ) ^ εa * Ψ) :
    0 ≤ b₀ ∧ b₀ ≤ Kb * b₀ ∧ 0 ≤ Kb * b₀ ∧ Kb * b₀ ≤ 1 ∧ b₀ ≤ 1 ∧ b₀ ≤ (2 * Cm)⁻¹ ∧
    2 * Cm * b₀ ≤ Kb * b₀ ∧ 0 ≤ (1 + 2 * Cm) * b₀ ∧ (1 + 2 * Cm) * b₀ ≤ 1 ∧
    2 * τ⁻¹ * ((1 + 2 * Cm) * b₀) ≤ Kb * b₀ ∧ τ⁻¹ * ((1 + 2 * Cm) * b₀) ≤ (2 * Cm)⁻¹ ∧
    2 * Cm * (2 * Cm ^ 2 * b₀ + τ⁻¹ * ((1 + 2 * Cm) * b₀)) ≤ 1 ∧
    ((p : ℝ) + 3) * (2 * (Cm + 1)) ^ (p + 3) * (Cm + 1) *
      (2 * Cm * (2 * Cm ^ 2 * b₀ + τ⁻¹ * ((1 + 2 * Cm) * b₀))) ^ (kTau τ + 1) ≤
        (N : ℝ) ^ (-(1 : ℝ) / 2) ∧
    (N : ℝ)⁻¹ * b₀ ≤ Cm * b₀ ^ 2 ∧ 4 * τ⁻¹ * (τ⁻¹ * c⁻¹) ^ 2 ≤ N * (Kb * b₀) ^ 2 ∧
    b₀ ^ 2 ≤ τ⁻¹ ^ 4 * ((N : ℝ) ^ δ * Ψ ^ 2) := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN0 : (0 : ℝ) < N := by linarith
  have hτi : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  have hτ0 : 0 ≤ τ⁻¹ := by positivity
  have hc0 : 0 ≤ c⁻¹ := by positivity
  have hA2 : 0 ≤ 2 * (Cm + 1) * c⁻¹ := mul_nonneg (by linarith) hc0
  have hKb1 : 1 ≤ Kb := by
    rw [hKb]
    have : 0 ≤ 2 * τ⁻¹ * (1 + 2 * Cm) := mul_nonneg (by positivity) (by linarith)
    linarith
  have hKb0 : 0 ≤ Kb := by linarith
  have hKb2 : 2 * Cm ≤ Kb := by
    rw [hKb]
    have : 0 ≤ 2 * τ⁻¹ * (1 + 2 * Cm) := mul_nonneg (by positivity) (by linarith)
    linarith
  have hKb3 : 2 * τ⁻¹ * (1 + 2 * Cm) ≤ Kb := by rw [hKb]; linarith
  have hKb4 : 2 * (Cm + 1) * c⁻¹ ≤ Kb := by
    rw [hKb]
    have : 0 ≤ 2 * τ⁻¹ * (1 + 2 * Cm) := mul_nonneg (by positivity) (by linarith)
    linarith
  have hKθ0 : 0 ≤ Kθ := by
    rw [hKθ]
    exact mul_nonneg (by linarith) (add_nonneg (by positivity) (mul_nonneg hτ0 (by linarith)))
  have hA3 : 0 ≤ 2 * Cm * (τ⁻¹ * (1 + 2 * Cm)) :=
    mul_nonneg (by linarith) (mul_nonneg hτ0 (by linarith))
  have hKc1 : Kb ≤ Kc := by rw [hKc]; linarith
  have hKc2 : 2 * Cm * (τ⁻¹ * (1 + 2 * Cm)) ≤ Kc := by rw [hKc]; linarith
  have hKc3 : Kθ ≤ Kc := by rw [hKc]; linarith
  have hKc4 : 1 + 2 * Cm ≤ Kc := by rw [hKc]; linarith
  have hKc0 : 0 ≤ Kc := by linarith
  have hΨpos : 0 < Ψ := lt_of_lt_of_le (by positivity) hΨge
  have hNεa : 1 ≤ (N : ℝ) ^ εa := Real.one_le_rpow hN1r hεa.le
  have hb₀0 : 0 ≤ b₀ := by rw [hb₀]; positivity
  have hΨb : τ⁻¹ ^ 2 * Ψ ≤ b₀ := by
    rw [hb₀, mul_right_comm]
    exact le_mul_of_one_le_right (by positivity) hNεa
  obtain ⟨ρ, hρ⟩ : ∃ x : ℝ, x = (N : ℝ) ^ (-τ / 16) := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρ]; exact Real.rpow_pos_of_pos hN0 _
  have hρ1 : ρ ≤ 1 := by
    rw [hρ]; exact Real.rpow_le_one_of_one_le_of_nonpos hN1r (by linarith)
  have hρinv : (N : ℝ) ^ (τ / 16) * ρ = 1 := by
    rw [hρ, ← Real.rpow_add hN0, show τ / 16 + -τ / 16 = 0 by ring, Real.rpow_zero]
  have hb₀ρ : b₀ ≤ B₀ * ρ ^ 7 := by
    have h7 : ρ ^ 7 = (N : ℝ) ^ (-7 * τ / 16) := by
      rw [hρ, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
    have hexp : (N : ℝ) ^ εa * (N : ℝ) ^ (-τ / 2) ≤ (N : ℝ) ^ (-7 * τ / 16) := by
      rw [← Real.rpow_add hN0]
      exact Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
    rw [hB₀, h7, hb₀]
    calc τ⁻¹ ^ 2 * (N : ℝ) ^ εa * Ψ
        ≤ τ⁻¹ ^ 2 * (N : ℝ) ^ εa * ((Real.sqrt Cm + 1) * (N : ℝ) ^ (-τ / 2)) :=
          mul_le_mul_of_nonneg_left hΨdec (by positivity)
      _ = τ⁻¹ ^ 2 * (Real.sqrt Cm + 1) * ((N : ℝ) ^ εa * (N : ℝ) ^ (-τ / 2)) := by ring
      _ ≤ τ⁻¹ ^ 2 * (Real.sqrt Cm + 1) * (N : ℝ) ^ (-7 * τ / 16) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
  have hρ6 : ρ ^ 6 ≤ 1 := pow_le_one₀ hρ0.le hρ1
  have hKcb : Kc * b₀ ≤ ρ ^ 6 := by
    have hKcB : Kc * B₀ * ρ ≤ 1 := by
      calc Kc * B₀ * ρ ≤ (N : ℝ) ^ (τ / 16) * ρ := mul_le_mul_of_nonneg_right hNa hρ0.le
        _ = 1 := hρinv
    calc Kc * b₀ ≤ Kc * (B₀ * ρ ^ 7) := mul_le_mul_of_nonneg_left hb₀ρ hKc0
      _ = (Kc * B₀ * ρ) * ρ ^ 6 := by ring
      _ ≤ 1 * ρ ^ 6 := mul_le_mul_of_nonneg_right hKcB (by positivity)
      _ = ρ ^ 6 := one_mul _
  have hKcb1 : Kc * b₀ ≤ 1 := hKcb.trans hρ6
  have hbb : b₀ ≤ Kb * b₀ := le_mul_of_one_le_left hb₀0 hKb1
  have hb0 : 0 ≤ Kb * b₀ := mul_nonneg hKb0 hb₀0
  have hb1 : Kb * b₀ ≤ 1 := (mul_le_mul_of_nonneg_right hKc1 hb₀0).trans hKcb1
  have hLb : 2 * Cm * b₀ ≤ Kb * b₀ := mul_le_mul_of_nonneg_right hKb2 hb₀0
  have hb₀m : b₀ ≤ (2 * Cm)⁻¹ := by
    have : b₀ ≤ 1 / (2 * Cm) := (le_div_iff₀' (by linarith)).2 (hLb.trans hb1)
    rwa [one_div] at this
  have hβb : 2 * τ⁻¹ * ((1 + 2 * Cm) * b₀) ≤ Kb * b₀ := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hKb3 hb₀0
  have hε : τ⁻¹ * ((1 + 2 * Cm) * b₀) ≤ (2 * Cm)⁻¹ := by
    have h : 2 * Cm * (τ⁻¹ * ((1 + 2 * Cm) * b₀)) ≤ 1 := by
      have := (mul_le_mul_of_nonneg_right hKc2 hb₀0).trans hKcb1
      linarith [show 2 * Cm * (τ⁻¹ * ((1 + 2 * Cm) * b₀)) =
        2 * Cm * (τ⁻¹ * (1 + 2 * Cm)) * b₀ by ring]
    have : τ⁻¹ * ((1 + 2 * Cm) * b₀) ≤ 1 / (2 * Cm) := (le_div_iff₀' (by linarith)).2 h
    rwa [one_div] at this
  have hθe : 2 * Cm * (2 * Cm ^ 2 * b₀ + τ⁻¹ * ((1 + 2 * Cm) * b₀)) = Kθ * b₀ := by
    rw [hKθ]; ring
  have hθρ : 2 * Cm * (2 * Cm ^ 2 * b₀ + τ⁻¹ * ((1 + 2 * Cm) * b₀)) ≤ ρ ^ 6 := by
    rw [hθe]; exact (mul_le_mul_of_nonneg_right hKc3 hb₀0).trans hKcb
  have hθ0 : 0 ≤ 2 * Cm * (2 * Cm ^ 2 * b₀ + τ⁻¹ * ((1 + 2 * Cm) * b₀)) := by
    rw [hθe]; exact mul_nonneg hKθ0 hb₀0
  have hρpow : (ρ ^ 6) ^ (kTau τ + 1) ≤ (N : ℝ) ^ (-9 : ℝ) := by
    rw [← pow_mul, hρ, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    apply Real.rpow_le_rpow_of_exponent_le hN1r
    have hk := claimT_kTau hτ
    have e : ((6 * (kTau τ + 1) : ℕ) : ℝ) = 6 * ((kTau τ : ℝ) + 1) := by push_cast; ring
    rw [e]
    linarith only [hk, show -τ / 16 * (6 * ((kTau τ : ℝ) + 1)) =
      -(3 / 8) * (((kTau τ : ℝ) + 1) * τ) by ring]
  have hrem : ((p : ℝ) + 3) * (2 * (Cm + 1)) ^ (p + 3) * (Cm + 1) *
      (2 * Cm * (2 * Cm ^ 2 * b₀ + τ⁻¹ * ((1 + 2 * Cm) * b₀))) ^ (kTau τ + 1) ≤
        (N : ℝ) ^ (-(1 : ℝ) / 2) := by
    rw [← hCrem]
    calc Crem * (2 * Cm * (2 * Cm ^ 2 * b₀ + τ⁻¹ * ((1 + 2 * Cm) * b₀))) ^ (kTau τ + 1)
        ≤ N * (N : ℝ) ^ (-9 : ℝ) :=
          mul_le_mul hNb ((pow_le_pow_left₀ hθ0 hθρ _).trans hρpow)
            (pow_nonneg hθ0 _) hN0.le
      _ = (N : ℝ) ^ ((1 : ℝ) + -9) := by rw [Real.rpow_add hN0, Real.rpow_one]
      _ ≤ (N : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hN1r (by norm_num)
  have hNib : (N : ℝ)⁻¹ * b₀ ≤ Cm * b₀ ^ 2 := by
    have h1 : (N : ℝ)⁻¹ ≤ b₀ := by
      have h3 : τ⁻¹ ^ 2 * (τ / N) = τ⁻¹ * (N : ℝ)⁻¹ := by field_simp
      have h4 : (N : ℝ)⁻¹ ≤ τ⁻¹ * (N : ℝ)⁻¹ := le_mul_of_one_le_left (by positivity) hτi
      calc (N : ℝ)⁻¹ ≤ τ⁻¹ ^ 2 * (τ / N) := h3 ▸ h4
        _ ≤ τ⁻¹ ^ 2 * Ψ := mul_le_mul_of_nonneg_left hΨge (by positivity)
        _ ≤ b₀ := hΨb
    calc (N : ℝ)⁻¹ * b₀ ≤ b₀ * b₀ := mul_le_mul_of_nonneg_right h1 hb₀0
      _ = 1 * b₀ ^ 2 := by ring
      _ ≤ Cm * b₀ ^ 2 := mul_le_mul_of_nonneg_right hCm1 (sq_nonneg _)
  have hNbb : 4 * τ⁻¹ * (τ⁻¹ * c⁻¹) ^ 2 ≤ N * (Kb * b₀) ^ 2 := by
    have h1 : Cm⁻¹ ≤ N * Ψ ^ 2 := by
      have := mul_le_mul_of_nonneg_left hΨsq hN0.le
      rwa [mul_inv, mul_left_comm, mul_inv_cancel₀ hN0.ne', mul_one] at this
    have h2 : Kb * τ⁻¹ ^ 2 * Ψ ≤ Kb * b₀ := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hΨb hKb0
    have h3 : (Kb * τ⁻¹ ^ 2) ^ 2 * Cm⁻¹ ≤ N * (Kb * b₀) ^ 2 := by
      calc (Kb * τ⁻¹ ^ 2) ^ 2 * Cm⁻¹ ≤ (Kb * τ⁻¹ ^ 2) ^ 2 * (N * Ψ ^ 2) :=
            mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
        _ = N * (Kb * τ⁻¹ ^ 2 * Ψ) ^ 2 := by ring
        _ ≤ N * (Kb * b₀) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h2 2) hN0.le
    have h5 : 4 * c⁻¹ ^ 2 ≤ Kb ^ 2 * Cm⁻¹ := by
      have h6 : (2 * (Cm + 1) * c⁻¹) ^ 2 ≤ Kb ^ 2 := pow_le_pow_left₀ hA2 hKb4 2
      have h7 : 4 * c⁻¹ ^ 2 * Cm ≤ Kb ^ 2 := by
        have : 4 * c⁻¹ ^ 2 * Cm ≤ (2 * (Cm + 1) * c⁻¹) ^ 2 := by
          nlinarith only [sq_nonneg c⁻¹, mul_nonneg (sq_nonneg c⁻¹) (sq_nonneg Cm),
            mul_nonneg (sq_nonneg c⁻¹) hcm.le]
        linarith only [this, h6]
      rw [← div_eq_mul_inv, le_div_iff₀ hcm]; exact h7
    have h6 : τ⁻¹ ^ 3 ≤ τ⁻¹ ^ 4 := pow_le_pow_right₀ hτi (by norm_num)
    have h8 : 4 * τ⁻¹ * (τ⁻¹ * c⁻¹) ^ 2 ≤ (Kb * τ⁻¹ ^ 2) ^ 2 * Cm⁻¹ := by
      calc 4 * τ⁻¹ * (τ⁻¹ * c⁻¹) ^ 2 = (4 * c⁻¹ ^ 2) * τ⁻¹ ^ 3 := by ring
        _ ≤ (Kb ^ 2 * Cm⁻¹) * τ⁻¹ ^ 4 :=
            mul_le_mul h5 h6 (by positivity) (mul_nonneg (sq_nonneg _) (inv_nonneg.2 hcm.le))
        _ = (Kb * τ⁻¹ ^ 2) ^ 2 * Cm⁻¹ := by ring
    linarith
  have hNδ : (N : ℝ) ^ εa * (N : ℝ) ^ εa ≤ (N : ℝ) ^ δ := by
    rw [← Real.rpow_add hN0]
    apply Real.rpow_le_rpow_of_exponent_le hN1r
    have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    have h40 : 40 * εa ≤ 20 * p * εa :=
      mul_le_mul_of_nonneg_right (by linarith only [hP]) hεa.le
    linarith only [h40, hεaδ, hεa]
  have hb₀sq : b₀ ^ 2 ≤ τ⁻¹ ^ 4 * ((N : ℝ) ^ δ * Ψ ^ 2) := by
    rw [hb₀]
    calc (τ⁻¹ ^ 2 * (N : ℝ) ^ εa * Ψ) ^ 2 =
          τ⁻¹ ^ 4 * ((N : ℝ) ^ εa * (N : ℝ) ^ εa * Ψ ^ 2) := by ring
      _ ≤ τ⁻¹ ^ 4 * ((N : ℝ) ^ δ * Ψ ^ 2) := by gcongr
  refine ⟨hb₀0, hbb, hb0, hb1, hbb.trans hb1, hb₀m, hLb, mul_nonneg (by linarith) hb₀0,
    (mul_le_mul_of_nonneg_right hKc4 hb₀0).trans hKcb1, hβb, hε, hθρ.trans hρ6, hrem, hNib,
    hNbb, hb₀sq⟩

/-- The final count at one `(i, μ)`: the bound of (avg_step 1) at the choices `s = N^{−D_r−p−1}`,
`P(Ξᶜ) ≤ N^{−D_r−4p−3}`, after `b₀² ≤ τ⁻⁴ N^δ Ψ²`. -/
private theorem claimT_tail {e Cpt c₂ Kg Kb b₀ τ Ψ δ EF : ℝ} {p N Dr : ℕ}
    (hN1 : (1 : ℝ) ≤ N) (he0 : 0 ≤ e) (hCpt0 : 0 ≤ Cpt) (hc₂0 : 0 ≤ c₂) (hKg0 : 0 ≤ Kg)
    (hb : b₀ ^ 2 ≤ τ⁻¹ ^ 4 * ((N : ℝ) ^ δ * Ψ ^ 2)) :
    Cpt * e * ((1 + (4 * c₂) ^ p) * ((Kb * b₀) ^ 2) ^ p + 4 ^ p * EF) +
        Cpt * 2 ^ p * ((N : ℝ) ^ (Dr + 4 * p + 3))⁻¹ +
      (e * Kg ^ (4 * p) * (((Kb * b₀) ^ 2) ^ p + 2 ^ p * (EF + (c₂ * b₀ ^ 2) ^ p)) +
        ((N : ℝ) ^ (Dr + p + 1))⁻¹ * (N : ℝ) ^ Dr +
        ((N : ℝ) ^ (Dr + 4 * p + 3))⁻¹ * (4 * ((N : ℝ) ^ (Dr + p + 1))⁻¹)⁻¹) ≤
      e * ((Cpt * (1 + (4 * c₂) ^ p) * (Kb ^ (2 * p) * τ⁻¹ ^ (4 * p)) +
            Kg ^ (4 * p) * (Kb ^ (2 * p) * τ⁻¹ ^ (4 * p)) +
            Kg ^ (4 * p) * 2 ^ p * (c₂ ^ p * τ⁻¹ ^ (4 * p))) *
          ((N : ℝ) ^ δ * Ψ ^ 2) ^ p +
        (Cpt * 4 ^ p + Kg ^ (4 * p) * 2 ^ p) * EF) +
      (Cpt * 2 ^ p + 2) * ((N : ℝ) ^ (p + 1))⁻¹ := by
  have hN0 : (0 : ℝ) < N := by linarith
  set W := ((N : ℝ) ^ δ * Ψ ^ 2) ^ p with hW
  have hbW : ((Kb * b₀) ^ 2) ^ p ≤ Kb ^ (2 * p) * τ⁻¹ ^ (4 * p) * W := by
    calc ((Kb * b₀) ^ 2) ^ p ≤ (Kb ^ 2 * (τ⁻¹ ^ 4 * ((N : ℝ) ^ δ * Ψ ^ 2))) ^ p := by
          rw [mul_pow]; gcongr
      _ = Kb ^ (2 * p) * τ⁻¹ ^ (4 * p) * W := by
          rw [hW, mul_pow, mul_pow, ← pow_mul, ← pow_mul]; ring
  have hcW : (c₂ * b₀ ^ 2) ^ p ≤ c₂ ^ p * τ⁻¹ ^ (4 * p) * W := by
    calc (c₂ * b₀ ^ 2) ^ p ≤ (c₂ * (τ⁻¹ ^ 4 * ((N : ℝ) ^ δ * Ψ ^ 2))) ^ p := by gcongr
      _ = c₂ ^ p * τ⁻¹ ^ (4 * p) * W := by rw [hW, mul_pow, mul_pow, ← pow_mul]; ring
  have hoff : Cpt * 2 ^ p * ((N : ℝ) ^ (Dr + 4 * p + 3))⁻¹ +
      ((N : ℝ) ^ (Dr + p + 1))⁻¹ * (N : ℝ) ^ Dr +
      ((N : ℝ) ^ (Dr + 4 * p + 3))⁻¹ * (4 * ((N : ℝ) ^ (Dr + p + 1))⁻¹)⁻¹ ≤
      (Cpt * 2 ^ p + 2) * ((N : ℝ) ^ (p + 1))⁻¹ := by
    have hNp : (0 : ℝ) < (N : ℝ) ^ (p + 1) := by positivity
    have e1 : (N : ℝ) ^ (Dr + 4 * p + 3) = (N : ℝ) ^ (Dr + p + 1) * ((N : ℝ) ^ (p + 1) *
        (N : ℝ) ^ (2 * p + 1)) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    have e2 : (N : ℝ) ^ (Dr + p + 1) = (N : ℝ) ^ Dr * (N : ℝ) ^ (p + 1) := by
      rw [← pow_add]; congr 1
    have h1 : ((N : ℝ) ^ (Dr + 4 * p + 3))⁻¹ ≤ ((N : ℝ) ^ (p + 1))⁻¹ :=
      inv_anti₀ hNp (pow_le_pow_right₀ hN1 (by omega))
    have h2 : ((N : ℝ) ^ (Dr + p + 1))⁻¹ * (N : ℝ) ^ Dr = ((N : ℝ) ^ (p + 1))⁻¹ := by
      rw [e2]; field_simp
    have h3 : ((N : ℝ) ^ (Dr + 4 * p + 3))⁻¹ * (4 * ((N : ℝ) ^ (Dr + p + 1))⁻¹)⁻¹ ≤
        ((N : ℝ) ^ (p + 1))⁻¹ := by
      have h4 : (1 : ℝ) ≤ 4 * (N : ℝ) ^ (2 * p + 1) := by
        have := one_le_pow₀ (n := 2 * p + 1) hN1
        linarith
      rw [e1]
      have h5 : ((N : ℝ) ^ (Dr + p + 1) * ((N : ℝ) ^ (p + 1) * (N : ℝ) ^ (2 * p + 1)))⁻¹ *
          (4 * ((N : ℝ) ^ (Dr + p + 1))⁻¹)⁻¹ =
          ((N : ℝ) ^ (p + 1))⁻¹ * (4 * (N : ℝ) ^ (2 * p + 1))⁻¹ := by
        field_simp
      rw [h5]
      exact mul_le_of_le_one_right (by positivity) (inv_le_one_of_one_le₀ h4)
    have h6 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hCpt0 (by positivity : (0 : ℝ) ≤ 2 ^ p))
    rw [h2]
    linarith
  have hc1 : 0 ≤ Cpt * (1 + (4 * c₂) ^ p) :=
    mul_nonneg hCpt0 (add_nonneg zero_le_one (pow_nonneg (by linarith) _))
  have hc2 : 0 ≤ Kg ^ (4 * p) := pow_nonneg hKg0 _
  have hc3 : 0 ≤ Kg ^ (4 * p) * 2 ^ p := mul_nonneg hc2 (by positivity)
  have k1 := mul_le_mul_of_nonneg_left hbW hc1
  have k2 := mul_le_mul_of_nonneg_left hbW hc2
  have k3 := mul_le_mul_of_nonneg_left hcW hc3
  have hin : Cpt * (1 + (4 * c₂) ^ p) * ((Kb * b₀) ^ 2) ^ p + Kg ^ (4 * p) * ((Kb * b₀) ^ 2) ^ p +
      Kg ^ (4 * p) * 2 ^ p * (c₂ * b₀ ^ 2) ^ p ≤
      (Cpt * (1 + (4 * c₂) ^ p) * (Kb ^ (2 * p) * τ⁻¹ ^ (4 * p)) +
        Kg ^ (4 * p) * (Kb ^ (2 * p) * τ⁻¹ ^ (4 * p)) +
        Kg ^ (4 * p) * 2 ^ p * (c₂ ^ p * τ⁻¹ ^ (4 * p))) * W := by
    have : (Cpt * (1 + (4 * c₂) ^ p) * (Kb ^ (2 * p) * τ⁻¹ ^ (4 * p)) +
          Kg ^ (4 * p) * (Kb ^ (2 * p) * τ⁻¹ ^ (4 * p)) +
          Kg ^ (4 * p) * 2 ^ p * (c₂ ^ p * τ⁻¹ ^ (4 * p))) * W =
        Cpt * (1 + (4 * c₂) ^ p) * (Kb ^ (2 * p) * τ⁻¹ ^ (4 * p) * W) +
          Kg ^ (4 * p) * (Kb ^ (2 * p) * τ⁻¹ ^ (4 * p) * W) +
          Kg ^ (4 * p) * 2 ^ p * (c₂ ^ p * τ⁻¹ ^ (4 * p) * W) := by ring
    rw [this]
    linarith
  have hin' := mul_le_mul_of_nonneg_left hin he0
  calc _ = e * (Cpt * (1 + (4 * c₂) ^ p) * ((Kb * b₀) ^ 2) ^ p +
          Kg ^ (4 * p) * ((Kb * b₀) ^ 2) ^ p + Kg ^ (4 * p) * 2 ^ p * (c₂ * b₀ ^ 2) ^ p) +
        e * ((Cpt * 4 ^ p + Kg ^ (4 * p) * 2 ^ p) * EF) +
        (Cpt * 2 ^ p * ((N : ℝ) ^ (Dr + 4 * p + 3))⁻¹ +
          ((N : ℝ) ^ (Dr + p + 1))⁻¹ * (N : ℝ) ^ Dr +
          ((N : ℝ) ^ (Dr + 4 * p + 3))⁻¹ * (4 * ((N : ℝ) ^ (Dr + p + 1))⁻¹)⁻¹) := by ring
    _ ≤ _ := by linarith

/-! ## The envelope, `F̃^p` and the column expectation at one `N` -/

/-- The envelope `Λ_e N^q (1 + ‖X‖_F²)^q` and its square are integrable, and
`E (2 Λ_e N^q (1 + ‖X‖_F²)^q)² ≤ N^{4q+1}` when `4 Λ_e² K_S ≤ N`. -/
private theorem claimT_envInt {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {τ : ℝ} (hτ : 0 < τ) {C : ℕ → ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ}
    (hX : EntryAssumption C X) (hN1 : 1 ≤ N) (hM : (M : ℝ) ≤ τ⁻¹ * N) {Λe : ℝ} {q : ℕ}
    (hNc : 4 * Λe ^ 2 * claimT_KS τ C (2 * q) ≤ N) :
    (Integrable fun ω => Λe * (N : ℝ) ^ q * (1 + claimT_sq (X ω)) ^ q) ∧
    (Integrable fun ω => (2 * (Λe * (N : ℝ) ^ q * (1 + claimT_sq (X ω)) ^ q)) ^ 2) ∧
    ∫ ω, (2 * (Λe * (N : ℝ) ^ q * (1 + claimT_sq (X ω)) ^ q)) ^ 2 ≤ (N : ℝ) ^ (4 * q + 1) := by
  have hmom := claimT_moment hτ hX hN1 hM q
  have hmom2 := claimT_moment hτ hX hN1 hM (2 * q)
  have he : ∀ ω, (2 * (Λe * (N : ℝ) ^ q * (1 + claimT_sq (X ω)) ^ q)) ^ 2 =
      4 * Λe ^ 2 * (N : ℝ) ^ (2 * q) * (1 + claimT_sq (X ω)) ^ (2 * q) := fun ω => by
    ring
  refine ⟨hmom.1.const_mul _, ?_, ?_⟩
  · simp only [he]
    exact hmom2.1.const_mul _
  · simp only [he]
    rw [integral_const_mul]
    calc 4 * Λe ^ 2 * (N : ℝ) ^ (2 * q) * ∫ ω, (1 + claimT_sq (X ω)) ^ (2 * q)
        ≤ 4 * Λe ^ 2 * (N : ℝ) ^ (2 * q) * (claimT_KS τ C (2 * q) * (N : ℝ) ^ (2 * q)) :=
          mul_le_mul_of_nonneg_left hmom2.2 (by positivity)
      _ = (4 * Λe ^ 2 * claimT_KS τ C (2 * q)) * (N : ℝ) ^ (4 * q) := by ring
      _ ≤ N * (N : ℝ) ^ (4 * q) := mul_le_mul_of_nonneg_right hNc (by positivity)
      _ = (N : ℝ) ^ (4 * q + 1) := by ring

/-- `F̃^p` is integrable: `F̃ ≤ R + C_m` with `R` a bound on the entries of `G`. -/
private theorem claimT_FtI {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {z : ℂ} (hz : 0 < z.im)
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hXm : Measurable X) (hN1 : 1 ≤ N) {R Cm : ℝ}
    (hRG : ∀ (A : Matrix (Fin M) (Fin N) ℝ) s t, ‖G Sig A z s t‖ ≤ R)
    (hm : ‖mFun N (specOf Sig) z‖ ≤ Cm) (p : ℕ) :
    Integrable fun ω => Ft Sig (X ω) z ^ p := by
  have hFt : Continuous fun A : Matrix (Fin M) (Fin N) ℝ => Ft Sig A z := by
    unfold Ft mN
    exact ((continuous_const.mul (continuous_finsetSum _ fun ν _ =>
      claimT_cont_Gent hSig hz _ _)).sub continuous_const).norm
  refine (integrable_const ((R + Cm) ^ p)).mono'
    ((hFt.pow p).measurable.comp hXm).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  have h0 : 0 ≤ Ft Sig (X ω) z := norm_nonneg _
  rw [Real.norm_of_nonneg (pow_nonneg h0 _)]
  exact pow_le_pow_left₀ h0 (claimT_Ft_le (X ω) hN1 (hRG (X ω)) hm) p

/-- (A+_avg) for the integrand with `G_μμ → P` at a fixed `X^{(μ)}`, the vanishing case
included: some `A(w_r, σ_r)` is an identically vanishing bracket and the integrand is `0`. -/
private theorem claimT_hmain {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {C : ℕ → ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) {τ : ℝ}
    (hτ : 0 < τ) (p Kx : ℕ) {Sig : Matrix (Fin M) (Fin M) ℝ} {A : Matrix (Fin M) (Fin N) ℝ}
    {z : ℂ} {i : Fin M} {μ : Fin N} {Kg b CY Cpt : ℝ} (hN2 : 2 ≤ N) (hM : (M : ℝ) ≤ τ⁻¹ * N)
    (hKg : 1 ≤ Kg) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hCY : 1 ≤ CY)
    (hCpt : Cpt = Classical.choose (claimT_point_main C τ hτ p Kx) * CY ^ (p + 3) *
      Kg ^ ((Kx + 3) * (p + 3)))
    (hGν : ∀ ν, ν ≠ μ → ∀ j, ‖Gmu Sig A z μ (Sum.inr ν) (Sum.inl j)‖ ≤ b ∧
      ‖Gmu Sig A z μ (Sum.inl j) (Sum.inr ν)‖ ≤ b)
    (hK : ∀ s t, ‖Gmu Sig A z μ s t‖ ≤ Kg)
    (hS1 : ∑ j, ‖Gmu Sig A z μ (Sum.inl i) (Sum.inl j)‖ ≤ N * b)
    (hS1' : ∑ j, ‖Gmu Sig A z μ (Sum.inl j) (Sum.inl i)‖ ≤ N * b)
    (hS2 : ∑ j, ‖Gmu Sig A z μ (Sum.inl i) (Sum.inl j)‖ ^ 2 ≤ N * b ^ 2)
    (hS2' : ∑ j, ‖Gmu Sig A z μ (Sum.inl j) (Sum.inl i)‖ ^ 2 ≤ N * b ^ 2)
    (hY : ∀ k, ‖calY z (Ymu Sig A z μ) Kx k‖ ≤ CY)
    (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r)) (σs : ∀ r, Fin (ns r + 1) → Fin 3)
    (cs : Fin p → Bool) (hns : ∑ r, ns r = 3) (hv : ∀ r, tagV (σs r) = 0) :
    ‖∫ y, claimT_FP Sig (updCol A μ y) z i μ Kx ns ws σs cs ∂(colLaw X μ)‖ ≤
      Cpt * (2 * ‖claimT_Shat Sig A z μ‖) ^
        (Finset.univ.filter fun r => ns r = 0 ∧ tagMu (σs r) = 0).card *
      (N : ℝ) ^ (-(1 : ℝ) / 2) *
      b ^ (2 * (p - (Finset.univ.filter fun r => ns r = 0 ∧ tagMu (σs r) = 0).card)) := by
  obtain ⟨hC₁0, hpm⟩ := Classical.choose_spec (claimT_point_main C τ hτ p Kx)
  have hN1 : 1 ≤ N := by omega
  by_cases hnz : ∀ r, tagNZ (ns r) (ws r) (σs r) = true
  · have : ∀ j, IsProbabilityMeasure (entryLaw X (j, μ)) := fun j =>
      (claimT_colLaw hX μ hN1 j).1
    rw [hCpt]
    exact hpm M N Sig A z i μ (fun j => entryLaw X (j, μ)) Kg b CY hN2 hM hKg hb0 hb1 hCY
      (fun j => (claimT_colLaw hX μ hN1 j).2.1) (fun j n => (claimT_colLaw hX μ hN1 j).2.2 n)
      hGν hK hS1 hS1' hS2 hS2' hY ns ws σs cs hns hnz hv
  · simp only [not_forall] at hnz
    obtain ⟨r, hr⟩ := hnz
    have hr' : tagNZ (ns r) (ws r) (σs r) = false := by simpa using hr
    have h0 : ∀ y, claimT_FP Sig (updCol A μ y) z i μ Kx ns ws σs cs = 0 := by
      intro y
      unfold claimT_FP
      rw [Finset.prod_eq_zero (Finset.mem_univ r), mul_zero]
      unfold claimT_H
      simp [claimT_tagA_zero _ _ _ _ _ _ _ _ _ hr', conjIf]
    have hCpt0 : 0 ≤ Cpt := by
      rw [hCpt]
      exact mul_nonneg (mul_nonneg hC₁0 (pow_nonneg (by linarith) _))
        (pow_nonneg (by linarith) _)
    simp only [h0, integral_zero, norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg hCpt0 (pow_nonneg (by positivity) _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (pow_nonneg hb0 _)

/-! ## (avg_step 1) at one `N ≥ N₀` -/

/-- (avg_step 1) at one `(i, μ)` and one `N ≥ N₀`, with the constants fixed by `(τ, c, C, p)`:
`|E F_{iμ}| ≤ N^{−1/2} (K₁ (N^δ Ψ²)^p + K₂ E F̃^p) + (C_pt 2^p + 2) N^{−p−1}`. -/
private theorem claimT_fixed {τ c εa δ Da : ℝ} {C : ℕ → ℝ} {p : ℕ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hc : 0 < c) (hp2 : 2 ≤ p) (hεa : 0 < εa) (hεaτ : 16 * εa ≤ τ)
    (hεaδ : 20 * p * εa ≤ δ) (hDa : dPrevTwo τ p ≤ Da)
    {Cm Kg KP CY c₂ Kb Kθ Kc B₀ Crem cR Λe Cpt : ℝ} {qe Dr : ℕ}
    (hCm : Cm = mBoundConst τ) (hKg : Kg = τ⁻¹ * c⁻¹ + Cm + 1) (hKP : KP = τ⁻¹ * c⁻¹ + Cm)
    (hCY : CY = ((kTau τ : ℝ) + 1) * (2 * Cm + 1) ^ (kTau τ + 1) * 2 ^ kTau τ *
      (2 * τ⁻¹ + Cm + (2 * Cm)⁻¹ + 1) ^ kTau τ)
    (hc₂ : c₂ = Cm + 2 * Cm)
    (hKb : Kb = 2 * τ⁻¹ * (1 + 2 * Cm) + 2 * Cm + 1 + 2 * (Cm + 1) * c⁻¹)
    (hKθ : Kθ = 2 * Cm * (2 * Cm ^ 2 + τ⁻¹ * (1 + 2 * Cm)))
    (hKc : Kc = Kb + 2 * Cm * (τ⁻¹ * (1 + 2 * Cm)) + Kθ + (1 + 2 * Cm))
    (hB₀ : B₀ = τ⁻¹ ^ 2 * (Real.sqrt Cm + 1))
    (hCrem : Crem = ((p : ℝ) + 3) * (2 * (Cm + 1)) ^ (p + 3) * (Cm + 1))
    (hcR : cR = (1 + 10 * τ⁻¹) * τ⁻¹ + 1)
    (hqe : qe = (2 * kTau τ + 15) * (p + 3)) (hDr : Dr = 4 * qe + 1)
    (hΛe : Λe = ((cR + KP) * (1 + cR) * (2 * τ⁻¹)) ^ (4 * (p + 3)) +
      (((kTau τ : ℝ) + 1) * CY * (1 + Kg) ^ kTau τ) ^ (p + 3) *
        ((Kg + KP) * (1 + Kg)) ^ (3 * (p + 3)) * (2 * τ⁻¹) ^ ((2 * kTau τ + 3) * (p + 3)))
    (hCpt : Cpt = Classical.choose (claimT_point_main C τ hτ p (kTau τ)) * CY ^ (p + 3) *
      Kg ^ ((kTau τ + 3) * (p + 3)))
    {M N : ℕ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ} (hset : CompSetting τ c M N Sig S)
    (hN2 : 2 ≤ N) (hNa : Kc * B₀ ≤ (N : ℝ) ^ (τ / 16)) (hNb : Crem ≤ N)
    (hNc : 4 * Λe ^ 2 * claimT_KS τ C (2 * qe) ≤ N)
    {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) {z : ℂ} (hz : z ∈ S)
    (hHP : HighProbAt N (Da - 3) {ω | ∀ s t, ‖G Sig (X ω) z s t - PiZ N Sig z s t‖ ≤
      τ⁻¹ ^ 2 * (N : ℝ) ^ εa * Psi N (specOf Sig) z})
    (i : Fin M) (μ : Fin N) (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r))
    (σs : ∀ r, Fin (ns r + 1) → Fin 3) (cs : Fin p → Bool) (hns : ∑ r, ns r = 3)
    (hv : ∀ r, tagV (σs r) = 0) :
    ‖∫ ω, claimT_F Sig (X ω) z i μ ns ws σs cs‖ ≤
      (N : ℝ) ^ (-(1 : ℝ) / 2) *
        ((Cpt * (1 + (4 * c₂) ^ p) * (Kb ^ (2 * p) * τ⁻¹ ^ (4 * p)) +
            Kg ^ (4 * p) * (Kb ^ (2 * p) * τ⁻¹ ^ (4 * p)) +
            Kg ^ (4 * p) * 2 ^ p * (c₂ ^ p * τ⁻¹ ^ (4 * p))) *
          ((N : ℝ) ^ δ * Psi N (specOf Sig) z ^ 2) ^ p +
        (Cpt * 4 ^ p + Kg ^ (4 * p) * 2 ^ p) * ∫ ω, Ft Sig (X ω) z ^ p) +
      (Cpt * 2 ^ p + 2) * ((N : ℝ) ^ (p + 1))⁻¹ := by
  -- the setting
  have hN1 : 1 ≤ N := by omega
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le one_pos hN1r
  have hτ0 : 0 ≤ τ⁻¹ := by positivity
  have hcm : 0 < Cm := hCm ▸ mBoundConst_pos hτ
  have hSig : Sig.PosDef := hset.sigma.posDef
  have hzD : z ∈ specDomain τ N := hset.domain.1 hz
  have hzim : 0 < z.im := hzD.1
  have hM : (M : ℝ) ≤ τ⁻¹ * N := (div_le_iff₀ hN0).1 hset.ratio_le
  have hXm : Measurable X :=
    measurable_pi_iff.2 fun j => measurable_pi_iff.2 fun ν => hX.measurable j ν
  obtain ⟨hm1, hm2, -⟩ := gen_prop_m_specDomain (claimT_density hset hN1) hzD
  rw [← hCm] at hm1 hm2
  have hCm1 : 1 ≤ Cm := by
    have h1 : Cm⁻¹ ≤ Cm := hm1.trans hm2
    have h2 : 1 ≤ Cm * Cm := by
      have := mul_le_mul_of_nonneg_left h1 hcm.le
      rwa [mul_inv_cancel₀ hcm.ne'] at this
    nlinarith only [h2, hcm]
  obtain ⟨hPi', hrow, hcol, htr⟩ := claimT_Pi hset hN1 hz
  rw [← hCm] at hPi'
  have hPi : ∀ s t, ‖PiZ N Sig z s t‖ ≤ KP := fun s t => hKP ▸ hPi' s t
  have hz2 : ‖z‖ ≤ 2 * τ⁻¹ := by
    obtain ⟨-, -, hre, -, him⟩ := hzD
    have := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos hzim] at this
    linarith only [this, hre, him]
  -- the constants
  have hKP0 : 0 ≤ KP := by rw [hKP]; exact add_nonneg (by positivity) hcm.le
  have hKg1 : 1 ≤ Kg := by
    rw [hKg]
    have : 0 ≤ τ⁻¹ * c⁻¹ := by positivity
    linarith only [this, hcm]
  have hKg0 : 0 ≤ Kg := zero_le_one.trans hKg1
  have hCY1 : 1 ≤ CY := by
    have h4 : 0 ≤ (2 * Cm)⁻¹ := inv_nonneg.2 (by linarith)
    rw [hCY]
    have hk0 : (0 : ℝ) ≤ kTau τ := Nat.cast_nonneg _
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by linarith only [hk0])
        (one_le_pow₀ (by linarith only [hcm])))
      (one_le_pow₀ (by norm_num))) (one_le_pow₀ (by linarith only [h4, hcm, hτ0]))
  have hCY0 : 0 ≤ CY := zero_le_one.trans hCY1
  have hc₂0 : 0 ≤ c₂ := by rw [hc₂]; linarith only [hcm]
  have hcR0 : 0 ≤ cR := by rw [hcR]; positivity
  have hΛ1 : 0 ≤ ((cR + KP) * (1 + cR) * (2 * τ⁻¹)) ^ (4 * (p + 3)) :=
    pow_nonneg (mul_nonneg (mul_nonneg (add_nonneg hcR0 hKP0) (by linarith only [hcR0]))
      (by positivity)) _
  have hΛ2 : 0 ≤ (((kTau τ : ℝ) + 1) * CY * (1 + Kg) ^ kTau τ) ^ (p + 3) *
      ((Kg + KP) * (1 + Kg)) ^ (3 * (p + 3)) * (2 * τ⁻¹) ^ ((2 * kTau τ + 3) * (p + 3)) :=
    mul_nonneg (mul_nonneg (pow_nonneg (mul_nonneg (mul_nonneg (by positivity) hCY0)
      (pow_nonneg (by linarith only [hKg0]) _)) _)
      (pow_nonneg (mul_nonneg (add_nonneg hKg0 hKP0) (by linarith only [hKg0])) _))
      (by positivity)
  have hΛe0 : 0 ≤ Λe := by rw [hΛe]; exact add_nonneg hΛ1 hΛ2
  have hCpt0 : 0 ≤ Cpt := by
    rw [hCpt]
    exact mul_nonneg (mul_nonneg
      (Classical.choose_spec (claimT_point_main C τ hτ p (kTau τ))).1 (pow_nonneg hCY0 _))
      (pow_nonneg hKg0 _)
  have hKb0 : 0 ≤ Kb := by
    rw [hKb]
    have h1 : 0 ≤ 2 * τ⁻¹ * (1 + 2 * Cm) := mul_nonneg (by positivity) (by linarith only [hcm])
    have h2 : 0 ≤ 2 * (Cm + 1) * c⁻¹ := mul_nonneg (by linarith only [hcm]) (by positivity)
    linarith only [h1, h2, hcm]
  -- `Ψ` and the scalar conditions
  have hΨge := claimT_Psi_ge (σ := specOf Sig) hN1 hτ hzD
  have hΨdec := claimT_Psi_decay hset hN1 hz
  have hΨsq := claimT_Psi_sq_ge hset hN1 hz
  rw [← hCm] at hΨdec hΨsq
  generalize Psi N (specOf Sig) z = Ψ at hΨge hΨdec hΨsq hHP ⊢
  obtain ⟨b₀, hb₀def⟩ : ∃ x : ℝ, x = τ⁻¹ ^ 2 * (N : ℝ) ^ εa * Ψ := ⟨_, rfl⟩
  rw [← hb₀def] at hHP
  obtain ⟨hb₀0, hbb, hb0, hb1, hb₀1, hb₀m, hLb, hβ0, hβ1, hβb, hε, hθ, hrem, hNib, hNbb,
    hb₀sq⟩ := claimT_scal hτ hτ1 hc hp2 hεa hεaτ hεaδ hcm hCm1 hKb hKθ hKc hB₀ hCrem hN2 hNa
      hNb hΨge hΨdec hΨsq hb₀def
  -- the rough bound `R` and the envelope
  have hR1 : 1 ≤ (1 + 5 * ‖z‖) / z.im * τ⁻¹ + 1 := le_add_of_nonneg_left (by positivity)
  have hRG : ∀ (A : Matrix (Fin M) (Fin N) ℝ) s t,
      ‖G Sig A z s t‖ ≤ (1 + 5 * ‖z‖) / z.im * τ⁻¹ + 1 := fun A s t =>
    (claimT_G_rough hset.sigma hτ hτ1 A hzim s t).trans (le_add_of_nonneg_right zero_le_one)
  have hRGmu : ∀ (A : Matrix (Fin M) (Fin N) ℝ) s t,
      ‖Gmu Sig A z μ s t‖ ≤ (1 + 5 * ‖z‖) / z.im * τ⁻¹ + 1 := fun A s t =>
    (claimT_Gmu_rough hset.sigma hτ hτ1 A hzim μ s t).trans (le_add_of_nonneg_right zero_le_one)
  have hRN : (1 + 5 * ‖z‖) / z.im * τ⁻¹ + 1 ≤ cR * N := by
    have hNη := claimT_one_le_N_im hN1 hτ hzD
    have h1 : (1 + 5 * ‖z‖) / z.im ≤ (1 + 10 * τ⁻¹) * N := by
      rw [div_le_iff₀ hzim]
      calc 1 + 5 * ‖z‖ ≤ (1 + 10 * τ⁻¹) * 1 := by linarith only [hz2]
        _ ≤ (1 + 10 * τ⁻¹) * (N * z.im) := mul_le_mul_of_nonneg_left hNη (by positivity)
        _ = (1 + 10 * τ⁻¹) * N * z.im := by ring
    have h3 := mul_le_mul_of_nonneg_right h1 hτ0
    rw [hcR]
    calc (1 + 5 * ‖z‖) / z.im * τ⁻¹ + 1 ≤ (1 + 10 * τ⁻¹) * N * τ⁻¹ + N := add_le_add h3 hN1r
      _ = ((1 + 10 * τ⁻¹) * τ⁻¹ + 1) * N := by ring
  have hsqV : ∀ A : Matrix (Fin M) (Fin N) ℝ,
      1 + claimT_V A μ ≤ 2 * τ⁻¹ * N * (1 + claimT_sq A) := fun A => by
    refine (claimT_V_le A μ).trans (mul_le_mul_of_nonneg_right ?_
      (by linarith only [claimT_sq_nonneg A]))
    have : (1 : ℝ) ≤ τ⁻¹ * N := one_le_mul_of_one_le_of_one_le ((one_le_inv₀ hτ).2 hτ1) hN1r
    linarith only [this, hM]
  have hqe1 : 4 * (p + 3) ≤ qe := by rw [hqe]; exact Nat.mul_le_mul_right _ (by omega)
  have hqe2 : 12 * (p + 3) ≤ qe := by rw [hqe]; exact Nat.mul_le_mul_right _ (by omega)
  have hqe3 : (2 * kTau τ + 3) * (p + 3) ≤ qe := by
    rw [hqe]; exact Nat.mul_le_mul_right _ (by omega)
  have hΛe1 : ((cR + KP) * (1 + cR) * (2 * τ⁻¹)) ^ (4 * (p + 3)) ≤ Λe := by
    rw [hΛe]; exact le_add_of_nonneg_right hΛ2
  have hΛe2 : (((kTau τ : ℝ) + 1) * CY * (1 + Kg) ^ kTau τ) ^ (p + 3) *
      ((Kg + KP) * (1 + Kg)) ^ (3 * (p + 3)) * (2 * τ⁻¹) ^ ((2 * kTau τ + 3) * (p + 3)) ≤ Λe := by
    rw [hΛe]; exact le_add_of_nonneg_left hΛ1
  -- the `X^{(μ)}`-measurable event
  have hbundle : ∀ A, claimT_Good Sig A z μ ((1 + 2 * Cm) * b₀) →
      (∀ s t, ‖Gmu Sig A z μ s t‖ ≤ Kg) ∧
      (∀ ν, ν ≠ μ → ∀ j, ‖Gmu Sig A z μ (Sum.inr ν) (Sum.inl j)‖ ≤ Kb * b₀ ∧
        ‖Gmu Sig A z μ (Sum.inl j) (Sum.inr ν)‖ ≤ Kb * b₀) ∧
      (∀ i, (∑ j, ‖Gmu Sig A z μ (Sum.inl i) (Sum.inl j)‖ ≤ N * (Kb * b₀)) ∧
        (∑ j, ‖Gmu Sig A z μ (Sum.inl j) (Sum.inl i)‖ ≤ N * (Kb * b₀)) ∧
        (∑ j, ‖Gmu Sig A z μ (Sum.inl i) (Sum.inl j)‖ ^ 2 ≤ N * (Kb * b₀) ^ 2) ∧
        (∑ j, ‖Gmu Sig A z μ (Sum.inl j) (Sum.inl i)‖ ^ 2 ≤ N * (Kb * b₀) ^ 2)) ∧
      (∀ k, ‖calY z (Ymu Sig A z μ) (kTau τ) k‖ ≤ CY) ∧
      ‖claimT_Shat Sig A z μ‖ ≤ 1 ∧
      ‖Ymu Sig A z μ - (-z - (mFun N (specOf Sig) z)⁻¹)‖ ≤ τ⁻¹ * ((1 + 2 * Cm) * b₀) := by
    intro A hA
    have h := claimT_good_bundle hτ hτ1 μ A (kTau τ) hcm hm1 hm2 hM htr hPi' hrow hcol hβ0 hβ1
      hβb hNbb hε hz2 hA
    rw [← hKg, ← hCY] at h
    exact h
  have hgood : ∀ A, claimT_Good Sig A z μ ((1 + 2 * Cm) * b₀) →
      (∀ s t, ‖Gmu Sig A z μ s t‖ ≤ Kg) ∧
      (∀ ν, ν ≠ μ → ∀ j, ‖Gmu Sig A z μ (Sum.inr ν) (Sum.inl j)‖ ≤ Kb * b₀ ∧
        ‖Gmu Sig A z μ (Sum.inl j) (Sum.inr ν)‖ ≤ Kb * b₀) ∧
      ‖claimT_Shat Sig A z μ‖ ≤ 1 ∧
      ‖Ymu Sig A z μ - (-z - (mFun N (specOf Sig) z)⁻¹)‖ ≤ τ⁻¹ * ((1 + 2 * Cm) * b₀) :=
    fun A hA => by
      obtain ⟨h1, h2, -, -, h5, h6⟩ := hbundle A hA
      exact ⟨h1, h2, h5, h6⟩
  have hmain : ∀ A, claimT_Good Sig A z μ ((1 + 2 * Cm) * b₀) →
      ‖∫ y, claimT_FP Sig (updCol A μ y) z i μ (kTau τ) ns ws σs cs ∂(colLaw X μ)‖ ≤
        Cpt * (2 * ‖claimT_Shat Sig A z μ‖) ^
          (Finset.univ.filter fun r => ns r = 0 ∧ tagMu (σs r) = 0).card *
        (N : ℝ) ^ (-(1 : ℝ) / 2) *
        (Kb * b₀) ^ (2 * (p - (Finset.univ.filter fun r => ns r = 0 ∧ tagMu (σs r) = 0).card)) :=
    fun A hA => by
      obtain ⟨hK, hGν, hsum, hY, -, -⟩ := hbundle A hA
      exact claimT_hmain hX hτ p (kTau τ) hN2 hM hKg1 hb0 hb1 hCY1 hCpt hGν hK (hsum i).1
        (hsum i).2.1 (hsum i).2.2.1 (hsum i).2.2.2 hY ns ws σs cs hns hv
  -- the a priori event
  have hΞ : ∀ ω ∈ {ω | ∀ s t, ‖G Sig (X ω) z s t - PiZ N Sig z s t‖ ≤ b₀},
      (∀ s t, ‖G Sig (X ω) z s t - PiZ N Sig z s t‖ ≤ b₀) ∧
      1 ≤ 2 * Cm * ‖G Sig (X ω) z (Sum.inr μ) (Sum.inr μ)‖ ∧
      claimT_Good Sig (X ω) z μ ((1 + 2 * Cm) * b₀) ∧
      ‖claimT_Shat Sig (X ω) z μ‖ ≤ Ft Sig (X ω) z + c₂ * b₀ ^ 2 := by
    intro ω hω
    have hG : ∀ s t, ‖G Sig (X ω) z s t - PiZ N Sig z s t‖ ≤ b₀ := hω
    obtain ⟨h1, h2, h3⟩ := claimT_event_bundle hSig (X ω) hzim μ hcm hm1 hb₀1 hb₀m hNib hG
    rw [← hc₂] at h3
    exact ⟨hG, h1, h2, h3⟩
  have hPΞ : (ℙ {ω | ∀ s t, ‖G Sig (X ω) z s t - PiZ N Sig z s t‖ ≤ b₀}ᶜ).toReal ≤
      ((N : ℝ) ^ (Dr + 4 * p + 3))⁻¹ := by
    refine (ENNReal.toReal_le_of_le_ofReal (by positivity) hHP).trans ?_
    rw [← Real.rpow_natCast, ← Real.rpow_neg hN0.le]
    apply Real.rpow_le_rpow_of_exponent_le hN1r
    have := claimT_Da hp2 hDa
    rw [hDr, hqe]
    push_cast at this ⊢
    linarith only [this]
  have hs : (0 : ℝ) < ((N : ℝ) ^ (Dr + p + 1))⁻¹ := by positivity
  -- the envelope
  have hEnv0 : ∀ A : Matrix (Fin M) (Fin N) ℝ,
      0 ≤ Λe * (N : ℝ) ^ qe * (1 + claimT_sq A) ^ qe := fun A =>
    mul_nonneg (mul_nonneg hΛe0 (by positivity))
      (pow_nonneg (by linarith only [claimT_sq_nonneg A]) _)
  obtain ⟨hEnvI, hEnv2I, hEnv2⟩ := claimT_envInt hτ hX hN1 hM hNc
  rw [← hDr] at hEnv2
  have hFtI := claimT_FtI hSig hzim hXm hN1 hRG hm2 p
  have H := claimT_per hX hSig hzim i μ (kTau τ) ns ws σs cs hns hv
    {ω | ∀ s t, ‖G Sig (X ω) z s t - PiZ N Sig z s t‖ ≤ b₀}
    (fun A => Λe * (N : ℝ) ^ qe * (1 + claimT_sq A) ^ qe)
    hcm hb0 hb1 hb₀0 hbb hb₀1 hb₀m hLb hKg1 hc₂0 hCpt0 hs hm1 hm2 hε hθ hrem hPΞ hΞ hgood hmain
    hEnvI hEnv0
    (fun A => claimT_envF (τ := τ) Sig A z i μ ns ws σs cs hns hv hR1 hKP0 hcR0 hτ0 hN1r
      (hRGmu A) (hRG A) hPi hRN (hsqV A) hqe1 hqe2 hΛe1)
    (fun A hA => by
      obtain ⟨hK, -, -, hY, -, -⟩ := hbundle A hA
      exact claimT_envFP Sig A z i μ (kTau τ) ns ws σs cs hns hv hKg1 hKP0 hCY1 hτ0 hN1r hK hPi
        hY (hsqV A) hqe3 hΛe2)
    hEnv2I hEnv2 hFtI
  exact H.trans (claimT_tail hN1r (Real.rpow_nonneg hN0.le _) hCpt0 hc₂0 hKg0 hb₀sq)

/-! ## (avg_step 1) -/

/-- The sum over `(i, μ)`: `N^{−3/2} ∑_{i,μ} (N^{−1/2} T₁ + T₂) ≤ τ⁻¹ T₁ + τ⁻¹ N T₂` for
`M ≤ τ⁻¹ N`. -/
private theorem claimT_sum {τ T₁ T₂ : ℝ} {M N : ℕ} (hN1 : 1 ≤ N) (hM : (M : ℝ) ≤ τ⁻¹ * N)
    (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂) {f : Fin M → Fin N → ℝ}
    (hf : ∀ i μ, f i μ ≤ (N : ℝ) ^ (-(1 : ℝ) / 2) * T₁ + T₂) :
    (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ, f i μ ≤ τ⁻¹ * T₁ + τ⁻¹ * (N * T₂) := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  set e := (N : ℝ) ^ (-(1 : ℝ) / 2) with he
  have he0 : 0 ≤ e := Real.rpow_nonneg hN0.le _
  have he1 : e ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1r (by norm_num)
  have he2 : e ^ 2 * N = 1 := by
    rw [he, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le,
      show (-(1 : ℝ) / 2 * ((2 : ℕ) : ℝ)) = -1 by norm_num, Real.rpow_neg_one,
      inv_mul_cancel₀ hN0.ne']
  have he3 : (N : ℝ) ^ (-(3 : ℝ) / 2) = e ^ 3 := by
    rw [he, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have hτ0 : 0 ≤ τ⁻¹ := by
    by_contra h
    have : (M : ℝ) < 0 := lt_of_le_of_lt hM (mul_neg_of_neg_of_pos (lt_of_not_ge h) hN0)
    linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
  have hsum : ∑ i, ∑ μ, f i μ ≤ (M : ℝ) * N * (e * T₁ + T₂) := by
    calc _ ≤ ∑ _i : Fin M, ∑ _μ : Fin N, (e * T₁ + T₂) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun μ _ => hf i μ
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hMN : (M : ℝ) * e ^ 2 ≤ τ⁻¹ := by
    have h1 : e ^ 2 = (N : ℝ)⁻¹ := eq_inv_of_mul_eq_one_left he2
    rw [h1, ← div_eq_mul_inv, div_le_iff₀ hN0]; exact hM
  have hMe : (M : ℝ) * e ≤ τ⁻¹ * N := (mul_le_of_le_one_right (Nat.cast_nonneg _) he1).trans hM
  rw [he3]
  calc e ^ 3 * ∑ i, ∑ μ, f i μ ≤ e ^ 3 * ((M : ℝ) * N * (e * T₁ + T₂)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (M : ℝ) * e ^ 2 * (e ^ 2 * N) * T₁ + ((M : ℝ) * e) * (e ^ 2 * N) * T₂ := by ring
    _ = (M : ℝ) * e ^ 2 * T₁ + ((M : ℝ) * e) * T₂ := by rw [he2]; ring
    _ ≤ τ⁻¹ * T₁ + τ⁻¹ * N * T₂ :=
        add_le_add (mul_le_mul_of_nonneg_right hMN hT₁) (mul_le_mul_of_nonneg_right hMe hT₂)
    _ = τ⁻¹ * T₁ + τ⁻¹ * (N * T₂) := by ring

/-- (avg_step 1) for one tagged tuple (`ℤ₂` tags, `ν_r ≠ μ`): the `n = 3` contribution of §9. -/
theorem avg_lem82 (τ c : ℝ) (C : ℕ → ℝ) (p : ℕ) (δ εa Da : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hc : 0 < c) (hp : Even p) (hp2 : 2 ≤ p) (hδ : 0 < δ) (hεa : 0 < εa) (hεaτ : 16 * εa ≤ τ)
    (hεaδ : 20 * p * εa ≤ δ) (hDa : dPrevTwo τ p ≤ Da) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (S : Set ℂ), CompSetting τ c M N Sig S → AnisoAllAt N C Sig S εa Da →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption C X →
        ∀ z ∈ S, ∀ (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r))
          (σs : ∀ r, Fin (ns r + 1) → Fin 3) (cs : Fin p → Bool),
          ∑ r, ns r = 3 → (∀ r, tagV (σs r) = 0) →
          (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ,
            ‖∫ ω, (N : ℂ)⁻¹ ^ p *
              ∑ νs ∈ Fintype.piFinset (fun _ : Fin p => Finset.univ.erase μ),
                ∏ r, conjIf (cs r) (tagA Sig (X ω) z (eI (Sum.inr (νs r))) i μ (ns r) (ws r)
                  (σs r) * G Sig (X ω) z (Sum.inr μ) (Sum.inr μ) ^ tagMu (σs r))‖ ≤
            K * (((N : ℝ) ^ δ * Psi N (specOf Sig) z ^ 2) ^ p + ∫ ω, Ft Sig (X ω) z ^ p) := by
  obtain ⟨_, _⟩ := hp
  -- the constants
  obtain ⟨Cm, hCm⟩ : ∃ x : ℝ, x = mBoundConst τ := ⟨_, rfl⟩
  have hcm : 0 < Cm := hCm ▸ mBoundConst_pos hτ
  obtain ⟨Kg, hKg⟩ : ∃ x : ℝ, x = τ⁻¹ * c⁻¹ + Cm + 1 := ⟨_, rfl⟩
  obtain ⟨KP, hKP⟩ : ∃ x : ℝ, x = τ⁻¹ * c⁻¹ + Cm := ⟨_, rfl⟩
  obtain ⟨CY, hCY⟩ : ∃ x : ℝ, x = ((kTau τ : ℝ) + 1) * (2 * Cm + 1) ^ (kTau τ + 1) *
      2 ^ kTau τ * (2 * τ⁻¹ + Cm + (2 * Cm)⁻¹ + 1) ^ kTau τ := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ x : ℝ, x = Cm + 2 * Cm := ⟨_, rfl⟩
  obtain ⟨Kb, hKb⟩ : ∃ x : ℝ, x = 2 * τ⁻¹ * (1 + 2 * Cm) + 2 * Cm + 1 + 2 * (Cm + 1) * c⁻¹ :=
    ⟨_, rfl⟩
  obtain ⟨Kθ, hKθ⟩ : ∃ x : ℝ, x = 2 * Cm * (2 * Cm ^ 2 + τ⁻¹ * (1 + 2 * Cm)) := ⟨_, rfl⟩
  obtain ⟨Kc, hKc⟩ : ∃ x : ℝ, x = Kb + 2 * Cm * (τ⁻¹ * (1 + 2 * Cm)) + Kθ + (1 + 2 * Cm) :=
    ⟨_, rfl⟩
  obtain ⟨B₀, hB₀⟩ : ∃ x : ℝ, x = τ⁻¹ ^ 2 * (Real.sqrt Cm + 1) := ⟨_, rfl⟩
  obtain ⟨Crem, hCrem⟩ : ∃ x : ℝ, x = ((p : ℝ) + 3) * (2 * (Cm + 1)) ^ (p + 3) * (Cm + 1) :=
    ⟨_, rfl⟩
  obtain ⟨cR, hcR⟩ : ∃ x : ℝ, x = (1 + 10 * τ⁻¹) * τ⁻¹ + 1 := ⟨_, rfl⟩
  obtain ⟨qe, hqe⟩ : ∃ x : ℕ, x = (2 * kTau τ + 15) * (p + 3) := ⟨_, rfl⟩
  obtain ⟨Dr, hDr⟩ : ∃ x : ℕ, x = 4 * qe + 1 := ⟨_, rfl⟩
  obtain ⟨Λe, hΛe⟩ : ∃ x : ℝ, x = ((cR + KP) * (1 + cR) * (2 * τ⁻¹)) ^ (4 * (p + 3)) +
      (((kTau τ : ℝ) + 1) * CY * (1 + Kg) ^ kTau τ) ^ (p + 3) *
        ((Kg + KP) * (1 + Kg)) ^ (3 * (p + 3)) * (2 * τ⁻¹) ^ ((2 * kTau τ + 3) * (p + 3)) :=
    ⟨_, rfl⟩
  obtain ⟨Cpt, hCpt⟩ : ∃ x : ℝ, x = Classical.choose (claimT_point_main C τ hτ p (kTau τ)) *
      CY ^ (p + 3) * Kg ^ ((kTau τ + 3) * (p + 3)) := ⟨_, rfl⟩
  have hKg0 : 0 ≤ Kg := by
    rw [hKg]; exact add_nonneg (add_nonneg (by positivity) hcm.le) zero_le_one
  have hCY0 : 0 ≤ CY := by
    rw [hCY]
    have : 0 ≤ (2 * Cm)⁻¹ := inv_nonneg.2 (by linarith)
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (by linarith) _))
      (by positivity)) (pow_nonneg (by linarith [inv_nonneg.2 hτ.le]) _)
  have hCpt0 : 0 ≤ Cpt := by
    rw [hCpt]
    exact mul_nonneg (mul_nonneg
      (Classical.choose_spec (claimT_point_main C τ hτ p (kTau τ))).1 (pow_nonneg hCY0 _))
      (pow_nonneg hKg0 _)
  have hc₂0 : 0 ≤ c₂ := by rw [hc₂]; linarith
  have hKb0 : 0 ≤ Kb := by
    rw [hKb]
    have : 0 ≤ 2 * τ⁻¹ * (1 + 2 * Cm) := mul_nonneg (by positivity) (by linarith)
    have : 0 ≤ 2 * (Cm + 1) * c⁻¹ := mul_nonneg (by linarith) (by positivity)
    linarith
  have hCrem0 : 0 ≤ Crem := by
    rw [hCrem]
    exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (by linarith) _)) (by linarith)
  have hKS0 : 0 ≤ claimT_KS τ C (2 * qe) := by
    unfold claimT_KS
    exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (by linarith [le_max_right (C (2 * (2 * qe))) 0])
  obtain ⟨K₁, hK₁⟩ : ∃ x : ℝ, x = Cpt * (1 + (4 * c₂) ^ p) * (Kb ^ (2 * p) * τ⁻¹ ^ (4 * p)) +
      Kg ^ (4 * p) * (Kb ^ (2 * p) * τ⁻¹ ^ (4 * p)) +
      Kg ^ (4 * p) * 2 ^ p * (c₂ ^ p * τ⁻¹ ^ (4 * p)) := ⟨_, rfl⟩
  obtain ⟨K₂, hK₂⟩ : ∃ x : ℝ, x = Cpt * 4 ^ p + Kg ^ (4 * p) * 2 ^ p := ⟨_, rfl⟩
  have hK₁0 : 0 ≤ K₁ := by
    rw [hK₁]
    have h4 : 0 ≤ 1 + (4 * c₂) ^ p := add_nonneg zero_le_one (pow_nonneg (by linarith) _)
    have h5 : 0 ≤ Kb ^ (2 * p) * τ⁻¹ ^ (4 * p) := mul_nonneg (pow_nonneg hKb0 _) (by positivity)
    exact add_nonneg (add_nonneg (mul_nonneg (mul_nonneg hCpt0 h4) h5)
      (mul_nonneg (pow_nonneg hKg0 _) h5))
      (mul_nonneg (mul_nonneg (pow_nonneg hKg0 _) (by positivity))
        (mul_nonneg (pow_nonneg hc₂0 _) (by positivity)))
  have hK₂0 : 0 ≤ K₂ := by
    rw [hK₂]
    exact add_nonneg (mul_nonneg hCpt0 (by positivity))
      (mul_nonneg (pow_nonneg hKg0 _) (by positivity))
  have hK₃0 : 0 ≤ (Cpt * 2 ^ p + 2) * Cm ^ p :=
    mul_nonneg (add_nonneg (mul_nonneg hCpt0 (by positivity)) (by norm_num)) (pow_nonneg hcm.le _)
  refine ⟨τ⁻¹ * (K₁ + K₂ + (Cpt * 2 ^ p + 2) * Cm ^ p), by positivity, ?_⟩
  obtain ⟨N₁, hN₁⟩ := avg_entry_highProb τ c εa Da hτ hτ1 hc
  obtain ⟨N₂, hN₂⟩ := claimT_large hτ (Kc * B₀) (Crem + 4 * Λe ^ 2 * claimT_KS τ C (2 * qe))
  refine ⟨max N₁ N₂, fun N hN M Sig S hset haniso Ω _ _ X hX z hz ns ws σs cs hns hv => ?_⟩
  obtain ⟨hNa, hNbc, hN2⟩ := hN₂ N (le_of_max_le_right hN)
  have hKS1 : 0 ≤ 4 * Λe ^ 2 * claimT_KS τ C (2 * qe) := mul_nonneg (by positivity) hKS0
  have hNb : Crem ≤ N := le_trans (le_add_of_nonneg_right hKS1) hNbc
  have hNc : 4 * Λe ^ 2 * claimT_KS τ C (2 * qe) ≤ N := le_trans (le_add_of_nonneg_left hCrem0) hNbc
  have hHP := hN₁ N (le_of_max_le_left hN) M Sig S hset Ω X (haniso Ω X hX) z hz
  have hper := fun i μ => claimT_fixed hτ hτ1 hc hp2 hεa hεaτ hεaδ hDa hCm hKg hKP hCY hc₂ hKb
    hKθ hKc hB₀ hCrem hcR hqe hDr hΛe hCpt hset hN2 hNa hNb hNc hX hz hHP i μ ns ws σs cs hns hv
  change (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ, ‖∫ ω, claimT_F Sig (X ω) z i μ ns ws σs cs‖ ≤ _
  have hN1 : 1 ≤ N := by omega
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hM : (M : ℝ) ≤ τ⁻¹ * N := (div_le_iff₀ hN0).1 hset.ratio_le
  have hΨsq := claimT_Psi_sq_ge hset hN1 hz
  rw [← hCm] at hΨsq
  rw [← hK₁, ← hK₂] at hper
  generalize Psi N (specOf Sig) z = Ψ at hper hΨsq ⊢
  have hEF0 : 0 ≤ ∫ ω, Ft Sig (X ω) z ^ p := integral_nonneg fun ω => pow_nonneg (norm_nonneg _) _
  generalize (∫ ω, Ft Sig (X ω) z ^ p) = EF at hper hEF0 ⊢
  have hT₂0 : 0 ≤ (Cpt * 2 ^ p + 2) * ((N : ℝ) ^ (p + 1))⁻¹ :=
    mul_nonneg (add_nonneg (mul_nonneg hCpt0 (by positivity)) (by norm_num)) (by positivity)
  have hW0 : 0 ≤ ((N : ℝ) ^ δ * Ψ ^ 2) ^ p := by positivity
  have hNT₂ : (N : ℝ) * ((Cpt * 2 ^ p + 2) * ((N : ℝ) ^ (p + 1))⁻¹) ≤
      (Cpt * 2 ^ p + 2) * Cm ^ p * ((N : ℝ) ^ δ * Ψ ^ 2) ^ p := by
    have hNi : (N : ℝ)⁻¹ ≤ Cm * Ψ ^ 2 := by
      have := mul_le_mul_of_nonneg_left hΨsq hcm.le
      rwa [mul_inv, ← mul_assoc, mul_inv_cancel₀ hcm.ne', one_mul] at this
    have h1 : (N : ℝ) * ((N : ℝ) ^ (p + 1))⁻¹ = ((N : ℝ)⁻¹) ^ p := by
      rw [inv_pow, pow_succ]; field_simp
    have h2 : ((N : ℝ)⁻¹) ^ p ≤ Cm ^ p * ((N : ℝ) ^ δ * Ψ ^ 2) ^ p := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      have : Ψ ^ 2 ≤ (N : ℝ) ^ δ * Ψ ^ 2 :=
        le_mul_of_one_le_left (sq_nonneg _) (Real.one_le_rpow hN1r hδ.le)
      calc (N : ℝ)⁻¹ ≤ Cm * Ψ ^ 2 := hNi
        _ ≤ Cm * ((N : ℝ) ^ δ * Ψ ^ 2) := mul_le_mul_of_nonneg_left this hcm.le
    calc (N : ℝ) * ((Cpt * 2 ^ p + 2) * ((N : ℝ) ^ (p + 1))⁻¹) =
          (Cpt * 2 ^ p + 2) * ((N : ℝ) * ((N : ℝ) ^ (p + 1))⁻¹) := by ring
      _ ≤ (Cpt * 2 ^ p + 2) * (Cm ^ p * ((N : ℝ) ^ δ * Ψ ^ 2) ^ p) := by
          rw [h1]; exact mul_le_mul_of_nonneg_left h2
            (add_nonneg (mul_nonneg hCpt0 (by positivity)) (by norm_num))
      _ = (Cpt * 2 ^ p + 2) * Cm ^ p * ((N : ℝ) ^ δ * Ψ ^ 2) ^ p := by ring
  have hτ0 : 0 ≤ τ⁻¹ := by positivity
  have hT₁0 : 0 ≤ K₁ * ((N : ℝ) ^ δ * Ψ ^ 2) ^ p + K₂ * EF :=
    add_nonneg (mul_nonneg hK₁0 hW0) (mul_nonneg hK₂0 hEF0)
  refine (claimT_sum hN1 hM hT₁0 hT₂0 hper).trans ?_
  have h1 := mul_le_mul_of_nonneg_left hNT₂ hτ0
  have h2 : K₁ * ((N : ℝ) ^ δ * Ψ ^ 2) ^ p + K₂ * EF +
      (Cpt * 2 ^ p + 2) * Cm ^ p * ((N : ℝ) ^ δ * Ψ ^ 2) ^ p ≤
      (K₁ + K₂ + (Cpt * 2 ^ p + 2) * Cm ^ p) *
        (((N : ℝ) ^ δ * Ψ ^ 2) ^ p + EF) := by
    have e : (K₁ + K₂ + (Cpt * 2 ^ p + 2) * Cm ^ p) *
        (((N : ℝ) ^ δ * Ψ ^ 2) ^ p + EF) =
        K₁ * ((N : ℝ) ^ δ * Ψ ^ 2) ^ p + K₂ * EF +
          (Cpt * 2 ^ p + 2) * Cm ^ p * ((N : ℝ) ^ δ * Ψ ^ 2) ^ p +
          (K₁ * EF + K₂ * ((N : ℝ) ^ δ * Ψ ^ 2) ^ p +
            (Cpt * 2 ^ p + 2) * Cm ^ p * EF) := by ring
    rw [e]
    have := add_nonneg (add_nonneg (mul_nonneg hK₁0 hEF0) (mul_nonneg hK₂0 hW0))
      (mul_nonneg hK₃0 hEF0)
    linarith only [this]
  have h3 := mul_le_mul_of_nonneg_left h2 hτ0
  calc τ⁻¹ * (K₁ * ((N : ℝ) ^ δ * Ψ ^ 2) ^ p + K₂ * EF) +
        τ⁻¹ * ((N : ℝ) * ((Cpt * 2 ^ p + 2) * ((N : ℝ) ^ (p + 1))⁻¹))
      ≤ τ⁻¹ * (K₁ * ((N : ℝ) ^ δ * Ψ ^ 2) ^ p + K₂ * EF) +
        τ⁻¹ * ((Cpt * 2 ^ p + 2) * Cm ^ p * ((N : ℝ) ^ δ * Ψ ^ 2) ^ p) := by linarith only [h1]
    _ = τ⁻¹ * (K₁ * ((N : ℝ) ^ δ * Ψ ^ 2) ^ p + K₂ * EF +
        (Cpt * 2 ^ p + 2) * Cm ^ p * ((N : ℝ) ^ δ * Ψ ^ 2) ^ p) := by ring
    _ ≤ _ := h3.trans_eq (by ring)

/-! ### Compiled instances -/

end Anisotropic
