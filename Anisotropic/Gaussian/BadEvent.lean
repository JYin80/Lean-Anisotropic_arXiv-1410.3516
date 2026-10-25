import Anisotropic.Gaussian.Measurable
import Anisotropic.Entrywise.Control
import Anisotropic.Probability.NormBound.GaussianLower
import Anisotropic.LinAlg.Spectral
import Anisotropic.LinAlg.Blocks
import Anisotropic.Framework.DominationUnion

/-!
# Deterministic bounds, Gaussian moments and the bad event (Lemma 6.2, `Σ = diag(σ)`)

For `B := Σ̲⁻¹ (G − Π) Σ̲⁻¹` with `Σ = diag(σ)` (Definition 3.20, (def_Pi), (def_ul_Sigma)):
* `Λ` of Section 5.1 is the maximum of the entries `|B_{st}|`, and `Λ_o` bounds the off-diagonal
  ones;
* the deterministic bound `Λ_o ≤ (1 + ‖X‖_F)² / η`, from (G=G) and (GN_spec);
* the Gaussian moments `E(1 + ‖X‖_F)^{2q} ≤ 2^{2q} (1 + M^q g_{2q})`;
* the bound `E Λ_o^p ≤ b^p + K_b N^{2p} a^{1/2}` when `P(Λ > b) ≤ a`, by Cauchy–Schwarz on the
  event `{Λ > b}`;
* the union bound `P(Λ > N^{ε₁} Ψ) ≤ (M + N)² N^{−D₁}` under the entrywise law at `(ε₁, D₁)`.

These are the bad-event estimates in the moment method for the off-diagonal part in the proof of
Lemma 6.2 for Gaussian `X`.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! ## The entries of `B` for `Σ = diag(σ)` -/

/-- `σ̲_s > 0` for `σ > 0`. -/
private theorem badEvent_sigS_pos {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (s : Fin M ⊕ Fin N) : 0 < sigS σ s := by
  cases s with
  | inl i => exact hσ i
  | inr μ => exact one_pos

/-- `Π = diag(m_s)` entrywise, for `Σ = diag(σ)`. -/
private theorem badEvent_PiDiag_apply {N : ℕ} (σ : Fin M → ℝ) (z : ℂ) (s t : Fin M ⊕ Fin N) :
    PiDiag N σ z s t = if s = t then mS N σ z s else 0 := by
  cases s <;> cases t <;> simp [PiDiag, mS, mI, diagonal_apply, one_apply]

/-- `B_{st} = (G_{st} − δ_{st} m_s) / (σ̲_s σ̲_t)`. -/
private theorem badEvent_lawMat_eq {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (s t : Fin M ⊕ Fin N) :
    lawMat (diagonal σ) Xm z s t
      = (G (diagonal σ) Xm z s t - (if s = t then mS N σ z s else 0))
        / ((sigS σ s : ℂ) * sigS σ t) := by
  unfold lawMat
  rw [← wEnt_eq hσ, piMat_diagonal (fun i => (hσ i).le) hz, wEnt, Matrix.sub_apply,
    badEvent_PiDiag_apply]

/-- `|B_{st}| = |G_{st} − δ_{st} m_s| / (σ̲_s σ̲_t)`. -/
private theorem badEvent_norm_lawMat {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (s t : Fin M ⊕ Fin N) :
    ‖lawMat (diagonal σ) Xm z s t‖
      = ‖G (diagonal σ) Xm z s t - (if s = t then mS N σ z s else 0)‖
        / (sigS σ s * sigS σ t) := by
  rw [badEvent_lawMat_eq hσ Xm hz, norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (badEvent_sigS_pos hσ s).le,
    Real.norm_of_nonneg (badEvent_sigS_pos hσ t).le]

/-- For `Σ = diag(σ)`, `σ > 0`: `|B_{st}| ≤ Λ` and, for `s ≠ t`, `|B_{st}| ≤ Λ_o`. -/
theorem norm_lawMat_le_Lambda {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (s t : Fin M ⊕ Fin N) :
    ‖lawMat (diagonal σ) Xm z s t‖ ≤ Lambda σ Xm z ∧
      (s ≠ t → ‖lawMat (diagonal σ) Xm z s t‖ ≤ LambdaO σ Xm z) := by
  rw [badEvent_norm_lawMat hσ Xm hz]
  refine ⟨?_, fun hst => ?_⟩
  · unfold Lambda
    refine le_trans ?_ (le_ciSup (Set.finite_range _).bddAbove s)
    exact le_ciSup (f := fun t => ‖G (diagonal σ) Xm z s t - (if s = t then mS N σ z s else 0)‖
      / (sigS σ s * sigS σ t)) (Set.finite_range _).bddAbove t
  · unfold LambdaO
    simp only [hst, ite_false, sub_zero]
    exact le_ciSup (f := fun p : {p : (Fin M ⊕ Fin N) × (Fin M ⊕ Fin N) // p.1 ≠ p.2} =>
      ‖G (diagonal σ) Xm z p.1.1 p.1.2‖ / (sigS σ p.1.1 * sigS σ p.1.2))
      (Set.finite_range _).bddAbove ⟨(s, t), hst⟩

/-- `Λ = max_{s,t} |B_{st}|`. -/
theorem Lambda_eq_sup_lawMat {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) :
    Lambda σ Xm z = ⨆ s : Fin M ⊕ Fin N, ⨆ t : Fin M ⊕ Fin N, ‖lawMat (diagonal σ) Xm z s t‖ := by
  unfold Lambda
  simp only [badEvent_norm_lawMat hσ Xm hz]

/-- `Λ ≥ 0`. -/
private theorem badEvent_Lambda_nonneg {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) : 0 ≤ Lambda σ Xm z :=
  Real.iSup_nonneg fun s => Real.iSup_nonneg fun t =>
    div_nonneg (norm_nonneg _) (mul_pos (badEvent_sigS_pos hσ s) (badEvent_sigS_pos hσ t)).le

/-- `Λ_o ≥ 0`. -/
private theorem badEvent_LambdaO_nonneg {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) : 0 ≤ LambdaO σ Xm z :=
  Real.iSup_nonneg fun _ =>
    div_nonneg (norm_nonneg _) (mul_pos (badEvent_sigS_pos hσ _) (badEvent_sigS_pos hσ _)).le

/-- `Λ_o ≤ Λ`. -/
private theorem badEvent_LambdaO_le_Lambda {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) :
    LambdaO σ Xm z ≤ Lambda σ Xm z := by
  refine Real.iSup_le (fun p => ?_) (badEvent_Lambda_nonneg hσ Xm z)
  obtain ⟨⟨s, t⟩, hst⟩ := p
  have h := (norm_lawMat_le_Lambda hσ Xm hz s t).1
  rw [badEvent_norm_lawMat hσ Xm hz] at h
  simpa [hst] using h

/-! ## The deterministic bound on `Λ_o` -/

/-- The Frobenius norm of a real matrix. -/
def frobNorm {N : ℕ} (Xm : Matrix (Fin M) (Fin N) ℝ) : ℝ := √(∑ i, ∑ μ, Xm i μ ^ 2)

/-- Completeness of a real orthonormal eigenbasis: `∑_k ζ_k ζ_kᵀ = 1`, entrywise. -/
private theorem badEvent_sum_eig_mul {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (μ ν : Fin N) :
    ∑ k, (hA.eigenvectorBasis k).ofLp μ * (hA.eigenvectorBasis k).ofLp ν
      = (1 : Matrix (Fin N) (Fin N) ℝ) μ ν := by
  have h := congrFun (congrFun (Unitary.coe_mul_star_self hA.eigenvectorUnitary) μ) ν
  rw [Unitary.coe_star, Matrix.mul_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [star_apply, hA.eigenvectorUnitary_apply, hA.eigenvectorUnitary_apply, star_trivial]

/-- Parseval: `∑_k (a · ζ_k)² = |a|²`. -/
private theorem badEvent_parseval {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (a : Fin N → ℝ) :
    ∑ k, (∑ μ, a μ * (hA.eigenvectorBasis k).ofLp μ) ^ 2 = ∑ μ, a μ ^ 2 := by
  calc ∑ k, (∑ μ, a μ * (hA.eigenvectorBasis k).ofLp μ) ^ 2
      = ∑ k, ∑ μ, ∑ ν, a μ * a ν
          * ((hA.eigenvectorBasis k).ofLp μ * (hA.eigenvectorBasis k).ofLp ν) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
        ring
    _ = ∑ μ, ∑ ν, a μ * a ν
          * ∑ k, (hA.eigenvectorBasis k).ofLp μ * (hA.eigenvectorBasis k).ofLp ν := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ν _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ μ, a μ ^ 2 := by
        simp only [badEvent_sum_eig_mul hA, one_apply, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq, Finset.mem_univ, ite_true, sq]

/-- `|aᵀ G_N b| ≤ |a| |b| / η` for real vectors `a, b`, by (GN_spec). -/
private theorem badEvent_bilin_GN_le {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (a b : Fin N → ℝ) :
    ‖∑ μ, ∑ ν, (a μ : ℂ) * GN (diagonal σ) Xm z μ ν * (b ν : ℂ)‖
      ≤ √(∑ μ, a μ ^ 2) * √(∑ ν, b ν ^ 2) / z.im := by
  have hSig : (diagonal σ).PosDef := posDef_diagonal_iff.2 hσ
  set hA := XSX_isHermitian hSig.1 Xm with hAdef
  set α : Fin N → ℝ := fun k => ∑ μ, a μ * (hA.eigenvectorBasis k).ofLp μ with hα
  set β : Fin N → ℝ := fun k => ∑ ν, b ν * (hA.eigenvectorBasis k).ofLp ν with hβ
  have e : ∑ μ, ∑ ν, (a μ : ℂ) * GN (diagonal σ) Xm z μ ν * (b ν : ℂ)
      = ∑ k, ((α k * β k : ℝ) : ℂ) / ((hA.eigenvalues k : ℂ) - z) := by
    have hr : ∀ k, ((α k * β k : ℝ) : ℂ) / ((hA.eigenvalues k : ℂ) - z)
        = ∑ μ, ∑ ν, (a μ : ℂ) * ((((hA.eigenvectorBasis k).ofLp μ
          * (hA.eigenvectorBasis k).ofLp ν : ℝ) : ℂ) / ((hA.eigenvalues k : ℂ) - z))
          * (b ν : ℂ) := by
      intro k
      simp only [hα, hβ, Finset.sum_mul_sum, Complex.ofReal_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
      push_cast
      ring
    rw [Finset.sum_congr rfl fun k _ => hr k]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [GN_spec hSig Xm hz, Finset.mul_sum, Finset.sum_mul]
  have hd : ∀ k, z.im ≤ ‖(hA.eigenvalues k : ℂ) - z‖ := by
    intro k
    have h := Complex.abs_im_le_norm ((hA.eigenvalues k : ℂ) - z)
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg, abs_of_pos hz] at h
    exact h
  have hCS : ∑ k, |α k| * |β k| ≤ √(∑ k, α k ^ 2) * √(∑ k, β k ^ 2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => |α k|) (fun k => |β k|)
    simp only [sq_abs] at h
    rw [← Real.sqrt_mul (Finset.sum_nonneg fun k _ => sq_nonneg _)]
    rw [← Real.sqrt_sq (Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg (α k))
      (abs_nonneg (β k)))]
    exact Real.sqrt_le_sqrt h
  rw [e]
  calc ‖∑ k, ((α k * β k : ℝ) : ℂ) / ((hA.eigenvalues k : ℂ) - z)‖
      ≤ ∑ k, ‖((α k * β k : ℝ) : ℂ) / ((hA.eigenvalues k : ℂ) - z)‖ := norm_sum_le _ _
    _ ≤ ∑ k, |α k| * |β k| / z.im := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_mul]
        exact div_le_div_of_nonneg_left (by positivity) hz (hd k)
    _ = (∑ k, |α k| * |β k|) / z.im := by rw [Finset.sum_div]
    _ ≤ √(∑ k, α k ^ 2) * √(∑ k, β k ^ 2) / z.im :=
        div_le_div_of_nonneg_right hCS hz.le
    _ = √(∑ μ, a μ ^ 2) * √(∑ ν, b ν ^ 2) / z.im := by
        rw [hα, hβ, badEvent_parseval hA a, badEvent_parseval hA b]

/-- `cplx(Σ̲) = diag(σ̲)` for `Σ = diag(σ)`. -/
private theorem badEvent_cplx_SigU {N : ℕ} (σ : Fin M → ℝ) :
    cplx (SigU (n := Fin N) (diagonal σ)) = diagonal fun s => (sigS σ s : ℂ) := by
  ext s t
  cases s <;> cases t <;>
    simp [SigU, sigS, diagonal_apply, one_apply, apply_ite (fun x : ℝ => (x : ℂ))]

/-- Off the diagonal, `G_{st} = σ̲_s (J G_N Jᵀ)_{st} σ̲_t` with `J = [X; 1]`, by (decompfullG). -/
private theorem badEvent_G_offdiag {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) {s t : Fin M ⊕ Fin N} (hst : s ≠ t) :
    G (diagonal σ) Xm z s t = (sigS σ s : ℂ)
      * (∑ μ, ∑ ν, (Jmat Xm s μ : ℂ) * GN (diagonal σ) Xm z μ ν * (Jmat Xm t ν : ℂ))
      * (sigS σ t : ℂ) := by
  have hSig : (diagonal σ).PosDef := posDef_diagonal_iff.2 hσ
  have h0 : cplx (fromBlocks (diagonal σ) 0 0 (0 : Matrix (Fin N) (Fin N) ℝ)) s t = 0 := by
    cases s <;> cases t <;> simp_all
  rw [decompfullG hSig Xm hz, Matrix.add_apply, Matrix.neg_apply, h0, neg_zero, zero_add,
    badEvent_cplx_SigU]
  simp only [Matrix.mul_assoc]
  rw [Matrix.diagonal_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_diagonal, mul_assoc]
  congr 2
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul,
    Complex.coe_algebraMap]
  rw [Finset.sum_comm]

/-- The rows of `J = [X; 1]` have length at most `1 + ‖X‖_F`. -/
private theorem badEvent_row_le {N : ℕ} (Xm : Matrix (Fin M) (Fin N) ℝ) (s : Fin M ⊕ Fin N) :
    √(∑ μ, Jmat Xm s μ ^ 2) ≤ 1 + frobNorm Xm := by
  have hF : 0 ≤ frobNorm Xm := Real.sqrt_nonneg _
  cases s with
  | inl k =>
    have h : √(∑ μ, Jmat Xm (Sum.inl k) μ ^ 2) ≤ frobNorm Xm := by
      unfold frobNorm
      refine Real.sqrt_le_sqrt ?_
      simp only [Jmat, fromRows_apply_inl]
      exact Finset.single_le_sum (f := fun i => ∑ μ, Xm i μ ^ 2)
        (fun i _ => Finset.sum_nonneg fun μ _ => sq_nonneg _) (Finset.mem_univ k)
    linarith
  | inr ν =>
    have h : ∑ μ, Jmat Xm (Sum.inr ν) μ ^ 2 = 1 := by
      simp [Jmat, fromRows_apply_inr, one_apply]
    rw [h, Real.sqrt_one]
    linarith

/-- Deterministic bound: `Λ_o ≤ (1 + ‖X‖_F)² / η`, independent of `σ`. -/
theorem LambdaO_le_frob {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) :
    LambdaO σ Xm z ≤ (1 + frobNorm Xm) ^ 2 / z.im := by
  have hF : 0 ≤ frobNorm Xm := Real.sqrt_nonneg _
  refine Real.iSup_le (fun p => ?_) (by positivity)
  obtain ⟨⟨s, t⟩, hst⟩ := p
  have hs := badEvent_sigS_pos (N := N) hσ s
  have ht := badEvent_sigS_pos (N := N) hσ t
  simp only
  rw [badEvent_G_offdiag hσ Xm hz hst, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg hs.le, Real.norm_of_nonneg ht.le,
    show sigS σ s * ‖∑ μ, ∑ ν, (Jmat Xm s μ : ℂ) * GN (diagonal σ) Xm z μ ν * (Jmat Xm t ν : ℂ)‖
        * sigS σ t / (sigS σ s * sigS σ t)
      = ‖∑ μ, ∑ ν, (Jmat Xm s μ : ℂ) * GN (diagonal σ) Xm z μ ν * (Jmat Xm t ν : ℂ)‖ by
      field_simp]
  refine (badEvent_bilin_GN_le hσ Xm hz (Jmat Xm s) (Jmat Xm t)).trans ?_
  refine div_le_div_of_nonneg_right ?_ hz.le
  rw [sq]
  exact mul_le_mul (badEvent_row_le Xm s) (badEvent_row_le Xm t) (Real.sqrt_nonneg _)
    (by linarith)

/-! ## Gaussian moments and the bad event -/

/-- `‖X‖_F² = ∑ X_{iμ}²`. -/
private theorem badEvent_frob_sq {N : ℕ} (Xm : Matrix (Fin M) (Fin N) ℝ) :
    frobNorm Xm ^ 2 = ∑ i, ∑ μ, Xm i μ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- Power mean: `‖X‖_F^{2(k+1)} ≤ (MN)^k ∑ X_{iμ}^{2(k+1)}`. -/
private theorem badEvent_frob_pow_le {N : ℕ} (Xm : Matrix (Fin M) (Fin N) ℝ) (k : ℕ) :
    frobNorm Xm ^ (2 * (k + 1)) ≤ ((M : ℝ) * N) ^ k * ∑ i, ∑ μ, Xm i μ ^ (2 * (k + 1)) := by
  rw [pow_mul, badEvent_frob_sq]
  calc (∑ i, ∑ μ, Xm i μ ^ 2) ^ (k + 1)
      ≤ (M : ℝ) ^ k * ∑ i, (∑ μ, Xm i μ ^ 2) ^ (k + 1) := by
        simpa using pow_sum_le_card_mul_sum_pow (s := Finset.univ)
          (f := fun i => ∑ μ, Xm i μ ^ 2)
          (fun i _ => Finset.sum_nonneg fun μ _ => sq_nonneg _) k
    _ ≤ (M : ℝ) ^ k * ∑ i, (N : ℝ) ^ k * ∑ μ, (Xm i μ ^ 2) ^ (k + 1) := by
        gcongr with i
        simpa using pow_sum_le_card_mul_sum_pow (s := Finset.univ) (f := fun μ => Xm i μ ^ 2)
          (fun μ _ => sq_nonneg _) k
    _ = ((M : ℝ) * N) ^ k * ∑ i, ∑ μ, Xm i μ ^ (2 * (k + 1)) := by
        simp only [Finset.mul_sum, ← pow_mul]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun μ _ => ?_
        ring

/-- `g_m ≥ 0`. -/
private theorem badEvent_gaussMoment_nonneg (m : ℕ) : 0 ≤ gaussMoment m :=
  integral_nonneg fun x => pow_nonneg (abs_nonneg x) m

section Moments

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- A Gaussian ensemble is a measurable random matrix. -/
private theorem badEvent_measurable_X {N : ℕ} {X : Ω → Matrix (Fin M) (Fin N) ℝ}
    (hX : IsGaussianEnsemble X) : Measurable X :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun μ => hX.measurable i μ

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- `‖X‖_F` is measurable. -/
private theorem badEvent_measurable_frob {N : ℕ} {X : Ω → Matrix (Fin M) (Fin N) ℝ}
    (hX : IsGaussianEnsemble X) : Measurable fun ω => frobNorm (X ω) := by
  unfold frobNorm
  exact (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun μ _ =>
    (hX.measurable i μ).pow_const 2).sqrt

/-- `E X_{iμ}^{2k} ≤ g_{2k} N^{−k}`, with integrability. -/
private theorem badEvent_entry_moment {N : ℕ} {X : Ω → Matrix (Fin M) (Fin N) ℝ}
    (hX : IsGaussianEnsemble X) (hN : 1 ≤ N) (k : ℕ) (i : Fin M) (μ : Fin N) :
    Integrable (fun ω => X ω i μ ^ (2 * k)) ∧
      ∫ ω, X ω i μ ^ (2 * k) ≤ gaussMoment (2 * k) / (N : ℝ) ^ k := by
  have hE := hX.entryAssumption hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNk : (0 : ℝ) < (N : ℝ) ^ k := pow_pos hNpos k
  have e : ∀ ω, |Real.sqrt N * X ω i μ| ^ (2 * k) = (N : ℝ) ^ k * X ω i μ ^ (2 * k) := by
    intro ω
    rw [pow_mul, sq_abs, mul_pow, Real.sq_sqrt hNpos.le, mul_pow, ← pow_mul]
  have hint := hE.integrable_moment (2 * k) i μ
  have hmom := hE.moment (2 * k) i μ
  simp only [e] at hint hmom
  have hint' : Integrable (fun ω => X ω i μ ^ (2 * k)) := by
    refine (hint.const_mul ((N : ℝ) ^ k)⁻¹).congr (ae_of_all _ fun ω => ?_)
    field_simp
  refine ⟨hint', ?_⟩
  rw [integral_const_mul] at hmom
  rw [le_div_iff₀ hNk]
  linarith

/-- `E(1 + ‖X‖_F)^{2q} ≤ 2^{2q}(1 + M^q g_{2q})`, `g_q = E|ζ|^q` for `ζ ∼ N(0,1)`. -/
theorem integral_one_add_frob_pow_le {N : ℕ} {X : Ω → Matrix (Fin M) (Fin N) ℝ}
    (hX : IsGaussianEnsemble X) (hN : 1 ≤ N) (q : ℕ) :
    Integrable (fun ω => (1 + frobNorm (X ω)) ^ (2 * q)) ∧
      ∫ ω, (1 + frobNorm (X ω)) ^ (2 * q) ≤
        2 ^ (2 * q) * (1 + (M : ℝ) ^ q * gaussMoment (2 * q)) := by
  have hmeasF := badEvent_measurable_frob hX
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp only [mul_zero, pow_zero, one_mul]
    refine ⟨integrable_const _, ?_⟩
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
    linarith [badEvent_gaussMoment_nonneg 0]
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
  set n := 2 * (k + 1) with hn
  have hent := fun i μ => badEvent_entry_moment hX hN (k + 1) i μ
  set Bd : Ω → ℝ := fun ω => 2 ^ n * (1 + ((M : ℝ) * N) ^ k * ∑ i, ∑ μ, X ω i μ ^ n) with hBd
  have hpt : ∀ ω, (1 + frobNorm (X ω)) ^ n ≤ Bd ω := by
    intro ω
    have hF : 0 ≤ frobNorm (X ω) := Real.sqrt_nonneg _
    have h1 := add_pow_le zero_le_one hF n
    have h2 := badEvent_frob_pow_le (X ω) k
    have h3 : (2 : ℝ) ^ (n - 1) ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) (Nat.sub_le n 1)
    have h4 : 0 ≤ 1 ^ n + frobNorm (X ω) ^ n := by positivity
    calc (1 + frobNorm (X ω)) ^ n ≤ 2 ^ (n - 1) * (1 ^ n + frobNorm (X ω) ^ n) := h1
      _ ≤ 2 ^ n * (1 ^ n + frobNorm (X ω) ^ n) := mul_le_mul_of_nonneg_right h3 h4
      _ ≤ Bd ω := by
          rw [hBd, one_pow]
          change 2 ^ n * (1 + frobNorm (X ω) ^ n)
            ≤ 2 ^ n * (1 + ((M : ℝ) * N) ^ k * ∑ i, ∑ μ, X ω i μ ^ n)
          gcongr
  have hsumint : Integrable fun ω => ∑ i, ∑ μ, X ω i μ ^ n :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun μ _ => (hent i μ).1
  have hBint : Integrable Bd :=
    ((integrable_const 1).add (hsumint.const_mul _)).const_mul _
  have hint : Integrable fun ω => (1 + frobNorm (X ω)) ^ n := by
    refine hBint.mono' ((hmeasF.const_add 1).pow_const n).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    have hF : 0 ≤ frobNorm (X ω) := Real.sqrt_nonneg _
    rw [Real.norm_of_nonneg (by positivity)]
    exact hpt ω
  refine ⟨hint, ?_⟩
  have hgn := badEvent_gaussMoment_nonneg n
  calc ∫ ω, (1 + frobNorm (X ω)) ^ n ≤ ∫ ω, Bd ω := integral_mono hint hBint hpt
    _ = 2 ^ n * (1 + ((M : ℝ) * N) ^ k * ∑ i, ∑ μ, ∫ ω, X ω i μ ^ n) := by
        rw [hBd, integral_const_mul, integral_add (integrable_const 1) (hsumint.const_mul _),
          integral_const_mul, integral_finsetSum _ fun i _ =>
            integrable_finsetSum _ fun μ _ => (hent i μ).1]
        simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
        congr 3
        refine Finset.sum_congr rfl fun i _ => ?_
        exact integral_finsetSum _ fun μ _ => (hent i μ).1
    _ ≤ 2 ^ n * (1 + ((M : ℝ) * N) ^ k * ∑ _i : Fin M, ∑ _μ : Fin N,
          gaussMoment n / (N : ℝ) ^ (k + 1)) := by
        gcongr with i _ μ _
        exact (hent i μ).2
    _ = 2 ^ n * (1 + (M : ℝ) ^ (k + 1) * gaussMoment n) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
        ring

/-- `K_b(τ, p) = 2^{2p+1} (1+τ⁻¹)^p g'^{1/2}_{4p}`, `g'_q = max(1, g_q)`. -/
def lawBadConst (τ : ℝ) (p : ℕ) : ℝ :=
  2 ^ (2 * p + 1) * (1 + τ⁻¹) ^ p * √(max 1 (gaussMoment (4 * p)))

/-- `E(Λ_o^{2p}) ≤ (K_b N^{2p})²` on `𝐃(τ, N)` when `M ≤ τ⁻¹ N`; this is the moment input of the
Cauchy–Schwarz step. -/
private theorem badEvent_moment_arith {τ : ℝ} (hτ : 0 < τ) {N : ℕ} (hN : 1 ≤ N) (p : ℕ)
    (hM : (M : ℝ) ≤ τ⁻¹ * N) :
    (N : ℝ) ^ (2 * p) * (2 ^ (2 * (2 * p)) * (1 + (M : ℝ) ^ (2 * p) * gaussMoment (4 * p)))
      ≤ (lawBadConst τ p * (N : ℝ) ^ (2 * p)) ^ 2 := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set κ := 1 + τ⁻¹ with hκ
  set g := gaussMoment (4 * p) with hg
  set g' := max 1 g with hg'
  have hκ1 : 1 ≤ κ := by have := inv_pos.2 hτ; linarith
  have hg0 : 0 ≤ g := badEvent_gaussMoment_nonneg _
  have hg'1 : 1 ≤ g' := le_max_left _ _
  have hgg' : g ≤ g' := le_max_right _ _
  have hMκ : (M : ℝ) ≤ κ * N := hM.trans (by nlinarith)
  have hMp : (M : ℝ) ^ (2 * p) ≤ κ ^ (2 * p) * (N : ℝ) ^ (2 * p) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hMκ _
  have h1 : (1 : ℝ) ≤ κ ^ (2 * p) * (N : ℝ) ^ (2 * p) := one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ hκ1) (one_le_pow₀ hNr)
  have hNp : 0 ≤ (N : ℝ) ^ (2 * p) := by positivity
  have hsq : (√g') ^ 2 = g' := Real.sq_sqrt (by linarith)
  have hstep : 1 + (M : ℝ) ^ (2 * p) * g ≤ 2 * g' * (κ ^ (2 * p) * (N : ℝ) ^ (2 * p)) := by
    have hMp0 : 0 ≤ (M : ℝ) ^ (2 * p) := by positivity
    nlinarith [mul_le_mul hMp hgg' hg0 (by positivity : (0 : ℝ) ≤ κ ^ (2 * p) * (N : ℝ) ^ (2 * p))]
  calc (N : ℝ) ^ (2 * p) * (2 ^ (2 * (2 * p)) * (1 + (M : ℝ) ^ (2 * p) * g))
      ≤ (N : ℝ) ^ (2 * p) * (2 ^ (2 * (2 * p)) * (2 * g' * (κ ^ (2 * p) * (N : ℝ) ^ (2 * p)))) := by
        gcongr
    _ ≤ (N : ℝ) ^ (2 * p) * (2 ^ (2 * (2 * p)) * (4 * g' * (κ ^ (2 * p) * (N : ℝ) ^ (2 * p)))) := by
        gcongr
        linarith
    _ = (lawBadConst τ p * (N : ℝ) ^ (2 * p)) ^ 2 := by
        rw [lawBadConst, ← hκ, ← hg, ← hg', mul_pow, mul_pow, mul_pow, hsq]
        ring

/-- `E Λ_o^p ≤ b^p + K_b N^{2p} a^{1/2}` when `P(Λ > b) ≤ a`. -/
theorem integral_LambdaO_pow_le {τ : ℝ} (hτ : 0 < τ) {N : ℕ} (hN : 1 ≤ N)
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : IsGaussianEnsemble X) {σ : Fin M → ℝ}
    (hσ : ∀ i, 0 < σ i) (hM : (M : ℝ) ≤ τ⁻¹ * N) {z : ℂ} (hz : z ∈ specDomain τ N) (p : ℕ)
    {a b : ℝ} (hb : 0 ≤ b) (ha : ℙ {ω | b < Lambda σ (X ω) z} ≤ ENNReal.ofReal a) :
    Integrable (fun ω => LambdaO σ (X ω) z ^ p) ∧
      ∫ ω, LambdaO σ (X ω) z ^ p ≤ b ^ p + lawBadConst τ p * (N : ℝ) ^ (2 * p) * √a := by
  have hzim : 0 < z.im := hz.1
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  -- `η⁻¹ ≤ N` on `𝐃(τ, N)`
  have hηN : z.im⁻¹ ≤ N := by
    have h1 : (N : ℝ) ^ (-1 : ℝ) ≤ (N : ℝ) ^ (-1 + τ) :=
      Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
    rw [Real.rpow_neg_one] at h1
    exact (inv_le_comm₀ hzim hNpos).2 (h1.trans hz.2.2.2.1)
  have hL0 : ∀ ω, 0 ≤ LambdaO σ (X ω) z := fun ω => badEvent_LambdaO_nonneg hσ _ _
  have hLF : ∀ ω, LambdaO σ (X ω) z ≤ N * (1 + frobNorm (X ω)) ^ 2 := by
    intro ω
    calc LambdaO σ (X ω) z ≤ (1 + frobNorm (X ω)) ^ 2 / z.im := LambdaO_le_frob hσ (X ω) hzim
      _ = (1 + frobNorm (X ω)) ^ 2 * z.im⁻¹ := div_eq_mul_inv _ _
      _ ≤ (1 + frobNorm (X ω)) ^ 2 * N := mul_le_mul_of_nonneg_left hηN (sq_nonneg _)
      _ = N * (1 + frobNorm (X ω)) ^ 2 := mul_comm _ _
  have hLFk : ∀ k : ℕ, ∀ ω,
      LambdaO σ (X ω) z ^ k ≤ (N : ℝ) ^ k * (1 + frobNorm (X ω)) ^ (2 * k) := by
    intro k ω
    rw [pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (hL0 ω) (hLF ω) k
  -- measurability
  have hXm := badEvent_measurable_X hX
  have hLm : Measurable fun ω => LambdaO σ (X ω) z := by
    unfold LambdaO
    exact Measurable.iSup fun q =>
      (((measurable_G_apply (diagonal σ) z q.1.1 q.1.2).comp hXm).norm).div_const _
  have hΛm : Measurable fun ω => Lambda σ (X ω) z := by
    unfold Lambda
    exact Measurable.iSup fun s => Measurable.iSup fun t =>
      ((((measurable_G_apply (diagonal σ) z s t).comp hXm).sub_const _).norm).div_const _
  -- integrability of `Λ_o^k` for `k = p, 2p`
  have hint : ∀ k : ℕ, Integrable fun ω => LambdaO σ (X ω) z ^ k := by
    intro k
    refine (((integral_one_add_frob_pow_le hX hN k).1).const_mul ((N : ℝ) ^ k)).mono'
      (hLm.pow_const k).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (pow_nonneg (hL0 ω) k)]
    exact hLFk k ω
  refine ⟨hint p, ?_⟩
  -- the moment `E Λ_o^{2p}`
  have hE2 : ∫ ω, LambdaO σ (X ω) z ^ (2 * p) ≤ (lawBadConst τ p * (N : ℝ) ^ (2 * p)) ^ 2 := by
    have hT := integral_one_add_frob_pow_le hX hN (2 * p)
    rw [show 2 * (2 * p) = 4 * p by ring] at hT
    calc ∫ ω, LambdaO σ (X ω) z ^ (2 * p)
        ≤ ∫ ω, (N : ℝ) ^ (2 * p) * (1 + frobNorm (X ω)) ^ (4 * p) := by
          refine integral_mono (hint _) (hT.1.const_mul _) fun ω => ?_
          have := hLFk (2 * p) ω
          rwa [show 2 * (2 * p) = 4 * p by ring] at this
      _ = (N : ℝ) ^ (2 * p) * ∫ ω, (1 + frobNorm (X ω)) ^ (4 * p) := integral_const_mul _ _
      _ ≤ (N : ℝ) ^ (2 * p) * (2 ^ (4 * p) * (1 + (M : ℝ) ^ (2 * p) * gaussMoment (4 * p))) :=
          mul_le_mul_of_nonneg_left hT.2 (by positivity)
      _ ≤ (lawBadConst τ p * (N : ℝ) ^ (2 * p)) ^ 2 := by
          have := badEvent_moment_arith hτ hN p hM
          rwa [show 2 * (2 * p) = 4 * p by ring] at this
  -- the bad event `A = {Λ > b}`
  set A := {ω | b < Lambda σ (X ω) z} with hA
  have hAm : MeasurableSet A := measurableSet_lt measurable_const hΛm
  have hpt : ∀ ω, LambdaO σ (X ω) z ^ p
      ≤ b ^ p + LambdaO σ (X ω) z ^ p * A.indicator 1 ω := by
    intro ω
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω, Pi.one_apply, mul_one]
      linarith [pow_nonneg hb p]
    · rw [Set.indicator_of_notMem hω, mul_zero, add_zero]
      have hΛ : Lambda σ (X ω) z ≤ b := not_lt.1 hω
      exact pow_le_pow_left₀ (hL0 ω) ((badEvent_LambdaO_le_Lambda hσ (X ω) hzim).trans hΛ) p
  have hind : Integrable fun ω => LambdaO σ (X ω) z ^ p * A.indicator 1 ω := by
    have h := (hint p).indicator hAm
    refine h.congr (ae_of_all _ fun ω => ?_)
    by_cases hω : ω ∈ A <;> simp [hω]
  -- Cauchy–Schwarz on `A`
  have hCS : ∫ ω, LambdaO σ (X ω) z ^ p * A.indicator 1 ω
      ≤ √(∫ ω, LambdaO σ (X ω) z ^ (2 * p)) * √((ℙ A).toReal) := by
    have hf2 : MemLp (fun ω => LambdaO σ (X ω) z ^ p) (ENNReal.ofReal 2) ℙ := by
      rw [show ENNReal.ofReal 2 = 2 by simp]
      refine (memLp_two_iff_integrable_sq (hLm.pow_const p).aestronglyMeasurable).2 ?_
      refine (hint (2 * p)).congr (ae_of_all _ fun ω => ?_)
      simp only
      ring
    have hg2 : MemLp (A.indicator (1 : Ω → ℝ)) (ENNReal.ofReal 2) ℙ :=
      memLp_indicator_const _ hAm.nullMeasurableSet (1 : ℝ) (Or.inr (measure_ne_top _ _))
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (ae_of_all _ fun ω => pow_nonneg (hL0 ω) p)
      (ae_of_all _ fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω) hf2 hg2
    have e1 : ∀ ω, (LambdaO σ (X ω) z ^ p) ^ (2 : ℝ) = LambdaO σ (X ω) z ^ (2 * p) := by
      intro ω
      rw [Real.rpow_two, ← pow_mul, mul_comm]
    have e2 : ∀ ω, (A.indicator (1 : Ω → ℝ) ω) ^ (2 : ℝ) = A.indicator 1 ω := by
      intro ω
      by_cases hω : ω ∈ A <;> simp [hω]
    calc ∫ ω, LambdaO σ (X ω) z ^ p * A.indicator 1 ω
        ≤ (∫ ω, (LambdaO σ (X ω) z ^ p) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
          * (∫ ω, (A.indicator (1 : Ω → ℝ) ω) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := h
      _ = √(∫ ω, LambdaO σ (X ω) z ^ (2 * p)) * √((ℙ A).toReal) := by
        rw [integral_congr_ae (ae_of_all _ e1), integral_congr_ae (ae_of_all _ e2),
          integral_indicator_one hAm, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, measureReal_def]
  have hPA : √((ℙ A).toReal) ≤ √a := by
    rcases le_or_gt 0 a with ha0 | ha0
    · exact Real.sqrt_le_sqrt (ENNReal.toReal_le_of_le_ofReal ha0 ha)
    · have h0 : ℙ A = 0 := le_antisymm (ha.trans (by rw [ENNReal.ofReal_of_nonpos ha0.le])) bot_le
      rw [h0, ENNReal.toReal_zero, Real.sqrt_zero]
      exact Real.sqrt_nonneg _
  have hK : 0 ≤ lawBadConst τ p * (N : ℝ) ^ (2 * p) := by
    have hκ : 0 < 1 + τ⁻¹ := by have := inv_pos.2 hτ; linarith
    unfold lawBadConst
    positivity
  have hE2' : √(∫ ω, LambdaO σ (X ω) z ^ (2 * p)) ≤ lawBadConst τ p * (N : ℝ) ^ (2 * p) := by
    rw [← Real.sqrt_sq hK]
    exact Real.sqrt_le_sqrt hE2
  calc ∫ ω, LambdaO σ (X ω) z ^ p
      ≤ ∫ ω, (b ^ p + LambdaO σ (X ω) z ^ p * A.indicator 1 ω) :=
        integral_mono (hint p) ((integrable_const _).add hind) hpt
    _ = b ^ p + ∫ ω, LambdaO σ (X ω) z ^ p * A.indicator 1 ω := by
        rw [integral_add (integrable_const _) hind]
        simp
    _ ≤ b ^ p + √(∫ ω, LambdaO σ (X ω) z ^ (2 * p)) * √((ℙ A).toReal) := by linarith
    _ ≤ b ^ p + lawBadConst τ p * (N : ℝ) ^ (2 * p) * √a := by
        gcongr

/-- Union bound over the `(M + N)²` entries. -/
theorem measure_Lambda_gt_le {N : ℕ} {ε₁ D₁ : ℝ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} {S : Set ℂ}
    (h : EntrywiseLawAt N ε₁ D₁ (diagonal σ) X S) {z : ℂ} (hz : z ∈ S) (hzim : 0 < z.im) :
    ℙ {ω | (N : ℝ) ^ ε₁ * Psi N σ z < Lambda σ (X ω) z} ≤
      ENNReal.ofReal (((M : ℝ) + N) ^ 2 * (N : ℝ) ^ (-D₁)) := by
  have hPsi : Psi N (specOf (diagonal σ)) z = Psi N σ z := by
    unfold Psi
    rw [mFun_specOf_diagonal]
  have hPsi0 : 0 ≤ Psi N σ z := by
    unfold Psi
    exact add_nonneg (Real.sqrt_nonneg _)
      (div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) hzim.le))
  set c := (N : ℝ) ^ ε₁ * Psi N σ z with hc
  have hc0 : 0 ≤ c := mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hPsi0
  have hsub : {ω | c < Lambda σ (X ω) z}
      ⊆ ⋃ s, ⋃ t, {ω | c < ‖lawMat (diagonal σ) (X ω) z s t‖} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion] at hω ⊢
    by_contra hne
    push Not at hne
    have hle : Lambda σ (X ω) z ≤ c := by
      rw [Lambda_eq_sup_lawMat hσ (X ω) hzim]
      exact Real.iSup_le (fun s => Real.iSup_le (fun t => hne s t) hc0) hc0
    linarith
  have hent : ∀ s t, ℙ {ω | c < ‖lawMat (diagonal σ) (X ω) z s t‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D₁)) := by
    intro s t
    have h1 := h z hz s t
    unfold ODomAt DomAt at h1
    rwa [hPsi] at h1
  calc ℙ {ω | c < Lambda σ (X ω) z}
      ≤ ℙ (⋃ s, ⋃ t, {ω | c < ‖lawMat (diagonal σ) (X ω) z s t‖}) := measure_mono hsub
    _ ≤ ∑ s, ℙ (⋃ t, {ω | c < ‖lawMat (diagonal σ) (X ω) z s t‖}) :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ s, ∑ t, ℙ {ω | c < ‖lawMat (diagonal σ) (X ω) z s t‖} :=
        Finset.sum_le_sum fun s _ => measure_iUnion_fintype_le _ _
    _ ≤ ∑ _s : Fin M ⊕ Fin N, ∑ _t : Fin M ⊕ Fin N, ENNReal.ofReal ((N : ℝ) ^ (-D₁)) :=
        Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun t _ => hent s t
    _ = ENNReal.ofReal (((M : ℝ) + N) ^ 2 * (N : ℝ) ^ (-D₁)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin,
          nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (by positivity), show ((M : ℝ) + N) ^ 2 = ((M + N) ^ 2 : ℕ) by
          push_cast; ring, ENNReal.ofReal_natCast]
        push_cast
        ring

end Moments

/-! ## Checks at `M = N = 2`, `σ ≡ 1`, `τ = 1/3`, `z = i` -/

section Checks

/-- The moment bound for the Gaussian `2 × 2` matrix, `q = 2`. -/
example : Integrable (fun ω => (1 + frobNorm (gaussX 2 2 ω)) ^ (2 * 2)) ∧
    ∫ ω, (1 + frobNorm (gaussX 2 2 ω)) ^ (2 * 2)
      ≤ 2 ^ (2 * 2) * (1 + ((2 : ℕ) : ℝ) ^ 2 * gaussMoment (2 * 2)) :=
  integral_one_add_frob_pow_le (gaussX_isGaussianEnsemble 2 2) (by norm_num) 2

end Checks

end Anisotropic

#print axioms Anisotropic.norm_lawMat_le_Lambda
#print axioms Anisotropic.Lambda_eq_sup_lawMat
#print axioms Anisotropic.frobNorm
#print axioms Anisotropic.LambdaO_le_frob
#print axioms Anisotropic.integral_one_add_frob_pow_le
#print axioms Anisotropic.lawBadConst
#print axioms Anisotropic.integral_LambdaO_pow_le
#print axioms Anisotropic.measure_Lambda_gt_le
