import Anisotropic.Comparison.RoughBoundUpd
import Anisotropic.Comparison.Words
import Anisotropic.Framework.DominationMoment

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # Lemma 7.15: the Taylor expansion along one entry -/

/-!
Lemma 7.15 (`lem:taylor_exp`): along the entry `(i, μ)`, with `f(s) = F_v^p(X^{(iμ),s})` and
`f_n = f^{(n)}/n!` the coefficients `fCoeff p (resCoeff …) n`, the bound `|f_n(s)| ≺ N^{2δ(n+p)}`
holds uniformly in `|s| ≤ |y|` for `|y| ≺ N^{−1/2}`, and
`f(y) = ∑_{n ≤ 4p} yⁿ f_n(0) + O_≺(N^{−2} Ψ^p)`.

Proof structure. On the events of Lemma 7.14 at the test vectors `v`, `Σ̲e_{(i)}`, `Σ̲e_{(μ)}`, the
entries of `G(X^{(iμ),s})` and `F_v` are `O(N^{2δ+3ε_A})`, so (w_est) gives the coefficient
bound; the re-expansion with remainder of order `4p + 1` and `Ψ ≥ 1/(Nη) ≥ τ/N` give the
remainder.
-/

/-! ## Bilinear forms of `G`, `Σ̲⁻¹` and `Π` at `v̄` -/



/-! ## Deterministic bound on `F_v` -/


private theorem tayR_ent_sub {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (v w : ι → ℝ) :
    ent (A - B) v w = ent A v w - ent B v w := by
  simp [ent, sub_mulVec, dotProduct_sub]

private theorem tayR_ent_eq {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (x y : ι → ℝ) :
    ent A x y = ∑ s, ∑ t, (x s : ℂ) * A s t * (y t : ℂ) := by
  simp only [ent, cvec, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

private theorem tayR_ent_transpose {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (x y : ι → ℝ) :
    ent Aᵀ x y = ent A y x := by
  rw [tayR_ent_eq, tayR_ent_eq, Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
    simp only [transpose_apply]; ring

private theorem tayR_ent_eI_right {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (x : ι → ℝ) (r : ι) : ent A x (eI r) = ∑ s, (x s : ℂ) * A s r := by
  rw [tayR_ent_eq]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [eI, Pi.single_apply, apply_ite]

private theorem tayR_diag {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) :
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

private theorem tayR_sum_sq_UT {K : ℕ} {U : Matrix (Fin K) (Fin K) ℝ} (h₂ : U * Uᵀ = 1)
    (x : Fin K → ℝ) : ∑ i, (Uᵀ *ᵥ x) i ^ 2 = ∑ i, x i ^ 2 := by
  have e : (Uᵀ *ᵥ x) ⬝ᵥ (Uᵀ *ᵥ x) = x ⬝ᵥ x := by
    rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, h₂, one_mulVec, dotProduct_comm]
  simpa [dotProduct, sq] using e

private theorem tayR_row_sq {K : ℕ} {U : Matrix (Fin K) (Fin K) ℝ} (h₂ : U * Uᵀ = 1) (i : Fin K) :
    ∑ k, U i k ^ 2 = 1 := by
  have := congrFun (congrFun h₂ i) i
  simpa [Matrix.mul_apply, sq, Matrix.one_apply] using this

/-- `|Σ x|² ≤ τ⁻² |x|²` under (bound_Sigma). -/
private theorem tayR_sumsq_Sig {τ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hS : SigmaAssumption τ Sig) (x : Fin M → ℝ) :
    ∑ l, (Sig *ᵥ x) l ^ 2 ≤ τ⁻¹ ^ 2 * ∑ l, x l ^ 2 := by
  obtain ⟨U, h₂, h₁, hSd, hσ⟩ := tayR_diag hS.posDef
  have hle : ∀ k, specOf Sig k ≤ τ⁻¹ := fun k => by
    rw [specOf_eq hS.posDef.isHermitian]; exact hS.eigenvalues_le k
  have hUU : Uᵀ * Uᵀᵀ = 1 := by rw [transpose_transpose]; exact h₁
  have e : Sig *ᵥ x = Uᵀᵀ *ᵥ (diagonal (specOf Sig) *ᵥ (Uᵀ *ᵥ x)) := by
    rw [transpose_transpose, mulVec_mulVec, mulVec_mulVec]
    exact congrArg (· *ᵥ x) hSd
  rw [e, tayR_sum_sq_UT hUU, ← tayR_sum_sq_UT h₂ x, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [mulVec_diagonal, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hσ k).le (hle k) 2) (sq_nonneg _)

/-- `|Σ̲ y| ≤ τ⁻¹ |y|`. -/
private theorem tayR_testNorm_SigU {τ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hS : SigmaAssumption τ Sig) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (y : Fin M ⊕ Fin N → ℝ) :
    testNorm (SigU (n := Fin N) Sig *ᵥ y) ≤ τ⁻¹ * testNorm y := by
  have hτi : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  have h1 := tayR_sumsq_Sig hS (y ∘ Sum.inl)
  have h2 : 0 ≤ ∑ ν, y (Sum.inr ν) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h3 : 0 ≤ ∑ l, y (Sum.inl l) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  unfold testNorm
  rw [← Real.sqrt_sq (inv_pos.2 hτ).le, ← Real.sqrt_mul (sq_nonneg _)]
  refine Real.sqrt_le_sqrt ?_
  simp only [SigU, fromBlocks_mulVec, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    zero_mulVec, add_zero, zero_add, one_mulVec]
  simp only [Function.comp_def] at h1
  have h4 : ∑ ν, y (Sum.inr ν) ^ 2 ≤ τ⁻¹ ^ 2 * ∑ ν, y (Sum.inr ν) ^ 2 :=
    le_mul_of_one_le_left h2 (one_le_pow₀ hτi)
  rw [mul_add]
  exact add_le_add h1 h4

/-- `v̄` of `Σ̲ y` is `y`. -/
private theorem tayR_vbar_SigU {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (y : Fin M ⊕ Fin N → ℝ) : vbar Sig (SigU (n := Fin N) Sig *ᵥ y) = y := by
  have hS : Sig⁻¹ * Sig = 1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hSig.isUnit)
  funext s
  rcases s with j | ν
  · simp [vbar, SigU, fromBlocks_mulVec, mulVec_mulVec, hS]
  · simp [vbar, SigU, fromBlocks_mulVec]


/-- `(1 + wΣ)⁻¹_{li} = ∑ₖ U_{lk} (1 + σₖ w)⁻¹ U_{ik}`. -/
private theorem tayR_cinv_entry {Sig U : Matrix (Fin M) (Fin M) ℝ} {σ : Fin M → ℝ}
    (h₂ : U * Uᵀ = 1) (h₁ : Uᵀ * U = 1) (hS : Sig = U * diagonal σ * Uᵀ) {w : ℂ}
    (hw : ∀ i, 1 + (σ i : ℂ) * w ≠ 0) (l i : Fin M) :
    (1 + w • cplx Sig)⁻¹ l i = ∑ k, (U l k : ℂ) * (1 + (σ k : ℂ) * w)⁻¹ * (U i k : ℂ) := by
  have c₂ : (cplx Uᵀ)ᵀ * cplx Uᵀ = 1 := by
    simp only [cplx]
    rw [← transpose_map, transpose_transpose, ← Matrix.map_mul, h₂,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have c₁ : cplx Uᵀ * (cplx Uᵀ)ᵀ = 1 := by
    simp only [cplx]
    rw [← transpose_map, transpose_transpose, ← Matrix.map_mul, h₁,
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
  rw [hinv]
  simp [Matrix.mul_apply, cplx, Matrix.diagonal_apply, mul_ite, Finset.sum_ite_eq']

private theorem tayR_abs_le_testNorm {ι : Type*} [Fintype ι] (x : ι → ℝ) (s : ι) :
    |x s| ≤ testNorm x := by
  unfold testNorm
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (fun t _ => sq_nonneg (x t)) (Finset.mem_univ s))

private theorem tayR_sqrt_inl_le (x : Fin M ⊕ Fin N → ℝ) :
    √(∑ j, x (Sum.inl j) ^ 2) ≤ testNorm x := by
  unfold testNorm
  refine Real.sqrt_le_sqrt ?_
  rw [Fintype.sum_sum_type]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- `|⟨v̄, Π e_p⟩| ≤ max(c⁻¹, K) |v|` when `|m| ≤ K` and `|1 + σᵢ m| ≥ c`. -/
private theorem tayR_pi_bound {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {c K : ℝ}
    (hc : 0 < c) {w : ℂ} (hwK : ‖w‖ ≤ K) (hOne : ∀ i, c ≤ ‖1 + (specOf Sig i : ℂ) * w‖)
    (x : Fin M ⊕ Fin N → ℝ) (p : Fin M ⊕ Fin N) :
    ‖ent (piMat (N := N) Sig w) (vbar Sig x) (eI p)‖ ≤ max c⁻¹ K * testNorm x := by
  rw [tayR_ent_eI_right, Fintype.sum_sum_type]
  rcases p with i | μ
  · simp only [piMat, fromBlocks_apply₁₁, fromBlocks_apply₂₁, Matrix.zero_apply, mul_zero,
      Finset.sum_const_zero, add_zero, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib, norm_neg]
    obtain ⟨U, h₂, h₁, hSd, hσ⟩ := tayR_diag hSig
    have hw0 : ∀ k, 1 + (specOf Sig k : ℂ) * w ≠ 0 := fun k h0 => by
      have := hOne k
      rw [h0, norm_zero] at this
      linarith
    set xM : Fin M → ℝ := fun j => x (Sum.inl j) with hxM
    have hSS : Sig * Sig⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hSig.isUnit)
    have hy : Sig *ᵥ (Sig⁻¹ *ᵥ xM) = xM := by rw [mulVec_mulVec, hSS, one_mulVec]
    have hT : Sigᵀ = Sig := by rw [← conjTranspose_eq_transpose_of_trivial]; exact hSig.1.eq
    have hsym : ∀ j l, Sig j l = Sig l j := fun j l => by
      conv_lhs => rw [← hT]
      rfl
    have e1 : ∑ j, ((vbar Sig x (Sum.inl j) : ℝ) : ℂ) * (cplx Sig * (1 + w • cplx Sig)⁻¹) j i =
        ∑ l, (xM l : ℂ) * (1 + w • cplx Sig)⁻¹ l i := by
      simp only [Matrix.mul_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      have e : xM l = ∑ j, Sig l j * (Sig⁻¹ *ᵥ xM) j := by
        conv_lhs => rw [← hy]
        rfl
      rw [e, Complex.ofReal_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [vbar, Sum.elim_inl, Function.comp_def, cplx, Matrix.map_apply,
        Complex.ofReal_mul, hsym l j, Complex.coe_algebraMap, ← hxM]
      ring
    have e2 : ∑ l, (xM l : ℂ) * (1 + w • cplx Sig)⁻¹ l i =
        ∑ k, (((Uᵀ *ᵥ xM) k : ℝ) : ℂ) * (1 + (specOf Sig k : ℂ) * w)⁻¹ * (U i k : ℂ) := by
      simp only [tayR_cinv_entry h₂ h₁ hSd hw0, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [mulVec, dotProduct, transpose_apply, Complex.ofReal_sum, Complex.ofReal_mul,
        Finset.sum_mul]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [e1, e2]
    have hb : ∀ k, ‖(((Uᵀ *ᵥ xM) k : ℝ) : ℂ) * (1 + (specOf Sig k : ℂ) * w)⁻¹ * (U i k : ℂ)‖ ≤
        c⁻¹ * (|(Uᵀ *ᵥ xM) k| * |U i k|) := by
      intro k
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, norm_inv]
      have hinv : ‖1 + (specOf Sig k : ℂ) * w‖⁻¹ ≤ c⁻¹ := inv_anti₀ hc (hOne k)
      have := mul_le_mul_of_nonneg_left hinv (abs_nonneg ((Uᵀ *ᵥ xM) k))
      nlinarith [abs_nonneg (U i k), abs_nonneg ((Uᵀ *ᵥ xM) k)]
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun k => |(Uᵀ *ᵥ xM) k|)
      (fun k => |U i k|)
    simp only [sq_abs] at hcs
    rw [tayR_sum_sq_UT h₂, tayR_row_sq h₂, Real.sqrt_one, mul_one] at hcs
    have hc0 : 0 ≤ c⁻¹ := (inv_pos.2 hc).le
    calc _ ≤ ∑ k, c⁻¹ * (|(Uᵀ *ᵥ xM) k| * |U i k|) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => hb k)
      _ ≤ c⁻¹ * √(∑ j, xM j ^ 2) := by
          rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hcs hc0
      _ ≤ max c⁻¹ K * testNorm x :=
          mul_le_mul (le_max_left _ _) (tayR_sqrt_inl_le x) (Real.sqrt_nonneg _)
            (hc0.trans (le_max_left _ _))
  · simp only [piMat, fromBlocks_apply₁₂, fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero,
      Finset.sum_const_zero, zero_add, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
      mul_one, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [vbar, Sum.elim_inr, Function.comp_apply]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul (hwK.trans (le_max_right _ _)) (tayR_abs_le_testNorm x _) (abs_nonneg _)
      ((norm_nonneg w).trans (hwK.trans (le_max_right _ _)))


/-- `|⟨v̄, G e_p⟩| ≤ |⟨v, Σ̲⁻¹(G − Π)Σ̲⁻¹ (Σ̲ e_p)⟩| + max(c⁻¹, K) |v|`. -/
private theorem tayR_G_left {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {c K : ℝ}
    (hc : 0 < c) {z : ℂ} (hwK : ‖mFun N (specOf Sig) z‖ ≤ K)
    (hOne : ∀ i, c ≤ ‖1 + (specOf Sig i : ℂ) * mFun N (specOf Sig) z‖)
    (A : Matrix (Fin M) (Fin N) ℝ) (x : Fin M ⊕ Fin N → ℝ) (p : Fin M ⊕ Fin N) :
    ‖ent (G Sig A z) (vbar Sig x) (eI p)‖ ≤
      ‖testBilin x (lawMat Sig A z) (SigU (n := Fin N) Sig *ᵥ eI p)‖ + max c⁻¹ K * testNorm x := by
  have e : ent (G Sig A z) (vbar Sig x) (eI p) =
      ent (G Sig A z - PiZ N Sig z) (vbar Sig x) (vbar Sig (SigU (n := Fin N) Sig *ᵥ eI p)) +
        ent (PiZ N Sig z) (vbar Sig x) (eI p) := by
    rw [tayR_vbar_SigU hSig, tayR_ent_sub]; ring
  rw [e, ent_vbar_eq_testBilin hSig]
  exact (norm_add_le _ _).trans (add_le_add le_rfl (tayR_pi_bound hSig hc hwK hOne x p))


/-- The setting of §7 gives the density assumptions on the eigenvalues of `Σ` (Lemma 4.10
input). -/
private theorem tayR_density {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) : DensityAssumptions τ N (specOf Sig) :=
  (IsModel.diagModel_specOf (Ω := GaussSpace M N)
    ⟨hset.ratio_ge, hset.ratio_le, (gaussX_isGaussianEnsemble M N).entryAssumption hN,
      hset.sigma⟩).densityAssumptions hset.pos

private theorem tayR_testNorm_eI {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι) :
    testNorm (eI p) = 1 := by
  unfold testNorm
  simp [eI, Pi.single_apply, Finset.sum_ite_eq']

/-! ## Rough deterministic bounds -/

/-- `Ψ ≥ 1/(Nη) ≥ τ/N` on `𝐃(τ, N)`. -/
private theorem tay_Psi_ge {τ : ℝ} {σ : Fin M → ℝ} {z : ℂ} (hN : 1 ≤ N) (hτ : 0 < τ)
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

/-! ## Continuity in the entries -/

/-- `F_v = |a_0|`. -/
private theorem tay_Fv_eq (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) :
    Fv Sig A z v = ‖resCoeff Sig A z v i μ 0‖ := by
  simp [resCoeff, Fv]

/-- `F_v^p = f_0` for even `p`. -/
private theorem tay_Fv_pow_eq {p : ℕ} (hp : Even p) (Sig : Matrix (Fin M) (Fin M) ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) :
    (Fv Sig A z v : ℂ) ^ p = fCoeff p (resCoeff Sig A z v i μ) 0 := by
  rw [fCoeff_zero hp, tay_Fv_eq Sig A z v i μ]

/-! ## Moments, Markov, events -/

private theorem tay_hp_mono {Ω : Type*} [MeasureSpace Ω] {N : ℕ} {D : ℝ} {A B : Set Ω}
    (h : A ⊆ B) (hA : HighProbAt N D A) : HighProbAt N D B :=
  (measure_mono (Set.compl_subset_compl.2 h)).trans hA

private theorem tay_le_rpow {K a : ℝ} (hK : 0 ≤ K) (ha : 0 < a) {N : ℕ}
    (hN : ⌈K ^ a⁻¹⌉₊ ≤ N) : K ≤ (N : ℝ) ^ a := by
  have h1 : K ^ a⁻¹ ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  calc K = (K ^ a⁻¹) ^ a := by rw [← Real.rpow_mul hK, inv_mul_cancel₀ ha.ne', Real.rpow_one]
    _ ≤ (N : ℝ) ^ a := Real.rpow_le_rpow (by positivity) h1 ha.le

private theorem tay_hp_level {Ω : Type*} [MeasureSpace Ω] {N : ℕ} {D D' : ℝ} {A : Set Ω}
    (hN : 1 ≤ N) (hD : D' ≤ D) (hA : HighProbAt N D A) : HighProbAt N D' A := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold HighProbAt at *
  exact hA.trans (ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)))

private theorem tay_abs_le_of_mem_uIcc {s t : ℝ} (hs : s ∈ Set.uIcc 0 t) : |s| ≤ |t| := by
  rcases Set.mem_uIcc.1 hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]; exact h2
  · rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]; linarith

/-! ## Lemma 7.15 -/

/-- The event of Lemma 7.15: `|y| ≤ N^{ε_A − 1/2}` and, for all `|s| ≤ |y|` and `n ≤ 4p + 1`,
`|f_n(s)| ≤ N^{(2δ+4ε_A)(n+p)}`, at a general `C₀`. -/
private theorem tay_event (τ c : ℝ) (C : ℕ → ℝ) (p : ℕ) (C₀ δ εA DA : ℝ) (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (hc : 0 < c) (hδ : 0 < δ) (hC₀ : 25 ≤ C₀) (hC₀δ : C₀ * δ ≤ τ / 4)
    (hεA : 0 < εA) (hεAδ : εA ≤ δ / 4) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ)
      (P : ModelClass M N) (m : ℕ), CompSetting τ c M N Sig S → 1 ≤ m →
      PropA N C P Sig S C₀ δ (m - 1) εA DA →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ) (y : Ω → ℝ), EntryAssumption C X → P Ω X →
        HighProbAt N DA {ω | |y ω| ≤ (N : ℝ) ^ (εA - 1 / 2)} →
        ∀ z ∈ levelSet N δ S m, ∀ (i : Fin M) (μ : Fin N) (v : Fin M ⊕ Fin N → ℝ),
          testNorm v = 1 →
          HighProbAt N (DA - 3) {ω | |y ω| ≤ (N : ℝ) ^ (εA - 1 / 2) ∧ ∀ s : ℝ, |s| ≤ |y ω| →
            ∀ n ≤ 4 * p + 1, ‖fCoeff p (resCoeff Sig (Xupd (X ω) i μ s) z v i μ) n‖ ≤
              (N : ℝ) ^ ((2 * δ + 4 * εA) * ((n : ℝ) + p))} := by
  obtain ⟨N₁, h₁⟩ := rough_bound_upd' τ c C C₀ δ εA DA hτ hτ1 hc hδ hC₀ hC₀δ hεA hεAδ
  set κ := max c⁻¹ (mBoundConst τ) with hκ
  have hκ0 : 0 ≤ κ := (inv_pos.2 hc).le.trans (le_max_left _ _)
  have hT0 : 0 ≤ τ⁻¹ := (inv_pos.2 hτ).le
  have hT1 : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  set Q₀ : ℝ := τ⁻¹ ^ 2 + κ * τ⁻¹ + κ + 1 with hQ₀
  have hQ₀1 : 1 ≤ Q₀ := by
    have : 0 ≤ κ * τ⁻¹ := mul_nonneg hκ0 hT0
    nlinarith [sq_nonneg τ⁻¹]
  set K₀ : ℝ := (4 * p + 2) * (2 * Q₀) with hK₀
  have hK₀0 : 0 ≤ K₀ := by positivity
  refine ⟨max (max N₁ 10) ⌈K₀ ^ εA⁻¹⌉₊, ?_⟩
  intro N hN M Sig S P m hset hm hA Ω _ _ X y hX hP hy z hz i μ v hv
  have hNN₁ : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN10 : 10 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN1 : 1 ≤ N := by omega
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : (0 : ℝ) < N := by linarith
  have hKN : K₀ ≤ (N : ℝ) ^ εA := tay_le_rpow hK₀0 hεA (le_trans (le_max_right _ _) hN)
  set L : Fin 3 → Fin M ⊕ Fin N → ℝ := ![v, SigU (n := Fin N) Sig *ᵥ eI (Sum.inl i),
    SigU (n := Fin N) Sig *ᵥ eI (Sum.inr μ)] with hL
  set E : ℝ := (N : ℝ) ^ (2 * δ + 3 * εA) with hE
  let Ev : (Fin 3 × Fin 3) ⊕ Unit → Set Ω := Sum.elim
    (fun jk => {ω | ∀ s : ℝ, |s| ≤ |y ω| →
      ‖testBilin (L jk.1) (lawMat Sig (Xupd (X ω) i μ s) z) (L jk.2)‖ ≤
        E * testNorm (L jk.1) * testNorm (L jk.2)})
    (fun _ => {ω | |y ω| ≤ (N : ℝ) ^ (εA - 1 / 2)})
  have hEv : ∀ ι ∈ (Finset.univ : Finset ((Fin 3 × Fin 3) ⊕ Unit)),
      HighProbAt N (DA - 3 + 1) (Ev ι) := by
    intro ι _
    rw [show DA - 3 + 1 = DA - 2 by ring]
    rcases ι with ⟨j, k⟩ | u
    · exact h₁ N hNN₁ M Sig S P m hset hm hA Ω X y hX hP hy z hz i μ (L j) (L k)
    · exact tay_hp_level hN1 (by linarith) hy
  have hcard : ((Finset.univ : Finset ((Fin 3 × Fin 3) ⊕ Unit)).card : ℝ) ≤
      (N : ℝ) ^ (1 : ℝ) := by
    rw [Real.rpow_one, Finset.card_univ]
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_unit]
    have : (10 : ℝ) ≤ N := by exact_mod_cast hN10
    norm_num
    linarith
  have hall := HighProbAt.biInter Finset.univ hN1 hcard hEv
  refine tay_hp_mono (fun ω hω => ?_) hall
  have hω' : ∀ ι, ω ∈ Ev ι := fun ι => Set.mem_iInter₂.1 hω ι (Finset.mem_univ _)
  refine ⟨hω' (Sum.inr ()), fun s hs n hn => ?_⟩
  have hb : ∀ j k, ‖testBilin (L j) (lawMat Sig (Xupd (X ω) i μ s) z) (L k)‖ ≤
      E * testNorm (L j) * testNorm (L k) := fun j k => hω' (Sum.inl (j, k)) s hs
  have hSig := hset.sigma.posDef
  have hzS : z ∈ S := hz.1
  have hzD := hset.domain.1 hzS
  have hη : 0 < z.im := hzD.1
  have hm := (gen_prop_m_specDomain (tayR_density hset hN1) hzD).2.1
  have hOne := hset.oneXm z hzS
  have hE1 : 1 ≤ E := Real.one_le_rpow hN1r (by linarith)
  have hu : ∀ p, testNorm (SigU (n := Fin N) Sig *ᵥ eI p) ≤ τ⁻¹ := fun p => by
    have := tayR_testNorm_SigU (N := N) hset.sigma hτ hset.le_one (eI p)
    rwa [tayR_testNorm_eI, mul_one] at this
  have hLn : ∀ j, testNorm (L j) ≤ τ⁻¹ := by
    intro j
    fin_cases j
    · simp only [hL, Fin.zero_eta, Matrix.cons_val_zero]; rw [hv]; exact hT1
    · exact hu _
    · exact hu _
  have hbil : ∀ j k, ‖testBilin (L j) (lawMat Sig (Xupd (X ω) i μ s) z) (L k)‖ ≤
      E * τ⁻¹ * τ⁻¹ := by
    intro j k
    refine (hb j k).trans ?_
    have h0j : 0 ≤ testNorm (L j) := Real.sqrt_nonneg _
    have h0k : 0 ≤ testNorm (L k) := Real.sqrt_nonneg _
    have hE0 : 0 ≤ E := by linarith
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hLn j) hE0) (hLn k) h0k
      (mul_nonneg hE0 (inv_pos.2 hτ).le)
  set A := Xupd (X ω) i μ s with hAdef
  set B : ℝ := E * Q₀ with hB
  have hB1 : 1 ≤ B := one_le_mul_of_one_le_of_one_le hE1 hQ₀1
  have key : ∀ (x : Fin M ⊕ Fin N → ℝ) (q : Fin M ⊕ Fin N), testNorm x ≤ τ⁻¹ →
      ‖testBilin x (lawMat Sig A z) (SigU (n := Fin N) Sig *ᵥ eI q)‖ ≤ E * τ⁻¹ * τ⁻¹ →
      ‖ent (G Sig A z) (vbar Sig x) (eI q)‖ ≤ B := by
    intro x q hx hxq
    refine (tayR_G_left hSig hc hm hOne A x q).trans ?_
    have h1 : κ * testNorm x ≤ κ * τ⁻¹ := mul_le_mul_of_nonneg_left hx hκ0
    have h2 : κ * τ⁻¹ ≤ E * (κ * τ⁻¹) := le_mul_of_one_le_left (mul_nonneg hκ0 hT0) hE1
    have h3 : 0 ≤ E * κ + E := by positivity
    rw [hB, hQ₀]
    nlinarith
  have hv1 : testNorm v ≤ τ⁻¹ := by rw [hv]; exact hT1
  have hL1 : L 1 = SigU (n := Fin N) Sig *ᵥ eI (Sum.inl i) := rfl
  have hL2 : L 2 = SigU (n := Fin N) Sig *ᵥ eI (Sum.inr μ) := rfl
  have hL0 : L 0 = v := rfl
  have hvi : ‖ent (G Sig A z) (vbar Sig v) (eI (Sum.inl i))‖ ≤ B :=
    key v _ hv1 (by have := hbil 0 1; rwa [hL0, hL1] at this)
  have hvμ : ‖ent (G Sig A z) (vbar Sig v) (eI (Sum.inr μ))‖ ≤ B :=
    key v _ hv1 (by have := hbil 0 2; rwa [hL0, hL2] at this)
  have hG : ∀ q p : Fin M ⊕ Fin N, (q = Sum.inl i ∨ q = Sum.inr μ) →
      (p = Sum.inl i ∨ p = Sum.inr μ) → ‖G Sig A z q p‖ ≤ B := by
    intro q p hq hp
    rw [← ent_eI_eI (G Sig A z) q p, ← tayR_vbar_SigU (N := N) hSig (eI q)]
    obtain ⟨jq, hjq⟩ : ∃ j, L j = SigU (n := Fin N) Sig *ᵥ eI q := by
      rcases hq with rfl | rfl
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    obtain ⟨jp, hjp⟩ : ∃ j, L j = SigU (n := Fin N) Sig *ᵥ eI p := by
      rcases hp with rfl | rfl
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    refine key _ p (hu q) ?_
    have := hbil jq jp
    rwa [hjq, hjp] at this
  have h0 : Fv Sig A z v ≤ B := by
    unfold Fv
    rw [ent_vbar_eq_testBilin hSig]
    have := hbil 0 0
    rw [hL0] at this
    have hE0 : 0 ≤ E := by linarith
    calc _ ≤ E * τ⁻¹ * τ⁻¹ := this
      _ ≤ B := by rw [hB, hQ₀]; nlinarith [mul_nonneg hκ0 hT0]
  have h1 : ∀ b, ‖ent (G Sig A z) (vbar Sig v) (eI (letterT i μ b))‖ ≤ B := by
    intro b; cases b
    · exact hvμ
    · exact hvi
  have h2 : ∀ b, ‖ent (G Sig A z) (eI (letterS i μ b)) (vbar Sig v)‖ ≤ B := by
    intro b
    rw [← tayR_ent_transpose, G_transpose hSig A hη]
    cases b
    · exact hvi
    · exact hvμ
  have h3 : ∀ b b', ‖G Sig A z (letterS i μ b) (letterT i μ b')‖ ≤ B := by
    intro b b'
    refine hG _ _ ?_ ?_
    · cases b <;> simp [letterS]
    · cases b' <;> simp [letterT]
  have hres : ∀ k, ‖resCoeff Sig A z v i μ k‖ ≤ (2 * B) ^ (k + 1) := by
    intro k
    refine (norm_resCoeff_le hSig A hη v i μ h0 h1 h2 h3 k).trans ?_
    have hB0 : 0 ≤ B ^ (k + 1) := by positivity
    calc (2 : ℝ) ^ k * B ^ (k + 1) ≤ 2 ^ (k + 1) * B ^ (k + 1) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hB0
      _ = (2 * B) ^ (k + 1) := (mul_pow 2 B (k + 1)).symm
  have hf := norm_fCoeff_le p (B := 2 * B) (by linarith) n fun k _ => hres k
  refine hf.trans ?_
  have hn1 : (n : ℝ) + 1 ≤ 4 * p + 2 := by
    have : (n : ℝ) ≤ 4 * p + 1 := by exact_mod_cast hn
    linarith
  have h42 : (1 : ℝ) ≤ 4 * p + 2 := by have := (Nat.cast_nonneg p : (0 : ℝ) ≤ p); linarith
  have hpow1 : ((n : ℝ) + 1) ^ p ≤ (4 * (p : ℝ) + 2) ^ (n + p) :=
    (pow_le_pow_left₀ (by positivity) hn1 p).trans (pow_le_pow_right₀ h42 (by omega))
  have hK : (4 * (p : ℝ) + 2) * (2 * B) ≤ (N : ℝ) ^ εA * E := by
    have : (4 * (p : ℝ) + 2) * (2 * B) = K₀ * E := by rw [hK₀, hB]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hKN (by linarith)
  have hNE : (N : ℝ) ^ εA * E = (N : ℝ) ^ (2 * δ + 4 * εA) := by
    rw [hE, ← Real.rpow_add hNp]; ring_nf
  calc ((n : ℝ) + 1) ^ p * (2 * B) ^ (n + p)
      ≤ (4 * (p : ℝ) + 2) ^ (n + p) * (2 * B) ^ (n + p) :=
        mul_le_mul_of_nonneg_right hpow1 (by positivity)
    _ = ((4 * (p : ℝ) + 2) * (2 * B)) ^ (n + p) := (mul_pow _ _ _).symm
    _ ≤ ((N : ℝ) ^ (2 * δ + 4 * εA)) ^ (n + p) := by
        rw [← hNE]; exact pow_le_pow_left₀ (by positivity) hK _
    _ = (N : ℝ) ^ ((2 * δ + 4 * εA) * ((n : ℝ) + p)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
        push_cast
        ring_nf

/-- The remainder of order `4p + 1` (re-expansion with remainder, exponents of (Taylo_id1)):
`|f_l(t) − ∑_{k ≤ 4p−l} C(l+k, l) t^k f_{l+k}(0)| ≤ N^{l/2−2} Ψ^p` for `|t| ≤ N^{ε_A − 1/2}` and
`|f_{4p+1}| ≤ N^{(2δ+4ε_A)(5p+1)}` on `[0, t]`. -/
private theorem tay_rem_det {τ δ εA : ℝ} {p : ℕ} (hp2 : 2 ≤ p) (hτ : 0 < τ) (hδ1 : δ ≤ 1 / 100)
    (hεA : 0 < εA) (hεAδ : εA ≤ δ / 4) {N : ℕ} (hN : 1 ≤ N)
    (hN10 : ((4 * p + 1).factorial : ℝ) ≤ τ ^ p * (N : ℝ) ^ (1 / 10 : ℝ))
    {σ : Fin M → ℝ} {z : ℂ} (hz : z ∈ specDomain τ N) {a : ℝ → ℕ → ℂ}
    (ha : ∀ k x, HasDerivAt (fun y => a y k) (((k : ℂ) + 1) * a x (k + 1)) x)
    (t : ℝ) (ht : |t| ≤ (N : ℝ) ^ (εA - 1 / 2))
    (hB : ∀ s : ℝ, |s| ≤ |t| → ‖fCoeff p (a s) (4 * p + 1)‖ ≤
      (N : ℝ) ^ ((2 * δ + 4 * εA) * (((4 * p + 1 : ℕ) : ℝ) + p)))
    (l : ℕ) (hl : l ≤ 4 * p) :
    ‖fCoeff p (a t) l - ∑ k ∈ Finset.range (4 * p - l + 1),
        ((l + k).choose l : ℂ) * (t : ℂ) ^ k * fCoeff p (a 0) (l + k)‖ ≤
      (N : ℝ) ^ ((l : ℝ) / 2 - 2) * Psi N σ z ^ p := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  set eB : ℝ := (2 * δ + 4 * εA) * (((4 * p + 1 : ℕ) : ℝ) + p) with heB
  have hidx : l + (4 * p - l) + 1 = 4 * p + 1 := by omega
  have hT := fCoeff_taylor p ha l (4 * p - l) 0 t ((N : ℝ) ^ eB) (fun s hs => by
    rw [zero_add, hidx]
    exact hB s (tay_abs_le_of_mem_uIcc hs))
  rw [zero_add, hidx] at hT
  refine hT.trans ?_
  have ht0 : 0 ≤ |t| := abs_nonneg t
  set et : ℝ := (εA - 1 / 2) * ((4 * p - l + 1 : ℕ) : ℝ) with het
  have htk : |t| ^ (4 * p - l + 1) ≤ (N : ℝ) ^ et := by
    rw [het, Real.rpow_mul hNp.le, Real.rpow_natCast]
    exact pow_le_pow_left₀ ht0 ht _
  have hΨ := tay_Psi_ge (σ := σ) hN hτ hz
  have hΨp : (τ / N) ^ p ≤ Psi N σ z ^ p := pow_le_pow_left₀ (by positivity) hΨ p
  have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hL : (l : ℝ) ≤ 4 * p := by exact_mod_cast hl
  have hL0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have hcast : ((4 * p - l + 1 : ℕ) : ℝ) = 4 * p - l + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hl]; push_cast; ring
  have hδ0 : 0 < δ := by linarith
  have hexp : 1 / 10 + eB + et ≤ (l : ℝ) / 2 - 2 - p := by
    rw [het, hcast, heB]
    push_cast
    have h1 : (2 * δ + 4 * εA) * (4 * p + 1 + p) ≤ 3 * δ * (5 * p + 1) := by nlinarith
    have h2 : εA * (4 * p - l + 1) ≤ δ / 4 * (4 * p + 1) := by nlinarith
    nlinarith
  have hfac0 : (0 : ℝ) ≤ ((4 * p + 1).factorial : ℝ) := Nat.cast_nonneg _
  calc ((4 * p + 1).factorial : ℝ) * (N : ℝ) ^ eB * |t| ^ (4 * p - l + 1)
      ≤ τ ^ p * (N : ℝ) ^ (1 / 10 : ℝ) * (N : ℝ) ^ eB * (N : ℝ) ^ et := by
        gcongr
    _ = τ ^ p * (N : ℝ) ^ (1 / 10 + eB + et) := by
        rw [Real.rpow_add hNp, Real.rpow_add hNp]; ring
    _ ≤ τ ^ p * (N : ℝ) ^ ((l : ℝ) / 2 - 2 - p) := by
        gcongr
    _ = (N : ℝ) ^ ((l : ℝ) / 2 - 2) * (τ / N) ^ p := by
        rw [show (l : ℝ) / 2 - 2 - p = ((l : ℝ) / 2 - 2) + (-(p : ℝ)) by ring,
          Real.rpow_add hNp, Real.rpow_neg hNp.le, Real.rpow_natCast, div_pow]
        field_simp
    _ ≤ (N : ℝ) ^ ((l : ℝ) / 2 - 2) * Psi N σ z ^ p := by gcongr

/-- Lemma 7.15 (`lem:taylor_exp`) at a general `C₀`. -/
theorem taylor_exp' (τ c : ℝ) (C : ℕ → ℝ) (p : ℕ) (C₀ δ εA DA : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hc : 0 < c) (hp : Even p) (hp2 : 2 ≤ p) (hδ : 0 < δ) (hC₀ : 25 ≤ C₀)
    (hC₀δ : C₀ * δ ≤ τ / 4) (hεA : 0 < εA) (hεAδ : εA ≤ δ / 4) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ)
      (P : ModelClass M N) (m : ℕ), CompSetting τ c M N Sig S → 1 ≤ m →
      PropA N C P Sig S C₀ δ (m - 1) εA DA →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ) (y : Ω → ℝ), EntryAssumption C X → P Ω X →
        HighProbAt N DA {ω | |y ω| ≤ (N : ℝ) ^ (εA - 1 / 2)} →
        ∀ z ∈ levelSet N δ S m, ∀ (i : Fin M) (μ : Fin N) (v : Fin M ⊕ Fin N → ℝ),
          testNorm v = 1 →
          (∀ n ≤ 4 * p + 1, HighProbAt N (DA - 3) {ω | ∀ s : ℝ, |s| ≤ |y ω| →
            ‖fCoeff p (resCoeff Sig (Xupd (X ω) i μ s) z v i μ) n‖ ≤
              (N : ℝ) ^ ((2 * δ + 4 * εA) * ((n : ℝ) + p))}) ∧
          HighProbAt N (DA - 3) {ω |
            ‖(Fv Sig (Xupd (X ω) i μ (y ω)) z v : ℂ) ^ p -
              ∑ n ∈ Finset.range (4 * p + 1),
                (y ω : ℂ) ^ n * fCoeff p (resCoeff Sig (Xupd (X ω) i μ 0) z v i μ) n‖ ≤
              (N : ℝ) ^ (-2 : ℝ) * Psi N (specOf Sig) z ^ p} := by
  obtain ⟨N₁, h₁⟩ := tay_event τ c C p C₀ δ εA DA hτ hτ1 hc hδ hC₀ hC₀δ hεA hεAδ
  have hδ1 : δ ≤ 1 / 100 := by nlinarith
  set K₁ : ℝ := ((4 * p + 1).factorial : ℝ) / τ ^ p with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  refine ⟨max (max N₁ 1) ⌈K₁ ^ (1 / 10 : ℝ)⁻¹⌉₊, ?_⟩
  intro N hN M Sig S P m hset hm hA Ω _ _ X y hX hP hy z hz i μ v hv
  have hNN₁ : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN1 : 1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN10 : ((4 * p + 1).factorial : ℝ) ≤ τ ^ p * (N : ℝ) ^ (1 / 10 : ℝ) := by
    have h := tay_le_rpow hK₁0 (by norm_num : (0 : ℝ) < 1 / 10) (le_trans (le_max_right _ _) hN)
    rw [hK₁, div_le_iff₀ (by positivity)] at h
    linarith
  have hev := h₁ N hNN₁ M Sig S P m hset hm hA Ω X y hX hP hy z hz i μ v hv
  refine ⟨fun n hn => tay_hp_mono ?_ hev, tay_hp_mono ?_ hev⟩
  · intro ω hω
    exact fun s hs => hω.2 s hs n hn
  intro ω hω
  rw [Set.mem_ofPred_eq] at hω ⊢
  have hSig := hset.sigma.posDef
  have hzD := hset.domain.1 hz.1
  have h := tay_rem_det (σ := specOf Sig) hp2 hτ hδ1 hεA hεAδ hN1 hN10 hzD
    (fun k x => hasDerivAt_resCoeff hSig (X ω) hzD.1 v i μ k x) (y ω) hω.1
    (fun s hs => hω.2 s hs (4 * p + 1) le_rfl) 0 (by omega)
  simp only [Nat.sub_zero, zero_add, Nat.choose_zero_right, Nat.cast_one, one_mul,
    CharP.cast_eq_zero, zero_div, zero_sub] at h
  rw [tay_Fv_pow_eq hp Sig _ z v i μ]
  exact h

/-! ## Instances

The parameters are `τ = 1/2`, `c = 1`, `C = 2`, `p = 2`, `δ = 1/200` (`δ = τ/100`, `25δ = τ/4`),
`ε_A = 1/800 = δ/4`, `D_A = 900 = dPrev 2`. The setting, (A_{m−1}), the class, the entry
conditions and the bound on `y` are hypotheses of the statement (conditional in them). -/

/-- Lemma 7.15 at a general `C₀`, instance `C₀ = 25` (`C₀ δ = τ/4`), other parameters as
above. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ)
      (P : ModelClass M N) (m : ℕ), CompSetting (1 / 2) 1 M N Sig S → 1 ≤ m →
      PropA N (fun _ => 2) P Sig S 25 (1 / 200) (m - 1) (1 / 800) 900 →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ) (y : Ω → ℝ), EntryAssumption (fun _ => 2) X →
        P Ω X → HighProbAt N 900 {ω | |y ω| ≤ (N : ℝ) ^ ((1 / 800 : ℝ) - 1 / 2)} →
        ∀ z ∈ levelSet N (1 / 200) S m, ∀ (i : Fin M) (μ : Fin N) (v : Fin M ⊕ Fin N → ℝ),
          testNorm v = 1 →
          (∀ n ≤ 4 * 2 + 1, HighProbAt N (900 - 3) {ω | ∀ s : ℝ, |s| ≤ |y ω| →
            ‖fCoeff 2 (resCoeff Sig (Xupd (X ω) i μ s) z v i μ) n‖ ≤
              (N : ℝ) ^ ((2 * (1 / 200 : ℝ) + 4 * (1 / 800)) * ((n : ℝ) + ((2 : ℕ) : ℝ)))}) ∧
          HighProbAt N (900 - 3) {ω |
            ‖(Fv Sig (Xupd (X ω) i μ (y ω)) z v : ℂ) ^ 2 -
              ∑ n ∈ Finset.range (4 * 2 + 1),
                (y ω : ℂ) ^ n * fCoeff 2 (resCoeff Sig (Xupd (X ω) i μ 0) z v i μ) n‖ ≤
              (N : ℝ) ^ (-2 : ℝ) * Psi N (specOf Sig) z ^ 2} :=
  taylor_exp' (1 / 2) 1 (fun _ => 2) 2 25 (1 / 200) (1 / 800) 900 (by norm_num) (by norm_num)
    (by norm_num) even_two le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

end Anisotropic

#print axioms Anisotropic.taylor_exp'
