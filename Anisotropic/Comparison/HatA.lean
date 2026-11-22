module

public import Anisotropic.Comparison.CountII
public import Anisotropic.Comparison.SelfConsistent

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # Lemma 8.5, Lemma 8.4 and Lemma 8.3 (`n = 3`) -/

/-!
Lemma 8.5: on the event `Θ` of Lemma 7.13 (a_priori_1) and (bound_sum_im) the entries of `G` are
at most `B = N^{5δ/2} Q₀`; `|∏_r c_r(A(w_r)) − ∏_r c_r(Â(w_r))| ≤ p v̄(μ)² ∏_r m(w_r)` with
`m(w) = F_v + F_{e_μ}` for the empty words, the nonempty words contribute `(2B)⁴ R_i^{q−1}`
((w_est), (w_est_1)), and `∑_i R_i^{q−1} ≤ (τ⁻¹ + 1) N (N^{C₀δ}Ψ)^{q−1}` by (bound_sum_im).
Young's inequality and `∑_μ v̄(μ)² ≤ 1` bound the sum by
`(N^{C₀δ}Ψ)^p + F_v^p + ∑_μ v̄(μ)² F_{e_μ}^p`; off `Θ`, Lemma 7.7 with (A_rough).
Lemma 8.4: `∏_r c_r(A(w_r)) = (∏_r c_r(A(w_r)) − ∏_r c_r(Â(w_r))) + ∏_r c_r(Â(w_r))`, and
(wh_A_identity) writes the last product as a sum over the `3^{p+3}` tag tuples, each bounded by
Lemma 8.8. Lemma 8.3: `a_k = (−1)^k ∑_{w ∈ 𝒲_k} A(w)` writes `f_3` as a sum over the
`8 |T(p, 3)|` word tuples, each bounded by Lemma 8.4.
-/

/-! ## Bilinear forms of `G`, `Σ̲` and `Π` -/

private theorem hA_ent_sub {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (v w : ι → ℝ) :
    ent (A - B) v w = ent A v w - ent B v w := by
  simp [ent, sub_mulVec, dotProduct_sub]

private theorem hA_ent_eq {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (x y : ι → ℝ) :
    ent A x y = ∑ s, ∑ t, (x s : ℂ) * A s t * (y t : ℂ) := by
  simp only [ent, cvec, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

private theorem hA_ent_transpose {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (x y : ι → ℝ) :
    ent Aᵀ x y = ent A y x := by
  rw [hA_ent_eq, hA_ent_eq, Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
    simp only [transpose_apply]; ring

private theorem hA_ent_eI_right {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (x : ι → ℝ) (r : ι) : ent A x (eI r) = ∑ s, (x s : ℂ) * A s r := by
  rw [hA_ent_eq]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [eI, Pi.single_apply, apply_ite]

private theorem hA_diag {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) :
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

private theorem hA_sum_sq_UT {K : ℕ} {U : Matrix (Fin K) (Fin K) ℝ} (h₂ : U * Uᵀ = 1)
    (x : Fin K → ℝ) : ∑ i, (Uᵀ *ᵥ x) i ^ 2 = ∑ i, x i ^ 2 := by
  have e : (Uᵀ *ᵥ x) ⬝ᵥ (Uᵀ *ᵥ x) = x ⬝ᵥ x := by
    rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, h₂, one_mulVec, dotProduct_comm]
  simpa [dotProduct, sq] using e

private theorem hA_row_sq {K : ℕ} {U : Matrix (Fin K) (Fin K) ℝ} (h₂ : U * Uᵀ = 1) (i : Fin K) :
    ∑ k, U i k ^ 2 = 1 := by
  have := congrFun (congrFun h₂ i) i
  simpa [Matrix.mul_apply, sq, Matrix.one_apply] using this

/-- `|Σ x|² ≤ τ⁻² |x|²` under (bound_Sigma). -/
private theorem hA_sumsq_Sig {τ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hS : SigmaAssumption τ Sig) (x : Fin M → ℝ) :
    ∑ l, (Sig *ᵥ x) l ^ 2 ≤ τ⁻¹ ^ 2 * ∑ l, x l ^ 2 := by
  obtain ⟨U, h₂, h₁, hSd, hσ⟩ := hA_diag hS.posDef
  have hle : ∀ k, specOf Sig k ≤ τ⁻¹ := fun k => by
    rw [specOf_eq hS.posDef.isHermitian]; exact hS.eigenvalues_le k
  have hUU : Uᵀ * Uᵀᵀ = 1 := by rw [transpose_transpose]; exact h₁
  have e : Sig *ᵥ x = Uᵀᵀ *ᵥ (diagonal (specOf Sig) *ᵥ (Uᵀ *ᵥ x)) := by
    rw [transpose_transpose, mulVec_mulVec, mulVec_mulVec]
    exact congrArg (· *ᵥ x) hSd
  rw [e, hA_sum_sq_UT hUU, ← hA_sum_sq_UT h₂ x, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [mulVec_diagonal, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hσ k).le (hle k) 2) (sq_nonneg _)

/-- `|Σ̲ y| ≤ τ⁻¹ |y|`. -/
private theorem hA_testNorm_SigU {τ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hS : SigmaAssumption τ Sig) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (y : Fin M ⊕ Fin N → ℝ) :
    testNorm (SigU (n := Fin N) Sig *ᵥ y) ≤ τ⁻¹ * testNorm y := by
  have hτi : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  have h1 := hA_sumsq_Sig hS (y ∘ Sum.inl)
  have h2 : 0 ≤ ∑ ν, y (Sum.inr ν) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
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
private theorem hA_vbar_SigU {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (y : Fin M ⊕ Fin N → ℝ) : vbar Sig (SigU (n := Fin N) Sig *ᵥ y) = y := by
  have hS : Sig⁻¹ * Sig = 1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hSig.isUnit)
  funext s
  rcases s with j | ν
  · simp [vbar, SigU, fromBlocks_mulVec, mulVec_mulVec, hS]
  · simp [vbar, SigU, fromBlocks_mulVec]

/-- `(1 + wΣ)⁻¹_{li} = ∑ₖ U_{lk} (1 + σₖ w)⁻¹ U_{ik}`. -/
private theorem hA_cinv_entry {Sig U : Matrix (Fin M) (Fin M) ℝ} {σ : Fin M → ℝ}
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

private theorem hA_abs_le_testNorm {ι : Type*} [Fintype ι] (x : ι → ℝ) (s : ι) :
    |x s| ≤ testNorm x := by
  unfold testNorm
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (fun t _ => sq_nonneg (x t)) (Finset.mem_univ s))

private theorem hA_sqrt_inl_le (x : Fin M ⊕ Fin N → ℝ) :
    √(∑ j, x (Sum.inl j) ^ 2) ≤ testNorm x := by
  unfold testNorm
  refine Real.sqrt_le_sqrt ?_
  rw [Fintype.sum_sum_type]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- `|⟨v̄, Π e_p⟩| ≤ max(c⁻¹, K) |v|` when `|m| ≤ K` and `|1 + σᵢ m| ≥ c`. -/
private theorem hA_pi_bound {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {c K : ℝ}
    (hc : 0 < c) {w : ℂ} (hwK : ‖w‖ ≤ K) (hOne : ∀ i, c ≤ ‖1 + (specOf Sig i : ℂ) * w‖)
    (x : Fin M ⊕ Fin N → ℝ) (p : Fin M ⊕ Fin N) :
    ‖ent (piMat (N := N) Sig w) (vbar Sig x) (eI p)‖ ≤ max c⁻¹ K * testNorm x := by
  rw [hA_ent_eI_right, Fintype.sum_sum_type]
  rcases p with i | μ
  · simp only [piMat, fromBlocks_apply₁₁, fromBlocks_apply₂₁, Matrix.zero_apply, mul_zero,
      Finset.sum_const_zero, add_zero, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib, norm_neg]
    obtain ⟨U, h₂, h₁, hSd, hσ⟩ := hA_diag hSig
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
      simp only [hA_cinv_entry h₂ h₁ hSd hw0, Finset.mul_sum]
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
    rw [hA_sum_sq_UT h₂, hA_row_sq h₂, Real.sqrt_one, mul_one] at hcs
    have hc0 : 0 ≤ c⁻¹ := (inv_pos.2 hc).le
    calc _ ≤ ∑ k, c⁻¹ * (|(Uᵀ *ᵥ xM) k| * |U i k|) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => hb k)
      _ ≤ c⁻¹ * √(∑ j, xM j ^ 2) := by
          rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hcs hc0
      _ ≤ max c⁻¹ K * testNorm x :=
          mul_le_mul (le_max_left _ _) (hA_sqrt_inl_le x) (Real.sqrt_nonneg _)
            (hc0.trans (le_max_left _ _))
  · simp only [piMat, fromBlocks_apply₁₂, fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero,
      Finset.sum_const_zero, zero_add, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
      mul_one, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [vbar, Sum.elim_inr, Function.comp_apply]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul (hwK.trans (le_max_right _ _)) (hA_abs_le_testNorm x _) (abs_nonneg _)
      ((norm_nonneg w).trans (hwK.trans (le_max_right _ _)))

/-- `|⟨v̄, G e_p⟩| ≤ |⟨v, Σ̲⁻¹(G − Π)Σ̲⁻¹ (Σ̲ e_p)⟩| + max(c⁻¹, K) |v|`. -/
private theorem hA_G_left {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {c K : ℝ}
    (hc : 0 < c) {z : ℂ} (hwK : ‖mFun N (specOf Sig) z‖ ≤ K)
    (hOne : ∀ i, c ≤ ‖1 + (specOf Sig i : ℂ) * mFun N (specOf Sig) z‖)
    (A : Matrix (Fin M) (Fin N) ℝ) (x : Fin M ⊕ Fin N → ℝ) (p : Fin M ⊕ Fin N) :
    ‖ent (G Sig A z) (vbar Sig x) (eI p)‖ ≤
      ‖testBilin x (lawMat Sig A z) (SigU (n := Fin N) Sig *ᵥ eI p)‖ + max c⁻¹ K * testNorm x := by
  have e : ent (G Sig A z) (vbar Sig x) (eI p) =
      ent (G Sig A z - PiZ N Sig z) (vbar Sig x) (vbar Sig (SigU (n := Fin N) Sig *ᵥ eI p)) +
        ent (PiZ N Sig z) (vbar Sig x) (eI p) := by
    rw [hA_vbar_SigU hSig, hA_ent_sub]; ring
  rw [e, ent_vbar_eq_testBilin hSig]
  exact (norm_add_le _ _).trans (add_le_add le_rfl (hA_pi_bound hSig hc hwK hOne x p))

/-- The setting of §7 gives the density assumptions on the eigenvalues of `Σ`. -/
private theorem hA_density {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) : DensityAssumptions τ N (specOf Sig) :=
  (IsModel.diagModel_specOf (Ω := GaussSpace M N)
    ⟨hset.ratio_ge, hset.ratio_le, (gaussX_isGaussianEnsemble M N).entryAssumption hN,
      hset.sigma⟩).densityAssumptions hset.pos

private theorem hA_testNorm_eI {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι) :
    testNorm (eI p) = 1 := by
  unfold testNorm
  simp [eI, Pi.single_apply, Finset.sum_ite_eq']

/-- `1 ≤ M` and `1 ≤ N` in the setting of §7 (from `τ ≤ M/N`). -/
private theorem hA_N_pos {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) : 1 ≤ N := by
  by_contra h
  have h0 : N = 0 := by omega
  have := hset.ratio_ge
  rw [h0] at this
  simp at this
  linarith [hset.pos]

/-! ## Continuity in the matrix -/

private theorem hA_continuous_G {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {z : ℂ}
    (hz : 0 < z.im) : Continuous fun A : Matrix (Fin M) (Fin N) ℝ => G Sig A z := by
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

private theorem hA_continuous_ent {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    Continuous fun B : Matrix ι ι ℂ => ent B x y := by
  have : (fun B : Matrix ι ι ℂ => ent B x y) =
      fun B => ∑ s, ∑ t, (x s : ℂ) * B s t * (y t : ℂ) := funext fun B => hA_ent_eq B x y
  rw [this]
  exact continuous_finsetSum _ fun s _ => continuous_finsetSum _ fun t _ =>
    (continuous_const.mul (continuous_id.matrix_elem s t)).mul continuous_const

private theorem hA_continuous_wordA {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {z : ℂ}
    (hz : 0 < z.im) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) (k : ℕ) (w : Word k) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => wordA Sig A z v i μ k w := by
  have hG := hA_continuous_G (N := N) hSig hz
  cases k with
  | zero =>
    simp only [wordA]
    exact (hA_continuous_ent _ _).comp (hG.sub continuous_const)
  | succ k =>
    simp only [wordA]
    refine (((hA_continuous_ent _ _).comp hG).mul ?_).mul ((hA_continuous_ent _ _).comp hG)
    exact continuous_finsetProd _ fun l _ => hG.matrix_elem _ _

private theorem hA_continuous_Fv {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {z : ℂ}
    (hz : 0 < z.im) (v : Fin M ⊕ Fin N → ℝ) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => Fv Sig A z v := by
  unfold Fv
  exact ((hA_continuous_ent _ _).comp ((hA_continuous_G (N := N) hSig hz).sub
    continuous_const)).norm

/-! ## Rough moments -/

/-- `‖A‖_F² = ∑_{jν} A_{jν}²`. -/
private def hA_sq (A : Matrix (Fin M) (Fin N) ℝ) : ℝ := ∑ α : Fin M × Fin N, A α.1 α.2 ^ 2

private theorem hA_sq_nonneg (A : Matrix (Fin M) (Fin N) ℝ) : 0 ≤ hA_sq A :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem hA_continuous_sq : Continuous fun A : Matrix (Fin M) (Fin N) ℝ => hA_sq A := by
  unfold hA_sq
  exact continuous_finsetSum _ fun α _ => ((continuous_id.matrix_elem α.1 α.2).pow 2)

/-- The `L²` operator norm is at most the Frobenius norm. -/
private theorem hA_opNorm_le {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
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

/-- `‖XᵀX‖ ≤ ‖X‖_F²`. -/
private theorem hA_XtX_le (A : Matrix (Fin M) (Fin N) ℝ) : ‖Aᵀ * A‖ ≤ hA_sq A := by
  have h1 : ‖Aᵀ * A‖ = ‖A‖ * ‖A‖ := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact l2_opNorm_conjTranspose_mul_self A
  have h2 := hA_opNorm_le A
  have h0 : 0 ≤ ∑ i, ∑ j, A i j ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [h1, hA_sq, Fintype.sum_prod_type]
  calc ‖A‖ * ‖A‖ ≤ Real.sqrt (∑ i, ∑ j, A i j ^ 2) * Real.sqrt (∑ i, ∑ j, A i j ^ 2) :=
        mul_le_mul h2 h2 (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := Real.mul_self_sqrt h0

/-- The moment constant `2^q (1 + τ^{−q} C'_{2q})`. -/
private def hA_KW (τ : ℝ) (C : ℕ → ℝ) (q : ℕ) : ℝ := 2 ^ q * (1 + τ⁻¹ ^ q * max (C (2 * q)) 0)

private theorem hA_KW_nonneg {τ : ℝ} (hτ : 0 < τ) (C : ℕ → ℝ) (q : ℕ) : 0 ≤ hA_KW τ C q := by
  unfold hA_KW
  have : 0 ≤ max (C (2 * q)) 0 := le_max_right _ _
  positivity

private theorem hA_measurable_X {Ω : Type*} [MeasureSpace Ω] {C : ℕ → ℝ}
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) : Measurable X :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun μ => hX.measurable i μ

/-- Moments of `W = 1 + ‖X‖_F²`: `E W^q ≤ 2^q (1 + τ^{−q} C'_{2q}) N^q`. -/
private theorem hA_moment_W {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {τ : ℝ} (hτ : 0 < τ) {C : ℕ → ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ}
    (hX : EntryAssumption C X) (hN : 1 ≤ N) (hM : (M : ℝ) ≤ τ⁻¹ * N) (q : ℕ) :
    Integrable (fun ω => (1 + hA_sq (X ω)) ^ q) ∧
      ∫ ω, (1 + hA_sq (X ω)) ^ q ≤ hA_KW τ C q * (N : ℝ) ^ q := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · refine ⟨by simp, ?_⟩
    simp only [pow_zero, integral_const, probReal_univ, smul_eq_mul, mul_one]
    unfold hA_KW
    have : 0 ≤ max (C (2 * 0)) 0 := le_max_right _ _
    simp only [pow_zero, one_mul]
    linarith
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
  set g : Ω → ℝ := fun ω => 2 ^ n * (1 + cd ^ n * ∑ α : Fin M × Fin N,
      (X ω α.1 α.2 ^ 2) ^ (n + 1)) with hg
  have hgi : Integrable g := ((integrable_const _).add (hSi.const_mul _)).const_mul _
  have hle : ∀ ω, (1 + hA_sq (X ω)) ^ (n + 1) ≤ g ω := by
    intro ω
    have h1 := add_pow_le zero_le_one (hA_sq_nonneg (X ω)) (n + 1)
    have h2 : hA_sq (X ω) ^ (n + 1) ≤ cd ^ n * ∑ α : Fin M × Fin N, (X ω α.1 α.2 ^ 2) ^ (n + 1) :=
      pow_sum_le_card_mul_sum_pow (fun _ _ => sq_nonneg _) n
    simp only [Nat.add_sub_cancel, one_pow] at h1
    calc _ ≤ _ := h1
      _ ≤ g ω := by
          simp only [hg]
          gcongr
  have hmeas : Measurable fun ω => (1 + hA_sq (X ω)) ^ (n + 1) :=
    ((measurable_const.add (hA_continuous_sq.measurable.comp (hA_measurable_X hX))).pow_const _)
  have hWi : Integrable fun ω => (1 + hA_sq (X ω)) ^ (n + 1) :=
    hgi.mono' hmeas.aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (by have := hA_sq_nonneg (X ω); positivity)]; exact hle ω)
  refine ⟨hWi, ?_⟩
  have hgval : ∫ ω, g ω = 2 ^ n * (1 + cd ^ n * ∑ α : Fin M × Fin N,
      ∫ ω, (X ω α.1 α.2 ^ 2) ^ (n + 1)) := by
    rw [hg, integral_const_mul, integral_add (integrable_const _) (hSi.const_mul _),
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
  have hM3 : (M : ℝ) ^ (n + 1) * C' ≤ τ⁻¹ ^ (n + 1) * C' * (N : ℝ) ^ (n + 1) := by
    nlinarith [mul_le_mul_of_nonneg_right hM2 hC'0]
  calc ∫ ω, (1 + hA_sq (X ω)) ^ (n + 1) ≤ ∫ ω, g ω := integral_mono hWi hgi hle
    _ ≤ 2 ^ n * (1 + τ⁻¹ ^ (n + 1) * C' * (N : ℝ) ^ (n + 1)) := by
        rw [hgval]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have := mul_le_mul_of_nonneg_left hsum (pow_nonneg hcd0 n)
        rw [hM1] at this
        linarith
    _ ≤ hA_KW τ C (n + 1) * (N : ℝ) ^ (n + 1) := by
        unfold hA_KW
        rw [← hC']
        have h2 : (2 : ℝ) ^ n ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        have h3 : 0 ≤ τ⁻¹ ^ (n + 1) * C' := by positivity
        have h4 : (1 : ℝ) + τ⁻¹ ^ (n + 1) * C' * (N : ℝ) ^ (n + 1) ≤
            (1 + τ⁻¹ ^ (n + 1) * C') * (N : ℝ) ^ (n + 1) := by nlinarith
        calc 2 ^ n * (1 + τ⁻¹ ^ (n + 1) * C' * (N : ℝ) ^ (n + 1))
            ≤ 2 ^ (n + 1) * ((1 + τ⁻¹ ^ (n + 1) * C') * (N : ℝ) ^ (n + 1)) :=
              mul_le_mul h2 h4 (by positivity) (by positivity)
          _ = _ := by ring

/-- `1 ≤ N η` on `𝐃(τ, N)`. -/
private theorem hA_one_le_N_im {τ : ℝ} {z : ℂ} (hN : 1 ≤ N) (hτ : 0 < τ)
    (hz : z ∈ specDomain τ N) : 1 ≤ (N : ℝ) * z.im := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have h1 : (N : ℝ) * (N : ℝ) ^ (-1 + τ) = (N : ℝ) ^ τ := by
    rw [mul_comm, ← Real.rpow_add_one hNp.ne']; ring_nf
  have h2 : 1 ≤ (N : ℝ) ^ τ := Real.one_le_rpow hN1r hτ.le
  calc (1 : ℝ) ≤ (N : ℝ) ^ τ := h2
    _ = (N : ℝ) * (N : ℝ) ^ (-1 + τ) := h1.symm
    _ ≤ (N : ℝ) * z.im := mul_le_mul_of_nonneg_left hz.2.2.2.1 hNp.le

private theorem hA_roughConst_ge {τ c : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hc : 0 < c) :
    1 ≤ roughConst τ c := by
  unfold roughConst
  have hT : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  have hK : 0 ≤ mBoundConst τ * max c⁻¹ 1 := by
    have : 0 < mBoundConst τ := by unfold mBoundConst genPropConst; positivity
    positivity
  have h3 : 1 ≤ τ⁻¹ ^ 3 := one_le_pow₀ hT
  nlinarith

/-- (A_rough) with `η ≥ N⁻¹` and `‖XᵀX‖ ≤ ‖X‖_F²`. -/
private theorem hA_wordA_rough {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) {z : ℂ} (hz : z ∈ S) (A : Matrix (Fin M) (Fin N) ℝ)
    (v : Fin M ⊕ Fin N → ℝ) (hv : testNorm v = 1) (i : Fin M) (μ : Fin N) (k : ℕ)
    (w : Word k) :
    ‖wordA Sig A z v i μ k w‖ ≤ (roughConst τ c * N * (1 + hA_sq A)) ^ (k + 1) := by
  refine (norm_wordA_rough hset hz A v hv i μ k w).trans (pow_le_pow_left₀ ?_ ?_ _)
  · have h1 : 0 ≤ roughConst τ c :=
      zero_le_one.trans (hA_roughConst_ge hset.pos hset.le_one hset.c_pos)
    have h2 : 0 < z.im := (hset.domain.1 hz).1
    positivity
  · have hzD := hset.domain.1 hz
    have hη : 0 < z.im := hzD.1
    have hNη := hA_one_le_N_im (hA_N_pos hset) hset.pos hzD
    have hR := zero_le_one.trans (hA_roughConst_ge hset.pos hset.le_one hset.c_pos)
    have h1 : (1 + ‖Aᵀ * A‖) / z.im ≤ N * (1 + hA_sq A) := by
      rw [div_le_iff₀ hη]
      have := hA_XtX_le A
      have h0 : 0 ≤ 1 + ‖Aᵀ * A‖ := by positivity
      nlinarith
    rw [mul_div_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left h1 hR

/-! ## The event `Θ` -/

/-- The constant `Q₀ = τ⁻² + κ τ⁻¹ + κ + 1`, `κ = max(c⁻¹, K_m)`, of the entry bounds. -/
private def hA_Q0 (τ c : ℝ) : ℝ :=
  τ⁻¹ ^ 2 + max c⁻¹ (mBoundConst τ) * τ⁻¹ + max c⁻¹ (mBoundConst τ) + 1

private theorem hA_Q0_ge {τ c : ℝ} (hτ : 0 < τ) (hc : 0 < c) : 1 ≤ hA_Q0 τ c := by
  unfold hA_Q0
  have hκ : 0 ≤ max c⁻¹ (mBoundConst τ) := (inv_pos.2 hc).le.trans (le_max_left _ _)
  have : 0 ≤ max c⁻¹ (mBoundConst τ) * τ⁻¹ := mul_nonneg hκ (inv_pos.2 hτ).le
  nlinarith [sq_nonneg τ⁻¹]

private theorem hA_hp_mono {Ω : Type*} [MeasureSpace Ω] {N : ℕ} {D : ℝ} {A B : Set Ω}
    (h : A ⊆ B) (hA : HighProbAt N D A) : HighProbAt N D B :=
  (measure_mono (Set.compl_subset_compl.2 h)).trans hA

private theorem hA_hp_of_dom {Ω : Type*} [MeasureSpace Ω] {N : ℕ} {ε D : ℝ} {ξ ζ : Ω → ℝ}
    (h : DomAt N ε D ξ ζ) : HighProbAt N D {ω | ξ ω ≤ (N : ℝ) ^ ε * ζ ω} := by
  unfold HighProbAt
  refine le_trans (measure_mono fun ω hω => ?_) h
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω
  exact hω

/-- The event `Θ`: Lemma 7.13 (a_priori_1) at the test vectors `v`, `Σ̲ e_a` and
(bound_sum_im), at level `2 ε_A`, give `F_v, |G_{v̄a}|, |G_{av̄}|, |G_{ab}| ≤ N^{2δ+2ε_A} Q₀` and
`N⁻¹ ∑_i R_i² + N⁻¹ ∑_μ R_μ² ≤ N^{2ε_A} N^{(C₀+2)δ} Ψ²` with probability `≥ 1 − N^{−(D_A−4)}`. -/
private theorem hA_event (τ c : ℝ) (C : ℕ → ℝ) (C₀ δ εA DA : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hc : 0 < c) (hδ : 0 < δ) (hC₀ : 25 ≤ C₀) (hC₀δ : C₀ * δ ≤ τ / 4) (hεA : 0 < εA) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ)
      (P : ModelClass M N) (m : ℕ), CompSetting τ c M N Sig S → 1 ≤ m →
      PropA N C P Sig S C₀ δ (m - 1) εA DA →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption C X → P Ω X →
        ∀ z ∈ levelSet N δ S m, ∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 →
          HighProbAt N (DA - 4) {ω |
            Fv Sig (X ω) z v ≤ (N : ℝ) ^ (2 * εA) * (N : ℝ) ^ (2 * δ) * hA_Q0 τ c ∧
            (∀ a, ‖ent (G Sig (X ω) z) (vbar Sig v) (eI a)‖ ≤
              (N : ℝ) ^ (2 * εA) * (N : ℝ) ^ (2 * δ) * hA_Q0 τ c) ∧
            (∀ a, ‖ent (G Sig (X ω) z) (eI a) (vbar Sig v)‖ ≤
              (N : ℝ) ^ (2 * εA) * (N : ℝ) ^ (2 * δ) * hA_Q0 τ c) ∧
            (∀ a b, ‖G Sig (X ω) z a b‖ ≤ (N : ℝ) ^ (2 * εA) * (N : ℝ) ^ (2 * δ) * hA_Q0 τ c) ∧
            (N : ℝ)⁻¹ *
              (∑ i, (‖ent (G Sig (X ω) z) (vbar Sig v) (eI (Sum.inl i))‖ +
                  ‖ent (G Sig (X ω) z) (eI (Sum.inl i)) (vbar Sig v)‖) ^ 2 +
                ∑ μ, (‖ent (G Sig (X ω) z) (vbar Sig v) (eI (Sum.inr μ))‖ +
                  ‖ent (G Sig (X ω) z) (eI (Sum.inr μ)) (vbar Sig v)‖) ^ 2) ≤
              (N : ℝ) ^ (2 * εA) * ((N : ℝ) ^ ((C₀ + 2) * δ) * Psi N (specOf Sig) z ^ 2)} := by
  obtain ⟨N₁, h₁⟩ := cor_rough_bound' τ c C C₀ δ εA DA hτ hτ1 hc hδ hC₀ hC₀δ hεA
  obtain ⟨N₂, h₂⟩ := bound_sum_im' τ c C C₀ δ εA DA hτ hτ1 hc hδ hC₀ hC₀δ hεA
  set κ := max c⁻¹ (mBoundConst τ) with hκ
  have hκ0 : 0 ≤ κ := (inv_pos.2 hc).le.trans (le_max_left _ _)
  have hT0 : 0 ≤ τ⁻¹ := (inv_pos.2 hτ).le
  have hT1 : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  refine ⟨max (max N₁ N₂) (⌈(τ⁻¹ + 2) ^ 2 + 1⌉₊ + 1), ?_⟩
  intro N hN M Sig S P m hset hm hA Ω _ _ X hX hP z hz v hv
  have hNN₁ : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNN₂ : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNc : ⌈(τ⁻¹ + 2) ^ 2 + 1⌉₊ + 1 ≤ N := le_trans (le_max_right _ _) hN
  have hN1 : 1 ≤ N := by omega
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : (0 : ℝ) < N := by linarith
  have hNc' : (τ⁻¹ + 2) ^ 2 + 1 ≤ (N : ℝ) := by
    have := Nat.le_ceil ((τ⁻¹ + 2) ^ 2 + 1)
    have h2 : (⌈(τ⁻¹ + 2) ^ 2 + 1⌉₊ : ℝ) ≤ N := by exact_mod_cast (by omega : _ ≤ N)
    linarith
  have hM : (M : ℝ) ≤ τ⁻¹ * N := by
    have := hset.ratio_le
    rwa [div_le_iff₀ hNp] at this
  set L : Option (Fin M ⊕ Fin N) → Fin M ⊕ Fin N → ℝ :=
    fun o => o.elim v fun a => SigU (n := Fin N) Sig *ᵥ eI a with hL
  set E : ℝ := (N : ℝ) ^ (2 * εA) * (N : ℝ) ^ (2 * δ) with hE
  let Ev : (Option (Fin M ⊕ Fin N) × Option (Fin M ⊕ Fin N)) ⊕ Unit → Set Ω := Sum.elim
    (fun jk => {ω | ‖testBilin (L jk.1) (lawMat Sig (X ω) z) (L jk.2)‖ ≤
      (N : ℝ) ^ (2 * εA) * ((N : ℝ) ^ (2 * δ) * testNorm (L jk.1) * testNorm (L jk.2))})
    (fun _ => {ω | (N : ℝ)⁻¹ *
              (∑ i, (‖ent (G Sig (X ω) z) (vbar Sig v) (eI (Sum.inl i))‖ +
                  ‖ent (G Sig (X ω) z) (eI (Sum.inl i)) (vbar Sig v)‖) ^ 2 +
                ∑ μ, (‖ent (G Sig (X ω) z) (vbar Sig v) (eI (Sum.inr μ))‖ +
                  ‖ent (G Sig (X ω) z) (eI (Sum.inr μ)) (vbar Sig v)‖) ^ 2) ≤
              (N : ℝ) ^ (2 * εA) * ((N : ℝ) ^ ((C₀ + 2) * δ) * Psi N (specOf Sig) z ^ 2)})
  have hEv : ∀ ι ∈ (Finset.univ : Finset ((Option (Fin M ⊕ Fin N) × Option (Fin M ⊕ Fin N)) ⊕
      Unit)), HighProbAt N (DA - 4 + 3) (Ev ι) := by
    intro ι _
    rw [show DA - 4 + 3 = DA - 1 by ring]
    rcases ι with ⟨j, k⟩ | u
    · exact hA_hp_of_dom ((h₁ N hNN₁ M Sig S P m hset hm hA Ω X hX hP z hz).1 (L j) (L k))
    · exact hA_hp_of_dom (h₂ N hNN₂ M Sig S P m hset hm hA Ω X hX hP z hz v hv)
  have hcard : ((Finset.univ : Finset ((Option (Fin M ⊕ Fin N) × Option (Fin M ⊕ Fin N)) ⊕
      Unit)).card : ℝ) ≤ (N : ℝ) ^ (3 : ℝ) := by
    rw [Finset.card_univ]
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_option, Fintype.card_fin,
      Fintype.card_unit]
    push_cast
    have h3 : (N : ℝ) ^ (3 : ℝ) = (N : ℝ) ^ 2 * N := by
      rw [show (3 : ℝ) = ((2 + 1 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    rw [h3]
    have hMN : (M : ℝ) + N + 1 ≤ (τ⁻¹ + 2) * N := by nlinarith
    have h0 : (0 : ℝ) ≤ M + N + 1 := by positivity
    have h4 : ((M : ℝ) + N + 1) ^ 2 ≤ (τ⁻¹ + 2) ^ 2 * (N : ℝ) ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ h0 hMN 2
    have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := one_le_pow₀ hN1r
    nlinarith
  have hall := HighProbAt.biInter Finset.univ hN1 hcard hEv
  refine hA_hp_mono (fun ω hω => ?_) hall
  have hω' : ∀ ι, ω ∈ Ev ι := fun ι => Set.mem_iInter₂.1 hω ι (Finset.mem_univ _)
  have hSig := hset.sigma.posDef
  have hzS : z ∈ S := hz.1
  have hzD := hset.domain.1 hzS
  have hη : 0 < z.im := hzD.1
  have hmK := (gen_prop_m_specDomain (hA_density hset hN1) hzD).2.1
  have hOne := hset.oneXm z hzS
  have hE1 : 1 ≤ E := one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hN1r (by linarith))
    (Real.one_le_rpow hN1r (by linarith))
  have hE0 : 0 ≤ E := by linarith
  have hu : ∀ a, testNorm (SigU (n := Fin N) Sig *ᵥ eI a) ≤ τ⁻¹ := fun a => by
    have := hA_testNorm_SigU (N := N) hset.sigma hτ hτ1 (eI a)
    rwa [hA_testNorm_eI, mul_one] at this
  have hLn : ∀ o, testNorm (L o) ≤ τ⁻¹ := by
    intro o
    rcases o with _ | a
    · simp only [hL, Option.elim]; rw [hv]; exact hT1
    · exact hu a
  have hbil : ∀ j k, ‖testBilin (L j) (lawMat Sig (X ω) z) (L k)‖ ≤ E * τ⁻¹ * τ⁻¹ := by
    intro j k
    have hb : ‖testBilin (L j) (lawMat Sig (X ω) z) (L k)‖ ≤
        (N : ℝ) ^ (2 * εA) * ((N : ℝ) ^ (2 * δ) * testNorm (L j) * testNorm (L k)) :=
      hω' (Sum.inl (j, k))
    refine hb.trans ?_
    have h0j : 0 ≤ testNorm (L j) := Real.sqrt_nonneg _
    have h0k : 0 ≤ testNorm (L k) := Real.sqrt_nonneg _
    have e : (N : ℝ) ^ (2 * εA) * ((N : ℝ) ^ (2 * δ) * testNorm (L j) * testNorm (L k)) =
        E * testNorm (L j) * testNorm (L k) := by rw [hE]; ring
    rw [e]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hLn j) hE0) (hLn k) h0k (mul_nonneg hE0 hT0)
  set B : ℝ := E * hA_Q0 τ c with hB
  have key : ∀ (x : Fin M ⊕ Fin N → ℝ) (q : Fin M ⊕ Fin N), testNorm x ≤ τ⁻¹ →
      ‖testBilin x (lawMat Sig (X ω) z) (SigU (n := Fin N) Sig *ᵥ eI q)‖ ≤ E * τ⁻¹ * τ⁻¹ →
      ‖ent (G Sig (X ω) z) (vbar Sig x) (eI q)‖ ≤ B := by
    intro x q hx hxq
    refine (hA_G_left hSig hc hmK hOne (X ω) x q).trans ?_
    have h1 : κ * testNorm x ≤ κ * τ⁻¹ := mul_le_mul_of_nonneg_left hx hκ0
    have h2 : κ * τ⁻¹ ≤ E * (κ * τ⁻¹) := le_mul_of_one_le_left (mul_nonneg hκ0 hT0) hE1
    have h3 : 0 ≤ E * κ + E := by positivity
    rw [hB, hA_Q0, ← hκ]
    nlinarith
  have hv1 : testNorm v ≤ τ⁻¹ := by rw [hv]; exact hT1
  have hL0 : L none = v := rfl
  have hLs : ∀ a, L (some a) = SigU (n := Fin N) Sig *ᵥ eI a := fun a => rfl
  have hva : ∀ a, ‖ent (G Sig (X ω) z) (vbar Sig v) (eI a)‖ ≤ B := fun a =>
    key v a hv1 (by have := hbil none (some a); rwa [hL0, hLs] at this)
  refine ⟨?_, hva, fun a => ?_, fun a b => ?_, hω' (Sum.inr ())⟩
  · unfold Fv
    rw [ent_vbar_eq_testBilin hSig]
    have := hbil none none
    rw [hL0] at this
    calc _ ≤ E * τ⁻¹ * τ⁻¹ := this
      _ ≤ B := by
          rw [hB, hA_Q0, ← hκ]
          have : 0 ≤ E * (κ * τ⁻¹ + κ + 1) := by positivity
          nlinarith
  · rw [← hA_ent_transpose, G_transpose hSig (X ω) hη]
    exact hva a
  · rw [← ent_eI_eI (G Sig (X ω) z) a b, ← hA_vbar_SigU (N := N) hSig (eI a)]
    refine key _ b (hu a) ?_
    have := hbil (some a) (some b)
    rwa [hLs, hLs] at this

/-- `N^{−n/2} = (N^{−1/2})^n`. -/
private theorem hA_rpow_neg_half (hN : 1 ≤ N) (n : ℕ) :
    (N : ℝ) ^ (-(n : ℝ) / 2) = ((Real.sqrt N)⁻¹) ^ n := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hNp.le, ← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
  congr 1
  ring

/-- `Ψ` from below and above on `𝐃(τ, N)`: `N^{−1/2} ≤ √K_m Ψ`, `Ψ ≤ (√K_m + 1) N^{−τ/2}`,
`Ψ ≥ τ/N`. -/
private theorem hA_Psi_bounds {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) {z : ℂ} (hz : z ∈ S) :
    (Real.sqrt N)⁻¹ ≤ Real.sqrt (mBoundConst τ) * Psi N (specOf Sig) z ∧
      Psi N (specOf Sig) z ≤ (Real.sqrt (mBoundConst τ) + 1) * (N : ℝ) ^ (-(τ / 2)) ∧
      τ / N ≤ Psi N (specOf Sig) z := by
  have hN := hA_N_pos hset
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hτ := hset.pos
  have hzD := hset.domain.1 hz
  have hη : 0 < z.im := hzD.1
  have hηt : z.im ≤ τ⁻¹ := hzD.2.2.2.2
  obtain ⟨-, hmK, hmI⟩ := gen_prop_m_specDomain (hA_density hset hN) hzD
  set Km := mBoundConst τ with hKm
  have hKm0 : 0 < Km := by rw [hKm]; unfold mBoundConst genPropConst; positivity
  set m := mFun N (specOf Sig) z with hm
  have hNη : 0 < (N : ℝ) * z.im := by positivity
  have hNη1 := hA_one_le_N_im hN hτ hzD
  have hNτ : (N : ℝ) ^ τ ≤ (N : ℝ) * z.im := by
    have h1 : (N : ℝ) * (N : ℝ) ^ (-1 + τ) = (N : ℝ) ^ τ := by
      rw [mul_comm, ← Real.rpow_add_one hNp.ne']; ring_nf
    rw [← h1]
    exact mul_le_mul_of_nonneg_left hzD.2.2.2.1 hNp.le
  have hNτ0 : 0 < (N : ℝ) ^ τ := Real.rpow_pos_of_pos hNp _
  have hP0 : 0 ≤ Real.sqrt (m.im / (N * z.im)) := Real.sqrt_nonneg _
  refine ⟨?_, ?_, ?_⟩
  · unfold Psi
    have hq : Km⁻¹ * (N : ℝ)⁻¹ ≤ m.im / (N * z.im) := by
      rw [le_div_iff₀ hNη]
      calc Km⁻¹ * (N : ℝ)⁻¹ * (N * z.im) = Km⁻¹ * z.im := by field_simp
        _ ≤ m.im := hmI
    have hs := Real.sqrt_le_sqrt hq
    rw [Real.sqrt_mul (inv_nonneg.2 hKm0.le), Real.sqrt_inv, Real.sqrt_inv] at hs
    have hsK : 0 < Real.sqrt Km := Real.sqrt_pos.2 hKm0
    have h1 : (Real.sqrt N)⁻¹ ≤ Real.sqrt Km * Real.sqrt (m.im / (N * z.im)) := by
      have := mul_le_mul_of_nonneg_left hs hsK.le
      rwa [← mul_assoc, mul_inv_cancel₀ hsK.ne', one_mul] at this
    have h2 : 0 ≤ Real.sqrt Km * (1 / (N * z.im)) := by positivity
    linarith [mul_add (Real.sqrt Km) (Real.sqrt (m.im / (N * z.im))) (1 / (N * z.im))]
  · unfold Psi
    have hmI' : m.im ≤ Km := (Complex.im_le_norm m).trans hmK
    have hsqτ : Real.sqrt ((N : ℝ) ^ τ) = (N : ℝ) ^ (τ / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNp.le]; ring_nf
    have hneg : (N : ℝ) ^ (-(τ / 2)) = ((N : ℝ) ^ (τ / 2))⁻¹ := Real.rpow_neg hNp.le _
    have hh0 : 0 < (N : ℝ) ^ (τ / 2) := Real.rpow_pos_of_pos hNp _
    have hh1 : 1 ≤ (N : ℝ) ^ (τ / 2) := Real.one_le_rpow hN1r (by linarith)
    have hsq : Real.sqrt (m.im / (N * z.im)) ≤ Real.sqrt Km * ((N : ℝ) ^ (τ / 2))⁻¹ := by
      have : m.im / (N * z.im) ≤ Km / (N : ℝ) ^ τ := by
        calc m.im / (N * z.im) ≤ Km / (N * z.im) :=
              div_le_div_of_nonneg_right hmI' hNη.le
          _ ≤ Km / (N : ℝ) ^ τ := div_le_div_of_nonneg_left hKm0.le hNτ0 hNτ
      calc _ ≤ Real.sqrt (Km / (N : ℝ) ^ τ) := Real.sqrt_le_sqrt this
        _ = Real.sqrt Km * ((N : ℝ) ^ (τ / 2))⁻¹ := by
            rw [Real.sqrt_div' _ hNτ0.le, hsqτ, div_eq_mul_inv]
    have h1 : 1 / ((N : ℝ) * z.im) ≤ ((N : ℝ) ^ (τ / 2))⁻¹ := by
      rw [one_div]
      refine inv_anti₀ hh0 ?_
      have : (N : ℝ) ^ (τ / 2) ≤ (N : ℝ) ^ τ :=
        Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
      linarith
    rw [hneg]
    nlinarith
  · unfold Psi
    have h1 : τ / N ≤ 1 / (N * z.im) := by
      rw [div_le_div_iff₀ hNp hNη, one_mul]
      calc τ * (N * z.im) ≤ τ * (N * τ⁻¹) := by gcongr
        _ = N := by field_simp
    linarith
/-! ## Conjugation, `max_{𝒱_v} E F^p`, `v̄(μ)` and `F_{e_μ}` -/

private theorem hA_conjIf_mul (b : Bool) (x y : ℂ) :
    conjIf b (x * y) = conjIf b x * conjIf b y := by
  cases b <;> simp [conjIf]

private theorem hA_conjIf_sub (b : Bool) (x y : ℂ) :
    conjIf b (x - y) = conjIf b x - conjIf b y := by
  cases b <;> simp [conjIf]

private theorem hA_conjIf_sum {ι : Type*} (s : Finset ι) (b : Bool) (f : ι → ℂ) :
    conjIf b (∑ i ∈ s, f i) = ∑ i ∈ s, conjIf b (f i) := by
  cases b <;> simp [conjIf, map_sum]

private theorem hA_norm_conjIf (b : Bool) (x : ℂ) : ‖conjIf b x‖ = ‖x‖ := by
  cases b <;> simp [conjIf]

private theorem hA_continuous_conjIf (b : Bool) : Continuous (conjIf b) := by
  cases b
  · have h : conjIf false = id := funext fun x => by simp [conjIf]
    rw [h]; exact continuous_id
  · have h : conjIf true = starRingEnd ℂ := funext fun x => by simp [conjIf]
    rw [h]; exact Complex.continuous_conj

/-- `|∏ X − ∏ Y| ≤ (∑ θ) ∏ m` when `|X_i|, |Y_i| ≤ m_i` and `|X_i − Y_i| ≤ θ_i m_i`. -/
private theorem hA_prod_sub_le {ι : Type*} (s : Finset ι) (X Y : ι → ℂ) (m θ : ι → ℝ)
    (hm : ∀ i ∈ s, 0 ≤ m i) (hX : ∀ i ∈ s, ‖X i‖ ≤ m i) (hY : ∀ i ∈ s, ‖Y i‖ ≤ m i)
    (hXY : ∀ i ∈ s, ‖X i - Y i‖ ≤ θ i * m i) :
    ‖∏ i ∈ s, X i - ∏ i ∈ s, Y i‖ ≤ (∑ i ∈ s, θ i) * ∏ i ∈ s, m i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hm hX hY hXY
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    have hYs : ‖∏ i ∈ s, Y i‖ ≤ ∏ i ∈ s, m i :=
      (Finset.norm_prod_le s Y).trans (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) hY.2)
    have hms : 0 ≤ ∏ i ∈ s, m i := Finset.prod_nonneg hm.2
    have e : X a * ∏ i ∈ s, X i - Y a * ∏ i ∈ s, Y i =
        X a * (∏ i ∈ s, X i - ∏ i ∈ s, Y i) + (X a - Y a) * ∏ i ∈ s, Y i := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h1 := mul_le_mul hX.1 (ih hm.2 hX.2 hY.2 hXY.2) (norm_nonneg _) hm.1
    have h2 := mul_le_mul hXY.1 hYs (norm_nonneg _) (by
      have := norm_nonneg (X a - Y a); linarith [hXY.1])
    nlinarith

private theorem hA_maxFp_ge {Ω : Type*} [MeasureSpace Ω] (Sig : Matrix (Fin M) (Fin M) ℝ)
    (X : Ω → Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (v : Fin M ⊕ Fin N → ℝ) (p : ℕ)
    (w : Option (Fin N)) : ∫ ω, Fv Sig (X ω) z (vfam v w) ^ p ≤ maxFp Sig X z v p := by
  unfold maxFp
  exact le_ciSup (Finite.bddAbove_range (fun w => ∫ ω, Fv Sig (X ω) z (vfam v w) ^ p)) w

private theorem hA_maxFp_nonneg {Ω : Type*} [MeasureSpace Ω] (Sig : Matrix (Fin M) (Fin M) ℝ)
    (X : Ω → Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (v : Fin M ⊕ Fin N → ℝ) (p : ℕ) :
    0 ≤ maxFp Sig X z v p :=
  (integral_nonneg fun _ => pow_nonneg (norm_nonneg _) p).trans (hA_maxFp_ge Sig X z v p none)

/-- `v̄` of `e_μ` is `e_μ`. -/
private theorem hA_vbar_eI_inr (Sig : Matrix (Fin M) (Fin M) ℝ) (μ : Fin N) :
    vbar Sig (eI (Sum.inr μ) : Fin M ⊕ Fin N → ℝ) = eI (Sum.inr μ) := by
  funext s
  rcases s with j | ν
  · have h0 : ((eI (Sum.inr μ) : Fin M ⊕ Fin N → ℝ) ∘ Sum.inl) = 0 := by
      funext k; simp [eI]
    simp only [vbar, Sum.elim_inl, h0, mulVec_zero, Pi.zero_apply]
    simp [eI]
  · simp [vbar, eI]

/-- `F_{e_μ} = |G_μμ − Π_μμ|`. -/
private theorem hA_Fv_eI (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (μ : Fin N) : Fv Sig A z (eI (Sum.inr μ)) =
      ‖G Sig A z (Sum.inr μ) (Sum.inr μ) - PiZ N Sig z (Sum.inr μ) (Sum.inr μ)‖ := by
  rw [Fv, hA_vbar_eI_inr, ent_eI_eI, Matrix.sub_apply]

private theorem hA_vbar_inr (Sig : Matrix (Fin M) (Fin M) ℝ) (v : Fin M ⊕ Fin N → ℝ) (μ : Fin N) :
    vbar Sig v (Sum.inr μ) = v (Sum.inr μ) := by
  simp [vbar]

/-- `∑_μ v̄(μ)² ≤ |v|² = 1`. -/
private theorem hA_sum_vbar_sq {Sig : Matrix (Fin M) (Fin M) ℝ} {v : Fin M ⊕ Fin N → ℝ}
    (hv : testNorm v = 1) : ∑ μ : Fin N, vbar Sig v (Sum.inr μ) ^ 2 ≤ 1 := by
  have h2 : ∑ s, v s ^ 2 = 1 := by
    unfold testNorm at hv
    rwa [Real.sqrt_eq_one] at hv
  simp only [hA_vbar_inr]
  rw [← h2, Fintype.sum_sum_type]
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => sq_nonneg _)

private theorem hA_vbar_sq_le {Sig : Matrix (Fin M) (Fin M) ℝ} {v : Fin M ⊕ Fin N → ℝ}
    (hv : testNorm v = 1) (μ : Fin N) : vbar Sig v (Sum.inr μ) ^ 2 ≤ 1 :=
  (Finset.single_le_sum (f := fun μ => vbar Sig v (Sum.inr μ) ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ μ)).trans (hA_sum_vbar_sq hv)

/-! ## The difference `∏_r c_r(A(w_r)) − ∏_r c_r(Â(w_r))` -/

/-- The majorant of `|A(w)|` and `|Â(w)|`: `F_v + F_{e_μ}` if `n(w) = 0`, `|A(w)|` otherwise. -/
private def hA_m (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) (n : ℕ) (w : Word n) : ℝ :=
  if n = 0 then Fv Sig A z v + Fv Sig A z (eI (Sum.inr μ)) else ‖wordA Sig A z v i μ n w‖

/-- `|A(w)|, |Â(w)| ≤ m(w)` and `|A(w) − Â(w)| ≤ v̄(μ)² m(w)`. -/
private theorem hA_word_facts (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) {v : Fin M ⊕ Fin N → ℝ} (hv : testNorm v = 1) (i : Fin M) (μ : Fin N) (n : ℕ)
    (w : Word n) :
    ‖wordA Sig A z v i μ n w‖ ≤ hA_m Sig A z v i μ n w ∧
      ‖hatA Sig A z v i μ n w‖ ≤ hA_m Sig A z v i μ n w ∧
      ‖wordA Sig A z v i μ n w - hatA Sig A z v i μ n w‖ ≤
        vbar Sig v (Sum.inr μ) ^ 2 * hA_m Sig A z v i μ n w := by
  have hF0 : 0 ≤ Fv Sig A z v := norm_nonneg _
  have hFm0 : 0 ≤ Fv Sig A z (eI (Sum.inr μ)) := norm_nonneg _
  have hv2 := hA_vbar_sq_le (Sig := Sig) hv μ
  have hv20 : 0 ≤ vbar Sig v (Sum.inr μ) ^ 2 := sq_nonneg _
  cases n with
  | zero =>
    have hw : ‖wordA Sig A z v i μ 0 w‖ = Fv Sig A z v := rfl
    have hd : ‖((vbar Sig v (Sum.inr μ) : ℝ) : ℂ) ^ 2 *
        (G Sig A z (Sum.inr μ) (Sum.inr μ) - PiZ N Sig z (Sum.inr μ) (Sum.inr μ))‖ =
        vbar Sig v (Sum.inr μ) ^ 2 * Fv Sig A z (eI (Sum.inr μ)) := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, hA_Fv_eI]
    simp only [hA_m, ↓reduceIte]
    refine ⟨by rw [hw]; linarith, ?_, ?_⟩
    · simp only [hatA]
      refine (norm_sub_le _ _).trans ?_
      rw [hw, hd]
      nlinarith
    · simp only [hatA, sub_sub_cancel]
      rw [hd]
      nlinarith
  | succ k =>
    simp only [hA_m, Nat.succ_ne_zero, ↓reduceIte, hatA, sub_self, norm_zero]
    exact ⟨le_rfl, le_rfl, by positivity⟩

/-- `|∏_r c_r(A(w_r)) − ∏_r c_r(Â(w_r))| ≤ p v̄(μ)² ∏_r m(w_r)`. -/
private theorem hA_D_le (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    {v : Fin M ⊕ Fin N → ℝ} (hv : testNorm v = 1) (i : Fin M) (μ : Fin N) {p : ℕ}
    (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r)) (cs : Fin p → Bool) :
    ‖(∏ r, conjIf (cs r) (wordA Sig A z v i μ (ns r) (ws r))) -
        ∏ r, conjIf (cs r) (hatA Sig A z v i μ (ns r) (ws r))‖ ≤
      p * vbar Sig v (Sum.inr μ) ^ 2 * ∏ r, hA_m Sig A z v i μ (ns r) (ws r) := by
  have h := hA_prod_sub_le Finset.univ
    (fun r => conjIf (cs r) (wordA Sig A z v i μ (ns r) (ws r)))
    (fun r => conjIf (cs r) (hatA Sig A z v i μ (ns r) (ws r)))
    (fun r => hA_m Sig A z v i μ (ns r) (ws r)) (fun _ => vbar Sig v (Sum.inr μ) ^ 2)
    (fun r _ => (norm_nonneg _).trans (hA_word_facts Sig A z hv i μ _ (ws r)).1)
    (fun r _ => by rw [hA_norm_conjIf]; exact (hA_word_facts Sig A z hv i μ _ (ws r)).1)
    (fun r _ => by rw [hA_norm_conjIf]; exact (hA_word_facts Sig A z hv i μ _ (ws r)).2.1)
    (fun r _ => by
      rw [← hA_conjIf_sub, hA_norm_conjIf]; exact (hA_word_facts Sig A z hv i μ _ (ws r)).2.2)
  simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h

/-- `∏_r m(w_r) = ∏_{n_r ≥ 1} |A(w_r)| (F_v + F_{e_μ})^{p−q}`. -/
private theorem hA_prod_m (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) {p : ℕ} (ns : Fin p → ℕ)
    (ws : ∀ r, Word (ns r)) :
    ∏ r, hA_m Sig A z v i μ (ns r) (ws r) =
      (∏ r ∈ Finset.univ.filter (fun r => 1 ≤ ns r), ‖wordA Sig A z v i μ (ns r) (ws r)‖) *
        (Fv Sig A z v + Fv Sig A z (eI (Sum.inr μ))) ^
          (p - (Finset.univ.filter (fun r => 1 ≤ ns r)).card) := by
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun r => 1 ≤ ns r)]
  congr 1
  · refine Finset.prod_congr rfl fun r hr => ?_
    have : ns r ≠ 0 := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr; omega
    simp [hA_m, this]
  · have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin p)))
      (fun r => 1 ≤ ns r)
    rw [Finset.card_univ, Fintype.card_fin] at hc
    rw [Finset.prod_congr rfl fun r hr => (show hA_m Sig A z v i μ (ns r) (ws r) =
        Fv Sig A z v + Fv Sig A z (eI (Sum.inr μ)) by
      have : ns r = 0 := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hr; omega
      simp [hA_m, this]), Finset.prod_const]
    congr 1
    omega

/-- `R_i = |G_{v̄ i}| + |G_{i v̄}|`. -/
private def hA_Ri (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) : ℝ :=
  ‖ent (G Sig A z) (vbar Sig v) (eI (Sum.inl i))‖ + ‖ent (G Sig A z) (eI (Sum.inl i)) (vbar Sig v)‖

/-- The nonempty words with `∑_r n(w_r) = 3`: `∏_{n_r ≥ 1} |A(w_r)| ≤ (2B)⁴ R_i^{q−1}` when the
entries are at most `B`; each word with `n(w_r) = 1` carries one factor `R_i` (w_est_1), and there
are at least `q − 1` of them. -/
private theorem hA_P_le {Sig : Matrix (Fin M) (Fin M) ℝ} {A : Matrix (Fin M) (Fin N) ℝ} {z : ℂ}
    {v : Fin M ⊕ Fin N → ℝ} (i : Fin M) (μ : Fin N) {B : ℝ} (hB : 0 < B)
    (h0 : Fv Sig A z v ≤ B)
    (h1 : ∀ a, ‖ent (G Sig A z) (vbar Sig v) (eI a)‖ ≤ B)
    (h2 : ∀ a, ‖ent (G Sig A z) (eI a) (vbar Sig v)‖ ≤ B)
    (h3 : ∀ a b, ‖G Sig A z a b‖ ≤ B) {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r))
    (hns : ∑ r, ns r = 3) :
    ∏ r ∈ Finset.univ.filter (fun r => 1 ≤ ns r), ‖wordA Sig A z v i μ (ns r) (ws r)‖ ≤
      (2 * B) ^ 4 * hA_Ri Sig A z v i ^ ((Finset.univ.filter (fun r => 1 ≤ ns r)).card - 1) := by
  set T := Finset.univ.filter (fun r => 1 ≤ ns r) with hT
  set q := T.card with hq
  set R := hA_Ri Sig A z v i with hR
  have hR0 : 0 ≤ R := by rw [hR, hA_Ri]; positivity
  have hR2 : R ≤ 2 * B := by
    rw [hR, hA_Ri]; linarith [h1 (Sum.inl i), h2 (Sum.inl i)]
  have hRm2 : ‖ent (G Sig A z) (vbar Sig v) (eI (Sum.inr μ))‖ +
      ‖ent (G Sig A z) (eI (Sum.inr μ)) (vbar Sig v)‖ ≤ 2 * B := by
    linarith [h1 (Sum.inr μ), h2 (Sum.inr μ)]
  have hB2 : 0 < 2 * B := by linarith
  set e : Fin p → ℕ := fun r => if ns r = 1 then 1 else 0 with he
  have key : ∀ (n : ℕ) (w : Word n), 1 ≤ n →
      ‖wordA Sig A z v i μ n w‖ * (2 * B) ^ (if n = 1 then 1 else 0) ≤
        R ^ (if n = 1 then 1 else 0) * (2 * B) ^ (n + 1) := by
    intro n w hn
    by_cases h : n = 1
    · subst h
      simp only [↓reduceIte, pow_one]
      have hw := wordA_one_le (Sig := Sig) A z v i μ w
      have hRm0 : 0 ≤ ‖ent (G Sig A z) (vbar Sig v) (eI (Sum.inr μ))‖ +
          ‖ent (G Sig A z) (eI (Sum.inr μ)) (vbar Sig v)‖ := by positivity
      calc ‖wordA Sig A z v i μ 1 w‖ * (2 * B)
          ≤ (R * (‖ent (G Sig A z) (vbar Sig v) (eI (Sum.inr μ))‖ +
              ‖ent (G Sig A z) (eI (Sum.inr μ)) (vbar Sig v)‖)) * (2 * B) :=
            mul_le_mul_of_nonneg_right hw hB2.le
        _ ≤ (R * (2 * B)) * (2 * B) := by gcongr
        _ = R * (2 * B) ^ (1 + 1) := by ring
    · simp only [h, ↓reduceIte, pow_zero, mul_one, one_mul]
      have hw := wordA_le (Sig := Sig) A z v i μ h0 (fun b => h1 _) (fun b => h2 _)
        (fun b b' => h3 _ _) n w
      exact hw.trans (pow_le_pow_left₀ hB.le (by linarith) _)
  have hsT : ∑ r ∈ T, ns r = 3 := by
    rw [← hns]
    exact Finset.sum_filter_of_ne fun r _ h => Nat.one_le_iff_ne_zero.2 h
  have hTne : T.Nonempty := Finset.nonempty_of_sum_ne_zero (by rw [hsT]; omega)
  have hq1 : 1 ≤ q := Finset.card_pos.2 hTne
  set t := ∑ r ∈ T, e r with ht
  have htq : t ≤ q := by
    have : ∑ r ∈ T, e r ≤ ∑ r ∈ T, 1 := Finset.sum_le_sum fun r _ => by
      simp only [he]; split_ifs <;> omega
    simpa using this
  have h2q : 2 * q ≤ 3 + t := by
    have h : ∑ r ∈ T, 2 ≤ ∑ r ∈ T, (ns r + e r) := Finset.sum_le_sum fun r hr => by
      have := (Finset.mem_filter.1 hr).2
      simp only [he]; split_ifs <;> omega
    rw [Finset.sum_add_distrib, hsT, Finset.sum_const, smul_eq_mul] at h
    omega
  have hprod : (∏ r ∈ T, ‖wordA Sig A z v i μ (ns r) (ws r)‖) * (2 * B) ^ t ≤
      R ^ t * (2 * B) ^ (3 + q) := by
    have hs1 : ∑ r ∈ T, (ns r + 1) = 3 + q := by
      rw [Finset.sum_add_distrib, hsT, Finset.sum_const, smul_eq_mul, mul_one]
    calc (∏ r ∈ T, ‖wordA Sig A z v i μ (ns r) (ws r)‖) * (2 * B) ^ t
        = ∏ r ∈ T, (‖wordA Sig A z v i μ (ns r) (ws r)‖ * (2 * B) ^ e r) := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      _ ≤ ∏ r ∈ T, (R ^ e r * (2 * B) ^ (ns r + 1)) :=
          Finset.prod_le_prod₀ (fun r _ => by positivity) fun r hr =>
            key _ _ (Finset.mem_filter.1 hr).2
      _ = R ^ t * (2 * B) ^ (3 + q) := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, hs1]
  have hRt : R ^ t ≤ R ^ (q - 1) * (2 * B) ^ (t - (q - 1)) := by
    have e1 : R ^ t = R ^ (q - 1) * R ^ (t - (q - 1)) := by
      rw [← pow_add]; congr 1; omega
    rw [e1]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR0 hR2 _) (pow_nonneg hR0 _)
  have hfin : (∏ r ∈ T, ‖wordA Sig A z v i μ (ns r) (ws r)‖) * (2 * B) ^ t ≤
      ((2 * B) ^ 4 * R ^ (q - 1)) * (2 * B) ^ t := by
    calc _ ≤ R ^ t * (2 * B) ^ (3 + q) := hprod
      _ ≤ (R ^ (q - 1) * (2 * B) ^ (t - (q - 1))) * (2 * B) ^ (3 + q) :=
          mul_le_mul_of_nonneg_right hRt (by positivity)
      _ = ((2 * B) ^ 4 * R ^ (q - 1)) * (2 * B) ^ t := by
          rw [mul_assoc, ← pow_add, mul_comm ((2 * B) ^ 4), mul_assoc, ← pow_add]
          congr 2
          omega
  exact le_of_mul_le_mul_right hfin (by positivity)

/-- `∑_i R_i^k ≤ (T + 1) N a^k` for `k ≤ 2`, from `∑_i R_i² ≤ N a²` and `M ≤ T N`
(`2 a R_i ≤ a² + R_i²` for `k = 1`). -/
private theorem hA_sumR {R : Fin M → ℝ} {a T : ℝ} (ha : 0 < a)
    (hM : (M : ℝ) ≤ T * N) (h2 : ∑ i, R i ^ 2 ≤ N * a ^ 2) (k : ℕ) (hk : k ≤ 2) :
    ∑ i, R i ^ k ≤ (T + 1) * N * a ^ k := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  interval_cases k
  · simp only [pow_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one]
    nlinarith
  · simp only [pow_one]
    have hs : ∀ i, 2 * a * R i ≤ a ^ 2 + R i ^ 2 := fun i => by nlinarith [sq_nonneg (a - R i)]
    have h3 : 2 * a * ∑ i, R i ≤ (M : ℝ) * a ^ 2 + ∑ i, R i ^ 2 := by
      rw [Finset.mul_sum]
      calc ∑ i, 2 * a * R i ≤ ∑ i, (a ^ 2 + R i ^ 2) := Finset.sum_le_sum fun i _ => hs i
        _ = _ := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]
    have h4 : 2 * a * ∑ i, R i ≤ 2 * a * ((T + 1) * N * a) := by nlinarith
    exact le_of_mul_le_mul_left h4 (by positivity)
  · nlinarith

/-! ## Lemma 8.5 on the event `Θ` -/

/-- The constant `K₁ = 16 p Q₀⁴ (τ⁻¹ + 1)(√K_m + 1)` of Lemma 8.5 on `Θ`. -/
private def hA_K1 (τ c : ℝ) (p : ℕ) : ℝ :=
  16 * p * hA_Q0 τ c ^ 4 * (τ⁻¹ + 1) * (Real.sqrt (mBoundConst τ) + 1)

private theorem hA_K1_ge {τ c : ℝ} (hτ : 0 < τ) (hc : 0 < c) {p : ℕ} (hp : 1 ≤ p) :
    1 ≤ hA_K1 τ c p := by
  unfold hA_K1
  have hQ := hA_Q0_ge hτ hc
  have h1 : (1 : ℝ) ≤ 16 * p := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have h2 : 1 ≤ hA_Q0 τ c ^ 4 := one_le_pow₀ hQ
  have h3 : (1 : ℝ) ≤ τ⁻¹ + 1 := by have := inv_pos.2 hτ; linarith
  have h4 : (1 : ℝ) ≤ Real.sqrt (mBoundConst τ) + 1 := by
    have := Real.sqrt_nonneg (mBoundConst τ); linarith
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le h1 h2) h3) h4

/-- Lemma 8.5 on `Θ`, deterministic: with the entry bounds `B = N^{2ε_A+2δ} Q₀` and
`N⁻¹ ∑_i R_i² ≤ N^{2ε_A} N^{(C₀+2)δ} Ψ²` at `ε_A = δ/4`,
`N^{−3/2} ∑_{iμ} |∏_r c_r(A(w_r)) − ∏_r c_r(Â(w_r))| ≤ K₁ (N^{C₀δ}Ψ)^p +
K₁ 2^p (F_v^p + ∑_μ v̄(μ)² F_{e_μ}^p)`. -/
private theorem hA_on_event {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) {z : ℂ} (hz : z ∈ S) (A : Matrix (Fin M) (Fin N) ℝ)
    {v : Fin M ⊕ Fin N → ℝ} (hv : testNorm v = 1) {p : ℕ} (hp : 0 < p) (ns : Fin p → ℕ)
    (ws : ∀ r, Word (ns r)) (cs : Fin p → Bool) (hns : ∑ r, ns r = 3) {C₀ δ : ℝ} (hδ : 0 < δ)
    (hC₀ : 25 ≤ C₀)
    (h0 : Fv Sig A z v ≤ (N : ℝ) ^ (2 * (δ / 4)) * (N : ℝ) ^ (2 * δ) * hA_Q0 τ c)
    (h1 : ∀ a, ‖ent (G Sig A z) (vbar Sig v) (eI a)‖ ≤
      (N : ℝ) ^ (2 * (δ / 4)) * (N : ℝ) ^ (2 * δ) * hA_Q0 τ c)
    (h2 : ∀ a, ‖ent (G Sig A z) (eI a) (vbar Sig v)‖ ≤
      (N : ℝ) ^ (2 * (δ / 4)) * (N : ℝ) ^ (2 * δ) * hA_Q0 τ c)
    (h3 : ∀ a b, ‖G Sig A z a b‖ ≤ (N : ℝ) ^ (2 * (δ / 4)) * (N : ℝ) ^ (2 * δ) * hA_Q0 τ c)
    (hQ : (N : ℝ)⁻¹ *
              (∑ i, (‖ent (G Sig A z) (vbar Sig v) (eI (Sum.inl i))‖ +
                  ‖ent (G Sig A z) (eI (Sum.inl i)) (vbar Sig v)‖) ^ 2 +
                ∑ μ, (‖ent (G Sig A z) (vbar Sig v) (eI (Sum.inr μ))‖ +
                  ‖ent (G Sig A z) (eI (Sum.inr μ)) (vbar Sig v)‖) ^ 2) ≤
              (N : ℝ) ^ (2 * (δ / 4)) * ((N : ℝ) ^ ((C₀ + 2) * δ) * Psi N (specOf Sig) z ^ 2)) :
    (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ,
        ‖(∏ r, conjIf (cs r) (wordA Sig A z v i μ (ns r) (ws r))) -
          ∏ r, conjIf (cs r) (hatA Sig A z v i μ (ns r) (ws r))‖ ≤
      hA_K1 τ c p * ((N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z) ^ p +
        hA_K1 τ c p * 2 ^ p * (Fv Sig A z v ^ p +
          ∑ μ, vbar Sig v (Sum.inr μ) ^ 2 * Fv Sig A z (eI (Sum.inr μ)) ^ p) := by
  have hN := hA_N_pos hset
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hτ := hset.pos
  have hM : (M : ℝ) ≤ τ⁻¹ * N := by
    have := hset.ratio_le
    rwa [div_le_iff₀ hNp] at this
  obtain ⟨hsiΨ, -, hΨτ⟩ := hA_Psi_bounds hset hz
  set Ψ := Psi N (specOf Sig) z with hΨdef
  have hΨ0 : 0 < Ψ := lt_of_lt_of_le (by positivity) hΨτ
  set g := (N : ℝ) ^ (C₀ * δ) with hg
  have hg0 : 0 < g := Real.rpow_pos_of_pos hNp _
  have hgΨ : 0 < g * Ψ := mul_pos hg0 hΨ0
  set Q₀ := hA_Q0 τ c with hQ₀
  have hQ₀1 : 1 ≤ Q₀ := hA_Q0_ge hτ hset.c_pos
  set B := (N : ℝ) ^ (2 * (δ / 4)) * (N : ℝ) ^ (2 * δ) * Q₀ with hB
  have hB0 : 0 < B := by positivity
  set k₀ := Real.sqrt (mBoundConst τ) with hk₀
  have hk₀0 : 0 ≤ k₀ := Real.sqrt_nonneg _
  set si := (Real.sqrt N)⁻¹ with hsi
  have hB4 : (2 * B) ^ 4 ≤ 16 * Q₀ ^ 4 * g := by
    have e : (2 * B) ^ 4 = 16 * Q₀ ^ 4 * ((N : ℝ) ^ (2 * (δ / 4)) * (N : ℝ) ^ (2 * δ)) ^ 4 := by
      rw [hB]; ring
    have h4 : ((N : ℝ) ^ (2 * (δ / 4)) * (N : ℝ) ^ (2 * δ)) ^ 4 ≤ g := by
      rw [← Real.rpow_add hNp, ← Real.rpow_natCast, ← Real.rpow_mul hNp.le, hg]
      exact Real.rpow_le_rpow_of_exponent_le hN1r (by push_cast; nlinarith)
    rw [e]
    exact mul_le_mul_of_nonneg_left h4 (by positivity)
  set Rx : Fin M → ℝ := fun i => hA_Ri Sig A z v i with hRx
  have hR2 : ∑ i, Rx i ^ 2 ≤ N * (g * Ψ) ^ 2 := by
    have hμ0 : 0 ≤ ∑ μ : Fin N, (‖ent (G Sig A z) (vbar Sig v) (eI (Sum.inr μ))‖ +
        ‖ent (G Sig A z) (eI (Sum.inr μ)) (vbar Sig v)‖) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have h' : ∑ i, Rx i ^ 2 ≤ N * ((N : ℝ) ^ (2 * (δ / 4)) *
        ((N : ℝ) ^ ((C₀ + 2) * δ) * Ψ ^ 2)) := by
      have := mul_le_mul_of_nonneg_left hQ hNp.le
      rw [← mul_assoc, mul_inv_cancel₀ hNp.ne', one_mul] at this
      simp only [hRx, hA_Ri]
      linarith
    refine h'.trans (mul_le_mul_of_nonneg_left ?_ hNp.le)
    have he : (N : ℝ) ^ (2 * (δ / 4)) * (N : ℝ) ^ ((C₀ + 2) * δ) ≤ g ^ 2 := by
      rw [← Real.rpow_add hNp, hg, ← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
      exact Real.rpow_le_rpow_of_exponent_le hN1r (by push_cast; nlinarith)
    calc (N : ℝ) ^ (2 * (δ / 4)) * ((N : ℝ) ^ ((C₀ + 2) * δ) * Ψ ^ 2)
        = ((N : ℝ) ^ (2 * (δ / 4)) * (N : ℝ) ^ ((C₀ + 2) * δ)) * Ψ ^ 2 := by ring
      _ ≤ g ^ 2 * Ψ ^ 2 := mul_le_mul_of_nonneg_right he (sq_nonneg _)
      _ = (g * Ψ) ^ 2 := by ring
  set T := Finset.univ.filter (fun r => 1 ≤ ns r) with hT
  set q := T.card with hq
  have hqp : q ≤ p := by
    have := Finset.card_filter_le (Finset.univ : Finset (Fin p)) (fun r => 1 ≤ ns r)
    rwa [Finset.card_univ, Fintype.card_fin] at this
  have hsT : ∑ r ∈ T, ns r = 3 := by
    rw [← hns]
    exact Finset.sum_filter_of_ne fun r _ h => Nat.one_le_iff_ne_zero.2 h
  have hq3 : q ≤ 3 := by
    have : ∑ r ∈ T, 1 ≤ ∑ r ∈ T, ns r :=
      Finset.sum_le_sum fun r hr => (Finset.mem_filter.1 hr).2
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at this
    omega
  have hq1 : 1 ≤ q := Finset.card_pos.2 (Finset.nonempty_of_sum_ne_zero (by rw [hsT]; omega))
  set L : Fin N → ℝ := fun μ => Fv Sig A z v + Fv Sig A z (eI (Sum.inr μ)) with hL
  have hL0 : ∀ μ, 0 ≤ L μ := fun μ => by
    simp only [hL]
    exact add_nonneg (norm_nonneg _) (norm_nonneg _)
  set w2 : Fin N → ℝ := fun μ => vbar Sig v (Sum.inr μ) ^ 2 with hw2
  have hper : ∀ i μ, ‖(∏ r, conjIf (cs r) (wordA Sig A z v i μ (ns r) (ws r))) -
      ∏ r, conjIf (cs r) (hatA Sig A z v i μ (ns r) (ws r))‖ ≤
      p * (2 * B) ^ 4 * (Rx i ^ (q - 1) * (w2 μ * L μ ^ (p - q))) := by
    intro i μ
    refine (hA_D_le Sig A z hv i μ ns ws cs).trans ?_
    rw [hA_prod_m]
    have hP := hA_P_le (Sig := Sig) (A := A) (z := z) (v := v) i μ hB0 h0 h1 h2 h3 ns ws hns
    have hw20 : 0 ≤ w2 μ := sq_nonneg _
    have hLq : 0 ≤ L μ ^ (p - q) := pow_nonneg (hL0 μ) _
    calc (p : ℝ) * vbar Sig v (Sum.inr μ) ^ 2 *
          ((∏ r ∈ T, ‖wordA Sig A z v i μ (ns r) (ws r)‖) *
            (Fv Sig A z v + Fv Sig A z (eI (Sum.inr μ))) ^ (p - q))
        ≤ p * w2 μ * (((2 * B) ^ 4 * Rx i ^ (q - 1)) * L μ ^ (p - q)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hP hLq) (by positivity)
      _ = _ := by ring
  have hS : ∑ i, ∑ μ, (p : ℝ) * (2 * B) ^ 4 * (Rx i ^ (q - 1) * (w2 μ * L μ ^ (p - q))) =
      p * (2 * B) ^ 4 * ((∑ i, Rx i ^ (q - 1)) * ∑ μ, w2 μ * L μ ^ (p - q)) := by
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  have hsumR : ∑ i, Rx i ^ (q - 1) ≤ (τ⁻¹ + 1) * N * (g * Ψ) ^ (q - 1) :=
    hA_sumR hgΨ hM hR2 (q - 1) (by omega)
  have hW0 : 0 ≤ ∑ μ, w2 μ * L μ ^ (p - q) :=
    Finset.sum_nonneg fun μ _ => mul_nonneg (sq_nonneg _) (pow_nonneg (hL0 μ) _)
  have hN32 : (N : ℝ) ^ (-(3 : ℝ) / 2) * N = si := by
    have h := hA_rpow_neg_half hN 3
    push_cast at h
    rw [h, hsi]
    have hs : Real.sqrt N ^ 2 = N := Real.sq_sqrt hNp.le
    calc ((Real.sqrt N)⁻¹) ^ 3 * N = (Real.sqrt N)⁻¹ * ((Real.sqrt N ^ 2)⁻¹ * N) := by ring
      _ = (Real.sqrt N)⁻¹ := by rw [hs, inv_mul_cancel₀ hNp.ne', mul_one]
  have hsi : si ≤ (k₀ + 1) * Ψ := hsiΨ.trans (mul_le_mul_of_nonneg_right (by linarith) hΨ0.le)
  have hsi0 : 0 ≤ si := by positivity
  have hY : ∀ μ, w2 μ * L μ ^ (p - q) * (g * Ψ) ^ q ≤
      w2 μ * ((g * Ψ) ^ p + 2 ^ p * (Fv Sig A z v ^ p + Fv Sig A z (eI (Sum.inr μ)) ^ p)) := by
    intro μ
    have hy := young_pow (hL0 μ) hgΨ.le hqp hp
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp
    have hc1 : ((p - q : ℕ) : ℝ) / p ≤ 1 := by
      rw [div_le_one hpR]; exact_mod_cast Nat.sub_le p q
    have hc2 : (q : ℝ) / p ≤ 1 := by
      rw [div_le_one hpR]; exact_mod_cast hqp
    have hLp : L μ ^ p ≤ 2 ^ p * (Fv Sig A z v ^ p + Fv Sig A z (eI (Sum.inr μ)) ^ p) := by
      refine (add_pow_le (norm_nonneg _) (norm_nonneg _) p).trans ?_
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Nat.sub_le p 1))
        (by positivity)
    have hLp0 : 0 ≤ L μ ^ p := pow_nonneg (hL0 μ) p
    have hgp0 : 0 ≤ (g * Ψ) ^ p := pow_nonneg hgΨ.le p
    have h' : L μ ^ (p - q) * (g * Ψ) ^ q ≤
        (g * Ψ) ^ p + 2 ^ p * (Fv Sig A z v ^ p + Fv Sig A z (eI (Sum.inr μ)) ^ p) := by
      nlinarith [mul_le_mul_of_nonneg_right hc1 hLp0, mul_le_mul_of_nonneg_right hc2 hgp0]
    calc w2 μ * L μ ^ (p - q) * (g * Ψ) ^ q = w2 μ * (L μ ^ (p - q) * (g * Ψ) ^ q) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h' (sq_nonneg _)
  have hw2s : ∑ μ, w2 μ ≤ 1 := hA_sum_vbar_sq hv
  have hFv0 : 0 ≤ Fv Sig A z v ^ p := pow_nonneg (norm_nonneg _) p
  have hgp0 : 0 ≤ (g * Ψ) ^ p := pow_nonneg hgΨ.le p
  have hK1 : 0 ≤ hA_K1 τ c p := zero_le_one.trans (hA_K1_ge hτ hset.c_pos hp)
  calc (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ,
        ‖(∏ r, conjIf (cs r) (wordA Sig A z v i μ (ns r) (ws r))) -
          ∏ r, conjIf (cs r) (hatA Sig A z v i μ (ns r) (ws r))‖
      ≤ (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ,
          (p : ℝ) * (2 * B) ^ 4 * (Rx i ^ (q - 1) * (w2 μ * L μ ^ (p - q))) := by
        gcongr with i _ μ _
        exact hper i μ
    _ = (N : ℝ) ^ (-(3 : ℝ) / 2) *
          (p * (2 * B) ^ 4 * ((∑ i, Rx i ^ (q - 1)) * ∑ μ, w2 μ * L μ ^ (p - q))) := by rw [hS]
    _ ≤ (N : ℝ) ^ (-(3 : ℝ) / 2) *
          (p * (2 * B) ^ 4 * (((τ⁻¹ + 1) * N * (g * Ψ) ^ (q - 1)) *
            ∑ μ, w2 μ * L μ ^ (p - q))) := by gcongr
    _ = ((N : ℝ) ^ (-(3 : ℝ) / 2) * N) * (2 * B) ^ 4 *
          (p * (τ⁻¹ + 1) * (g * Ψ) ^ (q - 1) * ∑ μ, w2 μ * L μ ^ (p - q)) := by ring
    _ = si * (2 * B) ^ 4 *
          (p * (τ⁻¹ + 1) * (g * Ψ) ^ (q - 1) * ∑ μ, w2 μ * L μ ^ (p - q)) := by rw [hN32]
    _ ≤ ((k₀ + 1) * Ψ) * (16 * Q₀ ^ 4 * g) *
          (p * (τ⁻¹ + 1) * (g * Ψ) ^ (q - 1) * ∑ μ, w2 μ * L μ ^ (p - q)) := by
        have : 0 ≤ (p : ℝ) * (τ⁻¹ + 1) * (g * Ψ) ^ (q - 1) * ∑ μ, w2 μ * L μ ^ (p - q) := by
          have : (0 : ℝ) ≤ τ⁻¹ + 1 := by have := inv_pos.2 hτ; linarith
          positivity
        exact mul_le_mul_of_nonneg_right (mul_le_mul hsi hB4 (by positivity) (by positivity)) this
    _ = hA_K1 τ c p * ∑ μ, w2 μ * L μ ^ (p - q) * (g * Ψ) ^ q := by
        rw [hA_K1, ← Finset.sum_mul, ← hQ₀, ← hk₀]
        obtain ⟨q', hq'⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
        rw [hq', Nat.add_sub_cancel, pow_succ]
        ring
    _ ≤ hA_K1 τ c p * ∑ μ, w2 μ * ((g * Ψ) ^ p +
          2 ^ p * (Fv Sig A z v ^ p + Fv Sig A z (eI (Sum.inr μ)) ^ p)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun μ _ => hY μ) hK1
    _ = hA_K1 τ c p * ((∑ μ, w2 μ) * ((g * Ψ) ^ p + 2 ^ p * Fv Sig A z v ^ p) +
          2 ^ p * ∑ μ, w2 μ * Fv Sig A z (eI (Sum.inr μ)) ^ p) := by
        congr 1
        rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun μ _ => ?_
        ring
    _ ≤ hA_K1 τ c p * (1 * ((g * Ψ) ^ p + 2 ^ p * Fv Sig A z v ^ p) +
          2 ^ p * ∑ μ, w2 μ * Fv Sig A z (eI (Sum.inr μ)) ^ p) := by
        gcongr
    _ = _ := by simp only [hw2]; ring

/-- (A_rough) for the difference: `|∏_r c_r(A(w_r)) − ∏_r c_r(Â(w_r))| ≤ p (2 K N W)^{p+3}`,
`W = 1 + ‖X‖_F²`. -/
private theorem hA_D_rough {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) {z : ℂ} (hz : z ∈ S) (A : Matrix (Fin M) (Fin N) ℝ)
    {v : Fin M ⊕ Fin N → ℝ} (hv : testNorm v = 1) (i : Fin M) (μ : Fin N) {p : ℕ}
    (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r)) (cs : Fin p → Bool) (hns : ∑ r, ns r = 3) :
    ‖(∏ r, conjIf (cs r) (wordA Sig A z v i μ (ns r) (ws r))) -
        ∏ r, conjIf (cs r) (hatA Sig A z v i μ (ns r) (ws r))‖ ≤
      p * (2 * (roughConst τ c * N * (1 + hA_sq A))) ^ (p + 3) := by
  refine (hA_D_le Sig A z hv i μ ns ws cs).trans ?_
  set K := roughConst τ c * N * (1 + hA_sq A) with hK
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hA_N_pos hset
  have hK1 : 1 ≤ K := by
    have hR := hA_roughConst_ge hset.pos hset.le_one hset.c_pos
    have hs := hA_sq_nonneg A
    have h1 : 1 ≤ roughConst τ c * N := one_le_mul_of_one_le_of_one_le hR hN1r
    nlinarith
  have key : ∀ (n : ℕ) (w : Word n), hA_m Sig A z v i μ n w ≤ (2 * K) ^ (n + 1) := by
    intro n w
    cases n with
    | zero =>
      simp only [hA_m, ↓reduceIte, zero_add, pow_one]
      have ha := hA_wordA_rough hset hz A v hv i μ 0 w
      have hb := hA_wordA_rough hset hz A (eI (Sum.inr μ)) (hA_testNorm_eI _) i μ 0 w
      have ea : ‖wordA Sig A z v i μ 0 w‖ = Fv Sig A z v := rfl
      have eb : ‖wordA Sig A z (eI (Sum.inr μ)) i μ 0 w‖ = Fv Sig A z (eI (Sum.inr μ)) := rfl
      rw [ea, zero_add, pow_one] at ha
      rw [eb, zero_add, pow_one] at hb
      linarith
    | succ k =>
      simp only [hA_m, Nat.succ_ne_zero, ↓reduceIte]
      exact (hA_wordA_rough hset hz A v hv i μ _ w).trans
        (pow_le_pow_left₀ (by linarith) (by linarith) _)
  have hv2 := hA_vbar_sq_le (Sig := Sig) hv μ
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hprod : ∏ r, hA_m Sig A z v i μ (ns r) (ws r) ≤ (2 * K) ^ (p + 3) := by
    calc ∏ r, hA_m Sig A z v i μ (ns r) (ws r) ≤ ∏ r, (2 * K) ^ (ns r + 1) :=
          Finset.prod_le_prod₀ (fun r _ => by
            unfold hA_m; split_ifs
            · exact add_nonneg (norm_nonneg _) (norm_nonneg _)
            · exact norm_nonneg _) fun r _ => key _ _
      _ = (2 * K) ^ (p + 3) := by
          rw [Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib, hns]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
          ring_nf
  have hm0 : 0 ≤ ∏ r, hA_m Sig A z v i μ (ns r) (ws r) := Finset.prod_nonneg fun r _ => by
    unfold hA_m; split_ifs
    · exact add_nonneg (norm_nonneg _) (norm_nonneg _)
    · exact norm_nonneg _
  calc (p : ℝ) * vbar Sig v (Sum.inr μ) ^ 2 * ∏ r, hA_m Sig A z v i μ (ns r) (ws r)
      ≤ p * 1 * (2 * K) ^ (p + 3) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hv2 hp0) hprod hm0 (by positivity)
    _ = _ := by ring

private theorem hA_continuous_hatA {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {z : ℂ}
    (hz : 0 < z.im) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) (k : ℕ) (w : Word k) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => hatA Sig A z v i μ k w := by
  cases k with
  | zero =>
    simp only [hatA]
    exact (hA_continuous_wordA hSig hz v i μ 0 w).sub (continuous_const.mul
      (((hA_continuous_G (N := N) hSig hz).matrix_elem _ _).sub continuous_const))
  | succ k =>
    simp only [hatA]
    exact hA_continuous_wordA hSig hz v i μ _ w

private theorem hA_continuous_D {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {z : ℂ}
    (hz : 0 < z.im) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) {p : ℕ} (ns : Fin p → ℕ)
    (ws : ∀ r, Word (ns r)) (cs : Fin p → Bool) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ =>
      (∏ r, conjIf (cs r) (wordA Sig A z v i μ (ns r) (ws r))) -
        ∏ r, conjIf (cs r) (hatA Sig A z v i μ (ns r) (ws r)) :=
  (continuous_finsetProd _ fun _ _ => (hA_continuous_conjIf _).comp
    (hA_continuous_wordA hSig hz v i μ _ _)).sub
  (continuous_finsetProd _ fun _ _ => (hA_continuous_conjIf _).comp
    (hA_continuous_hatA hSig hz v i μ _ _))

/-- `C₀(τ) ≥ 25`. -/
private theorem hA_czero_ge {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) : 25 ≤ czero τ := by
  unfold czero
  have h1 : 2400 / τ ≤ (⌈2400 / τ⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : 2400 ≤ 2400 / τ := by rw [le_div_iff₀ hτ]; nlinarith
  linarith

/-- `dPrev p ≤ dPrevTwo τ p`. -/
private theorem hA_dPrev_le (τ : ℝ) (p : ℕ) : dPrev p ≤ dPrevTwo τ p := by
  unfold dPrevTwo
  have h0 : 0 ≤ dPrev p := by unfold dPrev; positivity
  have h1 : (1 : ℝ) ≤ (kTau τ : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) (kTau τ); linarith
  exact le_mul_of_one_le_right h0 h1

/-- `3 (4p + 17) ≤ dPrev p − 4`: the level of the off-event bound. -/
private theorem hA_dPrev_ge (p : ℕ) : 3 * ((4 * p + 17 : ℕ) : ℝ) ≤ dPrev p - 4 := by
  unfold dPrev
  push_cast
  have : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  nlinarith

/-! ## Polynomial growth in the matrix: integrability of the tagged-word terms -/

private theorem hA_ent_eI_left {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ)
    (y : ι → ℝ) (r : ι) : ent B (eI r) y = ∑ t, B r t * (y t : ℂ) := by
  rw [hA_ent_eq]
  simp [eI, Pi.single_apply, apply_ite, ite_mul, Finset.sum_ite_eq']

/-- The column `μ` of `X̂` vanishes for `X` with column `μ` set to `0`. -/
private theorem hA_Xhat_col (A : Matrix (Fin M) (Fin N) ℝ) (μ : Fin N) (q : Fin M ⊕ Fin N) :
    Xhat (updCol A μ 0) q (Sum.inr μ) = 0 := by
  rcases q with j | ν
  · simp [Xhat, cplx, updCol]
  · simp [Xhat]

/-- `G^{(μ)} = G(X⁰) + z⁻¹ e_μ e_μ^*` for `X⁰` the matrix `X` with column `μ` set to `0`. -/
private theorem hA_Gmu_apply {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (μ : Fin N) (s t : Fin M ⊕ Fin N) :
    Gmu Sig A z μ s t = G Sig (updCol A μ 0) z s t +
      (if s = Sum.inr μ ∧ t = Sum.inr μ then z⁻¹ else 0) := by
  set A0 := updCol A μ 0 with hA0
  have hcol : ∀ x : Fin M ⊕ Fin N → ℝ,
      ent (G1 Sig A0 z (Sum.inr μ) * Xhat A0) x (eI (Sum.inr μ)) = 0 := by
    intro x
    rw [hA_ent_eI_right]
    refine Finset.sum_eq_zero fun r _ => ?_
    simp [Matrix.mul_apply, hA0, hA_Xhat_col]
  have hrow : ∀ y : Fin M ⊕ Fin N → ℝ,
      ent ((Xhat A0)ᵀ * G1 Sig A0 z (Sum.inr μ)) (eI (Sum.inr μ)) y = 0 := by
    intro y
    rw [hA_ent_eI_left]
    refine Finset.sum_eq_zero fun r _ => ?_
    simp [Matrix.mul_apply, hA0, hA_Xhat_col]
  have hQ : ((Xhat A0)ᵀ * G1 Sig A0 z (Sum.inr μ) * Xhat A0) (Sum.inr μ) (Sum.inr μ) = 0 := by
    simp [Matrix.mul_apply, hA0, hA_Xhat_col]
  have hii := Gii hSig A0 hz μ
  rw [hQ, sub_zero] at hii
  have hg : G Sig A0 z (Sum.inr μ) (Sum.inr μ) = -z⁻¹ := by
    have : G Sig A0 z (Sum.inr μ) (Sum.inr μ) = 1 / (-z) := by
      rw [← hii, one_div_one_div]
    rw [this, one_div, inv_neg]
  have hm := main_identity hSig A0 hz μ (eI s) (eI t)
  rw [hcol, hrow, ent_eI_eI, ent_eI_eI] at hm
  have hG1 : G1 Sig A0 z (Sum.inr μ) = Gmu Sig A z μ := Gmu_updCol Sig A z μ 0
  rw [hG1, hg] at hm
  by_cases hs : s = Sum.inr μ <;> by_cases ht : t = Sum.inr μ
  · subst hs; subst ht
    simp [eI] at hm
    simp only [and_self, ite_true]
    linear_combination -hm
  · simp [eI, hs, ht] at hm
    simp [hs, ht, hm]
  · simp [eI, hs, ht] at hm
    simp [hs, ht, hm]
  · simp [eI, hs, ht] at hm
    simp [hs, ht, hm]

private theorem hA_continuous_updCol0 (μ : Fin N) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => updCol A μ 0 := by
  refine continuous_pi fun j => continuous_pi fun ν => ?_
  by_cases h : ν = μ
  · simp only [updCol, h, ite_true]
    exact continuous_const
  · simp only [updCol, h, ite_false]
    exact continuous_id.matrix_elem j ν

/-- `f` is continuous and `|f(A)| ≤ C (1 + ‖A‖_F²)^k`. -/
private def hA_PG (f : Matrix (Fin M) (Fin N) ℝ → ℂ) : Prop :=
  Continuous f ∧ ∃ C : ℝ, ∃ k : ℕ, ∀ A, ‖f A‖ ≤ C * (1 + hA_sq A) ^ k

private theorem hA_W_one (A : Matrix (Fin M) (Fin N) ℝ) : 1 ≤ 1 + hA_sq A := by
  have := hA_sq_nonneg A; linarith

private theorem hA_PG_of_bdd {f : Matrix (Fin M) (Fin N) ℝ → ℂ} (hc : Continuous f)
    (hb : ∃ C : ℝ, ∀ A, ‖f A‖ ≤ C) : hA_PG f := by
  obtain ⟨C, hC⟩ := hb
  exact ⟨hc, C, 0, fun A => by rw [pow_zero, mul_one]; exact hC A⟩

private theorem hA_PG_const (b : ℂ) : hA_PG (M := M) (N := N) fun _ => b :=
  hA_PG_of_bdd continuous_const ⟨‖b‖, fun _ => le_rfl⟩

private theorem hA_PG_mul {f g : Matrix (Fin M) (Fin N) ℝ → ℂ} (hf : hA_PG f) (hg : hA_PG g) :
    hA_PG fun A => f A * g A := by
  obtain ⟨hfc, C₁, k₁, hf⟩ := hf
  obtain ⟨hgc, C₂, k₂, hg⟩ := hg
  refine ⟨hfc.mul hgc, C₁ * C₂, k₁ + k₂, fun A => ?_⟩
  rw [norm_mul, pow_add]
  calc ‖f A‖ * ‖g A‖ ≤ (C₁ * (1 + hA_sq A) ^ k₁) * (C₂ * (1 + hA_sq A) ^ k₂) :=
        mul_le_mul (hf A) (hg A) (norm_nonneg _) ((norm_nonneg _).trans (hf A))
    _ = _ := by ring

private theorem hA_PG_add_aux {f g h : Matrix (Fin M) (Fin N) ℝ → ℂ}
    (hc : Continuous h) (hle : ∀ A, ‖h A‖ ≤ ‖f A‖ + ‖g A‖) (hf : hA_PG f) (hg : hA_PG g) :
    hA_PG h := by
  obtain ⟨-, C₁, k₁, hf⟩ := hf
  obtain ⟨-, C₂, k₂, hg⟩ := hg
  refine ⟨hc, |C₁| + |C₂|, k₁ + k₂, fun A => ?_⟩
  have hW := hA_W_one A
  have h1 : (1 + hA_sq A) ^ k₁ ≤ (1 + hA_sq A) ^ (k₁ + k₂) := pow_le_pow_right₀ hW (by omega)
  have h2 : (1 + hA_sq A) ^ k₂ ≤ (1 + hA_sq A) ^ (k₁ + k₂) := pow_le_pow_right₀ hW (by omega)
  have hp1 : 0 ≤ (1 + hA_sq A) ^ k₁ := by positivity
  have hp2 : 0 ≤ (1 + hA_sq A) ^ k₂ := by positivity
  calc ‖h A‖ ≤ ‖f A‖ + ‖g A‖ := hle A
    _ ≤ C₁ * (1 + hA_sq A) ^ k₁ + C₂ * (1 + hA_sq A) ^ k₂ := add_le_add (hf A) (hg A)
    _ ≤ |C₁| * (1 + hA_sq A) ^ (k₁ + k₂) + |C₂| * (1 + hA_sq A) ^ (k₁ + k₂) :=
        add_le_add (mul_le_mul (le_abs_self _) h1 hp1 (abs_nonneg _))
          (mul_le_mul (le_abs_self _) h2 hp2 (abs_nonneg _))
    _ = _ := by ring

private theorem hA_PG_add {f g : Matrix (Fin M) (Fin N) ℝ → ℂ} (hf : hA_PG f) (hg : hA_PG g) :
    hA_PG fun A => f A + g A :=
  hA_PG_add_aux (hf.1.add hg.1) (fun _ => norm_add_le _ _) hf hg

private theorem hA_PG_sub {f g : Matrix (Fin M) (Fin N) ℝ → ℂ} (hf : hA_PG f) (hg : hA_PG g) :
    hA_PG fun A => f A - g A :=
  hA_PG_add_aux (hf.1.sub hg.1) (fun _ => norm_sub_le _ _) hf hg

private theorem hA_PG_sum {ι : Type*} (s : Finset ι) {f : ι → Matrix (Fin M) (Fin N) ℝ → ℂ}
    (hf : ∀ i ∈ s, hA_PG (f i)) : hA_PG fun A => ∑ i ∈ s, f i A := by
  induction s using Finset.induction_on with
  | empty => simpa using hA_PG_const (M := M) (N := N) 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact hA_PG_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private theorem hA_PG_prod {ι : Type*} (s : Finset ι) {f : ι → Matrix (Fin M) (Fin N) ℝ → ℂ}
    (hf : ∀ i ∈ s, hA_PG (f i)) : hA_PG fun A => ∏ i ∈ s, f i A := by
  induction s using Finset.induction_on with
  | empty => simpa using hA_PG_const (M := M) (N := N) 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact hA_PG_mul (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private theorem hA_PG_list {α : Type*} (l : List α) {f : α → Matrix (Fin M) (Fin N) ℝ → ℂ}
    (hf : ∀ a ∈ l, hA_PG (f a)) : hA_PG fun A => (l.map fun a => f a A).prod := by
  induction l with
  | nil => simpa using hA_PG_const (M := M) (N := N) 1
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact hA_PG_mul (hf a (by simp)) (ih fun b hb => hf b (by simp [hb]))

private theorem hA_PG_pow {f : Matrix (Fin M) (Fin N) ℝ → ℂ} (hf : hA_PG f) (n : ℕ) :
    hA_PG fun A => f A ^ n := by
  induction n with
  | zero => simpa using hA_PG_const (M := M) (N := N) 1
  | succ n ih =>
    simp only [pow_succ]
    exact hA_PG_mul ih hf

private theorem hA_PG_conjIf (b : Bool) {f : Matrix (Fin M) (Fin N) ℝ → ℂ} (hf : hA_PG f) :
    hA_PG fun A => conjIf b (f A) := by
  obtain ⟨hfc, C, k, hb⟩ := hf
  exact ⟨(hA_continuous_conjIf b).comp hfc, C, k, fun A => by rw [hA_norm_conjIf]; exact hb A⟩

private theorem hA_PG_entry (j : Fin M) (μ : Fin N) :
    hA_PG fun A : Matrix (Fin M) (Fin N) ℝ => ((A j μ : ℝ) : ℂ) := by
  refine ⟨Complex.continuous_ofReal.comp (continuous_id.matrix_elem j μ), 1, 1, fun A => ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs, one_mul, pow_one]
  have h1 : A j μ ^ 2 ≤ hA_sq A := by
    unfold hA_sq
    exact Finset.single_le_sum (f := fun α : Fin M × Fin N => A α.1 α.2 ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ (j, μ))
  nlinarith [abs_nonneg (A j μ), sq_abs (A j μ), sq_nonneg (|A j μ| - 1)]

private theorem hA_G_bdd {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {z : ℂ}
    (hz : 0 < z.im) (s t : Fin M ⊕ Fin N) :
    ∃ C : ℝ, ∀ A : Matrix (Fin M) (Fin N) ℝ, ‖G Sig A z s t‖ ≤ C :=
  ⟨(1 + 5 * ‖z‖) / z.im * Real.sqrt (eI s ⬝ᵥ SigU (n := Fin N) Sig *ᵥ eI s) *
    Real.sqrt (eI t ⬝ᵥ SigU (n := Fin N) Sig *ᵥ eI t), fun A => by
      rw [← ent_eI_eI (G Sig A z) s t]; exact opbound hSig A hz (eI s) (eI t)⟩

private theorem hA_PG_G {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {z : ℂ}
    (hz : 0 < z.im) (s t : Fin M ⊕ Fin N) :
    hA_PG fun A : Matrix (Fin M) (Fin N) ℝ => G Sig A z s t :=
  hA_PG_of_bdd ((hA_continuous_G hSig hz).matrix_elem s t) (hA_G_bdd hSig hz s t)

private theorem hA_PG_Gmu {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {z : ℂ}
    (hz : 0 < z.im) (μ : Fin N) (s t : Fin M ⊕ Fin N) :
    hA_PG fun A : Matrix (Fin M) (Fin N) ℝ => Gmu Sig A z μ s t := by
  have e : (fun A : Matrix (Fin M) (Fin N) ℝ => Gmu Sig A z μ s t) = fun A =>
      G Sig (updCol A μ 0) z s t + (if s = Sum.inr μ ∧ t = Sum.inr μ then z⁻¹ else 0) :=
    funext fun A => hA_Gmu_apply hSig A hz μ s t
  rw [e]
  refine hA_PG_add ?_ (hA_PG_const _)
  obtain ⟨C, hC⟩ := hA_G_bdd (N := N) hSig hz s t
  exact hA_PG_of_bdd (((hA_continuous_G hSig hz).matrix_elem s t).comp (hA_continuous_updCol0 μ))
    ⟨C, fun A => hC _⟩

private theorem hA_PG_ent {F : Matrix (Fin M) (Fin N) ℝ → Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ}
    (hF : ∀ s t, hA_PG fun A => F A s t) (x y : Fin M ⊕ Fin N → ℝ) :
    hA_PG fun A => ent (F A) x y := by
  have e : (fun A => ent (F A) x y) = fun A => ∑ s, ∑ t, (x s : ℂ) * F A s t * (y t : ℂ) :=
    funext fun A => hA_ent_eq _ x y
  rw [e]
  exact hA_PG_sum _ fun s _ => hA_PG_sum _ fun t _ =>
    hA_PG_mul (hA_PG_mul (hA_PG_const _) (hF s t)) (hA_PG_const _)

private theorem hA_PG_entGmu {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {z : ℂ}
    (hz : 0 < z.im) (μ : Fin N) (x y : Fin M ⊕ Fin N → ℝ) :
    hA_PG fun A : Matrix (Fin M) (Fin N) ℝ => ent (Gmu Sig A z μ) x y :=
  hA_PG_ent (F := fun A => Gmu Sig A z μ) (hA_PG_Gmu hSig hz μ) x y

private theorem hA_PG_linCol {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {z : ℂ}
    (hz : 0 < z.im) (μ : Fin N) (x : Fin M ⊕ Fin N → ℝ) :
    hA_PG fun A : Matrix (Fin M) (Fin N) ℝ => linForm (colC Sig A z x μ) fun j => A j μ := by
  unfold linForm colC
  exact hA_PG_sum _ fun j _ => hA_PG_mul (hA_PG_entGmu hSig hz μ _ _) (hA_PG_entry j μ)

private theorem hA_PG_linRow {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {z : ℂ}
    (hz : 0 < z.im) (μ : Fin N) (x : Fin M ⊕ Fin N → ℝ) :
    hA_PG fun A : Matrix (Fin M) (Fin N) ℝ => linForm (rowC Sig A z x μ) fun j => A j μ := by
  unfold linForm rowC
  exact hA_PG_sum _ fun j _ => hA_PG_mul (hA_PG_entGmu hSig hz μ _ _) (hA_PG_entry j μ)

/-- The shape of the list of linear forms of `[G_{xy}]^s` (`true` for a column form). -/
private def hA_bfT (x y : Letter) (s : Fin 3) : List Bool :=
  if s = 0 then []
  else if s = 1 then (if x = .M then [] else [true]) ++ (if y = .M then [] else [false])
  else if x = .V then (if y = .M then [] else [false])
  else if y = .V then (if x = .M then [] else [true]) else []

private theorem hA_brackForms_eq (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) (x y : Letter) (s : Fin 3) :
    brackForms Sig A z v i μ x y s = (hA_bfT x y s).map fun t =>
      if t then colC Sig A z (letVec Sig v i μ x) μ else rowC Sig A z (letVec Sig v i μ y) μ := by
  unfold brackForms hA_bfT
  split_ifs <;> simp

private theorem hA_PG_brack {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {z : ℂ}
    (hz : 0 < z.im) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) (x y : Letter) (s : Fin 3) :
    hA_PG fun A : Matrix (Fin M) (Fin N) ℝ => brack Sig A z v i μ x y s := by
  unfold brack
  refine hA_PG_mul ?_ ?_
  · unfold brackScal
    split_ifs
    · exact hA_PG_entGmu hSig hz μ _ _
    all_goals exact hA_PG_const _
  · simp only [hA_brackForms_eq, List.map_map, Function.comp_def]
    refine hA_PG_list _ (f := fun (t : Bool) (A : Matrix (Fin M) (Fin N) ℝ) =>
      linForm (if t then colC Sig A z (letVec Sig v i μ x) μ
        else rowC Sig A z (letVec Sig v i μ y) μ) fun j => A j μ) fun t _ => ?_
    cases t
    · simpa using hA_PG_linRow hSig hz μ (letVec Sig v i μ y)
    · simpa using hA_PG_linCol hSig hz μ (letVec Sig v i μ x)

private theorem hA_PG_tagA {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {z : ℂ}
    (hz : 0 < z.im) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) (n : ℕ) (w : Word n)
    (σ : Fin (n + 1) → Fin 3) :
    hA_PG fun A : Matrix (Fin M) (Fin N) ℝ => tagA Sig A z v i μ n w σ := by
  cases n with
  | zero =>
    simp only [tagA]
    refine hA_PG_mul ?_ ?_
    · unfold emptyScal
      split_ifs
      · exact hA_PG_sub (hA_PG_entGmu hSig hz μ _ _) (hA_PG_const _)
      all_goals exact hA_PG_const _
    · unfold emptyForms
      split_ifs
      · simpa using hA_PG_const (M := M) (N := N) 1
      · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
        exact hA_PG_mul (hA_PG_linCol hSig hz μ _) (hA_PG_linRow hSig hz μ _)
      · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
        have e : ∀ A : Matrix (Fin M) (Fin N) ℝ,
            linForm (colC Sig A z (vbar Sig v) μ + rowC Sig A z (vbar Sig v) μ) (fun j => A j μ) =
              linForm (colC Sig A z (vbar Sig v) μ) (fun j => A j μ) +
                linForm (rowC Sig A z (vbar Sig v) μ) (fun j => A j μ) := fun A => by
          simp only [linForm, Pi.add_apply, add_mul, Finset.sum_add_distrib]
        simp only [e]
        exact hA_PG_add (hA_PG_linCol hSig hz μ _) (hA_PG_linRow hSig hz μ _)
  | succ k =>
    simp only [tagA]
    exact hA_PG_prod _ fun l _ => hA_PG_brack hSig hz v i μ _ _ _

private theorem hA_PG_wordA {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {z : ℂ}
    (hz : 0 < z.im) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) (n : ℕ) (w : Word n) :
    hA_PG fun A : Matrix (Fin M) (Fin N) ℝ => wordA Sig A z v i μ n w := by
  cases n with
  | zero =>
    simp only [wordA]
    exact hA_PG_ent (F := fun A => G Sig A z - PiZ N Sig z)
      (fun s t => by simpa using hA_PG_sub (hA_PG_G hSig hz s t) (hA_PG_const _)) _ _
  | succ k =>
    simp only [wordA]
    refine hA_PG_mul (hA_PG_mul ?_ (hA_PG_prod _ fun l _ => hA_PG_G hSig hz _ _)) ?_
    · exact hA_PG_ent (F := fun A => G Sig A z) (hA_PG_G hSig hz) _ _
    · exact hA_PG_ent (F := fun A => G Sig A z) (hA_PG_G hSig hz) _ _

private theorem hA_PG_hatA {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {z : ℂ}
    (hz : 0 < z.im) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) (n : ℕ) (w : Word n) :
    hA_PG fun A : Matrix (Fin M) (Fin N) ℝ => hatA Sig A z v i μ n w := by
  cases n with
  | zero =>
    simp only [hatA]
    exact hA_PG_sub (hA_PG_wordA hSig hz v i μ 0 w)
      (hA_PG_mul (hA_PG_const _) (hA_PG_sub (hA_PG_G hSig hz _ _) (hA_PG_const _)))
  | succ k =>
    simp only [hatA]
    exact hA_PG_wordA hSig hz v i μ _ w

private theorem hA_PG_integrable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {τ : ℝ} (hτ : 0 < τ) {C : ℕ → ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ}
    (hX : EntryAssumption C X) (hN : 1 ≤ N) (hM : (M : ℝ) ≤ τ⁻¹ * N)
    {f : Matrix (Fin M) (Fin N) ℝ → ℂ} (hf : hA_PG f) : Integrable fun ω => f (X ω) := by
  obtain ⟨hfc, C', k, hb⟩ := hf
  have hW := (hA_moment_W hτ hX hN hM k).1
  exact (hW.const_mul C').mono' (hfc.measurable.comp (hA_measurable_X hX)).aestronglyMeasurable
    (ae_of_all _ fun ω => hb (X ω))

/-! ## Sums over tagged-word tuples and word tuples -/

private theorem hA_conjIf_ofReal_pow (b : Bool) (x : ℝ) (k : ℕ) :
    conjIf b ((x : ℂ) ^ k) = (x : ℂ) ^ k := by
  cases b <;> simp [conjIf]

private theorem hA_sum_swap {α β γ : Type*} [Fintype α] [Fintype β] (s : Finset γ)
    (f : α → β → γ → ℝ) : ∑ a, ∑ b, ∑ c ∈ s, f a b c = ∑ c ∈ s, ∑ a, ∑ b, f a b c := by
  calc ∑ a, ∑ b, ∑ c ∈ s, f a b c = ∑ a, ∑ c ∈ s, ∑ b, f a b c :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- (wh_A_identity) for products:
`∏_r c_r(Â(w_r)) = ∑_{σs} v̄(μ)^{d_v} ∏_r c_r(A(w_r, σ_r) G_μμ^{|σ_r|_μ})`. -/
private theorem hA_prod_hatA {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M)
    (μ : Fin N) {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r)) (cs : Fin p → Bool) :
    ∏ r, conjIf (cs r) (hatA Sig A z v i μ (ns r) (ws r)) =
      ∑ σs : (∀ r, Fin (ns r + 1) → Fin 3), ((vbar Sig v (Sum.inr μ) : ℝ) : ℂ) ^ dVof σs *
        ∏ r, conjIf (cs r) (tagA Sig A z v i μ (ns r) (ws r) (σs r) *
          G Sig A z (Sum.inr μ) (Sum.inr μ) ^ tagMu (σs r)) := by
  have h1 : ∀ r, conjIf (cs r) (hatA Sig A z v i μ (ns r) (ws r)) =
      ∑ σ : Fin (ns r + 1) → Fin 3, conjIf (cs r) (tagA Sig A z v i μ (ns r) (ws r) σ *
        G Sig A z (Sum.inr μ) (Sum.inr μ) ^ tagMu σ) *
          ((vbar Sig v (Sum.inr μ) : ℝ) : ℂ) ^ tagV σ := by
    intro r
    rw [wh_A_identity hSig A hz v i μ (ns r) (ws r), hA_conjIf_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hA_conjIf_mul, hA_conjIf_ofReal_pow]
  simp only [h1]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun σs _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, mul_comm]
  rfl

/-- Lemma 8.5 (`lem:A wt A`): replacing `A` by `Â` in (sc_step 5) with `n = 3` costs at most
`K((N^{C₀δ}Ψ)^p + max_{𝒱_v} E F^p)`; any conjugation pattern. -/
theorem hatA_replace (τ c : ℝ) (C : ℕ → ℝ) (p : ℕ) (C₀ δ DA : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hc : 0 < c) (hp : Even p) (hp2 : 2 ≤ p) (hδ : 0 < δ) (hC₀ : czero τ ≤ C₀)
    (hC₀δ : C₀ * δ ≤ τ / 4) (hDA : dPrevTwo τ p ≤ DA) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (S : Set ℂ) (m : ℕ), CompSetting τ c M N Sig S → 1 ≤ m →
      PropA N C allModels Sig S C₀ δ (m - 1) (δ / 4) DA →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption C X →
        ∀ z ∈ levelSet N δ S m, ∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 →
          ∀ (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r)) (cs : Fin p → Bool), ∑ r, ns r = 3 →
            (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ,
              ‖∫ ω, ((∏ r, conjIf (cs r) (wordA Sig (X ω) z v i μ (ns r) (ws r))) -
                ∏ r, conjIf (cs r) (hatA Sig (X ω) z v i μ (ns r) (ws r)))‖ ≤
              K * (((N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z) ^ p + maxFp Sig X z v p) := by
  have _ := hp
  have hC25 : 25 ≤ C₀ := (hA_czero_ge hτ hτ1).trans hC₀
  have hDA' : dPrev p ≤ DA := (hA_dPrev_le τ p).trans hDA
  have hεA : 0 < δ / 4 := by positivity
  obtain ⟨N₁, h₁⟩ := hA_event τ c C C₀ δ (δ / 4) DA hτ hτ1 hc hδ hC25 hC₀δ hεA
  obtain ⟨N₂, h₂⟩ := integral_Fv_pow_le τ c C p hτ hτ1 hc
  set K1 := hA_K1 τ c p with hK1def
  have hK1 : 1 ≤ K1 := hA_K1_ge hτ hc (by omega)
  set R := roughConst τ c with hR
  have hR1 : 1 ≤ R := hA_roughConst_ge hτ hτ1 hc
  have hT0 : 0 ≤ τ⁻¹ := (inv_pos.2 hτ).le
  set Kz : ℝ := τ⁻¹ ^ 2 * (p : ℝ) ^ 2 * (2 * R) ^ (2 * (p + 3)) * hA_KW τ C (2 * (p + 3))
    with hKz
  have hKz0 : 0 ≤ Kz := by
    have := hA_KW_nonneg hτ C (2 * (p + 3))
    rw [hKz]; positivity
  refine ⟨2 * K1 + 2 * (K1 * 2 ^ p), by positivity,
    max (max N₁ N₂) (max ⌈Kz⌉₊ (max ⌈τ⁻¹ ^ p⌉₊ 1)), ?_⟩
  intro N hN M Sig S m hset hm hA Ω _ _ X hX z hz v hv ns ws cs hns
  have hNN₁ : N₁ ≤ N := by omega
  have hNN₂ : N₂ ≤ N := by omega
  have hNKz : ⌈Kz⌉₊ ≤ N := by omega
  have hNτ : ⌈τ⁻¹ ^ p⌉₊ ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : (0 : ℝ) < N := by linarith
  have hzS : z ∈ S := hz.1
  have hzD := hset.domain.1 hzS
  have hη : 0 < z.im := hzD.1
  have hSig := hset.sigma.posDef
  have hM : (M : ℝ) ≤ τ⁻¹ * N := by
    have := hset.ratio_le
    rwa [div_le_iff₀ hNp] at this
  obtain ⟨-, -, hΨτ⟩ := hA_Psi_bounds hset hzS
  set Ψ := Psi N (specOf Sig) z with hΨdef
  have hΨ0 : 0 ≤ Ψ := le_trans (by positivity) hΨτ
  set g := (N : ℝ) ^ (C₀ * δ) with hg
  have hg1 : 1 ≤ g := Real.one_le_rpow hN1r (by nlinarith)
  have hgp0 : 0 ≤ (g * Ψ) ^ p := pow_nonneg (mul_nonneg (by linarith) hΨ0) p
  -- the event `Θ`
  set Θ := {ω |
            Fv Sig (X ω) z v ≤ (N : ℝ) ^ (2 * (δ / 4)) * (N : ℝ) ^ (2 * δ) * hA_Q0 τ c ∧
            (∀ a, ‖ent (G Sig (X ω) z) (vbar Sig v) (eI a)‖ ≤
              (N : ℝ) ^ (2 * (δ / 4)) * (N : ℝ) ^ (2 * δ) * hA_Q0 τ c) ∧
            (∀ a, ‖ent (G Sig (X ω) z) (eI a) (vbar Sig v)‖ ≤
              (N : ℝ) ^ (2 * (δ / 4)) * (N : ℝ) ^ (2 * δ) * hA_Q0 τ c) ∧
            (∀ a b, ‖G Sig (X ω) z a b‖ ≤
              (N : ℝ) ^ (2 * (δ / 4)) * (N : ℝ) ^ (2 * δ) * hA_Q0 τ c) ∧
            (N : ℝ)⁻¹ *
              (∑ i, (‖ent (G Sig (X ω) z) (vbar Sig v) (eI (Sum.inl i))‖ +
                  ‖ent (G Sig (X ω) z) (eI (Sum.inl i)) (vbar Sig v)‖) ^ 2 +
                ∑ μ, (‖ent (G Sig (X ω) z) (vbar Sig v) (eI (Sum.inr μ))‖ +
                  ‖ent (G Sig (X ω) z) (eI (Sum.inr μ)) (vbar Sig v)‖) ^ 2) ≤
              (N : ℝ) ^ (2 * (δ / 4)) * ((N : ℝ) ^ ((C₀ + 2) * δ) * Psi N (specOf Sig) z ^ 2)}
    with hΘ
  have hΘp : HighProbAt N (DA - 4) Θ :=
    h₁ N hNN₁ M Sig S allModels m hset hm hA Ω X hX trivial z hz v hv
  -- the random variables
  set Dm : Fin M → Fin N → Matrix (Fin M) (Fin N) ℝ → ℂ := fun i μ A =>
    (∏ r, conjIf (cs r) (wordA Sig A z v i μ (ns r) (ws r))) -
      ∏ r, conjIf (cs r) (hatA Sig A z v i μ (ns r) (ws r)) with hDm
  set Z : Ω → ℝ := fun ω => (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ, ‖Dm i μ (X ω)‖ with hZ
  set Y : Ω → ℝ := fun ω => Fv Sig (X ω) z v ^ p +
    ∑ μ, vbar Sig v (Sum.inr μ) ^ 2 * Fv Sig (X ω) z (eI (Sum.inr μ)) ^ p with hY
  set ξ : Ω → ℝ := fun ω => max (Z ω - K1 * 2 ^ p * Y ω) 0 with hξ
  have hZΘ : ∀ ω ∈ Θ, Z ω ≤ K1 * (g * Ψ) ^ p + K1 * 2 ^ p * Y ω := by
    intro ω hω
    obtain ⟨h0, h1, h2, h3, hQ⟩ := hω
    exact hA_on_event hset hzS (X ω) hv (by omega) ns ws cs hns hδ hC25 h0 h1 h2 h3 hQ
  have hΓ0 : 0 ≤ K1 * (g * Ψ) ^ p := by positivity
  have hξΘ : ∀ ω ∈ Θ, ξ ω ≤ K1 * (g * Ψ) ^ p := fun ω hω =>
    max_le (by have := hZΘ ω hω; linarith) hΓ0
  have hdom : DomAt N 0 (DA - 4) ξ (fun _ => K1 * (g * Ψ) ^ p) := by
    unfold DomAt
    refine le_trans (measure_mono fun ω hω => ?_) hΘp
    simp only [Set.mem_ofPred_eq, Real.rpow_zero, one_mul] at hω
    intro hωΘ
    exact absurd (hξΘ ω hωΘ) (not_le.2 hω)
  -- measurability and the rough bound
  have hXm := hA_measurable_X hX
  have hDmeas : ∀ i μ, Measurable fun ω => ‖Dm i μ (X ω)‖ := fun i μ =>
    ((hA_continuous_D hSig hη v i μ ns ws cs).norm.measurable).comp hXm
  set W : Ω → ℝ := fun ω => 1 + hA_sq (X ω) with hW
  have hW1 : ∀ ω, 1 ≤ W ω := fun ω => by
    have := hA_sq_nonneg (X ω); simp only [hW]; linarith
  have hDr : ∀ i μ ω, ‖Dm i μ (X ω)‖ ≤ p * (2 * R * N) ^ (p + 3) * W ω ^ (p + 3) := by
    intro i μ ω
    have := hA_D_rough hset hzS (X ω) hv i μ ns ws cs hns
    calc ‖Dm i μ (X ω)‖ ≤ p * (2 * (R * N * (1 + hA_sq (X ω)))) ^ (p + 3) := this
      _ = _ := by rw [show 2 * (R * N * (1 + hA_sq (X ω))) = 2 * R * N * W ω by ring, mul_pow]; ring
  obtain ⟨hWi, -⟩ := hA_moment_W hτ hX hN1 hM (p + 3)
  have hDint : ∀ i μ, Integrable fun ω => ‖Dm i μ (X ω)‖ := fun i μ =>
    (hWi.const_mul ((p : ℝ) * (2 * R * N) ^ (p + 3))).mono' (hDmeas i μ).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hDr i μ ω)
  have hZint : Integrable Z :=
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun μ _ => hDint i μ).const_mul _
  have hFv := fun (w : Fin M ⊕ Fin N → ℝ) (hw : testNorm w = 1) =>
    h₂ N hNN₂ M Sig X S ⟨hset.ratio_ge, hset.ratio_le, hX, hset.sigma⟩ hset.domain
      hset.oneXm z hzS w hw
  have hYint : Integrable Y :=
    (hFv v hv).1.add (integrable_finsetSum _ fun μ _ =>
      ((hFv _ (hA_testNorm_eI (Sum.inr μ))).1.const_mul _))
  have hZmeas : Measurable Z :=
    (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun μ _ => hDmeas i μ).const_mul _
  have hYmeas : Measurable Y := by
    refine ((((hA_continuous_Fv hSig hη v).measurable).comp hXm).pow_const p).add ?_
    exact Finset.measurable_sum _ fun μ _ => measurable_const.mul
      ((((hA_continuous_Fv hSig hη _).measurable).comp hXm).pow_const p)
  have hξmeas : Measurable ξ := (hZmeas.sub (hYmeas.const_mul _)).max measurable_const
  have hξ0 : ∀ ω, 0 ≤ ξ ω := fun ω => le_max_right _ _
  have hZ0 : ∀ ω, 0 ≤ Z ω := fun ω => mul_nonneg (Real.rpow_nonneg hNp.le _)
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hY0 : ∀ ω, 0 ≤ Y ω := fun ω => add_nonneg (pow_nonneg (norm_nonneg _) _)
    (Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (pow_nonneg (norm_nonneg _) _))
  have hK2 : 0 ≤ K1 * 2 ^ p := by positivity
  have hξZ : ∀ ω, ξ ω ≤ Z ω := fun ω =>
    max_le (by nlinarith [hY0 ω]) (hZ0 ω)
  set Kc : ℝ := τ⁻¹ * (N : ℝ) ^ 2 * (p * (2 * R * N) ^ (p + 3)) with hKc
  have hKc0 : 0 ≤ Kc := by rw [hKc]; positivity
  have hZW : ∀ ω, Z ω ≤ Kc * W ω ^ (p + 3) := by
    intro ω
    have hNn : (N : ℝ) ^ (-(3 : ℝ) / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hN1r (by norm_num)
    have hS0 : 0 ≤ ∑ i, ∑ μ, ‖Dm i μ (X ω)‖ :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hS : ∑ i, ∑ μ, ‖Dm i μ (X ω)‖ ≤
        (M : ℝ) * N * (p * (2 * R * N) ^ (p + 3) * W ω ^ (p + 3)) := by
      calc _ ≤ ∑ _i : Fin M, ∑ _μ : Fin N, (p * (2 * R * N) ^ (p + 3) * W ω ^ (p + 3)) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun μ _ => hDr i μ ω
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]; ring
    have hMN : (M : ℝ) * N ≤ τ⁻¹ * (N : ℝ) ^ 2 := by nlinarith
    have hW0 : 0 ≤ p * (2 * R * N) ^ (p + 3) * W ω ^ (p + 3) := by
      have := hW1 ω; positivity
    calc Z ω ≤ 1 * ∑ i, ∑ μ, ‖Dm i μ (X ω)‖ := mul_le_mul_of_nonneg_right hNn hS0
      _ ≤ (M : ℝ) * N * (p * (2 * R * N) ^ (p + 3) * W ω ^ (p + 3)) := by rw [one_mul]; exact hS
      _ ≤ τ⁻¹ * (N : ℝ) ^ 2 * (p * (2 * R * N) ^ (p + 3) * W ω ^ (p + 3)) :=
          mul_le_mul_of_nonneg_right hMN hW0
      _ = Kc * W ω ^ (p + 3) := by rw [hKc]; ring
  obtain ⟨hW2i, hW2⟩ := hA_moment_W hτ hX hN1 hM (2 * (p + 3))
  have hξ2bd : ∀ ω, ξ ω ^ 2 ≤ Kc ^ 2 * (1 + hA_sq (X ω)) ^ (2 * (p + 3)) := fun ω => by
    calc ξ ω ^ 2 ≤ Z ω ^ 2 := pow_le_pow_left₀ (hξ0 ω) (hξZ ω) 2
      _ ≤ (Kc * W ω ^ (p + 3)) ^ 2 := pow_le_pow_left₀ (hZ0 ω) (hZW ω) 2
      _ = Kc ^ 2 * (1 + hA_sq (X ω)) ^ (2 * (p + 3)) := by rw [hW]; ring
  have hξ2int : Integrable fun ω => ξ ω ^ 2 :=
    (hW2i.const_mul (Kc ^ 2)).mono' (hξmeas.pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hξ2bd ω)
  set Cc : ℝ := ((4 * p + 17 : ℕ) : ℝ) with hCc
  have hξ2le : ∫ ω, ξ ω ^ 2 ≤ (N : ℝ) ^ Cc := by
    have hKzN : Kz ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hNKz)
    calc ∫ ω, ξ ω ^ 2 ≤ ∫ ω, Kc ^ 2 * (1 + hA_sq (X ω)) ^ (2 * (p + 3)) :=
          integral_mono hξ2int (hW2i.const_mul _) hξ2bd
      _ = Kc ^ 2 * ∫ ω, (1 + hA_sq (X ω)) ^ (2 * (p + 3)) := integral_const_mul _ _
      _ ≤ Kc ^ 2 * (hA_KW τ C (2 * (p + 3)) * (N : ℝ) ^ (2 * (p + 3))) :=
          mul_le_mul_of_nonneg_left hW2 (by positivity)
      _ = Kz * (N : ℝ) ^ (4 * p + 16) := by
          rw [hKc, hKz, mul_pow (2 * R)]; ring
      _ ≤ (N : ℝ) * (N : ℝ) ^ (4 * p + 16) :=
          mul_le_mul_of_nonneg_right hKzN (by positivity)
      _ = (N : ℝ) ^ Cc := by rw [hCc, Real.rpow_natCast]; ring
  have hΓ : (N : ℝ) ^ (-Cc) ≤ K1 * (g * Ψ) ^ p := by
    have hτN : τ⁻¹ ^ p ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hNτ)
    have e1 : (N : ℝ) ^ (-Cc) = ((N : ℝ) ^ (4 * p + 17))⁻¹ := by
      rw [Real.rpow_neg hNp.le, hCc, Real.rpow_natCast]
    have h1 : (N : ℝ) ^ (p + 1) ≤ (N : ℝ) ^ (4 * p + 17) := pow_le_pow_right₀ hN1r (by omega)
    have h2 : (τ / N) ^ p ≤ Ψ ^ p := pow_le_pow_left₀ (by positivity) hΨτ p
    have h3 : Ψ ^ p ≤ (g * Ψ) ^ p := pow_le_pow_left₀ hΨ0 (le_mul_of_one_le_left hΨ0 hg1) p
    have h5 : (N : ℝ)⁻¹ ≤ τ ^ p := by
      have := inv_anti₀ (by positivity : (0 : ℝ) < τ⁻¹ ^ p) hτN
      rwa [inv_pow, inv_inv] at this
    have h4 : ((N : ℝ) ^ (p + 1))⁻¹ ≤ (τ / N) ^ p :=
      calc ((N : ℝ) ^ (p + 1))⁻¹ = (N : ℝ)⁻¹ * ((N : ℝ) ^ p)⁻¹ := by
            rw [pow_succ, mul_inv, mul_comm]
        _ ≤ τ ^ p * ((N : ℝ) ^ p)⁻¹ := mul_le_mul_of_nonneg_right h5 (by positivity)
        _ = (τ / N) ^ p := by rw [div_pow, div_eq_mul_inv]
    rw [e1]
    calc ((N : ℝ) ^ (4 * p + 17))⁻¹ ≤ ((N : ℝ) ^ (p + 1))⁻¹ := inv_anti₀ (by positivity) h1
      _ ≤ (g * Ψ) ^ p := h4.trans (h2.trans h3)
      _ ≤ K1 * (g * Ψ) ^ p := le_mul_of_one_le_left hgp0 hK1
  have hD : 3 * Cc ≤ DA - 4 := (hA_dPrev_ge p).trans (by linarith only [hDA'])
  have hint := integral_le_of_domAt hN1 le_rfl hD hΓ hξ0 hξ2int hξ2le hdom
  rw [Real.rpow_zero, mul_one] at hint
  -- assembly
  have hξint : Integrable ξ := by
    refine hZint.mono' hξmeas.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (hξ0 ω)]
    exact hξZ ω
  have hLHS : (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ,
      ‖∫ ω, ((∏ r, conjIf (cs r) (wordA Sig (X ω) z v i μ (ns r) (ws r))) -
        ∏ r, conjIf (cs r) (hatA Sig (X ω) z v i μ (ns r) (ws r)))‖ ≤ ∫ ω, Z ω := by
    rw [hZ, integral_const_mul, integral_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun μ _ => hDint i μ]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (Real.rpow_nonneg hNp.le _)
    rw [integral_finsetSum _ fun μ _ => hDint i μ]
    exact Finset.sum_le_sum fun μ _ => norm_integral_le_integral_norm _
  have hZle : ∫ ω, Z ω ≤ ∫ ω, (K1 * 2 ^ p * Y ω + ξ ω) :=
    integral_mono hZint ((hYint.const_mul _).add hξint) fun ω => by
      have := le_max_left (Z ω - K1 * 2 ^ p * Y ω) 0
      simp only [hξ] at this ⊢
      linarith
  have hmax0 := hA_maxFp_nonneg Sig X z v p
  have hYle : ∫ ω, Y ω ≤ 2 * maxFp Sig X z v p := by
    have hμint : ∀ μ : Fin N, Integrable fun ω =>
        vbar Sig v (Sum.inr μ) ^ 2 * Fv Sig (X ω) z (eI (Sum.inr μ)) ^ p := fun μ =>
      (hFv _ (hA_testNorm_eI (Sum.inr μ))).1.const_mul _
    rw [hY, integral_add (hFv v hv).1 (integrable_finsetSum _ fun μ _ => hμint μ),
      integral_finsetSum _ fun μ _ => hμint μ]
    have h1 : ∫ ω, Fv Sig (X ω) z v ^ p ≤ maxFp Sig X z v p := hA_maxFp_ge Sig X z v p none
    have h2 : ∑ μ, ∫ ω, vbar Sig v (Sum.inr μ) ^ 2 * Fv Sig (X ω) z (eI (Sum.inr μ)) ^ p ≤
        ∑ μ, vbar Sig v (Sum.inr μ) ^ 2 * maxFp Sig X z v p := by
      refine Finset.sum_le_sum fun μ _ => ?_
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hA_maxFp_ge Sig X z v p (some μ)) (sq_nonneg _)
    have h3 : ∑ μ, vbar Sig v (Sum.inr μ) ^ 2 * maxFp Sig X z v p ≤ maxFp Sig X z v p := by
      rw [← Finset.sum_mul]
      exact mul_le_of_le_one_left hmax0 (hA_sum_vbar_sq hv)
    linarith
  have e : ∫ ω, (K1 * 2 ^ p * Y ω + ξ ω) = K1 * 2 ^ p * (∫ ω, Y ω) + ∫ ω, ξ ω := by
    rw [integral_add (hYint.const_mul (K1 * 2 ^ p)) hξint, integral_const_mul]
  have hEZ : ∫ ω, Z ω ≤ K1 * 2 ^ p * (2 * maxFp Sig X z v p) + 2 * (K1 * (g * Ψ) ^ p) := by
    have := mul_le_mul_of_nonneg_left hYle hK2
    linarith [hZle, e, hint]
  refine hLHS.trans (hEZ.trans ?_)
  have h0 : 0 ≤ 2 * K1 * maxFp Sig X z v p + 2 * (K1 * 2 ^ p) * (g * Ψ) ^ p := by positivity
  calc K1 * 2 ^ p * (2 * maxFp Sig X z v p) + 2 * (K1 * (g * Ψ) ^ p)
      = (2 * K1 + 2 * (K1 * 2 ^ p)) * ((g * Ψ) ^ p + maxFp Sig X z v p) -
          (2 * K1 * maxFp Sig X z v p + 2 * (K1 * 2 ^ p) * (g * Ψ) ^ p) := by ring
    _ ≤ _ := sub_le_self _ h0

/-- Lemma 8.4 (`lem:76`): (sc_step 5) with `n = 3`, any conjugation pattern. -/
theorem sc_step5_three (τ c : ℝ) (C : ℕ → ℝ) (p : ℕ) (C₀ δ DA : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hc : 0 < c) (hp : Even p) (hp2 : 2 ≤ p) (hδ : 0 < δ) (hC₀ : czero τ ≤ C₀)
    (hC₀δ : C₀ * δ ≤ τ / 4) (hDA : dPrevTwo τ p ≤ DA) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (S : Set ℂ) (m : ℕ), CompSetting τ c M N Sig S → 1 ≤ m →
      PropA N C allModels Sig S C₀ δ (m - 1) (δ / 4) DA →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption C X →
        ∀ z ∈ levelSet N δ S m, ∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 →
          ∀ (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r)) (cs : Fin p → Bool), ∑ r, ns r = 3 →
            (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ,
              ‖∫ ω, ∏ r, conjIf (cs r) (wordA Sig (X ω) z v i μ (ns r) (ws r))‖ ≤
              K * (((N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z) ^ p + maxFp Sig X z v p) := by
  obtain ⟨K₅, hK₅, N₅, h₅⟩ := hatA_replace τ c C p C₀ δ DA hτ hτ1 hc hp hp2 hδ hC₀ hC₀δ hDA
  obtain ⟨K₈, hK₈, N₈, h₈⟩ := lem82 τ c C p C₀ δ DA hτ hτ1 hc hp hp2 hδ hC₀ hC₀δ hDA
  refine ⟨K₅ + 3 ^ (p + 3) * K₈, by positivity, max N₅ N₈, ?_⟩
  intro N hN M Sig S m hset hm hA Ω _ _ X hX z hz v hv ns ws cs hns
  have hNN₅ : N₅ ≤ N := le_trans (le_max_left _ _) hN
  have hNN₈ : N₈ ≤ N := le_trans (le_max_right _ _) hN
  have hzS : z ∈ S := hz.1
  have hη : 0 < z.im := (hset.domain.1 hzS).1
  have hSig := hset.sigma.posDef
  have hN1 := hA_N_pos hset
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
  have hM : (M : ℝ) ≤ τ⁻¹ * N := by
    have := hset.ratio_le
    rwa [div_le_iff₀ hNp] at this
  set b := ((N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z) ^ p + maxFp Sig X z v p with hb
  set T : Fin M → Fin N → (∀ r, Fin (ns r + 1) → Fin 3) → Matrix (Fin M) (Fin N) ℝ → ℂ :=
    fun i μ σs A => ((vbar Sig v (Sum.inr μ) : ℝ) : ℂ) ^ dVof σs *
      ∏ r, conjIf (cs r) (tagA Sig A z v i μ (ns r) (ws r) (σs r) *
        G Sig A z (Sum.inr μ) (Sum.inr μ) ^ tagMu (σs r)) with hT
  set D : Fin M → Fin N → Matrix (Fin M) (Fin N) ℝ → ℂ := fun i μ A =>
    (∏ r, conjIf (cs r) (wordA Sig A z v i μ (ns r) (ws r))) -
      ∏ r, conjIf (cs r) (hatA Sig A z v i μ (ns r) (ws r)) with hD
  have hIT : ∀ i μ σs, Integrable fun ω => T i μ σs (X ω) := fun i μ σs =>
    hA_PG_integrable hset.pos hX hN1 hM (hA_PG_mul (hA_PG_const _) (hA_PG_prod _ fun r _ =>
      hA_PG_conjIf _ (hA_PG_mul (hA_PG_tagA hSig hη v i μ _ _ _)
        (hA_PG_pow (hA_PG_G hSig hη _ _) _))))
  have hID : ∀ i μ, Integrable fun ω => D i μ (X ω) := fun i μ =>
    hA_PG_integrable hset.pos hX hN1 hM (hA_PG_sub
      (hA_PG_prod _ fun r _ => hA_PG_conjIf _ (hA_PG_wordA hSig hη v i μ _ _))
      (hA_PG_prod _ fun r _ => hA_PG_conjIf _ (hA_PG_hatA hSig hη v i μ _ _)))
  have hper : ∀ i μ, ‖∫ ω, ∏ r, conjIf (cs r) (wordA Sig (X ω) z v i μ (ns r) (ws r))‖ ≤
      ‖∫ ω, D i μ (X ω)‖ + ∑ σs, ‖∫ ω, T i μ σs (X ω)‖ := by
    intro i μ
    have e1 : (fun ω => ∏ r, conjIf (cs r) (wordA Sig (X ω) z v i μ (ns r) (ws r))) =
        fun ω => D i μ (X ω) + ∑ σs, T i μ σs (X ω) := by
      funext ω
      simp only [hD, hT]
      rw [← hA_prod_hatA hSig (X ω) hη v i μ ns ws cs]
      ring
    rw [e1, integral_add (hID i μ) (integrable_finsetSum _ fun σs _ => hIT i μ σs),
      integral_finsetSum _ fun σs _ => hIT i μ σs]
    exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
  have hcard : (Fintype.card (∀ r, Fin (ns r + 1) → Fin 3) : ℝ) = 3 ^ (p + 3) := by
    rw [Fintype.card_pi]
    simp only [Fintype.card_fun, Fintype.card_fin]
    rw [Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib, hns]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    push_cast
    ring
  have hb0 : 0 ≤ b := by
    have h1 := hA_maxFp_nonneg Sig X z v p
    have h2 := (hA_Psi_bounds hset hzS).2.2
    have h3 : 0 ≤ Psi N (specOf Sig) z := le_trans (by have := hset.pos; positivity) h2
    have h4 : 0 ≤ ((N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z) ^ p :=
      pow_nonneg (mul_nonneg (Real.rpow_nonneg hNp.le _) h3) p
    linarith
  have hNn0 : 0 ≤ (N : ℝ) ^ (-(3 : ℝ) / 2) := Real.rpow_nonneg hNp.le _
  have h5 := h₅ N hNN₅ M Sig S m hset hm hA Ω X hX z hz v hv ns ws cs hns
  have h8 : ∀ σs : (∀ r, Fin (ns r + 1) → Fin 3), (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ,
      ‖∫ ω, T i μ σs (X ω)‖ ≤ K₈ * b := fun σs =>
    h₈ N hNN₈ M Sig S m hset hm hA Ω X hX z hz v hv ns ws σs cs hns
  calc (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ,
        ‖∫ ω, ∏ r, conjIf (cs r) (wordA Sig (X ω) z v i μ (ns r) (ws r))‖
      ≤ (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ,
          (‖∫ ω, D i μ (X ω)‖ + ∑ σs, ‖∫ ω, T i μ σs (X ω)‖) := by
        gcongr with i _ μ _
        exact hper i μ
    _ = (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ, ‖∫ ω, D i μ (X ω)‖ +
          ∑ σs, (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ, ‖∫ ω, T i μ σs (X ω)‖ := by
        have e1 : ∑ i, ∑ μ, (‖∫ ω, D i μ (X ω)‖ + ∑ σs, ‖∫ ω, T i μ σs (X ω)‖) =
            ∑ i, ∑ μ, ‖∫ ω, D i μ (X ω)‖ + ∑ i, ∑ μ, ∑ σs, ‖∫ ω, T i μ σs (X ω)‖ := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib
        rw [e1, hA_sum_swap Finset.univ (fun i μ σs => ‖∫ ω, T i μ σs (X ω)‖), mul_add]
        congr 1
        exact Finset.mul_sum _ _ _
    _ ≤ K₅ * b + ∑ _σs : (∀ r, Fin (ns r + 1) → Fin 3), K₈ * b :=
        add_le_add h5 (Finset.sum_le_sum fun σs _ => h8 σs)
    _ = (K₅ + 3 ^ (p + 3) * K₈) * b := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
        ring

/-- Lemma 8.3 (`lem:73`): (sc_step 3) with `n = 3`, coefficient form. -/
theorem sc_step3_three (τ c : ℝ) (C : ℕ → ℝ) (p : ℕ) (C₀ δ DA : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hc : 0 < c) (hp : Even p) (hp2 : 2 ≤ p) (hδ : 0 < δ) (hC₀ : czero τ ≤ C₀)
    (hC₀δ : C₀ * δ ≤ τ / 4) (hDA : dPrevTwo τ p ≤ DA) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (S : Set ℂ) (m : ℕ), CompSetting τ c M N Sig S → 1 ≤ m →
      PropA N C allModels Sig S C₀ δ (m - 1) (δ / 4) DA →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption C X →
        ∀ z ∈ levelSet N δ S m, ∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 →
          (N : ℝ) ^ (-(3 : ℝ) / 2) *
            ∑ i, ∑ μ, ‖∫ ω, fCoeff p (resCoeff Sig (X ω) z v i μ) 3‖ ≤
              K * (((N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z) ^ p + maxFp Sig X z v p) := by
  obtain ⟨K₄, hK₄, N₄, h₄⟩ := sc_step5_three τ c C p C₀ δ DA hτ hτ1 hc hp hp2 hδ hC₀ hC₀δ hDA
  refine ⟨((Finset.Nat.antidiagonalTuple p 3).card : ℝ) * 8 * K₄, by positivity, N₄, ?_⟩
  intro N hN M Sig S m hset hm hA Ω _ _ X hX z hz v hv
  have hzS : z ∈ S := hz.1
  have hη : 0 < z.im := (hset.domain.1 hzS).1
  have hSig := hset.sigma.posDef
  have hN1 := hA_N_pos hset
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
  have hM : (M : ℝ) ≤ τ⁻¹ * N := by
    have := hset.ratio_le
    rwa [div_le_iff₀ hNp] at this
  set b := ((N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z) ^ p + maxFp Sig X z v p with hb
  set T := Finset.Nat.antidiagonalTuple p 3 with hTdef
  set cs : Fin p → Bool := fun r => !decide ((r : ℕ) < p / 2) with hcs
  set P : Fin M → Fin N → ∀ κ : Fin p → ℕ, (∀ r, Word (κ r)) → Matrix (Fin M) (Fin N) ℝ → ℂ :=
    fun i μ κ ws A => ∏ r, conjIf (cs r) (wordA Sig A z v i μ (κ r) (ws r)) with hP
  have hfc : ∀ i μ (A : Matrix (Fin M) (Fin N) ℝ), fCoeff p (resCoeff Sig A z v i μ) 3 =
      ∑ κ ∈ T, ∑ ws : (∀ r, Word (κ r)), (-1) * P i μ κ ws A := by
    intro i μ A
    unfold fCoeff
    refine Finset.sum_congr rfl fun κ hκ => ?_
    have hs : ∑ r, κ r = 3 := Finset.Nat.mem_antidiagonalTuple.1 hκ
    have h1 : ∀ r : Fin p, (if (r : ℕ) < p / 2 then resCoeff Sig A z v i μ (κ r)
        else starRingEnd ℂ (resCoeff Sig A z v i μ (κ r))) =
        (-1) ^ κ r * ∑ w : Word (κ r), conjIf (cs r) (wordA Sig A z v i μ (κ r) w) := by
      intro r
      rw [resCoeff_eq_sum_wordA hSig A hη v i μ (κ r)]
      by_cases h : (r : ℕ) < p / 2
      · simp [h, hcs, conjIf]
      · simp [h, hcs, conjIf, map_sum]
    simp only [h1]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hs, Fintype.prod_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ws _ => ?_
    simp only [hP]
    norm_num
  have hIP : ∀ i μ κ (ws : ∀ r, Word (κ r)), Integrable fun ω => P i μ κ ws (X ω) :=
    fun i μ κ ws => hA_PG_integrable hset.pos hX hN1 hM (hA_PG_prod _ fun r _ =>
      hA_PG_conjIf _ (hA_PG_wordA hSig hη v i μ _ _))
  have hper : ∀ i μ, ‖∫ ω, fCoeff p (resCoeff Sig (X ω) z v i μ) 3‖ ≤
      ∑ κ ∈ T, ∑ ws : (∀ r, Word (κ r)), ‖∫ ω, P i μ κ ws (X ω)‖ := by
    intro i μ
    simp only [hfc]
    rw [integral_finsetSum _ fun κ _ => integrable_finsetSum _ fun ws _ =>
      (hIP i μ κ ws).const_mul (-1)]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun κ _ => ?_)
    rw [integral_finsetSum _ fun ws _ => (hIP i μ κ ws).const_mul (-1)]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ws _ => ?_)
    rw [integral_const_mul, norm_mul, norm_neg, norm_one, one_mul]
  have hcardw : ∀ κ ∈ T, (Fintype.card (∀ r : Fin p, Word (κ r)) : ℝ) = 8 := by
    intro κ hκ
    have hs : ∑ r, κ r = 3 := Finset.Nat.mem_antidiagonalTuple.1 hκ
    rw [Fintype.card_pi]
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    rw [Finset.prod_pow_eq_pow_sum, hs]
    norm_num
  have hstep : ∀ κ ∈ T, ∀ ws : (∀ r : Fin p, Word (κ r)), (N : ℝ) ^ (-(3 : ℝ) / 2) *
      ∑ i, ∑ μ, ‖∫ ω, P i μ κ ws (X ω)‖ ≤ K₄ * b := fun κ hκ ws =>
    h₄ N hN M Sig S m hset hm hA Ω X hX z hz v hv κ ws cs (Finset.Nat.mem_antidiagonalTuple.1 hκ)
  calc (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ, ‖∫ ω, fCoeff p (resCoeff Sig (X ω) z v i μ) 3‖
      ≤ (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ, ∑ κ ∈ T, ∑ ws : (∀ r : Fin p, Word (κ r)),
          ‖∫ ω, P i μ κ ws (X ω)‖ := by
        gcongr with i _ μ _
        exact hper i μ
    _ = ∑ κ ∈ T, ∑ ws : (∀ r : Fin p, Word (κ r)), (N : ℝ) ^ (-(3 : ℝ) / 2) *
          ∑ i, ∑ μ, ‖∫ ω, P i μ κ ws (X ω)‖ := by
        rw [hA_sum_swap, Finset.mul_sum]
        refine Finset.sum_congr rfl fun κ _ => ?_
        rw [hA_sum_swap Finset.univ, Finset.mul_sum]
    _ ≤ ∑ κ ∈ T, ∑ _ws : (∀ r : Fin p, Word (κ r)), K₄ * b :=
        Finset.sum_le_sum fun κ hκ => Finset.sum_le_sum fun ws _ => hstep κ hκ ws
    _ = ∑ _κ ∈ T, 8 * (K₄ * b) := by
        refine Finset.sum_congr rfl fun κ hκ => ?_
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardw κ hκ]
    _ = (T.card : ℝ) * 8 * K₄ * b := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-! ### Instances -/

section Checks

/-- Lemma 8.5 at `τ = 1/2`, `c = 1`, `C_p = 2`, `p = 2`, `C₀ = C₀(1/2) = 4800`,
`δ = min(1, 1/2)/(4 C₀(1/2)) = 1/38400`, `D_A = D(1/2, 2)` and the word lengths `n = (3, 0)`
(one word with three pairs and one empty word, so `q = 1 < p`): the parameter hypotheses are
discharged and the model hypotheses stay binders of the conclusion. At `N = 2` the level
`N^{C₀δ} Ψ` exceeds `1`, so the bound is meaningful only for large `N`. -/
example : ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
    (S : Set ℂ) (m : ℕ), CompSetting (1 / 2) 1 M N Sig S → 1 ≤ m →
    PropA N (fun _ => 2) allModels Sig S (czero (1 / 2)) (deltaTwo 1 (1 / 2)) (m - 1)
      (deltaTwo 1 (1 / 2) / 4) (dPrevTwo (1 / 2) 2) →
    ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption (fun _ => 2) X →
      ∀ z ∈ levelSet N (deltaTwo 1 (1 / 2)) S m, ∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 →
        ∀ (ws : ∀ r, Word ((![3, 0] : Fin 2 → ℕ) r)) (cs : Fin 2 → Bool),
          (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ,
            ‖∫ ω, ((∏ r, conjIf (cs r) (wordA Sig (X ω) z v i μ ((![3, 0] : Fin 2 → ℕ) r) (ws r))) -
              ∏ r, conjIf (cs r) (hatA Sig (X ω) z v i μ ((![3, 0] : Fin 2 → ℕ) r) (ws r)))‖ ≤
            K * (((N : ℝ) ^ (czero (1 / 2) * deltaTwo 1 (1 / 2)) * Psi N (specOf Sig) z) ^ 2 +
              maxFp Sig X z v 2) := by
  have hc : czero (1 / 2) = 4800 := by norm_num [czero]
  have hd : deltaTwo 1 (1 / 2) = 1 / 38400 := by
    rw [deltaTwo, hc]; norm_num
  obtain ⟨K, hK, N₀, h⟩ := hatA_replace (1 / 2) 1 (fun _ => 2) 2 (czero (1 / 2))
    (deltaTwo 1 (1 / 2)) (dPrevTwo (1 / 2) 2) (by norm_num) (by norm_num) one_pos even_two le_rfl
    (by rw [hd]; norm_num) le_rfl (by rw [hc, hd]; norm_num) le_rfl
  exact ⟨K, hK, N₀, fun N hN M Sig S m h1 h2 h3 Ω _ _ X hX z hz v hv ws cs =>
    h N hN M Sig S m h1 h2 h3 Ω X hX z hz v hv _ ws cs (by simp)⟩

/-- Lemma 8.4 at the same parameters and word lengths `n = (3, 0)`; the model hypotheses stay
binders of the conclusion, which is meaningful only for large `N`. -/
example : ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
    (S : Set ℂ) (m : ℕ), CompSetting (1 / 2) 1 M N Sig S → 1 ≤ m →
    PropA N (fun _ => 2) allModels Sig S (czero (1 / 2)) (deltaTwo 1 (1 / 2)) (m - 1)
      (deltaTwo 1 (1 / 2) / 4) (dPrevTwo (1 / 2) 2) →
    ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption (fun _ => 2) X →
      ∀ z ∈ levelSet N (deltaTwo 1 (1 / 2)) S m, ∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 →
        ∀ (ws : ∀ r, Word ((![3, 0] : Fin 2 → ℕ) r)) (cs : Fin 2 → Bool),
          (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ,
            ‖∫ ω, ∏ r, conjIf (cs r) (wordA Sig (X ω) z v i μ ((![3, 0] : Fin 2 → ℕ) r) (ws r))‖ ≤
            K * (((N : ℝ) ^ (czero (1 / 2) * deltaTwo 1 (1 / 2)) * Psi N (specOf Sig) z) ^ 2 +
              maxFp Sig X z v 2) := by
  have hc : czero (1 / 2) = 4800 := by norm_num [czero]
  have hd : deltaTwo 1 (1 / 2) = 1 / 38400 := by
    rw [deltaTwo, hc]; norm_num
  obtain ⟨K, hK, N₀, h⟩ := sc_step5_three (1 / 2) 1 (fun _ => 2) 2 (czero (1 / 2))
    (deltaTwo 1 (1 / 2)) (dPrevTwo (1 / 2) 2) (by norm_num) (by norm_num) one_pos even_two le_rfl
    (by rw [hd]; norm_num) le_rfl (by rw [hc, hd]; norm_num) le_rfl
  exact ⟨K, hK, N₀, fun N hN M Sig S m h1 h2 h3 Ω _ _ X hX z hz v hv ws cs =>
    h N hN M Sig S m h1 h2 h3 Ω X hX z hz v hv _ ws cs (by simp)⟩

/-- Lemma 8.3 at the same parameters: the coefficient `f_3` of `F_v^2`; the model hypotheses stay
binders of the conclusion, which is meaningful only for large `N`. -/
example : ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
    (S : Set ℂ) (m : ℕ), CompSetting (1 / 2) 1 M N Sig S → 1 ≤ m →
    PropA N (fun _ => 2) allModels Sig S (czero (1 / 2)) (deltaTwo 1 (1 / 2)) (m - 1)
      (deltaTwo 1 (1 / 2) / 4) (dPrevTwo (1 / 2) 2) →
    ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption (fun _ => 2) X →
      ∀ z ∈ levelSet N (deltaTwo 1 (1 / 2)) S m, ∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 →
        (N : ℝ) ^ (-(3 : ℝ) / 2) *
          ∑ i, ∑ μ, ‖∫ ω, fCoeff 2 (resCoeff Sig (X ω) z v i μ) 3‖ ≤
            K * (((N : ℝ) ^ (czero (1 / 2) * deltaTwo 1 (1 / 2)) * Psi N (specOf Sig) z) ^ 2 +
              maxFp Sig X z v 2) := by
  have hc : czero (1 / 2) = 4800 := by norm_num [czero]
  have hd : deltaTwo 1 (1 / 2) = 1 / 38400 := by
    rw [deltaTwo, hc]; norm_num
  exact sc_step3_three (1 / 2) 1 (fun _ => 2) 2 (czero (1 / 2)) (deltaTwo 1 (1 / 2))
    (dPrevTwo (1 / 2) 2) (by norm_num) (by norm_num) one_pos even_two le_rfl
    (by rw [hd]; norm_num) le_rfl (by rw [hc, hd]; norm_num) le_rfl

end Checks

end Anisotropic
