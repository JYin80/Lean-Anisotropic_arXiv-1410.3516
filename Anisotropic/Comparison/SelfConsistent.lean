import Anisotropic.Comparison.WordBounds
import Anisotropic.Comparison.Taylor

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # (sc_step 6)–(sc_step 8), Lemma 7.17 -/

/-!
(sc_step 6)–(sc_step 8): for words `w_r` (`r < p`) with `n = ∑ n(w_r) ∈ [4, 4p]`, on the
intersection `Θ` of the events of Lemma 7.13 (a_priori_1) at the test vectors `v`, `Σ̲ e_a`, and of
(bound_sum_im), the entries of `G` and `F_v` are `O(N^{2δ+2ε_A})`, and (w_est), (w_est_2),
(w_est_1) with the pigeonhole principle give
`N^{−n/2} ∑_{iμ} ∏_r |A(w_r)| ≤ F_v^{p−q} (N^{C₀δ} Ψ)^q ≤ F_v^p + (N^{C₀δ} Ψ)^p`
(`q` the number of nonempty words, Young's inequality). Off `Θ`, Lemma 7.7 with the rough bound
(A_rough) bounds the excess over `F_v^p` by `2 (N^{C₀δ} Ψ)^p`.
Lemma 7.17: `f_n = ∑_{κ} ∏_r a_{κ_r}` (Leibniz) with `a_k = (−1)^k ∑_{w ∈ 𝒲_k} A(w)`.
-/

/-! ## Bilinear forms of `G`, `Σ̲` and `Π` -/

private theorem scR_ent_sub {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (v w : ι → ℝ) :
    ent (A - B) v w = ent A v w - ent B v w := by
  simp [ent, sub_mulVec, dotProduct_sub]

private theorem scR_ent_eq {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (x y : ι → ℝ) :
    ent A x y = ∑ s, ∑ t, (x s : ℂ) * A s t * (y t : ℂ) := by
  simp only [ent, cvec, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

private theorem scR_ent_transpose {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (x y : ι → ℝ) :
    ent Aᵀ x y = ent A y x := by
  rw [scR_ent_eq, scR_ent_eq, Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
    simp only [transpose_apply]; ring

private theorem scR_ent_eI_right {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (x : ι → ℝ) (r : ι) : ent A x (eI r) = ∑ s, (x s : ℂ) * A s r := by
  rw [scR_ent_eq]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [eI, Pi.single_apply, apply_ite]

private theorem scR_diag {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) :
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

private theorem scR_sum_sq_UT {K : ℕ} {U : Matrix (Fin K) (Fin K) ℝ} (h₂ : U * Uᵀ = 1)
    (x : Fin K → ℝ) : ∑ i, (Uᵀ *ᵥ x) i ^ 2 = ∑ i, x i ^ 2 := by
  have e : (Uᵀ *ᵥ x) ⬝ᵥ (Uᵀ *ᵥ x) = x ⬝ᵥ x := by
    rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, h₂, one_mulVec, dotProduct_comm]
  simpa [dotProduct, sq] using e

private theorem scR_row_sq {K : ℕ} {U : Matrix (Fin K) (Fin K) ℝ} (h₂ : U * Uᵀ = 1) (i : Fin K) :
    ∑ k, U i k ^ 2 = 1 := by
  have := congrFun (congrFun h₂ i) i
  simpa [Matrix.mul_apply, sq, Matrix.one_apply] using this

/-- `|Σ x|² ≤ τ⁻² |x|²` under (bound_Sigma). -/
private theorem scR_sumsq_Sig {τ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hS : SigmaAssumption τ Sig) (x : Fin M → ℝ) :
    ∑ l, (Sig *ᵥ x) l ^ 2 ≤ τ⁻¹ ^ 2 * ∑ l, x l ^ 2 := by
  obtain ⟨U, h₂, h₁, hSd, hσ⟩ := scR_diag hS.posDef
  have hle : ∀ k, specOf Sig k ≤ τ⁻¹ := fun k => by
    rw [specOf_eq hS.posDef.isHermitian]; exact hS.eigenvalues_le k
  have hUU : Uᵀ * Uᵀᵀ = 1 := by rw [transpose_transpose]; exact h₁
  have e : Sig *ᵥ x = Uᵀᵀ *ᵥ (diagonal (specOf Sig) *ᵥ (Uᵀ *ᵥ x)) := by
    rw [transpose_transpose, mulVec_mulVec, mulVec_mulVec]
    exact congrArg (· *ᵥ x) hSd
  rw [e, scR_sum_sq_UT hUU, ← scR_sum_sq_UT h₂ x, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [mulVec_diagonal, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hσ k).le (hle k) 2) (sq_nonneg _)

/-- `|Σ̲ y| ≤ τ⁻¹ |y|`. -/
private theorem scR_testNorm_SigU {τ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hS : SigmaAssumption τ Sig) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (y : Fin M ⊕ Fin N → ℝ) :
    testNorm (SigU (n := Fin N) Sig *ᵥ y) ≤ τ⁻¹ * testNorm y := by
  have hτi : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  have h1 := scR_sumsq_Sig hS (y ∘ Sum.inl)
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
private theorem scR_vbar_SigU {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (y : Fin M ⊕ Fin N → ℝ) : vbar Sig (SigU (n := Fin N) Sig *ᵥ y) = y := by
  have hS : Sig⁻¹ * Sig = 1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hSig.isUnit)
  funext s
  rcases s with j | ν
  · simp [vbar, SigU, fromBlocks_mulVec, mulVec_mulVec, hS]
  · simp [vbar, SigU, fromBlocks_mulVec]

/-- `(1 + wΣ)⁻¹_{li} = ∑ₖ U_{lk} (1 + σₖ w)⁻¹ U_{ik}`. -/
private theorem scR_cinv_entry {Sig U : Matrix (Fin M) (Fin M) ℝ} {σ : Fin M → ℝ}
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

private theorem scR_abs_le_testNorm {ι : Type*} [Fintype ι] (x : ι → ℝ) (s : ι) :
    |x s| ≤ testNorm x := by
  unfold testNorm
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (fun t _ => sq_nonneg (x t)) (Finset.mem_univ s))

private theorem scR_sqrt_inl_le (x : Fin M ⊕ Fin N → ℝ) :
    √(∑ j, x (Sum.inl j) ^ 2) ≤ testNorm x := by
  unfold testNorm
  refine Real.sqrt_le_sqrt ?_
  rw [Fintype.sum_sum_type]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- `|⟨v̄, Π e_p⟩| ≤ max(c⁻¹, K) |v|` when `|m| ≤ K` and `|1 + σᵢ m| ≥ c`. -/
private theorem scR_pi_bound {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {c K : ℝ}
    (hc : 0 < c) {w : ℂ} (hwK : ‖w‖ ≤ K) (hOne : ∀ i, c ≤ ‖1 + (specOf Sig i : ℂ) * w‖)
    (x : Fin M ⊕ Fin N → ℝ) (p : Fin M ⊕ Fin N) :
    ‖ent (piMat (N := N) Sig w) (vbar Sig x) (eI p)‖ ≤ max c⁻¹ K * testNorm x := by
  rw [scR_ent_eI_right, Fintype.sum_sum_type]
  rcases p with i | μ
  · simp only [piMat, fromBlocks_apply₁₁, fromBlocks_apply₂₁, Matrix.zero_apply, mul_zero,
      Finset.sum_const_zero, add_zero, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib, norm_neg]
    obtain ⟨U, h₂, h₁, hSd, hσ⟩ := scR_diag hSig
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
      simp only [scR_cinv_entry h₂ h₁ hSd hw0, Finset.mul_sum]
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
    rw [scR_sum_sq_UT h₂, scR_row_sq h₂, Real.sqrt_one, mul_one] at hcs
    have hc0 : 0 ≤ c⁻¹ := (inv_pos.2 hc).le
    calc _ ≤ ∑ k, c⁻¹ * (|(Uᵀ *ᵥ xM) k| * |U i k|) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => hb k)
      _ ≤ c⁻¹ * √(∑ j, xM j ^ 2) := by
          rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hcs hc0
      _ ≤ max c⁻¹ K * testNorm x :=
          mul_le_mul (le_max_left _ _) (scR_sqrt_inl_le x) (Real.sqrt_nonneg _)
            (hc0.trans (le_max_left _ _))
  · simp only [piMat, fromBlocks_apply₁₂, fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero,
      Finset.sum_const_zero, zero_add, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
      mul_one, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [vbar, Sum.elim_inr, Function.comp_apply]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul (hwK.trans (le_max_right _ _)) (scR_abs_le_testNorm x _) (abs_nonneg _)
      ((norm_nonneg w).trans (hwK.trans (le_max_right _ _)))

/-- `|⟨v̄, G e_p⟩| ≤ |⟨v, Σ̲⁻¹(G − Π)Σ̲⁻¹ (Σ̲ e_p)⟩| + max(c⁻¹, K) |v|`. -/
private theorem scR_G_left {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {c K : ℝ}
    (hc : 0 < c) {z : ℂ} (hwK : ‖mFun N (specOf Sig) z‖ ≤ K)
    (hOne : ∀ i, c ≤ ‖1 + (specOf Sig i : ℂ) * mFun N (specOf Sig) z‖)
    (A : Matrix (Fin M) (Fin N) ℝ) (x : Fin M ⊕ Fin N → ℝ) (p : Fin M ⊕ Fin N) :
    ‖ent (G Sig A z) (vbar Sig x) (eI p)‖ ≤
      ‖testBilin x (lawMat Sig A z) (SigU (n := Fin N) Sig *ᵥ eI p)‖ + max c⁻¹ K * testNorm x := by
  have e : ent (G Sig A z) (vbar Sig x) (eI p) =
      ent (G Sig A z - PiZ N Sig z) (vbar Sig x) (vbar Sig (SigU (n := Fin N) Sig *ᵥ eI p)) +
        ent (PiZ N Sig z) (vbar Sig x) (eI p) := by
    rw [scR_vbar_SigU hSig, scR_ent_sub]; ring
  rw [e, ent_vbar_eq_testBilin hSig]
  exact (norm_add_le _ _).trans (add_le_add le_rfl (scR_pi_bound hSig hc hwK hOne x p))

/-- The setting of §7 gives the density assumptions on the eigenvalues of `Σ`. -/
private theorem scR_density {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) : DensityAssumptions τ N (specOf Sig) :=
  (IsModel.diagModel_specOf (Ω := GaussSpace M N)
    ⟨hset.ratio_ge, hset.ratio_le, (gaussX_isGaussianEnsemble M N).entryAssumption hN,
      hset.sigma⟩).densityAssumptions hset.pos

private theorem scR_testNorm_eI {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι) :
    testNorm (eI p) = 1 := by
  unfold testNorm
  simp [eI, Pi.single_apply, Finset.sum_ite_eq']

/-- `1 ≤ M` and `1 ≤ N` in the setting of §7 (from `τ ≤ M/N`). -/
private theorem sc_N_pos {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) : 1 ≤ N := by
  by_contra h
  have h0 : N = 0 := by omega
  have := hset.ratio_ge
  rw [h0] at this
  simp at this
  linarith [hset.pos]

/-! ## Continuity in the matrix -/

private theorem sc_continuous_G {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {z : ℂ}
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

private theorem sc_continuous_ent {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    Continuous fun B : Matrix ι ι ℂ => ent B x y := by
  have : (fun B : Matrix ι ι ℂ => ent B x y) =
      fun B => ∑ s, ∑ t, (x s : ℂ) * B s t * (y t : ℂ) := funext fun B => scR_ent_eq B x y
  rw [this]
  exact continuous_finsetSum _ fun s _ => continuous_finsetSum _ fun t _ =>
    (continuous_const.mul (continuous_id.matrix_elem s t)).mul continuous_const

private theorem sc_continuous_wordA {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {z : ℂ}
    (hz : 0 < z.im) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) (k : ℕ) (w : Word k) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => wordA Sig A z v i μ k w := by
  have hG := sc_continuous_G (N := N) hSig hz
  cases k with
  | zero =>
    simp only [wordA]
    exact (sc_continuous_ent _ _).comp (hG.sub continuous_const)
  | succ k =>
    simp only [wordA]
    refine (((sc_continuous_ent _ _).comp hG).mul ?_).mul ((sc_continuous_ent _ _).comp hG)
    exact continuous_finsetProd _ fun l _ => hG.matrix_elem _ _

private theorem sc_continuous_Fv {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {z : ℂ}
    (hz : 0 < z.im) (v : Fin M ⊕ Fin N → ℝ) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => Fv Sig A z v := by
  unfold Fv
  exact ((sc_continuous_ent _ _).comp ((sc_continuous_G (N := N) hSig hz).sub
    continuous_const)).norm

/-! ## Rough moments -/

/-- `‖A‖_F² = ∑_{jν} A_{jν}²`. -/
private def scSq (A : Matrix (Fin M) (Fin N) ℝ) : ℝ := ∑ α : Fin M × Fin N, A α.1 α.2 ^ 2

private theorem scSq_nonneg (A : Matrix (Fin M) (Fin N) ℝ) : 0 ≤ scSq A :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem sc_continuous_scSq : Continuous fun A : Matrix (Fin M) (Fin N) ℝ => scSq A := by
  unfold scSq
  exact continuous_finsetSum _ fun α _ => ((continuous_id.matrix_elem α.1 α.2).pow 2)

/-- The `L²` operator norm is at most the Frobenius norm. -/
private theorem sc_opNorm_le {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
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
private theorem sc_XtX_le (A : Matrix (Fin M) (Fin N) ℝ) : ‖Aᵀ * A‖ ≤ scSq A := by
  have h1 : ‖Aᵀ * A‖ = ‖A‖ * ‖A‖ := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact l2_opNorm_conjTranspose_mul_self A
  have h2 := sc_opNorm_le A
  have h0 : 0 ≤ ∑ i, ∑ j, A i j ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [h1, scSq, Fintype.sum_prod_type]
  calc ‖A‖ * ‖A‖ ≤ Real.sqrt (∑ i, ∑ j, A i j ^ 2) * Real.sqrt (∑ i, ∑ j, A i j ^ 2) :=
        mul_le_mul h2 h2 (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := Real.mul_self_sqrt h0

/-- The moment constant `2^q (1 + τ^{−q} C'_{2q})`. -/
private def scKW (τ : ℝ) (C : ℕ → ℝ) (q : ℕ) : ℝ := 2 ^ q * (1 + τ⁻¹ ^ q * max (C (2 * q)) 0)

private theorem scKW_nonneg {τ : ℝ} (hτ : 0 < τ) (C : ℕ → ℝ) (q : ℕ) : 0 ≤ scKW τ C q := by
  unfold scKW
  have : 0 ≤ max (C (2 * q)) 0 := le_max_right _ _
  positivity

private theorem sc_measurable_X {Ω : Type*} [MeasureSpace Ω] {C : ℕ → ℝ}
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) : Measurable X :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun μ => hX.measurable i μ

/-- Moments of `W = 1 + ‖X‖_F²`: `E W^q ≤ 2^q (1 + τ^{−q} C'_{2q}) N^q`. -/
private theorem sc_moment_W {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {τ : ℝ} (hτ : 0 < τ) {C : ℕ → ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ}
    (hX : EntryAssumption C X) (hN : 1 ≤ N) (hM : (M : ℝ) ≤ τ⁻¹ * N) (q : ℕ) :
    Integrable (fun ω => (1 + scSq (X ω)) ^ q) ∧
      ∫ ω, (1 + scSq (X ω)) ^ q ≤ scKW τ C q * (N : ℝ) ^ q := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · refine ⟨by simp, ?_⟩
    simp only [pow_zero, integral_const, probReal_univ, smul_eq_mul, mul_one]
    unfold scKW
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
  have hle : ∀ ω, (1 + scSq (X ω)) ^ (n + 1) ≤ g ω := by
    intro ω
    have h1 := add_pow_le zero_le_one (scSq_nonneg (X ω)) (n + 1)
    have h2 : scSq (X ω) ^ (n + 1) ≤ cd ^ n * ∑ α : Fin M × Fin N, (X ω α.1 α.2 ^ 2) ^ (n + 1) :=
      pow_sum_le_card_mul_sum_pow (fun _ _ => sq_nonneg _) n
    simp only [Nat.add_sub_cancel, one_pow] at h1
    calc _ ≤ _ := h1
      _ ≤ g ω := by
          simp only [hg]
          gcongr
  have hmeas : Measurable fun ω => (1 + scSq (X ω)) ^ (n + 1) :=
    ((measurable_const.add (sc_continuous_scSq.measurable.comp (sc_measurable_X hX))).pow_const _)
  have hWi : Integrable fun ω => (1 + scSq (X ω)) ^ (n + 1) :=
    hgi.mono' hmeas.aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (by have := scSq_nonneg (X ω); positivity)]; exact hle ω)
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
  calc ∫ ω, (1 + scSq (X ω)) ^ (n + 1) ≤ ∫ ω, g ω := integral_mono hWi hgi hle
    _ ≤ 2 ^ n * (1 + τ⁻¹ ^ (n + 1) * C' * (N : ℝ) ^ (n + 1)) := by
        rw [hgval]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have := mul_le_mul_of_nonneg_left hsum (pow_nonneg hcd0 n)
        rw [hM1] at this
        linarith
    _ ≤ scKW τ C (n + 1) * (N : ℝ) ^ (n + 1) := by
        unfold scKW
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
private theorem sc_one_le_N_im {τ : ℝ} {z : ℂ} (hN : 1 ≤ N) (hτ : 0 < τ)
    (hz : z ∈ specDomain τ N) : 1 ≤ (N : ℝ) * z.im := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have h1 : (N : ℝ) * (N : ℝ) ^ (-1 + τ) = (N : ℝ) ^ τ := by
    rw [mul_comm, ← Real.rpow_add_one hNp.ne']; ring_nf
  have h2 : 1 ≤ (N : ℝ) ^ τ := Real.one_le_rpow hN1r hτ.le
  calc (1 : ℝ) ≤ (N : ℝ) ^ τ := h2
    _ = (N : ℝ) * (N : ℝ) ^ (-1 + τ) := h1.symm
    _ ≤ (N : ℝ) * z.im := mul_le_mul_of_nonneg_left hz.2.2.2.1 hNp.le

private theorem sc_roughConst_ge {τ c : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hc : 0 < c) :
    1 ≤ roughConst τ c := by
  unfold roughConst
  have hT : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  have hK : 0 ≤ mBoundConst τ * max c⁻¹ 1 := by
    have : 0 < mBoundConst τ := by unfold mBoundConst genPropConst; positivity
    positivity
  have h3 : 1 ≤ τ⁻¹ ^ 3 := one_le_pow₀ hT
  nlinarith

/-- (A_rough) with `η ≥ N⁻¹` and `‖XᵀX‖ ≤ ‖X‖_F²`. -/
private theorem sc_wordA_rough {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) {z : ℂ} (hz : z ∈ S) (A : Matrix (Fin M) (Fin N) ℝ)
    (v : Fin M ⊕ Fin N → ℝ) (hv : testNorm v = 1) (i : Fin M) (μ : Fin N) (k : ℕ)
    (w : Word k) :
    ‖wordA Sig A z v i μ k w‖ ≤ (roughConst τ c * N * (1 + scSq A)) ^ (k + 1) := by
  refine (norm_wordA_rough hset hz A v hv i μ k w).trans (pow_le_pow_left₀ ?_ ?_ _)
  · have h1 : 0 ≤ roughConst τ c :=
      zero_le_one.trans (sc_roughConst_ge hset.pos hset.le_one hset.c_pos)
    have h2 : 0 < z.im := (hset.domain.1 hz).1
    positivity
  · have hzD := hset.domain.1 hz
    have hη : 0 < z.im := hzD.1
    have hNη := sc_one_le_N_im (sc_N_pos hset) hset.pos hzD
    have hR := zero_le_one.trans (sc_roughConst_ge hset.pos hset.le_one hset.c_pos)
    have h1 : (1 + ‖Aᵀ * A‖) / z.im ≤ N * (1 + scSq A) := by
      rw [div_le_iff₀ hη]
      have := sc_XtX_le A
      have h0 : 0 ≤ 1 + ‖Aᵀ * A‖ := by positivity
      nlinarith
    rw [mul_div_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left h1 hR

/-- `∏_r |A(w_r)| ≤ (K N W)^{5p}` for `∑ n(w_r) ≤ 4p`, `W = 1 + ‖X‖_F²`. -/
private theorem sc_prod_rough {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) {z : ℂ} (hz : z ∈ S) (A : Matrix (Fin M) (Fin N) ℝ)
    (v : Fin M ⊕ Fin N → ℝ) (hv : testNorm v = 1) (i : Fin M) (μ : Fin N) {p : ℕ}
    (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r)) (hn : ∑ r, ns r ≤ 4 * p) :
    ∏ r, ‖wordA Sig A z v i μ (ns r) (ws r)‖ ≤ (roughConst τ c * N * (1 + scSq A)) ^ (5 * p) := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast sc_N_pos hset
  have hR1 : 1 ≤ roughConst τ c * N * (1 + scSq A) := by
    have hR := sc_roughConst_ge hset.pos hset.le_one hset.c_pos
    have hs := scSq_nonneg A
    have h1 : 1 ≤ roughConst τ c * N := one_le_mul_of_one_le_of_one_le hR hN1r
    nlinarith
  calc ∏ r, ‖wordA Sig A z v i μ (ns r) (ws r)‖
      ≤ ∏ r, (roughConst τ c * N * (1 + scSq A)) ^ (ns r + 1) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun r _ =>
          sc_wordA_rough hset hz A v hv i μ _ _
    _ = (roughConst τ c * N * (1 + scSq A)) ^ (∑ r, (ns r + 1)) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ _ := by
        refine pow_le_pow_right₀ hR1 ?_
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
        omega

/-- Integrability of `∏_r |A(w_r)|`. -/
private theorem sc_integrable_prod {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {τ c : ℝ} {C : ℕ → ℝ}
    {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ} (hset : CompSetting τ c M N Sig S) {z : ℂ}
    (hz : z ∈ S) {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X)
    (v : Fin M ⊕ Fin N → ℝ) (hv : testNorm v = 1) (i : Fin M) (μ : Fin N) {p : ℕ}
    (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r)) (hn : ∑ r, ns r ≤ 4 * p) :
    Integrable fun ω => ∏ r, ‖wordA Sig (X ω) z v i μ (ns r) (ws r)‖ := by
  have hN := sc_N_pos hset
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hM : (M : ℝ) ≤ τ⁻¹ * N := by
    have := hset.ratio_le
    rwa [div_le_iff₀ hNp] at this
  have hη : 0 < z.im := (hset.domain.1 hz).1
  have hW := (sc_moment_W hset.pos hX hN hM (5 * p)).1
  have hmeas : Measurable fun ω => ∏ r, ‖wordA Sig (X ω) z v i μ (ns r) (ws r)‖ := by
    refine Finset.measurable_prod _ fun r _ => ?_
    exact ((sc_continuous_wordA hset.sigma.posDef hη v i μ _ _).norm.measurable).comp
      (sc_measurable_X hX)
  refine (hW.const_mul ((roughConst τ c * N) ^ (5 * p))).mono' hmeas.aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  rw [Real.norm_of_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _), ← mul_pow]
  exact sc_prod_rough hset hz (X ω) v hv i μ ns ws hn

/-! ## The event `Θ` -/

/-- The constant `Q₀ = τ⁻² + κ τ⁻¹ + κ + 1`, `κ = max(c⁻¹, K_m)`, of the entry bounds. -/
private def scQ0 (τ c : ℝ) : ℝ :=
  τ⁻¹ ^ 2 + max c⁻¹ (mBoundConst τ) * τ⁻¹ + max c⁻¹ (mBoundConst τ) + 1

private theorem scQ0_ge {τ c : ℝ} (hτ : 0 < τ) (hc : 0 < c) : 1 ≤ scQ0 τ c := by
  unfold scQ0
  have hκ : 0 ≤ max c⁻¹ (mBoundConst τ) := (inv_pos.2 hc).le.trans (le_max_left _ _)
  have : 0 ≤ max c⁻¹ (mBoundConst τ) * τ⁻¹ := mul_nonneg hκ (inv_pos.2 hτ).le
  nlinarith [sq_nonneg τ⁻¹]

private theorem sc_le_rpow {K a : ℝ} (hK : 0 ≤ K) (ha : 0 < a) {N : ℕ}
    (hN : ⌈K ^ a⁻¹⌉₊ ≤ N) : K ≤ (N : ℝ) ^ a := by
  have h1 : K ^ a⁻¹ ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  calc K = (K ^ a⁻¹) ^ a := by rw [← Real.rpow_mul hK, inv_mul_cancel₀ ha.ne', Real.rpow_one]
    _ ≤ (N : ℝ) ^ a := Real.rpow_le_rpow (by positivity) h1 ha.le

private theorem sc_hp_mono {Ω : Type*} [MeasureSpace Ω] {N : ℕ} {D : ℝ} {A B : Set Ω}
    (h : A ⊆ B) (hA : HighProbAt N D A) : HighProbAt N D B :=
  (measure_mono (Set.compl_subset_compl.2 h)).trans hA

private theorem sc_hp_of_dom {Ω : Type*} [MeasureSpace Ω] {N : ℕ} {ε D : ℝ} {ξ ζ : Ω → ℝ}
    (h : DomAt N ε D ξ ζ) : HighProbAt N D {ω | ξ ω ≤ (N : ℝ) ^ ε * ζ ω} := by
  unfold HighProbAt
  refine le_trans (measure_mono fun ω hω => ?_) h
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω
  exact hω

/-- The event `Θ` of (sc_step 6): Lemma 7.13 (a_priori_1) at the test vectors `v`, `Σ̲ e_a` and
(bound_sum_im), at level `2 ε_A`, give `F_v, |G_{v̄a}|, |G_{av̄}|, |G_{ab}| ≤ N^{2δ+2ε_A} Q₀` and
`N⁻¹ ∑_i R_i² + N⁻¹ ∑_μ R_μ² ≤ N^{2ε_A} N^{(C₀+2)δ} Ψ²` with probability `≥ 1 − N^{−(D_A−4)}`. -/
private theorem sc_event (τ c : ℝ) (C : ℕ → ℝ) (C₀ δ εA DA : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hc : 0 < c) (hδ : 0 < δ) (hC₀ : 25 ≤ C₀) (hC₀δ : C₀ * δ ≤ τ / 4) (hεA : 0 < εA) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ)
      (P : ModelClass M N) (m : ℕ), CompSetting τ c M N Sig S → 1 ≤ m →
      PropA N C P Sig S C₀ δ (m - 1) εA DA →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption C X → P Ω X →
        ∀ z ∈ levelSet N δ S m, ∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 →
          HighProbAt N (DA - 4) {ω |
            Fv Sig (X ω) z v ≤ (N : ℝ) ^ (2 * εA) * (N : ℝ) ^ (2 * δ) * scQ0 τ c ∧
            (∀ a, ‖ent (G Sig (X ω) z) (vbar Sig v) (eI a)‖ ≤
              (N : ℝ) ^ (2 * εA) * (N : ℝ) ^ (2 * δ) * scQ0 τ c) ∧
            (∀ a, ‖ent (G Sig (X ω) z) (eI a) (vbar Sig v)‖ ≤
              (N : ℝ) ^ (2 * εA) * (N : ℝ) ^ (2 * δ) * scQ0 τ c) ∧
            (∀ a b, ‖G Sig (X ω) z a b‖ ≤ (N : ℝ) ^ (2 * εA) * (N : ℝ) ^ (2 * δ) * scQ0 τ c) ∧
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
    · exact sc_hp_of_dom ((h₁ N hNN₁ M Sig S P m hset hm hA Ω X hX hP z hz).1 (L j) (L k))
    · exact sc_hp_of_dom (h₂ N hNN₂ M Sig S P m hset hm hA Ω X hX hP z hz v hv)
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
  refine sc_hp_mono (fun ω hω => ?_) hall
  have hω' : ∀ ι, ω ∈ Ev ι := fun ι => Set.mem_iInter₂.1 hω ι (Finset.mem_univ _)
  have hSig := hset.sigma.posDef
  have hzS : z ∈ S := hz.1
  have hzD := hset.domain.1 hzS
  have hη : 0 < z.im := hzD.1
  have hmK := (gen_prop_m_specDomain (scR_density hset hN1) hzD).2.1
  have hOne := hset.oneXm z hzS
  have hE1 : 1 ≤ E := one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hN1r (by linarith))
    (Real.one_le_rpow hN1r (by linarith))
  have hE0 : 0 ≤ E := by linarith
  have hu : ∀ a, testNorm (SigU (n := Fin N) Sig *ᵥ eI a) ≤ τ⁻¹ := fun a => by
    have := scR_testNorm_SigU (N := N) hset.sigma hτ hτ1 (eI a)
    rwa [scR_testNorm_eI, mul_one] at this
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
  set B : ℝ := E * scQ0 τ c with hB
  have key : ∀ (x : Fin M ⊕ Fin N → ℝ) (q : Fin M ⊕ Fin N), testNorm x ≤ τ⁻¹ →
      ‖testBilin x (lawMat Sig (X ω) z) (SigU (n := Fin N) Sig *ᵥ eI q)‖ ≤ E * τ⁻¹ * τ⁻¹ →
      ‖ent (G Sig (X ω) z) (vbar Sig x) (eI q)‖ ≤ B := by
    intro x q hx hxq
    refine (scR_G_left hSig hc hmK hOne (X ω) x q).trans ?_
    have h1 : κ * testNorm x ≤ κ * τ⁻¹ := mul_le_mul_of_nonneg_left hx hκ0
    have h2 : κ * τ⁻¹ ≤ E * (κ * τ⁻¹) := le_mul_of_one_le_left (mul_nonneg hκ0 hT0) hE1
    have h3 : 0 ≤ E * κ + E := by positivity
    rw [hB, scQ0, ← hκ]
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
          rw [hB, scQ0, ← hκ]
          have : 0 ≤ E * (κ * τ⁻¹ + κ + 1) := by positivity
          nlinarith
  · rw [← scR_ent_transpose, G_transpose hSig (X ω) hη]
    exact hva a
  · rw [← ent_eI_eI (G Sig (X ω) z) a b, ← scR_vbar_SigU (N := N) hSig (eI a)]
    refine key _ b (hu a) ?_
    have := hbil (some a) (some b)
    rwa [hLs, hLs] at this

/-! ## Exponent arithmetic of (sc_step 6)–(sc_step 8) -/

/-- Case `n(w) ≥ q + 2`, `n = n' + 4`: with `s = N^{−1/2} ≤ k₀ Ψ`, `d = N^δ`, `e = N^{ε_A}`,
`e⁴ ≤ d`, `d^{25} ≤ g = N^{C₀δ}`, `g Ψ ≤ 1` and the constant at most `d`:
`s^{n'} c₁ (e² g d² Ψ²) (e² d² Q₀)^{n+q−2} ≤ (g Ψ)^q`. -/
private theorem sc_arithA {n' q : ℕ} (hq : q ≤ n' + 2) {si Ψ g d e Q₀ c₁ k₀ : ℝ}
    (hsi0 : 0 ≤ si) (hΨ : 0 ≤ Ψ) (hg0 : 0 ≤ g) (hd1 : 1 ≤ d) (he1 : 1 ≤ e) (hQ₀ : 0 ≤ Q₀)
    (hc₁ : 0 ≤ c₁) (hsi : si ≤ k₀ * Ψ) (hg : d ^ 25 ≤ g) (he : e ^ 4 ≤ d)
    (hgΨ : g * Ψ ≤ 1) (hK : c₁ * k₀ ^ n' * Q₀ ^ (n' + q + 2) ≤ d) :
    si ^ n' * c₁ * (e ^ 2 * (g * d ^ 2) * Ψ ^ 2) * (e ^ 2 * d ^ 2 * Q₀) ^ (n' + q + 2) ≤
      (g * Ψ) ^ q := by
  have hd0 : 0 ≤ d := by linarith
  have he0 : 0 ≤ e := by linarith
  have h1 : si ^ n' ≤ k₀ ^ n' * Ψ ^ n' := by rw [← mul_pow]; exact pow_le_pow_left₀ hsi0 hsi n'
  have h2 : e ^ (2 * (n' + q + 2) + 2) ≤ d ^ (n' + q + 3) := by
    calc e ^ (2 * (n' + q + 2) + 2) ≤ e ^ (4 * (n' + q + 3)) := pow_le_pow_right₀ he1 (by omega)
      _ = (e ^ 4) ^ (n' + q + 3) := by rw [pow_mul]
      _ ≤ d ^ (n' + q + 3) := pow_le_pow_left₀ (by positivity) he _
  have h3 : d ^ (3 * (n' + q + 2) + 4) ≤ g ^ (n' + 1) := by
    calc d ^ (3 * (n' + q + 2) + 4) ≤ d ^ (25 * (n' + 1)) := pow_le_pow_right₀ hd1 (by omega)
      _ = (d ^ 25) ^ (n' + 1) := by rw [pow_mul]
      _ ≤ g ^ (n' + 1) := pow_le_pow_left₀ (by positivity) hg _
  have hgΨ0 : 0 ≤ g * Ψ := mul_nonneg hg0 hΨ
  calc si ^ n' * c₁ * (e ^ 2 * (g * d ^ 2) * Ψ ^ 2) * (e ^ 2 * d ^ 2 * Q₀) ^ (n' + q + 2)
      ≤ (k₀ ^ n' * Ψ ^ n') * c₁ * (e ^ 2 * (g * d ^ 2) * Ψ ^ 2) *
          (e ^ 2 * d ^ 2 * Q₀) ^ (n' + q + 2) := by gcongr
    _ = (c₁ * k₀ ^ n' * Q₀ ^ (n' + q + 2)) * e ^ (2 * (n' + q + 2) + 2) *
          (d ^ (2 * (n' + q + 2) + 2) * g * Ψ ^ (n' + 2)) := by ring
    _ ≤ d * d ^ (n' + q + 3) * (d ^ (2 * (n' + q + 2) + 2) * g * Ψ ^ (n' + 2)) := by gcongr
    _ = d ^ (3 * (n' + q + 2) + 4) * g * Ψ ^ (n' + 2) := by ring
    _ ≤ g ^ (n' + 1) * g * Ψ ^ (n' + 2) := by gcongr
    _ = (g * Ψ) ^ (n' + 2) := by ring
    _ ≤ (g * Ψ) ^ q := pow_le_pow_of_le_one hgΨ0 hgΨ hq

/-- Case `n(w) ≤ q + 1` (two words of length one), `n = n' + 4`:
`s^{n'} (e² g d² Ψ²)² (e² d² Q₀)^{n+q−4} ≤ (g Ψ)^q`. -/
private theorem sc_arithB {n' q : ℕ} (hq : q ≤ n' + 4) {si Ψ g d e Q₀ k₀ : ℝ}
    (hsi0 : 0 ≤ si) (hΨ : 0 ≤ Ψ) (hg0 : 0 ≤ g) (hd1 : 1 ≤ d) (he1 : 1 ≤ e) (hQ₀ : 0 ≤ Q₀)
    (hsi : si ≤ k₀ * Ψ) (hg : d ^ 25 ≤ g) (he : e ^ 4 ≤ d)
    (hgΨ : g * Ψ ≤ 1) (hK : k₀ ^ n' * Q₀ ^ (n' + q) ≤ d) :
    si ^ n' * (e ^ 2 * (g * d ^ 2) * Ψ ^ 2) ^ 2 * (e ^ 2 * d ^ 2 * Q₀) ^ (n' + q) ≤
      (g * Ψ) ^ q := by
  have hd0 : 0 ≤ d := by linarith
  have he0 : 0 ≤ e := by linarith
  have h1 : si ^ n' ≤ k₀ ^ n' * Ψ ^ n' := by rw [← mul_pow]; exact pow_le_pow_left₀ hsi0 hsi n'
  have h2 : e ^ (2 * (n' + q) + 4) ≤ d ^ (n' + q + 1) := by
    calc e ^ (2 * (n' + q) + 4) ≤ e ^ (4 * (n' + q + 1)) := pow_le_pow_right₀ he1 (by omega)
      _ = (e ^ 4) ^ (n' + q + 1) := by rw [pow_mul]
      _ ≤ d ^ (n' + q + 1) := pow_le_pow_left₀ (by positivity) he _
  have h3 : d ^ (3 * (n' + q) + 6) ≤ g ^ (n' + 2) := by
    calc d ^ (3 * (n' + q) + 6) ≤ d ^ (25 * (n' + 2)) := pow_le_pow_right₀ hd1 (by omega)
      _ = (d ^ 25) ^ (n' + 2) := by rw [pow_mul]
      _ ≤ g ^ (n' + 2) := pow_le_pow_left₀ (by positivity) hg _
  have hgΨ0 : 0 ≤ g * Ψ := mul_nonneg hg0 hΨ
  calc si ^ n' * (e ^ 2 * (g * d ^ 2) * Ψ ^ 2) ^ 2 * (e ^ 2 * d ^ 2 * Q₀) ^ (n' + q)
      ≤ (k₀ ^ n' * Ψ ^ n') * (e ^ 2 * (g * d ^ 2) * Ψ ^ 2) ^ 2 *
          (e ^ 2 * d ^ 2 * Q₀) ^ (n' + q) := by gcongr
    _ = (k₀ ^ n' * Q₀ ^ (n' + q)) * e ^ (2 * (n' + q) + 4) *
          (d ^ (2 * (n' + q) + 4) * g ^ 2 * Ψ ^ (n' + 4)) := by ring
    _ ≤ d * d ^ (n' + q + 1) * (d ^ (2 * (n' + q) + 4) * g ^ 2 * Ψ ^ (n' + 4)) := by gcongr
    _ = d ^ (3 * (n' + q) + 6) * g ^ 2 * Ψ ^ (n' + 4) := by ring
    _ ≤ g ^ (n' + 2) * g ^ 2 * Ψ ^ (n' + 4) := by gcongr
    _ = (g * Ψ) ^ (n' + 4) := by ring
    _ ≤ (g * Ψ) ^ q := pow_le_pow_of_le_one hgΨ0 hgΨ hq

/-- `N^{−n/2} = (N^{−1/2})^n`. -/
private theorem sc_rpow_neg_half (hN : 1 ≤ N) (n : ℕ) :
    (N : ℝ) ^ (-(n : ℝ) / 2) = ((Real.sqrt N)⁻¹) ^ n := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hNp.le, ← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
  congr 1
  ring

/-- `Ψ` from below and above on `𝐃(τ, N)`: `N^{−1/2} ≤ √K_m Ψ`, `Ψ ≤ (√K_m + 1) N^{−τ/2}`,
`Ψ ≥ τ/N`. -/
private theorem sc_Psi_bounds {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) {z : ℂ} (hz : z ∈ S) :
    (Real.sqrt N)⁻¹ ≤ Real.sqrt (mBoundConst τ) * Psi N (specOf Sig) z ∧
      Psi N (specOf Sig) z ≤ (Real.sqrt (mBoundConst τ) + 1) * (N : ℝ) ^ (-(τ / 2)) ∧
      τ / N ≤ Psi N (specOf Sig) z := by
  have hN := sc_N_pos hset
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hτ := hset.pos
  have hzD := hset.domain.1 hz
  have hη : 0 < z.im := hzD.1
  have hηt : z.im ≤ τ⁻¹ := hzD.2.2.2.2
  obtain ⟨-, hmK, hmI⟩ := gen_prop_m_specDomain (scR_density hset hN) hzD
  set Km := mBoundConst τ with hKm
  have hKm0 : 0 < Km := by rw [hKm]; unfold mBoundConst genPropConst; positivity
  set m := mFun N (specOf Sig) z with hm
  have hNη : 0 < (N : ℝ) * z.im := by positivity
  have hNη1 := sc_one_le_N_im hN hτ hzD
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

/-! ## Products of words on `Θ` -/

/-- `R_i = |G_{v̄ i}| + |G_{i v̄}|`. -/
private def scRi (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) : ℝ :=
  ‖ent (G Sig A z) (vbar Sig v) (eI (Sum.inl i))‖ + ‖ent (G Sig A z) (eI (Sum.inl i)) (vbar Sig v)‖

/-- `R_μ = |G_{v̄ μ}| + |G_{μ v̄}|`. -/
private def scRm (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (v : Fin M ⊕ Fin N → ℝ) (μ : Fin N) : ℝ :=
  ‖ent (G Sig A z) (vbar Sig v) (eI (Sum.inr μ))‖ + ‖ent (G Sig A z) (eI (Sum.inr μ)) (vbar Sig v)‖

private theorem sc_wordA_zero (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) (k : ℕ) (w : Word k) (hk : k = 0) :
    ‖wordA Sig A z v i μ k w‖ = Fv Sig A z v := by
  subst hk
  rfl

private theorem sc_wordA_R {Sig : Matrix (Fin M) (Fin M) ℝ} (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) {B : ℝ} (hB : 0 ≤ B)
    (h3 : ∀ b b', ‖G Sig A z (letterS i μ b) (letterT i μ b')‖ ≤ B) (k : ℕ) (w : Word k)
    (hk : 1 ≤ k) :
    ‖wordA Sig A z v i μ k w‖ ≤ (scRi Sig A z v i ^ 2 + scRm Sig A z v μ ^ 2) * B ^ (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simpa [scRi, scRm] using wordA_le_R A z v i μ hB h3 j w

private theorem sc_wordA_one {Sig : Matrix (Fin M) (Fin M) ℝ} (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) (k : ℕ) (w : Word k) (hk : k = 1) :
    ‖wordA Sig A z v i μ k w‖ ≤ scRi Sig A z v i * scRm Sig A z v μ := by
  subst hk
  exact wordA_one_le A z v i μ w

/-- Pigeonhole on a subfamily `T`: `∑_{r ∈ T} n_r + 2 ≤ 2 |T|`, all `n_r ≥ 1`, give two indices
with `n_r = 1`. -/
private theorem sc_pigeonhole {p : ℕ} (ns : Fin p → ℕ) (T : Finset (Fin p))
    (hT : ∀ r ∈ T, 1 ≤ ns r) (hn : ∑ r ∈ T, ns r + 2 ≤ 2 * T.card) :
    ∃ r₁ ∈ T, ∃ r₂ ∈ T, r₁ ≠ r₂ ∧ ns r₁ = 1 ∧ ns r₂ = 1 := by
  set e := T.equivFin
  have hsum : ∑ k, ns (e.symm k) = ∑ r ∈ T, ns r := by
    rw [Equiv.sum_comp e.symm (fun r : T => ns r)]
    exact Finset.sum_coe_sort T ns
  obtain ⟨k₁, k₂, hne, h1, h2⟩ := pigeonhole_words (fun k : Fin T.card => ns (e.symm k))
    (fun k => hT _ (e.symm k).2) (by rw [hsum]; exact hn)
  exact ⟨e.symm k₁, (e.symm k₁).2, e.symm k₂, (e.symm k₂).2,
    fun h => hne (e.symm.injective (Subtype.ext h)), h1, h2⟩

/-- The words of length `0` contribute `F_v^{p − q}`, `q = #{r : n_r ≥ 1}`. -/
private theorem sc_prod_split (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) {p : ℕ} (ns : Fin p → ℕ)
    (ws : ∀ r, Word (ns r)) :
    ∏ r, ‖wordA Sig A z v i μ (ns r) (ws r)‖ =
      (∏ r ∈ Finset.univ.filter (fun r => 1 ≤ ns r), ‖wordA Sig A z v i μ (ns r) (ws r)‖) *
        Fv Sig A z v ^ (p - (Finset.univ.filter (fun r => 1 ≤ ns r)).card) := by
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun r => 1 ≤ ns r)]
  congr 1
  have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin p)))
    (fun r => 1 ≤ ns r)
  rw [Finset.card_univ, Fintype.card_fin] at hc
  rw [Finset.prod_congr rfl fun r hr => sc_wordA_zero Sig A z v i μ (ns r) (ws r)
    (by simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hr; omega),
    Finset.prod_const]
  congr 1
  omega

/-- Case `n ≥ q + 2`: `∏_r |A(w_r)| ≤ F_v^{p−q} (R_i² + R_μ²) B^{n+q−2}` ((w_est), (w_est_2)). -/
private theorem sc_prod_caseA {Sig : Matrix (Fin M) (Fin M) ℝ} (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) {B : ℝ} (hB1 : 1 ≤ B)
    (h0 : Fv Sig A z v ≤ B)
    (h1 : ∀ b, ‖ent (G Sig A z) (vbar Sig v) (eI (letterT i μ b))‖ ≤ B)
    (h2 : ∀ b, ‖ent (G Sig A z) (eI (letterS i μ b)) (vbar Sig v)‖ ≤ B)
    (h3 : ∀ b b', ‖G Sig A z (letterS i μ b) (letterT i μ b')‖ ≤ B) {p : ℕ} (ns : Fin p → ℕ)
    (ws : ∀ r, Word (ns r)) (r₀ : Fin p) (hr₀ : 1 ≤ ns r₀) :
    ∏ r, ‖wordA Sig A z v i μ (ns r) (ws r)‖ ≤
      Fv Sig A z v ^ (p - (Finset.univ.filter (fun r => 1 ≤ ns r)).card) *
        ((scRi Sig A z v i ^ 2 + scRm Sig A z v μ ^ 2) *
          B ^ (∑ r, ns r + (Finset.univ.filter (fun r => 1 ≤ ns r)).card - 2)) := by
  set T := Finset.univ.filter (fun r => 1 ≤ ns r) with hT
  have hB0 : 0 ≤ B := by linarith
  have hr₀T : r₀ ∈ T := by simp [hT, hr₀]
  rw [sc_prod_split, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (norm_nonneg _) _)
  have hsT : ∑ r ∈ T, ns r = ∑ r, ns r :=
    Finset.sum_filter_of_ne fun r _ h => Nat.one_le_iff_ne_zero.2 h
  have herase := Finset.add_sum_erase T ns hr₀T
  have hcard := Finset.card_erase_of_mem hr₀T
  have hTpos : 1 ≤ T.card := Finset.card_pos.2 ⟨r₀, hr₀T⟩
  have hsum1 : ∑ r ∈ T.erase r₀, (ns r + 1) = ∑ r ∈ T.erase r₀, ns r + (T.erase r₀).card := by
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
  rw [← Finset.mul_prod_erase T _ hr₀T]
  have hR0 : 0 ≤ scRi Sig A z v i ^ 2 + scRm Sig A z v μ ^ 2 := by positivity
  calc ‖wordA Sig A z v i μ (ns r₀) (ws r₀)‖ *
        ∏ r ∈ T.erase r₀, ‖wordA Sig A z v i μ (ns r) (ws r)‖
      ≤ ((scRi Sig A z v i ^ 2 + scRm Sig A z v μ ^ 2) * B ^ (ns r₀ - 1)) *
          ∏ r ∈ T.erase r₀, B ^ (ns r + 1) := by
        refine mul_le_mul (sc_wordA_R A z v i μ hB0 h3 _ _ hr₀)
          (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun r _ =>
            wordA_le A z v i μ h0 h1 h2 h3 _ _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
          (by positivity)
    _ = (scRi Sig A z v i ^ 2 + scRm Sig A z v μ ^ 2) *
          B ^ (ns r₀ - 1 + ∑ r ∈ T.erase r₀, (ns r + 1)) := by
        rw [Finset.prod_pow_eq_pow_sum, pow_add]; ring
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB1 ?_) hR0
        rw [hsum1]
        omega

/-- Case `n ≤ q + 1` with two words of length one: `∏_r |A(w_r)| ≤ F_v^{p−q} R_i² R_μ² B^{n+q−4}`
((w_est_1)). -/
private theorem sc_prod_caseB {Sig : Matrix (Fin M) (Fin M) ℝ} (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) {B : ℝ} (hB1 : 1 ≤ B)
    (h0 : Fv Sig A z v ≤ B)
    (h1 : ∀ b, ‖ent (G Sig A z) (vbar Sig v) (eI (letterT i μ b))‖ ≤ B)
    (h2 : ∀ b, ‖ent (G Sig A z) (eI (letterS i μ b)) (vbar Sig v)‖ ≤ B)
    (h3 : ∀ b b', ‖G Sig A z (letterS i μ b) (letterT i μ b')‖ ≤ B) {p : ℕ} (ns : Fin p → ℕ)
    (ws : ∀ r, Word (ns r)) (r₁ r₂ : Fin p) (hne : r₁ ≠ r₂) (hr₁ : ns r₁ = 1)
    (hr₂ : ns r₂ = 1) :
    ∏ r, ‖wordA Sig A z v i μ (ns r) (ws r)‖ ≤
      Fv Sig A z v ^ (p - (Finset.univ.filter (fun r => 1 ≤ ns r)).card) *
        (scRi Sig A z v i ^ 2 * scRm Sig A z v μ ^ 2 *
          B ^ (∑ r, ns r + (Finset.univ.filter (fun r => 1 ≤ ns r)).card - 4)) := by
  set T := Finset.univ.filter (fun r => 1 ≤ ns r) with hT
  have hB0 : 0 ≤ B := by linarith
  have hr₁T : r₁ ∈ T := by simp [hT, hr₁]
  have hr₂T : r₂ ∈ T.erase r₁ := Finset.mem_erase.2 ⟨hne.symm, by simp [hT, hr₂]⟩
  rw [sc_prod_split, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (norm_nonneg _) _)
  have hsT : ∑ r ∈ T, ns r = ∑ r, ns r :=
    Finset.sum_filter_of_ne fun r _ h => Nat.one_le_iff_ne_zero.2 h
  have herase1 := Finset.add_sum_erase T ns hr₁T
  have herase2 := Finset.add_sum_erase (T.erase r₁) ns hr₂T
  have hcard1 := Finset.card_erase_of_mem hr₁T
  have hcard2 := Finset.card_erase_of_mem hr₂T
  have hTpos : 1 ≤ T.card := Finset.card_pos.2 ⟨r₁, hr₁T⟩
  have hT2 : 1 ≤ (T.erase r₁).card := Finset.card_pos.2 ⟨r₂, hr₂T⟩
  set T'' := (T.erase r₁).erase r₂ with hT''
  have hsum1 : ∑ r ∈ T'', (ns r + 1) = ∑ r ∈ T'', ns r + T''.card := by
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
  rw [← Finset.mul_prod_erase T _ hr₁T, ← Finset.mul_prod_erase (T.erase r₁) _ hr₂T]
  have hx := sc_wordA_one (Sig := Sig) A z v i μ _ (ws r₁) hr₁
  have hy := sc_wordA_one (Sig := Sig) A z v i μ _ (ws r₂) hr₂
  have hRi : 0 ≤ scRi Sig A z v i := by unfold scRi; positivity
  have hRm : 0 ≤ scRm Sig A z v μ := by unfold scRm; positivity
  calc ‖wordA Sig A z v i μ (ns r₁) (ws r₁)‖ * (‖wordA Sig A z v i μ (ns r₂) (ws r₂)‖ *
        ∏ r ∈ T'', ‖wordA Sig A z v i μ (ns r) (ws r)‖)
      ≤ (scRi Sig A z v i * scRm Sig A z v μ) * ((scRi Sig A z v i * scRm Sig A z v μ) *
          ∏ r ∈ T'', B ^ (ns r + 1)) := by
        refine mul_le_mul hx (mul_le_mul hy (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          fun r _ => wordA_le A z v i μ h0 h1 h2 h3 _ _)
          (Finset.prod_nonneg fun _ _ => norm_nonneg _) (by positivity))
          (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _))
          (by positivity)
    _ = scRi Sig A z v i ^ 2 * scRm Sig A z v μ ^ 2 * B ^ (∑ r ∈ T'', (ns r + 1)) := by
        rw [Finset.prod_pow_eq_pow_sum]; ring
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB1 ?_) (by positivity)
        rw [hsum1]
        omega

/-- (sc_step 6)–(sc_step 8) on `Θ`, deterministic: with the entry bounds `B = N^{2δ+2ε_A} Q₀` and
`N⁻¹ ∑ R² ≤ N^{2ε_A} N^{(C₀+2)δ} Ψ²`, `N^{−n/2} ∑_{iμ} ∏_r |A(w_r)| ≤ F_v^p + (N^{C₀δ}Ψ)^p`. -/
private theorem sc_on_event {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) {z : ℂ} (hz : z ∈ S) (A : Matrix (Fin M) (Fin N) ℝ)
    (v : Fin M ⊕ Fin N → ℝ) {p : ℕ} (hp2 : 2 ≤ p) (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r))
    (hn4 : 4 ≤ ∑ r, ns r) (hn : ∑ r, ns r ≤ 4 * p) {C₀ δ εA : ℝ} (hδ : 0 < δ) (hC₀ : 25 ≤ C₀)
    (hεA : 0 < εA) (hεAδ : εA ≤ δ / 4)
    (hK : (τ⁻¹ + 1) * (Real.sqrt (mBoundConst τ) + 1) ^ (4 * p) * scQ0 τ c ^ (5 * p) ≤
      (N : ℝ) ^ δ)
    (hgΨ : (N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z ≤ 1)
    (h0 : Fv Sig A z v ≤ (N : ℝ) ^ (2 * εA) * (N : ℝ) ^ (2 * δ) * scQ0 τ c)
    (h1 : ∀ a, ‖ent (G Sig A z) (vbar Sig v) (eI a)‖ ≤
      (N : ℝ) ^ (2 * εA) * (N : ℝ) ^ (2 * δ) * scQ0 τ c)
    (h2 : ∀ a, ‖ent (G Sig A z) (eI a) (vbar Sig v)‖ ≤
      (N : ℝ) ^ (2 * εA) * (N : ℝ) ^ (2 * δ) * scQ0 τ c)
    (h3 : ∀ a b, ‖G Sig A z a b‖ ≤ (N : ℝ) ^ (2 * εA) * (N : ℝ) ^ (2 * δ) * scQ0 τ c)
    (hQ : (N : ℝ)⁻¹ *
              (∑ i, (‖ent (G Sig A z) (vbar Sig v) (eI (Sum.inl i))‖ +
                  ‖ent (G Sig A z) (eI (Sum.inl i)) (vbar Sig v)‖) ^ 2 +
                ∑ μ, (‖ent (G Sig A z) (vbar Sig v) (eI (Sum.inr μ))‖ +
                  ‖ent (G Sig A z) (eI (Sum.inr μ)) (vbar Sig v)‖) ^ 2) ≤
              (N : ℝ) ^ (2 * εA) * ((N : ℝ) ^ ((C₀ + 2) * δ) * Psi N (specOf Sig) z ^ 2)) :
    (N : ℝ) ^ (-((∑ r, ns r : ℕ) : ℝ) / 2) *
        ∑ i, ∑ μ, ∏ r, ‖wordA Sig A z v i μ (ns r) (ws r)‖ ≤
      Fv Sig A z v ^ p + ((N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z) ^ p := by
  have hN := sc_N_pos hset
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hτ := hset.pos
  have hM : (M : ℝ) ≤ τ⁻¹ * N := by
    have := hset.ratio_le
    rwa [div_le_iff₀ hNp] at this
  obtain ⟨hsiΨ, -, hΨτ⟩ := sc_Psi_bounds hset hz
  set Ψ := Psi N (specOf Sig) z with hΨdef
  have hΨ0 : 0 ≤ Ψ := le_trans (by positivity) hΨτ
  set n := ∑ r, ns r with hndef
  obtain ⟨n', hn'⟩ : ∃ n', n = n' + 4 := ⟨n - 4, by omega⟩
  set T := Finset.univ.filter (fun r => 1 ≤ ns r) with hT
  set q := T.card with hqdef
  have hsT : ∑ r ∈ T, ns r = n :=
    Finset.sum_filter_of_ne fun r _ h => Nat.one_le_iff_ne_zero.2 h
  have hqp : q ≤ p := by
    have := Finset.card_filter_le (Finset.univ : Finset (Fin p)) (fun r => 1 ≤ ns r)
    rwa [Finset.card_univ, Fintype.card_fin] at this
  have hTne : T.Nonempty := Finset.nonempty_of_sum_ne_zero (by rw [hsT]; omega)
  have hq1 : 1 ≤ q := Finset.card_pos.2 hTne
  have hqn : q ≤ n := by
    have : ∑ r ∈ T, 1 ≤ ∑ r ∈ T, ns r :=
      Finset.sum_le_sum fun r hr => (Finset.mem_filter.1 hr).2
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at this
    omega
  -- powers of `N`
  set e := (N : ℝ) ^ εA with he
  set d := (N : ℝ) ^ δ with hd
  set g := (N : ℝ) ^ (C₀ * δ) with hg
  set Q₀ := scQ0 τ c with hQ₀
  set k₀ := Real.sqrt (mBoundConst τ) with hk₀
  set si := (Real.sqrt N)⁻¹ with hsi
  have hQ₀1 : 1 ≤ Q₀ := scQ0_ge hτ hset.c_pos
  have he1 : 1 ≤ e := Real.one_le_rpow hN1r hεA.le
  have hd1 : 1 ≤ d := Real.one_le_rpow hN1r hδ.le
  have hg0 : 0 ≤ g := Real.rpow_nonneg hNp.le _
  have hk₀0 : 0 ≤ k₀ := Real.sqrt_nonneg _
  have hsi0 : 0 ≤ si := by positivity
  have hpow : ∀ (a : ℝ) (k : ℕ), (N : ℝ) ^ ((k : ℝ) * a) = ((N : ℝ) ^ a) ^ k := fun a k => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le, mul_comm]
  have hN2εA : (N : ℝ) ^ (2 * εA) = e ^ 2 := by rw [he, ← hpow]; norm_num
  have hN2δ : (N : ℝ) ^ (2 * δ) = d ^ 2 := by rw [hd, ← hpow]; norm_num
  have hNC : (N : ℝ) ^ ((C₀ + 2) * δ) = g * d ^ 2 := by
    rw [hg, ← hN2δ, ← Real.rpow_add hNp]; ring_nf
  have he4 : e ^ 4 ≤ d := by
    rw [he, hd, ← hpow]
    exact Real.rpow_le_rpow_of_exponent_le hN1r (by push_cast; linarith)
  have hg25 : d ^ 25 ≤ g := by
    rw [hd, hg, ← hpow]
    exact Real.rpow_le_rpow_of_exponent_le hN1r (by push_cast; nlinarith)
  set B := (N : ℝ) ^ (2 * εA) * (N : ℝ) ^ (2 * δ) * Q₀ with hB
  have hBe : B = e ^ 2 * d ^ 2 * Q₀ := by rw [hB, hN2εA, hN2δ]
  have hB1 : 1 ≤ B := by
    rw [hBe]
    have : 1 ≤ e ^ 2 * d ^ 2 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ he1) (one_le_pow₀ hd1)
    exact one_le_mul_of_one_le_of_one_le this hQ₀1
  have hNn : (N : ℝ) ^ (-((n : ℕ) : ℝ) / 2) = si ^ n' * si ^ 4 := by
    rw [sc_rpow_neg_half hN, hn', pow_add]
  have hsi4 : si ^ 4 * (N : ℝ) ^ 2 = 1 := by
    have hs : Real.sqrt N ^ 2 = N := Real.sq_sqrt hNp.le
    have hs0 : 0 < Real.sqrt N := Real.sqrt_pos.2 hNp
    rw [hsi, inv_pow, show Real.sqrt N ^ 4 = (Real.sqrt N ^ 2) ^ 2 by ring, hs,
      inv_mul_cancel₀ (by positivity)]
  set Rx : Fin M → ℝ := fun i => scRi Sig A z v i with hRx
  set Ry : Fin N → ℝ := fun μ => scRm Sig A z v μ with hRy
  set Qs := (N : ℝ)⁻¹ * (∑ i, Rx i ^ 2 + ∑ μ, Ry μ ^ 2) with hQsd
  have hQs : Qs ≤ e ^ 2 * (g * d ^ 2 * Ψ ^ 2) := by
    have := hQ
    rw [hN2εA, hNC] at this
    simpa [hQsd, hRx, hRy, scRi, scRm, mul_assoc] using this
  have hSxy : ∑ i, Rx i ^ 2 + ∑ μ, Ry μ ^ 2 = (N : ℝ) * Qs := by
    rw [hQsd, ← mul_assoc, mul_inv_cancel₀ hNp.ne', one_mul]
  have hSx0 : 0 ≤ ∑ i, Rx i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hSy0 : 0 ≤ ∑ μ, Ry μ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hQs0 : 0 ≤ Qs := by rw [hQsd]; positivity
  have hb1 : ∀ i μ b, ‖ent (G Sig A z) (vbar Sig v) (eI (letterT i μ b))‖ ≤ B :=
    fun _ _ _ => h1 _
  have hb2 : ∀ i μ b, ‖ent (G Sig A z) (eI (letterS i μ b)) (vbar Sig v)‖ ≤ B :=
    fun _ _ _ => h2 _
  have hb3 : ∀ i μ b b', ‖G Sig A z (letterS i μ b) (letterT i μ b')‖ ≤ B :=
    fun _ _ _ _ => h3 _ _
  set F := Fv Sig A z v with hF
  have hF0 : 0 ≤ F := norm_nonneg _
  have hk4 : k₀ ^ n' ≤ (k₀ + 1) ^ (4 * p) :=
    (pow_le_pow_left₀ hk₀0 (by linarith) n').trans
      (pow_le_pow_right₀ (by linarith) (by omega))
  have hτ1 : 0 ≤ τ⁻¹ := (inv_pos.2 hτ).le
  have hmain : (N : ℝ) ^ (-((n : ℕ) : ℝ) / 2) *
      ∑ i, ∑ μ, ∏ r, ‖wordA Sig A z v i μ (ns r) (ws r)‖ ≤ F ^ (p - q) * (g * Ψ) ^ q := by
    by_cases hcase : q + 2 ≤ n
    · -- case A
      obtain ⟨r₀, hr₀T⟩ := hTne
      have hr₀ : 1 ≤ ns r₀ := (Finset.mem_filter.1 hr₀T).2
      have hper : ∀ i μ, ∏ r, ‖wordA Sig A z v i μ (ns r) (ws r)‖ ≤
          F ^ (p - q) * ((Rx i ^ 2 + Ry μ ^ 2) * B ^ (n' + q + 2)) := by
        intro i μ
        have := sc_prod_caseA A z v i μ hB1 h0 (hb1 i μ) (hb2 i μ) (hb3 i μ) ns ws r₀ hr₀
        rw [← hndef, ← hT, ← hqdef, show n + q - 2 = n' + q + 2 by omega] at this
        exact this
      have hsum : ∑ i, ∑ μ, (Rx i ^ 2 + Ry μ ^ 2) ≤ (τ⁻¹ + 1) * (N : ℝ) ^ 2 * Qs := by
        have e1 : ∑ i, ∑ μ, (Rx i ^ 2 + Ry μ ^ 2) =
            (N : ℝ) * ∑ i, Rx i ^ 2 + (M : ℝ) * ∑ μ, Ry μ ^ 2 := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
        rw [e1]
        have h5 : (N : ℝ) * ∑ i, Rx i ^ 2 ≤ (τ⁻¹ + 1) * N * ∑ i, Rx i ^ 2 := by
          have : (N : ℝ) ≤ (τ⁻¹ + 1) * N := by
            have := mul_nonneg hτ1 hNp.le
            linarith only [this]
          exact mul_le_mul_of_nonneg_right this hSx0
        have h6 : (M : ℝ) * ∑ μ, Ry μ ^ 2 ≤ (τ⁻¹ + 1) * N * ∑ μ, Ry μ ^ 2 := by
          have : (M : ℝ) ≤ (τ⁻¹ + 1) * N := by linarith only [hM, hNp]
          exact mul_le_mul_of_nonneg_right this hSy0
        calc (N : ℝ) * ∑ i, Rx i ^ 2 + (M : ℝ) * ∑ μ, Ry μ ^ 2
            ≤ (τ⁻¹ + 1) * N * (∑ i, Rx i ^ 2 + ∑ μ, Ry μ ^ 2) := by
              rw [mul_add]; exact add_le_add h5 h6
          _ = (τ⁻¹ + 1) * (N : ℝ) ^ 2 * Qs := by rw [hSxy]; ring
      have hA := sc_arithA (n' := n') (q := q) (by omega) hsi0 hΨ0 hg0 hd1 he1
        (by linarith only [hQ₀1]) (by linarith only [hτ1]) hsiΨ hg25 he4 hgΨ (c₁ := τ⁻¹ + 1)
        (k₀ := k₀) (Q₀ := Q₀) (by
          calc (τ⁻¹ + 1) * k₀ ^ n' * Q₀ ^ (n' + q + 2)
              ≤ (τ⁻¹ + 1) * (k₀ + 1) ^ (4 * p) * Q₀ ^ (5 * p) := by
                gcongr
                omega
            _ ≤ d := hK)
      calc (N : ℝ) ^ (-((n : ℕ) : ℝ) / 2) * ∑ i, ∑ μ, ∏ r, ‖wordA Sig A z v i μ (ns r) (ws r)‖
          ≤ (si ^ n' * si ^ 4) * ∑ i, ∑ μ,
              F ^ (p - q) * ((Rx i ^ 2 + Ry μ ^ 2) * B ^ (n' + q + 2)) := by
            rw [hNn]
            gcongr with i _ μ _
            exact hper i μ
        _ = F ^ (p - q) * (si ^ n' * B ^ (n' + q + 2)) * (si ^ 4 *
              ∑ i, ∑ μ, (Rx i ^ 2 + Ry μ ^ 2)) := by
            simp only [← Finset.mul_sum, ← Finset.sum_mul]
            ring
        _ ≤ F ^ (p - q) * (si ^ n' * B ^ (n' + q + 2)) * (si ^ 4 *
              ((τ⁻¹ + 1) * (N : ℝ) ^ 2 * Qs)) := by gcongr
        _ = F ^ (p - q) * (si ^ n' * (τ⁻¹ + 1) * Qs * B ^ (n' + q + 2)) := by
            have : si ^ 4 * ((τ⁻¹ + 1) * (N : ℝ) ^ 2 * Qs) = (τ⁻¹ + 1) * Qs := by
              rw [show si ^ 4 * ((τ⁻¹ + 1) * (N : ℝ) ^ 2 * Qs) =
                (si ^ 4 * (N : ℝ) ^ 2) * ((τ⁻¹ + 1) * Qs) by ring, hsi4, one_mul]
            rw [this]; ring
        _ ≤ F ^ (p - q) * (si ^ n' * (τ⁻¹ + 1) * (e ^ 2 * (g * d ^ 2) * Ψ ^ 2) *
              (e ^ 2 * d ^ 2 * Q₀) ^ (n' + q + 2)) := by
            rw [hBe]
            gcongr
            calc Qs ≤ e ^ 2 * (g * d ^ 2 * Ψ ^ 2) := hQs
              _ = e ^ 2 * (g * d ^ 2) * Ψ ^ 2 := by ring
        _ ≤ F ^ (p - q) * (g * Ψ) ^ q := by gcongr
    · -- case B
      have hpig : ∑ r ∈ T, ns r + 2 ≤ 2 * T.card := by rw [hsT]; omega
      obtain ⟨r₁, hr₁T, r₂, hr₂T, hne, hr₁, hr₂⟩ :=
        sc_pigeonhole ns T (fun r hr => (Finset.mem_filter.1 hr).2) hpig
      have hper : ∀ i μ, ∏ r, ‖wordA Sig A z v i μ (ns r) (ws r)‖ ≤
          F ^ (p - q) * (Rx i ^ 2 * Ry μ ^ 2 * B ^ (n' + q)) := by
        intro i μ
        have := sc_prod_caseB A z v i μ hB1 h0 (hb1 i μ) (hb2 i μ) (hb3 i μ) ns ws r₁ r₂ hne
          hr₁ hr₂
        rw [← hndef, ← hT, ← hqdef, show n + q - 4 = n' + q by omega] at this
        exact this
      have hsum : ∑ i, ∑ μ, Rx i ^ 2 * Ry μ ^ 2 ≤ (N : ℝ) ^ 2 * Qs ^ 2 := by
        rw [← Finset.sum_mul_sum]
        have : (N : ℝ) ^ 2 * Qs ^ 2 = (∑ i, Rx i ^ 2 + ∑ μ, Ry μ ^ 2) ^ 2 := by
          rw [hSxy]; ring
        rw [this]
        nlinarith only [mul_nonneg hSx0 hSy0, sq_nonneg (∑ i, Rx i ^ 2), sq_nonneg (∑ μ, Ry μ ^ 2)]
      have hBB := sc_arithB (n' := n') (q := q) (by omega) hsi0 hΨ0 hg0 hd1 he1
        (by linarith only [hQ₀1])
        hsiΨ hg25 he4 hgΨ (k₀ := k₀) (Q₀ := Q₀) (by
          calc k₀ ^ n' * Q₀ ^ (n' + q) ≤ (τ⁻¹ + 1) * (k₀ + 1) ^ (4 * p) * Q₀ ^ (5 * p) := by
                have h5 : Q₀ ^ (n' + q) ≤ Q₀ ^ (5 * p) := pow_le_pow_right₀ hQ₀1 (by omega)
                have h6 : 1 ≤ τ⁻¹ + 1 := by linarith only [hτ1]
                have h7 : 0 ≤ (k₀ + 1) ^ (4 * p) * Q₀ ^ (5 * p) := by positivity
                calc k₀ ^ n' * Q₀ ^ (n' + q) ≤ (k₀ + 1) ^ (4 * p) * Q₀ ^ (5 * p) :=
                      mul_le_mul hk4 h5 (by positivity) (by positivity)
                  _ ≤ (τ⁻¹ + 1) * ((k₀ + 1) ^ (4 * p) * Q₀ ^ (5 * p)) :=
                      le_mul_of_one_le_left h7 h6
                  _ = _ := by ring
            _ ≤ d := hK)
      calc (N : ℝ) ^ (-((n : ℕ) : ℝ) / 2) * ∑ i, ∑ μ, ∏ r, ‖wordA Sig A z v i μ (ns r) (ws r)‖
          ≤ (si ^ n' * si ^ 4) * ∑ i, ∑ μ, F ^ (p - q) * (Rx i ^ 2 * Ry μ ^ 2 * B ^ (n' + q)) := by
            rw [hNn]
            gcongr with i _ μ _
            exact hper i μ
        _ = F ^ (p - q) * (si ^ n' * B ^ (n' + q)) * (si ^ 4 *
              ∑ i, ∑ μ, Rx i ^ 2 * Ry μ ^ 2) := by
            simp only [← Finset.mul_sum, ← Finset.sum_mul]
            ring
        _ ≤ F ^ (p - q) * (si ^ n' * B ^ (n' + q)) * (si ^ 4 * ((N : ℝ) ^ 2 * Qs ^ 2)) := by
            gcongr
        _ = F ^ (p - q) * (si ^ n' * Qs ^ 2 * B ^ (n' + q)) := by
            have : si ^ 4 * ((N : ℝ) ^ 2 * Qs ^ 2) = Qs ^ 2 := by
              rw [← mul_assoc, hsi4, one_mul]
            rw [this]; ring
        _ ≤ F ^ (p - q) * (si ^ n' * (e ^ 2 * (g * d ^ 2) * Ψ ^ 2) ^ 2 *
              (e ^ 2 * d ^ 2 * Q₀) ^ (n' + q)) := by
            rw [hBe]
            gcongr
            calc Qs ≤ e ^ 2 * (g * d ^ 2 * Ψ ^ 2) := hQs
              _ = e ^ 2 * (g * d ^ 2) * Ψ ^ 2 := by ring
        _ ≤ F ^ (p - q) * (g * Ψ) ^ q := by gcongr
  refine hmain.trans ?_
  have hY := young_pow hF0 (mul_nonneg hg0 hΨ0) hqp (by omega : 0 < p)
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hc1 : ((p - q : ℕ) : ℝ) / p ≤ 1 := by
    rw [div_le_one hpR]; exact_mod_cast Nat.sub_le p q
  have hc2 : (q : ℝ) / p ≤ 1 := by
    rw [div_le_one hpR]; exact_mod_cast hqp
  have hFp : 0 ≤ F ^ p := pow_nonneg hF0 p
  have hgp : 0 ≤ (g * Ψ) ^ p := pow_nonneg (mul_nonneg hg0 hΨ0) p
  linarith only [hY, mul_le_mul_of_nonneg_right hc1 hFp, mul_le_mul_of_nonneg_right hc2 hgp]

/-! ## (sc_step 6)–(sc_step 8) -/

private theorem sc_dPrev_ge (p : ℕ) : 3 * ((20 * p + 5 : ℕ) : ℝ) ≤ dPrev p - 4 := by
  unfold dPrev
  push_cast
  have : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  nlinarith

/-- (sc_step 6)–(sc_step 8) at a general `C₀ ≥ 25` with `C₀ δ ≤ τ/4`. -/
private theorem sc_step6_gen (τ c : ℝ) (C : ℕ → ℝ) (p : ℕ) (C₀ δ εA DA : ℝ) (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (hc : 0 < c) (hp2 : 2 ≤ p) (hδ : 0 < δ) (hC₀ : 25 ≤ C₀)
    (hC₀δ : C₀ * δ ≤ τ / 4) (hεA : 0 < εA) (hεAδ : εA ≤ δ / 4) (hDA : dPrev p ≤ DA) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ)
      (P : ModelClass M N) (m : ℕ), CompSetting τ c M N Sig S → 1 ≤ m →
      PropA N C P Sig S C₀ δ (m - 1) εA DA →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption C X → P Ω X →
        ∀ z ∈ levelSet N δ S m, ∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 →
          ∀ (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r)), 4 ≤ ∑ r, ns r → ∑ r, ns r ≤ 4 * p →
            (N : ℝ) ^ (-((∑ r, ns r : ℕ) : ℝ) / 2) *
                ∑ i, ∑ μ, ∫ ω, ∏ r, ‖wordA Sig (X ω) z v i μ (ns r) (ws r)‖ ≤
              2 * ((N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z) ^ p +
                ∫ ω, Fv Sig (X ω) z v ^ p := by
  obtain ⟨N₁, h₁⟩ := sc_event τ c C C₀ δ εA DA hτ hτ1 hc hδ hC₀ hC₀δ hεA
  obtain ⟨N₂, h₂⟩ := integral_Fv_pow_le τ c C p hτ hτ1 hc
  set k₀ := Real.sqrt (mBoundConst τ) with hk₀
  have hk₀0 : 0 ≤ k₀ := Real.sqrt_nonneg _
  have hT0 : 0 ≤ τ⁻¹ := (inv_pos.2 hτ).le
  set K₁ : ℝ := (τ⁻¹ + 1) * (k₀ + 1) ^ (4 * p) * scQ0 τ c ^ (5 * p) with hK₁
  have hK₁0 : 0 ≤ K₁ := by
    have := scQ0_ge hτ hc
    rw [hK₁]; positivity
  set R := roughConst τ c with hR
  have hR1 : 1 ≤ R := sc_roughConst_ge hτ hτ1 hc
  set Kz : ℝ := τ⁻¹ ^ 2 * R ^ (10 * p) * scKW τ C (10 * p) with hKz
  have hKz0 : 0 ≤ Kz := by
    have := scKW_nonneg hτ C (10 * p)
    rw [hKz]; positivity
  refine ⟨max (max (max N₁ N₂) (max ⌈K₁ ^ δ⁻¹⌉₊ ⌈(k₀ + 1) ^ (τ / 4)⁻¹⌉₊))
    (max ⌈Kz⌉₊ (max ⌈τ⁻¹ ^ p⌉₊ 1)), ?_⟩
  intro N hN M Sig S P m hset hm hA Ω _ _ X hX hP z hz v hv ns ws hn4 hn
  have hNN₁ : N₁ ≤ N := by omega
  have hNN₂ : N₂ ≤ N := by omega
  have hNK₁ : ⌈K₁ ^ δ⁻¹⌉₊ ≤ N := by omega
  have hNk₀ : ⌈(k₀ + 1) ^ (τ / 4)⁻¹⌉₊ ≤ N := by omega
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
  obtain ⟨-, hΨup, hΨτ⟩ := sc_Psi_bounds hset hzS
  set Ψ := Psi N (specOf Sig) z with hΨdef
  have hΨ0 : 0 ≤ Ψ := le_trans (by positivity) hΨτ
  set g := (N : ℝ) ^ (C₀ * δ) with hg
  have hg1 : 1 ≤ g := Real.one_le_rpow hN1r (by nlinarith)
  have hgΨ : g * Ψ ≤ 1 := by
    have hk : k₀ + 1 ≤ (N : ℝ) ^ (τ / 4) := sc_le_rpow (by positivity) (by positivity) hNk₀
    have h1 : g * (N : ℝ) ^ (-(τ / 2)) ≤ (N : ℝ) ^ (-(τ / 4)) := by
      rw [hg, ← Real.rpow_add hNp]
      exact Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
    have h2 : (N : ℝ) ^ (τ / 4) * (N : ℝ) ^ (-(τ / 4)) = 1 := by
      rw [← Real.rpow_add hNp]; simp
    calc g * Ψ ≤ g * ((k₀ + 1) * (N : ℝ) ^ (-(τ / 2))) :=
          mul_le_mul_of_nonneg_left hΨup (by linarith)
      _ = (k₀ + 1) * (g * (N : ℝ) ^ (-(τ / 2))) := by ring
      _ ≤ (N : ℝ) ^ (τ / 4) * (N : ℝ) ^ (-(τ / 4)) :=
          mul_le_mul hk h1 (by positivity) (by positivity)
      _ = 1 := h2
  have hK : K₁ ≤ (N : ℝ) ^ δ := sc_le_rpow hK₁0 hδ hNK₁
  -- the event `Θ`
  set Θ := {ω |
            Fv Sig (X ω) z v ≤ (N : ℝ) ^ (2 * εA) * (N : ℝ) ^ (2 * δ) * scQ0 τ c ∧
            (∀ a, ‖ent (G Sig (X ω) z) (vbar Sig v) (eI a)‖ ≤
              (N : ℝ) ^ (2 * εA) * (N : ℝ) ^ (2 * δ) * scQ0 τ c) ∧
            (∀ a, ‖ent (G Sig (X ω) z) (eI a) (vbar Sig v)‖ ≤
              (N : ℝ) ^ (2 * εA) * (N : ℝ) ^ (2 * δ) * scQ0 τ c) ∧
            (∀ a b, ‖G Sig (X ω) z a b‖ ≤ (N : ℝ) ^ (2 * εA) * (N : ℝ) ^ (2 * δ) * scQ0 τ c) ∧
            (N : ℝ)⁻¹ *
              (∑ i, (‖ent (G Sig (X ω) z) (vbar Sig v) (eI (Sum.inl i))‖ +
                  ‖ent (G Sig (X ω) z) (eI (Sum.inl i)) (vbar Sig v)‖) ^ 2 +
                ∑ μ, (‖ent (G Sig (X ω) z) (vbar Sig v) (eI (Sum.inr μ))‖ +
                  ‖ent (G Sig (X ω) z) (eI (Sum.inr μ)) (vbar Sig v)‖) ^ 2) ≤
              (N : ℝ) ^ (2 * εA) * ((N : ℝ) ^ ((C₀ + 2) * δ) * Psi N (specOf Sig) z ^ 2)}
    with hΘ
  have hΘp : HighProbAt N (DA - 4) Θ := h₁ N hNN₁ M Sig S P m hset hm hA Ω X hX hP z hz v hv
  -- the random variables
  set n := ∑ r, ns r with hndef
  set Z : Ω → ℝ := fun ω => (N : ℝ) ^ (-((n : ℕ) : ℝ) / 2) *
    ∑ i, ∑ μ, ∏ r, ‖wordA Sig (X ω) z v i μ (ns r) (ws r)‖ with hZ
  set Fp : Ω → ℝ := fun ω => Fv Sig (X ω) z v ^ p with hFp
  set ξ : Ω → ℝ := fun ω => max (Z ω - Fp ω) 0 with hξ
  have hZΘ : ∀ ω ∈ Θ, Z ω ≤ Fp ω + (g * Ψ) ^ p := by
    intro ω hω
    obtain ⟨h0, h1, h2, h3, hQ⟩ := hω
    exact sc_on_event hset hzS (X ω) v hp2 ns ws hn4 hn hδ hC₀ hεA hεAδ hK hgΨ h0 h1 h2 h3 hQ
  have hgp0 : 0 ≤ (g * Ψ) ^ p := pow_nonneg (mul_nonneg (by linarith) hΨ0) p
  have hξΘ : ∀ ω ∈ Θ, ξ ω ≤ (g * Ψ) ^ p := fun ω hω =>
    max_le (by have := hZΘ ω hω; simp only [hZ, hFp] at this ⊢; linarith) hgp0
  have hdom : DomAt N 0 (DA - 4) ξ (fun _ => (g * Ψ) ^ p) := by
    unfold DomAt
    refine le_trans (measure_mono fun ω hω => ?_) hΘp
    simp only [Set.mem_ofPred_eq, Real.rpow_zero, one_mul] at hω
    intro hωΘ
    exact absurd (hξΘ ω hωΘ) (not_le.2 hω)
  -- integrability
  have hIprod : ∀ i μ, Integrable fun ω => ∏ r, ‖wordA Sig (X ω) z v i μ (ns r) (ws r)‖ :=
    fun i μ => sc_integrable_prod hset hzS hX v hv i μ ns ws hn
  have hZint : Integrable Z :=
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun μ _ => hIprod i μ).const_mul _
  have hFv := h₂ N hNN₂ M Sig X S ⟨hset.ratio_ge, hset.ratio_le, hX, hset.sigma⟩ hset.domain
    hset.oneXm z hzS v hv
  have hFint : Integrable Fp := hFv.1
  have hXm := sc_measurable_X hX
  have hZmeas : Measurable Z := by
    refine Measurable.const_mul (Finset.measurable_sum _ fun i _ =>
      Finset.measurable_sum _ fun μ _ => Finset.measurable_prod _ fun r _ => ?_) _
    exact ((sc_continuous_wordA hSig hη v i μ _ _).norm.measurable).comp hXm
  have hFmeas : Measurable Fp :=
    (((sc_continuous_Fv hSig hη v).measurable).comp hXm).pow_const p
  have hξmeas : Measurable ξ := (hZmeas.sub hFmeas).max measurable_const
  have hξ0 : ∀ ω, 0 ≤ ξ ω := fun ω => le_max_right _ _
  have hZ0 : ∀ ω, 0 ≤ Z ω := fun ω => mul_nonneg (Real.rpow_nonneg hNp.le _)
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.prod_nonneg fun _ _ => norm_nonneg _)
  have hF0 : ∀ ω, 0 ≤ Fp ω := fun ω => pow_nonneg (norm_nonneg _) p
  have hξZ : ∀ ω, ξ ω ≤ Z ω := fun ω => max_le (by linarith [hF0 ω]) (hZ0 ω)
  -- the rough bound `Z ≤ K_c W^{5p}`
  set Kc : ℝ := τ⁻¹ * (N : ℝ) ^ 2 * (R * N) ^ (5 * p) with hKc
  have hKc0 : 0 ≤ Kc := by rw [hKc]; positivity
  have hZW : ∀ ω, Z ω ≤ Kc * (1 + scSq (X ω)) ^ (5 * p) := by
    intro ω
    have hW0 : 0 ≤ 1 + scSq (X ω) := by have := scSq_nonneg (X ω); linarith
    have hNn : (N : ℝ) ^ (-((n : ℕ) : ℝ) / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hN1r (by
        have : (0 : ℝ) ≤ ((n : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith)
    have hS0 : 0 ≤ ∑ i, ∑ μ, ∏ r, ‖wordA Sig (X ω) z v i μ (ns r) (ws r)‖ :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        Finset.prod_nonneg fun _ _ => norm_nonneg _
    have hS : ∑ i, ∑ μ, ∏ r, ‖wordA Sig (X ω) z v i μ (ns r) (ws r)‖ ≤
        (M : ℝ) * N * (R * N * (1 + scSq (X ω))) ^ (5 * p) := by
      calc _ ≤ ∑ _i : Fin M, ∑ _μ : Fin N, (R * N * (1 + scSq (X ω))) ^ (5 * p) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun μ _ =>
              sc_prod_rough hset hzS (X ω) v hv i μ ns ws hn
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]; ring
    have hMN : (M : ℝ) * N ≤ τ⁻¹ * (N : ℝ) ^ 2 := by nlinarith
    calc Z ω ≤ 1 * ∑ i, ∑ μ, ∏ r, ‖wordA Sig (X ω) z v i μ (ns r) (ws r)‖ :=
          mul_le_mul_of_nonneg_right hNn hS0
      _ ≤ (M : ℝ) * N * (R * N * (1 + scSq (X ω))) ^ (5 * p) := by rw [one_mul]; exact hS
      _ ≤ τ⁻¹ * (N : ℝ) ^ 2 * (R * N * (1 + scSq (X ω))) ^ (5 * p) :=
          mul_le_mul_of_nonneg_right hMN (by positivity)
      _ = Kc * (1 + scSq (X ω)) ^ (5 * p) := by rw [hKc, mul_pow (R * N)]; ring
  obtain ⟨hW10i, hW10⟩ := sc_moment_W hτ hX hN1 hM (10 * p)
  have hξ2int : Integrable fun ω => ξ ω ^ 2 := by
    refine (hW10i.const_mul (Kc ^ 2)).mono' (hξmeas.pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    calc ξ ω ^ 2 ≤ Z ω ^ 2 := pow_le_pow_left₀ (hξ0 ω) (hξZ ω) 2
      _ ≤ (Kc * (1 + scSq (X ω)) ^ (5 * p)) ^ 2 := pow_le_pow_left₀ (hZ0 ω) (hZW ω) 2
      _ = Kc ^ 2 * (1 + scSq (X ω)) ^ (10 * p) := by ring
  set Cc : ℝ := ((20 * p + 5 : ℕ) : ℝ) with hCc
  have hξ2le : ∫ ω, ξ ω ^ 2 ≤ (N : ℝ) ^ Cc := by
    have hKzN : Kz ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hNKz)
    calc ∫ ω, ξ ω ^ 2 ≤ ∫ ω, Kc ^ 2 * (1 + scSq (X ω)) ^ (10 * p) := by
          refine integral_mono hξ2int (hW10i.const_mul _) fun ω => ?_
          calc ξ ω ^ 2 ≤ Z ω ^ 2 := pow_le_pow_left₀ (hξ0 ω) (hξZ ω) 2
            _ ≤ (Kc * (1 + scSq (X ω)) ^ (5 * p)) ^ 2 := pow_le_pow_left₀ (hZ0 ω) (hZW ω) 2
            _ = Kc ^ 2 * (1 + scSq (X ω)) ^ (10 * p) := by ring
      _ = Kc ^ 2 * ∫ ω, (1 + scSq (X ω)) ^ (10 * p) := integral_const_mul _ _
      _ ≤ Kc ^ 2 * (scKW τ C (10 * p) * (N : ℝ) ^ (10 * p)) :=
          mul_le_mul_of_nonneg_left hW10 (by positivity)
      _ = Kz * (N : ℝ) ^ (20 * p + 4) := by
          rw [hKc, hKz, mul_pow R]; ring
      _ ≤ (N : ℝ) * (N : ℝ) ^ (20 * p + 4) :=
          mul_le_mul_of_nonneg_right hKzN (by positivity)
      _ = (N : ℝ) ^ Cc := by rw [hCc, Real.rpow_natCast]; ring
  have hΓ : (N : ℝ) ^ (-Cc) ≤ (g * Ψ) ^ p := by
    have hτN : τ⁻¹ ^ p ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hNτ)
    have hNp1 : (0 : ℝ) < (N : ℝ) ^ p := by positivity
    have e1 : (N : ℝ) ^ (-Cc) = ((N : ℝ) ^ (20 * p + 5))⁻¹ := by
      rw [Real.rpow_neg hNp.le, hCc, Real.rpow_natCast]
    have h1 : (N : ℝ) ^ (p + 1) ≤ (N : ℝ) ^ (20 * p + 5) := pow_le_pow_right₀ hN1r (by omega)
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
    calc ((N : ℝ) ^ (20 * p + 5))⁻¹ ≤ ((N : ℝ) ^ (p + 1))⁻¹ :=
          inv_anti₀ (by positivity) h1
      _ ≤ _ := h4.trans (h2.trans h3)
  have hD : 3 * Cc ≤ DA - 4 := (sc_dPrev_ge p).trans (by linarith only [hDA])
  have hint := integral_le_of_domAt hN1 le_rfl hD hΓ hξ0 hξ2int hξ2le hdom
  rw [Real.rpow_zero, mul_one] at hint
  -- assembly
  have hLHS : (N : ℝ) ^ (-((n : ℕ) : ℝ) / 2) *
      ∑ i, ∑ μ, ∫ ω, ∏ r, ‖wordA Sig (X ω) z v i μ (ns r) (ws r)‖ = ∫ ω, Z ω := by
    rw [hZ, integral_const_mul, integral_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun μ _ => hIprod i μ]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun μ _ => hIprod i μ]
  have hξint : Integrable ξ := by
    refine hZint.mono' hξmeas.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (hξ0 ω)]
    exact hξZ ω
  have hZle : ∫ ω, Z ω ≤ ∫ ω, (Fp ω + ξ ω) :=
    integral_mono hZint (hFint.add hξint) fun ω => by
      have := le_max_left (Z ω - Fp ω) 0
      simp only [hξ] at this ⊢
      linarith
  rw [hLHS]
  calc ∫ ω, Z ω ≤ ∫ ω, (Fp ω + ξ ω) := hZle
    _ = (∫ ω, Fp ω) + ∫ ω, ξ ω := integral_add hFint hξint
    _ ≤ (∫ ω, Fp ω) + 2 * (g * Ψ) ^ p := by linarith
    _ = 2 * (g * Ψ) ^ p + ∫ ω, Fv Sig (X ω) z v ^ p := by rw [hFp]; ring

/-- (sc_step 6)–(sc_step 8) at a general `C₀` (`n ∈ [4, 4p]`). -/
theorem sc_step6' (τ c : ℝ) (C : ℕ → ℝ) (p : ℕ) (C₀ δ εA DA : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hc : 0 < c) (hp : Even p) (hp2 : 2 ≤ p) (hδ : 0 < δ) (hC₀ : 25 ≤ C₀)
    (hC₀δ : C₀ * δ ≤ τ / 4) (hεA : 0 < εA) (hεAδ : εA ≤ δ / 4) (hDA : dPrev p ≤ DA) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ)
      (P : ModelClass M N) (m : ℕ), CompSetting τ c M N Sig S → 1 ≤ m →
      PropA N C P Sig S C₀ δ (m - 1) εA DA →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption C X → P Ω X →
        ∀ z ∈ levelSet N δ S m, ∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 →
          ∀ (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r)), 4 ≤ ∑ r, ns r → ∑ r, ns r ≤ 4 * p →
            (N : ℝ) ^ (-((∑ r, ns r : ℕ) : ℝ) / 2) *
                ∑ i, ∑ μ, ∫ ω, ∏ r, ‖wordA Sig (X ω) z v i μ (ns r) (ws r)‖ ≤
              2 * ((N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z) ^ p +
                ∫ ω, Fv Sig (X ω) z v ^ p :=
  sc_step6_gen τ c C p C₀ δ εA DA hτ hτ1 hc hp2 hδ hC₀ hC₀δ hεA hεAδ hDA

/-! ## Lemma 7.17 -/

/-- `|T(p, n)| ≤ (n + 1)^p` for the set `T(p, n)` of `κ : Fin p → ℕ` with `∑ κ = n`. -/
private theorem sc_card_tuple (p n : ℕ) :
    ((Finset.Nat.antidiagonalTuple p n).card : ℝ) ≤ ((n : ℝ) + 1) ^ p := by
  have hsub : Finset.Nat.antidiagonalTuple p n ⊆
      Fintype.piFinset fun _ : Fin p => Finset.range (n + 1) := by
    intro κ hκ
    rw [Finset.Nat.mem_antidiagonalTuple] at hκ
    simp only [Fintype.mem_piFinset, Finset.mem_range]
    intro r
    have := Finset.single_le_sum (fun j _ => Nat.zero_le (κ j)) (Finset.mem_univ r)
    omega
  have := Finset.card_le_card hsub
  simp only [Fintype.card_piFinset, Finset.card_range, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at this
  exact_mod_cast this

/-- `|f_n| ≤ ∑_{κ ∈ T(p,n)} ∏_r b_{κ_r}` when `|a_k| ≤ b_k`. -/
private theorem sc_norm_fCoeff_le (p n : ℕ) (a : ℕ → ℂ) (b : ℕ → ℝ) (hab : ∀ k, ‖a k‖ ≤ b k) :
    ‖fCoeff p a n‖ ≤ ∑ κ ∈ Finset.Nat.antidiagonalTuple p n, ∏ r : Fin p, b (κ r) := by
  unfold fCoeff
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun κ _ => ?_)
  rw [norm_prod]
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun r _ => ?_
  split_ifs
  · exact hab _
  · rw [Complex.norm_conj]; exact hab _

/-- (sc_step 3)–(sc_step 5): `|f_n| ≤ ∑_{κ ∈ T(p,n)} ∑_{w_r ∈ 𝒲_{κ_r}} ∏_r |A(w_r)|`, from
`a_k = (−1)^k ∑_{w ∈ 𝒲_k} A(w)`. -/
private theorem sc_fCoeff_words {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M)
    (μ : Fin N) (p n : ℕ) :
    ‖fCoeff p (resCoeff Sig A z v i μ) n‖ ≤
      ∑ κ ∈ Finset.Nat.antidiagonalTuple p n, ∑ ws : (∀ r : Fin p, Word (κ r)),
        ∏ r, ‖wordA Sig A z v i μ (κ r) (ws r)‖ := by
  have hab : ∀ k, ‖resCoeff Sig A z v i μ k‖ ≤ ∑ w : Word k, ‖wordA Sig A z v i μ k w‖ := by
    intro k
    rw [resCoeff_eq_sum_wordA hSig A hz v i μ k, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
      one_mul]
    exact norm_sum_le _ _
  refine (sc_norm_fCoeff_le p n _ _ hab).trans (le_of_eq (Finset.sum_congr rfl fun κ _ => ?_))
  exact Fintype.prod_sum fun r (w : Word (κ r)) => ‖wordA Sig A z v i μ (κ r) w‖

private theorem sc_sum_swap {α β γ : Type*} [Fintype α] [Fintype β] (s : Finset γ)
    (f : α → β → γ → ℝ) : ∑ a, ∑ b, ∑ c ∈ s, f a b c = ∑ c ∈ s, ∑ a, ∑ b, f a b c := by
  calc ∑ a, ∑ b, ∑ c ∈ s, f a b c = ∑ a, ∑ c ∈ s, ∑ b, f a b c :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Lemma 7.17 (`lem:sc_step 3`) at a general `C₀` (`n ∈ [4, 4p]`). -/
theorem sc_step3' (τ c : ℝ) (C : ℕ → ℝ) (p : ℕ) (C₀ δ εA DA : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hc : 0 < c) (hp : Even p) (hp2 : 2 ≤ p) (hδ : 0 < δ) (hC₀ : 25 ≤ C₀)
    (hC₀δ : C₀ * δ ≤ τ / 4) (hεA : 0 < εA) (hεAδ : εA ≤ δ / 4) (hDA : dPrev p ≤ DA) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (S : Set ℂ) (P : ModelClass M N) (m : ℕ), CompSetting τ c M N Sig S → 1 ≤ m →
      PropA N C P Sig S C₀ δ (m - 1) εA DA →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption C X → P Ω X →
        ∀ z ∈ levelSet N δ S m, ∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 →
          ∀ n ∈ Finset.Icc 4 (4 * p), (N : ℝ) ^ (-(n : ℝ) / 2) *
            ∑ i, ∑ μ, ‖∫ ω, fCoeff p (resCoeff Sig (X ω) z v i μ) n‖ ≤
              K * (((N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z) ^ p +
                ∫ ω, Fv Sig (X ω) z v ^ p) := by
  obtain ⟨N₀, h₀⟩ := sc_step6' τ c C p C₀ δ εA DA hτ hτ1 hc hp hp2 hδ hC₀ hC₀δ hεA hεAδ hDA
  refine ⟨2 * ((((4 * p : ℕ) : ℝ) + 1) ^ p * 2 ^ (4 * p)), by positivity, N₀, ?_⟩
  intro N hN M Sig S P m hset hm hA Ω _ _ X hX hP z hz v hv n hn
  have hn' := Finset.mem_Icc.1 hn
  have hzS : z ∈ S := hz.1
  have hη : 0 < z.im := (hset.domain.1 hzS).1
  have hSig := hset.sigma.posDef
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast sc_N_pos hset
  have hNp : (0 : ℝ) < N := by linarith
  set b := ((N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z) ^ p with hbdef
  set EF := ∫ ω, Fv Sig (X ω) z v ^ p with hEFdef
  have hEF : 0 ≤ EF := integral_nonneg fun ω => pow_nonneg (norm_nonneg _) _
  have hb : 0 ≤ b := by
    have := (sc_Psi_bounds hset hzS).2.2
    have h0 : 0 ≤ Psi N (specOf Sig) z := le_trans (by have := hset.pos; positivity) this
    exact pow_nonneg (mul_nonneg (Real.rpow_nonneg hNp.le _) h0) p
  set T := Finset.Nat.antidiagonalTuple p n with hT
  have hI : ∀ κ ∈ T, ∀ (ws : ∀ r, Word (κ r)) (i : Fin M) (μ : Fin N),
      Integrable fun ω => ∏ r, ‖wordA Sig (X ω) z v i μ (κ r) (ws r)‖ := by
    intro κ hκ ws i μ
    refine sc_integrable_prod hset hzS hX v hv i μ κ ws ?_
    rw [Finset.Nat.mem_antidiagonalTuple.1 hκ]
    exact hn'.2
  have hper : ∀ i μ, ‖∫ ω, fCoeff p (resCoeff Sig (X ω) z v i μ) n‖ ≤
      ∑ κ ∈ T, ∑ ws : (∀ r : Fin p, Word (κ r)),
        ∫ ω, ∏ r, ‖wordA Sig (X ω) z v i μ (κ r) (ws r)‖ := by
    intro i μ
    have hsI : Integrable fun ω => ∑ κ ∈ T, ∑ ws : (∀ r : Fin p, Word (κ r)),
        ∏ r, ‖wordA Sig (X ω) z v i μ (κ r) (ws r)‖ :=
      integrable_finsetSum _ fun κ hκ => integrable_finsetSum _ fun ws _ => hI κ hκ ws i μ
    calc ‖∫ ω, fCoeff p (resCoeff Sig (X ω) z v i μ) n‖
        ≤ ∫ ω, ‖fCoeff p (resCoeff Sig (X ω) z v i μ) n‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ ω, ∑ κ ∈ T, ∑ ws : (∀ r : Fin p, Word (κ r)),
            ∏ r, ‖wordA Sig (X ω) z v i μ (κ r) (ws r)‖ :=
          integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hsI
            (ae_of_all _ fun ω => sc_fCoeff_words hSig (X ω) hη v i μ p n)
      _ = _ := by
          rw [integral_finsetSum _ fun κ hκ => integrable_finsetSum _ fun ws _ => hI κ hκ ws i μ]
          exact Finset.sum_congr rfl fun κ hκ =>
            integral_finsetSum _ fun ws _ => hI κ hκ ws i μ
  have hstep : ∀ κ ∈ T, ∀ ws : (∀ r : Fin p, Word (κ r)), (N : ℝ) ^ (-(n : ℝ) / 2) *
      ∑ i, ∑ μ, ∫ ω, ∏ r, ‖wordA Sig (X ω) z v i μ (κ r) (ws r)‖ ≤ 2 * b + EF := by
    intro κ hκ ws
    have hs : ∑ r, κ r = n := Finset.Nat.mem_antidiagonalTuple.1 hκ
    have := h₀ N hN M Sig S P m hset hm hA Ω X hX hP z hz v hv κ ws (by omega) (by omega)
    rwa [hs] at this
  have hcardw : ∀ κ ∈ T, (Fintype.card (∀ r : Fin p, Word (κ r)) : ℝ) = 2 ^ n := by
    intro κ hκ
    have hs : ∑ r, κ r = n := Finset.Nat.mem_antidiagonalTuple.1 hκ
    rw [Fintype.card_pi]
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    rw [Finset.prod_pow_eq_pow_sum, hs]
    norm_num
  have hNn0 : 0 ≤ (N : ℝ) ^ (-(n : ℝ) / 2) := Real.rpow_nonneg hNp.le _
  calc (N : ℝ) ^ (-(n : ℝ) / 2) * ∑ i, ∑ μ, ‖∫ ω, fCoeff p (resCoeff Sig (X ω) z v i μ) n‖
      ≤ (N : ℝ) ^ (-(n : ℝ) / 2) * ∑ i, ∑ μ, ∑ κ ∈ T, ∑ ws : (∀ r : Fin p, Word (κ r)),
          ∫ ω, ∏ r, ‖wordA Sig (X ω) z v i μ (κ r) (ws r)‖ := by
        gcongr with i _ μ _
        exact hper i μ
    _ = ∑ κ ∈ T, ∑ ws : (∀ r : Fin p, Word (κ r)), (N : ℝ) ^ (-(n : ℝ) / 2) *
          ∑ i, ∑ μ, ∫ ω, ∏ r, ‖wordA Sig (X ω) z v i μ (κ r) (ws r)‖ := by
        rw [sc_sum_swap, Finset.mul_sum]
        refine Finset.sum_congr rfl fun κ _ => ?_
        rw [sc_sum_swap Finset.univ, Finset.mul_sum]
    _ ≤ ∑ κ ∈ T, ∑ _ws : (∀ r : Fin p, Word (κ r)), (2 * b + EF) :=
        Finset.sum_le_sum fun κ hκ => Finset.sum_le_sum fun ws _ => hstep κ hκ ws
    _ = ∑ _κ ∈ T, 2 ^ n * (2 * b + EF) := by
        refine Finset.sum_congr rfl fun κ hκ => ?_
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardw κ hκ]
    _ = (T.card : ℝ) * 2 ^ n * (2 * b + EF) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ (((4 * p : ℕ) : ℝ) + 1) ^ p * 2 ^ (4 * p) * (2 * (b + EF)) := by
        have h1 : (T.card : ℝ) ≤ (((4 * p : ℕ) : ℝ) + 1) ^ p := by
          refine (sc_card_tuple p n).trans (pow_le_pow_left₀ (by positivity) ?_ p)
          have : (n : ℝ) ≤ ((4 * p : ℕ) : ℝ) := by exact_mod_cast hn'.2
          linarith
        have h2 : (2 : ℝ) ^ n ≤ 2 ^ (4 * p) := pow_le_pow_right₀ (by norm_num) hn'.2
        have h3 : 2 * b + EF ≤ 2 * (b + EF) := by linarith
        gcongr
    _ = 2 * ((((4 * p : ℕ) : ℝ) + 1) ^ p * 2 ^ (4 * p)) * (b + EF) := by ring

/-! ## Instances of the statements -/

-- `sc_step6'` at `τ = 1/2`, `c = 1`, `C_q = 2`, `p = 2`, `C₀ = 25`, `δ = 1/200`, `ε_A = 1/800`,
-- `D_A = dPrev 2`; the hypotheses on `N, Σ, X, z, v` and the words stay as binders.
example :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ)
      (P : ModelClass M N) (m : ℕ), CompSetting (1 / 2) 1 M N Sig S → 1 ≤ m →
      PropA N (fun _ => 2) P Sig S 25 (1 / 200) (m - 1) (1 / 800) (dPrev 2) →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption (fun _ => 2) X → P Ω X →
        ∀ z ∈ levelSet N (1 / 200) S m, ∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 →
          ∀ (ns : Fin 2 → ℕ) (ws : ∀ r, Word (ns r)), 4 ≤ ∑ r, ns r → ∑ r, ns r ≤ 4 * 2 →
            (N : ℝ) ^ (-((∑ r, ns r : ℕ) : ℝ) / 2) *
                ∑ i, ∑ μ, ∫ ω, ∏ r, ‖wordA Sig (X ω) z v i μ (ns r) (ws r)‖ ≤
              2 * ((N : ℝ) ^ (25 * (1 / 200) : ℝ) * Psi N (specOf Sig) z) ^ 2 +
                ∫ ω, Fv Sig (X ω) z v ^ 2 :=
  sc_step6' (1 / 2) 1 (fun _ => 2) 2 25 (1 / 200) (1 / 800) (dPrev 2) (by norm_num) (by norm_num)
    (by norm_num) even_two le_rfl (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num) le_rfl

-- `sc_step3'` at `τ = 1/2`, `c = 1`, `C_q = 2`, `p = 2`, `C₀ = 25`, `δ = 1/200`, `ε_A = 1/800`,
-- `D_A = dPrev 2`; the hypotheses on `N, Σ, X, z, v` stay as binders.
example :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (S : Set ℂ) (P : ModelClass M N) (m : ℕ), CompSetting (1 / 2) 1 M N Sig S → 1 ≤ m →
      PropA N (fun _ => 2) P Sig S 25 (1 / 200) (m - 1) (1 / 800) (dPrev 2) →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption (fun _ => 2) X → P Ω X →
        ∀ z ∈ levelSet N (1 / 200) S m, ∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 →
          ∀ n ∈ Finset.Icc 4 (4 * 2 : ℕ), (N : ℝ) ^ (-(n : ℝ) / 2) *
            ∑ i, ∑ μ, ‖∫ ω, fCoeff 2 (resCoeff Sig (X ω) z v i μ) n‖ ≤
              K * (((N : ℝ) ^ (25 * (1 / 200) : ℝ) * Psi N (specOf Sig) z) ^ 2 +
                ∫ ω, Fv Sig (X ω) z v ^ 2) :=
  sc_step3' (1 / 2) 1 (fun _ => 2) 2 25 (1 / 200) (1 / 800) (dPrev 2) (by norm_num) (by norm_num)
    (by norm_num) even_two le_rfl (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num) le_rfl

end Anisotropic

#print axioms Anisotropic.sc_step6'
#print axioms Anisotropic.sc_step3'
