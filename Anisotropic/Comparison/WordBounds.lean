module

public import Anisotropic.Comparison.RoughBound
public import Anisotropic.Comparison.Words
public import Anisotropic.LinAlg.Ward

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # Lemma 7.20, (A_rough), (bound_sum_im), pigeonhole, Young -/

/-- (w_est_2): for `n(w) ≥ 1`, `|A(w)| ≤ (R_i² + R_μ²) B^{n(w)−1}`, `R_s = |G_{v̄s}| + |G_{sv̄}|`. -/
theorem wordA_le_R {Sig : Matrix (Fin M) (Fin M) ℝ} (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) {B : ℝ} (hB : 0 ≤ B)
    (h3 : ∀ b b', ‖G Sig A z (letterS i μ b) (letterT i μ b')‖ ≤ B) (n : ℕ) (w : Word (n + 1)) :
    ‖wordA Sig A z v i μ (n + 1) w‖ ≤
      ((‖ent (G Sig A z) (vbar Sig v) (eI (Sum.inl i))‖ +
          ‖ent (G Sig A z) (eI (Sum.inl i)) (vbar Sig v)‖) ^ 2 +
        (‖ent (G Sig A z) (vbar Sig v) (eI (Sum.inr μ))‖ +
          ‖ent (G Sig A z) (eI (Sum.inr μ)) (vbar Sig v)‖) ^ 2) * B ^ n := by
  set x := ‖ent (G Sig A z) (vbar Sig v) (eI (Sum.inl i))‖ +
    ‖ent (G Sig A z) (eI (Sum.inl i)) (vbar Sig v)‖ with hx
  set y := ‖ent (G Sig A z) (vbar Sig v) (eI (Sum.inr μ))‖ +
    ‖ent (G Sig A z) (eI (Sum.inr μ)) (vbar Sig v)‖ with hy
  have hx0 : 0 ≤ x := by positivity
  have hy0 : 0 ≤ y := by positivity
  have hfirst : ∀ b, ‖ent (G Sig A z) (vbar Sig v) (eI (letterT i μ b))‖ ≤
      if b then x else y := by
    intro b
    cases b
    · simp only [letterT, Bool.false_eq_true, ite_false, hy]
      exact le_add_of_nonneg_right (norm_nonneg _)
    · simp only [letterT, ite_true, hx]
      exact le_add_of_nonneg_right (norm_nonneg _)
  have hlast : ∀ b, ‖ent (G Sig A z) (eI (letterS i μ b)) (vbar Sig v)‖ ≤
      if b then y else x := by
    intro b
    cases b
    · simp only [letterS, Bool.false_eq_true, ite_false, hx]
      exact le_add_of_nonneg_left (norm_nonneg _)
    · simp only [letterS, ite_true, hy]
      exact le_add_of_nonneg_left (norm_nonneg _)
  have hmid : ‖∏ l : Fin n, G Sig A z (letterS i μ (w l.castSucc)) (letterT i μ (w l.succ))‖ ≤
      B ^ n := by
    rw [norm_prod]
    have := Finset.prod_le_prod₀ (s := (Finset.univ : Finset (Fin n)))
      (f := fun l => ‖G Sig A z (letterS i μ (w l.castSucc)) (letterT i μ (w l.succ))‖)
      (g := fun _ => B) (fun l _ => norm_nonneg _) fun l _ => h3 _ _
    simpa using this
  unfold wordA
  rw [norm_mul, norm_mul]
  have hcore : ‖ent (G Sig A z) (vbar Sig v) (eI (letterT i μ (w 0)))‖ *
      ‖ent (G Sig A z) (eI (letterS i μ (w (Fin.last n)))) (vbar Sig v)‖ ≤ x ^ 2 + y ^ 2 := by
    have h1 := hfirst (w 0)
    have h2 := hlast (w (Fin.last n))
    have hf0 := norm_nonneg (ent (G Sig A z) (vbar Sig v) (eI (letterT i μ (w 0))))
    have hl0 := norm_nonneg (ent (G Sig A z) (eI (letterS i μ (w (Fin.last n)))) (vbar Sig v))
    have h12 := mul_le_mul h1 h2 hl0 (by split_ifs <;> assumption)
    refine h12.trans ?_
    split_ifs <;> nlinarith [sq_nonneg (x - y)]
  calc _ = (‖ent (G Sig A z) (vbar Sig v) (eI (letterT i μ (w 0)))‖ *
        ‖ent (G Sig A z) (eI (letterS i μ (w (Fin.last n)))) (vbar Sig v)‖) *
        ‖∏ l : Fin n, G Sig A z (letterS i μ (w l.castSucc)) (letterT i μ (w l.succ))‖ := by ring
    _ ≤ _ := mul_le_mul hcore hmid (norm_nonneg _) (by positivity)

/-- (w_est_1): for `n(w) = 1`, `|A(w)| ≤ R_i R_μ` (since `t_1 ≠ s_2`). -/
theorem wordA_one_le {Sig : Matrix (Fin M) (Fin M) ℝ} (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) (w : Word 1) :
    ‖wordA Sig A z v i μ 1 w‖ ≤
      (‖ent (G Sig A z) (vbar Sig v) (eI (Sum.inl i))‖ +
          ‖ent (G Sig A z) (eI (Sum.inl i)) (vbar Sig v)‖) *
        (‖ent (G Sig A z) (vbar Sig v) (eI (Sum.inr μ))‖ +
          ‖ent (G Sig A z) (eI (Sum.inr μ)) (vbar Sig v)‖) := by
  have h0 : (Fin.last 0 : Fin 1) = 0 := rfl
  unfold wordA
  simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one, h0, norm_mul]
  cases w 0
  · simp only [letterT, letterS, Bool.false_eq_true, ite_false]
    rw [mul_comm]
    exact mul_le_mul (le_add_of_nonneg_left (norm_nonneg _))
      (le_add_of_nonneg_right (norm_nonneg _)) (norm_nonneg _) (by positivity)
  · simp only [letterT, letterS, ite_true]
    exact mul_le_mul (le_add_of_nonneg_right (norm_nonneg _))
      (le_add_of_nonneg_left (norm_nonneg _)) (norm_nonneg _) (by positivity)


/-! ## Helpers -/

private theorem wb_ent_add {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (v w : ι → ℝ) :
    ent (A + B) v w = ent A v w + ent B v w := by
  simp [ent, add_mulVec, dotProduct_add]

private theorem wb_ent_sub {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (v w : ι → ℝ) :
    ent (A - B) v w = ent A v w - ent B v w := by
  simp [ent, sub_mulVec, dotProduct_sub]

private theorem wb_ent_cplx {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (v w : ι → ℝ) :
    ent (cplx A) v w = ((v ⬝ᵥ A *ᵥ w : ℝ) : ℂ) := by
  simp [ent, cplx, dotProduct, mulVec, Complex.ofReal_sum, Complex.ofReal_mul]

/-- `Σ = U diag(σ) Uᵀ` with `U` orthogonal and `σ = specOf Σ > 0`. -/
private theorem wb_diag {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) :
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

/-- `|Uᵀ x| = |x|` for orthogonal `U`. -/
private theorem wb_sum_sq_UT {K : ℕ} {U : Matrix (Fin K) (Fin K) ℝ} (h₂ : U * Uᵀ = 1)
    (x : Fin K → ℝ) : ∑ i, (Uᵀ *ᵥ x) i ^ 2 = ∑ i, x i ^ 2 := by
  have e : (Uᵀ *ᵥ x) ⬝ᵥ (Uᵀ *ᵥ x) = x ⬝ᵥ x := by
    rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, h₂, one_mulVec, dotProduct_comm]
  simpa [dotProduct, sq] using e

/-- `(1 + w Σ)⁻¹ = U diag((1 + σᵢ w)⁻¹) Uᵀ` when every `1 + σᵢ w ≠ 0`. -/
private theorem wb_cinv_eq {Sig U : Matrix (Fin M) (Fin M) ℝ} {σ : Fin M → ℝ}
    (h₂ : U * Uᵀ = 1) (h₁ : Uᵀ * U = 1) (hS : Sig = U * diagonal σ * Uᵀ) {w : ℂ}
    (hw : ∀ i, 1 + (σ i : ℂ) * w ≠ 0) :
    (1 + w • cplx Sig)⁻¹ =
      (cplx Uᵀ)ᵀ * diagonal (fun i => (1 + (σ i : ℂ) * w)⁻¹) * cplx Uᵀ := by
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

/-- The block `−Σ(1 + wΣ)⁻¹` of `Π` in the eigenbasis of `Σ`. -/
private theorem wb_piBlock_eq {Sig U : Matrix (Fin M) (Fin M) ℝ} {σ : Fin M → ℝ}
    (h₂ : U * Uᵀ = 1) (h₁ : Uᵀ * U = 1) (hS : Sig = U * diagonal σ * Uᵀ) {w : ℂ}
    (hw : ∀ i, 1 + (σ i : ℂ) * w ≠ 0) :
    -(cplx Sig * (1 + w • cplx Sig)⁻¹) =
      (cplx Uᵀ)ᵀ * diagonal (fun i => -((σ i : ℂ) * (1 + (σ i : ℂ) * w)⁻¹)) * cplx Uᵀ := by
  have c₁ : cplx Uᵀ * (cplx Uᵀ)ᵀ = 1 := by
    simp only [cplx]
    rw [← transpose_map, transpose_transpose, ← Matrix.map_mul, h₁,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have e1 : cplx Sig = (cplx Uᵀ)ᵀ * diagonal (fun i => (σ i : ℂ)) * cplx Uᵀ := by
    simp only [cplx]
    rw [hS, ← transpose_map, transpose_transpose, Matrix.map_mul, Matrix.map_mul,
      diagonal_map (map_zero _)]
    rfl
  rw [wb_cinv_eq h₂ h₁ hS hw, e1]
  calc -((cplx Uᵀ)ᵀ * diagonal (fun i => (σ i : ℂ)) * cplx Uᵀ *
        ((cplx Uᵀ)ᵀ * diagonal (fun i => (1 + (σ i : ℂ) * w)⁻¹) * cplx Uᵀ))
      = -((cplx Uᵀ)ᵀ * (diagonal (fun i => (σ i : ℂ)) * (cplx Uᵀ * (cplx Uᵀ)ᵀ) *
          diagonal (fun i => (1 + (σ i : ℂ) * w)⁻¹)) * cplx Uᵀ) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [c₁, Matrix.mul_one, diagonal_mul_diagonal, ← Matrix.neg_mul, ← Matrix.mul_neg,
          ← diagonal_neg]

/-- `⟨a, diag(P, Q) b⟩ = ⟨a_M, P b_M⟩ + ⟨a_N, Q b_N⟩`. -/
private theorem wb_ent_blocks (P : Matrix (Fin M) (Fin M) ℂ) (Q : Matrix (Fin N) (Fin N) ℂ)
    (a b : Fin M ⊕ Fin N → ℝ) :
    ent (fromBlocks P 0 0 Q) a b = ent P (a ∘ Sum.inl) (b ∘ Sum.inl) +
      ent Q (a ∘ Sum.inr) (b ∘ Sum.inr) := by
  simp only [ent, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, zero_mulVec, add_zero, zero_add]
  rfl

/-- `Π_{xy} = ∑ᵢ pᵢ qᵢ (−σᵢ/(1 + σᵢ w)) + w ⟨x_N, y_N⟩` with `p = Uᵀ x_M`, `q = Uᵀ y_M`. -/
private theorem wb_pi_coord {Sig U : Matrix (Fin M) (Fin M) ℝ} {σ : Fin M → ℝ}
    (h₂ : U * Uᵀ = 1) (h₁ : Uᵀ * U = 1) (hS : Sig = U * diagonal σ * Uᵀ) {w : ℂ}
    (hw : ∀ i, 1 + (σ i : ℂ) * w ≠ 0) (x y : Fin M ⊕ Fin N → ℝ) :
    ent (piMat (N := N) Sig w) x y =
      ∑ i, (((Uᵀ *ᵥ (x ∘ Sum.inl)) i * (Uᵀ *ᵥ (y ∘ Sum.inl)) i : ℝ) : ℂ) *
          (-((σ i : ℂ) * (1 + (σ i : ℂ) * w)⁻¹)) +
        w * ∑ μ, ((x (Sum.inr μ) * y (Sum.inr μ) : ℝ) : ℂ) := by
  rw [piMat, wb_ent_blocks, wb_piBlock_eq h₂ h₁ hS hw]
  congr 1
  · change testBilin _ _ _ = _
    rw [testBilin_conj]
    simp only [testBilin, mulVec_diagonal, dotProduct, Complex.ofReal_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  · simp only [ent, smul_mulVec, one_mulVec, dotProduct, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, Complex.ofReal_mul]
    exact Finset.sum_congr rfl fun μ _ => by simp only [cvec, Function.comp_apply]; ring

/-- `⟨x, diag(Σ, 0) y⟩ = ∑ᵢ σᵢ pᵢ qᵢ`. -/
private theorem wb_real_coord {Sig U : Matrix (Fin M) (Fin M) ℝ} {σ : Fin M → ℝ}
    (hS : Sig = U * diagonal σ * Uᵀ) (x y : Fin M ⊕ Fin N → ℝ) :
    x ⬝ᵥ fromBlocks Sig 0 0 (0 : Matrix (Fin N) (Fin N) ℝ) *ᵥ y =
      ∑ i, σ i * ((Uᵀ *ᵥ (x ∘ Sum.inl)) i * (Uᵀ *ᵥ (y ∘ Sum.inl)) i) := by
  have e : x ⬝ᵥ fromBlocks Sig 0 0 (0 : Matrix (Fin N) (Fin N) ℝ) *ᵥ y =
      (x ∘ Sum.inl) ⬝ᵥ Sig *ᵥ (y ∘ Sum.inl) := by
    simp only [fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl,
      Sum.elim_inr, zero_mulVec, add_zero, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
    rfl
  rw [e, hS, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
  simp only [dotProduct, mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `|Σ̲ x|² = |Uᵀ Σ x_M|² + |x_N|²` and `(Uᵀ Σ x_M)ᵢ = σᵢ (Uᵀ x_M)ᵢ`. -/
private theorem wb_testNorm_SigU {Sig U : Matrix (Fin M) (Fin M) ℝ} {σ : Fin M → ℝ}
    (h₂ : U * Uᵀ = 1) (h₁ : Uᵀ * U = 1) (hS : Sig = U * diagonal σ * Uᵀ)
    (x : Fin M ⊕ Fin N → ℝ) :
    testNorm (SigU (n := Fin N) Sig *ᵥ x) =
      √(∑ i, (σ i * (Uᵀ *ᵥ (x ∘ Sum.inl)) i) ^ 2 + ∑ μ, x (Sum.inr μ) ^ 2) := by
  have e : ∀ i, σ i * (Uᵀ *ᵥ (x ∘ Sum.inl)) i = (Uᵀ *ᵥ (Sig *ᵥ (x ∘ Sum.inl))) i := by
    intro i
    rw [hS, mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h₁, Matrix.one_mul,
      ← mulVec_mulVec, mulVec_diagonal]
  simp only [e, wb_sum_sq_UT h₂]
  unfold testNorm
  congr 1
  simp only [SigU, fromBlocks_mulVec, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    zero_mulVec, add_zero, zero_add, one_mulVec]
  rfl

/-- `|−⟨x, diag(Σ, 0) y⟩ − Π_{xy}| ≤ K max(c⁻¹, 1) |Σ̲x| |Σ̲y|` when `|w| ≤ K` and
`|1 + σᵢ w| ≥ c`. -/
private theorem wb_pi_part {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {c K : ℝ}
    (hc : 0 < c) {w : ℂ} (hwK : ‖w‖ ≤ K) (hOne : ∀ i, c ≤ ‖1 + (specOf Sig i : ℂ) * w‖)
    (x y : Fin M ⊕ Fin N → ℝ) :
    ‖-((x ⬝ᵥ fromBlocks Sig 0 0 (0 : Matrix (Fin N) (Fin N) ℝ) *ᵥ y : ℝ) : ℂ) -
        ent (piMat (N := N) Sig w) x y‖ ≤
      K * max c⁻¹ 1 * testNorm (SigU (n := Fin N) Sig *ᵥ x) *
        testNorm (SigU (n := Fin N) Sig *ᵥ y) := by
  obtain ⟨U, h₂, h₁, hSd, hσ⟩ := wb_diag hSig
  set σ := specOf Sig with hσdef
  have hw0 : ∀ i, 1 + (σ i : ℂ) * w ≠ 0 := fun i h0 => by
    have := hOne i
    rw [h0, norm_zero] at this
    linarith
  set p := Uᵀ *ᵥ (x ∘ Sum.inl) with hp
  set q := Uᵀ *ᵥ (y ∘ Sum.inl) with hq
  have hK : 0 ≤ K := (norm_nonneg w).trans hwK
  set κ := max c⁻¹ 1 with hκ
  have hκ1 : 1 ≤ κ := le_max_right _ _
  have hκc : c⁻¹ ≤ κ := le_max_left _ _
  rw [wb_pi_coord h₂ h₁ hSd hw0, wb_real_coord hSd, wb_testNorm_SigU h₂ h₁ hSd,
    wb_testNorm_SigU h₂ h₁ hSd]
  -- the remainder as a sum of eigen-coordinates
  have e : -(((∑ i, σ i * (p i * q i) : ℝ)) : ℂ) -
      (∑ i, ((p i * q i : ℝ) : ℂ) * (-((σ i : ℂ) * (1 + (σ i : ℂ) * w)⁻¹)) +
        w * ∑ μ, ((x (Sum.inr μ) * y (Sum.inr μ) : ℝ) : ℂ)) =
      ∑ i, (((σ i * p i) * (σ i * q i) : ℝ) : ℂ) * (-(w * (1 + (σ i : ℂ) * w)⁻¹)) +
        (-w) * ∑ μ, ((x (Sum.inr μ) * y (Sum.inr μ) : ℝ) : ℂ) := by
    have ht : ∀ i, -(((σ i * (p i * q i) : ℝ)) : ℂ) -
        ((p i * q i : ℝ) : ℂ) * (-((σ i : ℂ) * (1 + (σ i : ℂ) * w)⁻¹)) =
        (((σ i * p i) * (σ i * q i) : ℝ) : ℂ) * (-(w * (1 + (σ i : ℂ) * w)⁻¹)) := by
      intro i
      have := hw0 i
      push_cast
      field_simp
      ring
    rw [Complex.ofReal_sum, ← Finset.sum_congr rfl fun i _ => ht i, Finset.sum_sub_distrib,
      Finset.sum_neg_distrib]
    ring
  rw [e]
  have h1 : ∀ i, ‖(((σ i * p i) * (σ i * q i) : ℝ) : ℂ) * (-(w * (1 + (σ i : ℂ) * w)⁻¹))‖ ≤
      K * κ * (|σ i * p i| * |σ i * q i|) := by
    intro i
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, norm_neg, norm_mul, norm_inv]
    have hpos : 0 < ‖1 + (σ i : ℂ) * w‖ := hc.trans_le (hOne i)
    have hinv : ‖1 + (σ i : ℂ) * w‖⁻¹ ≤ κ := (inv_anti₀ hc (hOne i)).trans hκc
    have : ‖w‖ * ‖1 + (σ i : ℂ) * w‖⁻¹ ≤ K * κ :=
      mul_le_mul hwK hinv (inv_nonneg.2 hpos.le) hK
    nlinarith [mul_nonneg (abs_nonneg (σ i * p i)) (abs_nonneg (σ i * q i))]
  have h2 : ‖(-w) * ∑ μ, ((x (Sum.inr μ) * y (Sum.inr μ) : ℝ) : ℂ)‖ ≤
      K * κ * ∑ μ, |x (Sum.inr μ)| * |y (Sum.inr μ)| := by
    rw [norm_mul, norm_neg]
    have hs : ‖∑ μ, ((x (Sum.inr μ) * y (Sum.inr μ) : ℝ) : ℂ)‖ ≤
        ∑ μ, |x (Sum.inr μ)| * |y (Sum.inr μ)| := by
      refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun μ _ => ?_))
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
    have hs0 : 0 ≤ ∑ μ, |x (Sum.inr μ)| * |y (Sum.inr μ)| :=
      Finset.sum_nonneg fun μ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hwκ : ‖w‖ ≤ K * κ := hwK.trans (le_mul_of_one_le_right hK hκ1)
    exact mul_le_mul hwκ hs (norm_nonneg _) (by positivity)
  -- Cauchy–Schwarz on `Fin M ⊕ Fin N`
  set f : Fin M ⊕ Fin N → ℝ := Sum.elim (fun i => |σ i * p i|) (fun μ => |x (Sum.inr μ)|)
  set g : Fin M ⊕ Fin N → ℝ := Sum.elim (fun i => |σ i * q i|) (fun μ => |y (Sum.inr μ)|)
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ f g
  simp only [f, g, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, sq_abs] at hcs
  calc _ ≤ ‖∑ i, (((σ i * p i) * (σ i * q i) : ℝ) : ℂ) * (-(w * (1 + (σ i : ℂ) * w)⁻¹))‖ +
        ‖(-w) * ∑ μ, ((x (Sum.inr μ) * y (Sum.inr μ) : ℝ) : ℂ)‖ := norm_add_le _ _
    _ ≤ ∑ i, K * κ * (|σ i * p i| * |σ i * q i|) +
        K * κ * ∑ μ, |x (Sum.inr μ)| * |y (Sum.inr μ)| :=
        add_le_add ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => h1 i)) h2
    _ = K * κ * (∑ i, |σ i * p i| * |σ i * q i| +
        ∑ μ, |x (Sum.inr μ)| * |y (Sum.inr μ)|) := by rw [← Finset.mul_sum]; ring
    _ ≤ _ := by
        rw [mul_assoc (K * κ)]
        exact mul_le_mul_of_nonneg_left hcs (by positivity)

/-- (Lemma 4.10 input) The setting of §7 gives the density assumptions on `specOf Σ`. -/
private theorem wb_density {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) : DensityAssumptions τ N (specOf Sig) :=
  (IsModel.diagModel_specOf (Ω := GaussSpace M N)
    ⟨hset.ratio_ge, hset.ratio_le, (gaussX_isGaussianEnsemble M N).entryAssumption hN,
      hset.sigma⟩).densityAssumptions hset.pos

/-- `Σ̲ v̄ = v`. -/
private theorem wb_SigU_vbar {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (v : Fin M ⊕ Fin N → ℝ) : SigU (n := Fin N) Sig *ᵥ vbar Sig v = v := by
  have hS : Sig * Sig⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hSig.isUnit)
  funext s
  rcases s with i | μ
  · simp [SigU, vbar, fromBlocks_mulVec, mulVec_mulVec, hS]
  · simp [SigU, vbar, fromBlocks_mulVec]

/-- `|⟨x, y⟩| ≤ |x| |y|` for real test vectors. -/
private theorem wb_dot_le {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    |x ⬝ᵥ y| ≤ testNorm x * testNorm y := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun s => |x s|) (fun s => |y s|)
  simp only [sq_abs] at h
  unfold testNorm
  calc |x ⬝ᵥ y| = |∑ s, x s * y s| := rfl
    _ ≤ ∑ s, |x s * y s| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s, |x s| * |y s| := by simp [abs_mul]
    _ ≤ _ := h

/-- `√(x ⬝ x) = |x|`. -/
private theorem wb_sqrt_dot {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    Real.sqrt (x ⬝ᵥ x) = testNorm x := by
  unfold testNorm
  congr 1
  simp [dotProduct, sq]

/-- `|e_s| = 1`. -/
private theorem wb_testNorm_eI {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ι) :
    testNorm (eI s) = 1 := by
  unfold testNorm eI
  simp [Pi.single_apply]

/-- `Σ̲ = diag(Σ, 1)` is symmetric. -/
private theorem wb_SigU_transpose {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) :
    (SigU (n := Fin N) Sig)ᵀ = SigU (n := Fin N) Sig := by
  have hS : Sigᵀ = Sig := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact hSig.1.eq
  unfold SigU
  rw [fromBlocks_transpose]
  simp [hS]

/-- `⟨x, Σ̲ y⟩ = ⟨Σ̲ x, y⟩`. -/
private theorem wb_dot_SigU {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (x y : Fin M ⊕ Fin N → ℝ) :
    x ⬝ᵥ SigU (n := Fin N) Sig *ᵥ y = (SigU (n := Fin N) Sig *ᵥ x) ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, wb_SigU_transpose hSig]

/-- `|Σ̲ x| ≤ τ⁻¹ |x|` under (bound_Sigma) and `τ ≤ 1`. -/
private theorem wb_SigU_le {τ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hS : SigmaAssumption τ Sig) (hτ1 : τ ≤ 1) (hτ : 0 < τ) (x : Fin M ⊕ Fin N → ℝ) :
    testNorm (SigU (n := Fin N) Sig *ᵥ x) ≤ τ⁻¹ * testNorm x := by
  obtain ⟨U, h₂, h₁, hSd, hσ⟩ := wb_diag hS.posDef
  have hle : ∀ i, specOf Sig i ≤ τ⁻¹ := fun i => by
    rw [specOf_eq hS.posDef.isHermitian]; exact hS.eigenvalues_le i
  have ht1 : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  have ht0 : 0 ≤ τ⁻¹ := by linarith
  rw [wb_testNorm_SigU h₂ h₁ hSd]
  unfold testNorm
  rw [show τ⁻¹ * Real.sqrt (∑ s, x s ^ 2) = Real.sqrt (τ⁻¹ ^ 2 * ∑ s, x s ^ 2) by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq ht0]]
  refine Real.sqrt_le_sqrt ?_
  simp only [Fintype.sum_sum_type]
  have h3 : ∑ i, (specOf Sig i * (Uᵀ *ᵥ (x ∘ Sum.inl)) i) ^ 2 ≤
      τ⁻¹ ^ 2 * ∑ i, x (Sum.inl i) ^ 2 := by
    rw [show ∑ i, x (Sum.inl i) ^ 2 = ∑ i, (Uᵀ *ᵥ (x ∘ Sum.inl)) i ^ 2 from
      (wb_sum_sq_UT h₂ (x ∘ Sum.inl)).symm, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (hσ i).le (hle i) 2) (sq_nonneg _)
  have h4 : ∑ μ, x (Sum.inr μ) ^ 2 ≤ τ⁻¹ ^ 2 * ∑ μ, x (Sum.inr μ) ^ 2 := by
    refine le_mul_of_one_le_left (Finset.sum_nonneg fun _ _ => sq_nonneg _) ?_
    nlinarith
  linarith

/-- `‖Σ‖ ≤ |τ⁻¹|` for the operator norm, from the eigenvalue bound of `Σ`. -/
private theorem wb_opNorm_Sig_le {τ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hS : SigmaAssumption τ Sig) : ‖Sig‖ ≤ |τ⁻¹| := by
  obtain ⟨U, h₂, h₁, hSd, hσ⟩ := wb_diag hS.posDef
  have hle : ∀ i, specOf Sig i ≤ |τ⁻¹| := fun i => by
    rw [specOf_eq hS.posDef.isHermitian]; exact (hS.eigenvalues_le i).trans (le_abs_self _)
  generalize specOf Sig = σ at hSd hσ hle
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  refine (Matrix.toEuclideanCLM (n := Fin M) (𝕜 := ℝ) Sig).opNorm_le_bound (abs_nonneg _)
    fun x => ?_
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [Matrix.ofLp_toEuclideanCLM, Real.norm_eq_abs, sq_abs, sq_abs]
  have e : ∀ i, σ i * (Uᵀ *ᵥ x.ofLp) i = (Uᵀ *ᵥ (Sig *ᵥ x.ofLp)) i := by
    intro i
    rw [hSd, mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h₁, Matrix.one_mul,
      ← mulVec_mulVec, mulVec_diagonal]
  rw [← wb_sum_sq_UT h₂ (Sig *ᵥ x.ofLp), ← wb_sum_sq_UT h₂ x.ofLp, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← e i, mul_pow]
  have := pow_le_pow_left₀ (hσ i).le (hle i) 2
  rw [sq_abs] at this
  exact mul_le_mul_of_nonneg_right this (sq_nonneg _)

/-- `cplx` of `Σ̲` is invertible, with the block-diagonal inverse. -/
private theorem wb_cplx_SigU_inv {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) :
    cplx (SigU (n := Fin N) Sig) * cplx (SigU (n := Fin N) Sig)⁻¹ = 1 ∧
      cplx (SigU (n := Fin N) Sig)⁻¹ * cplx (SigU (n := Fin N) Sig) = 1 := by
  have hS : Sig * Sig⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hSig.isUnit)
  have hS' : Sig⁻¹ * Sig = 1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hSig.isUnit)
  have h1 : SigU (n := Fin N) Sig * fromBlocks Sig⁻¹ 0 0 1 = 1 := by
    rw [SigU, fromBlocks_multiply]
    simp [hS]
  have h2 : fromBlocks Sig⁻¹ 0 0 (1 : Matrix (Fin N) (Fin N) ℝ) * SigU (n := Fin N) Sig = 1 := by
    rw [SigU, fromBlocks_multiply]
    simp [hS']
  have c1 : cplx (SigU (n := Fin N) Sig) *
      cplx (fromBlocks Sig⁻¹ 0 0 (1 : Matrix (Fin N) (Fin N) ℝ)) = 1 := by
    simp only [cplx]
    rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have c2 : cplx (fromBlocks Sig⁻¹ 0 0 (1 : Matrix (Fin N) (Fin N) ℝ)) *
      cplx (SigU (n := Fin N) Sig) = 1 := by
    simp only [cplx]
    rw [← Matrix.map_mul, h2, Matrix.map_one _ (map_zero _) (map_one _)]
  have hinv : (SigU (n := Fin N) Sig)⁻¹ = fromBlocks Sig⁻¹ 0 0 (1 : Matrix (Fin N) (Fin N) ℝ) :=
    Matrix.inv_eq_right_inv h1
  rw [hinv]
  exact ⟨c1, c2⟩

/-- `ent` is symmetric under transposition of the matrix. -/
private theorem wb_ent_symm {ι : Type*} [Fintype ι] (B : Matrix ι ι ℂ) (x y : ι → ℝ) :
    ent B x y = ent Bᵀ y x := by
  unfold ent
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, dotProduct_comm]
  rfl

/-- `cplx` commutes with `*ᵥ` on complexified vectors. -/
private theorem wb_cvec_mulVec {ι : Type*} [Fintype ι] (Q : Matrix ι ι ℝ) (a : ι → ℝ) :
    cvec (Q *ᵥ a) = cplx Q *ᵥ cvec a := by
  ext s
  simp [cplx, cvec, Matrix.mulVec, dotProduct]

/-- `(G + Σ̲)_{ab} = (Σ̲⁻¹(G + Σ̲)Σ̲⁻¹)_{Σ̲a, Σ̲b}`. -/
private theorem wb_ent_G_add_u {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (a b : Fin M ⊕ Fin N → ℝ) :
    ent (G Sig A z + cplx (SigU (n := Fin N) Sig)) a b =
      ent (cplx (SigU (n := Fin N) Sig)⁻¹ * (G Sig A z + cplx (SigU (n := Fin N) Sig)) *
        cplx (SigU (n := Fin N) Sig)⁻¹)
        (SigU (n := Fin N) Sig *ᵥ a) (SigU (n := Fin N) Sig *ᵥ b) := by
  obtain ⟨hu, hV⟩ := wb_cplx_SigU_inv (N := N) hSig
  set u := cplx (SigU (n := Fin N) Sig) with hudef
  set V := cplx (SigU (n := Fin N) Sig)⁻¹ with hVdef
  have hT : uᵀ = u := by
    rw [hudef, cplx, ← Matrix.transpose_map, wb_SigU_transpose hSig]
  have key : ∀ (S B : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ), Sᵀ = S →
      ∀ a b : Fin M ⊕ Fin N → ℂ, (S *ᵥ a) ⬝ᵥ (B *ᵥ (S *ᵥ b)) = a ⬝ᵥ ((S * B * S) *ᵥ b) := by
    intro S B hS a b
    rw [← vecMul_transpose, hS, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  unfold ent
  rw [wb_cvec_mulVec, wb_cvec_mulVec, key u _ hT]
  congr 2
  calc G Sig A z + u = (u * V) * (G Sig A z + u) * (V * u) := by rw [hu, hV]; simp
    _ = _ := by simp only [Matrix.mul_assoc]

/-- `|G_{ab}|` through the bound of `Σ̲⁻¹(G + Σ̲)Σ̲⁻¹`. -/
private theorem wb_G_bound {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (a b : Fin M ⊕ Fin N → ℝ) :
    ‖ent (G Sig A z) a b‖ ≤
        ((1 + ‖Aᵀ * A‖) / z.im + 1) * testNorm (SigU (n := Fin N) Sig *ᵥ a) *
          testNorm (SigU (n := Fin N) Sig *ᵥ b) +
        min (testNorm a * testNorm (SigU (n := Fin N) Sig *ᵥ b))
          (testNorm (SigU (n := Fin N) Sig *ᵥ a) * testNorm b) := by
  have h1 := opnorm_G hSig A hz (SigU (n := Fin N) Sig *ᵥ a) (SigU (n := Fin N) Sig *ᵥ b)
  rw [wb_sqrt_dot, wb_sqrt_dot] at h1
  have h2 := wb_ent_G_add_u hSig A z a b
  rw [wb_ent_add, wb_ent_cplx] at h2
  have h3 : ent (G Sig A z) a b = ent (cplx (SigU (n := Fin N) Sig)⁻¹ *
      (G Sig A z + cplx (SigU (n := Fin N) Sig)) * cplx (SigU (n := Fin N) Sig)⁻¹)
      (SigU (n := Fin N) Sig *ᵥ a) (SigU (n := Fin N) Sig *ᵥ b) -
      ((a ⬝ᵥ SigU (n := Fin N) Sig *ᵥ b : ℝ) : ℂ) := by
    rw [← h2]; ring
  have hd1 : |a ⬝ᵥ SigU (n := Fin N) Sig *ᵥ b| ≤
      testNorm a * testNorm (SigU (n := Fin N) Sig *ᵥ b) := wb_dot_le _ _
  have hd2 : |a ⬝ᵥ SigU (n := Fin N) Sig *ᵥ b| ≤
      testNorm (SigU (n := Fin N) Sig *ᵥ a) * testNorm b := by
    rw [wb_dot_SigU hSig]; exact wb_dot_le _ _
  have hd : ‖((a ⬝ᵥ SigU (n := Fin N) Sig *ᵥ b : ℝ) : ℂ)‖ ≤
      min (testNorm a * testNorm (SigU (n := Fin N) Sig *ᵥ b))
        (testNorm (SigU (n := Fin N) Sig *ᵥ a) * testNorm b) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact le_min hd1 hd2
  rw [h3]
  refine (norm_sub_le _ _).trans ?_
  refine add_le_add ?_ hd
  exact h1

/-- A bound on the coordinates `x_N` of a unit vector. -/
private theorem wb_sum_inr_le {v : Fin M ⊕ Fin N → ℝ} (hv : testNorm v = 1) :
    ∑ μ, v (Sum.inr μ) ^ 2 ≤ 1 := by
  have h : ∑ s, v s ^ 2 = 1 := by
    unfold testNorm at hv
    have h0 : 0 ≤ ∑ s, v s ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    rwa [Real.sqrt_eq_one] at hv
  rw [Fintype.sum_sum_type] at h
  have h0 : 0 ≤ ∑ i, v (Sum.inl i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

/-- `⟨x, Σ̲ y⟩ = ⟨x, diag(Σ, 0) y⟩ + ⟨x_N, y_N⟩`. -/
private theorem wb_dot_SigU_split {Sig : Matrix (Fin M) (Fin M) ℝ} (x y : Fin M ⊕ Fin N → ℝ) :
    x ⬝ᵥ SigU (n := Fin N) Sig *ᵥ y =
      x ⬝ᵥ fromBlocks Sig 0 0 (0 : Matrix (Fin N) (Fin N) ℝ) *ᵥ y +
        ∑ μ, x (Sum.inr μ) * y (Sum.inr μ) := by
  simp only [SigU, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, zero_mulVec, add_zero, zero_add, one_mulVec, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero]
  rfl

/-- `N ≥ 1` in the setting of §7. -/
private theorem wb_N_pos {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) : 1 ≤ N := by
  by_contra h
  have h0 : N = 0 := by omega
  have := hset.ratio_ge
  rw [h0] at this
  simp at this
  linarith [hset.pos]

/-- `|G_{v̄v̄} − Π_{v̄v̄}| ≤ (X + 1) + (K_m max(c⁻¹, 1) + 1)` for a unit vector `v`. -/
private theorem wb_Fv_bound {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) {z : ℂ} (hz : z ∈ S) (A : Matrix (Fin M) (Fin N) ℝ)
    (v : Fin M ⊕ Fin N → ℝ) (hv : testNorm v = 1) :
    ‖ent (G Sig A z - PiZ N Sig z) (vbar Sig v) (vbar Sig v)‖ ≤
      ((1 + ‖Aᵀ * A‖) / z.im + 1) + (mBoundConst τ * max c⁻¹ 1 + 1) := by
  have hSig := hset.sigma.posDef
  have hzD := hset.domain.1 hz
  have hη : 0 < z.im := hzD.1
  have hm := (gen_prop_m_specDomain (wb_density hset (wb_N_pos hset)) hzD).2.1
  set x := vbar Sig v with hx
  set u := cplx (SigU (n := Fin N) Sig) with hudef
  have hSx : SigU (n := Fin N) Sig *ᵥ x = v := wb_SigU_vbar hSig v
  have e1 : ent (G Sig A z - PiZ N Sig z) x x =
      ent (G Sig A z + u) x x - (ent (PiZ N Sig z) x x + ent u x x) := by
    rw [← wb_ent_add, ← wb_ent_sub]
    congr 1
    abel
  have h1 : ‖ent (G Sig A z + u) x x‖ ≤ (1 + ‖Aᵀ * A‖) / z.im + 1 := by
    have h := opnorm_G hSig A hη (SigU (n := Fin N) Sig *ᵥ x) (SigU (n := Fin N) Sig *ᵥ x)
    rw [hSx, wb_sqrt_dot, hv] at h
    rw [wb_ent_G_add_u hSig A z x x, hSx]
    simpa using h
  have h2 : ‖ent (PiZ N Sig z) x x + ent u x x‖ ≤ mBoundConst τ * max c⁻¹ 1 + 1 := by
    have hp := wb_pi_part (N := N) hSig hset.c_pos hm (hset.oneXm z hz) x x
    rw [hSx, hv, mul_one, mul_one] at hp
    have e2 : ent (PiZ N Sig z) x x + ent u x x =
        -(-((x ⬝ᵥ fromBlocks Sig 0 0 (0 : Matrix (Fin N) (Fin N) ℝ) *ᵥ x : ℝ) : ℂ) -
          ent (piMat (N := N) Sig (mFun N (specOf Sig) z)) x x) +
          ((∑ μ, x (Sum.inr μ) * x (Sum.inr μ) : ℝ) : ℂ) := by
      rw [hudef, wb_ent_cplx, wb_dot_SigU_split]
      change ent (piMat (N := N) Sig (mFun N (specOf Sig) z)) x x + _ = _
      push_cast
      ring
    rw [e2]
    refine (norm_add_le _ _).trans (add_le_add (by rwa [norm_neg]) ?_)
    rw [Complex.norm_real, Real.norm_eq_abs]
    have hxN : ∀ μ, x (Sum.inr μ) = v (Sum.inr μ) := fun μ => by simp [hx, vbar]
    have h0 : 0 ≤ ∑ μ, x (Sum.inr μ) * x (Sum.inr μ) :=
      Finset.sum_nonneg fun _ _ => mul_self_nonneg _
    rw [abs_of_nonneg h0]
    have := wb_sum_inr_le hv
    simp only [hxN, ← sq]
    exact this
  rw [e1]
  refine (norm_sub_le _ _).trans ?_
  linarith

/-- The three factor bounds of (A_rough), at `t = τ⁻¹ ≥ 1`, `1 ≤ t X`, `κ' ≥ 0`. -/
private theorem wb_rough_arith {t X κ : ℝ} (ht : 1 ≤ t) (hX : 0 < X) (htX : 1 ≤ t * X)
    (hκ : 0 ≤ κ) :
    ((X + 1) * t ^ 2 + t ≤ 4 * t ^ 3 * (2 + κ) * X) ∧
      ((X + 1) * t + 1 ≤ 4 * t ^ 3 * (2 + κ) * X) ∧
      ((X + 1) + (κ + 1) ≤ 4 * t ^ 3 * (2 + κ) * X) := by
  have ht0 : 0 < t := by linarith
  have h2 : t ≤ t ^ 2 * X := by nlinarith
  have h3 : t ^ 2 ≤ t ^ 3 * X := by nlinarith
  have h4 : t ^ 2 * X ≤ t ^ 3 * X := by
    have : t ^ 2 ≤ t ^ 3 := by nlinarith [sq_nonneg t]
    exact mul_le_mul_of_nonneg_right this hX.le
  have h5 : X ≤ t ^ 3 * X := by
    have : 1 ≤ t ^ 3 := one_le_pow₀ ht
    nlinarith
  have h6 : X * t ^ 2 ≤ t ^ 3 * X := by nlinarith
  have h7 : 0 ≤ t ^ 3 * κ * X := by positivity
  have h8 : 1 ≤ t ^ 2 * X := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · have h9 : κ ≤ t ^ 3 * κ * X := by
      have : 1 ≤ t ^ 3 * X := by nlinarith
      nlinarith
    nlinarith

/-- The rough constant of (A_rough). -/
def roughConst (τ c : ℝ) : ℝ := 4 * τ⁻¹ ^ 3 * (2 + mBoundConst τ * max c⁻¹ 1)

/-- (A_rough), deterministic: `|A(w)| ≤ (K (1 + ‖XᵀX‖)/η)^{n(w)+1}`. -/
theorem norm_wordA_rough {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) {z : ℂ} (hz : z ∈ S) (A : Matrix (Fin M) (Fin N) ℝ)
    (v : Fin M ⊕ Fin N → ℝ) (hv : testNorm v = 1) (i : Fin M) (μ : Fin N) (n : ℕ)
    (w : Word n) :
    ‖wordA Sig A z v i μ n w‖ ≤ (roughConst τ c * (1 + ‖Aᵀ * A‖) / z.im) ^ (n + 1) := by
  have hSig := hset.sigma.posDef
  have hτ := hset.pos
  have hτ1 := hset.le_one
  have hzD := hset.domain.1 hz
  have hη : 0 < z.im := hzD.1
  have hηt : z.im ≤ τ⁻¹ := hzD.2.2.2.2
  set X := (1 + ‖Aᵀ * A‖) / z.im with hXdef
  set t := τ⁻¹ with htdef
  have ht1 : 1 ≤ t := (one_le_inv₀ hτ).2 hτ1
  have hX0 : 0 < X := by
    have := norm_nonneg (Aᵀ * A)
    positivity
  have htX : 1 ≤ t * X := by
    have h1 : 1 / z.im ≤ X := by
      rw [hXdef]
      exact div_le_div_of_nonneg_right (by linarith [norm_nonneg (Aᵀ * A)]) hη.le
    have h2 : τ ≤ 1 / z.im := by
      rw [le_div_iff₀ hη]
      calc τ * z.im ≤ τ * τ⁻¹ := mul_le_mul_of_nonneg_left hηt hτ.le
        _ = 1 := mul_inv_cancel₀ hτ.ne'
    calc (1 : ℝ) = t * τ := by rw [htdef]; exact (inv_mul_cancel₀ hτ.ne').symm
      _ ≤ t * X := mul_le_mul_of_nonneg_left (h2.trans h1) (by linarith)
  have hK0 : 0 ≤ mBoundConst τ * max c⁻¹ 1 := by
    have : 0 < mBoundConst τ := by unfold mBoundConst genPropConst; positivity
    exact mul_nonneg this.le (le_trans zero_le_one (le_max_right _ _))
  obtain ⟨a1, a2, a3⟩ := wb_rough_arith ht1 hX0 htX hK0
  have hrc : roughConst τ c * (1 + ‖Aᵀ * A‖) / z.im =
      4 * t ^ 3 * (2 + mBoundConst τ * max c⁻¹ 1) * X := by
    rw [hXdef]
    unfold roughConst
    ring
  rw [hrc]
  set Kc := 4 * t ^ 3 * (2 + mBoundConst τ * max c⁻¹ 1) * X with hKc
  have hKc0 : 0 ≤ Kc := by positivity
  -- unit vectors and their images under `Σ̲`
  have hSv : testNorm (SigU (n := Fin N) Sig *ᵥ vbar Sig v) = 1 := by
    rw [wb_SigU_vbar hSig, hv]
  have hSe : ∀ s : Fin M ⊕ Fin N, testNorm (SigU (n := Fin N) Sig *ᵥ eI s) ≤ t := fun s => by
    have := wb_SigU_le hset.sigma hτ1 hτ (eI s)
    rwa [wb_testNorm_eI, mul_one] at this
  have hSe0 : ∀ s : Fin M ⊕ Fin N, 0 ≤ testNorm (SigU (n := Fin N) Sig *ᵥ eI s) := fun s =>
    Real.sqrt_nonneg _
  have hX1 : 0 ≤ X + 1 := by linarith
  -- the factor bounds
  have hfirst : ∀ s, ‖ent (G Sig A z) (vbar Sig v) (eI s)‖ ≤ Kc := by
    intro s
    refine (wb_G_bound hSig A hη (vbar Sig v) (eI s)).trans ?_
    rw [hSv, wb_testNorm_eI, ← hXdef]
    have h1 : (X + 1) * 1 * testNorm (SigU (n := Fin N) Sig *ᵥ eI s) ≤ (X + 1) * t := by
      rw [mul_one]; exact mul_le_mul_of_nonneg_left (hSe s) hX1
    have h2 := min_le_right (testNorm (vbar Sig v) * testNorm (SigU (n := Fin N) Sig *ᵥ eI s))
      (1 * 1)
    linarith
  have hlast : ∀ s, ‖ent (G Sig A z) (eI s) (vbar Sig v)‖ ≤ Kc := by
    intro s
    refine (wb_G_bound hSig A hη (eI s) (vbar Sig v)).trans ?_
    rw [hSv, wb_testNorm_eI, ← hXdef]
    have h1 : (X + 1) * testNorm (SigU (n := Fin N) Sig *ᵥ eI s) * 1 ≤ (X + 1) * t := by
      rw [mul_one]; exact mul_le_mul_of_nonneg_left (hSe s) hX1
    have h2 := min_le_left (1 * 1)
      (testNorm (SigU (n := Fin N) Sig *ᵥ eI s) * testNorm (vbar Sig v))
    linarith
  have hmid : ∀ s s', ‖G Sig A z s s'‖ ≤ Kc := by
    intro s s'
    rw [show G Sig A z s s' = ent (G Sig A z) (eI s) (eI s') from (ent_eI_eI _ _ _).symm]
    refine (wb_G_bound hSig A hη (eI s) (eI s')).trans ?_
    rw [wb_testNorm_eI, wb_testNorm_eI, ← hXdef]
    have h1 : (X + 1) * testNorm (SigU (n := Fin N) Sig *ᵥ eI s) *
        testNorm (SigU (n := Fin N) Sig *ᵥ eI s') ≤ (X + 1) * t ^ 2 := by
      rw [sq, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (hSe s) (hSe s') (hSe0 s') (by linarith)) hX1
    have h2 := min_le_left (1 * testNorm (SigU (n := Fin N) Sig *ᵥ eI s'))
      (testNorm (SigU (n := Fin N) Sig *ᵥ eI s) * 1)
    have h3 := hSe s'
    linarith
  have hF : ‖ent (G Sig A z - PiZ N Sig z) (vbar Sig v) (vbar Sig v)‖ ≤ Kc := by
    refine (wb_Fv_bound hset hz A v hv).trans ?_
    linarith
  cases n with
  | zero =>
    simpa [wordA] using hF
  | succ k =>
    unfold wordA
    rw [norm_mul, norm_mul, norm_prod]
    have hp : ∏ l : Fin k, ‖G Sig A z (letterS i μ (w l.castSucc)) (letterT i μ (w l.succ))‖ ≤
        Kc ^ k := by
      have := Finset.prod_le_prod₀ (s := (Finset.univ : Finset (Fin k)))
        (f := fun l => ‖G Sig A z (letterS i μ (w l.castSucc)) (letterT i μ (w l.succ))‖)
        (g := fun _ => Kc) (fun l _ => norm_nonneg _) fun l _ => hmid _ _
      simpa using this
    have h1 := hfirst (letterT i μ (w 0))
    have h2 := hlast (letterS i μ (w (Fin.last k)))
    calc _ ≤ Kc * Kc ^ k * Kc :=
          mul_le_mul (mul_le_mul h1 hp (Finset.prod_nonneg fun _ _ => norm_nonneg _) hKc0) h2
            (norm_nonneg _) (by positivity)
      _ = Kc ^ (k + 1 + 1) := by ring

/-- `∑_i v_i² ≤ 1` over the `𝓘_M` coordinates of a unit vector. -/
private theorem wb_sum_inl_le {v : Fin M ⊕ Fin N → ℝ} (hv : testNorm v = 1) :
    ∑ i, v (Sum.inl i) ^ 2 ≤ 1 := by
  have h : ∑ s, v s ^ 2 = 1 := by
    unfold testNorm at hv
    rwa [Real.sqrt_eq_one] at hv
  rw [Fintype.sum_sum_type] at h
  have h0 : 0 ≤ ∑ μ, v (Sum.inr μ) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

/-- `Im G_{xx} ≥ 0` for `Im z > 0`. -/
private theorem wb_ImG_nonneg {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (x : Fin M ⊕ Fin N → ℝ) :
    0 ≤ (ent (G Sig A z) x x).im := by
  have h2 := GMaa4_unified hSig A hz x
  have h0 : 0 ≤ ∑ μ, ‖ent (G Sig A z) x (eI (Sum.inr μ))‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [h2] at h0
  have := mul_nonneg h0 hz.le
  rwa [div_mul_cancel₀ _ hz.ne'] at this

/-- (bound_sum_im), deterministic part (Lemma 4.6 (GMaa), (GMaa4) with `x = v̄`). -/
theorem bound_sum_im_det {τ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} (hS : SigmaAssumption τ Sig)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (v : Fin M ⊕ Fin N → ℝ)
    (hv : testNorm v = 1) :
    ∑ i, ‖ent (G Sig A z) (vbar Sig v) (eI (Sum.inl i))‖ ^ 2 +
        ∑ μ, ‖ent (G Sig A z) (vbar Sig v) (eI (Sum.inr μ))‖ ^ 2 ≤
      (2 * τ⁻¹ ^ 2 * ‖Aᵀ * A‖ + 1) / z.im * ImGvv Sig A z v + 2 := by
  have hSig := hS.posDef
  set x := vbar Sig v with hx
  have h1 := GMaa_unified hSig A hz x
  have h2 := GMaa4_unified hSig A hz x
  have hIm := wb_ImG_nonneg hSig A hz x
  have hSym : Sigᵀ = Sig := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact hSig.1.eq
  have hSS : Sig *ᵥ (x ∘ Sum.inl) = v ∘ Sum.inl := by
    have hS1 : Sig * Sig⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hSig.isUnit)
    have : x ∘ Sum.inl = Sig⁻¹ *ᵥ (v ∘ Sum.inl) := by
      funext i; simp [hx, vbar]
    rw [this, mulVec_mulVec, hS1, one_mulVec]
  have hq : (x ∘ Sum.inl) ⬝ᵥ (Sig * Sig) *ᵥ (x ∘ Sum.inl) ≤ 1 := by
    have hvm : (x ∘ Sum.inl) ᵥ* Sig = Sig *ᵥ (x ∘ Sum.inl) := by
      rw [← Matrix.vecMul_transpose, hSym]
    rw [← mulVec_mulVec, Matrix.dotProduct_mulVec, hvm, hSS]
    have := wb_sum_inl_le hv
    simpa [dotProduct, sq] using this
  have hn : ‖Sig‖ ^ 2 ≤ τ⁻¹ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) (wb_opNorm_Sig_le hS) 2
    rwa [sq_abs] at this
  have hc : 2 * ‖Sig‖ ^ 2 * ‖Aᵀ * A‖ / z.im * (ent (G Sig A z) x x).im ≤
      2 * τ⁻¹ ^ 2 * ‖Aᵀ * A‖ / z.im * (ent (G Sig A z) x x).im := by
    have h0 := norm_nonneg (Aᵀ * A)
    have h3 : 2 * ‖Sig‖ ^ 2 * ‖Aᵀ * A‖ ≤ 2 * τ⁻¹ ^ 2 * ‖Aᵀ * A‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn (by norm_num)) h0
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right h3 hz.le) hIm
  have e : (2 * τ⁻¹ ^ 2 * ‖Aᵀ * A‖ + 1) / z.im * ImGvv Sig A z v =
      2 * τ⁻¹ ^ 2 * ‖Aᵀ * A‖ / z.im * (ent (G Sig A z) x x).im +
        (ent (G Sig A z) x x).im / z.im := by
    simp only [ImGvv, ← hx]
    ring
  rw [e, h2]
  linarith

/-- The real arithmetic of (bound_sum_im): with `u = 1/(Nη)`,
`4 N⁻¹ (c' η⁻¹ Im G + 2) ≤ e e (f g ps²)`. -/
private theorem wb_chain {Nr η mi ps Km c' e f g ImG : ℝ} (hNr : 0 < Nr) (hη : 0 < η)
    (hKm : 0 < Km) (hmi : Km⁻¹ * η ≤ mi) (hps0 : 0 ≤ ps)
    (hps2 : mi / (Nr * η) ≤ ps ^ 2) (hps1 : 1 / (Nr * η) ≤ ps) (hc' : 1 ≤ c')
    (hf : 1 ≤ f) (hg : 1 ≤ g) (he : 1 ≤ e)
    (hImG : ImG ≤ e * (f * (mi + g * ps))) (hK' : 8 * c' + 8 * Km ≤ e) :
    4 * Nr⁻¹ * (c' / η * ImG + 2) ≤ e * e * (f * g * ps ^ 2) := by
  set u := 1 / (Nr * η) with hu
  have hu0 : 0 ≤ u := by positivity
  have hmi0 : 0 ≤ mi := le_trans (by positivity) hmi
  have hNinv : Nr⁻¹ ≤ Km * ps ^ 2 := by
    have h1 : Km⁻¹ * η * u ≤ mi * u := mul_le_mul_of_nonneg_right hmi hu0
    have h2 : Km⁻¹ * η * u = Km⁻¹ * Nr⁻¹ := by
      rw [hu]; field_simp
    have h3 : mi * u = mi / (Nr * η) := by rw [hu]; ring
    have h4 : Km⁻¹ * Nr⁻¹ ≤ ps ^ 2 := by
      rw [← h2]; exact h1.trans (h3 ▸ hps2)
    have h5 : Nr⁻¹ ≤ Km * ps ^ 2 := by
      have := mul_le_mul_of_nonneg_left h4 hKm.le
      rwa [← mul_assoc, mul_inv_cancel₀ hKm.ne', one_mul] at this
    exact h5
  have hlhs : 4 * Nr⁻¹ * (c' / η * ImG + 2) = 4 * c' * u * ImG + 8 * Nr⁻¹ := by
    rw [hu]; field_simp; ring
  have hps2' : mi * u ≤ ps ^ 2 := by
    have : mi * u = mi / (Nr * η) := by rw [hu]; ring
    rw [this]; exact hps2
  have hpsu : ps * u ≤ ps ^ 2 := by
    rw [sq]; exact mul_le_mul_of_nonneg_left hps1 hps0
  have hef : 0 ≤ e * f := by positivity
  have hImGu : u * ImG ≤ e * f * (ps ^ 2 + g * ps ^ 2) := by
    calc u * ImG ≤ u * (e * (f * (mi + g * ps))) := mul_le_mul_of_nonneg_left hImG hu0
      _ = e * f * (mi * u + g * (ps * u)) := by ring
      _ ≤ e * f * (ps ^ 2 + g * ps ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hef
          have := mul_le_mul_of_nonneg_left hpsu (by linarith : (0 : ℝ) ≤ g)
          linarith
  have hc0 : 0 ≤ c' := by linarith
  have hps2n : 0 ≤ ps ^ 2 := sq_nonneg _
  have hefg : 1 ≤ e * f * g := by
    have := mul_le_mul he hf zero_le_one (by linarith)
    have := mul_le_mul this hg zero_le_one (by nlinarith)
    simpa using this
  have h6 : 4 * c' * u * ImG ≤ 4 * c' * (e * f * (ps ^ 2 + g * ps ^ 2)) := by
    have := mul_le_mul_of_nonneg_left hImGu (by positivity : (0 : ℝ) ≤ 4 * c')
    linarith
  have h7 : 4 * c' * (e * f * (ps ^ 2 + g * ps ^ 2)) ≤ 8 * c' * (e * f * g) * ps ^ 2 := by
    have h1 : ps ^ 2 + g * ps ^ 2 ≤ 2 * g * ps ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_left h1 hef
    nlinarith [mul_nonneg hc0 (mul_nonneg hef hps2n)]
  have h8 : 8 * Nr⁻¹ ≤ 8 * Km * (e * f * g) * ps ^ 2 := by
    have h1 : Km * ps ^ 2 ≤ Km * (e * f * g) * ps ^ 2 := by
      have := mul_le_mul_of_nonneg_right hefg (mul_nonneg hKm.le hps2n)
      nlinarith
    linarith
  rw [hlhs]
  calc 4 * c' * u * ImG + 8 * Nr⁻¹ ≤
        8 * c' * (e * f * g) * ps ^ 2 + 8 * Km * (e * f * g) * ps ^ 2 := by linarith
    _ = (8 * c' + 8 * Km) * (e * f * g * ps ^ 2) := by ring
    _ ≤ e * (e * f * g * ps ^ 2) :=
        mul_le_mul_of_nonneg_right hK' (by positivity)
    _ = e * e * (f * g * ps ^ 2) := by ring

/-- (bound_sum_im) at a general `C₀`. -/
private theorem wb_bsi (τ c : ℝ) (C : ℕ → ℝ) (C₀ δ εA DA : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hc : 0 < c) (hδ : 0 < δ) (hC₀ : 25 ≤ C₀) (hC₀δ : C₀ * δ ≤ τ / 4) (hεA : 0 < εA) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ)
      (P : ModelClass M N) (m : ℕ), CompSetting τ c M N Sig S → 1 ≤ m →
      PropA N C P Sig S C₀ δ (m - 1) εA DA →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption C X → P Ω X →
        ∀ z ∈ levelSet N δ S m, ∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 →
          DomAt N (2 * εA) (DA - 1)
            (fun ω => (N : ℝ)⁻¹ *
              (∑ i, (‖ent (G Sig (X ω) z) (vbar Sig v) (eI (Sum.inl i))‖ +
                  ‖ent (G Sig (X ω) z) (eI (Sum.inl i)) (vbar Sig v)‖) ^ 2 +
                ∑ μ, (‖ent (G Sig (X ω) z) (vbar Sig v) (eI (Sum.inr μ))‖ +
                  ‖ent (G Sig (X ω) z) (eI (Sum.inr μ)) (vbar Sig v)‖) ^ 2))
            (fun _ => (N : ℝ) ^ ((C₀ + 2) * δ) * Psi N (specOf Sig) z ^ 2) := by
  obtain ⟨Cn, hCn⟩ := norm_XtX_le hτ hτ1
  obtain ⟨N₁, hN₁⟩ := hCn C DA
  obtain ⟨N₂, hN₂⟩ := cor_rough_bound' τ c C C₀ δ εA DA hτ hτ1 hc hδ hC₀ hC₀δ hεA
  have hKm0 : 0 < mBoundConst τ := by unfold mBoundConst genPropConst; positivity
  have hCn'0 : 0 ≤ max Cn 0 := le_max_right _ _
  set c' := 2 * τ⁻¹ ^ 2 * max Cn 0 + 1 with hc'def
  have hc'1 : 1 ≤ c' := by
    have : 0 ≤ 2 * τ⁻¹ ^ 2 * max Cn 0 := by positivity
    linarith
  set K' := 8 * c' + 8 * mBoundConst τ with hK'def
  have hK'0 : 0 ≤ K' := by positivity
  refine ⟨max (max N₁ N₂) (max 2 ⌈K' ^ εA⁻¹⌉₊), ?_⟩
  intro N hN M Sig S P m hset hm hA Ω _ _ X hX hP z hz v hv
  have hN2 : 2 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNN₁ : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNN₂ : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNr2 : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNp : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hNK : K' ≤ (N : ℝ) ^ εA := by
    have h0 : ⌈K' ^ εA⁻¹⌉₊ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
    have h1 : K' ^ εA⁻¹ ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast h0)
    calc K' = (K' ^ εA⁻¹) ^ εA := (Real.rpow_inv_rpow hK'0 hεA.ne').symm
      _ ≤ (N : ℝ) ^ εA := Real.rpow_le_rpow (Real.rpow_nonneg hK'0 _) h1 hεA.le
  have hM : (M : ℝ) ≤ τ⁻¹ * N := by
    have := hset.ratio_le
    rwa [div_le_iff₀ hNp] at this
  have hE := hN₁ N hNN₁ (Ω := Ω) M X hX hM
  have hSig := hset.sigma.posDef
  have hzD := hset.domain.1 hz.1
  have hη : 0 < z.im := hzD.1
  have hmK := gen_prop_m_specDomain (wb_density hset (wb_N_pos hset)) hzD
  obtain ⟨-, hIm2⟩ := hN₂ N hNN₂ M Sig S P m hset hm hA Ω X hX hP z hz
  have hD := hIm2 v hv
  set mi := (mFun N (specOf Sig) z).im with hmi
  set ps := Psi N (specOf Sig) z with hps
  have hmi0 : 0 ≤ mi := le_trans (by positivity) hmK.2.2
  have hps0 : 0 ≤ ps := by
    rw [hps]; unfold Psi; positivity
  have hps1 : 1 / ((N : ℝ) * z.im) ≤ ps := by
    rw [hps]; unfold Psi
    exact le_add_of_nonneg_left (Real.sqrt_nonneg _)
  have hps2 : mi / ((N : ℝ) * z.im) ≤ ps ^ 2 := by
    have ha : 0 ≤ mi / ((N : ℝ) * z.im) := by positivity
    have h1 := Real.sq_sqrt ha
    have h2 : Real.sqrt (mi / ((N : ℝ) * z.im)) ≤ ps := by
      rw [hps]; unfold Psi
      exact le_add_of_nonneg_right (by positivity)
    nlinarith [Real.sqrt_nonneg (mi / ((N : ℝ) * z.im))]
  have he : 1 ≤ (N : ℝ) ^ εA := Real.one_le_rpow hN1 hεA.le
  have hf : 1 ≤ (N : ℝ) ^ (2 * δ) := Real.one_le_rpow hN1 (by linarith)
  have hg : 1 ≤ (N : ℝ) ^ (C₀ * δ) := Real.one_le_rpow hN1 (by nlinarith)
  have e2ε : (N : ℝ) ^ (2 * εA) = (N : ℝ) ^ εA * (N : ℝ) ^ εA := by
    rw [two_mul, Real.rpow_add hNp]
  have eC : (N : ℝ) ^ ((C₀ + 2) * δ) = (N : ℝ) ^ (2 * δ) * (N : ℝ) ^ (C₀ * δ) := by
    rw [show (C₀ + 2) * δ = 2 * δ + C₀ * δ by ring, Real.rpow_add hNp]
  refine DomAt.of_highProbAt (A := {ω | ‖(X ω)ᵀ * X ω‖ ≤ Cn}) hN2 hE ?_
  refine le_trans (measure_mono ?_) hD
  intro ω hω
  obtain ⟨hωE, hωQ⟩ := hω
  have hωE' : ‖(X ω)ᵀ * X ω‖ ≤ Cn := hωE
  have hωQ' : (N : ℝ) ^ (2 * εA) * ((N : ℝ) ^ ((C₀ + 2) * δ) * ps ^ 2) <
      (N : ℝ)⁻¹ *
        (∑ i, (‖ent (G Sig (X ω) z) (vbar Sig v) (eI (Sum.inl i))‖ +
            ‖ent (G Sig (X ω) z) (eI (Sum.inl i)) (vbar Sig v)‖) ^ 2 +
          ∑ μ, (‖ent (G Sig (X ω) z) (vbar Sig v) (eI (Sum.inr μ))‖ +
            ‖ent (G Sig (X ω) z) (eI (Sum.inr μ)) (vbar Sig v)‖) ^ 2) := hωQ
  change (N : ℝ) ^ εA * ((N : ℝ) ^ (2 * δ) * (mi + (N : ℝ) ^ (C₀ * δ) * ps)) <
    ImGvv Sig (X ω) z v
  by_contra hle
  push Not at hle
  have hsymm : ∀ s, ‖ent (G Sig (X ω) z) (eI s) (vbar Sig v)‖ =
      ‖ent (G Sig (X ω) z) (vbar Sig v) (eI s)‖ := fun s => by
    rw [wb_ent_symm, G_transpose hSig (X ω) hη]
  have h4 : ∀ a : ℝ, (a + a) ^ 2 = 4 * a ^ 2 := fun a => by ring
  simp only [hsymm, h4, ← Finset.mul_sum] at hωQ'
  have hdet := bound_sum_im_det hset.sigma (X ω) hη v hv
  have hIm0 := wb_ImG_nonneg hSig (X ω) hη (vbar Sig v)
  have hcoef : (2 * τ⁻¹ ^ 2 * ‖(X ω)ᵀ * X ω‖ + 1) / z.im * ImGvv Sig (X ω) z v ≤
      c' / z.im * ImGvv Sig (X ω) z v := by
    have h1 : 2 * τ⁻¹ ^ 2 * ‖(X ω)ᵀ * X ω‖ + 1 ≤ c' := by
      have := mul_le_mul_of_nonneg_left (hωE'.trans (le_max_left Cn 0))
        (by positivity : (0 : ℝ) ≤ 2 * τ⁻¹ ^ 2)
      rw [hc'def]; linarith
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right h1 hη.le) hIm0
  have hchain := wb_chain (Nr := (N : ℝ)) (η := z.im) (mi := mi) (ps := ps)
    (Km := mBoundConst τ) (c' := c') (e := (N : ℝ) ^ εA) (f := (N : ℝ) ^ (2 * δ))
    (g := (N : ℝ) ^ (C₀ * δ)) (ImG := ImGvv Sig (X ω) z v) hNp hη hKm0 hmK.2.2 hps0 hps2
    hps1 hc'1 hf hg he hle hNK
  rw [e2ε, eC] at hωQ'
  have hsum : (N : ℝ)⁻¹ * (4 * ∑ i, ‖ent (G Sig (X ω) z) (vbar Sig v) (eI (Sum.inl i))‖ ^ 2 +
      4 * ∑ μ, ‖ent (G Sig (X ω) z) (vbar Sig v) (eI (Sum.inr μ))‖ ^ 2) ≤
      4 * (N : ℝ)⁻¹ * (c' / z.im * ImGvv Sig (X ω) z v + 2) := by
    have h5 : 0 ≤ (N : ℝ)⁻¹ := by positivity
    have := mul_le_mul_of_nonneg_left (hdet.trans (add_le_add_left hcoef 2)) h5
    nlinarith
  linarith

/-- Pigeonhole: `q` words with `n(w_r) ≥ 1` and `∑ n(w_r) ≤ 2q − 2` contain two of length 1. -/
theorem pigeonhole_words {q : ℕ} (ns : Fin q → ℕ) (h1 : ∀ r, 1 ≤ ns r)
    (hn : ∑ r, ns r + 2 ≤ 2 * q) : ∃ r₁ r₂, r₁ ≠ r₂ ∧ ns r₁ = 1 ∧ ns r₂ = 1 := by
  by_contra hcon
  push Not at hcon
  have hle : (Finset.univ.filter fun r => ns r = 1).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    by_contra hab
    exact hcon a b hab ha hb
  have h2 : ∀ r, 2 ≤ ns r + (if ns r = 1 then 1 else 0) := by
    intro r
    have := h1 r
    split_ifs with h <;> omega
  have hsum : ∑ _r : Fin q, 2 ≤ ∑ r, (ns r + (if ns r = 1 then 1 else 0)) :=
    Finset.sum_le_sum fun r _ => h2 r
  rw [Finset.sum_add_distrib, ← Finset.card_filter] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  omega

/-- Young's inequality `a^{p−q} b^q ≤ ((p−q)/p) a^p + (q/p) b^p`. -/
theorem young_pow {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {p q : ℕ} (hqp : q ≤ p) (hp : 0 < p) :
    a ^ (p - q) * b ^ q ≤ (((p - q : ℕ) : ℝ) / p) * a ^ p + ((q : ℝ) / p) * b ^ p := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hw1 : (0 : ℝ) ≤ ((p - q : ℕ) : ℝ) / p := by positivity
  have hw2 : (0 : ℝ) ≤ (q : ℝ) / p := by positivity
  have hsum : ((p - q : ℕ) : ℝ) / p + (q : ℝ) / p = 1 := by
    rw [← add_div, Nat.cast_sub hqp]
    field_simp
    ring
  have h := Real.geom_mean_le_arith_mean2_weighted hw1 hw2 (pow_nonneg ha p) (pow_nonneg hb p) hsum
  have e1 : (a ^ p) ^ (((p - q : ℕ) : ℝ) / p) = a ^ (p - q) := by
    rw [← Real.rpow_natCast a p, ← Real.rpow_mul ha,
      show (p : ℝ) * (((p - q : ℕ) : ℝ) / p) = ((p - q : ℕ) : ℝ) by field_simp,
      Real.rpow_natCast]
  have e2 : (b ^ p) ^ ((q : ℝ) / p) = b ^ q := by
    rw [← Real.rpow_natCast b p, ← Real.rpow_mul hb,
      show (p : ℝ) * ((q : ℝ) / p) = (q : ℝ) by field_simp, Real.rpow_natCast]
  rwa [e1, e2] at h

/-- (bound_sum_im) at a general `C₀`: `N⁻¹ ∑_i R_i² + N⁻¹ ∑_μ R_μ² ≺ N^{(C₀+2)δ} Ψ²`. -/
theorem bound_sum_im' (τ c : ℝ) (C : ℕ → ℝ) (C₀ δ εA DA : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hc : 0 < c) (hδ : 0 < δ) (hC₀ : 25 ≤ C₀) (hC₀δ : C₀ * δ ≤ τ / 4) (hεA : 0 < εA) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ)
      (P : ModelClass M N) (m : ℕ), CompSetting τ c M N Sig S → 1 ≤ m →
      PropA N C P Sig S C₀ δ (m - 1) εA DA →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption C X → P Ω X →
        ∀ z ∈ levelSet N δ S m, ∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 →
          DomAt N (2 * εA) (DA - 1)
            (fun ω => (N : ℝ)⁻¹ *
              (∑ i, (‖ent (G Sig (X ω) z) (vbar Sig v) (eI (Sum.inl i))‖ +
                  ‖ent (G Sig (X ω) z) (eI (Sum.inl i)) (vbar Sig v)‖) ^ 2 +
                ∑ μ, (‖ent (G Sig (X ω) z) (vbar Sig v) (eI (Sum.inr μ))‖ +
                  ‖ent (G Sig (X ω) z) (eI (Sum.inr μ)) (vbar Sig v)‖) ^ 2))
            (fun _ => (N : ℝ) ^ ((C₀ + 2) * δ) * Psi N (specOf Sig) z ^ 2) :=
  wb_bsi τ c C C₀ δ εA DA hτ hτ1 hc hδ hC₀ hC₀δ hεA


/-! ## Instances -/

/-- `pigeonhole_words` at `q = 3`, `ns = (1, 1, 2)`: two words have length 1. -/
example : ∃ r₁ r₂, r₁ ≠ r₂ ∧ (![1, 1, 2] : Fin 3 → ℕ) r₁ = 1 ∧ (![1, 1, 2] : Fin 3 → ℕ) r₂ = 1 :=
  pigeonhole_words ![1, 1, 2] (fun r => by fin_cases r <;> simp)
    (by simp [Fin.sum_univ_three])

/-- `young_pow` at `a = b = 1`, `p = 2`, `q = 1` (equality case). -/
example : (1 : ℝ) ^ (2 - 1) * 1 ^ 1 ≤
    ((((2 - 1 : ℕ) : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) * 1 ^ 2 + (((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) * 1 ^ 2 :=
  young_pow (a := 1) (b := 1) (p := 2) (q := 1) zero_le_one zero_le_one (by norm_num)
    (by norm_num)

/-- `young_pow` at `a = 2`, `b = 1`, `p = 3`, `q = 1` (strict case): `4 ≤ (2/3) 8 + (1/3) 1`. -/
example : (2 : ℝ) ^ (3 - 1) * 1 ^ 1 ≤
    ((((3 - 1 : ℕ) : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) * 2 ^ 3 + (((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) * 1 ^ 3 :=
  young_pow (a := 2) (b := 1) (p := 3) (q := 1) (by norm_num) zero_le_one (by norm_num)
    (by norm_num)

/-- `wordA_one_le` at `M = N = 2`, `Σ = 1`, `X = 0`, `z = i`, `v = e_{(inl 0)}`. -/
example (w : Word 1) :
    ‖wordA (1 : Matrix (Fin 2) (Fin 2) ℝ) (0 : Matrix (Fin 2) (Fin 2) ℝ) Complex.I
        (eI (Sum.inl 0)) 0 0 1 w‖ ≤
      (‖ent (G (1 : Matrix (Fin 2) (Fin 2) ℝ) (0 : Matrix (Fin 2) (Fin 2) ℝ) Complex.I)
            (vbar 1 (eI (Sum.inl 0))) (eI (Sum.inl (0 : Fin 2)))‖ +
          ‖ent (G (1 : Matrix (Fin 2) (Fin 2) ℝ) (0 : Matrix (Fin 2) (Fin 2) ℝ) Complex.I)
            (eI (Sum.inl (0 : Fin 2))) (vbar 1 (eI (Sum.inl 0)))‖) *
        (‖ent (G (1 : Matrix (Fin 2) (Fin 2) ℝ) (0 : Matrix (Fin 2) (Fin 2) ℝ) Complex.I)
            (vbar 1 (eI (Sum.inl 0))) (eI (Sum.inr (0 : Fin 2)))‖ +
          ‖ent (G (1 : Matrix (Fin 2) (Fin 2) ℝ) (0 : Matrix (Fin 2) (Fin 2) ℝ) Complex.I)
            (eI (Sum.inr (0 : Fin 2))) (vbar 1 (eI (Sum.inl 0)))‖) :=
  wordA_one_le _ _ _ _ _ w

/-- `wordA_le_R` at `M = N = 2`, `Σ = 1`, `X = 0`, `z = i`, `n = 1`: conditional in the entry
bound `B` (the hypotheses `0 ≤ B` and `h3` are binders). -/
example {B : ℝ} (hB : 0 ≤ B)
    (h3 : ∀ b b', ‖G (1 : Matrix (Fin 2) (Fin 2) ℝ) (0 : Matrix (Fin 2) (Fin 2) ℝ) Complex.I
      (letterS (0 : Fin 2) (0 : Fin 2) b) (letterT (0 : Fin 2) (0 : Fin 2) b')‖ ≤ B)
    (w : Word (1 + 1)) :
    ‖wordA (1 : Matrix (Fin 2) (Fin 2) ℝ) (0 : Matrix (Fin 2) (Fin 2) ℝ) Complex.I
        (eI (Sum.inl 0)) 0 0 (1 + 1) w‖ ≤
      ((‖ent (G (1 : Matrix (Fin 2) (Fin 2) ℝ) (0 : Matrix (Fin 2) (Fin 2) ℝ) Complex.I)
            (vbar 1 (eI (Sum.inl 0))) (eI (Sum.inl (0 : Fin 2)))‖ +
          ‖ent (G (1 : Matrix (Fin 2) (Fin 2) ℝ) (0 : Matrix (Fin 2) (Fin 2) ℝ) Complex.I)
            (eI (Sum.inl (0 : Fin 2))) (vbar 1 (eI (Sum.inl 0)))‖) ^ 2 +
        (‖ent (G (1 : Matrix (Fin 2) (Fin 2) ℝ) (0 : Matrix (Fin 2) (Fin 2) ℝ) Complex.I)
            (vbar 1 (eI (Sum.inl 0))) (eI (Sum.inr (0 : Fin 2)))‖ +
          ‖ent (G (1 : Matrix (Fin 2) (Fin 2) ℝ) (0 : Matrix (Fin 2) (Fin 2) ℝ) Complex.I)
            (eI (Sum.inr (0 : Fin 2))) (vbar 1 (eI (Sum.inl 0)))‖) ^ 2) * B ^ 1 :=
  wordA_le_R _ _ _ _ _ hB h3 1 w

/-- `bound_sum_im'` at `τ = 1/2`, `c = 1`, `C = 2`, `C₀ = 25`, `δ = 1/200` (`C₀ δ = τ/4`),
`ε_A = 1/800`, `D_A = 3`. Conditional: the setting, the class and the hypothesis on the previous
level are hypotheses of the statement. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ)
      (P : ModelClass M N) (m : ℕ), CompSetting (1 / 2) 1 M N Sig S → 1 ≤ m →
      PropA N (fun _ => 2) P Sig S 25 (1 / 200) (m - 1) (1 / 800) 3 →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption (fun _ => 2) X → P Ω X →
        ∀ z ∈ levelSet N (1 / 200) S m, ∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 →
          DomAt N (2 * (1 / 800)) (3 - 1)
            (fun ω => (N : ℝ)⁻¹ *
              (∑ i, (‖ent (G Sig (X ω) z) (vbar Sig v) (eI (Sum.inl i))‖ +
                  ‖ent (G Sig (X ω) z) (eI (Sum.inl i)) (vbar Sig v)‖) ^ 2 +
                ∑ μ, (‖ent (G Sig (X ω) z) (vbar Sig v) (eI (Sum.inr μ))‖ +
                  ‖ent (G Sig (X ω) z) (eI (Sum.inr μ)) (vbar Sig v)‖) ^ 2))
            (fun _ => (N : ℝ) ^ (((25 : ℝ) + 2) * (1 / 200 : ℝ)) *
              Psi N (specOf Sig) z ^ 2) :=
  bound_sum_im' (1 / 2) 1 (fun _ => 2) 25 (1 / 200) (1 / 800) 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Anisotropic
