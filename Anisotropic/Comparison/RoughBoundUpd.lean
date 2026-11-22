module

public import Anisotropic.Comparison.RoughBound
public import Anisotropic.LinAlg.Expansion

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # Lemma 7.14: a priori bound after replacing one entry -/

/-!
Lemma 7.14 (`lem:rough bound`, eq. (rough_bound2)): under (A_{m−1}), for `X` in the class and
`|y| ≺ N^{−1/2}`, the matrix `Σ̲⁻¹(G(Xˢ) − Π)Σ̲⁻¹` with entry `(i, μ)` of `X` replaced by any
`s`, `|s| ≤ |y|`, is `O_≺(N^{2δ})`, at level `2δ + 3ε_A`.

Proof: (res_exp) at `λ = X_{iμ}`, `λ' = s`, `K = 10` writes
`G(Xˢ) = G + ∑_{k=1}^{10} G(ΔG)^k + G(Xˢ)(ΔG)^{11}` with `Δ = Δ^{λ−s}_{(iμ)}`. Each factor of a
word is an entry `G_{v̄ p}`, `G_{qp}`, `G_{q w̄}` with `p, q ∈ {(i), (μ)}`, bounded by (a_priori_1)
of Lemma 7.13 at the test vectors `v, w, Σ̲e_{(i)}, Σ̲e_{(μ)}` together with (Pi_bounded),
`|Σ̲⁻¹Π| ≤ max(c⁻¹, K_m)` from (1+xm); the first factor of the remainder is bounded by
Lemma 4.9 on the event `‖XˢᵀXˢ‖ ≤ C`, obtained from the variant of Lemma 4.8 at `s = ±1` and
convexity. With
`|λ − s| ≤ 2N^{ε_A−1/2}` (Markov for `X_{iμ}`), the words are `O(N^{2δ+2ε_A} N^{−1/4})` and
the remainder `O(N^{2δ+2ε_A} N^{−1/4})`. All events are independent of `s`, so the bound is
uniform in `|s| ≤ |y|`.
-/

private theorem rbu_ent_add {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (v w : ι → ℝ) :
    ent (A + B) v w = ent A v w + ent B v w := by
  simp [ent, add_mulVec, dotProduct_add]

private theorem rbu_ent_sub {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (v w : ι → ℝ) :
    ent (A - B) v w = ent A v w - ent B v w := by
  simp [ent, sub_mulVec, dotProduct_sub]

private theorem rbu_ent_sum {ι κ : Type*} [Fintype ι] (s : Finset κ) (A : κ → Matrix ι ι ℂ)
    (v w : ι → ℝ) : ent (∑ k ∈ s, A k) v w = ∑ k ∈ s, ent (A k) v w := by
  simp [ent, sum_mulVec, dotProduct_sum]

private theorem rbu_ent_eq {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (x y : ι → ℝ) :
    ent A x y = ∑ s, ∑ t, (x s : ℂ) * A s t * (y t : ℂ) := by
  simp only [ent, cvec, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

private theorem rbu_ent_transpose {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (x y : ι → ℝ) :
    ent Aᵀ x y = ent A y x := by
  rw [rbu_ent_eq, rbu_ent_eq, Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
    simp only [transpose_apply]; ring

private theorem rbu_ent_eI_right {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (x : ι → ℝ) (r : ι) : ent A x (eI r) = ∑ s, (x s : ℂ) * A s r := by
  rw [rbu_ent_eq]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [eI, Pi.single_apply, apply_ite]

private theorem rbu_ent_eI_left {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (y : ι → ℝ) (r : ι) : ent A (eI r) y = ∑ t, A r t * (y t : ℂ) := by
  rw [rbu_ent_eq]
  simp [eI, Pi.single_apply, apply_ite, ite_mul, Finset.sum_ite_eq']

private theorem rbu_Delta_eq (i : Fin M) (μ : Fin N) (d : ℝ) :
    Delta i μ d = (d : ℂ) • (Matrix.single (Sum.inl i) (Sum.inr μ) 1 +
      Matrix.single (Sum.inr μ) (Sum.inl i) 1) := by
  ext s t
  simp only [Delta, Matrix.smul_apply, Matrix.add_apply, Matrix.single_apply, smul_eq_mul]
  by_cases h1 : s = Sum.inl i ∧ t = Sum.inr μ
  · obtain ⟨rfl, rfl⟩ := h1; simp
  · by_cases h2 : s = Sum.inr μ ∧ t = Sum.inl i
    · obtain ⟨rfl, rfl⟩ := h2; simp
    · have h3 : ¬ ((s = Sum.inl i ∧ t = Sum.inr μ) ∨ (s = Sum.inr μ ∧ t = Sum.inl i)) := by
        tauto
      have h4 : ¬ (Sum.inl i = s ∧ Sum.inr μ = t) := fun h => h1 ⟨h.1.symm, h.2.symm⟩
      have h5 : ¬ (Sum.inr μ = s ∧ Sum.inl i = t) := fun h => h2 ⟨h.1.symm, h.2.symm⟩
      simp only [h3, h4, h5, ite_false, add_zero, mul_zero]

private theorem rbu_ent_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P Q : Matrix ι ι ℂ) (a b : ι) (x y : ι → ℝ) :
    ent (P * (Matrix.single a b 1 * Q)) x y = ent P x (eI a) * ent Q (eI b) y := by
  rw [rbu_ent_eI_right, rbu_ent_eI_left, Finset.sum_mul_sum, rbu_ent_eq]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  simp only [Matrix.mul_apply, Matrix.single_apply]
  simp [Finset.sum_ite_eq, ite_and]
  ring

/-- `⟨x, P Δ Q y⟩ = d (P_{x a} Q_{b y} + P_{x b} Q_{a y})` for `a = (i)`, `b = (μ)`. -/
private theorem rbu_ent_Delta (P Q : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ)
    (i : Fin M) (μ : Fin N) (d : ℝ) (x y : Fin M ⊕ Fin N → ℝ) :
    ent (P * (Delta i μ d * Q)) x y =
      d * (ent P x (eI (Sum.inl i)) * ent Q (eI (Sum.inr μ)) y +
        ent P x (eI (Sum.inr μ)) * ent Q (eI (Sum.inl i)) y) := by
  rw [rbu_Delta_eq, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add]
  simp only [ent, smul_mulVec, dotProduct_smul, add_mulVec, dotProduct_add, smul_eq_mul]
  rw [← ent, ← ent, rbu_ent_single, rbu_ent_single]
  rfl


/-- `|⟨x, P (Δ Q)^{k+1} y⟩| ≤ (2|d|)^{k+1} B^k B_y R` when `|P_{x p}| ≤ R`, `|Q_{qp}| ≤ B`,
`|Q_{q y}| ≤ B_y` for `p, q ∈ {(i), (μ)}`. -/
private theorem rbu_word (Q : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) (i : Fin M) (μ : Fin N)
    (d : ℝ) (x y : Fin M ⊕ Fin N → ℝ) {B By : ℝ}
    (hQ : ∀ q ∈ ({Sum.inl i, Sum.inr μ} : Finset (Fin M ⊕ Fin N)),
      ∀ p ∈ ({Sum.inl i, Sum.inr μ} : Finset (Fin M ⊕ Fin N)), ‖Q q p‖ ≤ B)
    (hy : ∀ q ∈ ({Sum.inl i, Sum.inr μ} : Finset (Fin M ⊕ Fin N)), ‖ent Q (eI q) y‖ ≤ By)
    (k : ℕ) : ∀ (P : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) (R : ℝ),
      (∀ p ∈ ({Sum.inl i, Sum.inr μ} : Finset (Fin M ⊕ Fin N)), ‖ent P x (eI p)‖ ≤ R) →
      ‖ent (P * (Delta i μ d * Q) ^ (k + 1)) x y‖ ≤ (2 * |d|) ^ (k + 1) * B ^ k * By * R := by
  have ha : Sum.inl i ∈ ({Sum.inl i, Sum.inr μ} : Finset (Fin M ⊕ Fin N)) := by simp
  have hb : Sum.inr μ ∈ ({Sum.inl i, Sum.inr μ} : Finset (Fin M ⊕ Fin N)) := by simp
  have hB : 0 ≤ B := (norm_nonneg _).trans (hQ _ ha _ ha)
  have hBy : 0 ≤ By := (norm_nonneg _).trans (hy _ ha)
  have step : ∀ (P : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) (R B' : ℝ) (z : Fin M ⊕ Fin N → ℝ),
      0 ≤ B' → (∀ p ∈ ({Sum.inl i, Sum.inr μ} : Finset (Fin M ⊕ Fin N)), ‖ent P x (eI p)‖ ≤ R) →
      (∀ q ∈ ({Sum.inl i, Sum.inr μ} : Finset (Fin M ⊕ Fin N)), ‖ent Q (eI q) z‖ ≤ B') →
      ‖ent (P * (Delta i μ d * Q)) x z‖ ≤ 2 * |d| * B' * R := by
    intro P R B' z hB' hP hz
    have hR : 0 ≤ R := (norm_nonneg _).trans (hP _ ha)
    rw [rbu_ent_Delta, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 := mul_le_mul (hP _ ha) (hz _ hb) (norm_nonneg _) hR
    have h2 := mul_le_mul (hP _ hb) (hz _ ha) (norm_nonneg _) hR
    have h3 := (norm_add_le _ _).trans (add_le_add ((norm_mul_le _ _).trans h1)
      ((norm_mul_le _ _).trans h2))
    calc |d| * ‖_‖ ≤ |d| * (R * B' + R * B') := mul_le_mul_of_nonneg_left h3 (abs_nonneg d)
      _ = 2 * |d| * B' * R := by ring
  induction k with
  | zero =>
    intro P R hP
    rw [zero_add, pow_one, pow_one, pow_zero, mul_one]
    exact step P R By y hBy hP hy
  | succ k ih =>
    intro P R hP
    rw [pow_succ', ← Matrix.mul_assoc]
    have hP' : ∀ p ∈ ({Sum.inl i, Sum.inr μ} : Finset (Fin M ⊕ Fin N)),
        ‖ent (P * (Delta i μ d * Q)) x (eI p)‖ ≤ 2 * |d| * B * R := fun p hp =>
      step P R B (eI p) hB hP fun q hq => by rw [ent_eI_eI]; exact hQ q hq p hp
    refine (ih _ _ hP').trans (le_of_eq ?_)
    ring


/-! ## `Σ̲`, `v̄` and `Π` -/

private theorem rbu_diag {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) :
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

private theorem rbu_sum_sq_UT {K : ℕ} {U : Matrix (Fin K) (Fin K) ℝ} (h₂ : U * Uᵀ = 1)
    (x : Fin K → ℝ) : ∑ i, (Uᵀ *ᵥ x) i ^ 2 = ∑ i, x i ^ 2 := by
  have e : (Uᵀ *ᵥ x) ⬝ᵥ (Uᵀ *ᵥ x) = x ⬝ᵥ x := by
    rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, h₂, one_mulVec, dotProduct_comm]
  simpa [dotProduct, sq] using e

private theorem rbu_row_sq {K : ℕ} {U : Matrix (Fin K) (Fin K) ℝ} (h₂ : U * Uᵀ = 1) (i : Fin K) :
    ∑ k, U i k ^ 2 = 1 := by
  have := congrFun (congrFun h₂ i) i
  simpa [Matrix.mul_apply, sq, Matrix.one_apply] using this

/-- `|Σ x|² ≤ τ⁻² |x|²` under (bound_Sigma). -/
private theorem rbu_sumsq_Sig {τ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hS : SigmaAssumption τ Sig) (x : Fin M → ℝ) :
    ∑ l, (Sig *ᵥ x) l ^ 2 ≤ τ⁻¹ ^ 2 * ∑ l, x l ^ 2 := by
  obtain ⟨U, h₂, h₁, hSd, hσ⟩ := rbu_diag hS.posDef
  have hle : ∀ k, specOf Sig k ≤ τ⁻¹ := fun k => by
    rw [specOf_eq hS.posDef.isHermitian]; exact hS.eigenvalues_le k
  have hUU : Uᵀ * Uᵀᵀ = 1 := by rw [transpose_transpose]; exact h₁
  have e : Sig *ᵥ x = Uᵀᵀ *ᵥ (diagonal (specOf Sig) *ᵥ (Uᵀ *ᵥ x)) := by
    rw [transpose_transpose, mulVec_mulVec, mulVec_mulVec]
    exact congrArg (· *ᵥ x) hSd
  rw [e, rbu_sum_sq_UT hUU, ← rbu_sum_sq_UT h₂ x, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [mulVec_diagonal, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hσ k).le (hle k) 2) (sq_nonneg _)

/-- `|Σ̲ y| ≤ τ⁻¹ |y|`. -/
private theorem rbu_testNorm_SigU {τ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hS : SigmaAssumption τ Sig) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (y : Fin M ⊕ Fin N → ℝ) :
    testNorm (SigU (n := Fin N) Sig *ᵥ y) ≤ τ⁻¹ * testNorm y := by
  have hτi : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  have h1 := rbu_sumsq_Sig hS (y ∘ Sum.inl)
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
private theorem rbu_vbar_SigU {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (y : Fin M ⊕ Fin N → ℝ) : vbar Sig (SigU (n := Fin N) Sig *ᵥ y) = y := by
  have hS : Sig⁻¹ * Sig = 1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hSig.isUnit)
  funext s
  rcases s with j | ν
  · simp [vbar, SigU, fromBlocks_mulVec, mulVec_mulVec, hS]
  · simp [vbar, SigU, fromBlocks_mulVec]


/-- `(1 + wΣ)⁻¹_{li} = ∑ₖ U_{lk} (1 + σₖ w)⁻¹ U_{ik}`. -/
private theorem rbu_cinv_entry {Sig U : Matrix (Fin M) (Fin M) ℝ} {σ : Fin M → ℝ}
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

private theorem rbu_abs_le_testNorm {ι : Type*} [Fintype ι] (x : ι → ℝ) (s : ι) :
    |x s| ≤ testNorm x := by
  unfold testNorm
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (fun t _ => sq_nonneg (x t)) (Finset.mem_univ s))

private theorem rbu_sqrt_inl_le (x : Fin M ⊕ Fin N → ℝ) :
    √(∑ j, x (Sum.inl j) ^ 2) ≤ testNorm x := by
  unfold testNorm
  refine Real.sqrt_le_sqrt ?_
  rw [Fintype.sum_sum_type]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- `|⟨v̄, Π e_p⟩| ≤ max(c⁻¹, K) |v|` when `|m| ≤ K` and `|1 + σᵢ m| ≥ c`. -/
private theorem rbu_pi_bound {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {c K : ℝ}
    (hc : 0 < c) {w : ℂ} (hwK : ‖w‖ ≤ K) (hOne : ∀ i, c ≤ ‖1 + (specOf Sig i : ℂ) * w‖)
    (x : Fin M ⊕ Fin N → ℝ) (p : Fin M ⊕ Fin N) :
    ‖ent (piMat (N := N) Sig w) (vbar Sig x) (eI p)‖ ≤ max c⁻¹ K * testNorm x := by
  rw [rbu_ent_eI_right, Fintype.sum_sum_type]
  rcases p with i | μ
  · simp only [piMat, fromBlocks_apply₁₁, fromBlocks_apply₂₁, Matrix.zero_apply, mul_zero,
      Finset.sum_const_zero, add_zero, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib, norm_neg]
    obtain ⟨U, h₂, h₁, hSd, hσ⟩ := rbu_diag hSig
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
      simp only [rbu_cinv_entry h₂ h₁ hSd hw0, Finset.mul_sum]
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
    rw [rbu_sum_sq_UT h₂, rbu_row_sq h₂, Real.sqrt_one, mul_one] at hcs
    have hc0 : 0 ≤ c⁻¹ := (inv_pos.2 hc).le
    calc _ ≤ ∑ k, c⁻¹ * (|(Uᵀ *ᵥ xM) k| * |U i k|) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => hb k)
      _ ≤ c⁻¹ * √(∑ j, xM j ^ 2) := by
          rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hcs hc0
      _ ≤ max c⁻¹ K * testNorm x :=
          mul_le_mul (le_max_left _ _) (rbu_sqrt_inl_le x) (Real.sqrt_nonneg _)
            (hc0.trans (le_max_left _ _))
  · simp only [piMat, fromBlocks_apply₁₂, fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero,
      Finset.sum_const_zero, zero_add, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
      mul_one, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [vbar, Sum.elim_inr, Function.comp_apply]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul (hwK.trans (le_max_right _ _)) (rbu_abs_le_testNorm x _) (abs_nonneg _)
      ((norm_nonneg w).trans (hwK.trans (le_max_right _ _)))


/-- `|⟨v̄, G e_p⟩| ≤ |⟨v, Σ̲⁻¹(G − Π)Σ̲⁻¹ (Σ̲ e_p)⟩| + max(c⁻¹, K) |v|`. -/
private theorem rbu_G_left {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {c K : ℝ}
    (hc : 0 < c) {z : ℂ} (hwK : ‖mFun N (specOf Sig) z‖ ≤ K)
    (hOne : ∀ i, c ≤ ‖1 + (specOf Sig i : ℂ) * mFun N (specOf Sig) z‖)
    (A : Matrix (Fin M) (Fin N) ℝ) (x : Fin M ⊕ Fin N → ℝ) (p : Fin M ⊕ Fin N) :
    ‖ent (G Sig A z) (vbar Sig x) (eI p)‖ ≤
      ‖testBilin x (lawMat Sig A z) (SigU (n := Fin N) Sig *ᵥ eI p)‖ + max c⁻¹ K * testNorm x := by
  have e : ent (G Sig A z) (vbar Sig x) (eI p) =
      ent (G Sig A z - PiZ N Sig z) (vbar Sig x) (vbar Sig (SigU (n := Fin N) Sig *ᵥ eI p)) +
        ent (PiZ N Sig z) (vbar Sig x) (eI p) := by
    rw [rbu_vbar_SigU hSig, rbu_ent_sub]; ring
  rw [e, ent_vbar_eq_testBilin hSig]
  exact (norm_add_le _ _).trans (add_le_add le_rfl (rbu_pi_bound hSig hc hwK hOne x p))

private theorem rbu_cplx_mulVec {ι : Type*} [Fintype ι] (S : Matrix ι ι ℝ) (b : ι → ℝ) :
    cplx S *ᵥ cvec b = cvec (S *ᵥ b) := by
  funext s
  simp [cplx, cvec, mulVec, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul]

/-- `⟨a, S M S b⟩ = ⟨S a, M S b⟩` for a real symmetric `S`. -/
private theorem rbu_ent_conj {ι : Type*} [Fintype ι] (S : Matrix ι ι ℝ) (hS : Sᵀ = S)
    (B : Matrix ι ι ℂ) (a b : ι → ℝ) :
    ent (cplx S * B * cplx S) a b = ent B (S *ᵥ a) (S *ᵥ b) := by
  have hC : (cplx S)ᵀ = cplx S := by rw [cplx, ← transpose_map, hS]
  unfold ent
  rw [← mulVec_mulVec, ← mulVec_mulVec, rbu_cplx_mulVec, dotProduct_mulVec, ← hC,
    vecMul_transpose, rbu_cplx_mulVec]

private theorem rbu_SigU_inv {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) :
    (SigU (n := Fin N) Sig)⁻¹ = SigU (n := Fin N) Sig⁻¹ := by
  have hS : Sig * Sig⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hSig.isUnit)
  apply Matrix.inv_eq_right_inv
  rw [SigU, SigU, fromBlocks_multiply, hS]
  simp [fromBlocks_one]

private theorem rbu_testNorm_eq {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    Real.sqrt (x ⬝ᵥ x) = testNorm x := by
  unfold testNorm
  simp [dotProduct, sq]

/-- `|⟨v̄, G e_p⟩| ≤ ((1 + ‖AᵀA‖)/η + 1) |v| |Σ̲ e_p| + |v|` (Lemma 4.9). -/
private theorem rbu_G_left_op {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (x : Fin M ⊕ Fin N → ℝ)
    (p : Fin M ⊕ Fin N) :
    ‖ent (G Sig A z) (vbar Sig x) (eI p)‖ ≤
      ((1 + ‖Aᵀ * A‖) / z.im + 1) * testNorm x * testNorm (SigU (n := Fin N) Sig *ᵥ eI p) +
        testNorm x := by
  have hT : Sigᵀ = Sig := by rw [← conjTranspose_eq_transpose_of_trivial]; exact hSig.1.eq
  have hTi : (SigU (n := Fin N) Sig⁻¹)ᵀ = SigU (n := Fin N) Sig⁻¹ := by
    rw [SigU, fromBlocks_transpose, transpose_nonsing_inv, hT]
    simp
  have hvb : ∀ y, SigU (n := Fin N) Sig⁻¹ *ᵥ y = vbar Sig y := fun y => by
    funext s
    rcases s with j | ν
    · simp [vbar, SigU, fromBlocks_mulVec]
    · simp [vbar, SigU, fromBlocks_mulVec]
  have h := opnorm_G hSig A hz x (SigU (n := Fin N) Sig *ᵥ eI p)
  rw [rbu_SigU_inv hSig, Matrix.mul_add, Matrix.add_mul, rbu_ent_add, rbu_ent_conj _ hTi,
    rbu_ent_conj _ hTi, hvb, hvb, rbu_vbar_SigU hSig, rbu_testNorm_eq, rbu_testNorm_eq] at h
  have hS : ‖ent (cplx (SigU (n := Fin N) Sig)) (vbar Sig x) (eI p)‖ ≤ testNorm x := by
    have hTS : (SigU (n := Fin N) Sig)ᵀ = SigU (n := Fin N) Sig := by
      rw [SigU, fromBlocks_transpose, hT]; simp
    have hSv : SigU (n := Fin N) Sig *ᵥ vbar Sig x = x := by
      have hS' : Sig * Sig⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hSig.isUnit)
      funext s
      rcases s with j | ν
      · simp [SigU, vbar, fromBlocks_mulVec, mulVec_mulVec, hS']
      · simp [SigU, vbar, fromBlocks_mulVec]
    have hC : (cplx (SigU (n := Fin N) Sig))ᵀ = cplx (SigU (n := Fin N) Sig) := by
      rw [cplx, ← transpose_map, hTS]
    have e : ent (cplx (SigU (n := Fin N) Sig)) (vbar Sig x) (eI p) = (x p : ℂ) := by
      rw [← rbu_ent_transpose, hC, rbu_ent_eI_left]
      conv_rhs => rw [← hSv]
      simp [cplx, mulVec, dotProduct, Complex.ofReal_sum]
    rw [e, Complex.norm_real, Real.norm_eq_abs]
    exact rbu_abs_le_testNorm x p
  calc ‖ent (G Sig A z) (vbar Sig x) (eI p)‖
      = ‖(ent (G Sig A z) (vbar Sig x) (eI p) +
          ent (cplx (SigU (n := Fin N) Sig)) (vbar Sig x) (eI p)) -
          ent (cplx (SigU (n := Fin N) Sig)) (vbar Sig x) (eI p)‖ := by rw [add_sub_cancel_right]
    _ ≤ _ := (norm_sub_le _ _).trans (add_le_add h hS)


/-- The setting of §7 gives the density assumptions on the eigenvalues of `Σ` (Lemma 4.10
input). -/
private theorem rbu_density {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) : DensityAssumptions τ N (specOf Sig) :=
  (IsModel.diagModel_specOf (Ω := GaussSpace M N)
    ⟨hset.ratio_ge, hset.ratio_le, (gaussX_isGaussianEnsemble M N).entryAssumption hN,
      hset.sigma⟩).densityAssumptions hset.pos

private theorem rbu_testNorm_eI {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι) :
    testNorm (eI p) = 1 := by
  unfold testNorm
  simp [eI, Pi.single_apply, Finset.sum_ite_eq']

/-! ## The deterministic estimate -/

/-- Lemma 7.14, deterministic part: with `G = G(A)`, `Gˢ = G(Aˢ)`, `Aˢ = A` with entry `(i, μ)`
replaced by `s`, `d = A_{iμ} − s`, (res_exp) at `K = 10` bounds `|⟨v, Σ̲⁻¹(Gˢ − Π)Σ̲⁻¹ w⟩|` by
`E + ∑_{k=1}^{10} (2|d|)^k (F τ⁻¹)^{k−1} F² + (2|d|)^{11} (F τ⁻¹)^{10} F F'` times `|v| |w|`, where
`E` bounds the entries `⟨x, Σ̲⁻¹(G − Π)Σ̲⁻¹ y⟩` for `x, y ∈ {v, w, Σ̲e_{(i)}, Σ̲e_{(μ)}}`,
`F = E τ⁻¹ + max(c⁻¹, K_m)` and `F' = ((1 + ‖AˢᵀAˢ‖)/η + 1) τ⁻¹ + 1` (Lemma 4.9). -/
private theorem rbu_det {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) {z : ℂ} (hz : z ∈ S)
    (A : Matrix (Fin M) (Fin N) ℝ) (i : Fin M) (μ : Fin N) (s : ℝ) (v w : Fin M ⊕ Fin N → ℝ)
    {E C₁ : ℝ}
    (hvw : ‖testBilin v (lawMat Sig A z) w‖ ≤ E * testNorm v * testNorm w)
    (hv : ∀ p ∈ ({Sum.inl i, Sum.inr μ} : Finset (Fin M ⊕ Fin N)),
      ‖testBilin v (lawMat Sig A z) (SigU (n := Fin N) Sig *ᵥ eI p)‖ ≤
        E * testNorm v * testNorm (SigU (n := Fin N) Sig *ᵥ eI p))
    (hw : ∀ p ∈ ({Sum.inl i, Sum.inr μ} : Finset (Fin M ⊕ Fin N)),
      ‖testBilin w (lawMat Sig A z) (SigU (n := Fin N) Sig *ᵥ eI p)‖ ≤
        E * testNorm w * testNorm (SigU (n := Fin N) Sig *ᵥ eI p))
    (huu : ∀ q ∈ ({Sum.inl i, Sum.inr μ} : Finset (Fin M ⊕ Fin N)),
      ∀ p ∈ ({Sum.inl i, Sum.inr μ} : Finset (Fin M ⊕ Fin N)),
      ‖testBilin (SigU (n := Fin N) Sig *ᵥ eI q) (lawMat Sig A z)
          (SigU (n := Fin N) Sig *ᵥ eI p)‖ ≤
        E * testNorm (SigU (n := Fin N) Sig *ᵥ eI q) * testNorm (SigU (n := Fin N) Sig *ᵥ eI p))
    (hE : 0 ≤ E) (hC₁ : ‖(Xupd A i μ s)ᵀ * Xupd A i μ s‖ ≤ C₁) :
    ‖testBilin v (lawMat Sig (Xupd A i μ s) z) w‖ ≤
      (E + ∑ k ∈ Finset.Icc 1 10, (2 * |A i μ - s|) ^ k *
          ((E * τ⁻¹ + max c⁻¹ (mBoundConst τ)) * τ⁻¹) ^ (k - 1) *
          (E * τ⁻¹ + max c⁻¹ (mBoundConst τ)) ^ 2 +
        (2 * |A i μ - s|) ^ 11 * ((E * τ⁻¹ + max c⁻¹ (mBoundConst τ)) * τ⁻¹) ^ 10 *
          (E * τ⁻¹ + max c⁻¹ (mBoundConst τ)) * (((1 + C₁) / z.im + 1) * τ⁻¹ + 1)) *
        testNorm v * testNorm w := by
  have hSig := hset.sigma.posDef
  have hτ := hset.pos
  have hzD := hset.domain.1 hz
  have hη : 0 < z.im := hzD.1
  have hm := (gen_prop_m_specDomain (rbu_density hset hN) hzD).2.1
  have hOne := hset.oneXm z hz
  set T := τ⁻¹ with hTdef
  set κ := max c⁻¹ (mBoundConst τ) with hκdef
  set F := E * T + κ with hFdef
  set d := A i μ - s with hd
  set G0 := G Sig A z with hG0
  set Gs := G Sig (Xupd A i μ s) z with hGs
  set Pset : Finset (Fin M ⊕ Fin N) := {Sum.inl i, Sum.inr μ} with hPset
  have hT0 : 0 ≤ T := (inv_pos.2 hτ).le
  have hκ0 : 0 ≤ κ := (inv_pos.2 hset.c_pos).le.trans (le_max_left _ _)
  have hu : ∀ p, testNorm (SigU (n := Fin N) Sig *ᵥ eI p) ≤ T := fun p => by
    have := rbu_testNorm_SigU (N := N) hset.sigma hτ hset.le_one (eI p)
    rwa [rbu_testNorm_eI, mul_one] at this
  have hnv : 0 ≤ testNorm v := Real.sqrt_nonneg _
  have hnw : 0 ≤ testNorm w := Real.sqrt_nonneg _
  -- base entries of `G`
  have hleft : ∀ x : Fin M ⊕ Fin N → ℝ, ∀ p ∈ Pset,
      ‖testBilin x (lawMat Sig A z) (SigU (n := Fin N) Sig *ᵥ eI p)‖ ≤
        E * testNorm x * testNorm (SigU (n := Fin N) Sig *ᵥ eI p) →
      ‖ent G0 (vbar Sig x) (eI p)‖ ≤ F * testNorm x := by
    intro x p _ hx
    have hnx : 0 ≤ testNorm x := Real.sqrt_nonneg _
    refine (rbu_G_left hSig hset.c_pos hm hOne A x p).trans ?_
    have : E * testNorm x * testNorm (SigU (n := Fin N) Sig *ᵥ eI p) ≤ E * testNorm x * T :=
      mul_le_mul_of_nonneg_left (hu p) (mul_nonneg hE hnx)
    nlinarith
  have hP0 : ∀ p ∈ Pset, ‖ent G0 (vbar Sig v) (eI p)‖ ≤ F * testNorm v :=
    fun p hp => hleft v p hp (hv p hp)
  have hQ : ∀ q ∈ Pset, ∀ p ∈ Pset, ‖G0 q p‖ ≤ F * T := by
    intro q hq p hp
    rw [← ent_eI_eI G0 q p, ← rbu_vbar_SigU (N := N) hSig (eI q)]
    refine (hleft _ p hp (huu q hq p hp)).trans ?_
    exact mul_le_mul_of_nonneg_left (hu q) (add_nonneg (mul_nonneg hE hT0) hκ0)
  have hy : ∀ q ∈ Pset, ‖ent G0 (eI q) (vbar Sig w)‖ ≤ F * testNorm w := by
    intro q hq
    rw [← rbu_ent_transpose, hG0, G_transpose hSig A hη]
    exact hleft w q hq (hw q hq)
  have hPs : ∀ p ∈ Pset, ‖ent Gs (vbar Sig v) (eI p)‖ ≤
      (((1 + C₁) / z.im + 1) * T + 1) * testNorm v := by
    intro p _
    refine (rbu_G_left_op hSig (Xupd A i μ s) hη v p).trans ?_
    have h1 : (1 + ‖(Xupd A i μ s)ᵀ * Xupd A i μ s‖) / z.im + 1 ≤ (1 + C₁) / z.im + 1 := by
      gcongr
    have h0 : 0 ≤ (1 + ‖(Xupd A i μ s)ᵀ * Xupd A i μ s‖) / z.im + 1 := by positivity
    have h2 := mul_le_mul h1 (hu p) (Real.sqrt_nonneg _) (h0.trans h1)
    nlinarith
  -- (res_exp) at `K = 10`
  have hexp := res_exp hSig A hη i μ (A i μ) s 10
  rw [Xupd_self] at hexp
  have e : testBilin v (lawMat Sig (Xupd A i μ s) z) w =
      testBilin v (lawMat Sig A z) w +
        ∑ k ∈ Finset.Icc 1 10, ent (G0 * (Delta i μ d * G0) ^ k) (vbar Sig v) (vbar Sig w) +
        ent (Gs * (Delta i μ d * G0) ^ (10 + 1)) (vbar Sig v) (vbar Sig w) := by
    rw [← ent_vbar_eq_testBilin hSig, ← ent_vbar_eq_testBilin hSig]
    have : Gs - PiZ N Sig z = (G0 - PiZ N Sig z) +
        ∑ k ∈ Finset.Icc 1 10, G0 * (Delta i μ d * G0) ^ k +
        Gs * (Delta i μ d * G0) ^ (10 + 1) := by
      conv_lhs => rw [hGs, hexp]
      abel
    rw [this, rbu_ent_add, rbu_ent_add, rbu_ent_sum]
  rw [e]
  have hterm : ∀ k ∈ Finset.Icc 1 10,
      ‖ent (G0 * (Delta i μ d * G0) ^ k) (vbar Sig v) (vbar Sig w)‖ ≤
        (2 * |d|) ^ k * (F * T) ^ (k - 1) * F ^ 2 * testNorm v * testNorm w := by
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by have := (Finset.mem_Icc.1 hk).1; omega⟩
    refine (rbu_word G0 i μ d (vbar Sig v) (vbar Sig w) hQ hy j G0 _ hP0).trans (le_of_eq ?_)
    rw [Nat.add_sub_cancel]
    ring
  have hrem : ‖ent (Gs * (Delta i μ d * G0) ^ (10 + 1)) (vbar Sig v) (vbar Sig w)‖ ≤
      (2 * |d|) ^ 11 * (F * T) ^ 10 * F * (((1 + C₁) / z.im + 1) * T + 1) *
        testNorm v * testNorm w := by
    refine (rbu_word G0 i μ d (vbar Sig v) (vbar Sig w) hQ hy 10 Gs _ hPs).trans (le_of_eq ?_)
    ring
  have hsum := (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
  calc _ ≤ ‖testBilin v (lawMat Sig A z) w‖ +
        ‖∑ k ∈ Finset.Icc 1 10, ent (G0 * (Delta i μ d * G0) ^ k) (vbar Sig v) (vbar Sig w)‖ +
        ‖ent (Gs * (Delta i μ d * G0) ^ (10 + 1)) (vbar Sig v) (vbar Sig w)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ E * testNorm v * testNorm w +
        ∑ k ∈ Finset.Icc 1 10, (2 * |d|) ^ k * (F * T) ^ (k - 1) * F ^ 2 * testNorm v *
          testNorm w +
        (2 * |d|) ^ 11 * (F * T) ^ 10 * F * (((1 + C₁) / z.im + 1) * T + 1) *
          testNorm v * testNorm w := add_le_add (add_le_add hvw hsum) hrem
    _ = _ := by
        simp only [add_mul, Finset.sum_mul]


private theorem rbu_pow_id (dd E Q : ℝ) (j : ℕ) :
    dd ^ (j + 1) * (E * Q ^ 2) ^ j * (E * Q) ^ 2 = E * (dd * E * Q ^ 2) ^ (j + 1) := by
  ring

/-- Exponent bookkeeping of Lemma 7.14, with `ϑ = N^{ε_A − 1/2}`, `E = N^{2δ + 2ε_A}`,
`θ = N^{−1/4}`: the coefficient of the deterministic estimate is at most `2E`. -/
private theorem rbu_num {E T κ C₁ dd ϑ η Nr θ : ℝ} (hE : 1 ≤ E) (hT : 1 ≤ T) (hκ : 0 ≤ κ)
    (hC₁ : 0 ≤ C₁) (hdd0 : 0 ≤ dd) (hdd : dd ≤ 4 * ϑ) (hN : 1 ≤ Nr) (hη : 0 < η)
    (hηN : 1 ≤ Nr * η) (hθ1 : ϑ * E ≤ θ) (hθ2 : ϑ ^ 3 * E ^ 2 * Nr ≤ θ)
    (hQ1 : 80 * (T + κ) ^ 2 * θ ≤ 1) (hQ2 : 128 * (C₁ + 3) * (T + κ) ^ 6 * θ ≤ 1) :
    E + ∑ k ∈ Finset.Icc 1 10, dd ^ k * ((E * T + κ) * T) ^ (k - 1) * (E * T + κ) ^ 2 +
      dd ^ 11 * ((E * T + κ) * T) ^ 10 * (E * T + κ) * (((1 + C₁) / η + 1) * T + 1) ≤
      2 * E := by
  set Q := T + κ with hQ
  set F := E * T + κ with hFdef
  have hϑ : 0 ≤ ϑ := by linarith
  have hE0 : 0 ≤ E := by linarith
  have hQ1' : 1 ≤ Q := by linarith
  have hF0 : 0 ≤ F := by positivity
  have hF : F ≤ E * Q := by nlinarith
  have hFT : F * T ≤ E * Q ^ 2 := by
    calc F * T ≤ (E * Q) * Q := mul_le_mul hF (by linarith) (by linarith) (by positivity)
      _ = E * Q ^ 2 := by ring
  have hFp : ((1 + C₁) / η + 1) * T + 1 ≤ (C₁ + 3) * Nr * Q := by
    have h1 : (1 + C₁) / η ≤ (1 + C₁) * Nr := by
      rw [div_le_iff₀ hη]; nlinarith
    have h2 : ((1 + C₁) / η + 1) * T ≤ ((1 + C₁) * Nr + 1) * T :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have h3 : T ≤ Nr * T := le_mul_of_one_le_left (by linarith) hN
    have h4 : 0 ≤ (C₁ + 3) * Nr * κ := by positivity
    have e1 : (C₁ + 3) * Nr * Q = (1 + C₁) * Nr * T + 2 * (Nr * T) + (C₁ + 3) * Nr * κ := by
      rw [hQ]; ring
    have e2 : ((1 + C₁) * Nr + 1) * T = (1 + C₁) * Nr * T + T := by ring
    linarith
  set r := dd * E * Q ^ 2 with hr
  have hr0 : 0 ≤ r := by positivity
  have hr20 : 20 * r ≤ 1 := by
    calc 20 * r = 20 * dd * E * Q ^ 2 := by rw [hr]; ring
      _ ≤ 20 * (4 * ϑ) * E * Q ^ 2 := by gcongr
      _ = 80 * Q ^ 2 * (ϑ * E) := by ring
      _ ≤ 80 * Q ^ 2 * θ := by gcongr
      _ ≤ 1 := hQ1
  have hr1 : r ≤ 1 := by linarith
  have hterm : ∀ k ∈ Finset.Icc 1 10,
      dd ^ k * (F * T) ^ (k - 1) * F ^ 2 ≤ E * r := by
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by have := (Finset.mem_Icc.1 hk).1; omega⟩
    rw [Nat.add_sub_cancel]
    calc dd ^ (j + 1) * (F * T) ^ j * F ^ 2 ≤ dd ^ (j + 1) * (E * Q ^ 2) ^ j * (E * Q) ^ 2 := by
          gcongr
      _ = E * r ^ (j + 1) := by rw [hr]; exact rbu_pow_id dd E Q j
      _ ≤ E * r := mul_le_mul_of_nonneg_left (pow_le_of_le_one hr0 hr1 (by omega)) hE0
  have hsum : ∑ k ∈ Finset.Icc 1 10, dd ^ k * (F * T) ^ (k - 1) * F ^ 2 ≤ E / 2 := by
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    norm_num
    nlinarith
  have hrem : dd ^ 11 * (F * T) ^ 10 * F * (((1 + C₁) / η + 1) * T + 1) ≤ E / 2 := by
    have hr2 : r ^ 10 ≤ r ^ 2 := pow_le_pow_of_le_one hr0 hr1 (by norm_num)
    have hk : r ^ 2 * dd * ((C₁ + 3) * Nr * Q ^ 2) ≤ 1 / 2 := by
      calc r ^ 2 * dd * ((C₁ + 3) * Nr * Q ^ 2)
          ≤ ((4 * ϑ) * E * Q ^ 2) ^ 2 * (4 * ϑ) * ((C₁ + 3) * Nr * Q ^ 2) := by
            rw [hr]; gcongr
        _ = 64 * (C₁ + 3) * Q ^ 6 * (ϑ ^ 3 * E ^ 2 * Nr) := by ring
        _ ≤ 64 * (C₁ + 3) * Q ^ 6 * θ := by gcongr
        _ ≤ 1 / 2 := by linarith
    calc dd ^ 11 * (F * T) ^ 10 * F * (((1 + C₁) / η + 1) * T + 1)
        ≤ dd ^ 11 * (E * Q ^ 2) ^ 10 * (E * Q) * ((C₁ + 3) * Nr * Q) := by
          gcongr
      _ = E * r ^ 10 * (dd * ((C₁ + 3) * Nr * Q ^ 2)) := by rw [hr]; ring
      _ ≤ E * r ^ 2 * (dd * ((C₁ + 3) * Nr * Q ^ 2)) := by gcongr
      _ = E * (r ^ 2 * dd * ((C₁ + 3) * Nr * Q ^ 2)) := by ring
      _ ≤ E * (1 / 2) := mul_le_mul_of_nonneg_left hk hE0
      _ = E / 2 := by ring
  linarith

/-- `‖AˢᵀAˢ‖ ≤ C₁` for `|s| ≤ 1` when it holds at `s = ±1` (convexity of the operator norm). -/
private theorem rbu_norm_upd (A : Matrix (Fin M) (Fin N) ℝ) (i : Fin M) (μ : Fin N) {s C₁ : ℝ}
    (hs : |s| ≤ 1) (h1 : ‖(Xupd A i μ 1)ᵀ * Xupd A i μ 1‖ ≤ C₁)
    (h2 : ‖(Xupd A i μ (-1))ᵀ * Xupd A i μ (-1)‖ ≤ C₁) :
    ‖(Xupd A i μ s)ᵀ * Xupd A i μ s‖ ≤ C₁ := by
  have hsq : ∀ B : Matrix (Fin M) (Fin N) ℝ, ‖Bᵀ * B‖ = ‖B‖ * ‖B‖ := fun B => by
    simpa [conjTranspose_eq_transpose_of_trivial] using l2_opNorm_conjTranspose_mul_self B
  rw [hsq] at h1 h2 ⊢
  have e : Xupd A i μ s = ((1 + s) / 2) • Xupd A i μ 1 + ((1 - s) / 2) • Xupd A i μ (-1) := by
    ext j ν
    simp only [Xupd, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> ring
  obtain ⟨hs1, hs2⟩ := abs_le.1 hs
  set n₁ := ‖Xupd A i μ 1‖
  set n₂ := ‖Xupd A i μ (-1)‖
  have hn₁ : 0 ≤ n₁ := norm_nonneg _
  have hn₂ : 0 ≤ n₂ := norm_nonneg _
  have hle : ‖Xupd A i μ s‖ ≤ max n₁ n₂ := by
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith),
      Real.norm_of_nonneg (by linarith)]
    have := le_max_left n₁ n₂
    have := le_max_right n₁ n₂
    nlinarith
  have hm : max n₁ n₂ * max n₁ n₂ ≤ C₁ := by
    rcases le_total n₁ n₂ with h | h
    · rw [max_eq_right h]; exact h2
    · rw [max_eq_left h]; exact h1
  exact (mul_self_le_mul_self (norm_nonneg _) hle).trans hm

/-! ## Lemma 7.14 -/

/-- Lemma 7.14 at a general `C₀`. -/
private theorem rbu_main (τ c : ℝ) (C : ℕ → ℝ) (C₀ δ εA DA : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hc : 0 < c) (hδ : 0 < δ) (hC₀ : 25 ≤ C₀) (hC₀δ : C₀ * δ ≤ τ / 4) (hεA : 0 < εA)
    (hεAδ : εA ≤ δ / 4) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ)
      (P : ModelClass M N) (m : ℕ), CompSetting τ c M N Sig S → 1 ≤ m →
      PropA N C P Sig S C₀ δ (m - 1) εA DA →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ) (y : Ω → ℝ), EntryAssumption C X → P Ω X →
        HighProbAt N DA {ω | |y ω| ≤ (N : ℝ) ^ (εA - 1 / 2)} →
        ∀ z ∈ levelSet N δ S m, ∀ (i : Fin M) (μ : Fin N) (v w : Fin M ⊕ Fin N → ℝ),
          HighProbAt N (DA - 2) {ω | ∀ s : ℝ, |s| ≤ |y ω| →
            ‖testBilin v (lawMat Sig (Xupd (X ω) i μ s) z) w‖ ≤
              (N : ℝ) ^ (2 * δ + 3 * εA) * testNorm v * testNorm w} := by
  obtain ⟨N₁, h₁⟩ := cor_rough_bound' τ c C C₀ δ εA DA hτ hτ1 hc hδ hC₀ hC₀δ hεA
  obtain ⟨C₁, hC₁⟩ := norm_XtX_updEntry_le hτ hτ1
  obtain ⟨N₂, h₂⟩ := hC₁ C (DA - 1)
  have hδ1 : δ ≤ 1 / 100 := by nlinarith
  set C₁' := max C₁ 0 with hC₁'
  set κ := max c⁻¹ (mBoundConst τ) with hκ
  set Q := τ⁻¹ + κ with hQ
  set Kb := max (80 * Q ^ 2) (128 * (C₁' + 3) * Q ^ 6) with hKb
  set q : ℕ := ⌈2 * max (DA - 1) 0 / εA⌉₊ + 1 with hq
  set Cq := max (C q) 1 with hCq
  refine ⟨max (max (max N₁ N₂) 20) (max (max (⌈Kb⌉₊ ^ 4) ⌈(2 : ℝ) ^ εA⁻¹⌉₊)
    ⌈Cq ^ (2 / εA)⌉₊), ?_⟩
  intro N hN M Sig S P m hset hm hA Ω _ _ X y hX hP hy z hz i μ v w
  have hNN₁ : N₁ ≤ N := by omega
  have hNN₂ : N₂ ≤ N := by omega
  have hN20 : 20 ≤ N := by omega
  have hNK : ⌈Kb⌉₊ ^ 4 ≤ N := by omega
  have hN2e : ⌈(2 : ℝ) ^ εA⁻¹⌉₊ ≤ N := by omega
  have hNq : ⌈Cq ^ (2 / εA)⌉₊ ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hNr : (20 : ℝ) ≤ N := by exact_mod_cast hN20
  have hNp : (0 : ℝ) < N := by linarith
  have hN1r : (1 : ℝ) ≤ N := by linarith
  -- size conditions on `N`
  have hKb0 : 0 ≤ Kb := by
    have : 0 ≤ 80 * Q ^ 2 := by positivity
    exact this.trans (le_max_left _ _)
  have hKbN : Kb ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
    have h0 : Kb ^ 4 ≤ (N : ℝ) := by
      have h1 : (⌈Kb⌉₊ : ℝ) ^ 4 ≤ N := by exact_mod_cast hNK
      exact (pow_le_pow_left₀ hKb0 (Nat.le_ceil Kb) 4).trans h1
    have h3 : (Kb ^ 4) ^ (1 / 4 : ℝ) = Kb := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hKb0]
      norm_num
    rw [← h3]
    exact Real.rpow_le_rpow (by positivity) h0 (by norm_num)
  have hθ : (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (-(1 / 4) : ℝ) = 1 := by
    rw [← Real.rpow_add hNp]; norm_num
  have hθ0 : 0 ≤ (N : ℝ) ^ (-(1 / 4) : ℝ) := Real.rpow_nonneg hNp.le _
  have h2e : 2 ≤ (N : ℝ) ^ εA := by
    have h1 : (2 : ℝ) ^ εA⁻¹ ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN2e)
    calc (2 : ℝ) = ((2 : ℝ) ^ εA⁻¹) ^ εA := by
          rw [← Real.rpow_mul (by norm_num), inv_mul_cancel₀ hεA.ne', Real.rpow_one]
      _ ≤ (N : ℝ) ^ εA := Real.rpow_le_rpow (by positivity) h1 hεA.le
  have hCqN : Cq ≤ (N : ℝ) ^ (εA / 2) := by
    have hCq0 : 0 ≤ Cq := zero_le_one.trans (le_max_right _ _)
    have h1 : Cq ^ (2 / εA) ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hNq)
    calc Cq = (Cq ^ (2 / εA)) ^ (εA / 2) := by
          rw [← Real.rpow_mul hCq0, div_mul_div_comm, mul_comm 2 εA,
            div_self (by positivity), Real.rpow_one]
      _ ≤ (N : ℝ) ^ (εA / 2) := Real.rpow_le_rpow (by positivity) h1 (by positivity)
  have hM : (M : ℝ) ≤ τ⁻¹ * N := by
    have := hset.ratio_le
    rwa [div_le_iff₀ hNp] at this
  -- the events
  obtain ⟨hap, -⟩ := h₁ N hNN₁ M Sig S P m hset hm hA Ω X hX hP z hz
  set u : Fin M ⊕ Fin N → Fin M ⊕ Fin N → ℝ := fun p => SigU (n := Fin N) Sig *ᵥ eI p with hu
  set L : Fin 4 → Fin M ⊕ Fin N → ℝ := ![v, w, u (Sum.inl i), u (Sum.inr μ)] with hL
  set ϑ : ℝ := (N : ℝ) ^ (εA - 1 / 2) with hϑ
  let Ev : (Fin 4 × Fin 4) ⊕ Fin 4 → Set Ω := Sum.elim
    (fun jk => {ω | ‖testBilin (L jk.1) (lawMat Sig (X ω) z) (L jk.2)‖ ≤
      (N : ℝ) ^ (2 * εA) * ((N : ℝ) ^ (2 * δ) * testNorm (L jk.1) * testNorm (L jk.2))})
    ![{ω | ‖(updEntry (X ω) i μ 1)ᵀ * updEntry (X ω) i μ 1‖ ≤ C₁},
      {ω | ‖(updEntry (X ω) i μ (-1))ᵀ * updEntry (X ω) i μ (-1)‖ ≤ C₁},
      {ω | |Real.sqrt N * X ω i μ| ≤ (N : ℝ) ^ εA * 1},
      {ω | |y ω| ≤ ϑ}]
  have hEv : ∀ ι ∈ (Finset.univ : Finset ((Fin 4 × Fin 4) ⊕ Fin 4)),
      HighProbAt N (DA - 2 + 1) (Ev ι) := by
    intro ι _
    rw [show DA - 2 + 1 = DA - 1 by ring]
    rcases ι with ⟨j, k⟩ | t
    · have h := hap (L j) (L k)
      unfold DomAt at h
      unfold HighProbAt
      simpa [Ev, Set.compl_ofPred, not_le] using h
    · have htriv : ∀ r : ℝ, |r| ≤ 1 →
          HighProbAt N (DA - 1 + 1) {ω : Ω | |(fun _ => r) ω| ≤ 1} := by
        intro r hr
        unfold HighProbAt
        have : {ω : Ω | |(fun _ => r) ω| ≤ 1}ᶜ = ∅ := by ext ω; simp [hr]
        rw [this, measure_empty]
        exact zero_le
      fin_cases t
      · exact h₂ N hNN₂ M X i μ (fun _ => 1) hX hM (htriv 1 (by norm_num))
      · exact h₂ N hNN₂ M X i μ (fun _ => -1) hX hM (htriv (-1) (by norm_num))
      · have hq1 : 2 * max (DA - 1) 0 / εA ≤ (q : ℝ) := by
          rw [hq]
          push_cast
          linarith [Nat.le_ceil (2 * max (DA - 1) 0 / εA)]
        have hp : DA - 1 ≤ (εA - εA / 2) * q := by
          calc DA - 1 ≤ max (DA - 1) 0 := le_max_left _ _
            _ = (εA - εA / 2) * (2 * max (DA - 1) 0 / εA) := by field_simp; ring
            _ ≤ (εA - εA / 2) * q := mul_le_mul_of_nonneg_left hq1 (by linarith)
        have hNe1 : 1 ≤ (N : ℝ) ^ (εA / 2) := Real.one_le_rpow hN1r (by positivity)
        have hmom : ∫ ω, |Real.sqrt N * X ω i μ| ^ q ≤ ((N : ℝ) ^ (εA / 2) * 1) ^ q := by
          rw [mul_one]
          calc ∫ ω, |Real.sqrt N * X ω i μ| ^ q ≤ C q := hX.moment q i μ
            _ ≤ Cq := le_max_left _ _
            _ ≤ (N : ℝ) ^ (εA / 2) := hCqN
            _ ≤ ((N : ℝ) ^ (εA / 2)) ^ q := le_self_pow₀ hNe1 (by omega)
        have hd := DomAt.of_moment (ε := εA / 2) (ε' := εA) (D := DA - 1) (ζ := 1)
          (ξ := fun ω => |Real.sqrt N * X ω i μ|) q hN1 hp (fun ω => abs_nonneg _) one_pos
          (hX.integrable_moment q i μ) hmom
        unfold DomAt at hd
        unfold HighProbAt
        simpa [Ev, Set.compl_ofPred, not_le] using hd
      · unfold HighProbAt at hy ⊢
        refine hy.trans (ENNReal.ofReal_le_ofReal ?_)
        exact Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
  have hcard : ((Finset.univ : Finset ((Fin 4 × Fin 4) ⊕ Fin 4)).card : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) := by
    rw [Real.rpow_one, Finset.card_univ]
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    norm_num
    linarith
  have hall := HighProbAt.biInter Finset.univ hN1 hcard hEv
  unfold HighProbAt at hall ⊢
  refine le_trans (measure_mono (Set.compl_subset_compl.2 ?_)) hall
  intro ω hω s hs
  have hω' : ∀ ι, ω ∈ Ev ι := fun ι => Set.mem_iInter₂.1 hω ι (Finset.mem_univ _)
  set E : ℝ := (N : ℝ) ^ (2 * εA) * (N : ℝ) ^ (2 * δ) with hEdef
  have hLb : ∀ j k, ‖testBilin (L j) (lawMat Sig (X ω) z) (L k)‖ ≤
      E * testNorm (L j) * testNorm (L k) := fun j k => by
    have h : ‖testBilin (L j) (lawMat Sig (X ω) z) (L k)‖ ≤
        (N : ℝ) ^ (2 * εA) * ((N : ℝ) ^ (2 * δ) * testNorm (L j) * testNorm (L k)) :=
      hω' (Sum.inl (j, k))
    calc _ ≤ _ := h
      _ = _ := by rw [hEdef]; ring
  have hF0 : ‖(updEntry (X ω) i μ 1)ᵀ * updEntry (X ω) i μ 1‖ ≤ C₁ := hω' (Sum.inr 0)
  have hF1 : ‖(updEntry (X ω) i μ (-1))ᵀ * updEntry (X ω) i μ (-1)‖ ≤ C₁ := hω' (Sum.inr 1)
  have hF2 : |Real.sqrt N * X ω i μ| ≤ (N : ℝ) ^ εA * 1 := hω' (Sum.inr 2)
  have hF3 : |y ω| ≤ ϑ := hω' (Sum.inr 3)
  -- the scalars
  have hϑ1 : ϑ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1r (by linarith)
  have hϑ0 : 0 ≤ ϑ := Real.rpow_nonneg hNp.le _
  have hs1 : |s| ≤ ϑ := hs.trans hF3
  have hX1 : |X ω i μ| ≤ ϑ := by
    have hsq : Real.sqrt N = (N : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
    have hsq0 : 0 < Real.sqrt N := Real.sqrt_pos.2 hNp
    rw [abs_mul, abs_of_pos hsq0, mul_one] at hF2
    rw [hϑ, Real.rpow_sub hNp, ← hsq, le_div_iff₀ hsq0, mul_comm]
    exact hF2
  have hdd : 2 * |X ω i μ - s| ≤ 4 * ϑ := by
    have := abs_sub (X ω i μ) s
    linarith
  have hAs : ‖(Xupd (X ω) i μ s)ᵀ * Xupd (X ω) i μ s‖ ≤ C₁' := by
    refine rbu_norm_upd (X ω) i μ (hs1.trans hϑ1) ?_ ?_
    · rw [Xupd_eq_updEntry]; exact hF0.trans (le_max_left _ _)
    · rw [Xupd_eq_updEntry]; exact hF1.trans (le_max_left _ _)
  have hE1 : 1 ≤ E := one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hN1r (by positivity))
    (Real.one_le_rpow hN1r (by positivity))
  have hPa : Sum.inl i ∈ ({Sum.inl i, Sum.inr μ} : Finset (Fin M ⊕ Fin N)) := by simp
  have hdet := rbu_det hset hN1 hz.1 (X ω) i μ s v w (C₁ := C₁') (hLb 0 1)
    (fun p hp => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact hLb 0 2
      · exact hLb 0 3)
    (fun p hp => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact hLb 1 2
      · exact hLb 1 3)
    (fun q hq p hp => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
      rcases hq with rfl | rfl <;> rcases hp with rfl | rfl
      · exact hLb 2 2
      · exact hLb 2 3
      · exact hLb 3 2
      · exact hLb 3 3)
    (by linarith) hAs
  -- the exponents
  have hzD := hset.domain.1 hz.1
  have hηN : 1 ≤ (N : ℝ) * z.im := by
    have h1 : (N : ℝ) * (N : ℝ) ^ (-1 + τ) = (N : ℝ) ^ τ := by
      rw [mul_comm, ← Real.rpow_add_one hNp.ne']; ring_nf
    have h2 : 1 ≤ (N : ℝ) ^ τ := Real.one_le_rpow hN1r hτ.le
    calc (1 : ℝ) ≤ (N : ℝ) ^ τ := h2
      _ = (N : ℝ) * (N : ℝ) ^ (-1 + τ) := h1.symm
      _ ≤ (N : ℝ) * z.im := mul_le_mul_of_nonneg_left hzD.2.2.2.1 hNp.le
  have hθ1 : ϑ * E ≤ (N : ℝ) ^ (-(1 / 4) : ℝ) := by
    have e : ϑ * E = (N : ℝ) ^ (3 * εA + 2 * δ - 1 / 2) := by
      rw [hϑ, hEdef, show 3 * εA + 2 * δ - 1 / 2 = (εA - 1 / 2) + 2 * εA + 2 * δ by ring,
        Real.rpow_add hNp, Real.rpow_add hNp]
      ring
    rw [e]
    exact Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
  have hθ2 : ϑ ^ 3 * E ^ 2 * (N : ℝ) ≤ (N : ℝ) ^ (-(1 / 4) : ℝ) := by
    have e : ϑ ^ 3 * E ^ 2 * (N : ℝ) = (N : ℝ) ^ (7 * εA + 4 * δ - 1 / 2) := by
      rw [hϑ, hEdef, show 7 * εA + 4 * δ - 1 / 2 = (εA - 1 / 2) + (εA - 1 / 2) + (εA - 1 / 2) +
        2 * εA + 2 * δ + 2 * εA + 2 * δ + 1 by ring]
      simp only [Real.rpow_add hNp, Real.rpow_one]
      ring
    rw [e]
    exact Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
  have hQ1 : 80 * (τ⁻¹ + κ) ^ 2 * (N : ℝ) ^ (-(1 / 4) : ℝ) ≤ 1 := by
    calc 80 * (τ⁻¹ + κ) ^ 2 * (N : ℝ) ^ (-(1 / 4) : ℝ)
        ≤ (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (-(1 / 4) : ℝ) :=
          mul_le_mul_of_nonneg_right ((le_max_left _ _).trans hKbN) hθ0
      _ = 1 := hθ
  have hQ2 : 128 * (C₁' + 3) * (τ⁻¹ + κ) ^ 6 * (N : ℝ) ^ (-(1 / 4) : ℝ) ≤ 1 := by
    calc 128 * (C₁' + 3) * (τ⁻¹ + κ) ^ 6 * (N : ℝ) ^ (-(1 / 4) : ℝ)
        ≤ (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (-(1 / 4) : ℝ) :=
          mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hKbN) hθ0
      _ = 1 := hθ
  have hnum := rbu_num hE1 ((one_le_inv₀ hτ).2 hτ1)
    ((inv_pos.2 hc).le.trans (le_max_left _ _)) (le_max_right C₁ 0) (by positivity) hdd hN1r
    hzD.1 hηN hθ1 hθ2 hQ1 hQ2
  have hnv : 0 ≤ testNorm v := Real.sqrt_nonneg _
  have hnw : 0 ≤ testNorm w := Real.sqrt_nonneg _
  have hfin : 2 * E ≤ (N : ℝ) ^ (2 * δ + 3 * εA) := by
    have e : (N : ℝ) ^ (2 * δ + 3 * εA) = (N : ℝ) ^ εA * E := by
      rw [hEdef, show 2 * δ + 3 * εA = εA + 2 * εA + 2 * δ by ring, Real.rpow_add hNp,
        Real.rpow_add hNp]
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_right h2e (by linarith)
  refine hdet.trans ?_
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hnum.trans hfin) hnv) hnw
  exact this

/-- Lemma 7.14 (`lem:rough bound`) at a general `C₀`. -/
theorem rough_bound_upd' (τ c : ℝ) (C : ℕ → ℝ) (C₀ δ εA DA : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hc : 0 < c) (hδ : 0 < δ) (hC₀ : 25 ≤ C₀) (hC₀δ : C₀ * δ ≤ τ / 4) (hεA : 0 < εA)
    (hεAδ : εA ≤ δ / 4) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ)
      (P : ModelClass M N) (m : ℕ), CompSetting τ c M N Sig S → 1 ≤ m →
      PropA N C P Sig S C₀ δ (m - 1) εA DA →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ) (y : Ω → ℝ), EntryAssumption C X → P Ω X →
        HighProbAt N DA {ω | |y ω| ≤ (N : ℝ) ^ (εA - 1 / 2)} →
        ∀ z ∈ levelSet N δ S m, ∀ (i : Fin M) (μ : Fin N) (v w : Fin M ⊕ Fin N → ℝ),
          HighProbAt N (DA - 2) {ω | ∀ s : ℝ, |s| ≤ |y ω| →
            ‖testBilin v (lawMat Sig (Xupd (X ω) i μ s) z) w‖ ≤
              (N : ℝ) ^ (2 * δ + 3 * εA) * testNorm v * testNorm w} :=
  rbu_main τ c C C₀ δ εA DA hτ hτ1 hc hδ hC₀ hC₀δ hεA hεAδ

/-! ## Instances

The parameters are `τ = 1/2`, `c = 1`, `C = 2`, `δ = 1/200` (`δ = τ/100`, `25δ = τ/4`),
`ε_A = 1/800 = δ/4`, `D_A = 3`. The setting, (A_{m−1}), the class, the entry conditions and
the bound on `y` are hypotheses of the statements (conditional in them); in the last instance
(A_0) is supplied by Lemma 7.3 and `y = 0`. -/

/-- Lemma 7.14 at a general `C₀`, instance `C₀ = 25` (`C₀ δ = τ/4`), other parameters as
above. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ)
      (P : ModelClass M N) (m : ℕ), CompSetting (1 / 2) 1 M N Sig S → 1 ≤ m →
      PropA N (fun _ => 2) P Sig S 25 (1 / 200) (m - 1) (1 / 800) 3 →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ) (y : Ω → ℝ), EntryAssumption (fun _ => 2) X →
        P Ω X → HighProbAt N 3 {ω | |y ω| ≤ (N : ℝ) ^ ((1 / 800 : ℝ) - 1 / 2)} →
        ∀ z ∈ levelSet N (1 / 200) S m, ∀ (i : Fin M) (μ : Fin N) (v w : Fin M ⊕ Fin N → ℝ),
          HighProbAt N (3 - 2) {ω | ∀ s : ℝ, |s| ≤ |y ω| →
            ‖testBilin v (lawMat Sig (Xupd (X ω) i μ s) z) w‖ ≤
              (N : ℝ) ^ (2 * (1 / 200 : ℝ) + 3 * (1 / 800)) * testNorm v * testNorm w} :=
  rough_bound_upd' (1 / 2) 1 (fun _ => 2) 25 (1 / 200) (1 / 800) 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Anisotropic

#print axioms Anisotropic.rough_bound_upd'
