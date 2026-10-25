import Anisotropic.Comparison.Ensemble
import Anisotropic.Comparison.Interpolation
import Anisotropic.Density.Count
import Anisotropic.Density.Critical
import Anisotropic.EdgeUniv.Defs
import Anisotropic.EdgeUniv.Reduction
import Anisotropic.EdgeUniv.SmCount
import Anisotropic.EdgeUniv.Swap
import Anisotropic.EdgeUniv.ThirdSum
import Anisotropic.Entrywise.DiagModel
import Anisotropic.Framework.Domination
import Anisotropic.Framework.Model
import Anisotropic.Probability.NormBound.GaussianLower
import Anisotropic.Qdot.Defs
import Anisotropic.Qdot.EdgeCompare
import Anisotropic.Qdot.EdgeDefs
import Anisotropic.Qdot.LocalLaw

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # The third-order sum for `Q̇` -/

/-! ## Traces of powers of `2 × 2` matrices -/

/-- Cayley–Hamilton for `2 × 2` matrices. -/
private lemma dthird_sq_fin_two (A : Matrix (Fin 2) (Fin 2) ℂ) :
    A * A = A.trace • A - A.det • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

/-- The trace recursion `t_{k+2} = s t_{k+1} - P t_k` for `2 × 2` matrices. -/
private lemma dthird_trace_pow_rec (A : Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ) :
    (A ^ (k + 2)).trace = A.trace * (A ^ (k + 1)).trace - A.det * (A ^ k).trace := by
  have h : A ^ (k + 2) = A ^ k * (A * A) := by rw [pow_add, sq]
  rw [h, dthird_sq_fin_two, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, ← pow_succ, smul_eq_mul, smul_eq_mul]

private lemma dthird_norm_trace_fin_two_le (A : Matrix (Fin 2) (Fin 2) ℂ) {W : ℝ}
    (hA : ∀ r c, ‖A r c‖ ≤ W) : ‖A.trace‖ ≤ 2 * W := by
  rw [Matrix.trace_fin_two]
  calc ‖A 0 0 + A 1 1‖ ≤ ‖A 0 0‖ + ‖A 1 1‖ := norm_add_le _ _
    _ ≤ 2 * W := by linarith [hA 0 0, hA 1 1]

private lemma dthird_norm_det_fin_two_le (A : Matrix (Fin 2) (Fin 2) ℂ) {W : ℝ}
    (hA : ∀ r c, ‖A r c‖ ≤ W) : ‖A.det‖ ≤ 2 * W ^ 2 := by
  rw [Matrix.det_fin_two]
  have h0 : 0 ≤ W := (norm_nonneg _).trans (hA 0 0)
  calc ‖A 0 0 * A 1 1 - A 0 1 * A 1 0‖ ≤ ‖A 0 0‖ * ‖A 1 1‖ + ‖A 0 1‖ * ‖A 1 0‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, norm_mul]
    _ ≤ W * W + W * W := by
        gcongr <;> exact hA _ _
    _ = 2 * W ^ 2 := by ring

/-- `|tr A^k| ≤ 2 (4W)^k` for a `2 × 2` matrix with entries bounded by `W ≥ 1`. -/
private lemma dthird_norm_trace_pow_le (A : Matrix (Fin 2) (Fin 2) ℂ) {W : ℝ} (hW : 1 ≤ W)
    (hA : ∀ r c, ‖A r c‖ ≤ W) (k : ℕ) : ‖(A ^ k).trace‖ ≤ 2 * (4 * W) ^ k := by
  have hs := dthird_norm_trace_fin_two_le A hA
  have hP := dthird_norm_det_fin_two_le A hA
  have key : ∀ k, ‖(A ^ k).trace‖ ≤ 2 * (4 * W) ^ k ∧
      ‖(A ^ (k + 1)).trace‖ ≤ 2 * (4 * W) ^ (k + 1) := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · simp [Matrix.trace_one]
      · simp only [zero_add, pow_one]
        linarith
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      rw [show k + 1 + 1 = k + 2 by ring, dthird_trace_pow_rec]
      have h4 : (0 : ℝ) ≤ (4 * W) ^ k := by positivity
      calc ‖A.trace * (A ^ (k + 1)).trace - A.det * (A ^ k).trace‖
          ≤ ‖A.trace‖ * ‖(A ^ (k + 1)).trace‖ + ‖A.det‖ * ‖(A ^ k).trace‖ := by
            refine (norm_sub_le _ _).trans ?_
            rw [norm_mul, norm_mul]
        _ ≤ (2 * W) * (2 * (4 * W) ^ (k + 1)) + (2 * W ^ 2) * (2 * (4 * W) ^ k) := by
            gcongr
            · exact ih.2
            · exact ih.1
        _ = 20 * W ^ 2 * (4 * W) ^ k := by ring
        _ ≤ 32 * W ^ 2 * (4 * W) ^ k := by nlinarith [mul_nonneg (sq_nonneg W) h4]
        _ = 2 * (4 * W) ^ (k + 2) := by ring
  exact (key k).1

/-- Perturbation of `tr A^k` for `2 × 2` matrices through the trace and the determinant:
`|tr A^k - tr A'^k| ≤ (8W)^k (σ + ρ)` when `|tr A|, |tr A'| ≤ σ`, `|det A - det A'| ≤ ρ`, and
all entries are bounded by `W ≥ 1`. -/
private lemma dthird_trace_pow_sub_le (A A' : Matrix (Fin 2) (Fin 2) ℂ) {W σ ρ : ℝ} (hW : 1 ≤ W)
    (hA : ∀ r c, ‖A r c‖ ≤ W) (hA' : ∀ r c, ‖A' r c‖ ≤ W) (hs : ‖A.trace‖ ≤ σ)
    (hs' : ‖A'.trace‖ ≤ σ) (hρ : ‖A.det - A'.det‖ ≤ ρ) (k : ℕ) :
    ‖(A ^ k).trace - (A' ^ k).trace‖ ≤ (8 * W) ^ k * (σ + ρ) := by
  have hσ0 : 0 ≤ σ := (norm_nonneg _).trans hs
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hρ
  have hP' := dthird_norm_det_fin_two_le A' hA'
  have key : ∀ k, ‖(A ^ k).trace - (A' ^ k).trace‖ ≤ (8 * W) ^ k * (σ + ρ) ∧
      ‖(A ^ (k + 1)).trace - (A' ^ (k + 1)).trace‖ ≤ (8 * W) ^ (k + 1) * (σ + ρ) := by
    intro k
    induction k with
    | zero =>
      refine ⟨by simp; positivity, ?_⟩
      simp only [zero_add, pow_one]
      calc ‖A.trace - A'.trace‖ ≤ ‖A.trace‖ + ‖A'.trace‖ := norm_sub_le _ _
        _ ≤ 8 * W * (σ + ρ) := by nlinarith
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      rw [show k + 1 + 1 = k + 2 by ring, dthird_trace_pow_rec, dthird_trace_pow_rec]
      have t1 := dthird_norm_trace_pow_le A hW hA (k + 1)
      have t1' := dthird_norm_trace_pow_le A' hW hA' (k + 1)
      have t0 := dthird_norm_trace_pow_le A hW hA k
      have e : A.trace * (A ^ (k + 1)).trace - A.det * (A ^ k).trace -
          (A'.trace * (A' ^ (k + 1)).trace - A'.det * (A' ^ k).trace) =
          A.trace * (A ^ (k + 1)).trace - A'.trace * (A' ^ (k + 1)).trace -
            (A.det - A'.det) * (A ^ k).trace - A'.det * ((A ^ k).trace - (A' ^ k).trace) := by
        ring
      rw [e]
      have h4 : (0 : ℝ) ≤ (4 * W) ^ k := by positivity
      have h48 : (4 * W) ^ k ≤ (8 * W) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
      calc _ ≤ ‖A.trace‖ * ‖(A ^ (k + 1)).trace‖ + ‖A'.trace‖ * ‖(A' ^ (k + 1)).trace‖ +
            ‖A.det - A'.det‖ * ‖(A ^ k).trace‖ +
              ‖A'.det‖ * ‖(A ^ k).trace - (A' ^ k).trace‖ := by
            refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
              (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl) |>.trans ?_
            simp only [norm_mul]
            exact le_rfl
        _ ≤ σ * (2 * (4 * W) ^ (k + 1)) + σ * (2 * (4 * W) ^ (k + 1)) +
            ρ * (2 * (4 * W) ^ k) + (2 * W ^ 2) * ((8 * W) ^ k * (σ + ρ)) := by
            gcongr
            exact ih.1
        _ = 16 * W * ((4 * W) ^ k * σ) + 2 * ((4 * W) ^ k * ρ) +
            2 * W ^ 2 * ((8 * W) ^ k * (σ + ρ)) := by ring
        _ ≤ 16 * W ^ 2 * ((8 * W) ^ k * (σ + ρ)) + 2 * W ^ 2 * ((8 * W) ^ k * (σ + ρ)) +
            2 * W ^ 2 * ((8 * W) ^ k * (σ + ρ)) := by
            have h8 : (0 : ℝ) ≤ (8 * W) ^ k := by positivity
            have a1 : (4 * W) ^ k * σ ≤ (8 * W) ^ k * (σ + ρ) := by nlinarith
            have a2 : (4 * W) ^ k * ρ ≤ (8 * W) ^ k * (σ + ρ) := by nlinarith
            have a3 : 0 ≤ (8 * W) ^ k * (σ + ρ) := by positivity
            have hW2 : W ≤ W ^ 2 := by nlinarith
            gcongr ?_ + ?_ + _
            · calc 16 * W * ((4 * W) ^ k * σ) ≤ 16 * W * ((8 * W) ^ k * (σ + ρ)) := by gcongr
                _ ≤ 16 * W ^ 2 * ((8 * W) ^ k * (σ + ρ)) := by gcongr
            · calc 2 * ((4 * W) ^ k * ρ) ≤ 2 * ((8 * W) ^ k * (σ + ρ)) := by gcongr
                _ ≤ 2 * W ^ 2 * ((8 * W) ^ k * (σ + ρ)) := by nlinarith
        _ ≤ (8 * W) ^ (k + 2) * (σ + ρ) := by
            have a3 : 0 ≤ (8 * W) ^ k * (σ + ρ) := by positivity
            have e2 : (8 * W) ^ (k + 2) * (σ + ρ) = 64 * W ^ 2 * ((8 * W) ^ k * (σ + ρ)) := by
              ring
            rw [e2]
            nlinarith [mul_nonneg (sq_nonneg W) a3]
  exact (key k).1

/-! ## The `J × J` block of `tr (Δ¹ G)^k` and the entry derivatives of `𝒳` -/

/-- The `J × J` block `[[G_{μi}, G_{μμ}], [G_{ii}, G_{iμ}]]` governing `tr (Δ¹ G)^k`. -/
private def dthirdBlock (B : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) (i : Fin M) (μ : Fin N) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![B (Sum.inr μ) (Sum.inl i), B (Sum.inr μ) (Sum.inr μ);
    B (Sum.inl i) (Sum.inl i), B (Sum.inl i) (Sum.inr μ)]

/-- `tr (Δ¹ B)^{k+1}` is the trace of the `(k+1)`-st power of the `2 × 2` block. -/
private lemma dthird_trace_Delta_pow (B : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) (i : Fin M)
    (μ : Fin N) (k : ℕ) :
    ((Delta i μ 1 * B) ^ (k + 1)).trace = ((dthirdBlock B i μ) ^ (k + 1)).trace := by
  set P : Matrix (Fin M ⊕ Fin N) (Fin 2) ℂ := Matrix.of fun s r =>
    if r = 0 then (if s = Sum.inl i then 1 else 0) else (if s = Sum.inr μ then 1 else 0) with hP
  set R : Matrix (Fin 2) (Fin M ⊕ Fin N) ℂ := Matrix.of fun r t =>
    if r = 0 then B (Sum.inr μ) t else B (Sum.inl i) t with hR
  have h1 : Delta i μ 1 * B = P * R := by
    ext s t
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two]
    simp only [hP, hR, Matrix.of_apply, Delta]
    rcases s with s | s
    · by_cases hs : s = i
      · subst hs
        rw [Finset.sum_eq_single (Sum.inr μ)]
        · simp
        · intro b _ hb
          simp [hb]
        · simp
      · rw [Finset.sum_eq_zero]
        · simp [hs]
        · intro b _
          simp [hs]
    · by_cases hs : s = μ
      · subst hs
        rw [Finset.sum_eq_single (Sum.inl i)]
        · simp
        · intro b _ hb
          simp [hb]
        · simp
      · rw [Finset.sum_eq_zero]
        · simp [hs]
        · intro b _
          simp [hs]
  have h2 : R * P = dthirdBlock B i μ := by
    ext r c
    rw [Matrix.mul_apply]
    fin_cases r <;> fin_cases c <;> simp [hP, hR, dthirdBlock]
  have h3 : ∀ k : ℕ, (P * R) ^ (k + 1) = P * ((R * P) ^ k * R) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Matrix.mul_assoc]
  rw [h1, h3, Matrix.trace_mul_comm, Matrix.mul_assoc, ← pow_succ, h2]

private lemma dthird_factorial_le {n : ℕ} (hn : n ≤ 4) : (n.factorial : ℝ) ≤ 24 := by
  have : n.factorial ≤ 24 := by interval_cases n <;> decide
  exact_mod_cast this

/-- `|-(1/π) (-1)^n n! (Im a - Im b)| ≤ 24 ‖a - b‖` for `n ≤ 4`. -/
private lemma dthird_coef_le {n : ℕ} (hn : n ≤ 4) (a b : ℂ) :
    |-(1 / Real.pi) * (((-1 : ℝ) ^ n * (n.factorial : ℝ)) * (a.im - b.im))| ≤ 24 * ‖a - b‖ := by
  have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have h1 : |a.im - b.im| ≤ ‖a - b‖ := by
    rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
  rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi), Nat.abs_cast]
  have hf := dthird_factorial_le hn
  have h0 : 0 ≤ ‖a - b‖ := norm_nonneg _
  have hp : 1 / Real.pi ≤ 1 := by rw [div_le_one (by positivity)]; exact hpi
  calc 1 / Real.pi * ((n.factorial : ℝ) * |a.im - b.im|) ≤ 1 * (24 * ‖a - b‖) := by
        gcongr
    _ = 24 * ‖a - b‖ := one_mul _

/-- Entry bounds at the two window points give `|∂^{n+1} 𝒳| ≤ 24 (8L)^5 (4θ + κ)` for
`n + 1 ≤ 5`: the `J × J` entries are at most `L`, the off-diagonal ones at most `θ ≤ 1`, and the
products `G_{ii} G_{μμ}` at the two points differ by at most `κ`. -/
private lemma dthird_deriv_le_small {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {η : ℝ} (hη : 0 < η) (E₁ E₂ : ℝ) (i : Fin M) (μ : Fin N)
    (s : ℝ) {L θ κ : ℝ} (hL : 1 ≤ L) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (h₁ : ∀ a ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
      ∀ b ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
        ‖G Sig (Xupd Xm i μ s) ((E₁ : ℂ) + η * Complex.I) a b‖ ≤ L)
    (h₂ : ∀ a ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
      ∀ b ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
        ‖G Sig (Xupd Xm i μ s) ((E₂ : ℂ) + η * Complex.I) a b‖ ≤ L)
    (o₁ : ‖G Sig (Xupd Xm i μ s) ((E₁ : ℂ) + η * Complex.I) (Sum.inl i) (Sum.inr μ)‖ ≤ θ ∧
      ‖G Sig (Xupd Xm i μ s) ((E₁ : ℂ) + η * Complex.I) (Sum.inr μ) (Sum.inl i)‖ ≤ θ)
    (o₂ : ‖G Sig (Xupd Xm i μ s) ((E₂ : ℂ) + η * Complex.I) (Sum.inl i) (Sum.inr μ)‖ ≤ θ ∧
      ‖G Sig (Xupd Xm i μ s) ((E₂ : ℂ) + η * Complex.I) (Sum.inr μ) (Sum.inl i)‖ ≤ θ)
    (hκ : ‖G Sig (Xupd Xm i μ s) ((E₂ : ℂ) + η * Complex.I) (Sum.inl i) (Sum.inl i) *
          G Sig (Xupd Xm i μ s) ((E₂ : ℂ) + η * Complex.I) (Sum.inr μ) (Sum.inr μ) -
        G Sig (Xupd Xm i μ s) ((E₁ : ℂ) + η * Complex.I) (Sum.inl i) (Sum.inl i) *
          G Sig (Xupd Xm i μ s) ((E₁ : ℂ) + η * Complex.I) (Sum.inr μ) (Sum.inr μ)‖ ≤ κ)
    {n : ℕ} (hn : n ≤ 4) :
    |iteratedDeriv (n + 1) (fun t => smCount (QN Sig (Xupd Xm i μ t)) η E₁ E₂) s| ≤
      24 * (8 * L) ^ 5 * (4 * θ + κ) := by
  have hiJ : (Sum.inl i : Fin M ⊕ Fin N) ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)) :=
    Set.mem_insert _ _
  have hμJ : (Sum.inr μ : Fin M ⊕ Fin N) ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)) :=
    Set.mem_insert_of_mem _ rfl
  set B₁ := G Sig (Xupd Xm i μ s) ((E₁ : ℂ) + η * Complex.I) with hB₁
  set B₂ := G Sig (Xupd Xm i μ s) ((E₂ : ℂ) + η * Complex.I) with hB₂
  have hent : ∀ B : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ,
      (∀ a ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
        ∀ b ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)), ‖B a b‖ ≤ L) →
      ∀ r c, ‖dthirdBlock B i μ r c‖ ≤ L := by
    intro B hB r c
    fin_cases r <;> fin_cases c <;> simp only [dthirdBlock] <;> simp <;>
      first | exact hB _ hμJ _ hiJ | exact hB _ hμJ _ hμJ | exact hB _ hiJ _ hiJ |
        exact hB _ hiJ _ hμJ
  have htr : ∀ B : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ,
      (‖B (Sum.inl i) (Sum.inr μ)‖ ≤ θ ∧ ‖B (Sum.inr μ) (Sum.inl i)‖ ≤ θ) →
      ‖(dthirdBlock B i μ).trace‖ ≤ 2 * θ := by
    intro B hB
    rw [Matrix.trace_fin_two]
    simp only [dthirdBlock, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    calc _ ≤ ‖B (Sum.inr μ) (Sum.inl i)‖ + ‖B (Sum.inl i) (Sum.inr μ)‖ := norm_add_le _ _
      _ ≤ 2 * θ := by linarith [hB.1, hB.2]
  have hdet : ‖(dthirdBlock B₂ i μ).det - (dthirdBlock B₁ i μ).det‖ ≤ 2 * θ + κ := by
    rw [Matrix.det_fin_two, Matrix.det_fin_two]
    simp only [dthirdBlock, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    have e : B₂ (Sum.inr μ) (Sum.inl i) * B₂ (Sum.inl i) (Sum.inr μ) -
        B₂ (Sum.inr μ) (Sum.inr μ) * B₂ (Sum.inl i) (Sum.inl i) -
        (B₁ (Sum.inr μ) (Sum.inl i) * B₁ (Sum.inl i) (Sum.inr μ) -
          B₁ (Sum.inr μ) (Sum.inr μ) * B₁ (Sum.inl i) (Sum.inl i)) =
        B₂ (Sum.inr μ) (Sum.inl i) * B₂ (Sum.inl i) (Sum.inr μ) -
          B₁ (Sum.inr μ) (Sum.inl i) * B₁ (Sum.inl i) (Sum.inr μ) -
          (B₂ (Sum.inl i) (Sum.inl i) * B₂ (Sum.inr μ) (Sum.inr μ) -
            B₁ (Sum.inl i) (Sum.inl i) * B₁ (Sum.inr μ) (Sum.inr μ)) := by ring
    rw [e]
    have hθθ : θ * θ ≤ θ := by nlinarith
    calc _ ≤ ‖B₂ (Sum.inr μ) (Sum.inl i)‖ * ‖B₂ (Sum.inl i) (Sum.inr μ)‖ +
          ‖B₁ (Sum.inr μ) (Sum.inl i)‖ * ‖B₁ (Sum.inl i) (Sum.inr μ)‖ + κ := by
          refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans ?_) hκ)
          rw [norm_mul, norm_mul]
      _ ≤ θ * θ + θ * θ + κ := by
          gcongr
          · exact o₂.2
          · exact o₂.1
          · exact o₁.2
          · exact o₁.1
      _ ≤ 2 * θ + κ := by linarith
  rw [derivative_iteratedDeriv_smCount hSig Xm hη E₁ E₂ i μ n s]
  refine (dthird_coef_le hn _ _).trans ?_
  rw [dthird_trace_Delta_pow, dthird_trace_Delta_pow]
  have hd := dthird_trace_pow_sub_le (dthirdBlock B₂ i μ) (dthirdBlock B₁ i μ) hL (hent B₂ h₂)
    (hent B₁ h₁) (htr B₂ o₂) (htr B₁ o₁) hdet (n + 1)
  have hp : (8 * L) ^ (n + 1) ≤ (8 * L) ^ 5 :=
    pow_le_pow_right₀ (by linarith) (by omega)
  have hk0 : 0 ≤ 2 * θ + (2 * θ + κ) := by
    linarith [norm_nonneg ((dthirdBlock B₂ i μ).det - (dthirdBlock B₁ i μ).det)]
  calc 24 * ‖((dthirdBlock B₂ i μ) ^ (n + 1)).trace - ((dthirdBlock B₁ i μ) ^ (n + 1)).trace‖
      ≤ 24 * ((8 * L) ^ (n + 1) * (2 * θ + (2 * θ + κ))) := by gcongr
    _ ≤ 24 * ((8 * L) ^ 5 * (2 * θ + (2 * θ + κ))) := by gcongr
    _ = 24 * (8 * L) ^ 5 * (4 * θ + κ) := by ring

/-- Entry bounds `|G_{ab}| ≤ W` (`W ≥ 1`) on `J × J` at both window points give
`|∂^{n+1} 𝒳| ≤ (384 W)^{n+1}` for `n + 1 ≤ 5`. -/
private lemma dthird_deriv_le_crude {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {η : ℝ} (hη : 0 < η) (E₁ E₂ : ℝ) (i : Fin M) (μ : Fin N)
    (s : ℝ) {W : ℝ} (hW : 1 ≤ W)
    (h₁ : ∀ a b, ‖G Sig (Xupd Xm i μ s) ((E₁ : ℂ) + η * Complex.I) a b‖ ≤ W)
    (h₂ : ∀ a b, ‖G Sig (Xupd Xm i μ s) ((E₂ : ℂ) + η * Complex.I) a b‖ ≤ W)
    {n : ℕ} (hn : n ≤ 4) :
    |iteratedDeriv (n + 1) (fun t => smCount (QN Sig (Xupd Xm i μ t)) η E₁ E₂) s| ≤
      (384 * W) ^ (n + 1) := by
  have hent : ∀ B : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ, (∀ a b, ‖B a b‖ ≤ W) →
      ∀ r c, ‖dthirdBlock B i μ r c‖ ≤ W := by
    intro B hB r c
    fin_cases r <;> fin_cases c <;> simp only [dthirdBlock] <;> simp <;> exact hB _ _
  rw [derivative_iteratedDeriv_smCount hSig Xm hη E₁ E₂ i μ n s]
  refine (dthird_coef_le hn _ _).trans ?_
  rw [dthird_trace_Delta_pow, dthird_trace_Delta_pow]
  have t2 := dthird_norm_trace_pow_le _ hW (hent _ h₂) (n + 1)
  have t1 := dthird_norm_trace_pow_le _ hW (hent _ h₁) (n + 1)
  have h4 : (0 : ℝ) ≤ (4 * W) ^ (n + 1) := by positivity
  calc 24 * ‖_ - _‖ ≤ 24 * (2 * (4 * W) ^ (n + 1) + 2 * (4 * W) ^ (n + 1)) := by
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add t2 t1)
    _ = 96 * (4 * W) ^ (n + 1) := by ring
    _ ≤ 96 ^ (n + 1) * (4 * W) ^ (n + 1) := by
        gcongr
        exact le_self_pow₀ (by norm_num) (by omega)
    _ = (384 * W) ^ (n + 1) := by rw [← mul_pow]; ring

private lemma dthird_Xupd_self (Xm : Matrix (Fin M) (Fin N) ℝ) (i : Fin M) (μ : Fin N) :
    Xupd Xm i μ (Xm i μ) = Xm := by
  funext j ν
  by_cases h : j = i ∧ ν = μ
  · obtain ⟨rfl, rfl⟩ := h; simp [Xupd]
  · simp [Xupd, h]

/-! ## Derivatives of `F ∘ 𝒳` -/

/-- Iterated derivatives of a vector-valued function are taken componentwise. -/
private lemma dthird_iteratedDeriv_pi {l : ℕ} (φ : ℝ → Fin l → ℝ)
    (hφ : ∀ (j : Fin l) (n : ℕ), ContDiff ℝ n fun t => φ t j) (n : ℕ) :
    iteratedDeriv n φ = fun t j => iteratedDeriv n (fun s => φ s j) t := by
  induction n with
  | zero => funext t j; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    rw [deriv_pi fun j => ((hφ j (n + 1)).differentiable_iteratedDeriv n
      (by exact_mod_cast Nat.lt_succ_self n)).differentiableAt]
    funext j
    rw [iteratedDeriv_succ]

/-- Faà di Bruno bound: if `‖D^m F‖ ≤ C_b` for `m ≤ k` and the `i`-th derivatives of the
components of `φ` at `t` are at most `D^i` for `1 ≤ i ≤ n ≤ k`, then
`|(F ∘ φ)^{(n)}(t)| ≤ n! C_b D^n`. -/
private lemma dthird_comp_le {l : ℕ} {F : (Fin l → ℝ) → ℝ} {Cb : ℝ} {k : ℕ}
    (hF : ContDiff ℝ k F)
    (hFb : ∀ m ≤ k, ∀ x, ‖iteratedFDeriv ℝ m F x‖ ≤ Cb) (φ : ℝ → Fin l → ℝ)
    (hφ : ∀ (j : Fin l) (n : ℕ), ContDiff ℝ n fun t => φ t j) {n : ℕ} (hn : n ≤ k) (t : ℝ)
    {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ i, 1 ≤ i → i ≤ n → ∀ j, |iteratedDeriv i (fun s => φ s j) t| ≤ D ^ i) :
    |iteratedDeriv n (F ∘ φ) t| ≤ n.factorial * Cb * D ^ n := by
  have hφc : ContDiff ℝ k φ := contDiff_pi.2 fun j => hφ j k
  rw [← Real.norm_eq_abs, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  refine norm_iteratedFDeriv_comp_le hF hφc (by exact_mod_cast hn) t
    (fun i hi => hFb i (hi.trans hn) _) fun i h1 h2 => ?_
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, dthird_iteratedDeriv_pi φ hφ]
  exact (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => by
    rw [Real.norm_eq_abs]; exact hD i h1 h2 j

/-- The same bound with one small factor: if the component derivatives of orders `1, …, n` at
`t` are at most `Θ ∈ [0, 1]`, then `|(F ∘ φ)^{(n)}(t)| ≤ n! C_b Θ`. -/
private lemma dthird_comp_le_small {l : ℕ} {F : (Fin l → ℝ) → ℝ} {Cb : ℝ} {k : ℕ}
    (hF : ContDiff ℝ k F)
    (hFb : ∀ m ≤ k, ∀ x, ‖iteratedFDeriv ℝ m F x‖ ≤ Cb) (φ : ℝ → Fin l → ℝ)
    (hφ : ∀ (j : Fin l) (n : ℕ), ContDiff ℝ n fun t => φ t j) {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ k)
    (t : ℝ) {Θ : ℝ} (hΘ0 : 0 ≤ Θ) (hΘ1 : Θ ≤ 1)
    (hD : ∀ i, 1 ≤ i → i ≤ n → ∀ j, |iteratedDeriv i (fun s => φ s j) t| ≤ Θ) :
    |iteratedDeriv n (F ∘ φ) t| ≤ n.factorial * Cb * Θ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  set D : ℝ := Θ ^ ((n : ℝ)⁻¹) with hDdef
  have hD0 : 0 ≤ D := Real.rpow_nonneg hΘ0 _
  have hDn : D ^ n = Θ := by
    rw [hDdef, ← Real.rpow_natCast, ← Real.rpow_mul hΘ0, inv_mul_cancel₀ hn0.ne', Real.rpow_one]
  have h := dthird_comp_le hF hFb φ hφ hn t hD0 fun i h1 h2 j => by
    refine (hD i h1 h2 j).trans ?_
    rw [hDdef, ← Real.rpow_natCast, ← Real.rpow_mul hΘ0]
    conv_lhs => rw [← Real.rpow_one Θ]
    refine Real.rpow_le_rpow_of_exponent_ge' hΘ0 hΘ1 (by positivity) ?_
    rw [inv_mul_le_iff₀ hn0, mul_one]
    exact_mod_cast h2
  rwa [hDn] at h

/-! ## Continuity and measurability in `X` -/

/-- `(X, y) ↦ G(X, y + iη)` is jointly continuous. -/
private lemma dthird_continuous_G {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {η : ℝ}
    (hη : 0 < η) :
    Continuous fun p : Matrix (Fin M) (Fin N) ℝ × ℝ =>
      G Sig p.1 ((p.2 : ℂ) + η * Complex.I) := by
  have hX : Continuous fun p : Matrix (Fin M) (Fin N) ℝ × ℝ => cplx p.1 :=
    (continuous_id.matrix_map Complex.continuous_ofReal).comp continuous_fst
  have hXt : Continuous fun p : Matrix (Fin M) (Fin N) ℝ × ℝ => cplx p.1ᵀ :=
    ((continuous_id.matrix_transpose).matrix_map Complex.continuous_ofReal).comp continuous_fst
  have hH : Continuous fun p : Matrix (Fin M) (Fin N) ℝ × ℝ =>
      H Sig p.1 ((p.2 : ℂ) + η * Complex.I) := by
    have h3 : Continuous fun p : Matrix (Fin M) (Fin N) ℝ × ℝ =>
        -(((p.2 : ℂ) + η * Complex.I) • (1 : Matrix (Fin N) (Fin N) ℂ)) :=
      (((Complex.continuous_ofReal.comp continuous_snd).add continuous_const).smul
        continuous_const).neg
    exact continuous_const.matrix_fromBlocks hX hXt h3
  rw [continuous_iff_continuousAt]
  intro p
  have hu := (Matrix.isUnit_iff_isUnit_det _).1
    (H_isUnit hSig p.1 (z := (p.2 : ℂ) + η * Complex.I) (by simpa using hη))
  have hinv := continuousAt_matrix_inv _ (NormedRing.inverse_continuousAt hu.unit)
  change ContinuousAt (fun p : Matrix (Fin M) (Fin N) ℝ × ℝ =>
    (H Sig p.1 ((p.2 : ℂ) + η * Complex.I))⁻¹) p
  exact hinv.comp (f := fun p : Matrix (Fin M) (Fin N) ℝ × ℝ =>
    H Sig p.1 ((p.2 : ℂ) + η * Complex.I)) hH.continuousAt

/-- `X ↦ 𝒳_{[E₁,E₂]}(Q_N(X))` is continuous. -/
private lemma dthird_continuous_smCount {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    {η : ℝ} (hη : 0 < η) (E₁ E₂ : ℝ) :
    Continuous fun Xm : Matrix (Fin M) (Fin N) ℝ => smCount (QN Sig Xm) η E₁ E₂ := by
  have he : (fun Xm : Matrix (Fin M) (Fin N) ℝ => smCount (QN Sig Xm) η E₁ E₂) =
      fun Xm => N / Real.pi * ∫ y in E₁..E₂, (mN Sig Xm (y + η * Complex.I)).im := by
    funext Xm
    exact smCount_eq_integral hSig Xm hη E₁ E₂
  rw [he]
  refine continuous_const.mul ?_
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (Xm : Matrix (Fin M) (Fin N) ℝ) (y : ℝ) => (mN Sig Xm (y + η * Complex.I)).im) ?_
    E₁ E₂
  have hG := dthird_continuous_G (N := N) hSig hη
  have : Function.uncurry (fun (Xm : Matrix (Fin M) (Fin N) ℝ) (y : ℝ) =>
      (mN Sig Xm (y + η * Complex.I)).im) = fun p : Matrix (Fin M) (Fin N) ℝ × ℝ =>
        ((N : ℂ)⁻¹ * ∑ ν, G Sig p.1 ((p.2 : ℂ) + η * Complex.I) (Sum.inr ν) (Sum.inr ν)).im := by
    funext p
    rfl
  rw [this]
  refine Complex.continuous_im.comp (continuous_const.mul (continuous_finsetSum _ fun ν _ => ?_))
  exact (continuous_apply_apply _ _).comp hG

/-- `(X, t) ↦ X^{t}_{(iμ)}` is continuous. -/
private lemma dthird_continuous_Xupd (i : Fin M) (μ : Fin N) :
    Continuous fun p : Matrix (Fin M) (Fin N) ℝ × ℝ => Xupd p.1 i μ p.2 := by
  refine continuous_matrix fun a b => ?_
  by_cases h : a = i ∧ b = μ
  · simpa [Xupd, h] using continuous_snd
  · have hc : Continuous fun p : Matrix (Fin M) (Fin N) ℝ × ℝ => p.1 a b :=
      (continuous_id.matrix_elem a b).comp continuous_fst
    simpa [Xupd, h] using hc

/-- Measurability of the iterated derivatives in a parameter, from the joint measurability of
the function and its smoothness in the variable. -/
private lemma dthird_measurable_iteratedDeriv {α : Type*} [MeasurableSpace α] (φ : α → ℝ → ℝ)
    (hφ : Measurable fun p : α × ℝ => φ p.1 p.2) (m : ℕ) (hd : ∀ a, ContDiff ℝ m (φ a)) :
    ∀ n ≤ m, Measurable fun p : α × ℝ => iteratedDeriv n (φ p.1) p.2 := by
  intro n
  induction n with
  | zero => intro _; simpa using hφ
  | succ n ih =>
    intro hn
    have ihn := ih (Nat.le_of_succ_le hn)
    have hdiff : ∀ a, Differentiable ℝ (iteratedDeriv n (φ a)) := fun a =>
      (hd a).differentiable_iteratedDeriv n (by exact_mod_cast hn)
    have hshift : ∀ c : ℝ, Measurable fun p : α × ℝ => iteratedDeriv n (φ p.1) (p.2 + c) :=
      fun c => ihn.comp (measurable_fst.prodMk (measurable_snd.add_const c))
    refine measurable_of_tendsto_metrizable (f := fun (k : ℕ) (p : α × ℝ) =>
      ((k : ℝ) + 1) * (iteratedDeriv n (φ p.1) (p.2 + 1 / ((k : ℝ) + 1)) -
        iteratedDeriv n (φ p.1) p.2)) (fun k => measurable_const.mul ((hshift _).sub ihn)) ?_
    rw [tendsto_pi_nhds]
    intro p
    have hder := ((hdiff p.1) p.2).hasDerivAt
    rw [hasDerivAt_iff_tendsto_slope] at hder
    have hu : Tendsto (fun k : ℕ => p.2 + 1 / ((k : ℝ) + 1)) atTop (𝓝[≠] p.2) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        simpa using (tendsto_const_nhds (x := p.2)).add h0
      · exact Eventually.of_forall fun k => by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff, add_eq_left]
          positivity
    have h := hder.comp hu
    rw [iteratedDeriv_succ]
    refine h.congr fun k => ?_
    simp only [Function.comp_apply, slope, vsub_eq_sub, smul_eq_mul, add_sub_cancel_left,
      one_div, inv_inv]

/-- A random matrix with measurable entries is measurable. -/
private lemma dthird_measurable_X {Ω : Type*} [MeasureSpace Ω] {C : ℕ → ℝ}
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) : Measurable X :=
  Measurable.of_eval_matrix X fun j ν => hX.measurable j ν

/-! ## Constants of the model and the exponent bookkeeping -/

/-- `‖Σ‖ ≤ τ⁻¹` under (bound_Sigma) (L2 operator norm). -/
private lemma dthird_norm_sig_le {τ : ℝ} (hτ : 0 < τ) {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hS : SigmaAssumption τ Sig) : ‖Sig‖ ≤ τ⁻¹ := by
  have hH := hS.posDef.isHermitian
  set U := hH.eigenvectorUnitary with hU
  have hUm : (U : Matrix (Fin M) (Fin M) ℝ) ∈ unitaryGroup (Fin M) ℝ := U.2
  have hUn : ‖(U : Matrix (Fin M) (Fin M) ℝ)‖ ≤ 1 := by
    have h1 : ‖(U : Matrix (Fin M) (Fin M) ℝ)ᴴ * (U : Matrix (Fin M) (Fin M) ℝ)‖ =
        ‖(U : Matrix (Fin M) (Fin M) ℝ)‖ * ‖(U : Matrix (Fin M) (Fin M) ℝ)‖ :=
      l2_opNorm_conjTranspose_mul_self _
    have h2 : (U : Matrix (Fin M) (Fin M) ℝ)ᴴ * (U : Matrix (Fin M) (Fin M) ℝ) = 1 := by
      rw [← star_eq_conjTranspose]; exact (mem_unitaryGroup_iff'.1 hUm)
    have h3 : ‖(1 : Matrix (Fin M) (Fin M) ℝ)‖ ≤ 1 := by
      rw [← diagonal_one, l2_opNorm_diagonal]
      exact pi_norm_le_iff_of_nonneg zero_le_one |>.2 fun _ => by simp
    rw [h2] at h1
    nlinarith [norm_nonneg (U : Matrix (Fin M) (Fin M) ℝ)]
  have hspec := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  rw [hspec]
  have hD : ‖(diagonal (RCLike.ofReal ∘ hH.eigenvalues) : Matrix (Fin M) (Fin M) ℝ)‖ ≤ τ⁻¹ := by
    rw [l2_opNorm_diagonal]
    refine pi_norm_le_iff_of_nonneg (inv_pos.2 hτ).le |>.2 fun i => ?_
    simp only [Function.comp_apply, RCLike.ofReal_real_eq_id, id, Real.norm_eq_abs]
    rw [abs_of_pos (hS.posDef.eigenvalues_pos i)]
    exact hS.eigenvalues_le i
  have hUs : ‖star (U : Matrix (Fin M) (Fin M) ℝ)‖ ≤ 1 := by
    rw [star_eq_conjTranspose, l2_opNorm_conjTranspose]; exact hUn
  calc _ ≤ ‖(U : Matrix (Fin M) (Fin M) ℝ) * diagonal (RCLike.ofReal ∘ hH.eigenvalues)‖ *
        ‖star (U : Matrix (Fin M) (Fin M) ℝ)‖ := l2_opNorm_mul _ _
    _ ≤ (‖(U : Matrix (Fin M) (Fin M) ℝ)‖ * ‖(diagonal (RCLike.ofReal ∘ hH.eigenvalues) :
          Matrix (Fin M) (Fin M) ℝ)‖) * ‖star (U : Matrix (Fin M) (Fin M) ℝ)‖ :=
        mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _)
    _ ≤ (1 * τ⁻¹) * 1 := by gcongr
    _ = τ⁻¹ := by ring

/-- `0 ≤ a_k ≤ 2τ⁻¹(1 + τ⁻¹)` at a regular edge of a model. -/
private lemma dthird_edgeVal_le {Ω : Type*} [MeasureSpace Ω] {τ : ℝ} {C : ℕ → ℝ}
    {Sig : Matrix (Fin M) (Fin M) ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ} {k : ℕ} (hτ : 0 < τ)
    (hm : IsModel τ C M N Sig X) (hk : RegularEdge τ N (specOf Sig) k) :
    |edgeVal N (specOf Sig) k| ≤ 2 * τ⁻¹ * (1 + τ⁻¹) := by
  have hda : DensityAssumptions τ N (specOf Sig) := hm.diagModel_specOf.densityAssumptions hτ
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · exfalso
      have := hm.ratio_ge
      simp [h0] at this
      linarith
    · exact h0
  have hM : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h0 | h0
    · exfalso
      have := hm.ratio_ge
      simp [h0] at this
      linarith
    · exact h0
  have hS : (posVals (specOf Sig)).Nonempty := by
    refine ⟨specOf Sig ⟨0, hM⟩, ?_⟩
    simp only [posVals, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨⟨_, rfl⟩, ?_⟩
    rw [specOf_eq hm.sigma.posDef.isHermitian]
    exact hm.sigma.posDef.eigenvalues_pos _
  have h := edgeVal_mem_Icc N (specOf Sig) hda.nonneg hN hS hτ hda.phi_lower hda.phi_upper
    hda.bound_Sigma hk.1 hk.2.1
  rw [abs_of_nonneg h.1]
  exact h.2

/-- `c N^y ≤ 1/2` eventually, for `y < 0`. -/
private lemma dthird_ev_small {y : ℝ} (hy : y < 0) (c : ℝ) :
    ∀ᶠ N : ℕ in atTop, c * (N : ℝ) ^ y ≤ 1 / 2 := by
  have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ y) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (y := -y) (by linarith)).comp tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using this
  have h2 : Tendsto (fun N : ℕ => c * (N : ℝ) ^ y) atTop (𝓝 0) := by
    simpa using h1.const_mul c
  exact (h2.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono fun _ h => h.le

/-- `N^x ≤ N^y` for `x ≤ y`, `N ≥ 1`. -/
private lemma dthird_rpow_le {N : ℕ} (hN : 1 ≤ N) {x y : ℝ} (h : x ≤ y) :
    (N : ℝ) ^ x ≤ (N : ℝ) ^ y :=
  Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) h

/-- The deterministic bound `|∂ⁿ f| ≤ n! C_b (384 W)^n`, `n ≤ 5`, for `f(t) = F(𝒳(X^{t}_{(iμ)}))`,
from `|G_{ab}| ≤ W` at all window points, uniformly in `X`. -/
private lemma dthird_crude {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {η : ℝ}
    (hη : 0 < η) {l : ℕ} {F : (Fin l → ℝ) → ℝ} {Cb : ℝ} (hF : ContDiff ℝ 5 F)
    (hFb : ∀ m ≤ 5, ∀ x, ‖iteratedFDeriv ℝ m F x‖ ≤ Cb) (Ea Eb : Fin l → ℝ) (i : Fin M)
    (μ : Fin N) {W : ℝ} (hW1 : 1 ≤ W)
    (hGW : ∀ (Xm : Matrix (Fin M) (Fin N) ℝ) (j : Fin l) (a b : Fin M ⊕ Fin N),
      ‖G Sig Xm ((Ea j : ℂ) + η * Complex.I) a b‖ ≤ W ∧
        ‖G Sig Xm ((Eb j : ℂ) + η * Complex.I) a b‖ ≤ W)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (s : ℝ) {n : ℕ} (hn : n ≤ 5) :
    |iteratedDeriv n (fun t => smF F Sig (Xupd Xm i μ t) η Ea Eb) s| ≤
      n.factorial * Cb * (384 * W) ^ n := by
  have hgvc : ∀ (j : Fin l) (n : ℕ), ContDiff ℝ n fun t =>
      smCount (QN Sig (Xupd Xm i μ t)) η (Ea j) (Eb j) := fun j n =>
    derivative_contDiff_smCount hSig Xm hη (Ea j) (Eb j) i μ n
  refine dthird_comp_le hF hFb (fun t j => smCount (QN Sig (Xupd Xm i μ t)) η (Ea j) (Eb j))
    hgvc hn s (by positivity) fun i' h1 h2 j => ?_
  obtain ⟨n', rfl⟩ : ∃ n', i' = n' + 1 := ⟨i' - 1, by omega⟩
  exact dthird_deriv_le_crude hSig Xm hη (Ea j) (Eb j) i μ s hW1
    (fun a b => (hGW _ j a b).1) (fun a b => (hGW _ j a b).2) (by omega)

/-! ## The third derivative of `F ∘ φ` -/

/-- `(∑_j A_j U_j)'' = ∑_j (A_j'' U_j + 2 A_j' U_j' + A_j U_j'')` for `C²` families. -/
private lemma dthird_deriv2_sum_mul {l : ℕ} (A U : Fin l → ℝ → ℝ)
    (hA : ∀ j, ContDiff ℝ 2 (A j)) (hU : ∀ j, ContDiff ℝ 2 (U j)) (t : ℝ) :
    deriv (deriv fun s => ∑ j, A j s * U j s) t =
      ∑ j, (deriv (deriv (A j)) t * U j t + 2 * deriv (A j) t * deriv (U j) t +
        A j t * deriv (deriv (U j)) t) := by
  have hA1 : ∀ j, Differentiable ℝ (A j) := fun j => (hA j).differentiable (by norm_num)
  have hU1 : ∀ j, Differentiable ℝ (U j) := fun j => (hU j).differentiable (by norm_num)
  have hA2 : ∀ j, Differentiable ℝ (deriv (A j)) := fun j => by
    have := (hA j).differentiable_iteratedDeriv 1 (by norm_num)
    rwa [iteratedDeriv_one] at this
  have hU2 : ∀ j, Differentiable ℝ (deriv (U j)) := fun j => by
    have := (hU j).differentiable_iteratedDeriv 1 (by norm_num)
    rwa [iteratedDeriv_one] at this
  have hd : deriv (fun s => ∑ j, A j s * U j s) =
      fun s => ∑ j, (deriv (A j) s * U j s + A j s * deriv (U j) s) := by
    funext s
    exact (HasDerivAt.fun_sum fun j _ => (hA1 j s).hasDerivAt.mul (hU1 j s).hasDerivAt).deriv
  have hd2 : HasDerivAt (fun s => ∑ j, (deriv (A j) s * U j s + A j s * deriv (U j) s))
      (∑ j, ((deriv (deriv (A j)) t * U j t + deriv (A j) t * deriv (U j) t) +
        (deriv (A j) t * deriv (U j) t + A j t * deriv (deriv (U j)) t))) t :=
    HasDerivAt.fun_sum fun j _ => ((hA2 j t).hasDerivAt.mul (hU1 j t).hasDerivAt).add
      ((hA1 j t).hasDerivAt.mul (hU2 j t).hasDerivAt)
  rw [hd, hd2.deriv]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The chain rule for `F ∘ φ` with `φ : ℝ → ℝ^l`:
`(F ∘ φ)' = ∑_j ∂_j F(φ) φ_j'`. -/
private lemma dthird_deriv_comp {l : ℕ} {F : (Fin l → ℝ) → ℝ} (hF : ContDiff ℝ 5 F)
    (φ : ℝ → Fin l → ℝ) (hφ : ∀ (j : Fin l) (n : ℕ), ContDiff ℝ n fun t => φ t j) :
    deriv (F ∘ φ) = fun t =>
      ∑ j, fderiv ℝ F (φ t) (Pi.single j 1) * deriv (fun s => φ s j) t := by
  funext t
  have hFd : HasFDerivAt F (fderiv ℝ F (φ t)) (φ t) :=
    ((hF.differentiable (by norm_num)) (φ t)).hasFDerivAt
  have hφd : DifferentiableAt ℝ φ t :=
    (contDiff_pi.2 fun j => hφ j 1).differentiable (by norm_num) t
  rw [(hFd.comp_hasDerivAt t hφd.hasDerivAt).deriv,
    deriv_pi fun j => ((hφ j 1).differentiable (by norm_num)) t]
  have hv : (fun j => deriv (fun s => φ s j) t) =
      ∑ j, deriv (fun s => φ s j) t • (Pi.single j 1 : Fin l → ℝ) := by
    conv_lhs => rw [← Finset.univ_sum_single (fun j => deriv (fun s => φ s j) t)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Pi.single_smul', smul_eq_mul, mul_one]
  rw [hv, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

/-- The third derivative of `F ∘ φ`:
`(F ∘ φ)''' = ∑_j ((∂_j F ∘ φ)'' φ_j' + 2 (∂_j F ∘ φ)' φ_j'' + ∂_j F(φ) φ_j''')`. -/
private lemma dthird_iteratedDeriv_three_comp {l : ℕ} {F : (Fin l → ℝ) → ℝ}
    (hF : ContDiff ℝ 5 F) (φ : ℝ → Fin l → ℝ)
    (hφ : ∀ (j : Fin l) (n : ℕ), ContDiff ℝ n fun t => φ t j) (t : ℝ) :
    iteratedDeriv 3 (F ∘ φ) t = ∑ j,
      (iteratedDeriv 2 (fun s => fderiv ℝ F (φ s) (Pi.single j 1)) t *
          iteratedDeriv 1 (fun s => φ s j) t +
        2 * iteratedDeriv 1 (fun s => fderiv ℝ F (φ s) (Pi.single j 1)) t *
          iteratedDeriv 2 (fun s => φ s j) t +
        fderiv ℝ F (φ t) (Pi.single j 1) * iteratedDeriv 3 (fun s => φ s j) t) := by
  have h2 : ∀ g : ℝ → ℝ, iteratedDeriv 2 g = deriv (deriv g) := fun g => by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have h3 : ∀ g : ℝ → ℝ, iteratedDeriv 3 g = deriv (deriv (deriv g)) := fun g => by
    rw [iteratedDeriv_succ, h2]
  have hg : ∀ j : Fin l, ContDiff ℝ 4 fun s => fderiv ℝ F (φ s) (Pi.single j 1) := fun j =>
    ((hF.fderiv_right (m := 4) (by norm_num)).clm_apply contDiff_const).comp
      (contDiff_pi.2 fun j => hφ j 4)
  have hu : ∀ j : Fin l, ContDiff ℝ 2 (deriv fun s => φ s j) := fun j => by
    have := (hφ j 3).iterate_deriv' 2 1
    simpa using this
  rw [iteratedDeriv_succ', dthird_deriv_comp hF φ hφ, h2,
    dthird_deriv2_sum_mul _ _ (fun j => (hg j).of_le (by norm_num)) hu]
  simp only [h2, h3, iteratedDeriv_one]

/-- The partial derivatives `∂_j F = DF(·) e_j` satisfy `‖D^m ∂_j F‖ ≤ C_b` for `m ≤ 4`. -/
private lemma dthird_partial_bound {l : ℕ} {F : (Fin l → ℝ) → ℝ} {Cb : ℝ}
    (hF : ContDiff ℝ 5 F) (hFb : ∀ m ≤ 5, ∀ x, ‖iteratedFDeriv ℝ m F x‖ ≤ Cb) (j : Fin l) :
    ∀ m ≤ 4, ∀ x, ‖iteratedFDeriv ℝ m (fun x => fderiv ℝ F x (Pi.single j 1)) x‖ ≤ Cb := by
  intro m hm x
  set L : ((Fin l → ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.apply ℝ ℝ (Pi.single j (1 : ℝ)) with hLdef
  have hL : ‖L‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun A => ?_
    rw [hLdef, ContinuousLinearMap.apply_apply, one_mul]
    calc ‖A (Pi.single j 1)‖ ≤ ‖A‖ * ‖(Pi.single j 1 : Fin l → ℝ)‖ := A.le_opNorm _
      _ = ‖A‖ := by rw [Pi.norm_single, norm_one, mul_one]
  have e : (fun x => fderiv ℝ F x (Pi.single j 1)) = L ∘ fderiv ℝ F := rfl
  rw [e]
  have hFd : ContDiff ℝ 4 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  refine (L.norm_iteratedFDeriv_comp_left hFd.contDiffAt (by exact_mod_cast hm)).trans ?_
  rw [norm_iteratedFDeriv_fderiv]
  calc ‖L‖ * ‖iteratedFDeriv ℝ (m + 1) F x‖ ≤ 1 * Cb :=
        mul_le_mul hL (hFb _ (by omega) x) (norm_nonneg _) zero_le_one
    _ = Cb := one_mul _

/-- `tr B̂³ = 2 G_{μi}³ + 6 G_{μi} G_{ii} G_{μμ}` for the `J × J` block `B̂` of a matrix with
`G_{iμ} = G_{μi}`. -/
private lemma dthird_trace_cube (B : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) (i : Fin M)
    (μ : Fin N) (hB : B (Sum.inl i) (Sum.inr μ) = B (Sum.inr μ) (Sum.inl i)) :
    ((dthirdBlock B i μ) ^ 3).trace = 2 * B (Sum.inr μ) (Sum.inl i) ^ 3 +
      6 * B (Sum.inr μ) (Sum.inl i) * (B (Sum.inl i) (Sum.inl i) * B (Sum.inr μ) (Sum.inr μ)) := by
  simp only [dthirdBlock, pow_succ, pow_zero, one_mul, Matrix.trace_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two]
  simp [hB]
  ring

/-! ## The bound for one entry at `X` -/

/-- `|Im(2g³ + 6g(d - w))| ≤ (2 + 6c) θ²` when `|g| ≤ θ ≤ 1` and `|d - w| ≤ c θ`. -/
private lemma dthird_cube_rest {g d w : ℂ} {θ c : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hg : ‖g‖ ≤ θ) (hd : ‖d - w‖ ≤ c * θ) :
    ‖2 * g ^ 3 + 6 * g * (d - w)‖ ≤ (2 + 6 * c) * θ ^ 2 := by
  have h3 : ‖g‖ ^ 3 ≤ θ ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hg 3
  have hθ3 : θ ^ 3 ≤ θ ^ 2 := by nlinarith [sq_nonneg θ]
  calc ‖2 * g ^ 3 + 6 * g * (d - w)‖ ≤ 2 * ‖g‖ ^ 3 + 6 * ‖g‖ * ‖d - w‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, norm_mul, norm_pow]
        norm_num
    _ ≤ 2 * θ ^ 3 + 6 * θ * (c * θ) := by
        gcongr
    _ ≤ (2 + 6 * c) * θ ^ 2 := by nlinarith

/-- The bound for one entry at `X` itself: if at both window points `z_{a,j}`, `z_{b,j}` the
`J × J` entries of `G` are at most `K + 1`, the off-diagonal ones at most `θ ≤ 1`,
`|G_{ii} G_{μμ} - w| ≤ (2K + 1) θ` with `|w_{b,j} - w_{a,j}| ≤ κ₀`, and `Θ ≤ 1` dominates the
resulting entry derivatives of `𝒳`, then `∂³_{iμ} F(𝒳)` is the leading term
`∑_j ∂_j F(𝒳) · (-π⁻¹) 2 Im[6 G_{μi} w]_{z_a}^{z_b}` up to `l C_b (4Θ² + (8 + 24(2K+1)) θ²)`. -/
private lemma dthird_entry {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {η : ℝ} (hη : 0 < η) {l : ℕ} {F : (Fin l → ℝ) → ℝ}
    {Cb : ℝ} (hF : ContDiff ℝ 5 F) (hFb : ∀ m ≤ 5, ∀ x, ‖iteratedFDeriv ℝ m F x‖ ≤ Cb)
    (Ea Eb : Fin l → ℝ) (i : Fin M) (μ : Fin N) (wa wb : Fin l → ℂ) {K θ κ₀ Θ : ℝ}
    (hK : 0 ≤ K) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hκ₀ : 0 ≤ κ₀)
    (hJ : ∀ j, ∀ a ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
      ∀ b ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
        ‖G Sig Xm ((Ea j : ℂ) + η * Complex.I) a b‖ ≤ K + 1 ∧
          ‖G Sig Xm ((Eb j : ℂ) + η * Complex.I) a b‖ ≤ K + 1)
    (hoff : ∀ j,
      (‖G Sig Xm ((Ea j : ℂ) + η * Complex.I) (Sum.inl i) (Sum.inr μ)‖ ≤ θ ∧
        ‖G Sig Xm ((Ea j : ℂ) + η * Complex.I) (Sum.inr μ) (Sum.inl i)‖ ≤ θ) ∧
      (‖G Sig Xm ((Eb j : ℂ) + η * Complex.I) (Sum.inl i) (Sum.inr μ)‖ ≤ θ ∧
        ‖G Sig Xm ((Eb j : ℂ) + η * Complex.I) (Sum.inr μ) (Sum.inl i)‖ ≤ θ))
    (hd : ∀ j,
      ‖G Sig Xm ((Ea j : ℂ) + η * Complex.I) (Sum.inl i) (Sum.inl i) *
          G Sig Xm ((Ea j : ℂ) + η * Complex.I) (Sum.inr μ) (Sum.inr μ) - wa j‖ ≤
        (2 * K + 1) * θ ∧
      ‖G Sig Xm ((Eb j : ℂ) + η * Complex.I) (Sum.inl i) (Sum.inl i) *
          G Sig Xm ((Eb j : ℂ) + η * Complex.I) (Sum.inr μ) (Sum.inr μ) - wb j‖ ≤
        (2 * K + 1) * θ)
    (hw : ∀ j, ‖wb j - wa j‖ ≤ κ₀)
    (hΘ : 24 * (8 * (K + 1)) ^ 5 * (4 * θ + (2 * (2 * K + 1) * θ + κ₀)) ≤ Θ) (hΘ1 : Θ ≤ 1) :
    |smT 3 F Sig Xm η Ea Eb i μ (Xm i μ) -
        ∑ j, fderiv ℝ F (fun j' => smCount (QN Sig Xm) η (Ea j') (Eb j')) (Pi.single j 1) *
          (-(1 / Real.pi) *
            (2 * ((6 * (G Sig Xm ((Eb j : ℂ) + η * Complex.I) (Sum.inr μ) (Sum.inl i) *
                wb j)).im -
              (6 * (G Sig Xm ((Ea j : ℂ) + η * Complex.I) (Sum.inr μ) (Sum.inl i) *
                wa j)).im)))| ≤
      l * (Cb * (4 * Θ ^ 2 + (8 + 24 * (2 * K + 1)) * θ ^ 2)) := by
  set φ : ℝ → Fin l → ℝ := fun t j => smCount (QN Sig (Xupd Xm i μ t)) η (Ea j) (Eb j)
    with hφdef
  have hφ : ∀ (j : Fin l) (n : ℕ), ContDiff ℝ n fun t => φ t j := fun j n =>
    derivative_contDiff_smCount hSig Xm hη (Ea j) (Eb j) i μ n
  have hφ0 : φ (Xm i μ) = fun j' => smCount (QN Sig Xm) η (Ea j') (Eb j') := by
    simp only [hφdef, dthird_Xupd_self]
  have hT : smT 3 F Sig Xm η Ea Eb i μ (Xm i μ) = iteratedDeriv 3 (F ∘ φ) (Xm i μ) := rfl
  have hΘ0 : 0 ≤ Θ := le_trans (by positivity) hΘ
  have hCb : 0 ≤ Cb := (norm_nonneg _).trans (hFb 0 (by norm_num) 0)
  have hz : ∀ E : ℝ, 0 < ((E : ℂ) + η * Complex.I).im := fun E => by simpa using hη
  have hsym : ∀ E : ℝ, G Sig Xm ((E : ℂ) + η * Complex.I) (Sum.inl i) (Sum.inr μ) =
      G Sig Xm ((E : ℂ) + η * Complex.I) (Sum.inr μ) (Sum.inl i) := fun E => by
    have h := congrFun (congrFun (G_transpose hSig Xm (hz E)) (Sum.inr μ)) (Sum.inl i)
    rw [Matrix.transpose_apply] at h
    exact h
  -- the entry derivatives of `𝒳`
  have hder : ∀ (j : Fin l) (n : ℕ), 1 ≤ n → n ≤ 5 →
      |iteratedDeriv n (fun s => φ s j) (Xm i μ)| ≤ Θ := by
    intro j n hn1 hn5
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    refine (dthird_deriv_le_small hSig Xm hη (Ea j) (Eb j) i μ (Xm i μ) (L := K + 1) (θ := θ)
      (κ := 2 * (2 * K + 1) * θ + κ₀) (by linarith) hθ0 hθ1 ?_ ?_ ?_ ?_ ?_ (by omega)).trans hΘ
    · rw [dthird_Xupd_self]; exact fun a ha b hb => (hJ j a ha b hb).1
    · rw [dthird_Xupd_self]; exact fun a ha b hb => (hJ j a ha b hb).2
    · rw [dthird_Xupd_self]; exact (hoff j).1
    · rw [dthird_Xupd_self]; exact (hoff j).2
    · rw [dthird_Xupd_self]
      set Ga := G Sig Xm ((Ea j : ℂ) + η * Complex.I)
      set Gb := G Sig Xm ((Eb j : ℂ) + η * Complex.I)
      have e : Gb (Sum.inl i) (Sum.inl i) * Gb (Sum.inr μ) (Sum.inr μ) -
          Ga (Sum.inl i) (Sum.inl i) * Ga (Sum.inr μ) (Sum.inr μ) =
          (Gb (Sum.inl i) (Sum.inl i) * Gb (Sum.inr μ) (Sum.inr μ) - wb j) + (wb j - wa j) -
            (Ga (Sum.inl i) (Sum.inl i) * Ga (Sum.inr μ) (Sum.inr μ) - wa j) := by ring
      rw [e]
      calc _ ≤ (2 * K + 1) * θ + κ₀ + (2 * K + 1) * θ :=
            (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
              (add_le_add (hd j).2 (hw j))) (hd j).1)
        _ = 2 * (2 * K + 1) * θ + κ₀ := by ring
  -- the derivatives of `∂_j F ∘ φ`
  have hgc : ∀ j : Fin l, ContDiff ℝ 4 fun x : Fin l → ℝ => fderiv ℝ F x (Pi.single j 1) :=
    fun j => (hF.fderiv_right (m := 4) (by norm_num)).clm_apply contDiff_const
  have hgd : ∀ (j : Fin l) (n : ℕ), 1 ≤ n → n ≤ 2 →
      |iteratedDeriv n (fun s => fderiv ℝ F (φ s) (Pi.single j 1)) (Xm i μ)| ≤
        n.factorial * Cb * Θ := fun j n hn1 hn2 =>
    dthird_comp_le_small (k := 4) (hgc j) (dthird_partial_bound hF hFb j) φ hφ hn1 (by omega)
      (Xm i μ) hΘ0 hΘ1 fun i' h1 h2 j' => hder j' i' h1 (by omega)
  have hg0 : ∀ j : Fin l, |fderiv ℝ F (fun j' => smCount (QN Sig Xm) η (Ea j') (Eb j'))
      (Pi.single j 1)| ≤ Cb := fun j => by
    have h := dthird_partial_bound hF hFb j 0 (by norm_num)
      (fun j' => smCount (QN Sig Xm) η (Ea j') (Eb j'))
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  -- the third derivative of `𝒳` and its leading term
  have hrest : ∀ j : Fin l, |iteratedDeriv 3 (fun s => φ s j) (Xm i μ) -
      -(1 / Real.pi) *
        (2 * ((6 * (G Sig Xm ((Eb j : ℂ) + η * Complex.I) (Sum.inr μ) (Sum.inl i) * wb j)).im -
          (6 * (G Sig Xm ((Ea j : ℂ) + η * Complex.I) (Sum.inr μ) (Sum.inl i) * wa j)).im))| ≤
      (8 + 24 * (2 * K + 1)) * θ ^ 2 := by
    intro j
    have h3 : iteratedDeriv 3 (fun s => φ s j) (Xm i μ) =
        -(1 / Real.pi) * (((-1 : ℝ) ^ 2 * ((2 : ℕ).factorial : ℝ)) *
          ((Matrix.trace ((Delta i μ 1 *
              G Sig (Xupd Xm i μ (Xm i μ)) ((Eb j : ℂ) + η * Complex.I)) ^ (2 + 1))).im -
            (Matrix.trace ((Delta i μ 1 *
              G Sig (Xupd Xm i μ (Xm i μ)) ((Ea j : ℂ) + η * Complex.I)) ^ (2 + 1))).im)) :=
      derivative_iteratedDeriv_smCount hSig Xm hη (Ea j) (Eb j) i μ 2 (Xm i μ)
    rw [dthird_Xupd_self, dthird_trace_Delta_pow, dthird_trace_Delta_pow,
      dthird_trace_cube _ i μ (hsym _), dthird_trace_cube _ i μ (hsym _)] at h3
    rw [h3]
    set ga := G Sig Xm ((Ea j : ℂ) + η * Complex.I) (Sum.inr μ) (Sum.inl i)
    set gb := G Sig Xm ((Eb j : ℂ) + η * Complex.I) (Sum.inr μ) (Sum.inl i)
    set da := G Sig Xm ((Ea j : ℂ) + η * Complex.I) (Sum.inl i) (Sum.inl i) *
      G Sig Xm ((Ea j : ℂ) + η * Complex.I) (Sum.inr μ) (Sum.inr μ)
    set db := G Sig Xm ((Eb j : ℂ) + η * Complex.I) (Sum.inl i) (Sum.inl i) *
      G Sig Xm ((Eb j : ℂ) + η * Complex.I) (Sum.inr μ) (Sum.inr μ)
    have e : ∀ g d w : ℂ, (2 * g ^ 3 + 6 * g * d).im - (6 * (g * w)).im =
        (2 * g ^ 3 + 6 * g * (d - w)).im := fun g d w => by
      rw [← Complex.sub_im]; congr 1; ring
    have key : -(1 / Real.pi) * (((-1 : ℝ) ^ 2 * ((2 : ℕ).factorial : ℝ)) *
        ((2 * gb ^ 3 + 6 * gb * db).im - (2 * ga ^ 3 + 6 * ga * da).im)) -
        -(1 / Real.pi) * (2 * ((6 * (gb * wb j)).im - (6 * (ga * wa j)).im)) =
        -(1 / Real.pi) * (2 * ((2 * gb ^ 3 + 6 * gb * (db - wb j)).im -
          (2 * ga ^ 3 + 6 * ga * (da - wa j)).im)) := by
      rw [← e gb db (wb j), ← e ga da (wa j)]
      norm_num [Nat.factorial]
      ring
    rw [key]
    have hpi : 1 / Real.pi ≤ 1 := by
      rw [div_le_one Real.pi_pos]; linarith [Real.pi_gt_three]
    have ra := dthird_cube_rest (g := ga) (d := da) (w := wa j) hθ0 hθ1 (hoff j).1.2 (hd j).1
    have rb := dthird_cube_rest (g := gb) (d := db) (w := wb j) hθ0 hθ1 (hoff j).2.2 (hd j).2
    have hia : |(2 * ga ^ 3 + 6 * ga * (da - wa j)).im| ≤ (2 + 6 * (2 * K + 1)) * θ ^ 2 :=
      (Complex.abs_im_le_norm _).trans ra
    have hib : |(2 * gb ^ 3 + 6 * gb * (db - wb j)).im| ≤ (2 + 6 * (2 * K + 1)) * θ ^ 2 :=
      (Complex.abs_im_le_norm _).trans rb
    rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi), abs_mul,
      abs_two]
    have hs := abs_sub (2 * gb ^ 3 + 6 * gb * (db - wb j)).im
      (2 * ga ^ 3 + 6 * ga * (da - wa j)).im
    have h0 : 0 ≤ |(2 * gb ^ 3 + 6 * gb * (db - wb j)).im -
        (2 * ga ^ 3 + 6 * ga * (da - wa j)).im| := abs_nonneg _
    calc 1 / Real.pi * (2 * |(2 * gb ^ 3 + 6 * gb * (db - wb j)).im -
          (2 * ga ^ 3 + 6 * ga * (da - wa j)).im|) ≤
          1 * (2 * ((2 + 6 * (2 * K + 1)) * θ ^ 2 + (2 + 6 * (2 * K + 1)) * θ ^ 2)) := by
          gcongr
          linarith
      _ = (8 + 24 * (2 * K + 1)) * θ ^ 2 := by ring
  -- the assembly
  rw [hT, dthird_iteratedDeriv_three_comp hF φ hφ, hφ0, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j, |_| ≤ ∑ _j : Fin l, Cb * (4 * Θ ^ 2 + (8 + 24 * (2 * K + 1)) * θ ^ 2) := by
        refine Finset.sum_le_sum fun j _ => ?_
        have h1 := hgd j 1 le_rfl (by norm_num)
        have h2 := hgd j 2 (by norm_num) le_rfl
        have u1 := hder j 1 le_rfl (by norm_num)
        have u2 := hder j 2 (by norm_num) (by norm_num)
        have hr := hrest j
        have hc0 := hg0 j
        set A2 := iteratedDeriv 2 (fun s => fderiv ℝ F (φ s) (Pi.single j 1)) (Xm i μ)
        set A1 := iteratedDeriv 1 (fun s => fderiv ℝ F (φ s) (Pi.single j 1)) (Xm i μ)
        set U1 := iteratedDeriv 1 (fun s => φ s j) (Xm i μ)
        set U2 := iteratedDeriv 2 (fun s => φ s j) (Xm i μ)
        set U3 := iteratedDeriv 3 (fun s => φ s j) (Xm i μ)
        set c := fderiv ℝ F (fun j' => smCount (QN Sig Xm) η (Ea j') (Eb j')) (Pi.single j 1)
        set Mj := -(1 / Real.pi) *
          (2 * ((6 * (G Sig Xm ((Eb j : ℂ) + η * Complex.I) (Sum.inr μ) (Sum.inl i) *
              wb j)).im -
            (6 * (G Sig Xm ((Ea j : ℂ) + η * Complex.I) (Sum.inr μ) (Sum.inl i) * wa j)).im))
        have e : A2 * U1 + 2 * A1 * U2 + c * U3 - c * Mj =
            A2 * U1 + 2 * A1 * U2 + c * (U3 - Mj) := by ring
        rw [e]
        norm_num [Nat.factorial] at h1 h2
        have hA2U1 : |A2 * U1| ≤ 2 * Cb * Θ * Θ := by
          rw [abs_mul]; exact mul_le_mul h2 u1 (abs_nonneg _) (by positivity)
        have hA1U2 : |2 * A1 * U2| ≤ 2 * (Cb * Θ * Θ) := by
          rw [abs_mul, abs_mul, abs_two, mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul h1 u2 (abs_nonneg _) (by positivity))
            (by norm_num : (0 : ℝ) ≤ 2)
        have hcU : |c * (U3 - Mj)| ≤ Cb * ((8 + 24 * (2 * K + 1)) * θ ^ 2) := by
          rw [abs_mul]; exact mul_le_mul hc0 hr (abs_nonneg _) hCb
        calc |A2 * U1 + 2 * A1 * U2 + c * (U3 - Mj)| ≤
              |A2 * U1| + |2 * A1 * U2| + |c * (U3 - Mj)| := by
              refine (abs_add_le _ _).trans ?_
              linarith [abs_add_le (A2 * U1) (2 * A1 * U2)]
          _ ≤ 2 * Cb * Θ * Θ + 2 * (Cb * Θ * Θ) + Cb * ((8 + 24 * (2 * K + 1)) * θ ^ 2) := by
              linarith
          _ = Cb * (4 * Θ ^ 2 + (8 + 24 * (2 * K + 1)) * θ ^ 2) := by ring
    _ = l * (Cb * (4 * Θ ^ 2 + (8 + 24 * (2 * K + 1)) * θ ^ 2)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ## The leading term summed over the entries -/

/-- The leading terms summed against `s`: for `|c_j| ≤ C_b`, `|w| ≤ W` and
`|∑_μ s_{iμ} G_{μi}| ≤ ρ` at both window points,
`|∑_{i,μ} s_{iμ} ∑_j c_j (-π⁻¹) 2 Im[6 G_{μi} w_i]_{z_a}^{z_b}| ≤ l C_b M · 24 W ρ`; the sum
over `μ` is taken inside, against the test vector `s_i`. -/
private lemma dthird_main_sum {l : ℕ} (s : Fin M → Fin N → ℝ) (c : Fin l → ℝ)
    (ga gb : Fin l → Fin M → Fin N → ℂ) (wa wb : Fin l → Fin M → ℂ) {Cb W ρ : ℝ}
    (hc : ∀ j, |c j| ≤ Cb) (hW : ∀ j i, ‖wa j i‖ ≤ W ∧ ‖wb j i‖ ≤ W)
    (hρ : ∀ j i, ‖∑ μ, (s i μ : ℂ) * ga j i μ‖ ≤ ρ ∧ ‖∑ μ, (s i μ : ℂ) * gb j i μ‖ ≤ ρ) :
    |∑ i, ∑ μ, s i μ * ∑ j, c j * (-(1 / Real.pi) * (2 * ((6 * (gb j i μ * wb j i)).im -
        (6 * (ga j i μ * wa j i)).im)))| ≤ l * (Cb * (M * (24 * (W * ρ)))) := by
  have e : ∀ (w : ℂ) (g : Fin N → ℂ) (si : Fin N → ℝ),
      ∑ μ, si μ * (6 * (g μ * w)).im = (6 * (w * ∑ μ, (si μ : ℂ) * g μ)).im := by
    intro w g si
    rw [show 6 * (w * ∑ μ, (si μ : ℂ) * g μ) = ∑ μ, (si μ : ℂ) * (6 * (g μ * w)) by
      rw [Finset.mul_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun μ _ => by ring,
      Complex.im_sum]
    simp only [Complex.im_ofReal_mul]
  have hsum : ∑ i, ∑ μ, s i μ * ∑ j, c j * (-(1 / Real.pi) * (2 * ((6 * (gb j i μ * wb j i)).im -
        (6 * (ga j i μ * wa j i)).im))) =
      ∑ j, c j * ∑ i, (-(1 / Real.pi) * (2 * ((6 * (wb j i * ∑ μ, (s i μ : ℂ) * gb j i μ)).im -
        (6 * (wa j i * ∑ μ, (s i μ : ℂ) * ga j i μ)).im))) := by
    calc _ = ∑ i, ∑ μ, ∑ j, s i μ * (c j * (-(1 / Real.pi) *
          (2 * ((6 * (gb j i μ * wb j i)).im - (6 * (ga j i μ * wa j i)).im)))) := by
          simp only [Finset.mul_sum]
      _ = ∑ i, ∑ j, ∑ μ, s i μ * (c j * (-(1 / Real.pi) *
          (2 * ((6 * (gb j i μ * wb j i)).im - (6 * (ga j i μ * wa j i)).im)))) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ j, ∑ i, ∑ μ, s i μ * (c j * (-(1 / Real.pi) *
          (2 * ((6 * (gb j i μ * wb j i)).im - (6 * (ga j i μ * wa j i)).im)))) :=
          Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← e, ← e, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum,
            Finset.mul_sum]
          exact Finset.sum_congr rfl fun μ _ => by ring
  rw [hsum]
  have hpi : 1 / Real.pi ≤ 1 := by
    rw [div_le_one Real.pi_pos]; linarith [Real.pi_gt_three]
  have hterm : ∀ j i, |-(1 / Real.pi) * (2 * ((6 * (wb j i * ∑ μ, (s i μ : ℂ) * gb j i μ)).im -
      (6 * (wa j i * ∑ μ, (s i μ : ℂ) * ga j i μ)).im))| ≤ 24 * (W * ρ) := by
    intro j i
    have hW0 : 0 ≤ W := (norm_nonneg _).trans (hW j i).1
    have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans (hρ j i).1
    have h6 : ∀ (w S : ℂ), ‖w‖ ≤ W → ‖S‖ ≤ ρ → |(6 * (w * S)).im| ≤ 6 * (W * ρ) := by
      intro w S hw hS
      refine (Complex.abs_im_le_norm _).trans ?_
      rw [norm_mul, norm_mul]
      have : ‖(6 : ℂ)‖ = 6 := by norm_num
      rw [this]
      gcongr
    have ha := h6 _ _ (hW j i).1 (hρ j i).1
    have hb := h6 _ _ (hW j i).2 (hρ j i).2
    rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi), abs_mul, abs_two]
    have hs := abs_sub (6 * (wb j i * ∑ μ, (s i μ : ℂ) * gb j i μ)).im
      (6 * (wa j i * ∑ μ, (s i μ : ℂ) * ga j i μ)).im
    have h0 : 0 ≤ |(6 * (wb j i * ∑ μ, (s i μ : ℂ) * gb j i μ)).im -
        (6 * (wa j i * ∑ μ, (s i μ : ℂ) * ga j i μ)).im| := abs_nonneg _
    calc _ ≤ 1 * (2 * (6 * (W * ρ) + 6 * (W * ρ))) := by
          gcongr
          linarith
      _ = 24 * (W * ρ) := by ring
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j, |c j * _| ≤ ∑ _j : Fin l, Cb * (M * (24 * (W * ρ))) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        have hCb : 0 ≤ Cb := (abs_nonneg _).trans (hc j)
        refine mul_le_mul (hc j) ((Finset.abs_sum_le_sum_abs _ _).trans ?_) (abs_nonneg _) hCb
        calc ∑ i, |_| ≤ ∑ _i : Fin M, 24 * (W * ρ) := Finset.sum_le_sum fun i _ => hterm j i
          _ = M * (24 * (W * ρ)) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = l * (Cb * (M * (24 * (W * ρ)))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ## The events and the exponent bookkeeping -/

/-- Union bound for finitely many events of probability `≥ 1 - q`: a nonnegative integrable
`T` with `E T ≤ |ι| q` such that at every point either all events hold or `T ≥ 1`. -/
private lemma dthird_events {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {ι : Type*} [Fintype ι] (P : ι → Set Ω) {q : ℝ} (hq : 0 ≤ q)
    (hP : ∀ x, (ℙ : Measure Ω) (P x)ᶜ ≤ ENNReal.ofReal q) :
    ∃ T : Ω → ℝ, (∀ ω, 0 ≤ T ω) ∧ Integrable T ∧ ∫ ω, T ω ≤ Fintype.card ι * q ∧
      ∀ ω, (∀ x, ω ∈ P x) ∨ 1 ≤ T ω := by
  set Q : ι → Set Ω := fun x => toMeasurable (ℙ : Measure Ω) (P x)ᶜ with hQ
  have hQm : ∀ x, MeasurableSet (Q x) := fun x => measurableSet_toMeasurable _ _
  have hind0 : ∀ x ω, 0 ≤ (Q x).indicator (1 : Ω → ℝ) ω := fun x ω =>
    Set.indicator_nonneg (fun _ _ => zero_le_one) ω
  have hindi : ∀ x ∈ (Finset.univ : Finset ι), Integrable ((Q x).indicator (1 : Ω → ℝ)) :=
    fun x _ => (integrable_const (1 : ℝ)).indicator (hQm x)
  refine ⟨fun ω => ∑ x, (Q x).indicator 1 ω, fun ω => Finset.sum_nonneg fun x _ => hind0 x ω,
    integrable_finsetSum _ hindi, ?_, fun ω => ?_⟩
  · rw [integral_finsetSum _ hindi]
    calc ∑ x, ∫ ω, (Q x).indicator (1 : Ω → ℝ) ω = ∑ x, (ℙ : Measure Ω).real (Q x) :=
          Finset.sum_congr rfl fun x _ => integral_indicator_one (hQm x)
      _ ≤ ∑ _x : ι, q := Finset.sum_le_sum fun x _ => by
          rw [measureReal_def, hQ, measure_toMeasurable]
          exact ENNReal.toReal_le_of_le_ofReal hq (hP _)
      _ = Fintype.card ι * q := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  · by_cases h : ∀ x, ω ∈ P x
    · exact Or.inl h
    · right
      push Not at h
      obtain ⟨x, hx⟩ := h
      have hmem : ω ∈ Q x := subset_toMeasurable _ _ hx
      have h1 : (Q x).indicator (1 : Ω → ℝ) ω = 1 := by
        rw [Set.indicator_of_mem hmem, Pi.one_apply]
      have hle := Finset.single_le_sum (f := fun x => (Q x).indicator (1 : Ω → ℝ) ω)
        (fun x _ => hind0 x ω) (Finset.mem_univ x)
      linarith

/-- The exponent bookkeeping of the third-order sum: the entry remainders
(`MN · N^{-2/3+20ε}`), the leading terms (`M · N^{-1/6+10ε} √N`) and the bad events
(`MN · N^{4+54ε} · (MN + M) N^{-8}`) are at most a constant times `S C_b N^{4/3+21ε}`, for
`M ≤ τ⁻¹ N`. -/
private lemma dthird_final_arith {N : ℕ} (hN : 1 ≤ N) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200)
    {m l τi S Cb a A K₂ : ℝ} (hm0 : 0 ≤ m) (hm : m ≤ τi * N) (hτi : 0 ≤ τi) (hl : 0 ≤ l)
    (hS : 0 ≤ S) (hCb : 0 ≤ Cb) (ha : 0 ≤ a) (hA : 0 ≤ A) :
    m * N * S * (l * (Cb * (a * ((N : ℝ) ^ (-1 / 3 + 10 * ε)) ^ 2))) +
        l * (Cb * (m * (24 * (K₂ * K₂ * ((N : ℝ) ^ ε * (τi * (2 * (N : ℝ) ^ (-1 / 3 + 9 * ε)) *
          (S * √N))))))) +
        m * N * S * (6 * Cb * (384 * (A * (N : ℝ) ^ (4 / 3 + 18 * ε))) ^ 3) *
          (l * 2 * (m * N + m) * (N : ℝ) ^ (-(8 : ℝ))) ≤
      (τi * l * a + l * (48 * τi ^ 2 * K₂ ^ 2) + 24 * 384 ^ 3 * A ^ 3 * l * τi ^ 2) * S * Cb *
        (N : ℝ) ^ (4 / 3 + 21 * ε) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set P : ℝ := (N : ℝ) ^ (4 / 3 + 21 * ε) with hP
  have r2 : ∀ x y : ℝ, (N : ℝ) ^ x * (N : ℝ) ^ y = (N : ℝ) ^ (x + y) := fun x y =>
    (Real.rpow_add hn x y).symm
  have hle : ∀ {x : ℝ}, x ≤ 4 / 3 + 21 * ε → (N : ℝ) ^ x ≤ P := fun h =>
    Real.rpow_le_rpow_of_exponent_le hn1 h
  have hN1 : (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
  have hsq : √(N : ℝ) = (N : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have hx2 : ((N : ℝ) ^ (-1 / 3 + 10 * ε)) ^ 2 = (N : ℝ) ^ (-2 / 3 + 20 * ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]; congr 1; push_cast; ring
  have hW3 : (384 * (A * (N : ℝ) ^ (4 / 3 + 18 * ε))) ^ 3 =
      384 ^ 3 * A ^ 3 * (N : ℝ) ^ (4 + 54 * ε) := by
    rw [mul_pow, mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ (4 / 3 + 18 * ε)) 3,
      ← Real.rpow_mul hn.le,
      show (4 / 3 + 18 * ε) * ((3 : ℕ) : ℝ) = 4 + 54 * ε by push_cast; ring]
    ring
  have hmN : m * N ≤ τi * (N : ℝ) ^ (2 : ℝ) := by
    rw [show (N : ℝ) ^ (2 : ℝ) = N * N by rw [Real.rpow_two, sq]]
    nlinarith
  have hmN' : m * N + m ≤ 2 * τi * (N : ℝ) ^ (2 : ℝ) := by
    have : m ≤ m * N := by nlinarith
    linarith
  -- the three terms
  have t1 : m * N * S * (l * (Cb * (a * ((N : ℝ) ^ (-1 / 3 + 10 * ε)) ^ 2))) ≤
      τi * l * a * S * Cb * P := by
    rw [hx2]
    have e : (N : ℝ) ^ (2 : ℝ) * (N : ℝ) ^ (-2 / 3 + 20 * ε) ≤ P := by
      rw [r2]; exact hle (by linarith)
    calc m * N * S * (l * (Cb * (a * (N : ℝ) ^ (-2 / 3 + 20 * ε)))) =
          (m * N) * (N : ℝ) ^ (-2 / 3 + 20 * ε) * (S * l * Cb * a) := by ring
      _ ≤ (τi * (N : ℝ) ^ (2 : ℝ)) * (N : ℝ) ^ (-2 / 3 + 20 * ε) * (S * l * Cb * a) := by
          gcongr
      _ = τi * ((N : ℝ) ^ (2 : ℝ) * (N : ℝ) ^ (-2 / 3 + 20 * ε)) * (S * l * Cb * a) := by ring
      _ ≤ τi * P * (S * l * Cb * a) := by gcongr
      _ = τi * l * a * S * Cb * P := by ring
  have t2 : l * (Cb * (m * (24 * (K₂ * K₂ * ((N : ℝ) ^ ε * (τi * (2 * (N : ℝ) ^ (-1 / 3 + 9 * ε)) *
          (S * √N))))))) ≤ l * (48 * τi ^ 2 * K₂ ^ 2) * S * Cb * P := by
    have e : (N : ℝ) ^ (1 : ℝ) * ((N : ℝ) ^ ε * ((N : ℝ) ^ (-1 / 3 + 9 * ε) *
        (N : ℝ) ^ (1 / 2 : ℝ))) ≤ P := by
      rw [r2, r2, r2]; exact hle (by linarith)
    have hm' : m ≤ τi * (N : ℝ) ^ (1 : ℝ) := by rw [← hN1]; exact hm
    have h0 : 0 ≤ (N : ℝ) ^ ε * ((N : ℝ) ^ (-1 / 3 + 9 * ε) * (N : ℝ) ^ (1 / 2 : ℝ)) := by
      positivity
    calc l * (Cb * (m * (24 * (K₂ * K₂ * ((N : ℝ) ^ ε * (τi * (2 * (N : ℝ) ^ (-1 / 3 + 9 * ε)) *
          (S * √N))))))) =
          m * ((N : ℝ) ^ ε * ((N : ℝ) ^ (-1 / 3 + 9 * ε) * (N : ℝ) ^ (1 / 2 : ℝ))) *
            (48 * l * Cb * K₂ ^ 2 * τi * S) := by rw [hsq]; ring
      _ ≤ (τi * (N : ℝ) ^ (1 : ℝ)) * ((N : ℝ) ^ ε * ((N : ℝ) ^ (-1 / 3 + 9 * ε) *
            (N : ℝ) ^ (1 / 2 : ℝ))) * (48 * l * Cb * K₂ ^ 2 * τi * S) := by
          gcongr
      _ = τi * ((N : ℝ) ^ (1 : ℝ) * ((N : ℝ) ^ ε * ((N : ℝ) ^ (-1 / 3 + 9 * ε) *
            (N : ℝ) ^ (1 / 2 : ℝ)))) * (48 * l * Cb * K₂ ^ 2 * τi * S) := by ring
      _ ≤ τi * P * (48 * l * Cb * K₂ ^ 2 * τi * S) := by gcongr
      _ = l * (48 * τi ^ 2 * K₂ ^ 2) * S * Cb * P := by ring
  have t3 : m * N * S * (6 * Cb * (384 * (A * (N : ℝ) ^ (4 / 3 + 18 * ε))) ^ 3) *
      (l * 2 * (m * N + m) * (N : ℝ) ^ (-(8 : ℝ))) ≤
        24 * 384 ^ 3 * A ^ 3 * l * τi ^ 2 * S * Cb * P := by
    rw [hW3]
    have e : (N : ℝ) ^ (2 : ℝ) * ((N : ℝ) ^ (2 : ℝ) * ((N : ℝ) ^ (4 + 54 * ε) *
        (N : ℝ) ^ (-(8 : ℝ)))) ≤ P := by
      rw [r2, r2, r2]; exact hle (by linarith)
    have h8 : 0 ≤ (N : ℝ) ^ (-(8 : ℝ)) := by positivity
    have h54 : 0 ≤ (N : ℝ) ^ (4 + 54 * ε) := by positivity
    have hmN0 : 0 ≤ m * N := by positivity
    calc m * N * S * (6 * Cb * (384 ^ 3 * A ^ 3 * (N : ℝ) ^ (4 + 54 * ε))) *
          (l * 2 * (m * N + m) * (N : ℝ) ^ (-(8 : ℝ))) =
          (m * N) * ((m * N + m) * ((N : ℝ) ^ (4 + 54 * ε) * (N : ℝ) ^ (-(8 : ℝ)))) *
            (12 * 384 ^ 3 * A ^ 3 * l * S * Cb) := by ring
      _ ≤ (τi * (N : ℝ) ^ (2 : ℝ)) * ((2 * τi * (N : ℝ) ^ (2 : ℝ)) *
            ((N : ℝ) ^ (4 + 54 * ε) * (N : ℝ) ^ (-(8 : ℝ)))) *
            (12 * 384 ^ 3 * A ^ 3 * l * S * Cb) := by
          gcongr
      _ = 2 * τi ^ 2 * ((N : ℝ) ^ (2 : ℝ) * ((N : ℝ) ^ (2 : ℝ) * ((N : ℝ) ^ (4 + 54 * ε) *
            (N : ℝ) ^ (-(8 : ℝ))))) * (12 * 384 ^ 3 * A ^ 3 * l * S * Cb) := by ring
      _ ≤ 2 * τi ^ 2 * P * (12 * 384 ^ 3 * A ^ 3 * l * S * Cb) := by gcongr
      _ = 24 * 384 ^ 3 * A ^ 3 * l * τi ^ 2 * S * Cb * P := by ring
  calc _ ≤ τi * l * a * S * Cb * P + l * (48 * τi ^ 2 * K₂ ^ 2) * S * Cb * P +
        24 * 384 ^ 3 * A ^ 3 * l * τi ^ 2 * S * Cb * P := add_le_add (add_le_add t1 t2) t3
    _ = _ := by ring

/-! ## The good event in the frames `R_μ` -/

/-- The bound on the good event with one matrix `X_μ` per column `μ`, all with the smoothed
counts of `Y`: if every entry `(i, μ)` of `X_μ` satisfies the hypotheses of the one-entry bound
with the values `w_{a,j,i}`, `w_{b,j,i}` (`|w| ≤ W`) and the sums `∑_μ s_{iμ} G(X_μ)_{μi}` are at
most `ρ` at all window points, then
`|∑_{i,μ} s_{iμ} ∂³_{iμ} F(𝒳(X_μ))| ≤ MN S l C_b (4Θ² + (8 + 24(2K+1)) θ²) + l C_b M · 24 W ρ`. -/
private lemma dthird_good_frame {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (Y : Matrix (Fin M) (Fin N) ℝ) (Xf : Fin N → Matrix (Fin M) (Fin N) ℝ) {η : ℝ} (hη : 0 < η)
    {l : ℕ} {F : (Fin l → ℝ) → ℝ} {Cb : ℝ} (hF : ContDiff ℝ 5 F)
    (hFb : ∀ m ≤ 5, ∀ x, ‖iteratedFDeriv ℝ m F x‖ ≤ Cb) (Ea Eb : Fin l → ℝ)
    (hcount : ∀ (μ : Fin N) (j : Fin l),
      smCount (QN Sig (Xf μ)) η (Ea j) (Eb j) = smCount (QN Sig Y) η (Ea j) (Eb j))
    (s : Fin M → Fin N → ℝ) {S : ℝ} (hs : ∀ i μ, |s i μ| ≤ S)
    (hS0 : 0 ≤ S) (wa wb : Fin l → Fin M → ℂ) {K θ κ₀ Θ W ρ : ℝ}
    (hK : 0 ≤ K) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hκ₀ : 0 ≤ κ₀)
    (hJ : ∀ j i μ, ∀ a ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
      ∀ b ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
        ‖G Sig (Xf μ) ((Ea j : ℂ) + η * Complex.I) a b‖ ≤ K + 1 ∧
          ‖G Sig (Xf μ) ((Eb j : ℂ) + η * Complex.I) a b‖ ≤ K + 1)
    (hoff : ∀ j (i : Fin M) (μ : Fin N),
      (‖G Sig (Xf μ) ((Ea j : ℂ) + η * Complex.I) (Sum.inl i) (Sum.inr μ)‖ ≤ θ ∧
        ‖G Sig (Xf μ) ((Ea j : ℂ) + η * Complex.I) (Sum.inr μ) (Sum.inl i)‖ ≤ θ) ∧
      (‖G Sig (Xf μ) ((Eb j : ℂ) + η * Complex.I) (Sum.inl i) (Sum.inr μ)‖ ≤ θ ∧
        ‖G Sig (Xf μ) ((Eb j : ℂ) + η * Complex.I) (Sum.inr μ) (Sum.inl i)‖ ≤ θ))
    (hd : ∀ j (i : Fin M) (μ : Fin N),
      ‖G Sig (Xf μ) ((Ea j : ℂ) + η * Complex.I) (Sum.inl i) (Sum.inl i) *
          G Sig (Xf μ) ((Ea j : ℂ) + η * Complex.I) (Sum.inr μ) (Sum.inr μ) - wa j i‖ ≤
        (2 * K + 1) * θ ∧
      ‖G Sig (Xf μ) ((Eb j : ℂ) + η * Complex.I) (Sum.inl i) (Sum.inl i) *
          G Sig (Xf μ) ((Eb j : ℂ) + η * Complex.I) (Sum.inr μ) (Sum.inr μ) - wb j i‖ ≤
        (2 * K + 1) * θ)
    (hw : ∀ j i, ‖wb j i - wa j i‖ ≤ κ₀)
    (hΘ : 24 * (8 * (K + 1)) ^ 5 * (4 * θ + (2 * (2 * K + 1) * θ + κ₀)) ≤ Θ) (hΘ1 : Θ ≤ 1)
    (hW : ∀ j i, ‖wa j i‖ ≤ W ∧ ‖wb j i‖ ≤ W)
    (hρ : ∀ j i,
      ‖∑ μ, (s i μ : ℂ) * G Sig (Xf μ) ((Ea j : ℂ) + η * Complex.I) (Sum.inr μ) (Sum.inl i)‖ ≤
          ρ ∧
        ‖∑ μ, (s i μ : ℂ) * G Sig (Xf μ) ((Eb j : ℂ) + η * Complex.I) (Sum.inr μ) (Sum.inl i)‖ ≤
          ρ) :
    |∑ i, ∑ μ, s i μ * smT 3 F Sig (Xf μ) η Ea Eb i μ (Xf μ i μ)| ≤
      M * N * S * (l * (Cb * (4 * Θ ^ 2 + (8 + 24 * (2 * K + 1)) * θ ^ 2))) +
        l * (Cb * (M * (24 * (W * ρ)))) := by
  set c : Fin l → ℝ := fun j => fderiv ℝ F
    (fun j' => smCount (QN Sig Y) η (Ea j') (Eb j')) (Pi.single j 1) with hcdef
  have hc : ∀ j, |c j| ≤ Cb := fun j => by
    have h := dthird_partial_bound hF hFb j 0 (by norm_num)
      (fun j' => smCount (QN Sig Y) η (Ea j') (Eb j'))
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  set R : ℝ := l * (Cb * (4 * Θ ^ 2 + (8 + 24 * (2 * K + 1)) * θ ^ 2)) with hR
  set Mt : Fin l → Fin M → Fin N → ℝ := fun j i μ => -(1 / Real.pi) *
    (2 * ((6 * (G Sig (Xf μ) ((Eb j : ℂ) + η * Complex.I) (Sum.inr μ) (Sum.inl i) *
        wb j i)).im -
      (6 * (G Sig (Xf μ) ((Ea j : ℂ) + η * Complex.I) (Sum.inr μ) (Sum.inl i) * wa j i)).im))
    with hMt
  have hent : ∀ (i : Fin M) (μ : Fin N),
      |smT 3 F Sig (Xf μ) η Ea Eb i μ (Xf μ i μ) - ∑ j, c j * Mt j i μ| ≤ R := fun i μ => by
    have h := dthird_entry hSig (Xf μ) hη hF hFb Ea Eb i μ (fun j => wa j i) (fun j => wb j i)
      hK hθ0 hθ1 hκ₀ (fun j => hJ j i μ) (fun j => hoff j i μ) (fun j => hd j i μ)
      (fun j => hw j i) hΘ hΘ1
    have e : (fun j' => smCount (QN Sig (Xf μ)) η (Ea j') (Eb j')) =
        fun j' => smCount (QN Sig Y) η (Ea j') (Eb j') := funext (hcount μ)
    rw [e] at h
    exact h
  have hmain : |∑ i, ∑ μ, s i μ * ∑ j, c j * Mt j i μ| ≤ l * (Cb * (M * (24 * (W * ρ)))) :=
    dthird_main_sum s c
      (fun j i μ => G Sig (Xf μ) ((Ea j : ℂ) + η * Complex.I) (Sum.inr μ) (Sum.inl i))
      (fun j i μ => G Sig (Xf μ) ((Eb j : ℂ) + η * Complex.I) (Sum.inr μ) (Sum.inl i)) wa wb hc
      hW hρ
  have hsplit : ∑ i, ∑ μ, s i μ * smT 3 F Sig (Xf μ) η Ea Eb i μ (Xf μ i μ) =
      ∑ i, ∑ μ, s i μ * (smT 3 F Sig (Xf μ) η Ea Eb i μ (Xf μ i μ) - ∑ j, c j * Mt j i μ) +
        ∑ i, ∑ μ, s i μ * ∑ j, c j * Mt j i μ := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun μ _ => by ring
  rw [hsplit]
  refine (abs_add_le _ _).trans (add_le_add ?_ hmain)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |∑ μ, _| ≤ ∑ _i : Fin M, ∑ _μ : Fin N, S * R := by
        refine Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine Finset.sum_le_sum fun μ _ => ?_
        rw [abs_mul]
        exact mul_le_mul (hs i μ) (hent i μ) (abs_nonneg _) hS0
    _ = M * N * S * R := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ,
          Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
        ring

/-- The summands `ω ↦ ∂³_{iμ} F(𝒳(X))` are integrable, bounded by `D`, when `X` is measurable
and `|∂³_{iμ} F(𝒳)| ≤ D` uniformly. -/
private lemma dthird_integrable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {η : ℝ} (hη : 0 < η) {l : ℕ}
    {F : (Fin l → ℝ) → ℝ} (hF : ContDiff ℝ 5 F) (Ea Eb : Fin l → ℝ)
    {X : Ω → Matrix (Fin M) (Fin N) ℝ}
    (hXm : Measurable X) (i : Fin M) (μ : Fin N) (hXe : Measurable fun ω => X ω i μ) {D : ℝ}
    (hD : ∀ (Xm : Matrix (Fin M) (Fin N) ℝ) (u : ℝ), |smT 3 F Sig Xm η Ea Eb i μ u| ≤ D) :
    Integrable fun ω => smT 3 F Sig (X ω) η Ea Eb i μ (X ω i μ) := by
  obtain ⟨f, hf⟩ : ∃ f : Matrix (Fin M) (Fin N) ℝ → ℝ → ℝ,
      f = fun Xm t => smF F Sig (Xupd Xm i μ t) η Ea Eb := ⟨_, rfl⟩
  have hfc : ∀ Xm, ContDiff ℝ 5 (f Xm) := fun Xm => by
    rw [hf]
    exact hF.comp (contDiff_pi.2 fun j =>
      derivative_contDiff_smCount hSig Xm hη (Ea j) (Eb j) i μ 5)
  have hf0c : Continuous fun q : Matrix (Fin M) (Fin N) ℝ × ℝ => f q.1 q.2 := by
    rw [hf]
    exact hF.continuous.comp (continuous_pi fun j =>
      (dthird_continuous_smCount hSig hη (Ea j) (Eb j)).comp (dthird_continuous_Xupd i μ))
  have hΦ := dthird_measurable_iteratedDeriv f hf0c.measurable 5 hfc 3 (by norm_num)
  have hp : Measurable fun ω => (X ω, X ω i μ) := hXm.prodMk hXe
  have h := hΦ.comp hp
  have hmeas : Measurable fun ω => iteratedDeriv 3 (f (X ω)) (X ω i μ) := by
    exact h
  have e : (fun ω => smT 3 F Sig (X ω) η Ea Eb i μ (X ω i μ)) =
      fun ω => iteratedDeriv 3 (f (X ω)) (X ω i μ) := by rw [hf]; rfl
  rw [e]
  exact Integrable.of_bound hmeas.aestronglyMeasurable D (Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, ← congrFun e ω]; exact hD _ _)

/-! ## The third-order sum for `Q̇`

The third-order term of the Green function comparison in the proof of Theorem 11.4 (Theorem 3.18
with the eigenvalues of `Q̇`, from Theorems 11.2 and 11.3), for a deterministic array `s_{iμ}`.
The third derivative of `F(𝒳(Ẋ))` in the entry `X_{iμ}` is `|π̄ e_μ|³` times the third
derivative of `F(𝒳)` in the entry `(i, μ)` of `Ẋ R_μ`, at `(Ẋ R_μ)_{iμ}`. -/

set_option maxHeartbeats 400000 in
-- many linear-arithmetic steps over a large context
/-- The third-order sum for `Q̇`:
`|∑_{i,μ} s_{iμ} E[|π̄ e_μ|³ ∂³_{iμ} F(𝒳(Ẋ R_μ))]| ≤ K S C_b N^{4/3+21ε}` for deterministic
`|s_{iμ}| ≤ S`, windows within `3N^{-2/3+ε}` of the edge `a_k`, and every smoothing scale
`η ∈ [N^{-2/3-9ε}/2, N^{-2/3-9ε}]`. -/
theorem dot_smT_third_sum (τ : ℝ) (C : ℕ → ℝ) (l : ℕ) (ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 200) :
    ∃ K : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)] (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (X : Ω → Matrix (Fin M) (Fin N) ℝ) (k : ℕ) (s : Fin M → Fin N → ℝ) (S : ℝ)
      (F : (Fin l → ℝ) → ℝ) (Cb : ℝ) (Ea Eb : Fin l → ℝ) (η : ℝ),
      IsModel τ C M N Sig X → RegularEdge τ N (specOf Sig) k → (∀ i μ, |s i μ| ≤ S) →
      ContDiff ℝ 5 F → (∀ m ≤ 5, ∀ x, ‖iteratedFDeriv ℝ m F x‖ ≤ Cb) →
      EdgeWindows N (edgeVal N (specOf Sig) k) ε Ea Eb →
      etaE N ε / 2 ≤ η → η ≤ etaE N ε →
      |∑ i, ∑ μ, s i μ * (∫ ω, dotLen N ^ 3 * smT 3 F Sig (Xdot (X ω) * dotRefl N μ) η Ea Eb i μ
          ((Xdot (X ω) * dotRefl N μ) i μ))| ≤
        K * S * Cb * (N : ℝ) ^ (4 / 3 + 21 * ε) := by
  obtain ⟨K₂, hK₂, N₂, hdet⟩ := dot_det τ ε hτ hε hε1
  obtain ⟨K₁, hK₁, N₁, hev⟩ := dot_event τ C ε ε 8 hτ hε hε1 hε le_rfl
  obtain ⟨K₃, hK₃, N₃, hmpi⟩ := dot_mPi_window τ ε hτ hε hε1
  obtain ⟨N₅, hsG⟩ := dot_sG τ C ε ε 8 hτ hε hε1 hε
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℝ, c₁ = 4 * τ⁻¹ ^ 2 := ⟨_, rfl⟩
  obtain ⟨cΘ, hcΘ⟩ : ∃ cΘ : ℝ,
      cΘ = 24 * (8 * (K₁ + 1)) ^ 5 * ((4 + 2 * (2 * K₁ + 1)) * c₁ + K₃) := ⟨_, rfl⟩
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ℝ, a₀ = τ⁻¹ + 2 * τ⁻¹ * (1 + τ⁻¹) + 3 := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = a₀ ^ 2 + 3 * a₀ + 1 := ⟨_, rfl⟩
  obtain ⟨ar, hardef⟩ : ∃ ar : ℝ, ar = 4 * cΘ ^ 2 + (8 + 24 * (2 * K₁ + 1)) * c₁ ^ 2 :=
    ⟨_, rfl⟩
  have hy2 : -1 / 3 + 10 * ε < 0 := by linarith
  obtain ⟨N₄, hN₄⟩ := eventually_atTop.1 ((dthird_ev_small hy2 c₁).and (dthird_ev_small hy2 cΘ))
  refine ⟨(4 * τ⁻¹) * l * ar + l * (48 * (4 * τ⁻¹) ^ 2 * K₂ ^ 2) +
      24 * 384 ^ 3 * (4 * A) ^ 3 * l * (4 * τ⁻¹) ^ 2,
    max (max (max N₁ N₂) (max N₃ N₄)) (max N₅ 2), ?_⟩
  intro N hN Ω _ _ M Sig X k s S F Cb Ea Eb η hm hk hs hF hFb hW hηl hηu
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) (le_of_max_le_right hN)
  have hNN : 1 ≤ N := by omega
  have hN5 : N₅ ≤ N := le_trans (le_max_left _ _) (le_of_max_le_right hN)
  have hN1 : N₁ ≤ N :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_of_max_le_left hN)
  have hN2' : N₂ ≤ N :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_of_max_le_left hN)
  have hN3 : N₃ ≤ N :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_of_max_le_left hN)
  have hN4 : N₄ ≤ N :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_of_max_le_left hN)
  obtain ⟨hA1, hA2⟩ := hN₄ N hN4
  have hn : (0 : ℝ) < N := by exact_mod_cast hNN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hNN
  have hSig := hm.sigma.posDef
  have hda : DensityAssumptions τ N (specOf Sig) := hm.diagModel_specOf.densityAssumptions hτ
  have hηN : 0 < etaE N ε := Real.rpow_pos_of_pos hn _
  have hη : 0 < η := by linarith
  have hη1 : η ≤ 1 := hηu.trans (Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith))
  have hCb : 0 ≤ Cb := (norm_nonneg _).trans (hFb 0 (by norm_num) 0)
  have hτi : 0 < τ⁻¹ := inv_pos.2 hτ
  have hK₁0 : 0 ≤ K₁ := hK₁.le
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; positivity
  have hcΘ0 : 0 ≤ cΘ := by rw [hcΘ]; positivity
  have ha₀0 : 0 < a₀ := by rw [ha₀]; positivity
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have har0 : 0 ≤ ar := by rw [hardef]; positivity
  obtain ⟨hL1, hL2⟩ := dot_dotLen_bounds hN2
  have hL0 : 0 ≤ dotLen N := by linarith
  -- the factor `|π̄ e_μ|³`
  have hL3 : ∑ i, ∑ μ, s i μ * (∫ ω, dotLen N ^ 3 * smT 3 F Sig (Xdot (X ω) * dotRefl N μ) η
      Ea Eb i μ ((Xdot (X ω) * dotRefl N μ) i μ)) =
      dotLen N ^ 3 * ∑ i, ∑ μ, s i μ * (∫ ω, smT 3 F Sig (Xdot (X ω) * dotRefl N μ) η Ea Eb i μ
        ((Xdot (X ω) * dotRefl N μ) i μ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [integral_const_mul]
    ring
  rw [hL3, abs_mul, abs_pow, abs_of_nonneg hL0]
  refine (mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ hL0 hL2.le)).trans ?_
  -- the dimensions
  have hMpos : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h0 | h0
    · exfalso
      have := hm.ratio_ge
      simp [h0] at this
      linarith
    · exact h0
  have hMN : (M : ℝ) ≤ τ⁻¹ * N := by
    have := hm.ratio_le
    rwa [div_le_iff₀ hn] at this
  have hMN4 : (M : ℝ) ≤ (4 * τ⁻¹) * N := by
    have : τ⁻¹ * (N : ℝ) ≤ (4 * τ⁻¹) * N := by nlinarith
    linarith
  have hS0 : 0 ≤ S := (abs_nonneg _).trans (hs ⟨0, hMpos⟩ ⟨0, by omega⟩)
  -- the deterministic bound
  have hW1 : 1 ≤ 4 * A * (N : ℝ) ^ (4 / 3 + 18 * ε) := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (4 / 3 + 18 * ε) := Real.one_le_rpow hn1 (by linarith)
    have h2 : 1 ≤ A := by rw [hAdef]; nlinarith
    nlinarith
  have hSn : ‖Sig‖ ≤ a₀ := (dthird_norm_sig_le hτ hm.sigma).trans (by
    rw [ha₀]
    have : 0 ≤ 2 * τ⁻¹ * (1 + τ⁻¹) := by positivity
    linarith)
  have hedge := dthird_edgeVal_le hτ hm hk
  have hwin1 : (N : ℝ) ^ (-2 / 3 + ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
  have hEa : ∀ E : ℝ, |E - edgeVal N (specOf Sig) k| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) →
      |E| ≤ a₀ := by
    intro E hE
    have h1 : |E| ≤ |E - edgeVal N (specOf Sig) k| + |edgeVal N (specOf Sig) k| := by
      have := abs_add_le (E - edgeVal N (specOf Sig) k) (edgeVal N (specOf Sig) k)
      simpa using this
    rw [ha₀]
    linarith
  have hη2 : (etaE N ε) ^ 2 * (N : ℝ) ^ (4 / 3 + 18 * ε) = 1 := by
    rw [etaE, ← Real.rpow_natCast, ← Real.rpow_mul hn.le, ← Real.rpow_add hn]
    have e : (-2 / 3 - 9 * ε) * ((2 : ℕ) : ℝ) + (4 / 3 + 18 * ε) = 0 := by push_cast; ring
    rw [e, Real.rpow_zero]
  have hGW : ∀ (Wm : Matrix (Fin M) (Fin N) ℝ) (E : ℝ), |E| ≤ a₀ → ∀ a b : Fin M ⊕ Fin N,
      ‖G Sig Wm ((E : ℂ) + η * Complex.I) a b‖ ≤ 4 * A * (N : ℝ) ^ (4 / 3 + 18 * ε) := by
    intro Wm E hE a b
    refine (derivative_norm_G_entry_le hSig ha₀0 hSn Wm hE hη hη1 a b).trans ?_
    rw [← hAdef, div_le_iff₀ (by positivity)]
    have hx0 : 0 ≤ (N : ℝ) ^ (4 / 3 + 18 * ε) := by positivity
    have hsq : etaE N ε ^ 2 ≤ 4 * η ^ 2 := by
      have h2 : etaE N ε ≤ 2 * η := by linarith
      calc etaE N ε ^ 2 ≤ (2 * η) ^ 2 := pow_le_pow_left₀ hηN.le h2 2
        _ = 4 * η ^ 2 := by ring
    calc A = A * ((etaE N ε) ^ 2 * (N : ℝ) ^ (4 / 3 + 18 * ε)) := by rw [hη2, mul_one]
      _ ≤ A * ((4 * η ^ 2) * (N : ℝ) ^ (4 / 3 + 18 * ε)) := by gcongr
      _ = 4 * A * (N : ℝ) ^ (4 / 3 + 18 * ε) * η ^ 2 := by ring
  have hcrude : ∀ (i : Fin M) (μ : Fin N) (Xm : Matrix (Fin M) (Fin N) ℝ) (u : ℝ),
      |smT 3 F Sig Xm η Ea Eb i μ u| ≤
        6 * Cb * (384 * (4 * A * (N : ℝ) ^ (4 / 3 + 18 * ε))) ^ 3 := by
    intro i μ Xm u
    refine (dthird_crude hSig hη hF hFb Ea Eb i μ hW1
      (fun Xm j a b => ⟨hGW _ _ (hEa _ (hW j).1) a b, hGW _ _ (hEa _ (hW j).2) a b⟩) Xm u
      (n := 3) (by norm_num)).trans (le_of_eq ?_)
    norm_num [Nat.factorial]
  -- measurability and integrability of the summands
  have hXm : Measurable X := dthird_measurable_X hm.entries
  have hXdc : Continuous fun Xm : Matrix (Fin M) (Fin N) ℝ => Xdot Xm := by
    unfold Xdot
    exact continuous_id.matrix_mul continuous_const
  have hWm : ∀ μ : Fin N, Measurable fun ω => Xdot (X ω) * dotRefl N μ := fun μ =>
    (hXdc.matrix_mul continuous_const).measurable.comp hXm
  have hint : ∀ (i : Fin M) (μ : Fin N),
      Integrable fun ω => smT 3 F Sig (Xdot (X ω) * dotRefl N μ) η Ea Eb i μ
        ((Xdot (X ω) * dotRefl N μ) i μ) := fun i μ =>
    dthird_integrable hSig hη hF Ea Eb (X := fun ω => Xdot (X ω) * dotRefl N μ) (hWm μ) i μ
      ((hWm μ).eval_matrix (i := i) (j := μ)) (hcrude i μ)
  have hYeq : (∫ ω, ∑ i, ∑ μ, s i μ * smT 3 F Sig (Xdot (X ω) * dotRefl N μ) η Ea Eb i μ
        ((Xdot (X ω) * dotRefl N μ) i μ)) =
      ∑ i, ∑ μ, s i μ * (∫ ω, smT 3 F Sig (Xdot (X ω) * dotRefl N μ) η Ea Eb i μ
        ((Xdot (X ω) * dotRefl N μ) i μ)) := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun μ _ => (hint i μ).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun μ _ => (hint i μ).const_mul _]
    exact Finset.sum_congr rfl fun μ _ => integral_const_mul _ _
  rw [← hYeq]
  -- the events
  obtain ⟨Aset, hAsetdef⟩ : ∃ Aset : ℝ → Fin M → Fin N → Set Ω, Aset = fun (E : ℝ) i μ => {ω |
      (∀ a ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
        ∀ b ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
          ‖G Sig (Xdot (X ω) * dotRefl N μ) ((E : ℂ) + η * Complex.I) a b -
              piMat Sig (mFun N (specOf Sig) ((E : ℂ) + η * Complex.I)) a b‖ ≤
            (N : ℝ) ^ ε * (τ⁻¹ ^ 2 * Psi N (specOf Sig) ((E : ℂ) + η * Complex.I)) ∧
          ‖G Sig (Xdot (X ω) * dotRefl N μ) ((E : ℂ) + η * Complex.I) a b‖ ≤ K₁ + 1) ∧
      ‖G Sig (Xdot (X ω) * dotRefl N μ) ((E : ℂ) + η * Complex.I) (Sum.inl i) (Sum.inr μ)‖ ≤
        (N : ℝ) ^ ε * (τ⁻¹ ^ 2 * Psi N (specOf Sig) ((E : ℂ) + η * Complex.I)) ∧
      ‖G Sig (Xdot (X ω) * dotRefl N μ) ((E : ℂ) + η * Complex.I) (Sum.inr μ) (Sum.inl i)‖ ≤
        (N : ℝ) ^ ε * (τ⁻¹ ^ 2 * Psi N (specOf Sig) ((E : ℂ) + η * Complex.I)) ∧
      ‖G Sig (Xdot (X ω) * dotRefl N μ) ((E : ℂ) + η * Complex.I) (Sum.inl i) (Sum.inl i) *
            G Sig (Xdot (X ω) * dotRefl N μ) ((E : ℂ) + η * Complex.I) (Sum.inr μ) (Sum.inr μ) -
          mFun N (specOf Sig) ((E : ℂ) + η * Complex.I) *
            piMat (N := N) Sig (mFun N (specOf Sig) ((E : ℂ) + η * Complex.I))
              (Sum.inl i) (Sum.inl i)‖ ≤
        (2 * K₁ + 1) *
          ((N : ℝ) ^ ε * (τ⁻¹ ^ 2 * Psi N (specOf Sig) ((E : ℂ) + η * Complex.I)))} :=
    ⟨_, rfl⟩
  obtain ⟨Bset, hBsetdef⟩ : ∃ Bset : ℝ → Fin M → Set Ω, Bset = fun (E : ℝ) i => {ω |
      ‖∑ μ, (s i μ : ℂ) *
          G Sig (Xdot (X ω) * dotRefl N μ) ((E : ℂ) + η * Complex.I) (Sum.inr μ) (Sum.inl i)‖ ≤
        (N : ℝ) ^ ε *
          (2 * τ⁻¹ * Psi N (specOf Sig) ((E : ℂ) + η * Complex.I) * testNorm (s i))} :=
    ⟨_, rfl⟩
  have hAprob : ∀ E : ℝ, |E - edgeVal N (specOf Sig) k| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) →
      ∀ (i : Fin M) (μ : Fin N),
        (ℙ : Measure Ω) (Aset E i μ)ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(8 : ℝ))) := by
    intro E hE i μ
    rw [hAsetdef]
    exact (hev N hN1 M Sig X k hm hk E hE η hηl hηu i μ).2
  have hBprob : ∀ E : ℝ, |E - edgeVal N (specOf Sig) k| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) →
      ∀ i : Fin M, (ℙ : Measure Ω) (Bset E i)ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(8 : ℝ))) := by
    intro E hE i
    refine le_trans (measure_mono ?_) (hsG N hN5 M Sig X k hm hk E hE η hηl hηu (s i) i)
    intro ω hω
    rw [hBsetdef] at hω
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω ⊢
    exact hω
  obtain ⟨P, hPdef⟩ : ∃ P : (Fin l × Bool) × ((Fin M × Fin N) ⊕ Fin M) → Set Ω,
      P = fun x => Sum.elim (fun p => Aset (if x.1.2 then Ea x.1.1 else Eb x.1.1) p.1 p.2)
        (fun i => Bset (if x.1.2 then Ea x.1.1 else Eb x.1.1) i) x.2 := ⟨_, rfl⟩
  have hEj : ∀ jb : Fin l × Bool, |(if jb.2 then Ea jb.1 else Eb jb.1) -
      edgeVal N (specOf Sig) k| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) := by
    rintro ⟨j, b⟩
    cases b
    · exact (hW j).2
    · exact (hW j).1
  obtain ⟨T, hT0, hTi, hTint, hT1⟩ := dthird_events P (q := (N : ℝ) ^ (-(8 : ℝ)))
    (by positivity) fun x => by
      obtain ⟨jb, p⟩ := x
      rcases p with ⟨i, μ⟩ | i
      · rw [hPdef]; exact hAprob _ (hEj jb) i μ
      · rw [hPdef]; exact hBprob _ (hEj jb) i
  -- the bound on the good event
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = (N : ℝ) ^ (-1 / 3 + 10 * ε) := ⟨_, rfl⟩
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ,
      ρ = (N : ℝ) ^ ε * ((4 * τ⁻¹) * (2 * (N : ℝ) ^ (-1 / 3 + 9 * ε)) * (S * √N)) := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := by rw [hxdef]; positivity
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; positivity
  have hdE := fun E (hE : |E - edgeVal N (specOf Sig) k| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε)) =>
    hdet N hN2' M Sig k hSig hda hk E hE η hηl hηu
  have hδle : ∀ E : ℝ, |E - edgeVal N (specOf Sig) k| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) →
      (N : ℝ) ^ ε * (τ⁻¹ ^ 2 * Psi N (specOf Sig) ((E : ℂ) + η * Complex.I)) ≤ c₁ * x := by
    intro E hE
    have h := (hdE E hE).1
    have e : (N : ℝ) ^ ε * (N : ℝ) ^ (-1 / 3 + 9 * ε) = (N : ℝ) ^ (-1 / 3 + 10 * ε) := by
      rw [← Real.rpow_add hn]; congr 1; ring
    have hNe : 0 ≤ (N : ℝ) ^ ε := by positivity
    calc (N : ℝ) ^ ε * (τ⁻¹ ^ 2 * Psi N (specOf Sig) ((E : ℂ) + η * Complex.I))
        ≤ (N : ℝ) ^ ε * (τ⁻¹ ^ 2 * (4 * (N : ℝ) ^ (-1 / 3 + 9 * ε))) := by gcongr
      _ = 4 * τ⁻¹ ^ 2 * ((N : ℝ) ^ ε * (N : ℝ) ^ (-1 / 3 + 9 * ε)) := by ring
      _ = c₁ * x := by rw [e, hc₁, hxdef]
  have hκle : K₃ * (N : ℝ) ^ (-1 / 3 + ε / 2) ≤ K₃ * x := by
    rw [hxdef]
    exact mul_le_mul_of_nonneg_left (dthird_rpow_le hNN (by linarith)) hK₃.le
  have hΘ : 24 * (8 * (K₁ + 1)) ^ 5 * (4 * (c₁ * x) +
      (2 * (2 * K₁ + 1) * (c₁ * x) + K₃ * (N : ℝ) ^ (-1 / 3 + ε / 2))) ≤ cΘ * x := by
    calc _ ≤ 24 * (8 * (K₁ + 1)) ^ 5 * (4 * (c₁ * x) +
          (2 * (2 * K₁ + 1) * (c₁ * x) + K₃ * x)) := by gcongr
      _ = cΘ * x := by rw [hcΘ]; ring
  have hΨ0 : ∀ E : ℝ, 0 ≤ Psi N (specOf Sig) ((E : ℂ) + η * Complex.I) := by
    intro E
    unfold Psi
    have him : ((E : ℂ) + η * Complex.I).im = η := by simp
    rw [him]
    exact add_nonneg (Real.sqrt_nonneg _) (div_nonneg zero_le_one (by positivity))
  have hρb : ∀ E : ℝ, |E - edgeVal N (specOf Sig) k| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) →
      ∀ i : Fin M, (N : ℝ) ^ ε * (2 * τ⁻¹ * Psi N (specOf Sig) ((E : ℂ) + η * Complex.I) *
        testNorm (s i)) ≤ ρ := by
    intro E hE i
    have hts := entryBounds_testNorm_le (s i) (hs i)
    have hP := (hdE E hE).1
    have ht0 : 0 ≤ testNorm (s i) := Real.sqrt_nonneg _
    have := hΨ0 E
    have e : (4 * τ⁻¹) * (2 * (N : ℝ) ^ (-1 / 3 + 9 * ε)) =
        2 * τ⁻¹ * (4 * (N : ℝ) ^ (-1 / 3 + 9 * ε)) := by ring
    rw [hρdef, e]
    gcongr
  have hgood : ∀ ω, (∀ x, ω ∈ P x) →
      |∑ i, ∑ μ, s i μ * smT 3 F Sig (Xdot (X ω) * dotRefl N μ) η Ea Eb i μ
          ((Xdot (X ω) * dotRefl N μ) i μ)| ≤
        M * N * S * (l * (Cb * (ar * x ^ 2))) + l * (Cb * (M * (24 * (K₂ * K₂ * ρ)))) := by
    intro ω hω
    have hA : ∀ (j : Fin l) (i : Fin M) (μ : Fin N),
        ω ∈ Aset (Ea j) i μ ∧ ω ∈ Aset (Eb j) i μ := fun j i μ => by
      have ha := hω ((j, true), Sum.inl (i, μ))
      have hb := hω ((j, false), Sum.inl (i, μ))
      rw [hPdef] at ha hb
      simp only [Sum.elim_inl, ite_true, Bool.false_eq_true, ite_false] at ha hb
      exact ⟨ha, hb⟩
    have hB : ∀ (j : Fin l) (i : Fin M), ω ∈ Bset (Ea j) i ∧ ω ∈ Bset (Eb j) i :=
      fun j i => by
        have ha := hω ((j, true), Sum.inr i)
        have hb := hω ((j, false), Sum.inr i)
        rw [hPdef] at ha hb
        simp only [Sum.elim_inr, ite_true, Bool.false_eq_true, ite_false] at ha hb
        exact ⟨ha, hb⟩
    rw [hAsetdef] at hA
    rw [hBsetdef] at hB
    simp only [Set.mem_ofPred_eq] at hA hB
    have h := dthird_good_frame hSig (Xdot (X ω)) (fun μ => Xdot (X ω) * dotRefl N μ) hη hF hFb
      Ea Eb (fun μ j => dot_smCount_mul_refl hSig.isHermitian hN2 (Xdot (X ω)) μ η (Ea j) (Eb j))
      s hs hS0
      (fun j i => mFun N (specOf Sig) ((Ea j : ℂ) + η * Complex.I) *
          piMat (N := N) Sig (mFun N (specOf Sig) ((Ea j : ℂ) + η * Complex.I))
            (Sum.inl i) (Sum.inl i))
      (fun j i => mFun N (specOf Sig) ((Eb j : ℂ) + η * Complex.I) *
          piMat (N := N) Sig (mFun N (specOf Sig) ((Eb j : ℂ) + η * Complex.I))
            (Sum.inl i) (Sum.inl i))
      (K := K₁) (θ := c₁ * x) (κ₀ := K₃ * (N : ℝ) ^ (-1 / 3 + ε / 2)) (Θ := cΘ * x)
      (W := K₂ * K₂) (ρ := ρ)
      hK₁0 (by positivity) (by rw [hxdef]; linarith) (by positivity)
      (fun j i μ a ha b hb => ⟨((hA j i μ).1.1 a ha b hb).2, ((hA j i μ).2.1 a ha b hb).2⟩)
      (fun j i μ => ⟨⟨(hA j i μ).1.2.1.trans (hδle _ (hW j).1),
          (hA j i μ).1.2.2.1.trans (hδle _ (hW j).1)⟩,
        ⟨(hA j i μ).2.2.1.trans (hδle _ (hW j).2),
          (hA j i μ).2.2.2.1.trans (hδle _ (hW j).2)⟩⟩)
      (fun j i μ => ⟨(hA j i μ).1.2.2.2.trans
          (mul_le_mul_of_nonneg_left (hδle _ (hW j).1) (by positivity)),
        (hA j i μ).2.2.2.2.trans
          (mul_le_mul_of_nonneg_left (hδle _ (hW j).2) (by positivity))⟩)
      (fun j i => (hmpi N hN3 M Sig k hSig hda hk (Ea j) (Eb j) (hW j).1 (hW j).2 η hηl
        hηu).2.2 i)
      hΘ (by rw [hxdef]; linarith)
      (fun j i => by
        have da := hdE (Ea j) (hW j).1
        have db := hdE (Eb j) (hW j).2
        refine ⟨?_, ?_⟩
        · rw [norm_mul]
          exact mul_le_mul da.2.1 (da.2.2 _ _) (norm_nonneg _) hK₂.le
        · rw [norm_mul]
          exact mul_le_mul db.2.1 (db.2.2 _ _) (norm_nonneg _) hK₂.le)
      (fun j i => ⟨(hB j i).1.trans (hρb _ (hW j).1 i), (hB j i).2.trans (hρb _ (hW j).2 i)⟩)
    refine h.trans (le_of_eq ?_)
    rw [hardef]; ring
  -- the deterministic bound everywhere
  have hbad : ∀ ω, |∑ i, ∑ μ, s i μ * smT 3 F Sig (Xdot (X ω) * dotRefl N μ) η Ea Eb i μ
        ((Xdot (X ω) * dotRefl N μ) i μ)| ≤
      M * N * S * (6 * Cb * (384 * (4 * A * (N : ℝ) ^ (4 / 3 + 18 * ε))) ^ 3) := by
    intro ω
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |∑ μ, _| ≤ ∑ _i : Fin M, ∑ _μ : Fin N,
          S * (6 * Cb * (384 * (4 * A * (N : ℝ) ^ (4 / 3 + 18 * ε))) ^ 3) := by
          refine Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_
          refine Finset.sum_le_sum fun μ _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hs i μ) (hcrude i μ _ _) (abs_nonneg _) hS0
      _ = M * N * S * (6 * Cb * (384 * (4 * A * (N : ℝ) ^ (4 / 3 + 18 * ε))) ^ 3) := by
          rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ,
            Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
          ring
  -- the integral
  set Bg : ℝ := M * N * S * (l * (Cb * (ar * x ^ 2))) + l * (Cb * (M * (24 * (K₂ * K₂ * ρ))))
    with hBg
  set Bc : ℝ := M * N * S * (6 * Cb * (384 * (4 * A * (N : ℝ) ^ (4 / 3 + 18 * ε))) ^ 3)
    with hBc
  have hBg0 : 0 ≤ Bg := by rw [hBg]; positivity
  have hBc0 : 0 ≤ Bc := by rw [hBc]; positivity
  have hpt : ∀ ω, ‖∑ i, ∑ μ, s i μ * smT 3 F Sig (Xdot (X ω) * dotRefl N μ) η Ea Eb i μ
        ((Xdot (X ω) * dotRefl N μ) i μ)‖ ≤ Bg + Bc * T ω := by
    intro ω
    rw [Real.norm_eq_abs]
    rcases hT1 ω with h | h
    · exact (hgood ω h).trans (le_add_of_nonneg_right (mul_nonneg hBc0 (hT0 ω)))
    · calc _ ≤ Bc := hbad ω
        _ ≤ Bc * T ω := le_mul_of_one_le_right hBc0 h
        _ ≤ Bg + Bc * T ω := le_add_of_nonneg_left hBg0
  have hcard : (Fintype.card ((Fin l × Bool) × ((Fin M × Fin N) ⊕ Fin M)) : ℝ) =
      l * 2 * (M * N + M) := by
    simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, Fintype.card_bool]
    push_cast; ring
  rw [hcard] at hTint
  have hI : |∫ ω, ∑ i, ∑ μ, s i μ * smT 3 F Sig (Xdot (X ω) * dotRefl N μ) η Ea Eb i μ
        ((Xdot (X ω) * dotRefl N μ) i μ)| ≤
      Bg + Bc * (l * 2 * (M * N + M) * (N : ℝ) ^ (-(8 : ℝ))) := by
    rw [← Real.norm_eq_abs]
    have hgi : Integrable fun ω => Bg + Bc * T ω := (integrable_const Bg).add (hTi.const_mul Bc)
    refine (norm_integral_le_of_norm_le hgi (Eventually.of_forall hpt)).trans ?_
    rw [integral_add (integrable_const Bg) (hTi.const_mul Bc), integral_const, integral_const_mul]
    simp only [probReal_univ, one_smul]
    gcongr
  refine hI.trans ?_
  rw [hBg, hBc, hxdef, hρdef]
  have := dthird_final_arith hNN hε hε1 (m := M) (l := l) (τi := 4 * τ⁻¹) (S := S) (Cb := Cb)
    (a := ar) (A := 4 * A) (K₂ := K₂) (Nat.cast_nonneg _) hMN4 (by positivity)
    (Nat.cast_nonneg _) hS0 hCb har0 (by positivity)
  linarith


#print axioms dot_smT_third_sum

end Anisotropic
