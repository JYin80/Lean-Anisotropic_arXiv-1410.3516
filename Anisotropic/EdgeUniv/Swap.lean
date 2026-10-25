import Anisotropic.Density.Count
import Anisotropic.Density.Critical
import Anisotropic.EdgeUniv.EntryBounds
import Anisotropic.EdgeUniv.SmCount
import Anisotropic.Entrywise.DiagModel
import Anisotropic.Framework.Domination
import Anisotropic.Framework.Model
import Anisotropic.LinAlg.Expansion
import Anisotropic.Rigidity.Defs

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # The one-entry swap between two laws with matching first two moments -/

/-- `F((𝒳_{[Ea_j, Eb_j]}(Q_N))_j)`. -/
def smF {l : ℕ} (F : (Fin l → ℝ) → ℝ) (Sig : Matrix (Fin M) (Fin M) ℝ)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (η : ℝ) (Ea Eb : Fin l → ℝ) : ℝ :=
  F (fun j => smCount (QN Sig Xm) η (Ea j) (Eb j))

/-- The `n`-th derivative of `smF` in the entry `(i, μ)`, at the value `u` of that entry. -/
def smT {l : ℕ} (n : ℕ) (F : (Fin l → ℝ) → ℝ) (Sig : Matrix (Fin M) (Fin M) ℝ)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (η : ℝ) (Ea Eb : Fin l → ℝ) (i : Fin M) (μ : Fin N)
    (u : ℝ) : ℝ :=
  iteratedDeriv n (fun t => smF F Sig (Xupd Xm i μ t) η Ea Eb) u

/-- Windows within `3 N^{-2/3+ε}` of the edge `a_k`. -/
def EdgeWindows (N : ℕ) (a ε : ℝ) {l : ℕ} (Ea Eb : Fin l → ℝ) : Prop :=
  ∀ j, |Ea j - a| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) ∧ |Eb j - a| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε)

/-! ## Traces of powers of `2 × 2` matrices -/

/-- Cayley–Hamilton for `2 × 2` matrices. -/
private lemma swap_sq_fin_two (A : Matrix (Fin 2) (Fin 2) ℂ) :
    A * A = A.trace • A - A.det • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

/-- The trace recursion `t_{k+2} = s t_{k+1} - P t_k` for `2 × 2` matrices. -/
private lemma swap_trace_pow_rec (A : Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ) :
    (A ^ (k + 2)).trace = A.trace * (A ^ (k + 1)).trace - A.det * (A ^ k).trace := by
  have h : A ^ (k + 2) = A ^ k * (A * A) := by rw [pow_add, sq]
  rw [h, swap_sq_fin_two, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, ← pow_succ, smul_eq_mul, smul_eq_mul]

private lemma swap_norm_trace_fin_two_le (A : Matrix (Fin 2) (Fin 2) ℂ) {W : ℝ}
    (hA : ∀ r c, ‖A r c‖ ≤ W) : ‖A.trace‖ ≤ 2 * W := by
  rw [Matrix.trace_fin_two]
  calc ‖A 0 0 + A 1 1‖ ≤ ‖A 0 0‖ + ‖A 1 1‖ := norm_add_le _ _
    _ ≤ 2 * W := by linarith [hA 0 0, hA 1 1]

private lemma swap_norm_det_fin_two_le (A : Matrix (Fin 2) (Fin 2) ℂ) {W : ℝ}
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
private lemma swap_norm_trace_pow_le (A : Matrix (Fin 2) (Fin 2) ℂ) {W : ℝ} (hW : 1 ≤ W)
    (hA : ∀ r c, ‖A r c‖ ≤ W) (k : ℕ) : ‖(A ^ k).trace‖ ≤ 2 * (4 * W) ^ k := by
  have hs := swap_norm_trace_fin_two_le A hA
  have hP := swap_norm_det_fin_two_le A hA
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
      rw [show k + 1 + 1 = k + 2 by ring, swap_trace_pow_rec]
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
private lemma swap_trace_pow_sub_le (A A' : Matrix (Fin 2) (Fin 2) ℂ) {W σ ρ : ℝ} (hW : 1 ≤ W)
    (hA : ∀ r c, ‖A r c‖ ≤ W) (hA' : ∀ r c, ‖A' r c‖ ≤ W) (hs : ‖A.trace‖ ≤ σ)
    (hs' : ‖A'.trace‖ ≤ σ) (hρ : ‖A.det - A'.det‖ ≤ ρ) (k : ℕ) :
    ‖(A ^ k).trace - (A' ^ k).trace‖ ≤ (8 * W) ^ k * (σ + ρ) := by
  have hσ0 : 0 ≤ σ := (norm_nonneg _).trans hs
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hρ
  have hP' := swap_norm_det_fin_two_le A' hA'
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
      rw [show k + 1 + 1 = k + 2 by ring, swap_trace_pow_rec, swap_trace_pow_rec]
      have t1 := swap_norm_trace_pow_le A hW hA (k + 1)
      have t1' := swap_norm_trace_pow_le A' hW hA' (k + 1)
      have t0 := swap_norm_trace_pow_le A hW hA k
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
private def swapBlock (B : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) (i : Fin M) (μ : Fin N) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![B (Sum.inr μ) (Sum.inl i), B (Sum.inr μ) (Sum.inr μ);
    B (Sum.inl i) (Sum.inl i), B (Sum.inl i) (Sum.inr μ)]

/-- `tr (Δ¹ B)^{k+1}` is the trace of the `(k+1)`-st power of the `2 × 2` block. -/
private lemma swap_trace_Delta_pow (B : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) (i : Fin M)
    (μ : Fin N) (k : ℕ) :
    ((Delta i μ 1 * B) ^ (k + 1)).trace = ((swapBlock B i μ) ^ (k + 1)).trace := by
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
  have h2 : R * P = swapBlock B i μ := by
    ext r c
    rw [Matrix.mul_apply]
    fin_cases r <;> fin_cases c <;> simp [hP, hR, swapBlock]
  have h3 : ∀ k : ℕ, (P * R) ^ (k + 1) = P * ((R * P) ^ k * R) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Matrix.mul_assoc]
  rw [h1, h3, Matrix.trace_mul_comm, Matrix.mul_assoc, ← pow_succ, h2]

private lemma swap_factorial_le {n : ℕ} (hn : n ≤ 4) : (n.factorial : ℝ) ≤ 24 := by
  have : n.factorial ≤ 24 := by interval_cases n <;> decide
  exact_mod_cast this

/-- `|-(1/π) (-1)^n n! (Im a - Im b)| ≤ 24 ‖a - b‖` for `n ≤ 4`. -/
private lemma swap_coef_le {n : ℕ} (hn : n ≤ 4) (a b : ℂ) :
    |-(1 / Real.pi) * (((-1 : ℝ) ^ n * (n.factorial : ℝ)) * (a.im - b.im))| ≤ 24 * ‖a - b‖ := by
  have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have h1 : |a.im - b.im| ≤ ‖a - b‖ := by
    rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
  rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi), Nat.abs_cast]
  have hf := swap_factorial_le hn
  have h0 : 0 ≤ ‖a - b‖ := norm_nonneg _
  have hp : 1 / Real.pi ≤ 1 := by rw [div_le_one (by positivity)]; exact hpi
  calc 1 / Real.pi * ((n.factorial : ℝ) * |a.im - b.im|) ≤ 1 * (24 * ‖a - b‖) := by
        gcongr
    _ = 24 * ‖a - b‖ := one_mul _

/-- Entry bounds at the two window points give `|∂^{n+1} 𝒳| ≤ 24 (8L)^5 (4θ + κ)` for
`n + 1 ≤ 5`: the `J × J` entries are at most `L`, the off-diagonal ones at most `θ ≤ 1`, and the
products `G_{ii} G_{μμ}` at the two points differ by at most `κ`. -/
private lemma swap_deriv_le_small {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
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
      ∀ r c, ‖swapBlock B i μ r c‖ ≤ L := by
    intro B hB r c
    fin_cases r <;> fin_cases c <;> simp only [swapBlock] <;> simp <;>
      first | exact hB _ hμJ _ hiJ | exact hB _ hμJ _ hμJ | exact hB _ hiJ _ hiJ |
        exact hB _ hiJ _ hμJ
  have htr : ∀ B : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ,
      (‖B (Sum.inl i) (Sum.inr μ)‖ ≤ θ ∧ ‖B (Sum.inr μ) (Sum.inl i)‖ ≤ θ) →
      ‖(swapBlock B i μ).trace‖ ≤ 2 * θ := by
    intro B hB
    rw [Matrix.trace_fin_two]
    simp only [swapBlock, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    calc _ ≤ ‖B (Sum.inr μ) (Sum.inl i)‖ + ‖B (Sum.inl i) (Sum.inr μ)‖ := norm_add_le _ _
      _ ≤ 2 * θ := by linarith [hB.1, hB.2]
  have hdet : ‖(swapBlock B₂ i μ).det - (swapBlock B₁ i μ).det‖ ≤ 2 * θ + κ := by
    rw [Matrix.det_fin_two, Matrix.det_fin_two]
    simp only [swapBlock, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
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
  refine (swap_coef_le hn _ _).trans ?_
  rw [swap_trace_Delta_pow, swap_trace_Delta_pow]
  have hd := swap_trace_pow_sub_le (swapBlock B₂ i μ) (swapBlock B₁ i μ) hL (hent B₂ h₂)
    (hent B₁ h₁) (htr B₂ o₂) (htr B₁ o₁) hdet (n + 1)
  have hp : (8 * L) ^ (n + 1) ≤ (8 * L) ^ 5 :=
    pow_le_pow_right₀ (by linarith) (by omega)
  have hk0 : 0 ≤ 2 * θ + (2 * θ + κ) := by
    linarith [norm_nonneg ((swapBlock B₂ i μ).det - (swapBlock B₁ i μ).det)]
  calc 24 * ‖((swapBlock B₂ i μ) ^ (n + 1)).trace - ((swapBlock B₁ i μ) ^ (n + 1)).trace‖
      ≤ 24 * ((8 * L) ^ (n + 1) * (2 * θ + (2 * θ + κ))) := by gcongr
    _ ≤ 24 * ((8 * L) ^ 5 * (2 * θ + (2 * θ + κ))) := by gcongr
    _ = 24 * (8 * L) ^ 5 * (4 * θ + κ) := by ring

/-- Entry bounds `|G_{ab}| ≤ W` (`W ≥ 1`) on `J × J` at both window points give
`|∂^{n+1} 𝒳| ≤ (384 W)^{n+1}` for `n + 1 ≤ 5`. -/
private lemma swap_deriv_le_crude {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {η : ℝ} (hη : 0 < η) (E₁ E₂ : ℝ) (i : Fin M) (μ : Fin N)
    (s : ℝ) {W : ℝ} (hW : 1 ≤ W)
    (h₁ : ∀ a b, ‖G Sig (Xupd Xm i μ s) ((E₁ : ℂ) + η * Complex.I) a b‖ ≤ W)
    (h₂ : ∀ a b, ‖G Sig (Xupd Xm i μ s) ((E₂ : ℂ) + η * Complex.I) a b‖ ≤ W)
    {n : ℕ} (hn : n ≤ 4) :
    |iteratedDeriv (n + 1) (fun t => smCount (QN Sig (Xupd Xm i μ t)) η E₁ E₂) s| ≤
      (384 * W) ^ (n + 1) := by
  have hent : ∀ B : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ, (∀ a b, ‖B a b‖ ≤ W) →
      ∀ r c, ‖swapBlock B i μ r c‖ ≤ W := by
    intro B hB r c
    fin_cases r <;> fin_cases c <;> simp only [swapBlock] <;> simp <;> exact hB _ _
  rw [derivative_iteratedDeriv_smCount hSig Xm hη E₁ E₂ i μ n s]
  refine (swap_coef_le hn _ _).trans ?_
  rw [swap_trace_Delta_pow, swap_trace_Delta_pow]
  have t2 := swap_norm_trace_pow_le _ hW (hent _ h₂) (n + 1)
  have t1 := swap_norm_trace_pow_le _ hW (hent _ h₁) (n + 1)
  have h4 : (0 : ℝ) ≤ (4 * W) ^ (n + 1) := by positivity
  calc 24 * ‖_ - _‖ ≤ 24 * (2 * (4 * W) ^ (n + 1) + 2 * (4 * W) ^ (n + 1)) := by
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add t2 t1)
    _ = 96 * (4 * W) ^ (n + 1) := by ring
    _ ≤ 96 ^ (n + 1) * (4 * W) ^ (n + 1) := by
        gcongr
        exact le_self_pow₀ (by norm_num) (by omega)
    _ = (384 * W) ^ (n + 1) := by rw [← mul_pow]; ring

private lemma swap_Xupd_self (Xm : Matrix (Fin M) (Fin N) ℝ) (i : Fin M) (μ : Fin N) :
    Xupd Xm i μ (Xm i μ) = Xm := by
  funext j ν
  by_cases h : j = i ∧ ν = μ
  · obtain ⟨rfl, rfl⟩ := h; simp [Xupd]
  · simp [Xupd, h]

private lemma swap_Xupd_Xupd (Xm : Matrix (Fin M) (Fin N) ℝ) (i : Fin M) (μ : Fin N) (s t : ℝ) :
    Xupd (Xupd Xm i μ s) i μ t = Xupd Xm i μ t := by
  funext j ν
  by_cases h : j = i ∧ ν = μ <;> simp [Xupd, h]

/-- From `|G_{ab} - Π_{ab}| ≤ θ ≤ 1` on `J × J`, with `|Π| ≤ K`, `Π_{iμ} = Π_{μi} = 0` and
`Π_{μμ} = m`: `|G_{ab}| ≤ K + 1`, `|G_{iμ}|, |G_{μi}| ≤ θ`, `|G_{ii} G_{μμ} - m Π_{ii}| ≤ (2K + 1) θ`. -/
private lemma swap_consequences {G P : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ} {m : ℂ}
    {K θ : ℝ} (i : Fin M) (μ : Fin N) (hPK : ∀ s t, ‖P s t‖ ≤ K)
    (hP1 : P (Sum.inl i) (Sum.inr μ) = 0) (hP2 : P (Sum.inr μ) (Sum.inl i) = 0)
    (hP3 : P (Sum.inr μ) (Sum.inr μ) = m) (hθ1 : θ ≤ 1)
    (h : ∀ a ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
      ∀ b ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)), ‖G a b - P a b‖ ≤ θ) :
    (∀ a ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
      ∀ b ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)), ‖G a b‖ ≤ K + 1) ∧
      (‖G (Sum.inl i) (Sum.inr μ)‖ ≤ θ ∧ ‖G (Sum.inr μ) (Sum.inl i)‖ ≤ θ) ∧
      ‖G (Sum.inl i) (Sum.inl i) * G (Sum.inr μ) (Sum.inr μ) -
          m * P (Sum.inl i) (Sum.inl i)‖ ≤ (2 * K + 1) * θ := by
  have hiJ : (Sum.inl i : Fin M ⊕ Fin N) ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)) :=
    Set.mem_insert _ _
  have hμJ : (Sum.inr μ : Fin M ⊕ Fin N) ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)) :=
    Set.mem_insert_of_mem _ rfl
  have hGK : ∀ a ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
      ∀ b ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)), ‖G a b‖ ≤ K + 1 := by
    intro a ha b hb
    have e : G a b = P a b + (G a b - P a b) := by ring
    rw [e]
    exact (norm_add_le _ _).trans (by linarith [hPK a b, h a ha b hb])
  have hθ0 : 0 ≤ θ := (norm_nonneg _).trans (h _ hiJ _ hiJ)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hPK (Sum.inl i) (Sum.inl i))
  refine ⟨hGK, ⟨?_, ?_⟩, ?_⟩
  · have := h _ hiJ _ hμJ
    rwa [hP1, sub_zero] at this
  · have := h _ hμJ _ hiJ
    rwa [hP2, sub_zero] at this
  · have e : G (Sum.inl i) (Sum.inl i) * G (Sum.inr μ) (Sum.inr μ) -
        m * P (Sum.inl i) (Sum.inl i) =
        (G (Sum.inl i) (Sum.inl i) - P (Sum.inl i) (Sum.inl i)) * G (Sum.inr μ) (Sum.inr μ) +
          P (Sum.inl i) (Sum.inl i) * (G (Sum.inr μ) (Sum.inr μ) - P (Sum.inr μ) (Sum.inr μ)) := by
      rw [hP3]; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h1 := mul_le_mul (h _ hiJ _ hiJ) (hGK _ hμJ _ hμJ) (norm_nonneg _) hθ0
    have h2 := mul_le_mul (hPK (Sum.inl i) (Sum.inl i)) (h _ hμJ _ hμJ) (norm_nonneg _) hK0
    calc _ ≤ θ * (K + 1) + K * θ := add_le_add h1 h2
      _ = (2 * K + 1) * θ := by ring

/-- The derivative bound at a perturbed entry: if the `J × J` entries of `G` at `X` are within
`δ_r ≤ 1` of `Π(m_r)` at the two window points `z_r = E_r + iη`, `|Π| ≤ K`,
`δ_r + 4(K+1)²|X_{iμ} - s| ≤ θ ≤ 1`, `2(K+1)|X_{iμ} - s| ≤ 1/2`, and
`|m_2 Π_{ii}(m_2) - m_1 Π_{ii}(m_1)| ≤ κ₀`, then at `X^{s}_{(iμ)}`,
`|∂^{n+1} 𝒳| ≤ 24 (8(K+1))^5 (4θ + 2(2K+1)θ + κ₀)` for `n + 1 ≤ 5`. -/
private lemma swap_deriv_le_pair {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {η : ℝ} (hη : 0 < η) (E₁ E₂ : ℝ) (i : Fin M) (μ : Fin N)
    (s : ℝ) {K δ₁ δ₂ θ κ₀ : ℝ} {m₁ m₂ : ℂ}
    (hδ₁ : ∀ a ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
      ∀ b ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
        ‖G Sig Xm ((E₁ : ℂ) + η * Complex.I) a b - piMat (N := N) Sig m₁ a b‖ ≤ δ₁)
    (hδ₂ : ∀ a ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
      ∀ b ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
        ‖G Sig Xm ((E₂ : ℂ) + η * Complex.I) a b - piMat (N := N) Sig m₂ a b‖ ≤ δ₂)
    (hP₁ : ∀ a b, ‖piMat (N := N) Sig m₁ a b‖ ≤ K) (hP₂ : ∀ a b, ‖piMat (N := N) Sig m₂ a b‖ ≤ K)
    (h1₁ : δ₁ ≤ 1) (h1₂ : δ₂ ≤ 1) (hd : 2 * (K + 1) * |Xm i μ - s| ≤ 1 / 2)
    (hθ₁ : δ₁ + 4 * (K + 1) ^ 2 * |Xm i μ - s| ≤ θ)
    (hθ₂ : δ₂ + 4 * (K + 1) ^ 2 * |Xm i μ - s| ≤ θ) (hθ1 : θ ≤ 1)
    (hmp : ‖m₂ * piMat (N := N) Sig m₂ (Sum.inl i) (Sum.inl i) -
      m₁ * piMat (N := N) Sig m₁ (Sum.inl i) (Sum.inl i)‖ ≤ κ₀)
    {n : ℕ} (hn : n ≤ 4) :
    |iteratedDeriv (n + 1) (fun t => smCount (QN Sig (Xupd Xm i μ t)) η E₁ E₂) s| ≤
      24 * (8 * (K + 1)) ^ 5 * (4 * θ + (2 * (2 * K + 1) * θ + κ₀)) := by
  have hz₁ : 0 < ((E₁ : ℂ) + η * Complex.I).im := by simpa using hη
  have hz₂ : 0 < ((E₂ : ℂ) + η * Complex.I).im := by simpa using hη
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hP₁ (Sum.inl i) (Sum.inl i))
  have hδ₁' : ∀ a ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
      ∀ b ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
        ‖G Sig (Xupd Xm i μ (Xm i μ)) ((E₁ : ℂ) + η * Complex.I) a b -
          piMat (N := N) Sig m₁ a b‖ ≤ δ₁ := by
    rw [swap_Xupd_self]; exact hδ₁
  have hδ₂' : ∀ a ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
      ∀ b ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
        ‖G Sig (Xupd Xm i μ (Xm i μ)) ((E₂ : ℂ) + η * Complex.I) a b -
          piMat (N := N) Sig m₂ a b‖ ≤ δ₂ := by
    rw [swap_Xupd_self]; exact hδ₂
  have hs₁ := entryBounds_stability_ref hSig Xm hz₁ i μ (Xm i μ) s K δ₁ _ hδ₁'
    (fun a _ b _ => hP₁ a b) h1₁ hd
  have hs₂ := entryBounds_stability_ref hSig Xm hz₂ i μ (Xm i μ) s K δ₂ _ hδ₂'
    (fun a _ b _ => hP₂ a b) h1₂ hd
  have hc₁ := swap_consequences (m := m₁) (G := G Sig (Xupd Xm i μ s) ((E₁ : ℂ) + η * Complex.I)) i μ hP₁
    (by simp [piMat]) (by simp [piMat]) (by simp [piMat]) hθ1
    fun a ha b hb => (hs₁ a ha b hb).trans hθ₁
  have hc₂ := swap_consequences (m := m₂) (G := G Sig (Xupd Xm i μ s) ((E₂ : ℂ) + η * Complex.I)) i μ hP₂
    (by simp [piMat]) (by simp [piMat]) (by simp [piMat]) hθ1
    fun a ha b hb => (hs₂ a ha b hb).trans hθ₂
  have hθ0 : 0 ≤ θ := (norm_nonneg _).trans ((hs₁ _ (Set.mem_insert _ _) _
    (Set.mem_insert _ _)).trans hθ₁)
  refine swap_deriv_le_small hSig Xm hη E₁ E₂ i μ s (by linarith) hθ0 hθ1 hc₁.1 hc₂.1 hc₁.2.1
    hc₂.2.1 ?_ hn
  set B₁ := G Sig (Xupd Xm i μ s) ((E₁ : ℂ) + η * Complex.I)
  set B₂ := G Sig (Xupd Xm i μ s) ((E₂ : ℂ) + η * Complex.I)
  have e : B₂ (Sum.inl i) (Sum.inl i) * B₂ (Sum.inr μ) (Sum.inr μ) -
      B₁ (Sum.inl i) (Sum.inl i) * B₁ (Sum.inr μ) (Sum.inr μ) =
      (B₂ (Sum.inl i) (Sum.inl i) * B₂ (Sum.inr μ) (Sum.inr μ) -
        m₂ * piMat (N := N) Sig m₂ (Sum.inl i) (Sum.inl i)) +
      (m₂ * piMat (N := N) Sig m₂ (Sum.inl i) (Sum.inl i) -
        m₁ * piMat (N := N) Sig m₁ (Sum.inl i) (Sum.inl i)) -
      (B₁ (Sum.inl i) (Sum.inl i) * B₁ (Sum.inr μ) (Sum.inr μ) -
        m₁ * piMat (N := N) Sig m₁ (Sum.inl i) (Sum.inl i)) := by ring
  rw [e]
  calc _ ≤ (2 * K + 1) * θ + κ₀ + (2 * K + 1) * θ :=
        (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add hc₂.2.2 hmp)) hc₁.2.2)
    _ = 2 * (2 * K + 1) * θ + κ₀ := by ring

/-! ## Derivatives of `F ∘ 𝒳` and Taylor's formula -/

/-- Iterated derivatives of a vector-valued function are taken componentwise. -/
private lemma swap_iteratedDeriv_pi {l : ℕ} (φ : ℝ → Fin l → ℝ)
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

/-- Faà di Bruno bound: if `‖D^m F‖ ≤ C_b` for `m ≤ 5` and the `i`-th derivatives of the
components of `φ` at `t` are at most `D^i` for `1 ≤ i ≤ n ≤ 5`, then
`|(F ∘ φ)^{(n)}(t)| ≤ n! C_b D^n`. -/
private lemma swap_comp_le {l : ℕ} {F : (Fin l → ℝ) → ℝ} {Cb : ℝ} (hF : ContDiff ℝ 5 F)
    (hFb : ∀ m ≤ 5, ∀ x, ‖iteratedFDeriv ℝ m F x‖ ≤ Cb) (φ : ℝ → Fin l → ℝ)
    (hφ : ∀ (j : Fin l) (n : ℕ), ContDiff ℝ n fun t => φ t j) {n : ℕ} (hn : n ≤ 5) (t : ℝ)
    {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ i, 1 ≤ i → i ≤ n → ∀ j, |iteratedDeriv i (fun s => φ s j) t| ≤ D ^ i) :
    |iteratedDeriv n (F ∘ φ) t| ≤ n.factorial * Cb * D ^ n := by
  have hφc : ContDiff ℝ 5 φ := contDiff_pi.2 fun j => hφ j 5
  rw [← Real.norm_eq_abs, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  refine norm_iteratedFDeriv_comp_le hF hφc (by exact_mod_cast hn) t
    (fun i hi => hFb i (hi.trans hn) _) fun i h1 h2 => ?_
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, swap_iteratedDeriv_pi φ hφ]
  exact (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => by
    rw [Real.norm_eq_abs]; exact hD i h1 h2 j

/-- The same bound with one small factor: if the component derivatives of orders `1, …, n` at
`t` are at most `Θ ∈ [0, 1]`, then `|(F ∘ φ)^{(n)}(t)| ≤ n! C_b Θ`. -/
private lemma swap_comp_le_small {l : ℕ} {F : (Fin l → ℝ) → ℝ} {Cb : ℝ} (hF : ContDiff ℝ 5 F)
    (hFb : ∀ m ≤ 5, ∀ x, ‖iteratedFDeriv ℝ m F x‖ ≤ Cb) (φ : ℝ → Fin l → ℝ)
    (hφ : ∀ (j : Fin l) (n : ℕ), ContDiff ℝ n fun t => φ t j) {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 5)
    (t : ℝ) {Θ : ℝ} (hΘ0 : 0 ≤ Θ) (hΘ1 : Θ ≤ 1)
    (hD : ∀ i, 1 ≤ i → i ≤ n → ∀ j, |iteratedDeriv i (fun s => φ s j) t| ≤ Θ) :
    |iteratedDeriv n (F ∘ φ) t| ≤ n.factorial * Cb * Θ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  set D : ℝ := Θ ^ ((n : ℝ)⁻¹) with hDdef
  have hD0 : 0 ≤ D := Real.rpow_nonneg hΘ0 _
  have hDn : D ^ n = Θ := by
    rw [hDdef, ← Real.rpow_natCast, ← Real.rpow_mul hΘ0, inv_mul_cancel₀ hn0.ne', Real.rpow_one]
  have h := swap_comp_le hF hFb φ hφ hn t hD0 fun i h1 h2 j => by
    refine (hD i h1 h2 j).trans ?_
    rw [hDdef, ← Real.rpow_natCast, ← Real.rpow_mul hΘ0]
    conv_lhs => rw [← Real.rpow_one Θ]
    refine Real.rpow_le_rpow_of_exponent_ge' hΘ0 hΘ1 (by positivity) ?_
    rw [inv_mul_le_iff₀ hn0, mul_one]
    exact_mod_cast h2
  rwa [hDn] at h

/-- Taylor's formula at `0` with the Lagrange remainder, the intermediate point bounded by `|y|`. -/
private lemma swap_taylor (h : ℝ → ℝ) (n : ℕ) (hh : ContDiff ℝ (n + 1) h) (y : ℝ) :
    ∃ ξ, |ξ| ≤ |y| ∧ h y = ∑ k ∈ Finset.range (n + 1), iteratedDeriv k h 0 * y ^ k / k.factorial +
      iteratedDeriv (n + 1) h ξ * y ^ (n + 1) / (n + 1).factorial := by
  by_cases hy : y = 0
  · subst hy
    refine ⟨0, by simp, ?_⟩
    rw [Finset.sum_range_succ']
    simp
  · obtain ⟨x', hx', heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (Ne.symm hy) hh.contDiffOn
    refine ⟨x', ?_, ?_⟩
    · rw [Set.uIoo, Set.mem_Ioo] at hx'
      rcases le_total 0 y with h0 | h0
      · rw [min_eq_left h0, max_eq_right h0] at hx'
        rw [abs_of_pos hx'.1, abs_of_nonneg h0]; exact hx'.2.le
      · rw [min_eq_right h0, max_eq_left h0] at hx'
        rw [abs_of_neg hx'.2, abs_of_nonpos h0]; linarith [hx'.1]
    · rw [taylor_within_apply, sub_zero] at heq
      have hk : ∀ k ∈ Finset.range (n + 1),
          ((k.factorial : ℝ)⁻¹ * y ^ k) • iteratedDerivWithin k h (Set.uIcc 0 y) 0 =
            iteratedDeriv k h 0 * y ^ k / k.factorial := by
        intro k hk
        rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (Ne.symm hy))
          (hh.contDiffAt.of_le (by
            have := Finset.mem_range.1 hk
            exact_mod_cast Nat.le_succ_of_le (Nat.lt_succ_iff.1 this))) Set.left_mem_uIcc,
          smul_eq_mul]
        ring
      rw [Finset.sum_congr rfl hk] at heq
      linarith

/-! ## Continuity and measurability in `X` -/

/-- `(X, y) ↦ G(X, y + iη)` is jointly continuous. -/
private lemma swap_continuous_G {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {η : ℝ}
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
private lemma swap_continuous_smCount {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
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
  have hG := swap_continuous_G (N := N) hSig hη
  have : Function.uncurry (fun (Xm : Matrix (Fin M) (Fin N) ℝ) (y : ℝ) =>
      (mN Sig Xm (y + η * Complex.I)).im) = fun p : Matrix (Fin M) (Fin N) ℝ × ℝ =>
        ((N : ℂ)⁻¹ * ∑ ν, G Sig p.1 ((p.2 : ℂ) + η * Complex.I) (Sum.inr ν) (Sum.inr ν)).im := by
    funext p
    rfl
  rw [this]
  refine Complex.continuous_im.comp (continuous_const.mul (continuous_finsetSum _ fun ν _ => ?_))
  exact (continuous_apply_apply _ _).comp hG

/-- `(X, t) ↦ X^{t}_{(iμ)}` is continuous. -/
private lemma swap_continuous_Xupd (i : Fin M) (μ : Fin N) :
    Continuous fun p : Matrix (Fin M) (Fin N) ℝ × ℝ => Xupd p.1 i μ p.2 := by
  refine continuous_matrix fun a b => ?_
  by_cases h : a = i ∧ b = μ
  · simpa [Xupd, h] using continuous_snd
  · have hc : Continuous fun p : Matrix (Fin M) (Fin N) ℝ × ℝ => p.1 a b :=
      (continuous_id.matrix_elem a b).comp continuous_fst
    simpa [Xupd, h] using hc

/-- Measurability of the iterated derivatives in a parameter, from the joint measurability of
the function and its smoothness in the variable. -/
private lemma swap_measurable_iteratedDeriv {α : Type*} [MeasurableSpace α] (φ : α → ℝ → ℝ)
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

/-! ## Independence -/

/-- The entry `X_{iμ}` is independent of the matrix `X^{0}_{(iμ)}` of the other entries. -/
private lemma swap_indep_entry {Ω : Type*} [MeasureSpace Ω] {C : ℕ → ℝ}
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) (i : Fin M) (μ : Fin N) :
    IndepFun (fun ω => Xupd (X ω) i μ 0) (fun ω => X ω i μ) := by
  set S : Finset (Fin M × Fin N) := Finset.univ.erase (i, μ) with hS
  set T : Finset (Fin M × Fin N) := {(i, μ)} with hT
  have hST : Disjoint S T := by
    rw [hS, hT, Finset.disjoint_singleton_right]
    exact Finset.notMem_erase _ _
  have h := hX.indep.indepFun_finset S T hST fun p => hX.measurable p.1 p.2
  set φ : (S → ℝ) → Matrix (Fin M) (Fin N) ℝ := fun v j ν =>
    if hm : (j, ν) ∈ S then v ⟨(j, ν), hm⟩ else 0 with hφ
  set ψ : (T → ℝ) → ℝ := fun v => v ⟨(i, μ), Finset.mem_singleton_self _⟩ with hψ
  have hφm : Measurable φ := by
    refine Measurable.of_eval_matrix _ fun j ν => ?_
    by_cases hm : (j, ν) ∈ S
    · simpa [hφ, hm] using measurable_pi_apply (⟨(j, ν), hm⟩ : S)
    · simp [hφ, hm]
  have hψm : Measurable ψ := measurable_pi_apply _
  have h2 := h.comp hφm hψm
  have e1 : (φ ∘ fun ω (k : S) => X ω (k : Fin M × Fin N).1 (k : Fin M × Fin N).2) =
      fun ω => Xupd (X ω) i μ 0 := by
    funext ω j ν
    change φ (fun k : S => X ω (k : Fin M × Fin N).1 (k : Fin M × Fin N).2) j ν = _
    by_cases hj : j = i ∧ ν = μ
    · obtain ⟨rfl, rfl⟩ := hj
      have hm : (j, ν) ∉ S := by simp [hS]
      simp [hφ, hm, Xupd]
    · have hm : (j, ν) ∈ S := by
        simp only [hS, Finset.mem_erase, Finset.mem_univ, and_true, ne_eq]
        exact fun h => hj ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
      simp [hφ, hm, Xupd, hj]
  have e2 : (ψ ∘ fun ω (k : T) => X ω (k : Fin M × Fin N).1 (k : Fin M × Fin N).2) =
      fun ω => X ω i μ := by
    funext ω
    rfl
  rw [e1, e2] at h2
  exact h2

/-- A random matrix with measurable entries is measurable. -/
private lemma swap_measurable_X {Ω : Type*} [MeasureSpace Ω] {C : ℕ → ℝ}
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) : Measurable X :=
  Measurable.of_eval_matrix X fun j ν => hX.measurable j ν

/-! ## Moments and the split of an integral along a good set -/

/-- `|y|^k = N^{-k/2} |√N y|^k`. -/
private lemma swap_abs_pow_eq {N : ℕ} (hN : 1 ≤ N) (y : ℝ) (k : ℕ) :
    |y| ^ k = (N : ℝ) ^ (-(k : ℝ) / 2) * |Real.sqrt N * y| ^ k := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, ← mul_assoc,
    Real.sqrt_eq_rpow, ← Real.rpow_natCast ((N : ℝ) ^ (1 / 2 : ℝ)), ← Real.rpow_mul hn.le,
    ← Real.rpow_add hn]
  have : -(k : ℝ) / 2 + 1 / 2 * k = 0 := by ring
  rw [this, Real.rpow_zero, one_mul]

/-- Integrability of `y^k` from that of `|√N y|^k`. -/
private lemma swap_integrable_pow {Ω : Type*} [MeasureSpace Ω] {N : ℕ} (hN : 1 ≤ N)
    {y : Ω → ℝ} (hy : Measurable y) {k : ℕ}
    (hi : Integrable fun ω => |Real.sqrt N * y ω| ^ k) : Integrable fun ω => y ω ^ k := by
  refine (hi.const_mul ((N : ℝ) ^ (-(k : ℝ) / 2))).mono' (hy.pow_const k).aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_pow, swap_abs_pow_eq hN]

/-- `|E y^k| ≤ N^{-k/2} C_k` when `E |√N y|^k ≤ C_k`. -/
private lemma swap_abs_integral_pow_le {Ω : Type*} [MeasureSpace Ω] {N : ℕ} (hN : 1 ≤ N)
    {y : Ω → ℝ} {k : ℕ} {Ck : ℝ}
    (hi : Integrable fun ω => |Real.sqrt N * y ω| ^ k)
    (hC : ∫ ω, |Real.sqrt N * y ω| ^ k ≤ Ck) :
    |∫ ω, y ω ^ k| ≤ (N : ℝ) ^ (-(k : ℝ) / 2) * Ck := by
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (hi.const_mul ((N : ℝ) ^ (-(k : ℝ) / 2)))
    (Eventually.of_forall fun ω => ?_)).trans ?_
  · rw [Real.norm_eq_abs, abs_pow, swap_abs_pow_eq hN]
  · rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hC (by positivity)

/-- The integral of a function bounded by `a |y|^k` on a good set and by `b |y|^k` off it, where
off the good set either `T ≥ 1` or `|√N y| > N^ε`:
`|E r| ≤ a N^{-k/2} C_k + b (N^{-k/2-pε} C_{k+p} + N^{-k/2+kε} β)` when `E T ≤ β`. -/
private lemma swap_split_integral {Ω : Type*} [MeasureSpace Ω] {N : ℕ} (hN : 1 ≤ N) {ε : ℝ}
    (C : ℕ → ℝ) {y : Ω → ℝ}
    (hmom : ∀ q : ℕ, Integrable (fun ω => |Real.sqrt N * y ω| ^ q) ∧
      ∫ ω, |Real.sqrt N * y ω| ^ q ≤ C q)
    (k p : ℕ) {T : Ω → ℝ} (hT : Integrable T) (hT0 : ∀ ω, 0 ≤ T ω) {β : ℝ}
    (hβ : ∫ ω, T ω ≤ β) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (r : Ω → ℝ)
    (hr : ∀ ω, |r ω| ≤ a * |y ω| ^ k ∨
      (|r ω| ≤ b * |y ω| ^ k ∧ (1 ≤ T ω ∨ (N : ℝ) ^ ε < |Real.sqrt N * y ω|))) :
    |∫ ω, r ω| ≤ a * ((N : ℝ) ^ (-(k : ℝ) / 2) * C k) +
      b * ((N : ℝ) ^ (-(k : ℝ) / 2 - p * ε) * C (k + p) +
        (N : ℝ) ^ (-(k : ℝ) / 2 + k * ε) * β) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set c1 : ℝ := (N : ℝ) ^ (-(k : ℝ) / 2) with hc1
  set c2 : ℝ := (N : ℝ) ^ (-(k : ℝ) / 2 - p * ε) with hc2
  set c3 : ℝ := (N : ℝ) ^ (-(k : ℝ) / 2 + k * ε) with hc3
  have hc10 : 0 ≤ c1 := by positivity
  have hc20 : 0 ≤ c2 := by positivity
  have hc30 : 0 ≤ c3 := by positivity
  set g : Ω → ℝ := fun ω => a * (c1 * |Real.sqrt N * y ω| ^ k) +
    b * (c2 * |Real.sqrt N * y ω| ^ (k + p) + c3 * T ω) with hg
  have hgi : Integrable g :=
    (((hmom k).1.const_mul c1).const_mul a).add
      ((((hmom (k + p)).1.const_mul c2).add (hT.const_mul c3)).const_mul b)
  have hpt : ∀ ω, |r ω| ≤ g ω := by
    intro ω
    have hw0 : 0 ≤ |Real.sqrt N * y ω| := abs_nonneg _
    have hyk : |y ω| ^ k = c1 * |Real.sqrt N * y ω| ^ k := swap_abs_pow_eq hN _ k
    have hA : 0 ≤ a * (c1 * |Real.sqrt N * y ω| ^ k) := by positivity
    have hB2 : 0 ≤ b * (c2 * |Real.sqrt N * y ω| ^ (k + p)) := by positivity
    have hB3 : 0 ≤ b * (c3 * T ω) := mul_nonneg hb (mul_nonneg hc30 (hT0 ω))
    rcases hr ω with h | ⟨h, hT1 | hbig⟩
    · rw [hyk] at h
      simp only [hg]
      nlinarith
    · by_cases hbig : (N : ℝ) ^ ε < |Real.sqrt N * y ω|
      · have hp : (N : ℝ) ^ (p * ε) ≤ |Real.sqrt N * y ω| ^ p := by
          rw [mul_comm, Real.rpow_mul hn.le, Real.rpow_natCast]
          exact pow_le_pow_left₀ (by positivity) hbig.le p
        have hc12 : c1 = c2 * (N : ℝ) ^ (p * ε) := by
          rw [hc1, hc2, ← Real.rpow_add hn]; congr 1; ring
        have : |y ω| ^ k ≤ c2 * |Real.sqrt N * y ω| ^ (k + p) := by
          rw [hyk, hc12, pow_add]
          have := mul_le_mul_of_nonneg_left hp (mul_nonneg hc20 (pow_nonneg hw0 k))
          nlinarith
        simp only [hg]
        nlinarith [mul_le_mul_of_nonneg_left this hb]
      · push Not at hbig
        have hk : |Real.sqrt N * y ω| ^ k ≤ (N : ℝ) ^ (k * ε) := by
          have e : (N : ℝ) ^ ((k : ℝ) * ε) = ((N : ℝ) ^ ε) ^ k := by
            rw [mul_comm, Real.rpow_mul hn.le, Real.rpow_natCast]
          rw [e]
          exact pow_le_pow_left₀ hw0 hbig k
        have hc13 : c1 * (N : ℝ) ^ (k * ε) = c3 := by
          rw [hc1, hc3, ← Real.rpow_add hn]
        have : |y ω| ^ k ≤ c3 * T ω := by
          rw [hyk]
          calc c1 * |Real.sqrt N * y ω| ^ k ≤ c1 * (N : ℝ) ^ (k * ε) :=
                mul_le_mul_of_nonneg_left hk hc10
            _ = c3 * 1 := by rw [hc13, mul_one]
            _ ≤ c3 * T ω := mul_le_mul_of_nonneg_left hT1 hc30
        simp only [hg]
        nlinarith [mul_le_mul_of_nonneg_left this hb]
    · have hp : (N : ℝ) ^ (p * ε) ≤ |Real.sqrt N * y ω| ^ p := by
        rw [mul_comm, Real.rpow_mul hn.le, Real.rpow_natCast]
        exact pow_le_pow_left₀ (by positivity) hbig.le p
      have hc12 : c1 = c2 * (N : ℝ) ^ (p * ε) := by
        rw [hc1, hc2, ← Real.rpow_add hn]; congr 1; ring
      have : |y ω| ^ k ≤ c2 * |Real.sqrt N * y ω| ^ (k + p) := by
        rw [hyk, hc12, pow_add]
        have := mul_le_mul_of_nonneg_left hp (mul_nonneg hc20 (pow_nonneg hw0 k))
        nlinarith
      simp only [hg]
      nlinarith [mul_le_mul_of_nonneg_left this hb]
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hgi (Eventually.of_forall fun ω => ?_)).trans ?_
  · rw [Real.norm_eq_abs]; exact hpt ω
  · have i1 : Integrable fun ω => a * (c1 * |Real.sqrt N * y ω| ^ k) :=
      ((hmom k).1.const_mul c1).const_mul a
    have i2 : Integrable fun ω => c2 * |Real.sqrt N * y ω| ^ (k + p) :=
      (hmom (k + p)).1.const_mul c2
    have i3 : Integrable fun ω => c3 * T ω := hT.const_mul c3
    have i23 : Integrable fun ω => c2 * |Real.sqrt N * y ω| ^ (k + p) + c3 * T ω := i2.add i3
    have e : ∫ ω, g ω = a * (c1 * ∫ ω, |Real.sqrt N * y ω| ^ k) +
        b * ((c2 * ∫ ω, |Real.sqrt N * y ω| ^ (k + p)) + c3 * ∫ ω, T ω) := by
      simp only [hg]
      rw [integral_add i1 (i23.const_mul b), integral_const_mul, integral_const_mul,
        integral_const_mul, integral_add i2 i3, integral_const_mul, integral_const_mul]
    rw [e]
    gcongr
    · exact (hmom k).2
    · exact (hmom (k + p)).2

/-- The Taylor expansion of `E f(X, y)` at `y = 0` to order three, for `y` independent of `X`
with `E y = 0` and `E y² = 1/N`: the remainder is
`f(X, y) - ∑_{k ≤ 3} ∂^k f(X, 0) y^k / k!`. -/
private lemma swap_expand {Ω α : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    [MeasurableSpace α] {N : ℕ} (hN : 1 ≤ N) (f : α → ℝ → ℝ)
    (hΦ : ∀ n ≤ 3, Measurable fun p : α × ℝ => iteratedDeriv n (f p.1) p.2) {B : ℝ}
    (hB : ∀ n ≤ 3, ∀ a s, |iteratedDeriv n (f a) s| ≤ B) {X : Ω → α} (hX : Measurable X)
    {y : Ω → ℝ} (hy : Measurable y) (hind : IndepFun X y) (h1 : ∫ ω, y ω = 0)
    (h2 : ∫ ω, y ω ^ 2 = 1 / (N : ℝ))
    (hmom : ∀ q : ℕ, Integrable fun ω => |Real.sqrt N * y ω| ^ q) :
    ∫ ω, f (X ω) (y ω) = (∫ ω, f (X ω) 0) +
      1 / (N : ℝ) / 2 * (∫ ω, iteratedDeriv 2 (f (X ω)) 0) +
      (∫ ω, y ω ^ 3) / 6 * (∫ ω, iteratedDeriv 3 (f (X ω)) 0) +
      ∫ ω, (f (X ω) (y ω) - (f (X ω) 0 + iteratedDeriv 1 (f (X ω)) 0 * y ω +
        iteratedDeriv 2 (f (X ω)) 0 * y ω ^ 2 / 2 + iteratedDeriv 3 (f (X ω)) 0 * y ω ^ 3 / 6)) := by
  have hm : ∀ n ≤ 3, Measurable fun ω => iteratedDeriv n (f (X ω)) 0 := fun n hn =>
    (hΦ n hn).comp (hX.prodMk measurable_const)
  have hbd : ∀ n ≤ 3, ∀ᵐ ω ∂(ℙ : Measure Ω), ‖iteratedDeriv n (f (X ω)) 0‖ ≤ B := fun n hn =>
    Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hB n hn _ _
  have hyk : ∀ k : ℕ, Integrable fun ω => y ω ^ k := fun k =>
    swap_integrable_pow hN hy (hmom k)
  have hg : ∀ n ≤ 3, Integrable fun ω => iteratedDeriv n (f (X ω)) 0 * y ω ^ n := fun n hn =>
    (hyk n).bdd_mul (hm n hn).aestronglyMeasurable (hbd n hn)
  have hint : ∀ n ≤ 3, ∫ ω, iteratedDeriv n (f (X ω)) 0 * y ω ^ n =
      (∫ ω, iteratedDeriv n (f (X ω)) 0) * ∫ ω, y ω ^ n := by
    intro n hn
    have hi := hind.comp (φ := fun a => iteratedDeriv n (f a) 0) (ψ := fun t => t ^ n)
      ((hΦ n hn).comp (measurable_id.prodMk measurable_const)) (measurable_id.pow_const n)
    exact hi.integral_fun_mul_eq_mul_integral (hm n hn).aestronglyMeasurable
      ((hy.pow_const n).aestronglyMeasurable)
  have hf0 : Measurable fun ω => f (X ω) (y ω) := by
    have := (hΦ 0 (by norm_num)).comp (hX.prodMk hy)
    simpa [Function.comp_def] using this
  have hfi : Integrable fun ω => f (X ω) (y ω) :=
    Integrable.of_bound hf0.aestronglyMeasurable B (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; simpa using hB 0 (by norm_num) (X ω) (y ω))
  have hg0 : Integrable fun ω => f (X ω) 0 := by
    have := hg 0 (by norm_num); simpa using this
  have hg1 := hg 1 (by norm_num)
  have hg2 := (hg 2 (by norm_num)).div_const 2
  have hg3 := (hg 3 (by norm_num)).div_const 6
  simp only [pow_one] at hg1
  have hS : Integrable fun ω => f (X ω) 0 + iteratedDeriv 1 (f (X ω)) 0 * y ω +
      iteratedDeriv 2 (f (X ω)) 0 * y ω ^ 2 / 2 + iteratedDeriv 3 (f (X ω)) 0 * y ω ^ 3 / 6 :=
    ((hg0.add hg1).add hg2).add hg3
  have hA : Integrable fun ω => f (X ω) 0 + iteratedDeriv 1 (f (X ω)) 0 * y ω := hg0.add hg1
  have hA2 : Integrable fun ω => f (X ω) 0 + iteratedDeriv 1 (f (X ω)) 0 * y ω +
      iteratedDeriv 2 (f (X ω)) 0 * y ω ^ 2 / 2 := hA.add hg2
  rw [integral_sub hfi hS, integral_add hA2 hg3, integral_add hA hg2, integral_add hg0 hg1,
    integral_div, integral_div]
  have i1 := hint 1 (by norm_num)
  have i2 := hint 2 (by norm_num)
  have i3 := hint 3 (by norm_num)
  simp only [pow_one] at i1
  rw [i1, i2, i3, h1, h2]
  ring

/-! ## Constants of the model and the exponent bookkeeping -/

/-- `‖Σ‖ ≤ τ⁻¹` under (bound_Sigma) (L2 operator norm). -/
private lemma swap_norm_sig_le {τ : ℝ} (hτ : 0 < τ) {Sig : Matrix (Fin M) (Fin M) ℝ}
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
private lemma swap_edgeVal_le {Ω : Type*} [MeasureSpace Ω] {τ : ℝ} {C : ℕ → ℝ}
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
private lemma swap_ev_small {y : ℝ} (hy : y < 0) (c : ℝ) :
    ∀ᶠ N : ℕ in atTop, c * (N : ℝ) ^ y ≤ 1 / 2 := by
  have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ y) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (y := -y) (by linarith)).comp tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using this
  have h2 : Tendsto (fun N : ℕ => c * (N : ℝ) ^ y) atTop (𝓝 0) := by
    simpa using h1.const_mul c
  exact (h2.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono fun _ h => h.le

/-- `N^x ≤ N^y` for `x ≤ y`, `N ≥ 1`. -/
private lemma swap_rpow_le {N : ℕ} (hN : 1 ≤ N) {x y : ℝ} (h : x ≤ y) :
    (N : ℝ) ^ x ≤ (N : ℝ) ^ y :=
  Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) h

/-- The exponent bookkeeping of the swap: the sum of the remainder, tail and coefficient-move
bounds is at most `K C_b N^{-7/3+20ε}`. -/
private lemma swap_final_arith {N : ℕ} (hN : 1 ≤ N) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200)
    {p : ℕ} (hp : 8 ≤ (p : ℝ) * ε) {Cb cΘ A c2 c3 c4 c2p c4p cp L : ℝ} (hCb : 0 ≤ Cb)
    (hcΘ : 0 ≤ cΘ) (hA : 0 ≤ A) (hc2 : 0 ≤ c2) (hc3 : 0 ≤ c3) (hc4 : 0 ≤ c4) (hc2p : 0 ≤ c2p)
    (hc4p : 0 ≤ c4p) (hcp : 0 ≤ cp) (hL : 0 ≤ L) :
    2 * (Cb * (cΘ * (N : ℝ) ^ (-1 / 3 + 10 * ε)) * ((N : ℝ) ^ (-(4 : ℝ) / 2) * c4) +
        Cb * (384 * (A * (N : ℝ) ^ (4 / 3 + 18 * ε))) ^ 4 *
          ((N : ℝ) ^ (-(4 : ℝ) / 2 - p * ε) * c4p +
            (N : ℝ) ^ (-(4 : ℝ) / 2 + 4 * ε) * (2 * L * (N : ℝ) ^ (-(8 : ℝ)) +
              (N : ℝ) ^ (-((p : ℝ) * ε)) * cp))) +
      2 * ((N : ℝ) ^ (-(3 : ℝ) / 2) * c3) / 6 *
        (60 * Cb * ((N : ℝ) ^ (-(2 : ℝ) / 2) * c2) +
          60 * Cb * (384 * (A * (N : ℝ) ^ (4 / 3 + 18 * ε))) ^ 5 *
            ((N : ℝ) ^ (-(2 : ℝ) / 2 - p * ε) * c2p +
              (N : ℝ) ^ (-(2 : ℝ) / 2 + 2 * ε) * (2 * L * (N : ℝ) ^ (-(8 : ℝ))))) ≤
      (2 * (cΘ * c4 + 384 ^ 4 * A ^ 4 * (c4p + 2 * L + cp)) +
        c3 / 3 * (60 * c2 + 60 * 384 ^ 5 * A ^ 5 * (c2p + 2 * L))) * Cb *
          (N : ℝ) ^ (-7 / 3 + 20 * ε) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  set P : ℝ := (N : ℝ) ^ (-7 / 3 + 20 * ε) with hP
  have hP0 : 0 ≤ P := by positivity
  have hW4 : (384 * (A * (N : ℝ) ^ (4 / 3 + 18 * ε))) ^ 4 =
      384 ^ 4 * A ^ 4 * (N : ℝ) ^ (16 / 3 + 72 * ε) := by
    rw [mul_pow, mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ (4 / 3 + 18 * ε)), ← Real.rpow_mul hn.le]
    ring_nf
  have hW5 : (384 * (A * (N : ℝ) ^ (4 / 3 + 18 * ε))) ^ 5 =
      384 ^ 5 * A ^ 5 * (N : ℝ) ^ (20 / 3 + 90 * ε) := by
    rw [mul_pow, mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ (4 / 3 + 18 * ε)), ← Real.rpow_mul hn.le]
    ring_nf
  have r2 : ∀ x y : ℝ, (N : ℝ) ^ x * (N : ℝ) ^ y = (N : ℝ) ^ (x + y) := fun x y =>
    (Real.rpow_add hn x y).symm
  have e1 : (N : ℝ) ^ (-1 / 3 + 10 * ε) * (N : ℝ) ^ (-(4 : ℝ) / 2) ≤ P := by
    rw [r2]; exact swap_rpow_le hN (by linarith)
  have e2 : (N : ℝ) ^ (16 / 3 + 72 * ε) * (N : ℝ) ^ (-(4 : ℝ) / 2 - p * ε) ≤ P := by
    rw [r2]; exact swap_rpow_le hN (by linarith)
  have e3 : (N : ℝ) ^ (16 / 3 + 72 * ε) * ((N : ℝ) ^ (-(4 : ℝ) / 2 + 4 * ε) *
      (N : ℝ) ^ (-(8 : ℝ))) ≤ P := by
    rw [r2, r2]; exact swap_rpow_le hN (by linarith)
  have e4 : (N : ℝ) ^ (16 / 3 + 72 * ε) * ((N : ℝ) ^ (-(4 : ℝ) / 2 + 4 * ε) *
      (N : ℝ) ^ (-((p : ℝ) * ε))) ≤ P := by
    rw [r2, r2]; exact swap_rpow_le hN (by linarith)
  have e5 : (N : ℝ) ^ (-(3 : ℝ) / 2) * (N : ℝ) ^ (-(2 : ℝ) / 2) ≤ P := by
    rw [r2]; exact swap_rpow_le hN (by linarith)
  have e6 : (N : ℝ) ^ (-(3 : ℝ) / 2) * ((N : ℝ) ^ (20 / 3 + 90 * ε) *
      (N : ℝ) ^ (-(2 : ℝ) / 2 - p * ε)) ≤ P := by
    rw [r2, r2]; exact swap_rpow_le hN (by linarith)
  have e7 : (N : ℝ) ^ (-(3 : ℝ) / 2) * ((N : ℝ) ^ (20 / 3 + 90 * ε) *
      ((N : ℝ) ^ (-(2 : ℝ) / 2 + 2 * ε) * (N : ℝ) ^ (-(8 : ℝ)))) ≤ P := by
    rw [r2, r2, r2]; exact swap_rpow_le hN (by linarith)
  rw [hW4, hW5]
  have expand : 2 * (Cb * (cΘ * (N : ℝ) ^ (-1 / 3 + 10 * ε)) * ((N : ℝ) ^ (-(4 : ℝ) / 2) * c4) +
        Cb * (384 ^ 4 * A ^ 4 * (N : ℝ) ^ (16 / 3 + 72 * ε)) *
          ((N : ℝ) ^ (-(4 : ℝ) / 2 - p * ε) * c4p +
            (N : ℝ) ^ (-(4 : ℝ) / 2 + 4 * ε) * (2 * L * (N : ℝ) ^ (-(8 : ℝ)) +
              (N : ℝ) ^ (-((p : ℝ) * ε)) * cp))) +
      2 * ((N : ℝ) ^ (-(3 : ℝ) / 2) * c3) / 6 *
        (60 * Cb * ((N : ℝ) ^ (-(2 : ℝ) / 2) * c2) +
          60 * Cb * (384 ^ 5 * A ^ 5 * (N : ℝ) ^ (20 / 3 + 90 * ε)) *
            ((N : ℝ) ^ (-(2 : ℝ) / 2 - p * ε) * c2p +
              (N : ℝ) ^ (-(2 : ℝ) / 2 + 2 * ε) * (2 * L * (N : ℝ) ^ (-(8 : ℝ))))) =
      Cb * (2 * (cΘ * c4) * ((N : ℝ) ^ (-1 / 3 + 10 * ε) * (N : ℝ) ^ (-(4 : ℝ) / 2)) +
        2 * (384 ^ 4 * A ^ 4) * (c4p * ((N : ℝ) ^ (16 / 3 + 72 * ε) *
          (N : ℝ) ^ (-(4 : ℝ) / 2 - p * ε)) +
          2 * L * ((N : ℝ) ^ (16 / 3 + 72 * ε) * ((N : ℝ) ^ (-(4 : ℝ) / 2 + 4 * ε) *
            (N : ℝ) ^ (-(8 : ℝ)))) +
          cp * ((N : ℝ) ^ (16 / 3 + 72 * ε) * ((N : ℝ) ^ (-(4 : ℝ) / 2 + 4 * ε) *
            (N : ℝ) ^ (-((p : ℝ) * ε))))) +
        c3 / 3 * (60 * c2 * ((N : ℝ) ^ (-(3 : ℝ) / 2) * (N : ℝ) ^ (-(2 : ℝ) / 2)) +
          60 * (384 ^ 5 * A ^ 5) * (c2p * ((N : ℝ) ^ (-(3 : ℝ) / 2) *
            ((N : ℝ) ^ (20 / 3 + 90 * ε) * (N : ℝ) ^ (-(2 : ℝ) / 2 - p * ε))) +
            2 * L * ((N : ℝ) ^ (-(3 : ℝ) / 2) * ((N : ℝ) ^ (20 / 3 + 90 * ε) *
              ((N : ℝ) ^ (-(2 : ℝ) / 2 + 2 * ε) * (N : ℝ) ^ (-(8 : ℝ)))))))) := by
    ring
  rw [expand]
  have hA4 : 0 ≤ 384 ^ 4 * A ^ 4 := by positivity
  have hA5 : 0 ≤ 384 ^ 5 * A ^ 5 := by positivity
  calc _ ≤ Cb * (2 * (cΘ * c4) * P + 2 * (384 ^ 4 * A ^ 4) * (c4p * P + 2 * L * P + cp * P) +
        c3 / 3 * (60 * c2 * P + 60 * (384 ^ 5 * A ^ 5) * (c2p * P + 2 * L * P))) := by
        gcongr
    _ = _ := by ring

private lemma swap_iteratedDeriv_iteratedDeriv (g : ℝ → ℝ) (a b : ℕ) :
    iteratedDeriv a (iteratedDeriv b g) = iteratedDeriv (a + b) g := by
  simp only [iteratedDeriv_eq_iterate]
  funext x
  rw [Function.iterate_add_apply]

/-- `|√N z| ≤ N^ε` gives `|z| ≤ N^{-1/2+ε}`. -/
private lemma swap_abs_le_of_sqrt {N : ℕ} (hN : 1 ≤ N) {ε z : ℝ}
    (h : |Real.sqrt N * z| ≤ (N : ℝ) ^ ε) : |z| ≤ (N : ℝ) ^ (-1 / 2 + ε) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hn
  rw [abs_mul, abs_of_pos hs] at h
  have e : (N : ℝ) ^ (-1 / 2 + ε) = (N : ℝ) ^ ε / Real.sqrt N := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hn]; congr 1; ring
  rw [e, le_div_iff₀ hs, mul_comm]
  exact h

/-- `|√N z|^p N^{-pε} ≥ 1` when `|√N z| > N^ε`. -/
private lemma swap_markov_one {N : ℕ} (hN : 1 ≤ N) {ε z : ℝ} (p : ℕ)
    (h : (N : ℝ) ^ ε < |Real.sqrt N * z|) :
    1 ≤ |Real.sqrt N * z| ^ p * (N : ℝ) ^ (-((p : ℝ) * ε)) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : (N : ℝ) ^ ((p : ℝ) * ε) ≤ |Real.sqrt N * z| ^ p := by
    have e : (N : ℝ) ^ ((p : ℝ) * ε) = ((N : ℝ) ^ ε) ^ p := by
      rw [mul_comm, Real.rpow_mul hn.le, Real.rpow_natCast]
    rw [e]
    exact pow_le_pow_left₀ (by positivity) h.le p
  rw [Real.rpow_neg hn.le]
  have hpos : 0 < (N : ℝ) ^ ((p : ℝ) * ε) := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos, one_mul]
  exact hp

/-- The Taylor remainder at order four of `E f(X, y)`: on the good event (`X` good,
`|√N X_α|, |√N y| ≤ N^ε`) `|∂⁴ f| ≤ 24 C_b Θ`, and everywhere `|∂⁴ f| ≤ 24 C_b D⁴`. -/
private lemma swap_remainder {Ω α : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {N : ℕ} (hN : 1 ≤ N) {ε : ℝ} (C : ℕ → ℝ) (p : ℕ) (f : α → ℝ → ℝ)
    (hfc : ∀ a, ContDiff ℝ 5 (f a)) {Cb D Θ β : ℝ} (hCb : 0 ≤ Cb) (hΘ : 0 ≤ Θ)
    (Good : α → Prop) (xα : α → ℝ)
    (hcrude : ∀ a s, |iteratedDeriv 4 (f a) s| ≤ 24 * Cb * D ^ 4)
    (hgood : ∀ a s, Good a → |xα a| ≤ (N : ℝ) ^ (-1 / 2 + ε) → |s| ≤ (N : ℝ) ^ (-1 / 2 + ε) →
      |iteratedDeriv 4 (f a) s| ≤ 24 * Cb * Θ)
    (X : Ω → α) {y : Ω → ℝ}
    (hmom : ∀ q : ℕ, Integrable (fun ω => |Real.sqrt N * y ω| ^ q) ∧
      ∫ ω, |Real.sqrt N * y ω| ^ q ≤ C q)
    (hmomX : ∀ q : ℕ, Integrable (fun ω => |Real.sqrt N * xα (X ω)| ^ q) ∧
      ∫ ω, |Real.sqrt N * xα (X ω)| ^ q ≤ C q)
    {TX : Ω → ℝ} (hTX0 : ∀ ω, 0 ≤ TX ω) (hTXi : Integrable TX) (hTXint : ∫ ω, TX ω ≤ β)
    (hTX1 : ∀ ω, Good (X ω) ∨ 1 ≤ TX ω) :
    |∫ ω, (f (X ω) (y ω) - (f (X ω) 0 + iteratedDeriv 1 (f (X ω)) 0 * y ω +
        iteratedDeriv 2 (f (X ω)) 0 * y ω ^ 2 / 2 + iteratedDeriv 3 (f (X ω)) 0 * y ω ^ 3 / 6))| ≤
      Cb * Θ * ((N : ℝ) ^ (-(4 : ℝ) / 2) * C 4) +
        Cb * D ^ 4 * ((N : ℝ) ^ (-(4 : ℝ) / 2 - p * ε) * C (4 + p) +
          (N : ℝ) ^ (-(4 : ℝ) / 2 + 4 * ε) * (β + (N : ℝ) ^ (-((p : ℝ) * ε)) * C p)) := by
  set T : Ω → ℝ := fun ω => TX ω + |Real.sqrt N * xα (X ω)| ^ p * (N : ℝ) ^ (-((p : ℝ) * ε))
    with hT
  have hTi : Integrable T := hTXi.add ((hmomX p).1.mul_const _)
  have hT0 : ∀ ω, 0 ≤ T ω := fun ω => add_nonneg (hTX0 ω) (by positivity)
  have hTint : ∫ ω, T ω ≤ β + (N : ℝ) ^ (-((p : ℝ) * ε)) * C p := by
    simp only [hT]
    rw [integral_add hTXi ((hmomX p).1.mul_const _), integral_mul_const]
    have hpos : 0 ≤ (N : ℝ) ^ (-((p : ℝ) * ε)) := by positivity
    nlinarith [(hmomX p).2]
  have h := swap_split_integral hN (ε := ε) C hmom 4 p hTi hT0 hTint (a := Cb * Θ) (b := Cb * D ^ 4)
    (by positivity) (by positivity) (fun ω => f (X ω) (y ω) - (f (X ω) 0 +
      iteratedDeriv 1 (f (X ω)) 0 * y ω + iteratedDeriv 2 (f (X ω)) 0 * y ω ^ 2 / 2 +
      iteratedDeriv 3 (f (X ω)) 0 * y ω ^ 3 / 6)) fun ω => ?_
  · refine h.trans (le_of_eq ?_)
    push_cast
    ring
  obtain ⟨ξ, hξ, heq⟩ := swap_taylor (f (X ω)) 3 ((hfc (X ω)).of_le (by norm_num)) (y ω)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
    iteratedDeriv_zero, Nat.factorial, Nat.cast_one, div_one, mul_one] at heq
  have hr : f (X ω) (y ω) - (f (X ω) 0 + iteratedDeriv 1 (f (X ω)) 0 * y ω +
      iteratedDeriv 2 (f (X ω)) 0 * y ω ^ 2 / 2 + iteratedDeriv 3 (f (X ω)) 0 * y ω ^ 3 / 6) =
      iteratedDeriv 4 (f (X ω)) ξ * y ω ^ 4 / 24 := by
    rw [heq]; push_cast; ring
  rw [hr, abs_div, abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 24)]
  have hy4 : 0 ≤ |y ω| ^ 4 := by positivity
  by_cases hg : Good (X ω) ∧ |Real.sqrt N * xα (X ω)| ≤ (N : ℝ) ^ ε ∧
      |Real.sqrt N * y ω| ≤ (N : ℝ) ^ ε
  · left
    have hb := hgood (X ω) ξ hg.1 (swap_abs_le_of_sqrt hN hg.2.1)
      (hξ.trans (swap_abs_le_of_sqrt hN hg.2.2))
    calc |iteratedDeriv 4 (f (X ω)) ξ| * |y ω| ^ 4 / 24 ≤ 24 * Cb * Θ * |y ω| ^ 4 / 24 := by
          gcongr
      _ = Cb * Θ * |y ω| ^ 4 := by ring
  · right
    refine ⟨?_, ?_⟩
    · calc |iteratedDeriv 4 (f (X ω)) ξ| * |y ω| ^ 4 / 24 ≤ 24 * Cb * D ^ 4 * |y ω| ^ 4 / 24 := by
            gcongr
            exact hcrude _ _
        _ = Cb * D ^ 4 * |y ω| ^ 4 := by ring
    · by_cases h1 : Good (X ω)
      · by_cases h2 : |Real.sqrt N * xα (X ω)| ≤ (N : ℝ) ^ ε
        · right
          push Not at hg
          exact hg h1 h2
        · left
          push Not at h2
          have := swap_markov_one hN p h2
          simp only [hT]
          linarith [hTX0 ω]
      · left
        rcases hTX1 ω with h | h
        · exact absurd h h1
        · simp only [hT]
          have : 0 ≤ |Real.sqrt N * xα (X ω)| ^ p * (N : ℝ) ^ (-((p : ℝ) * ε)) := by positivity
          linarith

/-- Moving the order-three coefficient from `X^{0}_{(iμ)}` to `X`: with `E[∂⁴f(X, 0) X_α] = 0`,
`E ∂³f(X, X_α) = E ∂³f(X, 0) + E R'`, where `|R'| ≤ 60 C_b X_α²` on the good event and
`|R'| ≤ 60 C_b D⁵ X_α²` everywhere. -/
private lemma swap_coef {Ω α : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    [MeasurableSpace α] {N : ℕ} (hN : 1 ≤ N) {ε : ℝ} (C : ℕ → ℝ) (p : ℕ) (f : α → ℝ → ℝ)
    (hfc : ∀ a, ContDiff ℝ 5 (f a))
    (hΦ : ∀ n ≤ 5, Measurable fun q : α × ℝ => iteratedDeriv n (f q.1) q.2)
    {Cb D β : ℝ} (hCb : 0 ≤ Cb) (hD : 0 ≤ D) (Good : α → Prop) (xα : α → ℝ)
    (hcrude : ∀ n ≤ 5, ∀ a s, |iteratedDeriv n (f a) s| ≤ n.factorial * Cb * D ^ n)
    (hgood : ∀ a s, Good a → |xα a| ≤ (N : ℝ) ^ (-1 / 2 + ε) → |s| ≤ (N : ℝ) ^ (-1 / 2 + ε) →
      |iteratedDeriv 5 (f a) s| ≤ 120 * Cb)
    {X : Ω → α} (hX : Measurable X) (hxα : Measurable fun ω => xα (X ω))
    (hind : IndepFun (fun ω => iteratedDeriv 4 (f (X ω)) 0) (fun ω => xα (X ω)))
    (hmean : ∫ ω, xα (X ω) = 0)
    (hmomX : ∀ q : ℕ, Integrable (fun ω => |Real.sqrt N * xα (X ω)| ^ q) ∧
      ∫ ω, |Real.sqrt N * xα (X ω)| ^ q ≤ C q)
    {TX : Ω → ℝ} (hTX0 : ∀ ω, 0 ≤ TX ω) (hTXi : Integrable TX) (hTXint : ∫ ω, TX ω ≤ β)
    (hTX1 : ∀ ω, Good (X ω) ∨ 1 ≤ TX ω) :
    ∫ ω, iteratedDeriv 3 (f (X ω)) (xα (X ω)) = (∫ ω, iteratedDeriv 3 (f (X ω)) 0) +
        ∫ ω, (iteratedDeriv 3 (f (X ω)) (xα (X ω)) - iteratedDeriv 3 (f (X ω)) 0 -
          iteratedDeriv 4 (f (X ω)) 0 * xα (X ω)) ∧
      |∫ ω, (iteratedDeriv 3 (f (X ω)) (xα (X ω)) - iteratedDeriv 3 (f (X ω)) 0 -
          iteratedDeriv 4 (f (X ω)) 0 * xα (X ω))| ≤
        60 * Cb * ((N : ℝ) ^ (-(2 : ℝ) / 2) * C 2) +
          60 * Cb * D ^ 5 * ((N : ℝ) ^ (-(2 : ℝ) / 2 - p * ε) * C (2 + p) +
            (N : ℝ) ^ (-(2 : ℝ) / 2 + 2 * ε) * β) := by
  have hbd : ∀ n ≤ 5, ∀ᵐ ω ∂(ℙ : Measure Ω), ∀ s, ‖iteratedDeriv n (f (X ω)) s‖ ≤
      n.factorial * Cb * D ^ n := fun n hn =>
    Eventually.of_forall fun ω s => by rw [Real.norm_eq_abs]; exact hcrude n hn _ _
  have hm3a : Measurable fun ω => iteratedDeriv 3 (f (X ω)) (xα (X ω)) := by
    have h := (hΦ 3 (by norm_num)).comp (hX.prodMk hxα)
    exact h
  have hm30 : Measurable fun ω => iteratedDeriv 3 (f (X ω)) 0 := by
    have h := (hΦ 3 (by norm_num)).comp (hX.prodMk (measurable_const (a := (0 : ℝ))))
    exact h
  have hm40 : Measurable fun ω => iteratedDeriv 4 (f (X ω)) 0 := by
    have h := (hΦ 4 (by norm_num)).comp (hX.prodMk (measurable_const (a := (0 : ℝ))))
    exact h
  have hi3a : Integrable fun ω => iteratedDeriv 3 (f (X ω)) (xα (X ω)) :=
    Integrable.of_bound hm3a.aestronglyMeasurable _
      ((hbd 3 (by norm_num)).mono fun ω h => h _)
  have hi30 : Integrable fun ω => iteratedDeriv 3 (f (X ω)) 0 :=
    Integrable.of_bound hm30.aestronglyMeasurable _
      ((hbd 3 (by norm_num)).mono fun ω h => h _)
  have hxi : Integrable fun ω => xα (X ω) := by
    have := swap_integrable_pow hN hxα (k := 1) (hmomX 1).1
    simpa using this
  have hi4 : Integrable fun ω => iteratedDeriv 4 (f (X ω)) 0 * xα (X ω) :=
    hxi.bdd_mul hm40.aestronglyMeasurable ((hbd 4 (by norm_num)).mono fun ω h => h _)
  have h40 : ∫ ω, iteratedDeriv 4 (f (X ω)) 0 * xα (X ω) = 0 := by
    rw [hind.integral_fun_mul_eq_mul_integral hm40.aestronglyMeasurable hxα.aestronglyMeasurable]
    change (∫ ω, iteratedDeriv 4 (f (X ω)) 0) * ∫ ω, xα (X ω) = 0
    rw [hmean, mul_zero]
  refine ⟨?_, ?_⟩
  · have h' : Integrable fun ω => iteratedDeriv 3 (f (X ω)) (xα (X ω)) -
        iteratedDeriv 3 (f (X ω)) 0 := hi3a.sub hi30
    rw [integral_sub h' hi4, integral_sub hi3a hi30, h40]
    ring
  · refine (swap_split_integral hN (ε := ε) C hmomX 2 p hTXi hTX0 hTXint (a := 60 * Cb)
      (b := 60 * Cb * D ^ 5) (by positivity) (by positivity)
      (fun ω => iteratedDeriv 3 (f (X ω)) (xα (X ω)) - iteratedDeriv 3 (f (X ω)) 0 -
        iteratedDeriv 4 (f (X ω)) 0 * xα (X ω)) fun ω => ?_).trans (le_of_eq ?_)
    · have hc2 : ContDiff ℝ 2 (iteratedDeriv 3 (f (X ω))) := by
        rw [iteratedDeriv_eq_iterate]
        exact ContDiff.iterate_deriv' 2 3 (by simpa using hfc (X ω))
      obtain ⟨ξ, hξ, heq⟩ := swap_taylor (iteratedDeriv 3 (f (X ω))) 1 (hc2.of_le (by norm_num))
        (xα (X ω))
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
        Nat.factorial, Nat.cast_one, div_one, mul_one, swap_iteratedDeriv_iteratedDeriv] at heq
      have hr : iteratedDeriv 3 (f (X ω)) (xα (X ω)) - iteratedDeriv 3 (f (X ω)) 0 -
          iteratedDeriv 4 (f (X ω)) 0 * xα (X ω) =
          iteratedDeriv 5 (f (X ω)) ξ * xα (X ω) ^ 2 / 2 := by
        rw [heq]; push_cast; ring_nf
      rw [hr, abs_div, abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      by_cases hg : Good (X ω) ∧ |Real.sqrt N * xα (X ω)| ≤ (N : ℝ) ^ ε
      · left
        have hs := swap_abs_le_of_sqrt hN hg.2
        have hb := hgood (X ω) ξ hg.1 hs (hξ.trans hs)
        calc |iteratedDeriv 5 (f (X ω)) ξ| * |xα (X ω)| ^ 2 / 2 ≤ 120 * Cb * |xα (X ω)| ^ 2 / 2 := by
              gcongr
          _ = 60 * Cb * |xα (X ω)| ^ 2 := by ring
      · right
        refine ⟨?_, ?_⟩
        · have hc := hcrude 5 le_rfl (X ω) ξ
          calc |iteratedDeriv 5 (f (X ω)) ξ| * |xα (X ω)| ^ 2 / 2 ≤
                (Nat.factorial 5 : ℝ) * Cb * D ^ 5 * |xα (X ω)| ^ 2 / 2 := by gcongr
            _ = 60 * Cb * D ^ 5 * |xα (X ω)| ^ 2 := by norm_num [Nat.factorial]; ring
        · by_cases h1 : Good (X ω)
          · right
            push Not at hg
            exact hg h1
          · left
            rcases hTX1 ω with h | h
            · exact absurd h h1
            · exact h
    · push_cast
      ring

/-- Union bound for finitely many events of probability `≥ 1 - q`: a nonnegative integrable
`T` with `E T ≤ 2 l q` such that at every point either all events hold or `T ≥ 1`. -/
private lemma swap_events {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {l : ℕ} (P : Fin l → Bool → Set Ω) {q : ℝ} (hq : 0 ≤ q)
    (hP : ∀ j b, (ℙ : Measure Ω) (P j b)ᶜ ≤ ENNReal.ofReal q) :
    ∃ T : Ω → ℝ, (∀ ω, 0 ≤ T ω) ∧ Integrable T ∧ ∫ ω, T ω ≤ 2 * l * q ∧
      ∀ ω, (∀ j b, ω ∈ P j b) ∨ 1 ≤ T ω := by
  set Q : Fin l × Bool → Set Ω := fun jb => toMeasurable (ℙ : Measure Ω) (P jb.1 jb.2)ᶜ with hQ
  have hQm : ∀ jb, MeasurableSet (Q jb) := fun jb => measurableSet_toMeasurable _ _
  have hind0 : ∀ jb ω, 0 ≤ (Q jb).indicator (1 : Ω → ℝ) ω := fun jb ω =>
    Set.indicator_nonneg (fun _ _ => zero_le_one) ω
  have hindi : ∀ jb ∈ (Finset.univ : Finset (Fin l × Bool)),
      Integrable ((Q jb).indicator (1 : Ω → ℝ)) := fun jb _ =>
    (integrable_const (1 : ℝ)).indicator (hQm jb)
  refine ⟨fun ω => ∑ jb, (Q jb).indicator 1 ω, fun ω => Finset.sum_nonneg fun jb _ => hind0 jb ω,
    integrable_finsetSum _ hindi, ?_, fun ω => ?_⟩
  · rw [integral_finsetSum _ hindi]
    calc ∑ jb, ∫ ω, (Q jb).indicator (1 : Ω → ℝ) ω = ∑ jb, (ℙ : Measure Ω).real (Q jb) :=
          Finset.sum_congr rfl fun jb _ => integral_indicator_one (hQm jb)
      _ ≤ ∑ _jb : Fin l × Bool, q := Finset.sum_le_sum fun jb _ => by
          rw [measureReal_def, hQ, measure_toMeasurable]
          exact ENNReal.toReal_le_of_le_ofReal hq (hP _ _)
      _ = 2 * l * q := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            Fintype.card_bool, nsmul_eq_mul]
          push_cast; ring
  · by_cases h : ∀ j b, ω ∈ P j b
    · exact Or.inl h
    · right
      push Not at h
      obtain ⟨j, b, hjb⟩ := h
      have hmem : ω ∈ Q (j, b) := subset_toMeasurable _ _ hjb
      have h1 : (Q (j, b)).indicator (1 : Ω → ℝ) ω = 1 := by
        rw [Set.indicator_of_mem hmem, Pi.one_apply]
      have hle := Finset.single_le_sum (f := fun jb => (Q jb).indicator (1 : Ω → ℝ) ω)
        (fun jb _ => hind0 jb ω) (Finset.mem_univ (j, b))
      linarith

/-- The deterministic bound `|∂ⁿ f| ≤ n! C_b (384 W)^n`, `n ≤ 5`, for `f(t) = F(𝒳(X^{t}_{(iμ)}))`,
from `|G_{ab}| ≤ W` at all window points, uniformly in `X`. -/
private lemma swap_crude {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {η : ℝ}
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
  refine swap_comp_le hF hFb (fun t j => smCount (QN Sig (Xupd Xm i μ t)) η (Ea j) (Eb j))
    hgvc hn s (by positivity) fun i' h1 h2 j => ?_
  obtain ⟨n', rfl⟩ : ∃ n', i' = n' + 1 := ⟨i' - 1, by omega⟩
  exact swap_deriv_le_crude hSig Xm hη (Ea j) (Eb j) i μ s hW1
    (fun a b => (hGW _ j a b).1) (fun a b => (hGW _ j a b).2) (by omega)

/-- The bound `|∂ⁿ f| ≤ n! C_b Θ`, `1 ≤ n ≤ 5`, at `X^{s}_{(iμ)}`, `|X_{iμ}|, |s| ≤ r`, when the
`J × J` entries of `G` at `X` are within `δ ≤ 1` of `Π(m)` at all window points and the
constants satisfy the stability and smallness conditions. -/
private lemma swap_good {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {η : ℝ}
    (hη : 0 < η) {l : ℕ} {F : (Fin l → ℝ) → ℝ} {Cb : ℝ} (hF : ContDiff ℝ 5 F)
    (hFb : ∀ m ≤ 5, ∀ x, ‖iteratedFDeriv ℝ m F x‖ ≤ Cb) (Ea Eb : Fin l → ℝ) (i : Fin M)
    (μ : Fin N) (ma mb : Fin l → ℂ) (δa δb : Fin l → ℝ) {K r θ κ₀ Θ : ℝ}
    (hP : ∀ j a b, ‖piMat (N := N) Sig (ma j) a b‖ ≤ K ∧ ‖piMat (N := N) Sig (mb j) a b‖ ≤ K)
    (hδ1 : ∀ j, δa j ≤ 1 ∧ δb j ≤ 1)
    (hθ : ∀ j, δa j + 4 * (K + 1) ^ 2 * (2 * r) ≤ θ ∧ δb j + 4 * (K + 1) ^ 2 * (2 * r) ≤ θ)
    (hθ1 : θ ≤ 1) (hd : 2 * (K + 1) * (2 * r) ≤ 1 / 2)
    (hmp : ∀ j, ‖mb j * piMat (N := N) Sig (mb j) (Sum.inl i) (Sum.inl i) -
      ma j * piMat (N := N) Sig (ma j) (Sum.inl i) (Sum.inl i)‖ ≤ κ₀)
    (hΘ : 24 * (8 * (K + 1)) ^ 5 * (4 * θ + (2 * (2 * K + 1) * θ + κ₀)) ≤ Θ) (hΘ0 : 0 ≤ Θ)
    (hΘ1 : Θ ≤ 1) (Xm : Matrix (Fin M) (Fin N) ℝ) (s : ℝ)
    (hG : ∀ j,
      (∀ a ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
        ∀ b ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
          ‖G Sig Xm ((Ea j : ℂ) + η * Complex.I) a b - piMat Sig (ma j) a b‖ ≤ δa j) ∧
      (∀ a ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
        ∀ b ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
          ‖G Sig Xm ((Eb j : ℂ) + η * Complex.I) a b - piMat Sig (mb j) a b‖ ≤ δb j))
    (hX : |Xm i μ| ≤ r) (hs : |s| ≤ r) {n : ℕ} (hn1 : 1 ≤ n) (hn5 : n ≤ 5) :
    |iteratedDeriv n (fun t => smF F Sig (Xupd Xm i μ t) η Ea Eb) s| ≤ n.factorial * Cb * Θ := by
  have hgvc : ∀ (j : Fin l) (n : ℕ), ContDiff ℝ n fun t =>
      smCount (QN Sig (Xupd Xm i μ t)) η (Ea j) (Eb j) := fun j n =>
    derivative_contDiff_smCount hSig Xm hη (Ea j) (Eb j) i μ n
  refine swap_comp_le_small hF hFb (fun t j => smCount (QN Sig (Xupd Xm i μ t)) η (Ea j) (Eb j))
    hgvc hn1 hn5 s hΘ0 hΘ1 fun i' h1 h2 j => ?_
  obtain ⟨n', rfl⟩ : ∃ n', i' = n' + 1 := ⟨i' - 1, by omega⟩
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hP j (Sum.inl i) (Sum.inl i)).1
  have hdiff : |Xm i μ - s| ≤ 2 * r := by
    have := abs_sub (Xm i μ) s
    linarith
  have hd' : 2 * (K + 1) * |Xm i μ - s| ≤ 1 / 2 :=
    le_trans (mul_le_mul_of_nonneg_left hdiff (by positivity)) hd
  have hst : 4 * (K + 1) ^ 2 * |Xm i μ - s| ≤ 4 * (K + 1) ^ 2 * (2 * r) :=
    mul_le_mul_of_nonneg_left hdiff (by positivity)
  exact (swap_deriv_le_pair hSig Xm hη (Ea j) (Eb j) i μ s (hG j).1 (hG j).2
    (fun a b => (hP j a b).1) (fun a b => (hP j a b).2) (hδ1 j).1 (hδ1 j).2 hd'
    (by linarith [(hθ j).1]) (by linarith [(hθ j).2]) hθ1 (hmp j) (by omega)).trans hΘ

/-- `|a - b - (m₁ - m₀)/6 · d| ≤ |a| + |b| + (|m₁| + |m₀|)/6 · |d|`. -/
private lemma swap_abs_combine (a b m₁ m₀ d : ℝ) :
    |a - b - (m₁ - m₀) / 6 * d| ≤ |a| + |b| + (|m₁| + |m₀|) / 6 * |d| := by
  have h1 : |(m₁ - m₀) / 6 * d| ≤ (|m₁| + |m₀|) / 6 * |d| := by
    rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    gcongr
    exact abs_sub _ _
  calc |a - b - (m₁ - m₀) / 6 * d| ≤ |a - b| + |(m₁ - m₀) / 6 * d| := abs_sub _ _
    _ ≤ |a| + |b| + (|m₁| + |m₀|) / 6 * |d| := by linarith [abs_sub a b]

/-- The probabilistic part of the swap: for `f(X, t)` with the deterministic bound
`|∂ⁿ f| ≤ n! C_b Dⁿ` and the bound `|∂ⁿ f| ≤ n! C_b Θ` on a good set of `X` near `X_{iμ} = 0`,
whose complement is controlled by `T ≥ 1` with `E T ≤ β`, the difference of the two swaps minus
the third-moment term is bounded by the remainder, tail and coefficient-move terms. -/
private lemma swap_prob {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {N : ℕ} (hN : 1 ≤ N) {ε : ℝ} (C : ℕ → ℝ) (p : ℕ) {X : Ω → Matrix (Fin M) (Fin N) ℝ}
    (hX : EntryAssumption C X) (i : Fin M) (μ : Fin N) (f : Matrix (Fin M) (Fin N) ℝ → ℝ → ℝ)
    (hfc : ∀ Xm, ContDiff ℝ 5 (f Xm))
    (hΦ : ∀ n ≤ 5,
      Measurable fun q : Matrix (Fin M) (Fin N) ℝ × ℝ => iteratedDeriv n (f q.1) q.2)
    (hfX : ∀ Xm, f (Xupd Xm i μ 0) = f Xm) {Cb D Θ β : ℝ} (hCb : 0 ≤ Cb) (hD1 : 1 ≤ D)
    (hΘ0 : 0 ≤ Θ) (hΘ1 : Θ ≤ 1) (Good : Matrix (Fin M) (Fin N) ℝ → Prop)
    (hcrude : ∀ n ≤ 5, ∀ (Xm : Matrix (Fin M) (Fin N) ℝ) (s : ℝ),
      |iteratedDeriv n (f Xm) s| ≤ n.factorial * Cb * D ^ n)
    (hgood : ∀ (Xm : Matrix (Fin M) (Fin N) ℝ) (s : ℝ), Good Xm →
      |Xm i μ| ≤ (N : ℝ) ^ (-1 / 2 + ε) → |s| ≤ (N : ℝ) ^ (-1 / 2 + ε) →
      ∀ n : ℕ, 1 ≤ n → n ≤ 5 → |iteratedDeriv n (f Xm) s| ≤ n.factorial * Cb * Θ)
    {TX : Ω → ℝ} (hTX0 : ∀ ω, 0 ≤ TX ω) (hTXi : Integrable TX) (hTXint : ∫ ω, TX ω ≤ β)
    (hTXg : ∀ ω, Good (X ω) ∨ 1 ≤ TX ω) {y₁ y₀ : Ω → ℝ} (hi₁ : IndepFun X y₁)
    (hi₀ : IndepFun X y₀) (hy₁ : Measurable y₁) (hy₀ : Measurable y₀) (hE₁ : ∫ ω, y₁ ω = 0)
    (hE₀ : ∫ ω, y₀ ω = 0) (hV₁ : ∫ ω, y₁ ω ^ 2 = 1 / (N : ℝ))
    (hV₀ : ∫ ω, y₀ ω ^ 2 = 1 / (N : ℝ))
    (hM₁ : ∀ q : ℕ, Integrable (fun ω => |Real.sqrt N * y₁ ω| ^ q) ∧
      ∫ ω, |Real.sqrt N * y₁ ω| ^ q ≤ C q)
    (hM₀ : ∀ q : ℕ, Integrable (fun ω => |Real.sqrt N * y₀ ω| ^ q) ∧
      ∫ ω, |Real.sqrt N * y₀ ω| ^ q ≤ C q) :
    |((∫ ω, f (X ω) (y₁ ω)) - (∫ ω, f (X ω) (y₀ ω))) -
        ((∫ ω, y₁ ω ^ 3) - (∫ ω, y₀ ω ^ 3)) / 6 *
          (∫ ω, iteratedDeriv 3 (f (X ω)) (X ω i μ))| ≤
      2 * (Cb * Θ * ((N : ℝ) ^ (-(4 : ℝ) / 2) * C 4) +
        Cb * D ^ 4 * ((N : ℝ) ^ (-(4 : ℝ) / 2 - p * ε) * C (4 + p) +
          (N : ℝ) ^ (-(4 : ℝ) / 2 + 4 * ε) * (β + (N : ℝ) ^ (-((p : ℝ) * ε)) * C p))) +
      2 * ((N : ℝ) ^ (-(3 : ℝ) / 2) * C 3) / 6 *
        (60 * Cb * ((N : ℝ) ^ (-(2 : ℝ) / 2) * C 2) +
          60 * Cb * D ^ 5 * ((N : ℝ) ^ (-(2 : ℝ) / 2 - p * ε) * C (2 + p) +
            (N : ℝ) ^ (-(2 : ℝ) / 2 + 2 * ε) * β)) := by
  have hD0 : 0 ≤ D := by linarith
  have hC3 : 0 ≤ C 3 := (integral_nonneg fun ω => by positivity).trans (hM₁ 3).2
  have hB3 : ∀ n ≤ 3, ∀ (Xm : Matrix (Fin M) (Fin N) ℝ) (s : ℝ),
      |iteratedDeriv n (f Xm) s| ≤ 6 * Cb * D ^ 3 := by
    intro n hn Xm s
    refine (hcrude n (by omega) Xm s).trans ?_
    have hfac : (n.factorial : ℝ) ≤ 6 := by
      have : n.factorial ≤ 6 := by interval_cases n <;> decide
      exact_mod_cast this
    have hpow : D ^ n ≤ D ^ 3 := pow_le_pow_right₀ hD1 hn
    have h0 : 0 ≤ D ^ n := by positivity
    calc (n.factorial : ℝ) * Cb * D ^ n ≤ 6 * Cb * D ^ n := by gcongr
      _ ≤ 6 * Cb * D ^ 3 := by gcongr
  have hXm : Measurable X := swap_measurable_X hX
  have e₁ := swap_expand hN f (fun n hn => hΦ n (by omega)) hB3 hXm hy₁ hi₁ hE₁ hV₁
    (fun q => (hM₁ q).1)
  have e₀ := swap_expand hN f (fun n hn => hΦ n (by omega)) hB3 hXm hy₀ hi₀ hE₀ hV₀
    (fun q => (hM₀ q).1)
  have hmomX : ∀ q : ℕ, Integrable (fun ω => |Real.sqrt N * X ω i μ| ^ q) ∧
      ∫ ω, |Real.sqrt N * X ω i μ| ^ q ≤ C q := fun q =>
    ⟨hX.integrable_moment q i μ, hX.moment q i μ⟩
  have hcrude4 : ∀ (Xm : Matrix (Fin M) (Fin N) ℝ) (s : ℝ),
      |iteratedDeriv 4 (f Xm) s| ≤ 24 * Cb * D ^ 4 := by
    intro Xm s
    have h := hcrude 4 (by norm_num) Xm s
    norm_num [Nat.factorial] at h
    linarith
  have hgood4 : ∀ (Xm : Matrix (Fin M) (Fin N) ℝ) (s : ℝ), Good Xm →
      |Xm i μ| ≤ (N : ℝ) ^ (-1 / 2 + ε) → |s| ≤ (N : ℝ) ^ (-1 / 2 + ε) →
      |iteratedDeriv 4 (f Xm) s| ≤ 24 * Cb * Θ := by
    intro Xm s hG hXs hs
    have h := hgood Xm s hG hXs hs 4 (by norm_num) (by norm_num)
    norm_num [Nat.factorial] at h
    linarith
  have hgood5 : ∀ (Xm : Matrix (Fin M) (Fin N) ℝ) (s : ℝ), Good Xm →
      |Xm i μ| ≤ (N : ℝ) ^ (-1 / 2 + ε) → |s| ≤ (N : ℝ) ^ (-1 / 2 + ε) →
      |iteratedDeriv 5 (f Xm) s| ≤ 120 * Cb := by
    intro Xm s hG hXs hs
    have h := hgood Xm s hG hXs hs 5 (by norm_num) (by norm_num)
    norm_num [Nat.factorial] at h
    nlinarith
  have r₁ := swap_remainder hN (ε := ε) C p f hfc hCb hΘ0 Good (fun Xm => Xm i μ) hcrude4
    hgood4 X hM₁ hmomX hTX0 hTXi hTXint hTXg
  have r₀ := swap_remainder hN (ε := ε) C p f hfc hCb hΘ0 Good (fun Xm => Xm i μ) hcrude4
    hgood4 X hM₀ hmomX hTX0 hTXi hTXint hTXg
  have hind : IndepFun (fun ω => iteratedDeriv 4 (f (X ω)) 0) (fun ω => X ω i μ) := by
    have hm4 : Measurable fun Xm : Matrix (Fin M) (Fin N) ℝ => iteratedDeriv 4 (f Xm) 0 := by
      have := (hΦ 4 (by norm_num)).comp (measurable_id.prodMk (measurable_const (a := (0 : ℝ))))
      exact this
    have h := (swap_indep_entry hX i μ).comp hm4 measurable_id
    have e : ((fun Xm : Matrix (Fin M) (Fin N) ℝ => iteratedDeriv 4 (f Xm) 0) ∘
        fun ω => Xupd (X ω) i μ 0) = fun ω => iteratedDeriv 4 (f (X ω)) 0 := by
      funext ω
      simp only [Function.comp_apply, hfX]
    rw [e] at h
    exact h
  have hc := swap_coef hN (ε := ε) C p f hfc hΦ hCb hD0 Good (fun Xm => Xm i μ)
    hcrude hgood5 hXm (hX.measurable i μ) hind (hX.mean i μ) hmomX hTX0 hTXi hTXint hTXg
  rw [e₁, e₀, hc.1]
  have m₁ := swap_abs_integral_pow_le hN (hM₁ 3).1 (hM₁ 3).2
  have m₀ := swap_abs_integral_pow_le hN (hM₀ 3).1 (hM₀ 3).2
  push_cast at m₁ m₀
  generalize ∫ ω, (f (X ω) (y₁ ω) - (f (X ω) 0 + iteratedDeriv 1 (f (X ω)) 0 * y₁ ω +
    iteratedDeriv 2 (f (X ω)) 0 * y₁ ω ^ 2 / 2 + iteratedDeriv 3 (f (X ω)) 0 * y₁ ω ^ 3 / 6)) = a₁
    at r₁ ⊢
  generalize ∫ ω, (f (X ω) (y₀ ω) - (f (X ω) 0 + iteratedDeriv 1 (f (X ω)) 0 * y₀ ω +
    iteratedDeriv 2 (f (X ω)) 0 * y₀ ω ^ 2 / 2 + iteratedDeriv 3 (f (X ω)) 0 * y₀ ω ^ 3 / 6)) = a₀
    at r₀ ⊢
  generalize ∫ ω, (iteratedDeriv 3 (f (X ω)) (X ω i μ) - iteratedDeriv 3 (f (X ω)) 0 -
    iteratedDeriv 4 (f (X ω)) 0 * X ω i μ) = d at hc ⊢
  generalize ∫ ω, y₁ ω ^ 3 = u₁ at m₁ ⊢
  generalize ∫ ω, y₀ ω ^ 3 = u₀ at m₀ ⊢
  generalize ∫ ω, f (X ω) 0 = v₀
  generalize ∫ ω, iteratedDeriv 2 (f (X ω)) 0 = v₂
  generalize ∫ ω, iteratedDeriv 3 (f (X ω)) 0 = v₃
  have key : v₀ + 1 / (N : ℝ) / 2 * v₂ + u₁ / 6 * v₃ + a₁ -
      (v₀ + 1 / (N : ℝ) / 2 * v₂ + u₀ / 6 * v₃ + a₀) - (u₁ - u₀) / 6 * (v₃ + d) =
      a₁ - a₀ - (u₁ - u₀) / 6 * d := by ring
  rw [key]
  refine (swap_abs_combine _ _ _ _ _).trans ?_
  have hm3 : (|u₁| + |u₀|) / 6 ≤ 2 * ((N : ℝ) ^ (-(3 : ℝ) / 2) * C 3) / 6 := by linarith
  have hd0 : 0 ≤ |d| := abs_nonneg _
  have hm30 : 0 ≤ 2 * ((N : ℝ) ^ (-(3 : ℝ) / 2) * C 3) / 6 := by positivity
  have hprod := mul_le_mul hm3 hc.2 hd0 hm30
  linarith

/-! ## The swap

The one-entry step of the Green function comparison in the proof of Theorem 3.18 under
(T_diag) (Section 10.2). -/

/-- One entry swap: for `y₁`, `y₀` independent of `X` with the first two moments of an entry,
`E F(X^{y₁}_{(iμ)}) - E F(X^{y₀}_{(iμ)})` is the third-moment term at `X` up to
`K C_b N^{-7/3+20ε}`. -/
theorem smF_swap (τ : ℝ) (C : ℕ → ℝ) (l : ℕ) (ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 200) :
    ∃ K : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)] (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (X : Ω → Matrix (Fin M) (Fin N) ℝ) (k : ℕ) (y₁ y₀ : Ω → ℝ) (i : Fin M) (μ : Fin N)
      (F : (Fin l → ℝ) → ℝ) (Cb : ℝ) (Ea Eb : Fin l → ℝ),
      IsModel τ C M N Sig X → RegularEdge τ N (specOf Sig) k →
      IndepFun X y₁ → IndepFun X y₀ → Measurable y₁ → Measurable y₀ →
      (∫ ω, y₁ ω) = 0 → (∫ ω, y₀ ω) = 0 → (∫ ω, y₁ ω ^ 2) = 1 / (N : ℝ) →
      (∫ ω, y₀ ω ^ 2) = 1 / (N : ℝ) →
      (∀ p : ℕ, Integrable (fun ω => |Real.sqrt N * y₁ ω| ^ p) ∧
        ∫ ω, |Real.sqrt N * y₁ ω| ^ p ≤ C p) →
      (∀ p : ℕ, Integrable (fun ω => |Real.sqrt N * y₀ ω| ^ p) ∧
        ∫ ω, |Real.sqrt N * y₀ ω| ^ p ≤ C p) →
      ContDiff ℝ 5 F → (∀ m ≤ 5, ∀ x, ‖iteratedFDeriv ℝ m F x‖ ≤ Cb) →
      EdgeWindows N (edgeVal N (specOf Sig) k) ε Ea Eb →
      |((∫ ω, smF F Sig (Xupd (X ω) i μ (y₁ ω)) (etaE N ε) Ea Eb) -
            (∫ ω, smF F Sig (Xupd (X ω) i μ (y₀ ω)) (etaE N ε) Ea Eb)) -
          ((∫ ω, y₁ ω ^ 3) - (∫ ω, y₀ ω ^ 3)) / 6 *
            (∫ ω, smT 3 F Sig (X ω) (etaE N ε) Ea Eb i μ (X ω i μ))| ≤
        K * Cb * (N : ℝ) ^ (-7 / 3 + 20 * ε) := by
  obtain ⟨K₂, hK₂, N₂, hdet⟩ := entryBounds_det τ ε hτ hε hε1
  obtain ⟨K₁, -, N₁, hev⟩ := entryBounds_event τ C ε ε 8 hτ hε hε1 hε le_rfl
  obtain ⟨K₃, hK₃, N₃, hmpi⟩ := entryBounds_mPi_window τ ε hτ hε hε1
  obtain ⟨p, hp⟩ : ∃ p : ℕ, 8 ≤ (p : ℝ) * ε := ⟨⌈8 / ε⌉₊, by
    calc (8 : ℝ) = 8 / ε * ε := by field_simp
      _ ≤ (⌈8 / ε⌉₊ : ℝ) * ε := mul_le_mul_of_nonneg_right (Nat.le_ceil _) hε.le⟩
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℝ, c₁ = 2 * τ⁻¹ ^ 2 + 8 * (K₂ + 1) ^ 2 := ⟨_, rfl⟩
  obtain ⟨cΘ, hcΘ⟩ : ∃ cΘ : ℝ,
      cΘ = 24 * (8 * (K₂ + 1)) ^ 5 * ((4 + 2 * (2 * K₂ + 1)) * c₁ + K₃) := ⟨_, rfl⟩
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ℝ, a₀ = τ⁻¹ + 2 * τ⁻¹ * (1 + τ⁻¹) + 3 := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = a₀ ^ 2 + 3 * a₀ + 1 := ⟨_, rfl⟩
  have hy1 : -1 / 2 + ε < 0 := by linarith
  have hy2 : -1 / 3 + 10 * ε < 0 := by linarith
  obtain ⟨N₄, hN₄⟩ := eventually_atTop.1 ((swap_ev_small hy1 (4 * (K₂ + 1))).and
    ((swap_ev_small hy2 c₁).and (swap_ev_small hy2 cΘ)))
  refine ⟨2 * (cΘ * C 4 + 384 ^ 4 * A ^ 4 * (C (4 + p) + 2 * l + C p)) +
    C 3 / 3 * (60 * C 2 + 60 * 384 ^ 5 * A ^ 5 * (C (2 + p) + 2 * l)),
    max (max (max N₁ N₂) (max N₃ N₄)) 1, ?_⟩
  intro N hN Ω _ _ M Sig X k y₁ y₀ i μ F Cb Ea Eb hm hk hi₁ hi₀ hy₁ hy₀ hE₁ hE₀ hV₁ hV₀ hM₁ hM₀
    hF hFb hW
  have hNN : 1 ≤ N := le_of_max_le_right hN
  have hN1 : N₁ ≤ N :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_of_max_le_left hN)
  have hN2 : N₂ ≤ N :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_of_max_le_left hN)
  have hN3 : N₃ ≤ N :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_of_max_le_left hN)
  have hN4 : N₄ ≤ N :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_of_max_le_left hN)
  obtain ⟨hA1, hA2, hA3⟩ := hN₄ N hN4
  have hn : (0 : ℝ) < N := by exact_mod_cast hNN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hNN
  have hSig := hm.sigma.posDef
  have hda : DensityAssumptions τ N (specOf Sig) := hm.diagModel_specOf.densityAssumptions hτ
  have hη : 0 < etaE N ε := Real.rpow_pos_of_pos hn _
  have hη1 : etaE N ε ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
  have hCb : 0 ≤ Cb := (norm_nonneg _).trans (hFb 0 (by norm_num) 0)
  have hC : ∀ q : ℕ, 0 ≤ C q := fun q =>
    (integral_nonneg fun ω => by positivity).trans (hM₁ q).2
  have hτi : 0 < τ⁻¹ := inv_pos.2 hτ
  have hK₂0 : 0 ≤ K₂ := hK₂.le
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; positivity
  have hcΘ0 : 0 ≤ cΘ := by rw [hcΘ]; positivity
  have ha₀0 : 0 < a₀ := by rw [ha₀]; positivity
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  -- the function of the entry
  obtain ⟨f, hf⟩ : ∃ f : Matrix (Fin M) (Fin N) ℝ → ℝ → ℝ,
      f = fun Xm t => smF F Sig (Xupd Xm i μ t) (etaE N ε) Ea Eb := ⟨_, rfl⟩
  have hfc : ∀ Xm, ContDiff ℝ 5 (f Xm) := fun Xm => by
    rw [hf]
    exact hF.comp (contDiff_pi.2 fun j =>
      derivative_contDiff_smCount hSig Xm hη (Ea j) (Eb j) i μ 5)
  have hf0c : Continuous fun q : Matrix (Fin M) (Fin N) ℝ × ℝ => f q.1 q.2 := by
    rw [hf]
    exact hF.continuous.comp (continuous_pi fun j =>
      (swap_continuous_smCount hSig hη (Ea j) (Eb j)).comp (swap_continuous_Xupd i μ))
  have hΦ := swap_measurable_iteratedDeriv f hf0c.measurable 5 hfc
  -- the deterministic bound
  have hW1 : 1 ≤ A * (N : ℝ) ^ (4 / 3 + 18 * ε) := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (4 / 3 + 18 * ε) := Real.one_le_rpow hn1 (by linarith)
    have h2 : 1 ≤ A := by rw [hAdef]; nlinarith
    nlinarith
  have hSn : ‖Sig‖ ≤ a₀ := (swap_norm_sig_le hτ hm.sigma).trans (by
    rw [ha₀]
    have : 0 ≤ 2 * τ⁻¹ * (1 + τ⁻¹) := by positivity
    linarith)
  have hedge := swap_edgeVal_le hτ hm hk
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
  have hη2 : (etaE N ε) ^ 2 = (N : ℝ) ^ (-(4 / 3 + 18 * ε)) := by
    rw [etaE, ← Real.rpow_natCast, ← Real.rpow_mul hn.le]
    congr 1; push_cast; ring
  have hGW : ∀ (Xm : Matrix (Fin M) (Fin N) ℝ) (E : ℝ), |E| ≤ a₀ → ∀ a b : Fin M ⊕ Fin N,
      ‖G Sig Xm ((E : ℂ) + etaE N ε * Complex.I) a b‖ ≤ A * (N : ℝ) ^ (4 / 3 + 18 * ε) := by
    intro Xm E hE a b
    refine (derivative_norm_G_entry_le hSig ha₀0 hSn Xm hE hη hη1 a b).trans (le_of_eq ?_)
    rw [hη2, Real.rpow_neg hn.le, div_inv_eq_mul, hAdef]
  have hcrude : ∀ n ≤ 5, ∀ (Xm : Matrix (Fin M) (Fin N) ℝ) (s : ℝ),
      |iteratedDeriv n (f Xm) s| ≤
        n.factorial * Cb * (384 * (A * (N : ℝ) ^ (4 / 3 + 18 * ε))) ^ n := by
    intro n hn5 Xm s
    rw [hf]
    exact swap_crude hSig hη hF hFb Ea Eb i μ hW1
      (fun Xm j a b => ⟨hGW _ _ (hEa _ (hW j).1) a b, hGW _ _ (hEa _ (hW j).2) a b⟩) Xm s hn5
  -- the bound on the good event
  have hdE := fun E (hE : |E - edgeVal N (specOf Sig) k| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε)) =>
    hdet N hN2 M Sig k hSig hda hk E hE
  have hvE := fun E (hE : |E - edgeVal N (specOf Sig) k| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε)) =>
    hev N hN1 M Sig X k hm hk E hE i μ
  have hδle : ∀ E : ℝ, |E - edgeVal N (specOf Sig) k| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) →
      (N : ℝ) ^ ε * (τ⁻¹ ^ 2 * Psi N (specOf Sig) ((E : ℂ) + etaE N ε * Complex.I)) ≤
        2 * τ⁻¹ ^ 2 * (N : ℝ) ^ (-1 / 3 + 10 * ε) := by
    intro E hE
    have h := (hdE E hE).1
    have e : (N : ℝ) ^ ε * (N : ℝ) ^ (-1 / 3 + 9 * ε) = (N : ℝ) ^ (-1 / 3 + 10 * ε) := by
      rw [← Real.rpow_add hn]; congr 1; ring
    have hNe : 0 ≤ (N : ℝ) ^ ε := by positivity
    calc (N : ℝ) ^ ε * (τ⁻¹ ^ 2 * Psi N (specOf Sig) ((E : ℂ) + etaE N ε * Complex.I))
        ≤ (N : ℝ) ^ ε * (τ⁻¹ ^ 2 * (2 * (N : ℝ) ^ (-1 / 3 + 9 * ε))) := by gcongr
      _ = 2 * τ⁻¹ ^ 2 * ((N : ℝ) ^ ε * (N : ℝ) ^ (-1 / 3 + 9 * ε)) := by ring
      _ = 2 * τ⁻¹ ^ 2 * (N : ℝ) ^ (-1 / 3 + 10 * ε) := by rw [e]
  have hr_le : (N : ℝ) ^ (-1 / 2 + ε) ≤ (N : ℝ) ^ (-1 / 3 + 10 * ε) :=
    swap_rpow_le hNN (by linarith)
  have hκle : (N : ℝ) ^ (-1 / 3 + ε / 2) ≤ (N : ℝ) ^ (-1 / 3 + 10 * ε) :=
    swap_rpow_le hNN (by linarith)
  have hx0 : 0 ≤ (N : ℝ) ^ (-1 / 3 + 10 * ε) := by positivity
  have hθj : ∀ E : ℝ, |E - edgeVal N (specOf Sig) k| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) →
      (N : ℝ) ^ ε * (τ⁻¹ ^ 2 * Psi N (specOf Sig) ((E : ℂ) + etaE N ε * Complex.I)) +
        4 * (K₂ + 1) ^ 2 * (2 * (N : ℝ) ^ (-1 / 2 + ε)) ≤ c₁ * (N : ℝ) ^ (-1 / 3 + 10 * ε) := by
    intro E hE
    have h1 := hδle E hE
    have h2 : 4 * (K₂ + 1) ^ 2 * (2 * (N : ℝ) ^ (-1 / 2 + ε)) ≤
        4 * (K₂ + 1) ^ 2 * (2 * (N : ℝ) ^ (-1 / 3 + 10 * ε)) := by gcongr
    have e : c₁ * (N : ℝ) ^ (-1 / 3 + 10 * ε) = 2 * τ⁻¹ ^ 2 * (N : ℝ) ^ (-1 / 3 + 10 * ε) +
        4 * (K₂ + 1) ^ 2 * (2 * (N : ℝ) ^ (-1 / 3 + 10 * ε)) := by
      rw [hc₁]; ring
    rw [e]
    exact add_le_add h1 h2
  have hΘ : 24 * (8 * (K₂ + 1)) ^ 5 * (4 * (c₁ * (N : ℝ) ^ (-1 / 3 + 10 * ε)) +
      (2 * (2 * K₂ + 1) * (c₁ * (N : ℝ) ^ (-1 / 3 + 10 * ε)) +
        K₃ * (N : ℝ) ^ (-1 / 3 + ε / 2))) ≤ cΘ * (N : ℝ) ^ (-1 / 3 + 10 * ε) := by
    have hK3 : K₃ * (N : ℝ) ^ (-1 / 3 + ε / 2) ≤ K₃ * (N : ℝ) ^ (-1 / 3 + 10 * ε) :=
      mul_le_mul_of_nonneg_left hκle hK₃.le
    calc _ ≤ 24 * (8 * (K₂ + 1)) ^ 5 * (4 * (c₁ * (N : ℝ) ^ (-1 / 3 + 10 * ε)) +
          (2 * (2 * K₂ + 1) * (c₁ * (N : ℝ) ^ (-1 / 3 + 10 * ε)) +
            K₃ * (N : ℝ) ^ (-1 / 3 + 10 * ε))) := by gcongr
      _ = cΘ * (N : ℝ) ^ (-1 / 3 + 10 * ε) := by rw [hcΘ]; ring
  obtain ⟨Good, hGooddef⟩ : ∃ Good : Matrix (Fin M) (Fin N) ℝ → Prop, Good = fun Xm => ∀ j,
      (∀ a ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
        ∀ b ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
          ‖G Sig Xm ((Ea j : ℂ) + etaE N ε * Complex.I) a b -
              piMat Sig (mFun N (specOf Sig) ((Ea j : ℂ) + etaE N ε * Complex.I)) a b‖ ≤
            (N : ℝ) ^ ε * (τ⁻¹ ^ 2 * Psi N (specOf Sig) ((Ea j : ℂ) + etaE N ε * Complex.I))) ∧
      (∀ a ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
        ∀ b ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
          ‖G Sig Xm ((Eb j : ℂ) + etaE N ε * Complex.I) a b -
              piMat Sig (mFun N (specOf Sig) ((Eb j : ℂ) + etaE N ε * Complex.I)) a b‖ ≤
            (N : ℝ) ^ ε * (τ⁻¹ ^ 2 * Psi N (specOf Sig) ((Eb j : ℂ) + etaE N ε * Complex.I))) :=
    ⟨_, rfl⟩
  have hgood : ∀ (Xm : Matrix (Fin M) (Fin N) ℝ) (s : ℝ), Good Xm →
      |Xm i μ| ≤ (N : ℝ) ^ (-1 / 2 + ε) → |s| ≤ (N : ℝ) ^ (-1 / 2 + ε) →
      ∀ n : ℕ, 1 ≤ n → n ≤ 5 →
        |iteratedDeriv n (f Xm) s| ≤ n.factorial * Cb * (cΘ * (N : ℝ) ^ (-1 / 3 + 10 * ε)) := by
    intro Xm s hG hX hs n hn1' hn5
    rw [hGooddef] at hG
    rw [hf]
    exact swap_good hSig hη hF hFb Ea Eb i μ
      (fun j => mFun N (specOf Sig) ((Ea j : ℂ) + etaE N ε * Complex.I))
      (fun j => mFun N (specOf Sig) ((Eb j : ℂ) + etaE N ε * Complex.I))
      (fun j => (N : ℝ) ^ ε * (τ⁻¹ ^ 2 * Psi N (specOf Sig) ((Ea j : ℂ) + etaE N ε * Complex.I)))
      (fun j => (N : ℝ) ^ ε * (τ⁻¹ ^ 2 * Psi N (specOf Sig) ((Eb j : ℂ) + etaE N ε * Complex.I)))
      (K := K₂) (r := (N : ℝ) ^ (-1 / 2 + ε)) (θ := c₁ * (N : ℝ) ^ (-1 / 3 + 10 * ε))
      (κ₀ := K₃ * (N : ℝ) ^ (-1 / 3 + ε / 2)) (Θ := cΘ * (N : ℝ) ^ (-1 / 3 + 10 * ε))
      (fun j a b => ⟨(hdE _ (hW j).1).2.2 a b, (hdE _ (hW j).2).2.2 a b⟩)
      (fun j => ⟨(hvE _ (hW j).1).1, (hvE _ (hW j).2).1⟩)
      (fun j => ⟨hθj _ (hW j).1, hθj _ (hW j).2⟩) (by linarith) (by linarith)
      (fun j => (hmpi N hN3 M Sig k hSig hda hk (Ea j) (Eb j) (hW j).1 (hW j).2).2.2 i)
      hΘ (by positivity) (by linarith) Xm s hG hX hs hn1' hn5
  -- the events
  obtain ⟨Aset, hAsetdef⟩ : ∃ Aset : ℝ → Set Ω, Aset = fun (E : ℝ) => {ω |
      ∀ a ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
        ∀ b ∈ ({Sum.inl i, Sum.inr μ} : Set (Fin M ⊕ Fin N)),
          ‖G Sig (X ω) ((E : ℂ) + etaE N ε * Complex.I) a b -
              piMat Sig (mFun N (specOf Sig) ((E : ℂ) + etaE N ε * Complex.I)) a b‖ ≤
            (N : ℝ) ^ ε * (τ⁻¹ ^ 2 * Psi N (specOf Sig) ((E : ℂ) + etaE N ε * Complex.I))} :=
    ⟨_, rfl⟩
  have hAset : ∀ E : ℝ, |E - edgeVal N (specOf Sig) k| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) →
      (ℙ : Measure Ω) (Aset E)ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(8 : ℝ))) := by
    intro E hE
    refine le_trans (measure_mono ?_) (hvE E hE).2
    intro ω hω
    rw [hAsetdef] at hω
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hω ⊢
    intro h
    exact hω fun a ha b hb => (h.1 a ha b hb).1
  obtain ⟨TX, hTX0, hTXi, hTXint, hTX1⟩ := swap_events
    (fun j (b : Bool) => if b then Aset (Ea j) else Aset (Eb j))
    (q := (N : ℝ) ^ (-(8 : ℝ))) (by positivity) fun j b => by
      cases b
      · exact hAset _ (hW j).2
      · exact hAset _ (hW j).1
  have hTXg : ∀ ω, Good (X ω) ∨ 1 ≤ TX ω := by
    intro ω
    rcases hTX1 ω with h | h
    · left
      rw [hGooddef]
      intro j
      have ha := h j true
      have hb := h j false
      simp only [ite_true, Bool.false_eq_true, ite_false] at ha hb
      rw [hAsetdef] at ha hb
      exact ⟨ha, hb⟩
    · exact Or.inr h
  -- the assembly
  have hD1 : 1 ≤ 384 * (A * (N : ℝ) ^ (4 / 3 + 18 * ε)) := by linarith
  have hfX : ∀ Xm : Matrix (Fin M) (Fin N) ℝ, f (Xupd Xm i μ 0) = f Xm := fun Xm => by
    rw [hf]
    funext t
    simp only [swap_Xupd_Xupd]
  have g1 : (∫ ω, smF F Sig (Xupd (X ω) i μ (y₁ ω)) (etaE N ε) Ea Eb) =
      ∫ ω, f (X ω) (y₁ ω) := by rw [hf]
  have g0 : (∫ ω, smF F Sig (Xupd (X ω) i μ (y₀ ω)) (etaE N ε) Ea Eb) =
      ∫ ω, f (X ω) (y₀ ω) := by rw [hf]
  have g3 : (∫ ω, smT 3 F Sig (X ω) (etaE N ε) Ea Eb i μ (X ω i μ)) =
      ∫ ω, iteratedDeriv 3 (f (X ω)) (X ω i μ) := by rw [hf]; rfl
  rw [g1, g0, g3]
  refine le_trans (swap_prob hNN (ε := ε) C p hm.entries i μ f hfc hΦ hfX hCb hD1
    (by positivity) (by linarith) Good hcrude hgood hTX0 hTXi hTXint hTXg hi₁ hi₀ hy₁ hy₀
    hE₁ hE₀ hV₁ hV₀ hM₁ hM₀) ?_
  exact swap_final_arith hNN hε hε1 hp hCb hcΘ0 hA0 (hC 2) (hC 3) (hC 4)
    (hC (2 + p)) (hC (4 + p)) (hC p) (Nat.cast_nonneg l)

end Anisotropic
