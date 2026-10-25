import Anisotropic.LinAlg.ResolventId

open Matrix ComplexOrder
set_option linter.unusedSectionVars false
namespace Anisotropic
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
open scoped Matrix.Norms.L2Operator
open Sum

/-! ### (res_exp) and (main_identity) -/

/-- `X^{λ}_{(iμ)}`: entry `(i, μ)` replaced by `lam`. -/
def Xupd (X : Matrix m n ℝ) (i : m) (μ : n) (lam : ℝ) : Matrix m n ℝ :=
  fun j ν => if j = i ∧ ν = μ then lam else X j ν

/-- `Δ^{lam}_{(iμ)}`. -/
noncomputable def Delta (i : m) (μ : n) (lam : ℝ) : Matrix (m ⊕ n) (m ⊕ n) ℂ := fun s t =>
  if (s = inl i ∧ t = inr μ) ∨ (s = inr μ ∧ t = inl i) then (lam : ℂ) else 0

/-- `H` for the matrix with entry `(i, μ)` replaced by `lam'` differs from `H` for the matrix with
entry `lam` by `-Δ^{lam - lam'}`. -/
private theorem expansion_H_upd (Sig : Matrix m m ℝ) (X : Matrix m n ℝ) (z : ℂ) (i : m) (μ : n)
    (lam lam' : ℝ) :
    H Sig (Xupd X i μ lam') z = H Sig (Xupd X i μ lam) z - Delta i μ (lam - lam') := by
  ext s t
  rcases s with a | a <;> rcases t with b | b
  · simp [H, linH, Delta]
  · by_cases h : a = i ∧ b = μ
    · obtain ⟨rfl, rfl⟩ := h
      simp [H, linH, Delta, Xupd, cplx]
    · have h' : ¬ (a = i ∧ b = μ) := h
      simp [H, linH, Delta, Xupd, cplx, h']
  · by_cases h : b = i ∧ a = μ
    · obtain ⟨rfl, rfl⟩ := h
      simp [H, linH, Delta, Xupd, cplx]
    · have h' : ¬ (b = i ∧ a = μ) := h
      simp [H, linH, Delta, Xupd, cplx, h', and_comm]
  · simp [H, linH, Delta]

/-- (res_exp). -/
theorem res_exp {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (X : Matrix m n ℝ) {z : ℂ}
    (hz : 0 < z.im) (i : m) (μ : n) (lam lam' : ℝ) (K : ℕ) :
    G Sig (Xupd X i μ lam') z = G Sig (Xupd X i μ lam) z
      + ∑ k ∈ Finset.Icc 1 K, G Sig (Xupd X i μ lam) z
          * (Delta i μ (lam - lam') * G Sig (Xupd X i μ lam) z) ^ k
      + G Sig (Xupd X i μ lam') z * (Delta i μ (lam - lam') * G Sig (Xupd X i μ lam) z) ^ (K + 1) := by
  set G0 := G Sig (Xupd X i μ lam) z
  set G' := G Sig (Xupd X i μ lam') z
  set D := Delta i μ (lam - lam')
  have h1 : G' = G0 + G' * (D * G0) := by
    have e1 : H Sig (Xupd X i μ lam') z * G' = 1 := H_mul_G hSig _ hz
    have e2 : G' * H Sig (Xupd X i μ lam') z = 1 := G_mul_H hSig _ hz
    have e3 : H Sig (Xupd X i μ lam) z * G0 = 1 := H_mul_G hSig _ hz
    have e4 := expansion_H_upd Sig X z i μ lam lam'
    calc G' = G' * (H Sig (Xupd X i μ lam) z * G0) := by rw [e3, Matrix.mul_one]
      _ = G' * ((H Sig (Xupd X i μ lam') z + D) * G0) := by
          rw [e4]; congr 3; abel
      _ = G0 + G' * (D * G0) := by
          rw [add_mul, Matrix.mul_add, ← Matrix.mul_assoc G', ← Matrix.mul_assoc, e2,
            Matrix.one_mul]
  induction K with
  | zero => simpa using h1
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have : G' * (D * G0) ^ (K + 1) = G0 * (D * G0) ^ (K + 1) + G' * (D * G0) ^ (K + 1 + 1) := by
      conv_lhs => rw [h1]
      rw [add_mul, pow_succ' (D * G0) (K + 1), Matrix.mul_assoc G', ← Matrix.mul_assoc G']
    calc G' = _ := ih
      _ = _ := by rw [this]; abel


/-- The zero extension `G^{(r)}` vanishes in row `r` and column `r`. -/
private theorem expansion_G1_row (Sig : Matrix m m ℝ) (X : Matrix m n ℝ) (z : ℂ) (r t : m ⊕ n) :
    G1 Sig X z r r t = 0 := by simp [G1, Gm]

private theorem expansion_G1_col (Sig : Matrix m m ℝ) (X : Matrix m n ℝ) (z : ℂ) (r s : m ⊕ n) :
    G1 Sig X z r s r = 0 := by simp [G1, Gm]

private theorem expansion_ent_eq {p : Type*} [Fintype p] (A : Matrix p p ℂ) (x y : p → ℝ) :
    ent A x y = ∑ s, ∑ t, (x s : ℂ) * A s t * (y t : ℂ) := by
  simp only [ent, cvec, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

private theorem expansion_ent_eI_right {p : Type*} [Fintype p] [DecidableEq p] (A : Matrix p p ℂ)
    (x : p → ℝ) (r : p) : ent A x (eI r) = ∑ s, (x s : ℂ) * A s r := by
  rw [expansion_ent_eq]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [eI, Pi.single_apply, apply_ite]

private theorem expansion_ent_eI_left {p : Type*} [Fintype p] [DecidableEq p] (A : Matrix p p ℂ)
    (y : p → ℝ) (r : p) : ent A (eI r) y = ∑ t, A r t * (y t : ℂ) := by
  rw [expansion_ent_eq]
  simp [eI, Pi.single_apply, apply_ite, ite_mul, Finset.sum_ite_eq']

/-- (main_identity). -/
theorem main_identity {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (X : Matrix m n ℝ) {z : ℂ}
    (hz : 0 < z.im) (μ : n) (x y : m ⊕ n → ℝ) :
    ent (G Sig X z) x y
      = (x (inr μ) * y (inr μ) : ℝ) * G Sig X z (inr μ) (inr μ) + ent (G1 Sig X z (inr μ)) x y
        + G Sig X z (inr μ) (inr μ) * ent (G1 Sig X z (inr μ) * Xhat X) x (eI (inr μ))
            * ent ((Xhat X)ᵀ * G1 Sig X z (inr μ)) (eI (inr μ)) y
        - (x (inr μ) : ℂ) * G Sig X z (inr μ) (inr μ)
            * ent ((Xhat X)ᵀ * G1 Sig X z (inr μ)) (eI (inr μ)) y
        - (y (inr μ) : ℂ) * G Sig X z (inr μ) (inr μ)
            * ent (G1 Sig X z (inr μ) * Xhat X) x (eI (inr μ)) := by
  set g := G Sig X z
  set g1 := G1 Sig X z (inr μ)
  set c := g (inr μ) (inr μ) with hc_def
  have hc : c ≠ 0 := G_diag_ne_zero hSig X hz _
  set a : m ⊕ n → ℂ := fun s => (g1 * Xhat X) s (inr μ) with ha_def
  set b : m ⊕ n → ℂ := fun t => ((Xhat X)ᵀ * g1) (inr μ) t with hb_def
  have ha0 : a (inr μ) = 0 := by
    simp only [ha_def, Matrix.mul_apply, g1, expansion_G1_row, zero_mul, Finset.sum_const_zero]
  have hb0 : b (inr μ) = 0 := by
    simp only [hb_def, Matrix.mul_apply, g1, expansion_G1_col, mul_zero, Finset.sum_const_zero]
  have hcol : ∀ s, s ≠ inr μ → g s (inr μ) = -c * a s := by
    rintro (i | ν) hs
    · exact (Gia hSig X hz i μ).1
    · have hνμ : ν ≠ μ := fun h => hs (by rw [h])
      exact (Gij hSig X hz ν μ hνμ).2.1
  have hrow : ∀ t, t ≠ inr μ → g (inr μ) t = -c * b t := by
    rintro (i | ν) ht
    · exact (Gia hSig X hz i μ).2
    · have hνμ : μ ≠ ν := fun h => ht (by rw [h])
      exact (Gij hSig X hz μ ν hνμ).1
  have key : ∀ s t, g s t = g1 s t + c * a s * b t
      - (if s = inr μ then 1 else 0) * c * b t - (if t = inr μ then 1 else 0) * c * a s
      + (if s = inr μ then 1 else 0) * (if t = inr μ then 1 else 0) * c := by
    intro s t
    by_cases hs : s = inr μ <;> by_cases ht : t = inr μ
    · subst hs; subst ht
      simp [g1, expansion_G1_row, ha0, hb0, hc_def]
    · subst hs
      simp [ht, ha0, g1, expansion_G1_row, hrow t ht]
    · subst ht
      simp [hs, hb0, g1, expansion_G1_col, hcol s hs]
    · have h : g1 s t = g s t - g s (inr μ) * g (inr μ) t / c := Gstu hSig X hz (inr μ) s t hs ht
      have e1 := hcol s hs
      have e2 := hrow t ht
      rw [e1, e2] at h
      simp only [hs, ht, ite_false]
      rw [show g s t = g1 s t + c * a s * b t by
        rw [h]; field_simp; ring]
      ring
  have hA : ent (g1 * Xhat X) x (eI (inr μ)) = ∑ s, (x s : ℂ) * a s :=
    expansion_ent_eI_right _ _ _
  have hB : ent ((Xhat X)ᵀ * g1) (eI (inr μ)) y = ∑ t, b t * (y t : ℂ) :=
    expansion_ent_eI_left _ _ _
  rw [hA, hB, expansion_ent_eq g x y, expansion_ent_eq g1 x y]
  simp only [key, add_mul, sub_mul, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  have t2 : ∑ s, ∑ t, (x s : ℂ) * (c * a s * b t) * (y t : ℂ)
      = (c * ∑ s, (x s : ℂ) * a s) * ∑ t, b t * (y t : ℂ) := by
    rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  have t3 : ∑ s, ∑ t, (x s : ℂ) * ((if s = inr μ then 1 else 0) * c * b t) * (y t : ℂ)
      = (x (inr μ) : ℂ) * c * ∑ t, b t * (y t : ℂ) := by
    simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, Finset.sum_ite_irrel, Finset.sum_const_zero]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  have t4 : ∑ s, ∑ t, (x s : ℂ) * ((if t = inr μ then 1 else 0) * c * a s) * (y t : ℂ)
      = (y (inr μ) : ℂ) * c * ∑ s, (x s : ℂ) * a s := by
    simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  have t5 : ∑ s, ∑ t, (x s : ℂ) * (((if s = inr μ then 1 else 0) * if t = inr μ then 1 else 0) * c)
        * (y t : ℂ) = (x (inr μ) * y (inr μ) : ℝ) * c := by
    simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    push_cast
    ring
  rw [t2, t3, t4, t5]
  ring

/-! ### Compiled checks at `Σ = diag(2,1)`, `X = I/√2`, `z = i` -/

section Checks

open Complex

end Checks

end Anisotropic
