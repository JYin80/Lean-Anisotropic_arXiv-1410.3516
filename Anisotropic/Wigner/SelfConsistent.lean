module

public import Anisotropic.MainDefs
public import Anisotropic.Framework.Domination

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

/-! # The Stieltjes transform of `A`, the definition of `m^W`, uniqueness, and the semicircle check at `A = 0`, `z = i` -/

/-- `m^W` depends only on the spectrum of `A` (§12.1). -/
theorem mW_comp_perm {N : ℕ} (a : Fin N → ℝ) (e : Equiv.Perm (Fin N)) (z : ℂ) :
    mW (a ∘ e) z = mW a z := by
  have h : ∀ w, stieltjesA (a ∘ e) w = stieltjesA a w := fun w => by
    unfold stieltjesA
    congr 1
    exact Equiv.sum_comp e (fun i => ((a i : ℂ) - w)⁻¹)
  unfold mW
  simp_rw [h]

/-- `‖x⁻¹‖² = |x|⁻²`. -/
private lemma selfConsistent_norm_inv_sq (x : ℂ) : ‖x⁻¹‖ ^ 2 = (Complex.normSq x)⁻¹ := by
  rw [norm_inv, inv_pow, Complex.sq_norm]

/-- `Im m_A(w) = Im w · S(w)` with `S(w) = N⁻¹ ∑ᵢ |aᵢ − w|⁻²`. -/
private lemma selfConsistent_im_stieltjesA {N : ℕ} (a : Fin N → ℝ) (w : ℂ) :
    (stieltjesA a w).im =
      w.im * ((N : ℝ)⁻¹ * ∑ i, (Complex.normSq ((a i : ℂ) - w))⁻¹) := by
  unfold stieltjesA
  rw [show ((N : ℂ)⁻¹) = (((N : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.im_ofReal_mul,
    Complex.im_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.inv_im]
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, neg_neg]
  ring

/-- `‖m_A(w)‖ ≤ N⁻¹ ∑ᵢ |aᵢ − w|⁻¹`. -/
private lemma selfConsistent_norm_stieltjesA_le {N : ℕ} (a : Fin N → ℝ) (w : ℂ) :
    ‖stieltjesA a w‖ ≤ (N : ℝ)⁻¹ * ∑ i, ‖((a i : ℂ) - w)⁻¹‖ := by
  unfold stieltjesA
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)

/-- At a solution `m` of `m = m_A(z + m)` with `Im m > 0` and `Im z > 0`,
`S(z + m) = Im m/(Im m + η) < 1`. -/
private lemma selfConsistent_S_lt_one {N : ℕ} (a : Fin N → ℝ) {z m : ℂ} (hz : 0 < z.im)
    (hm : 0 < m.im) (heq : m = stieltjesA a (z + m)) :
    (N : ℝ)⁻¹ * ∑ i, (Complex.normSq ((a i : ℂ) - (z + m)))⁻¹ < 1 := by
  have him := congrArg Complex.im heq
  rw [selfConsistent_im_stieltjesA] at him
  simp only [Complex.add_im] at him
  set S := (N : ℝ)⁻¹ * ∑ i, (Complex.normSq ((a i : ℂ) - (z + m)))⁻¹
  by_contra hS
  push Not at hS
  nlinarith

/-- `N⁻¹ ∑ᵢ |aᵢ − w|⁻¹ ≤ (S(w) + 1)/2` for `N ≥ 1`. -/
private lemma selfConsistent_sum_norm_inv_le {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) (w : ℂ) :
    (N : ℝ)⁻¹ * ∑ i, ‖((a i : ℂ) - w)⁻¹‖ ≤
      ((N : ℝ)⁻¹ * ∑ i, (Complex.normSq ((a i : ℂ) - w))⁻¹ + 1) / 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hle : ∑ i, ‖((a i : ℂ) - w)⁻¹‖ ≤
      ∑ i, ((Complex.normSq ((a i : ℂ) - w))⁻¹ + 1) / 2 := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← selfConsistent_norm_inv_sq]
    nlinarith [sq_nonneg (‖((a i : ℂ) - w)⁻¹‖ - 1)]
  rw [← Finset.sum_div, Finset.sum_add_distrib] at hle
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hle
  calc (N : ℝ)⁻¹ * ∑ i, ‖((a i : ℂ) - w)⁻¹‖
      ≤ (N : ℝ)⁻¹ * ((∑ i, (Complex.normSq ((a i : ℂ) - w))⁻¹ + N) / 2) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = _ := by field_simp

/-- `|m^W| < 1` on `ℂ₊` (`|m| ≤ S(w)^{1/2}` with `S(w) = Im m/(Im m + η) < 1`). -/
theorem norm_mW_lt_one {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) {z : ℂ} (hz : 0 < z.im) :
    ‖mW a z‖ < 1 := by
  unfold mW
  split_ifs with h
  · obtain ⟨hm, heq⟩ := h.choose_spec
    have hS := selfConsistent_S_lt_one a hz hm heq
    calc ‖h.choose‖ = ‖stieltjesA a (z + h.choose)‖ := by rw [← heq]
      _ ≤ _ := selfConsistent_norm_stieltjesA_le a _
      _ ≤ _ := selfConsistent_sum_norm_inv_le hN a _
      _ < 1 := by linarith
  · simp

/-! ## Examples -/

/-- `|m^W| < 1` at `N = 2`, spectrum `(1, −1)`, `z = i`. -/
example : ‖mW (![1, -1] : Fin 2 → ℝ) Complex.I‖ < 1 :=
  norm_mW_lt_one (by norm_num) _ (by simp)

#print axioms Anisotropic.stieltjesA
#print axioms Anisotropic.mW
#print axioms Anisotropic.mW_comp_perm
#print axioms Anisotropic.norm_mW_lt_one

end Anisotropic
