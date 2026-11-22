module

public import Anisotropic.Density.Basic

@[expose] public section

/-!
# Derivatives of `f` and the polynomial `P_z`

Derivatives `f'`, `f''` of the function `f` of (def_fx) given by (f_der), and the evaluation,
value at `0`, value at the poles `-1/s`, and degree of the polynomial `P_z` of Appendix A.1.
-/

open MeasureTheory Polynomial Filter Topology
open scoped ENNReal

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! ## Derivatives of `f` -/

private lemma poly_hasDerivAt_neg_inv {𝕜 : Type*} [NontriviallyNormedField 𝕜] {w : 𝕜}
    (hw : w ≠ 0) : HasDerivAt (fun w : 𝕜 => -w⁻¹) ((w ^ 2)⁻¹) w := by
  have h := (hasDerivAt_inv hw).neg
  convert h using 1
  ring

private lemma poly_hasDerivAt_inv_sq {𝕜 : Type*} [NontriviallyNormedField 𝕜] {w : 𝕜}
    (hw : w ≠ 0) : HasDerivAt (fun w : 𝕜 => (w ^ 2)⁻¹) (-2 * (w ^ 3)⁻¹) w := by
  have h1 : HasDerivAt (fun w : 𝕜 => w ^ 2) (((2 : ℕ) : 𝕜) * w ^ (2 - 1)) w :=
    hasDerivAt_pow 2 w
  have h := h1.inv (pow_ne_zero 2 hw)
  convert h using 1
  field_simp
  ring

private lemma poly_hasDerivAt_term {𝕜 : Type*} [NontriviallyNormedField 𝕜] (a n : 𝕜) {w : 𝕜}
    (h : 1 + a * w ≠ 0) :
    HasDerivAt (fun w : 𝕜 => a / (n * (1 + a * w))) (-(a ^ 2 / (n * (1 + a * w) ^ 2))) w := by
  have h1 : HasDerivAt (fun w : 𝕜 => 1 + a * w) a w := by
    simpa using ((hasDerivAt_id w).const_mul a).const_add 1
  have h2 := (h1.inv h).const_mul (a / n)
  have e : (fun w : 𝕜 => a / (n * (1 + a * w))) = fun w => (a / n) * (1 + a * w)⁻¹ := by
    funext w
    simp [div_eq_mul_inv]
    ring
  rw [e]
  convert h2 using 1
  simp [div_eq_mul_inv]
  ring

private lemma poly_hasDerivAt_term2 {𝕜 : Type*} [NontriviallyNormedField 𝕜] (a n : 𝕜) {w : 𝕜}
    (h : 1 + a * w ≠ 0) :
    HasDerivAt (fun w : 𝕜 => a ^ 2 / (n * (1 + a * w) ^ 2))
      (-(2 * (a ^ 3 / (n * (1 + a * w) ^ 3)))) w := by
  have h1 : HasDerivAt (fun w : 𝕜 => 1 + a * w) a w := by
    simpa using ((hasDerivAt_id w).const_mul a).const_add 1
  have h2 := (poly_hasDerivAt_inv_sq h).comp w h1
  have h3 := h2.const_mul (a ^ 2 / n)
  have e : (fun w : 𝕜 => a ^ 2 / (n * (1 + a * w) ^ 2)) =
      fun w => (a ^ 2 / n) * (((fun u : 𝕜 => (u ^ 2)⁻¹) ∘ fun w : 𝕜 => 1 + a * w) w) := by
    funext w
    simp [div_eq_mul_inv]
    ring
  rw [e]
  convert h3 using 1
  simp [div_eq_mul_inv]
  ring

/-- `f' = fCDeriv` on `ℂ` away from `0` and the poles `-1/σ_i`, (f_der). -/
theorem hasDerivAt_fC (N : ℕ) (σ : Fin M → ℝ) {w : ℂ} (hw : w ≠ 0)
    (hw' : ∀ i, 1 + (σ i : ℂ) * w ≠ 0) : HasDerivAt (fC N σ) (fCDeriv N σ w) w := by
  have hs : HasDerivAt (fun w : ℂ => ∑ i, (σ i : ℂ) / ((N : ℂ) * (1 + (σ i : ℂ) * w)))
      (∑ i, -((σ i : ℂ) ^ 2 / ((N : ℂ) * (1 + (σ i : ℂ) * w) ^ 2))) w :=
    HasDerivAt.fun_sum fun i _ => poly_hasDerivAt_term (σ i : ℂ) (N : ℂ) (hw' i)
  have h := (poly_hasDerivAt_neg_inv hw).add hs
  unfold fC fCDeriv
  convert h using 1
  rw [Finset.sum_neg_distrib, sub_eq_add_neg]

/-- `f' = fR1` on `ℝ` away from `0` and the poles `-1/σ_i`, (f_der). -/
theorem hasDerivAt_fR (N : ℕ) (σ : Fin M → ℝ) {x : ℝ} (hx : x ≠ 0)
    (hx' : ∀ i, 1 + σ i * x ≠ 0) : HasDerivAt (fR N σ) (fR1 N σ x) x := by
  have hs : HasDerivAt (fun w : ℝ => ∑ i, σ i / ((N : ℝ) * (1 + σ i * w)))
      (∑ i, -(σ i ^ 2 / ((N : ℝ) * (1 + σ i * x) ^ 2))) x :=
    HasDerivAt.fun_sum fun i _ => poly_hasDerivAt_term (σ i) (N : ℝ) (hx' i)
  have h := (poly_hasDerivAt_neg_inv hx).add hs
  unfold fR fR1
  convert h using 1
  rw [Finset.sum_neg_distrib, sub_eq_add_neg]

/-- `f'' = fR2` on `ℝ` away from `0` and the poles `-1/σ_i`, (f_der). -/
theorem hasDerivAt_fR1 (N : ℕ) (σ : Fin M → ℝ) {x : ℝ} (hx : x ≠ 0)
    (hx' : ∀ i, 1 + σ i * x ≠ 0) : HasDerivAt (fR1 N σ) (fR2 N σ x) x := by
  have hs : HasDerivAt (fun w : ℝ => ∑ i, σ i ^ 2 / ((N : ℝ) * (1 + σ i * w) ^ 2))
      (∑ i, -(2 * (σ i ^ 3 / ((N : ℝ) * (1 + σ i * x) ^ 3)))) x :=
    HasDerivAt.fun_sum fun i _ => poly_hasDerivAt_term2 (σ i) (N : ℝ) (hx' i)
  have h := (poly_hasDerivAt_inv_sq hx).sub hs
  unfold fR1 fR2
  convert h using 1
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
  ring

/-! ## The polynomial `P_z` -/

/-- `P_z(0) = -1` (Appendix A.1). -/
theorem scPoly_eval_zero (N : ℕ) (σ : Fin M → ℝ) (z : ℂ) : (scPoly N σ z).eval 0 = -1 := by
  simp [scPoly, eval_prod]


private lemma poly_eval_scPoly (N : ℕ) (σ : Fin M → ℝ) (z w : ℂ) :
    (scPoly N σ z).eval w = -(∏ s ∈ posVals σ, (1 + (s : ℂ) * w)) +
      w * ∑ s ∈ posVals σ, ((weight N σ s * s : ℝ) : ℂ) *
        ∏ s' ∈ (posVals σ).erase s, (1 + (s' : ℂ) * w) -
      z * w * ∏ s ∈ posVals σ, (1 + (s : ℂ) * w) := by
  simp only [scPoly, eval_sub, eval_add, eval_neg, eval_mul, eval_X, eval_C, eval_prod,
    eval_one, eval_finsetSum]

private lemma poly_sum_group (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (w : ℂ) :
    ∑ i, (σ i : ℂ) / ((N : ℂ) * (1 + (σ i : ℂ) * w)) =
      ∑ s ∈ posVals σ, ((weight N σ s * s : ℝ) : ℂ) / (1 + (s : ℂ) * w) := by
  set g : ℝ → ℂ := fun a => (a : ℂ) / ((N : ℂ) * (1 + (a : ℂ) * w)) with hg
  have h1 : ∑ i, g (σ i) = ∑ i ∈ Finset.univ.filter (fun i => 0 < σ i), g (σ i) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases (hσ i).eq_or_lt with h0 | hpos
    · rw [← h0]; simp [hg]
    · simp [hpos]
  have hmaps : ∀ i ∈ Finset.univ.filter (fun i => 0 < σ i), σ i ∈ posVals σ := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp [posVals, hi]
  change ∑ i, g (σ i) = _
  rw [h1, ← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs0 : 0 < s := (Finset.mem_filter.mp hs).2
  have hset : (Finset.univ.filter (fun i => 0 < σ i)).filter (fun i => σ i = s) =
      Finset.univ.filter (fun i => σ i = s) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨h ▸ hs0, h⟩
  rw [hset, Finset.sum_congr rfl (g := fun _ => g s)
      (fun i hi => by rw [(Finset.mem_filter.mp hi).2]),
    Finset.sum_const, nsmul_eq_mul]
  simp only [hg, weight]
  push_cast
  rw [div_mul_eq_div_div]
  ring

/-- `P_z(w) = w Π_s (1 + s w) (f(w) - z)` for `σ ≥ 0` and `w` not a pole (Appendix A.1). -/
theorem scPoly_eval (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (z : ℂ) {w : ℂ} (hw : w ≠ 0)
    (hw' : ∀ s ∈ posVals σ, 1 + (s : ℂ) * w ≠ 0) :
    (scPoly N σ z).eval w = w * (∏ s ∈ posVals σ, (1 + (s : ℂ) * w)) * (fC N σ w - z) := by
  have hf : fC N σ w =
      -w⁻¹ + ∑ s ∈ posVals σ, ((weight N σ s * s : ℝ) : ℂ) / (1 + (s : ℂ) * w) := by
    unfold fC
    rw [poly_sum_group N σ hσ w]
  have hterm : ∀ s ∈ posVals σ, (∏ t ∈ posVals σ, (1 + (t : ℂ) * w)) *
      (((weight N σ s * s : ℝ) : ℂ) / (1 + (s : ℂ) * w)) =
      ((weight N σ s * s : ℝ) : ℂ) * ∏ s' ∈ (posVals σ).erase s, (1 + (s' : ℂ) * w) := by
    intro s hs
    rw [← Finset.mul_prod_erase _ _ hs]
    field_simp [hw' s hs]
  rw [poly_eval_scPoly, hf]
  have : (∏ t ∈ posVals σ, (1 + (t : ℂ) * w)) *
      ∑ s ∈ posVals σ, ((weight N σ s * s : ℝ) : ℂ) / (1 + (s : ℂ) * w) =
      ∑ s ∈ posVals σ, ((weight N σ s * s : ℝ) : ℂ) *
        ∏ s' ∈ (posVals σ).erase s, (1 + (s' : ℂ) * w) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hterm
  have hinv : w * w⁻¹ = 1 := mul_inv_cancel₀ hw
  linear_combination (∏ t ∈ posVals σ, (1 + (t : ℂ) * w)) * hinv - w * this

/-- `P_z` does not vanish at a pole `-1/s`, `s` a positive value of `σ` (Appendix A.1). -/
theorem scPoly_eval_pole (N : ℕ) (σ : Fin M → ℝ) (hN : 0 < N) (z : ℂ) {s : ℝ}
    (hs : s ∈ posVals σ) : (scPoly N σ z).eval (-((s : ℂ))⁻¹) ≠ 0 := by
  have hs0 : 0 < s := (Finset.mem_filter.mp hs).2
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hP : ∏ t ∈ posVals σ, (1 + (t : ℂ) * (-((s : ℂ))⁻¹)) = 0 := by
    refine Finset.prod_eq_zero hs ?_
    field_simp
    ring
  have hsum : ∑ t ∈ posVals σ, ((weight N σ t * t : ℝ) : ℂ) *
        ∏ s' ∈ (posVals σ).erase t, (1 + (s' : ℂ) * (-((s : ℂ))⁻¹)) =
      ((weight N σ s * s : ℝ) : ℂ) *
        ∏ s' ∈ (posVals σ).erase s, (1 + (s' : ℂ) * (-((s : ℂ))⁻¹)) := by
    refine Finset.sum_eq_single s (fun t ht hts => ?_) (fun h => absurd hs h)
    have hmem : s ∈ (posVals σ).erase t := Finset.mem_erase.mpr ⟨hts.symm, hs⟩
    rw [Finset.prod_eq_zero hmem (by field_simp; ring), mul_zero]
  rw [poly_eval_scPoly, hP, hsum]
  simp only [neg_zero, zero_add, mul_zero, sub_zero]
  have hw : weight N σ s ≠ 0 := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hs).1
    unfold weight
    have hc : 0 < (Finset.univ.filter fun j => σ j = s).card :=
      Finset.card_pos.mpr ⟨i, by simp [hi]⟩
    have : (0 : ℝ) < ((Finset.univ.filter fun j => σ j = s).card : ℝ) / N := by
      positivity
    exact this.ne'
  refine mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero hsC)) (mul_ne_zero ?_ ?_)
  · exact_mod_cast mul_ne_zero hw hs0.ne'
  · refine Finset.prod_ne_zero_iff.mpr fun t ht => ?_
    have htne : t ≠ s := (Finset.mem_erase.mp ht).1
    intro h
    apply htne
    have : (t : ℂ) = s := by
      field_simp at h
      linear_combination -h
    exact_mod_cast this


/-! ## Concrete instance (Marchenko–Pastur: `M = 1`, `N = 2`, `σ = 1`) -/

example : HasDerivAt (fC 2 (fun _ : Fin 1 => (1 : ℝ)))
    (fCDeriv 2 (fun _ : Fin 1 => (1 : ℝ)) Complex.I) Complex.I :=
  hasDerivAt_fC 2 _ Complex.I_ne_zero (fun i => by
    simp only [Complex.ofReal_one, one_mul]
    intro h
    have := congrArg Complex.re h
    simp at this)

/-- MP: `f'(i) = -1 + i/4`. -/
example : fCDeriv 2 (fun _ : Fin 1 => (1 : ℝ)) Complex.I = ⟨-1, 1 / 4⟩ := by
  have h : (1 + Complex.I) ^ 2 = 2 * Complex.I := by
    ring_nf
    rw [Complex.I_sq]
    ring
  apply Complex.ext
  · simp [fCDeriv, h, Complex.inv_re, Complex.normSq]
  · simp [fCDeriv, h, Complex.inv_im, Complex.normSq]
    norm_num

example : (scPoly 2 (fun _ : Fin 1 => (1 : ℝ)) Complex.I).eval 0 = -1 :=
  scPoly_eval_zero 2 _ Complex.I

end Anisotropic
