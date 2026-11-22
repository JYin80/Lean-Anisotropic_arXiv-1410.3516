module

public import Anisotropic.Density.Count
public import Anisotropic.Density.Critical
public import Anisotropic.Density.GenProp
public import Anisotropic.Density.Ordering
public import Anisotropic.Density.SelfConsistent
public import Anisotropic.Density.Structure
public import Anisotropic.Density.Varrho

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # Marchenko–Pastur facts at `σ ≡ 1` on `Fin n`, `N = 2n` (`φ = ½`): one band, the edges, regularity of the top edge at `τ = 1/5` and bulk regularity with `c t = min t 1 / 50` -/

/-! ## The explicit critical points and edges

With `σ ≡ 1` on `Fin n` and `N = 2n`, (def_fx) reads `f(x) = -1/x + 1/(2(1+x))`. The finite
critical point in `I_1` is `x_1 = √2 - 2`, the one in `I_0` is `x_2 = 1/y_2` with
`y_2 = √2/2 - 1`, and the edges are `a_1 = 3/2 + √2`, `a_2 = 3/2 - √2` (Lemmas 2.4, 2.5). -/

private lemma marchenkoPastur_hσ (n : ℕ) : ∀ i, 0 ≤ (fun _ : Fin n => (1 : ℝ)) i :=
  fun _ => zero_le_one

private lemma marchenkoPastur_posVals {n : ℕ} (hn : 0 < n) :
    posVals (fun _ : Fin n => (1 : ℝ)) = {1} := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  rw [posVals, Finset.image_const hne, Finset.filter_singleton]
  simp

private lemma marchenkoPastur_weight {n : ℕ} (hn : 0 < n) :
    weight (2 * n) (fun _ : Fin n => (1 : ℝ)) 1 = 1 / 2 := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  simp [weight]
  field_simp

private lemma marchenkoPastur_nonempty {n : ℕ} (hn : 0 < n) :
    (posVals (fun _ : Fin n => (1 : ℝ))).Nonempty := by
  rw [marchenkoPastur_posVals hn]
  exact Finset.singleton_nonempty 1

private lemma marchenkoPastur_numBands {n : ℕ} (hn : 0 < n) :
    numBands (2 * n) (fun _ : Fin n => (1 : ℝ)) = 1 := by
  have hc := card_innerCrit (2 * n) _ (marchenkoPastur_hσ n) (by omega)
    (marchenkoPastur_nonempty hn)
  have hdeg : (critPoly (2 * n) (fun _ : Fin n => (1 : ℝ))).natDegree ≤ 2 := by
    simp only [critPoly, marchenkoPastur_posVals hn, Finset.prod_singleton,
      Finset.sum_singleton, Finset.erase_singleton, Finset.prod_empty,
      marchenkoPastur_weight hn]
    compute_degree!
  have hle : Multiset.card (innerCrit (2 * n) (fun _ : Fin n => (1 : ℝ))) ≤ 2 :=
    (Multiset.card_le_card (Multiset.filter_le _ _)).trans
      ((Polynomial.card_roots' _).trans hdeg)
  omega

/-- The critical point `x_1` satisfies `x_1 < 0`, `1 + x_1 > 0` and `2(1 + x_1)² = x_1²`. -/
private lemma marchenkoPastur_xCrit {n : ℕ} (hn : 0 < n) :
    xCrit (2 * n) (fun _ : Fin n => (1 : ℝ)) 1 < 0 ∧
      0 < 1 + xCrit (2 * n) (fun _ : Fin n => (1 : ℝ)) 1 ∧
      2 * (1 + xCrit (2 * n) (fun _ : Fin n => (1 : ℝ)) 1) ^ 2 =
        xCrit (2 * n) (fun _ : Fin n => (1 : ℝ)) 1 ^ 2 := by
  have hc := (card_innerCrit (2 * n) _ (marchenkoPastur_hσ n) (by omega)
    (marchenkoPastur_nonempty hn)).1
  rw [marchenkoPastur_numBands hn] at hc
  obtain ⟨x, hx⟩ := Multiset.card_eq_one.mp (by omega :
    Multiset.card (innerCrit (2 * n) (fun _ : Fin n => (1 : ℝ))) = 1)
  have hxc : xCrit (2 * n) (fun _ : Fin n => (1 : ℝ)) 1 = x := by
    simp [xCrit, marchenkoPastur_numBands hn, hx]
  have hm : x ∈ innerCrit (2 * n) (fun _ : Fin n => (1 : ℝ)) := by
    rw [hx]; exact Multiset.mem_singleton_self x
  rw [hxc]
  unfold innerCrit at hm
  rw [Multiset.mem_filter, Polynomial.mem_roots'] at hm
  obtain ⟨⟨-, hroot⟩, hx0, s, hs, h1⟩ := hm
  rw [marchenkoPastur_posVals hn, Finset.mem_singleton] at hs
  subst hs
  have h0 : (critPoly (2 * n) (fun _ : Fin n => (1 : ℝ))).eval x = 0 := hroot
  simp only [critPoly, marchenkoPastur_posVals hn, Finset.prod_singleton, Finset.sum_singleton,
    Finset.erase_singleton, Finset.prod_empty, marchenkoPastur_weight hn, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_one,
    Polynomial.eval_C, Polynomial.eval_X] at h0
  refine ⟨hx0, by linarith, by linarith⟩

/-- The chart point `y_2` satisfies `1 + y_2 > 0` and `2(1 + y_2)² = 1`. -/
private lemma marchenkoPastur_yEdge {n : ℕ} (hn : 0 < n) :
    0 < 1 + yEdge (2 * n) (fun _ : Fin n => (1 : ℝ)) ∧
      2 * (1 + yEdge (2 * n) (fun _ : Fin n => (1 : ℝ))) ^ 2 = 1 := by
  obtain ⟨hin, h1⟩ := yEdge_spec (2 * n) _ (marchenkoPastur_hσ n) (by omega)
    (marchenkoPastur_nonempty hn)
  have hy := hin 1 (by rw [marchenkoPastur_posVals hn]; exact Finset.mem_singleton_self 1)
  simp only [FChart1, marchenkoPastur_posVals hn, Finset.sum_singleton,
    marchenkoPastur_weight hn] at h1
  refine ⟨by linarith, ?_⟩
  have hne : yEdge (2 * n) (fun _ : Fin n => (1 : ℝ)) + 1 ≠ 0 := hy.ne'
  field_simp at h1
  linarith

/-- `x_1 = √2 - 2`. -/
private lemma marchenkoPastur_xCrit_eq {n : ℕ} (hn : 0 < n) :
    xCrit (2 * n) (fun _ : Fin n => (1 : ℝ)) 1 = Real.sqrt 2 - 2 := by
  obtain ⟨-, hx1, hx2⟩ := marchenkoPastur_xCrit hn
  set x := xCrit (2 * n) (fun _ : Fin n => (1 : ℝ)) 1
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 2 := by positivity
  have h : (Real.sqrt 2 * (1 + x) + x) * (Real.sqrt 2 * (1 + x) - x) = 0 := by
    linear_combination (1 + x) ^ 2 * hs2 + hx2
  rcases mul_eq_zero.mp h with h | h
  · linear_combination (Real.sqrt 2 - 1) * h - (1 + x) * hs2
  · nlinarith [mul_pos hs0 hx1]

/-- `a_1 = 3/2 + √2`. -/
private lemma marchenkoPastur_edgeVal_one {n : ℕ} (hn : 0 < n) :
    edgeVal (2 * n) (fun _ : Fin n => (1 : ℝ)) 1 = 3 / 2 + Real.sqrt 2 := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h1 : Real.sqrt 2 - 2 ≠ 0 := by nlinarith
  have h2 : 1 + (Real.sqrt 2 - 2) ≠ 0 := by nlinarith
  simp only [edgeVal, marchenkoPastur_numBands hn, fR, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, one_mul,
    show ¬((1 : ℕ) = 2 * 1) by norm_num, ↓reduceIte, marchenkoPastur_xCrit_eq hn]
  field_simp
  linear_combination (3 - 2 * Real.sqrt 2) * hs2

/-- `y_2 = √2/2 - 1`. -/
private lemma marchenkoPastur_yEdge_eq {n : ℕ} (hn : 0 < n) :
    yEdge (2 * n) (fun _ : Fin n => (1 : ℝ)) = Real.sqrt 2 / 2 - 1 := by
  obtain ⟨hy1, hy2⟩ := marchenkoPastur_yEdge hn
  set y := yEdge (2 * n) (fun _ : Fin n => (1 : ℝ))
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 2 := by positivity
  have h : (Real.sqrt 2 * (1 + y) - 1) * (Real.sqrt 2 * (1 + y) + 1) = 0 := by
    linear_combination (1 + y) ^ 2 * hs2 + hy2
  rcases mul_eq_zero.mp h with h | h
  · linear_combination (Real.sqrt 2 / 2) * h - ((1 + y) / 2) * hs2
  · nlinarith [mul_pos hs0 hy1]

/-- `a_2 = 3/2 - √2`. -/
private lemma marchenkoPastur_edgeVal_two {n : ℕ} (hn : 0 < n) :
    edgeVal (2 * n) (fun _ : Fin n => (1 : ℝ)) 2 = 3 / 2 - Real.sqrt 2 := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 2 := by positivity
  have h1 : Real.sqrt 2 / 2 - 1 + 1 ≠ 0 := by rw [sub_add_cancel]; positivity
  simp only [edgeVal, marchenkoPastur_numBands hn, mul_one, ↓reduceIte, FChart,
    marchenkoPastur_posVals hn, Finset.sum_singleton, marchenkoPastur_weight hn,
    marchenkoPastur_yEdge_eq hn]
  field_simp
  linear_combination (1 : ℝ) * hs2

/-- The equation `z m² + (z + ½) m + 1 = 0` for `m = m(E + i0)`, `E ≠ 0`. -/
private lemma marchenkoPastur_sc {n : ℕ} (hn : 0 < n) {E : ℝ} (hE : E ≠ 0) :
    (E : ℂ) * mExt (2 * n) (fun _ : Fin n => (1 : ℝ)) E ^ 2 +
      ((E : ℂ) + 1 / 2) * mExt (2 * n) (fun _ : Fin n => (1 : ℝ)) E + 1 = 0 := by
  have h := scPoly_eval_mExt (2 * n) _ (marchenkoPastur_hσ n) hE
  simp only [scPoly, marchenkoPastur_posVals hn, Finset.prod_singleton, Finset.sum_singleton,
    Finset.erase_singleton, Finset.prod_empty, marchenkoPastur_weight hn, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_add, Polynomial.eval_one,
    Polynomial.eval_C, Polynomial.eval_X] at h
  push_cast at h
  linear_combination -h

/-- On `[a_2 + t, a_1 - t]`, `t > 0`: `min(t, 1)/50 ≤ ρ(E) = π⁻¹ Im m(E + i0)`. With
`m(E + i0) = u + iv`, `v > 0`, the equation gives `4E²v² = (a_1 - E)(E - a_2) ≥ √2 t`. -/
private lemma marchenkoPastur_rhoDens_ge {n : ℕ} (hn : 0 < n) {t E : ℝ} (ht : 0 < t)
    (hE1 : 3 / 2 - Real.sqrt 2 + t ≤ E) (hE2 : E ≤ 3 / 2 + Real.sqrt 2 - t) :
    min t 1 / 50 ≤ rhoDens (2 * n) (fun _ : Fin n => (1 : ℝ)) E := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 2 := by positivity
  have hsl : 1.4 < Real.sqrt 2 := by nlinarith
  have hsu : Real.sqrt 2 < 1.42 := by nlinarith
  have hE0 : 0 < E := by linarith
  have hsc := marchenkoPastur_sc hn hE0.ne'
  have hv0 := im_mExt_nonneg (2 * n) _ (marchenkoPastur_hσ n) hE0.ne'
  set w := mExt (2 * n) (fun _ : Fin n => (1 : ℝ)) E
  have hre := congrArg Complex.re hsc
  have him := congrArg Complex.im hsc
  simp only [sq, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re, Complex.add_im, Complex.mul_im, Complex.one_im, Complex.zero_re,
    Complex.zero_im, Complex.div_ofNat_re, Complex.div_ofNat_im] at hre him
  set u := w.re
  set v := w.im
  set D := (3 / 2 + Real.sqrt 2 - E) * (E - (3 / 2 - Real.sqrt 2)) with hD_def
  have hD : 4 * E - (E + 1 / 2) ^ 2 = D := by
    rw [hD_def]
    linear_combination -hs2
  have hDt : t * Real.sqrt 2 ≤ D := by
    have h1 : 0 ≤ 3 / 2 + Real.sqrt 2 - E - t := by linarith
    have h2 : 0 ≤ E - (3 / 2 - Real.sqrt 2) - t := by linarith
    have h3 : 0 ≤ Real.sqrt 2 - t := by linarith
    nlinarith [mul_nonneg h1 h2, mul_nonneg ht.le h3]
  have hv : 0 < v := by
    rcases hv0.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at hre
      nlinarith [sq_nonneg (2 * E * u + E + 1 / 2)]
  have hu : 2 * E * u + E + 1 / 2 = 0 := by
    have h : v * (2 * E * u + E + 1 / 2) = 0 := by linear_combination him
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hv.ne'
    · exact h
  have hv2 : 4 * E ^ 2 * v ^ 2 = D := by
    linear_combination (-(4 : ℝ) * E) * hre + (2 * E * u + E + 1 / 2) * hu + hD
  have hm0 : 0 < min t 1 := lt_min ht one_pos
  have hm2 : min t 1 ^ 2 ≤ t := by
    nlinarith [min_le_left t 1, min_le_right t 1]
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have hpi2 : Real.pi ^ 2 ≤ 10 := by nlinarith
  have hE2' : E ^ 2 ≤ 9 := by nlinarith
  have hlhs : (min t 1 * Real.pi) ^ 2 ≤ 10 * t := by
    rw [mul_pow]
    nlinarith [sq_nonneg (min t 1), sq_nonneg Real.pi]
  have hrhs : 1.4 * t ≤ 36 * v ^ 2 := by
    nlinarith [sq_nonneg v, mul_nonneg (sq_nonneg v) (by linarith : (0 : ℝ) ≤ 9 - E ^ 2)]
  rw [rhoDens, le_div_iff₀ hpi0]
  refine (pow_le_pow_iff_left₀ (by positivity) hv.le two_ne_zero).mp ?_
  nlinarith

/-! ## The statements

`p = 1` (Lemma 2.4), `a_2 < 1/10` (Lemma 2.5), the edge `a_1` is regular in the sense of
Definition 2.7 (i) with `τ = 1/5`, and the bulk component `[a_2, a_1]` is regular in the sense of
Definition 2.7 (ii) with `c_{τ,τ'} = min(τ', 1)/50`. -/

theorem numBands_mp {n : ℕ} (hn : 0 < n) : numBands (2 * n) (fun _ : Fin n => (1 : ℝ)) = 1 :=
  marchenkoPastur_numBands hn

theorem edgeVal_mp_two_lt {n : ℕ} (hn : 0 < n) :
    edgeVal (2 * n) (fun _ : Fin n => (1 : ℝ)) 2 < 1 / 10 := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 2 := by positivity
  rw [marchenkoPastur_edgeVal_two hn]
  nlinarith

theorem regularEdge_mp {n : ℕ} (hn : 0 < n) :
    RegularEdge (1 / 5) (2 * n) (fun _ : Fin n => (1 : ℝ)) 1 := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 2 := by positivity
  have hsl : 1.4 < Real.sqrt 2 := by nlinarith
  refine ⟨le_rfl, by rw [marchenkoPastur_numBands hn]; norm_num, ?_, ?_, ?_⟩
  · rw [marchenkoPastur_edgeVal_one hn]
    linarith
  · intro l hl1 hl2 hl
    rw [marchenkoPastur_numBands hn] at hl2
    obtain rfl : l = 2 := by omega
    rw [marchenkoPastur_edgeVal_one hn, marchenkoPastur_edgeVal_two hn,
      abs_of_pos (by linarith)]
    linarith
  · intro _ s hs
    rw [marchenkoPastur_posVals hn, Finset.mem_singleton] at hs
    subst hs
    rw [marchenkoPastur_xCrit_eq hn, inv_one, abs_of_pos (by linarith)]
    linarith

theorem regularBulk_mp {n : ℕ} (hn : 0 < n) :
    RegularBulk (fun t => min t 1 / 50) (2 * n) (fun _ : Fin n => (1 : ℝ)) 1 := by
  refine ⟨le_rfl, by rw [marchenkoPastur_numBands hn], fun t ht => ⟨?_, fun E hE => ?_⟩⟩
  · exact div_pos (lt_min ht one_pos) (by norm_num)
  · rw [show 2 * 1 = 2 from rfl, show 2 * 1 - 1 = 1 from rfl, marchenkoPastur_edgeVal_two hn,
      marchenkoPastur_edgeVal_one hn] at hE
    exact marchenkoPastur_rhoDens_ge hn ht hE.1 hE.2

/-! ## Instances at `n = 3` (`M = 3`, `N = 6`) -/

example : numBands (2 * 3) (fun _ : Fin 3 => (1 : ℝ)) = 1 := numBands_mp (by norm_num)

example : edgeVal (2 * 3) (fun _ : Fin 3 => (1 : ℝ)) 2 < 1 / 10 :=
  edgeVal_mp_two_lt (by norm_num)

example : RegularEdge (1 / 5) (2 * 3) (fun _ : Fin 3 => (1 : ℝ)) 1 :=
  regularEdge_mp (by norm_num)

example : RegularBulk (fun t => min t 1 / 50) (2 * 3) (fun _ : Fin 3 => (1 : ℝ)) 1 :=
  regularBulk_mp (by norm_num)

#print axioms numBands_mp
#print axioms edgeVal_mp_two_lt
#print axioms regularEdge_mp
#print axioms regularBulk_mp

end Anisotropic
