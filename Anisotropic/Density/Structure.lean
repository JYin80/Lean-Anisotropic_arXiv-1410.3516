module

public import Anisotropic.Density.Ordering
public import Anisotropic.Density.Varrho

@[expose] public section

/-!
# `x_k = m(a_k)` and the structure of `ϱ`

Lemma 2.5: `m(a_k) = x_k` for every finite critical point `x_k`, and `1/m(z) → 0` as `z → 0` in
`ℂ₊` when `x_{2p} = ∞`, i.e. `φ π((0, ∞)) = 1` (the convention `m(0) = ∞`). Lemma 2.6, (rho_supp):
`supp ϱ ∩ (0, ∞)` is the union of the bands `[a_{2k}, a_{2k-1}]` intersected with `(0, ∞)`, the
density of `ϱ` is positive on the open bands, and `ϱ` vanishes outside `[0, a_1]`.

Proofs (Appendix A). The shape of `f` on `I_1, …, I_n, I_0` from Lemma 2.4 gives: `f' > 0` exactly
on `(x_1, 0)`, on `(x_{2j+1}, x_{2j})` and at the points `1/y` of `I_0` with `y > y_{2p}`, so the
values of `f` at points with `f' > 0` lie in the gaps `(a_1, ∞)`, `(a_{2j+1}, a_{2j})` and
`(-∞, a_{2p})`. On a gap `m(E)` is real by the sign lemma `f' > 0`, so the density vanishes; in an
open band a real `m(E)` would be a root of `P_E` with `f' < 0` (excluded by the sign lemma), with
`f' = 0` (a critical value), or with `f' > 0` (a gap value). At a nondegenerate critical point
`x_k`, `m(f(x)) = x` on the side where `f' > 0` and continuity of `m` give `m(a_k) = x_k`; at a
degenerate one, `x_k` is a triple root of `P_{a_k}` and the `n - 2` default roots fill the degree
`n + 1`, so every root of `P_{a_k}` is real and `m(a_k) = x_k` by the sign lemmas and the root
budget. For `φ π((0, ∞)) = 1`, a finite limit point `w` of `m(z)` as `z → 0` is a root of `P_0`,
real since `Re f > 0` where `Im f = 0` on `ℂ₊`, and `x² f'(x) = -Σ_s r_s (1 + s x)⁻² < 0` at a real
root of `f`, which contradicts `Im f(m(z)) = Im z > 0`.
-/

open MeasureTheory Polynomial Filter Topology
open scoped ENNReal

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! ## The functions `f^t` -/

/-- `g(x) = Σ_s r_s s / (1 + s x)`, so that `f(x) = -1/x + g(x)`. -/
private def strG (N : ℕ) (σ : Fin M → ℝ) (x : ℝ) : ℝ :=
  ∑ s ∈ posVals σ, weight N σ s * s / (1 + s * x)

/-- `f^t(x) = -1/x + t g(x)`; `f^1 = f`. -/
private def strF (N : ℕ) (σ : Fin M → ℝ) (t x : ℝ) : ℝ := -x⁻¹ + t * strG N σ x

/-- `G(x) = Σ_s r_s s² / (1 + s x)²`. -/
private def strH (N : ℕ) (σ : Fin M → ℝ) (x : ℝ) : ℝ :=
  ∑ s ∈ posVals σ, weight N σ s * s ^ 2 / (1 + s * x) ^ 2

/-- `(f^t)'(x) = 1/x² - t G(x)`. -/
private def strF1 (N : ℕ) (σ : Fin M → ℝ) (t x : ℝ) : ℝ := (x ^ 2)⁻¹ - t * strH N σ x

private lemma str_sum_group (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (g : ℝ → ℝ) (hg : g 0 = 0) :
    ∑ i, g (σ i) =
      ∑ s ∈ posVals σ, ((Finset.univ.filter fun i => σ i = s).card : ℝ) * g s := by
  have h1 : ∑ i, g (σ i) = ∑ i ∈ Finset.univ.filter (fun i => 0 < σ i), g (σ i) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases (hσ i).eq_or_lt with h0 | hpos
    · rw [← h0, hg]; simp
    · simp [hpos]
  have hmaps : ∀ i ∈ Finset.univ.filter (fun i => 0 < σ i), σ i ∈ posVals σ := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp [posVals, hi]
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

private lemma str_sum_pow (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {k : ℕ} (hk : 0 < k)
    (x : ℝ) :
    ∑ i, σ i ^ k / ((N : ℝ) * (1 + σ i * x) ^ k) =
      ∑ s ∈ posVals σ, weight N σ s * s ^ k / (1 + s * x) ^ k := by
  rw [str_sum_group σ hσ (fun a => a ^ k / ((N : ℝ) * (1 + a * x) ^ k))
    (by simp [zero_pow hk.ne'])]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [weight, div_eq_mul_inv, mul_inv]
  ring

private lemma str_fR_eq (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) :
    fR N σ = strF N σ 1 := by
  funext x
  have h := str_sum_pow N σ hσ (k := 1) one_pos x
  simp only [pow_one] at h
  rw [fR, h, strF, strG, one_mul]

private lemma str_fR1_eq (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) :
    fR1 N σ = strF1 N σ 1 := by
  funext x
  rw [fR1, str_sum_pow N σ hσ (k := 2) two_pos x, strF1, strH, one_mul]

private lemma str_pos_of_mem (σ : Fin M → ℝ) {s : ℝ} (hs : s ∈ posVals σ) : 0 < s :=
  (Finset.mem_filter.mp hs).2

private lemma str_weight_pos (N : ℕ) (σ : Fin M → ℝ) (hN : 0 < N) {s : ℝ}
    (hs : s ∈ posVals σ) : 0 < weight N σ s := by
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hs).1
  unfold weight
  have hc : 0 < (Finset.univ.filter fun j => σ j = s).card :=
    Finset.card_pos.mpr ⟨i, by simp [hi]⟩
  positivity

private lemma str_nonpole_all (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {x : ℝ}
    (hx : ∀ s ∈ posVals σ, 1 + s * x ≠ 0) : ∀ i, 1 + σ i * x ≠ 0 := by
  intro i
  rcases (hσ i).eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · exact hx (σ i) (by simp [posVals, hpos])

/-- For `s > 0`: `-1/s < x ↔ 0 < 1 + s x`. -/
private lemma str_lt_iff {s x : ℝ} (hs : 0 < s) : -s⁻¹ < x ↔ 0 < 1 + s * x := by
  have e : s * s⁻¹ = 1 := mul_inv_cancel₀ hs.ne'
  constructor
  · intro h
    have := mul_lt_mul_of_pos_left h hs
    rw [mul_neg, e] at this
    linarith
  · intro h
    by_contra h'
    have := mul_le_mul_of_nonneg_left (not_lt.1 h') hs.le
    rw [mul_neg, e] at this
    linarith

/-- For `s > 0`: `x < -1/s ↔ 1 + s x < 0`. -/
private lemma str_gt_iff {s x : ℝ} (hs : 0 < s) : x < -s⁻¹ ↔ 1 + s * x < 0 := by
  have e : s * s⁻¹ = 1 := mul_inv_cancel₀ hs.ne'
  constructor
  · intro h
    have := mul_lt_mul_of_pos_left h hs
    rw [mul_neg, e] at this
    linarith
  · intro h
    by_contra h'
    have := mul_le_mul_of_nonneg_left (not_lt.1 h') hs.le
    rw [mul_neg, e] at this
    linarith

private lemma str_hasDerivAt_term (c s : ℝ) {x : ℝ} (h : 1 + s * x ≠ 0) :
    HasDerivAt (fun y : ℝ => c * s / (1 + s * y)) (-(c * s ^ 2 / (1 + s * x) ^ 2)) x := by
  have h1 : HasDerivAt (fun y : ℝ => 1 + s * y) s x := by
    simpa using ((hasDerivAt_id x).const_mul s).const_add 1
  have h2 := (hasDerivAt_const x (c * s)).fun_div h1 h
  convert h2 using 1
  field_simp
  ring

private lemma str_hasDerivAt_F (N : ℕ) (σ : Fin M → ℝ) (t : ℝ) {x : ℝ} (hx : x ≠ 0)
    (hx' : ∀ s ∈ posVals σ, 1 + s * x ≠ 0) : HasDerivAt (strF N σ t) (strF1 N σ t x) x := by
  have h0 : HasDerivAt (fun y : ℝ => -y⁻¹) ((x ^ 2)⁻¹) x := by
    have := (hasDerivAt_inv hx).neg
    convert this using 1
    ring
  have hs : HasDerivAt (fun y => ∑ s ∈ posVals σ, weight N σ s * s / (1 + s * y))
      (∑ s ∈ posVals σ, -(weight N σ s * s ^ 2 / (1 + s * x) ^ 2)) x :=
    HasDerivAt.fun_sum fun s hs => str_hasDerivAt_term _ _ (hx' s hs)
  have h := h0.add (hs.const_mul t)
  unfold strF strF1 strH strG
  convert h using 1
  rw [Finset.sum_neg_distrib]
  ring

/-! ## The polynomial `P_E` for `f^t` -/

/-- `P^t_E(w) = w Π_s (1 + s w) (f^t(w) - E)` (Appendix A.1, weights `t r_s`). -/
private def strP (N : ℕ) (σ : Fin M → ℝ) (t E : ℝ) : ℝ[X] :=
  -(∏ s ∈ posVals σ, (1 + C s * X)) +
    C t * X * ∑ s ∈ posVals σ, C (weight N σ s * s) *
      ∏ s' ∈ (posVals σ).erase s, (1 + C s' * X) -
    C E * X * ∏ s ∈ posVals σ, (1 + C s * X)

private lemma str_eval_P (N : ℕ) (σ : Fin M → ℝ) (t E : ℝ) {x : ℝ} (hx : x ≠ 0)
    (hx' : ∀ s ∈ posVals σ, 1 + s * x ≠ 0) :
    (strP N σ t E).eval x = x * (∏ s ∈ posVals σ, (1 + s * x)) * (strF N σ t x - E) := by
  have hev : (strP N σ t E).eval x = -(∏ s ∈ posVals σ, (1 + s * x)) +
      t * x * ∑ s ∈ posVals σ, weight N σ s * s * ∏ s' ∈ (posVals σ).erase s, (1 + s' * x) -
      E * x * ∏ s ∈ posVals σ, (1 + s * x) := by
    simp only [strP, eval_sub, eval_add, eval_neg, eval_mul, eval_X, eval_C, eval_prod,
      eval_one, eval_finsetSum]
  have hterm : ∀ s ∈ posVals σ, (∏ u ∈ posVals σ, (1 + u * x)) *
      (weight N σ s * s / (1 + s * x)) =
      weight N σ s * s * ∏ s' ∈ (posVals σ).erase s, (1 + s' * x) := by
    intro s hs
    rw [← Finset.mul_prod_erase _ _ hs]
    have := hx' s hs
    field_simp
  have hsum : (∏ u ∈ posVals σ, (1 + u * x)) * strG N σ x =
      ∑ s ∈ posVals σ, weight N σ s * s * ∏ s' ∈ (posVals σ).erase s, (1 + s' * x) := by
    unfold strG
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hterm
  rw [hev, ← hsum]
  unfold strF
  have hinv : x * x⁻¹ = 1 := mul_inv_cancel₀ hx
  linear_combination (∏ u ∈ posVals σ, (1 + u * x)) * hinv

private lemma str_P_ne_zero (N : ℕ) (σ : Fin M → ℝ) (t E : ℝ) : strP N σ t E ≠ 0 := by
  intro h
  have : (strP N σ t E).eval 0 = -1 := by simp [strP, eval_prod]
  rw [h] at this
  simp at this

private lemma str_natDegree_prod_le (S : Finset ℝ) :
    natDegree (∏ s ∈ S, (1 + C s * X : ℝ[X])) ≤ S.card := by
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ s ∈ S, natDegree (1 + C s * X : ℝ[X]) ≤ ∑ _s ∈ S, 1 :=
        Finset.sum_le_sum fun s _ => by compute_degree
    _ = S.card := by simp

/-- `deg P^t_E ≤ n + 1`, and `deg P^t_0 ≤ n`. -/
private lemma str_natDegree_P (N : ℕ) (σ : Fin M → ℝ) (t E : ℝ) :
    (strP N σ t E).natDegree ≤ (posVals σ).card + 1 ∧
      (E = 0 → (strP N σ t E).natDegree ≤ (posVals σ).card) := by
  have h1 := str_natDegree_prod_le (posVals σ)
  have hsum : natDegree (∑ s ∈ posVals σ, C (weight N σ s * s) *
      ∏ s' ∈ (posVals σ).erase s, (1 + C s' * X)) ≤ (posVals σ).card - 1 := by
    refine natDegree_sum_le_of_forall_le _ _ fun s hs => ?_
    refine (natDegree_C_mul_le _ _).trans ?_
    refine (str_natDegree_prod_le _).trans ?_
    rw [Finset.card_erase_of_mem hs]
  have h2 : natDegree (C t * X * ∑ s ∈ posVals σ, C (weight N σ s * s) *
      ∏ s' ∈ (posVals σ).erase s, (1 + C s' * X)) ≤ (posVals σ).card := by
    by_cases h0 : (posVals σ).card = 0
    · have : posVals σ = ∅ := Finset.card_eq_zero.mp h0
      simp [this]
    · rw [mul_assoc]
      refine (natDegree_C_mul_le _ _).trans ?_
      have h := natDegree_mul_le_of_le (p := (X : ℝ[X])) natDegree_X_le hsum
      calc _ ≤ 1 + ((posVals σ).card - 1) := h
        _ = (posVals σ).card := by omega
  have h12 : natDegree (-(∏ s ∈ posVals σ, (1 + C s * X)) +
      C t * X * ∑ s ∈ posVals σ, C (weight N σ s * s) *
        ∏ s' ∈ (posVals σ).erase s, (1 + C s' * X)) ≤ (posVals σ).card :=
    natDegree_add_le_of_degree_le (by rw [natDegree_neg]; exact h1) h2
  have h3 : natDegree (C E * X * ∏ s ∈ posVals σ, (1 + C s * X)) ≤ (posVals σ).card + 1 := by
    refine natDegree_mul_le_of_le (m := 1) ?_ h1 |>.trans (by omega)
    exact (natDegree_C_mul_le _ _).trans natDegree_X_le
  refine ⟨?_, fun hE => ?_⟩
  · unfold strP
    exact (natDegree_sub_le_of_le h12 h3).trans (max_le (by omega) le_rfl)
  · subst hE
    unfold strP
    rw [C_0, zero_mul, zero_mul, sub_zero]
    exact h12

/-! ## Root budget -/

private lemma str_sum_count_le (m : Multiset ℝ) (T : Finset ℝ) :
    ∑ x ∈ T, m.count x ≤ Multiset.card m := by
  calc ∑ x ∈ T, m.count x = ∑ x ∈ T, (m.filter (· ∈ T)).count x :=
        Finset.sum_congr rfl fun x hx => by rw [Multiset.count_filter_of_pos hx]
    _ = Multiset.card (m.filter (· ∈ T)) :=
        Multiset.sum_count_eq_card fun x hx => (Multiset.mem_filter.1 hx).2
    _ ≤ Multiset.card m := Multiset.card_le_card (Multiset.filter_le _ _)

/-- The root budget: the root multiplicities of a polynomial over any finite set of points sum
to at most its degree. -/
private lemma str_budget (P : ℝ[X]) (T : Finset ℝ) :
    ∑ x ∈ T, P.rootMultiplicity x ≤ P.natDegree := by
  calc ∑ x ∈ T, P.rootMultiplicity x = ∑ x ∈ T, P.roots.count x :=
        Finset.sum_congr rfl fun x _ => by rw [count_roots]
    _ ≤ Multiset.card P.roots := str_sum_count_le _ _
    _ ≤ P.natDegree := card_roots' P

private lemma str_mult_one (N : ℕ) (σ : Fin M → ℝ) (t E : ℝ) {x : ℝ} (hx : x ≠ 0)
    (hx' : ∀ s ∈ posVals σ, 1 + s * x ≠ 0) (hr : strF N σ t x = E) :
    1 ≤ (strP N σ t E).rootMultiplicity x := by
  have := (rootMultiplicity_pos (str_P_ne_zero N σ t E) (x := x)).2
    (by simp [IsRoot, str_eval_P N σ t E hx hx', hr])
  omega

/-- The first and second derivatives of a polynomial that agrees with `G f₁` near `x`. -/
private lemma str_local_derivs (Q G : ℝ[X]) (f1 f2 : ℝ → ℝ) (f3 : ℝ) {x : ℝ}
    (hQ : ∀ᶠ y in 𝓝 x, Q.eval y = G.eval y * f1 y)
    (h1 : ∀ᶠ y in 𝓝 x, HasDerivAt f1 (f2 y) y) (h2 : HasDerivAt f2 f3 x) :
    (derivative Q).eval x = (derivative G).eval x * f1 x + G.eval x * f2 x ∧
    (derivative (derivative Q)).eval x = (derivative (derivative G)).eval x * f1 x +
      2 * (derivative G).eval x * f2 x + G.eval x * f3 := by
  have hA : ∀ᶠ y in 𝓝 x, (derivative Q).eval y =
      (derivative G).eval y * f1 y + G.eval y * f2 y := by
    filter_upwards [hQ.eventually_nhds, h1] with y hy hy1
    have hd1 : HasDerivAt (fun z => Q.eval z) ((derivative Q).eval y) y := Q.hasDerivAt y
    have hd2 : HasDerivAt (fun z => G.eval z * f1 z)
        ((derivative G).eval y * f1 y + G.eval y * f2 y) y := (G.hasDerivAt y).mul hy1
    have hd3 : HasDerivAt (fun z => Q.eval z)
        ((derivative G).eval y * f1 y + G.eval y * f2 y) y :=
      hd2.congr_of_eventuallyEq hy
    exact hd1.unique hd3
  refine ⟨hA.self_of_nhds, ?_⟩
  have hf1x : HasDerivAt f1 (f2 x) x := h1.self_of_nhds
  have hd : HasDerivAt (fun z => (derivative G).eval z * f1 z + G.eval z * f2 z)
      ((derivative (derivative G)).eval x * f1 x + (derivative G).eval x * f2 x +
        ((derivative G).eval x * f2 x + G.eval x * f3)) x :=
    (((derivative G).hasDerivAt x).mul hf1x).add ((G.hasDerivAt x).mul h2)
  have hd' : HasDerivAt (fun z => (derivative Q).eval z)
      ((derivative (derivative G)).eval x * f1 x + (derivative G).eval x * f2 x +
        ((derivative G).eval x * f2 x + G.eval x * f3)) x :=
    hd.congr_of_eventuallyEq hA
  rw [((derivative Q).hasDerivAt x).unique hd']
  ring

/-- Near a point that is neither `0` nor a pole, `x` stays away from `0` and from every pole. -/
private lemma str_eventually_good (σ : Fin M → ℝ) {x : ℝ} (hx : x ≠ 0)
    (hx' : ∀ s ∈ posVals σ, 1 + s * x ≠ 0) :
    ∀ᶠ y in 𝓝 x, y ≠ 0 ∧ ∀ s ∈ posVals σ, 1 + s * y ≠ 0 := by
  refine (eventually_ne_nhds hx).and ?_
  rw [Filter.eventually_all_finset]
  intro s hs
  have hc : Continuous fun y : ℝ => 1 + s * y := by fun_prop
  exact hc.continuousAt.eventually_ne (hx' s hs)

/-- At a critical point `x` of `f` with `f(x) = E`, `f - E` has a root of order `≥ 2`, and of
order `≥ 3` if also `f''(x) = 0`. -/
private lemma str_mult_crit (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (E : ℝ) {x : ℝ}
    (hx : x ≠ 0) (hx' : ∀ s ∈ posVals σ, 1 + s * x ≠ 0) (hr : fR N σ x = E)
    (h1 : fR1 N σ x = 0) :
    2 ≤ (strP N σ 1 E).rootMultiplicity x ∧
      (fR2 N σ x = 0 → 3 ≤ (strP N σ 1 E).rootMultiplicity x) := by
  set P := strP N σ 1 E with hPdef
  have hP0 : P ≠ 0 := str_P_ne_zero N σ 1 E
  set G : ℝ[X] := X * ∏ s ∈ posVals σ, (1 + C s * X) with hG
  have hGeval : ∀ y : ℝ, G.eval y = y * ∏ s ∈ posVals σ, (1 + s * y) := by
    intro y
    simp [hG, eval_prod]
  have hgood := str_eventually_good σ hx hx'
  have hQloc : ∀ᶠ y in 𝓝 x, P.eval y = G.eval y * (fR N σ y - E) := by
    filter_upwards [hgood] with y hy
    rw [hPdef, str_eval_P N σ 1 E hy.1 hy.2, hGeval, str_fR_eq N σ hσ]
  have h1loc : ∀ᶠ y in 𝓝 x, HasDerivAt (fun z => fR N σ z - E) (fR1 N σ y) y := by
    filter_upwards [hgood] with y hy
    exact (hasDerivAt_fR N σ hy.1 (str_nonpole_all σ hσ hy.2)).sub_const E
  have h2 := hasDerivAt_fR1 N σ hx (str_nonpole_all σ hσ hx')
  obtain ⟨hD1, hD2⟩ := str_local_derivs P G (fun z => fR N σ z - E) (fR1 N σ) (fR2 N σ x)
    hQloc h1loc h2
  have hroot : P.IsRoot x := by
    change P.eval x = 0
    rw [hQloc.self_of_nhds, hr, sub_self, mul_zero]
  have hD1z : (derivative P).IsRoot x := by
    change (derivative P).eval x = 0
    rw [hD1, hr, h1]
    simp
  have key := fun n => lt_rootMultiplicity_iff_isRoot_iterate_derivative (t := x) (n := n) hP0
  refine ⟨?_, fun h2' => ?_⟩
  · have : 1 < P.rootMultiplicity x := by
      rw [key 1]
      intro m hm
      interval_cases m
      · simpa using hroot
      · simpa using hD1z
    omega
  · have hD2z : (derivative (derivative P)).IsRoot x := by
      change (derivative (derivative P)).eval x = 0
      rw [hD2, hr, h1, h2']
      simp
    have : 2 < P.rootMultiplicity x := by
      rw [key 2]
      intro m hm
      interval_cases m
      · simpa using hroot
      · simpa using hD1z
      · simpa using hD2z
    omega

/-! ## The intervals `I_1, …, I_n` and `I_0` -/

/-- The right end of the interval `I_l` with left end `-1/s`: the pole `-1/s'` of the next larger
value `s'`, or `0` when `s = s_1` is the largest value. -/
private def strR (σ : Fin M → ℝ) (s : ℝ) : ℝ :=
  if h : ((posVals σ).filter (fun u => s < u)).Nonempty then
    -(((posVals σ).filter (fun u => s < u)).min' h)⁻¹ else 0

/-- `x ∈ (-1/s, strR s)`, the interval `I_l` with left end `-1/s`. -/
private def strK (σ : Fin M → ℝ) (s x : ℝ) : Prop := -s⁻¹ < x ∧ x < strR σ s

/-- `x ∈ (-∞, -1/s_n) ∪ (0, ∞)`, the finite points of `I_0`. -/
private def strI0 (σ : Fin M → ℝ) (x : ℝ) : Prop := 0 < x ∨ ∀ s ∈ posVals σ, 1 + s * x < 0

private lemma str_ne_max_iff (σ : Fin M → ℝ) (hS : (posVals σ).Nonempty) {s : ℝ}
    (hs : s ∈ posVals σ) :
    ((posVals σ).filter (fun u => s < u)).Nonempty ↔ s ≠ (posVals σ).max' hS := by
  constructor
  · rintro ⟨u, hu⟩ h
    obtain ⟨huS, hsu⟩ := Finset.mem_filter.mp hu
    have := (posVals σ).le_max' u huS
    rw [← h] at this
    linarith
  · intro h
    refine ⟨(posVals σ).max' hS, Finset.mem_filter.mpr ⟨(posVals σ).max'_mem hS, ?_⟩⟩
    exact lt_of_le_of_ne ((posVals σ).le_max' s hs) h

private lemma str_R_max (σ : Fin M → ℝ) (hS : (posVals σ).Nonempty) :
    strR σ ((posVals σ).max' hS) = 0 := by
  unfold strR
  rw [dite_eq_right]
  rw [str_ne_max_iff σ hS ((posVals σ).max'_mem hS)]
  simp

private lemma str_R_next (σ : Fin M → ℝ) (hS : (posVals σ).Nonempty) {s : ℝ}
    (hs : s ∈ posVals σ) (hne : s ≠ (posVals σ).max' hS) :
    ∃ s' ∈ posVals σ, s < s' ∧ (∀ u ∈ posVals σ, ¬ (s < u ∧ u < s')) ∧ strR σ s = -s'⁻¹ := by
  have hA := (str_ne_max_iff σ hS hs).2 hne
  have hm := Finset.min'_mem _ hA
  refine ⟨_, (Finset.mem_filter.mp hm).1, (Finset.mem_filter.mp hm).2, ?_, ?_⟩
  · rintro u hu ⟨h1, h2⟩
    have := Finset.min'_le _ u (Finset.mem_filter.mpr ⟨hu, h1⟩)
    linarith
  · unfold strR
    rw [dite_eq_left hA]

private lemma str_left_lt_R (σ : Fin M → ℝ) (hS : (posVals σ).Nonempty) {s : ℝ}
    (hs : s ∈ posVals σ) : -s⁻¹ < strR σ s := by
  have hs0 := str_pos_of_mem σ hs
  by_cases hmax : s = (posVals σ).max' hS
  · rw [hmax, str_R_max]
    rw [← hmax]
    simpa using hs0
  · obtain ⟨s', hs', hss', -, hR⟩ := str_R_next σ hS hs hmax
    rw [hR]
    have : s'⁻¹ < s⁻¹ := inv_strictAnti₀ hs0 hss'
    linarith

/-- On `I_l = (-1/s, strR s)`: `x < 0`, `1 + u x > 0` for `u ≤ s` and `1 + u x < 0` for `u > s`. -/
private lemma str_K_sign (σ : Fin M → ℝ) (hS : (posVals σ).Nonempty) {s : ℝ}
    (hs : s ∈ posVals σ) {x : ℝ} (hx : strK σ s x) :
    x < 0 ∧ ∀ u ∈ posVals σ, (u ≤ s → 0 < 1 + u * x) ∧ (s < u → 1 + u * x < 0) := by
  have hs0 := str_pos_of_mem σ hs
  have h1 : 0 < 1 + s * x := (str_lt_iff hs0).1 hx.1
  by_cases hmax : s = (posVals σ).max' hS
  · have hR : strR σ s = 0 := by rw [hmax]; exact str_R_max σ hS
    have hx0 : x < 0 := hR ▸ hx.2
    refine ⟨hx0, fun u hu => ⟨fun hus => ?_, fun hsu => ?_⟩⟩
    · have := mul_le_mul_of_nonpos_right hus hx0.le
      linarith
    · have := (posVals σ).le_max' u hu
      rw [← hmax] at this
      linarith
  · obtain ⟨s', hs', hss', hcons, hR⟩ := str_R_next σ hS hs hmax
    have hs'0 := str_pos_of_mem σ hs'
    have h2 : 1 + s' * x < 0 := (str_gt_iff hs'0).1 (hR ▸ hx.2)
    have hx0 : x < 0 := by
      by_contra h
      have := mul_nonneg hs'0.le (not_lt.1 h)
      linarith
    refine ⟨hx0, fun u hu => ⟨fun hus => ?_, fun hsu => ?_⟩⟩
    · have := mul_le_mul_of_nonpos_right hus hx0.le
      linarith
    · have hu' : s' ≤ u := by
        by_contra h
        exact hcons u hu ⟨hsu, lt_of_not_ge h⟩
      have := mul_le_mul_of_nonpos_right hu' hx0.le
      linarith

private lemma str_K_good (σ : Fin M → ℝ) (hS : (posVals σ).Nonempty) {s : ℝ}
    (hs : s ∈ posVals σ) {x : ℝ} (hx : strK σ s x) :
    x ≠ 0 ∧ ∀ u ∈ posVals σ, 1 + u * x ≠ 0 := by
  obtain ⟨hx0, h⟩ := str_K_sign σ hS hs hx
  refine ⟨hx0.ne, fun u hu => ?_⟩
  rcases le_or_gt u s with hus | hsu
  · exact ((h u hu).1 hus).ne'
  · exact ((h u hu).2 hsu).ne

private lemma str_K_disj (σ : Fin M → ℝ) (hS : (posVals σ).Nonempty) {s s' : ℝ}
    (hs : s ∈ posVals σ) (hs' : s' ∈ posVals σ) (hne : s ≠ s') {x : ℝ} (hx : strK σ s x)
    (hx' : strK σ s' x) : False := by
  rcases lt_or_gt_of_ne hne with h | h
  · have a := ((str_K_sign σ hS hs hx).2 s' hs').2 h
    have b := ((str_K_sign σ hS hs' hx').2 s' hs').1 le_rfl
    linarith
  · have a := ((str_K_sign σ hS hs' hx').2 s hs).2 h
    have b := ((str_K_sign σ hS hs hx).2 s hs).1 le_rfl
    linarith

private lemma str_I0_good (σ : Fin M → ℝ) (hS : (posVals σ).Nonempty) {x : ℝ}
    (hx : strI0 σ x) : x ≠ 0 ∧ ∀ u ∈ posVals σ, 1 + u * x ≠ 0 := by
  rcases hx with hx | hx
  · refine ⟨hx.ne', fun u hu => ?_⟩
    have := str_pos_of_mem σ hu
    have : 0 < 1 + u * x := by positivity
    exact this.ne'
  · obtain ⟨s, hs⟩ := hS
    refine ⟨?_, fun u hu => (hx u hu).ne⟩
    rintro rfl
    have := hx s hs
    norm_num at this

/-- Points of `(-1/s_n, 0)` off the poles lie in one of `I_1, …, I_n`. -/
private lemma str_exists_K (σ : Fin M → ℝ) (hS : (posVals σ).Nonempty) {x : ℝ} (hx0 : x < 0)
    (hx' : ∀ u ∈ posVals σ, 1 + u * x ≠ 0) (hin : ∃ s ∈ posVals σ, 0 < 1 + s * x) :
    ∃ s ∈ posVals σ, strK σ s x := by
  have hU : ((posVals σ).filter (fun u => 0 < 1 + u * x)).Nonempty := by
    obtain ⟨s, hs, h⟩ := hin
    exact ⟨s, Finset.mem_filter.mpr ⟨hs, h⟩⟩
  have hm := Finset.max'_mem _ hU
  obtain ⟨hmS, hm1⟩ := Finset.mem_filter.mp hm
  refine ⟨_, hmS, (str_lt_iff (str_pos_of_mem σ hmS)).2 hm1, ?_⟩
  by_cases hmax : ((posVals σ).filter (fun u => 0 < 1 + u * x)).max' hU = (posVals σ).max' hS
  · rw [hmax, str_R_max]
    exact hx0
  · obtain ⟨s', hs', hlt, -, hR⟩ := str_R_next σ hS hmS hmax
    rw [hR]
    apply (str_gt_iff (str_pos_of_mem σ hs')).2
    have hnot : ¬ 0 < 1 + s' * x := by
      intro h
      have := Finset.le_max' ((posVals σ).filter (fun u => 0 < 1 + u * x)) s'
        (Finset.mem_filter.mpr ⟨hs', h⟩)
      linarith
    exact lt_of_le_of_ne (not_lt.1 hnot) (hx' s' hs')

/-! ## Limits of `f^t` -/

private lemma str_tendsto_pole (N : ℕ) (σ : Fin M → ℝ) (hN : 0 < N) {s : ℝ}
    (hs : s ∈ posVals σ) {t : ℝ} (ht : 0 < t) :
    Tendsto (strF N σ t) (𝓝[>] (-s⁻¹)) atTop ∧ Tendsto (strF N σ t) (𝓝[<] (-s⁻¹)) atBot := by
  have hs0 := str_pos_of_mem σ hs
  have ha0 : (-s⁻¹ : ℝ) ≠ 0 := by simp [hs0.ne']
  have hcpos : 0 < t * (weight N σ s * s) := by
    have := str_weight_pos N σ hN hs
    positivity
  have hdec : ∀ y : ℝ, strF N σ t y =
      (-y⁻¹ + t * ∑ u ∈ (posVals σ).erase s, weight N σ u * u / (1 + u * y)) +
        t * (weight N σ s * s) * (1 + s * y)⁻¹ := by
    intro y
    rw [strF, strG, ← Finset.add_sum_erase _ _ hs]
    ring
  have hg : ContinuousAt (fun y : ℝ =>
      -y⁻¹ + t * ∑ u ∈ (posVals σ).erase s, weight N σ u * u / (1 + u * y)) (-s⁻¹) := by
    refine ContinuousAt.add (ContinuousAt.neg (ContinuousAt.inv₀ continuousAt_id ha0)) ?_
    refine ContinuousAt.mul continuousAt_const ?_
    refine tendsto_finsetSum _ fun u hu => ?_
    have hus : u ≠ s := (Finset.mem_erase.mp hu).1
    have hne : 1 + u * (-s⁻¹) ≠ 0 := by
      have : 1 + u * (-s⁻¹) = (s - u) / s := by field_simp; ring
      rw [this]
      exact div_ne_zero (sub_ne_zero.mpr hus.symm) hs0.ne'
    exact ContinuousAt.div continuousAt_const (by fun_prop) hne
  have hlin : Tendsto (fun y : ℝ => 1 + s * y) (𝓝 (-s⁻¹)) (𝓝 0) := by
    have hc : Continuous fun y : ℝ => 1 + s * y := by fun_prop
    have h := hc.tendsto (-s⁻¹)
    have e : 1 + s * (-s⁻¹) = 0 := by field_simp; ring
    rwa [e] at h
  constructor
  · have h1 : Tendsto (fun y : ℝ => 1 + s * y) (𝓝[>] (-s⁻¹)) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨hlin.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (str_lt_iff hs0).1 hy
    have h2 := (tendsto_inv_nhdsGT_zero.comp h1).const_mul_atTop hcpos
    have h3 := (hg.tendsto.mono_left nhdsWithin_le_nhds).add_atTop h2
    refine h3.congr fun y => ?_
    simp only [Function.comp, hdec y]
  · have h1 : Tendsto (fun y : ℝ => 1 + s * y) (𝓝[<] (-s⁻¹)) (𝓝[<] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨hlin.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (str_gt_iff hs0).1 hy
    have h2 := (tendsto_inv_nhdsLT_zero.comp h1).const_mul_atBot hcpos
    have h3 := (hg.tendsto.mono_left nhdsWithin_le_nhds).add_atBot h2
    refine h3.congr fun y => ?_
    simp only [Function.comp, hdec y]

private lemma str_tendsto_zero (N : ℕ) (σ : Fin M → ℝ) (t : ℝ) :
    Tendsto (strF N σ t) (𝓝[<] 0) atTop := by
  have hg : ContinuousAt (fun y => t * strG N σ y) 0 := by
    refine ContinuousAt.mul continuousAt_const ?_
    change ContinuousAt (fun y => ∑ u ∈ posVals σ, weight N σ u * u / (1 + u * y)) 0
    refine tendsto_finsetSum _ fun u _ => ?_
    exact ContinuousAt.div continuousAt_const (by fun_prop) (by simp)
  have h1 : Tendsto (fun y : ℝ => -y⁻¹) (𝓝[<] 0) atTop :=
    tendsto_neg_atBot_atTop.comp tendsto_inv_nhdsLT_zero
  exact h1.atTop_add (hg.tendsto.mono_left nhdsWithin_le_nhds)

/-! ## Roots of `f^t = E` -/

private lemma str_deriv_left {g : ℝ → ℝ} {d x a : ℝ} (hg : HasDerivAt g d x) (hd : 0 < d)
    (ha : a < x) : ∃ y ∈ Set.Ioo a x, g y < g x := by
  have hs := hasDerivAt_iff_tendsto_slope.mp hg
  have h1 : ∀ᶠ y in 𝓝[<] x, 0 < slope g x y :=
    (hs.mono_left (nhdsWithin_mono _ fun y hy => ne_of_lt hy)).eventually (lt_mem_nhds hd)
  obtain ⟨y, hy1, hy2⟩ := (h1.and (Ioo_mem_nhdsLT ha)).exists
  refine ⟨y, hy2, ?_⟩
  rw [slope_def_field] at hy1
  have hyx : y - x < 0 := by linarith [hy2.2]
  rcases div_pos_iff.mp hy1 with ⟨_, h⟩ | ⟨h, _⟩
  · linarith
  · linarith

private lemma str_deriv_right {g : ℝ → ℝ} {d x b : ℝ} (hg : HasDerivAt g d x) (hd : 0 < d)
    (hb : x < b) : ∃ y ∈ Set.Ioo x b, g x < g y := by
  have hs := hasDerivAt_iff_tendsto_slope.mp hg
  have h1 : ∀ᶠ y in 𝓝[>] x, 0 < slope g x y :=
    (hs.mono_left (nhdsWithin_mono _ fun y hy => ne_of_gt hy)).eventually (lt_mem_nhds hd)
  obtain ⟨y, hy1, hy2⟩ := (h1.and (Ioo_mem_nhdsGT hb)).exists
  refine ⟨y, hy2, ?_⟩
  rw [slope_def_field] at hy1
  have hyx : 0 < y - x := by linarith [hy2.1]
  rcases div_pos_iff.mp hy1 with ⟨h, _⟩ | ⟨_, h⟩
  · linarith
  · linarith

private lemma str_ivt {g : ℝ → ℝ} {a b E : ℝ} (hab : a ≤ b)
    (hc : ∀ x ∈ Set.Icc a b, ContinuousAt g x)
    (h : (g a < E ∧ E < g b) ∨ (g b < E ∧ E < g a)) : ∃ x ∈ Set.Ioo a b, g x = E := by
  have hcont : ContinuousOn g (Set.Icc a b) := fun x hx => (hc x hx).continuousWithinAt
  rcases h with h | h
  · exact intermediate_value_Ioo hab hcont h
  · exact intermediate_value_Ioo' hab hcont h

private lemma str_cont_K (N : ℕ) (σ : Fin M → ℝ) (hS : (posVals σ).Nonempty) (t : ℝ) {s : ℝ}
    (hs : s ∈ posVals σ) {a b : ℝ} (ha : strK σ s a) (hb : strK σ s b) :
    ∀ x ∈ Set.Icc a b, ContinuousAt (strF N σ t) x := by
  intro x hx
  have hK : strK σ s x := ⟨lt_of_lt_of_le ha.1 hx.1, lt_of_le_of_lt hx.2 hb.2⟩
  obtain ⟨h0, h1⟩ := str_K_good σ hS hs hK
  exact (str_hasDerivAt_F N σ t h0 h1).continuousAt

/-- A root of `f^t = E` in `I_l` to the left of a point where `f^t < E`. -/
private lemma str_root_left (N : ℕ) (σ : Fin M → ℝ) (hN : 0 < N) (hS : (posVals σ).Nonempty)
    {t : ℝ} (ht : 0 < t) {E s : ℝ} (hs : s ∈ posVals σ) {z : ℝ} (hz : strK σ s z)
    (hzE : strF N σ t z < E) : ∃ r, -s⁻¹ < r ∧ r < z ∧ strF N σ t r = E := by
  obtain ⟨y, hy, hyE⟩ : ∃ y ∈ Set.Ioo (-s⁻¹) z, E < strF N σ t y := by
    obtain ⟨y, h1, h2⟩ := (((str_tendsto_pole N σ hN hs ht).1.eventually
      (eventually_gt_atTop E)).and (Ioo_mem_nhdsGT hz.1)).exists
    exact ⟨y, h2, h1⟩
  have hyK : strK σ s y := ⟨hy.1, hy.2.trans hz.2⟩
  obtain ⟨r, hr, hrE⟩ := str_ivt hy.2.le (str_cont_K N σ hS t hs hyK hz) (Or.inr ⟨hzE, hyE⟩)
  exact ⟨r, hy.1.trans hr.1, hr.2, hrE⟩

/-- A root of `f^t = E` in `I_l`, `l ≥ 2`, to the right of a point where `f^t > E`. -/
private lemma str_root_right (N : ℕ) (σ : Fin M → ℝ) (hN : 0 < N) (hS : (posVals σ).Nonempty)
    {t : ℝ} (ht : 0 < t) {E s : ℝ} (hs : s ∈ posVals σ) (hne : s ≠ (posVals σ).max' hS) {z : ℝ}
    (hz : strK σ s z) (hzE : E < strF N σ t z) :
    ∃ r, z < r ∧ r < strR σ s ∧ strF N σ t r = E := by
  obtain ⟨s', hs', -, -, hR⟩ := str_R_next σ hS hs hne
  have hz2 : z < -s'⁻¹ := hR ▸ hz.2
  obtain ⟨y, hy, hyE⟩ : ∃ y ∈ Set.Ioo z (-s'⁻¹), strF N σ t y < E := by
    obtain ⟨y, h1, h2⟩ := (((str_tendsto_pole N σ hN hs' ht).2.eventually
      (eventually_lt_atBot E)).and (Ioo_mem_nhdsLT hz2)).exists
    exact ⟨y, h2, h1⟩
  have hyK : strK σ s y := ⟨hz.1.trans hy.1, hR ▸ hy.2⟩
  obtain ⟨r, hr, hrE⟩ := str_ivt hy.1.le (str_cont_K N σ hS t hs hz hyK) (Or.inr ⟨hyE, hzE⟩)
  exact ⟨r, hr.1, hr.2.trans hyK.2, hrE⟩

/-- Every `I_l`, `l ≥ 2`, contains a root of `f^t = E`. -/
private lemma str_root_default (N : ℕ) (σ : Fin M → ℝ) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {t : ℝ} (ht : 0 < t) (E : ℝ) {s : ℝ} (hs : s ∈ posVals σ)
    (hne : s ≠ (posVals σ).max' hS) : ∃ r, strK σ s r ∧ strF N σ t r = E := by
  have hlt := str_left_lt_R σ hS hs
  have hmid : strK σ s ((-s⁻¹ + strR σ s) / 2) := ⟨by linarith, by linarith⟩
  rcases lt_trichotomy (strF N σ t ((-s⁻¹ + strR σ s) / 2)) E with h | h | h
  · obtain ⟨r, h1, h2, h3⟩ := str_root_left N σ hN hS ht hs hmid h
    exact ⟨r, ⟨h1, h2.trans hmid.2⟩, h3⟩
  · exact ⟨_, hmid, h⟩
  · obtain ⟨r, h1, h2, h3⟩ := str_root_right N σ hN hS ht hs hne hmid h
    exact ⟨r, ⟨hmid.1.trans h1, h2⟩, h3⟩

/-! ## Root counts for `f^t` -/

/-- An increasing crossing of the level `E` in `I_l` gives `2` roots of `f^t = E` in `I_1` and
`3` in `I_l`, `l ≥ 2`. -/
private lemma str_special_K (N : ℕ) (σ : Fin M → ℝ) (hN : 0 < N) (hS : (posVals σ).Nonempty)
    {t : ℝ} (ht : 0 < t) {E s : ℝ} (hs : s ∈ posVals σ) {ξ : ℝ} (hξ : strK σ s ξ)
    (hE : strF N σ t ξ = E) (hd : 0 < strF1 N σ t ξ) :
    ∃ T : Finset ℝ, (∀ x ∈ T, strK σ s x ∧ strF N σ t x = E) ∧
      (if s = (posVals σ).max' hS then 0 else 1) + 2 ≤ T.card := by
  obtain ⟨h0, h1⟩ := str_K_good σ hS hs hξ
  have hder := str_hasDerivAt_F N σ t h0 h1
  obtain ⟨y1, hy1, hy1E⟩ := str_deriv_left hder hd hξ.1
  have hy1K : strK σ s y1 := ⟨hy1.1, hy1.2.trans hξ.2⟩
  obtain ⟨r1, hr1a, hr1b, hr1E⟩ := str_root_left N σ hN hS ht hs hy1K (hE ▸ hy1E)
  have hr1K : strK σ s r1 := ⟨hr1a, (hr1b.trans hy1.2).trans hξ.2⟩
  have hr1ξ : r1 < ξ := hr1b.trans hy1.2
  by_cases hmax : s = (posVals σ).max' hS
  · refine ⟨{r1, ξ}, ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ⟨hr1K, hr1E⟩
      · exact ⟨hξ, hE⟩
    · rw [ite_eq_left hmax, Finset.card_pair hr1ξ.ne]
  · obtain ⟨y2, hy2, hy2E⟩ := str_deriv_right hder hd hξ.2
    have hy2K : strK σ s y2 := ⟨hξ.1.trans hy2.1, hy2.2⟩
    obtain ⟨r2, hr2a, hr2b, hr2E⟩ := str_root_right N σ hN hS ht hs hmax hy2K (hE ▸ hy2E)
    have hr2K : strK σ s r2 := ⟨(hξ.1.trans hy2.1).trans hr2a, hr2b⟩
    have hξr2 : ξ < r2 := hy2.1.trans hr2a
    refine ⟨{r1, ξ, r2}, ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨hr1K, hr1E⟩
      · exact ⟨hξ, hE⟩
      · exact ⟨hr2K, hr2E⟩
    · rw [ite_eq_right hmax, Finset.card_eq_three.2 ⟨r1, ξ, r2, hr1ξ.ne, (hr1ξ.trans hξr2).ne,
        hξr2.ne, rfl⟩]

private lemma str_sum_base (S : Finset ℝ) (hS : S.Nonempty) :
    ∑ s ∈ S, (if s = S.max' hS then 0 else 1) = S.card - 1 := by
  have h : ∀ s ∈ S, (if s = S.max' hS then 0 else 1 : ℕ) = if s ≠ S.max' hS then 1 else 0 := by
    intro s _
    by_cases h : s = S.max' hS <;> simp [h]
  rw [Finset.sum_congr rfl h, Finset.sum_boole, Finset.filter_ne',
    Finset.card_erase_of_mem (S.max'_mem hS)]
  simp

private lemma str_sum_lb (S : Finset ℝ) (hS : S.Nonempty) (c e : ℝ → ℕ)
    (h : ∀ s ∈ S, (if s = S.max' hS then 0 else 1) + e s ≤ c s) :
    S.card - 1 + ∑ s ∈ S, e s ≤ ∑ s ∈ S, c s := by
  rw [← str_sum_base S hS, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum h

/-! ## The ordered critical points `x_1 ≥ ⋯ ≥ x_{2p-1}` -/

/-- The number of critical points in `(y, 0)` counted with multiplicity. -/
private def strA (N : ℕ) (σ : Fin M → ℝ) (y : ℝ) : ℕ :=
  Multiset.card ((innerCrit N σ).filter (fun x => y < x))

private lemma str_critPoly_ne_zero (N : ℕ) (σ : Fin M → ℝ) : critPoly N σ ≠ 0 := by
  intro h
  have := critPoly_eval_zero N σ
  rw [h] at this
  simp at this

/-- `Q(-1/u) ≠ 0` at the poles. -/
private lemma str_critPoly_pole (N : ℕ) (σ : Fin M → ℝ) (hN : 0 < N) {u : ℝ}
    (hu : u ∈ posVals σ) : (critPoly N σ).eval (-u⁻¹) ≠ 0 := by
  have hu0 := str_pos_of_mem σ hu
  have hP : ∏ t ∈ posVals σ, (1 + t * (-u⁻¹)) ^ 2 = 0 := by
    refine Finset.prod_eq_zero hu ?_
    field_simp
    ring
  have hsum : ∑ t ∈ posVals σ, weight N σ t * t ^ 2 *
        ∏ s' ∈ (posVals σ).erase t, (1 + s' * (-u⁻¹)) ^ 2 =
      weight N σ u * u ^ 2 * ∏ s' ∈ (posVals σ).erase u, (1 + s' * (-u⁻¹)) ^ 2 := by
    refine Finset.sum_eq_single u (fun t ht htu => ?_) (fun h => absurd hu h)
    have hmem : u ∈ (posVals σ).erase t := Finset.mem_erase.mpr ⟨htu.symm, hu⟩
    rw [Finset.prod_eq_zero hmem (by field_simp; ring), mul_zero]
  have hev : (critPoly N σ).eval (-u⁻¹) = ∏ t ∈ posVals σ, (1 + t * (-u⁻¹)) ^ 2 -
      (-u⁻¹) ^ 2 * ∑ t ∈ posVals σ, weight N σ t * t ^ 2 *
        ∏ s' ∈ (posVals σ).erase t, (1 + s' * (-u⁻¹)) ^ 2 := by
    simp only [critPoly, eval_sub, eval_mul, eval_prod, eval_pow, eval_add, eval_one, eval_C,
      eval_X, eval_finsetSum]
  rw [hev, hP, hsum, zero_sub, neg_ne_zero]
  refine mul_ne_zero (pow_ne_zero 2 (neg_ne_zero.mpr (inv_ne_zero hu0.ne')))
    (mul_ne_zero (mul_ne_zero (str_weight_pos N σ hN hu).ne' (pow_ne_zero 2 hu0.ne')) ?_)
  refine Finset.prod_ne_zero_iff.mpr fun t ht => ?_
  have htu : t ≠ u := (Finset.mem_erase.mp ht).1
  have : 1 + t * (-u⁻¹) = (u - t) / u := by field_simp; ring
  rw [this]
  exact pow_ne_zero 2 (div_ne_zero (sub_ne_zero.mpr htu.symm) hu0.ne')

private lemma str_mem_innerCrit (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    {x : ℝ} (hx : x ∈ innerCrit N σ) :
    InInner σ x ∧ (∀ u ∈ posVals σ, 1 + u * x ≠ 0) ∧ fR1 N σ x = 0 := by
  unfold innerCrit at hx
  rw [Multiset.mem_filter, mem_roots (str_critPoly_ne_zero N σ)] at hx
  obtain ⟨hroot, hin⟩ := hx
  have h0 : (critPoly N σ).eval x = 0 := hroot
  have hnp : ∀ u ∈ posVals σ, 1 + u * x ≠ 0 := by
    intro u hu h
    have hu0 := str_pos_of_mem σ hu
    have hx' : x = -u⁻¹ := by
      field_simp
      linear_combination h
    rw [hx'] at h0
    exact str_critPoly_pole N σ hN hu h0
  refine ⟨hin, hnp, ?_⟩
  rw [critPoly_eval N σ hσ hin.1.ne (str_nonpole_all σ hσ hnp)] at h0
  have hpre : x ^ 2 * ∏ s ∈ posVals σ, (1 + s * x) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hin.1.ne)
      (Finset.prod_ne_zero_iff.mpr fun s hs => pow_ne_zero 2 (hnp s hs))
  exact (mul_eq_zero.mp h0).resolve_left hpre

private lemma str_mem_innerCrit_of (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i)
    (hS : (posVals σ).Nonempty) {s : ℝ} (hs : s ∈ posVals σ) {x : ℝ} (hx : strK σ s x)
    (h1 : fR1 N σ x = 0) : x ∈ innerCrit N σ := by
  obtain ⟨hx0, hsgn⟩ := str_K_sign σ hS hs hx
  obtain ⟨-, hnp⟩ := str_K_good σ hS hs hx
  unfold innerCrit
  rw [Multiset.mem_filter, mem_roots (str_critPoly_ne_zero N σ)]
  refine ⟨?_, hx0, s, hs, (hsgn s hs).1 le_rfl⟩
  change (critPoly N σ).eval x = 0
  rw [critPoly_eval N σ hσ hx0.ne (str_nonpole_all σ hσ hnp), h1, mul_zero]

private lemma str_mem_K (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {x : ℝ} (hx : x ∈ innerCrit N σ) :
    ∃ s ∈ posVals σ, strK σ s x := by
  obtain ⟨hin, hnp, -⟩ := str_mem_innerCrit N σ hσ hN hx
  exact str_exists_K σ hS hin.1 hnp hin.2

/-- In a list sorted in decreasing order, the entries `> y` form an initial segment. -/
private lemma str_list_prefix (y : ℝ) : ∀ (L : List ℝ), L.Pairwise (fun a b => b ≤ a) →
    ∀ (i : ℕ) (hi : i < L.length), (y < L[i] ↔ i < L.countP (fun x => decide (y < x)))
  | [], _, i, hi => by simp at hi
  | a :: L, hpw, i, hi => by
    rw [List.pairwise_cons] at hpw
    have hrest : ¬ y < a → L.countP (fun x => decide (y < x)) = 0 := by
      intro hya
      rw [List.countP_eq_zero]
      intro b hb
      have := hpw.1 b hb
      simp only [decide_eq_true_eq]
      intro hyb
      exact hya (lt_of_lt_of_le hyb this)
    rw [List.countP_cons]
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero]
      by_cases hya : y < a
      · simp [hya]
      · simp [hya, hrest hya]
    | succ j =>
      simp only [List.getElem_cons_succ]
      have hj : j < L.length := by simpa using hi
      have ih := str_list_prefix y L hpw.2 j hj
      by_cases hya : y < a
      · simp only [hya, decide_true, ite_true]
        rw [ih]
        omega
      · simp only [hya, decide_false, Bool.false_eq_true, ite_false, add_zero]
        rw [hrest hya] at ih ⊢
        constructor
        · intro h
          exact absurd (ih.1 h) (Nat.not_lt_zero _)
        · intro h
          omega

private lemma str_sort_spec (m : Multiset ℝ) {i : ℕ} (hi : i < Multiset.card m) :
    (m.sort (· ≤ ·)).reverse.getD i 0 ∈ m ∧
      ∀ y, (y < (m.sort (· ≤ ·)).reverse.getD i 0 ↔
        i < Multiset.card (m.filter (fun x => y < x))) := by
  have hlen : (m.sort (· ≤ ·)).reverse.length = Multiset.card m := by
    rw [List.length_reverse, Multiset.length_sort]
  have hi' : i < (m.sort (· ≤ ·)).reverse.length := hlen ▸ hi
  rw [List.getD_eq_getElem _ _ hi']
  have hpw : (m.sort (· ≤ ·)).reverse.Pairwise (fun a b => b ≤ a) :=
    List.pairwise_reverse.2 (Multiset.pairwise_sort _ _)
  refine ⟨?_, fun y => ?_⟩
  · have := List.getElem_mem hi'
    rwa [List.mem_reverse, Multiset.mem_sort] at this
  · rw [str_list_prefix y _ hpw i hi', ← Multiset.countP_eq_card_filter,
      ← Multiset.coe_countP, Multiset.coe_reverse, Multiset.sort_eq]

private lemma str_sort_surj (m : Multiset ℝ) {d : ℝ} (hd : d ∈ m) :
    ∃ i < Multiset.card m, (m.sort (· ≤ ·)).reverse.getD i 0 = d := by
  have hd' : d ∈ (m.sort (· ≤ ·)).reverse := by
    rwa [List.mem_reverse, Multiset.mem_sort]
  obtain ⟨i, hi, hid⟩ := List.mem_iff_getElem.1 hd'
  have hlen : (m.sort (· ≤ ·)).reverse.length = Multiset.card m := by
    rw [List.length_reverse, Multiset.length_sort]
  exact ⟨i, hlen ▸ hi, by rw [List.getD_eq_getElem _ _ hi, hid]⟩

/-- `x_k ∈ 𝒞`, and `y < x_k` iff at least `k` critical points lie in `(y, 0)`. -/
private lemma str_xCrit_spec (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {k : ℕ} (hk1 : 1 ≤ k) (hk : k < 2 * numBands N σ) :
    xCrit N σ k ∈ innerCrit N σ ∧ ∀ y, (y < xCrit N σ k ↔ k ≤ strA N σ y) := by
  have hc := (card_innerCrit N σ hσ hN hS).1
  have hx : xCrit N σ k = ((innerCrit N σ).sort (· ≤ ·)).reverse.getD (k - 1) 0 := by
    unfold xCrit
    rw [ite_eq_right (by omega)]
  obtain ⟨hmem, hspec⟩ := str_sort_spec (innerCrit N σ) (i := k - 1) (by omega)
  rw [hx]
  refine ⟨hmem, fun y => ?_⟩
  rw [hspec y, strA]
  omega

private lemma str_xCrit_surj (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {d : ℝ} (hd : d ∈ innerCrit N σ) :
    ∃ k, 1 ≤ k ∧ k < 2 * numBands N σ ∧ xCrit N σ k = d := by
  have hc := (card_innerCrit N σ hσ hN hS).1
  obtain ⟨i, hi, hid⟩ := str_sort_surj _ hd
  refine ⟨i + 1, by omega, by omega, ?_⟩
  unfold xCrit
  rw [ite_eq_right (by omega), Nat.add_sub_cancel]
  exact hid

private lemma str_xCrit_anti (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {k k' : ℕ} (hk1 : 1 ≤ k) (hkk : k ≤ k')
    (hk' : k' < 2 * numBands N σ) : xCrit N σ k' ≤ xCrit N σ k := by
  by_contra h
  rw [not_le] at h
  have h1 := ((str_xCrit_spec N σ hσ hN hS (k := k') (by omega) hk').2 (xCrit N σ k)).1 h
  have h2 := ((str_xCrit_spec N σ hσ hN hS hk1 (by omega)).2 (xCrit N σ k)).2 (by omega)
  exact lt_irrefl _ h2

private lemma str_ne_R (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {s : ℝ} (hs : s ∈ posVals σ) {x : ℝ}
    (hx : x ∈ innerCrit N σ) : x ≠ strR σ s := by
  obtain ⟨hin, hnp, -⟩ := str_mem_innerCrit N σ hσ hN hx
  intro h
  by_cases hmax : s = (posVals σ).max' hS
  · rw [hmax, str_R_max] at h
    linarith [hin.1]
  · obtain ⟨s', hs', -, -, hR⟩ := str_R_next σ hS hs hmax
    rw [hR] at h
    apply hnp s' hs'
    rw [h]
    have := str_pos_of_mem σ hs'
    field_simp
    ring

private lemma str_A_split (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {s : ℝ} (hs : s ∈ posVals σ) :
    strA N σ (-s⁻¹) =
      strA N σ (strR σ s) + Multiset.card ((innerCrit N σ).filter (strK σ s)) := by
  have hlt := str_left_lt_R σ hS hs
  have hne := fun x (hx : x ∈ innerCrit N σ) => str_ne_R N σ hσ hN hS hs hx
  unfold strA
  have h1 := Multiset.filter_add_not (fun x : ℝ => x < strR σ s)
    ((innerCrit N σ).filter (fun x => -s⁻¹ < x))
  have e1 : ((innerCrit N σ).filter (fun x => -s⁻¹ < x)).filter (fun x => x < strR σ s) =
      (innerCrit N σ).filter (strK σ s) := by
    rw [Multiset.filter_filter]
    exact Multiset.filter_congr fun x _ => by simp only [strK, and_comm]
  have e2 : ((innerCrit N σ).filter (fun x => -s⁻¹ < x)).filter (fun x => ¬ x < strR σ s) =
      (innerCrit N σ).filter (fun x => strR σ s < x) := by
    rw [Multiset.filter_filter]
    refine Multiset.filter_congr fun x hx => ?_
    constructor
    · rintro ⟨h1, -⟩
      exact lt_of_le_of_ne (not_lt.mp h1) (hne x hx).symm
    · intro h
      exact ⟨not_lt.mpr h.le, lt_trans hlt h⟩
  rw [← h1, Multiset.card_add, e1, e2, add_comm]

private lemma str_A_zero (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) :
    strA N σ 0 = 0 := by
  unfold strA
  rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
  intro x hx
  exact not_lt.2 (str_mem_innerCrit N σ hσ hN hx).1.1.le

private lemma str_card_K_max (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) :
    Multiset.card ((innerCrit N σ).filter (strK σ ((posVals σ).max' hS))) = 1 := by
  rw [← card_innerCrit_I1 N σ hσ hN hS]
  congr 1
  refine Multiset.filter_congr fun x hx => ?_
  have hin := (str_mem_innerCrit N σ hσ hN hx).1
  have hm := (posVals σ).max'_mem hS
  constructor
  · intro hK s hs
    exact ((str_K_sign σ hS hm hK).2 s hs).1 ((posVals σ).le_max' s hs)
  · intro h
    refine ⟨(str_lt_iff (str_pos_of_mem σ hm)).2 (h _ hm), ?_⟩
    rw [str_R_max]
    exact hin.1

private lemma str_card_K_inner (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {s : ℝ} (hs : s ∈ posVals σ) (hne : s ≠ (posVals σ).max' hS) :
    Multiset.card ((innerCrit N σ).filter (strK σ s)) = 0 ∨
      Multiset.card ((innerCrit N σ).filter (strK σ s)) = 2 := by
  obtain ⟨s', hs', hss', hcons, hR⟩ := str_R_next σ hS hs hne
  have e : (innerCrit N σ).filter (strK σ s) =
      (innerCrit N σ).filter (fun x => -s⁻¹ < x ∧ x < -s'⁻¹) :=
    Multiset.filter_congr fun x _ => by rw [strK, hR]
  rw [e]
  exact card_innerCrit_Ii N σ hσ hN hs hs' hss' hcons

private lemma str_A_odd (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) (n : ℕ) : ∀ s ∈ posVals σ,
    ((posVals σ).filter (fun u => s < u)).card = n → Odd (strA N σ (-s⁻¹)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs hcard
    rw [str_A_split N σ hσ hN hS hs]
    by_cases hmax : s = (posVals σ).max' hS
    · subst hmax
      rw [str_R_max, str_A_zero N σ hσ hN, str_card_K_max N σ hσ hN hS]
      exact odd_one
    · obtain ⟨s', hs', hss', -, hR⟩ := str_R_next σ hS hs hmax
      have hsub : (posVals σ).filter (fun u => s' < u) ⊆ (posVals σ).filter (fun u => s < u) := by
        intro u hu
        obtain ⟨huT, hu'⟩ := Finset.mem_filter.mp hu
        exact Finset.mem_filter.mpr ⟨huT, lt_trans hss' hu'⟩
      have hlt : ((posVals σ).filter (fun u => s' < u)).card < n := by
        rw [← hcard]
        exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).2
          ⟨s', Finset.mem_filter.mpr ⟨hs', hss'⟩, fun h => lt_irrefl _ (Finset.mem_filter.mp h).2⟩)
      have ho := ih _ hlt s' hs' rfl
      rw [hR]
      rcases str_card_K_inner N σ hσ hN hS hs hmax with h | h
      · rw [h, add_zero]
        exact ho
      · rw [h]
        exact ho.add_even even_two

/-- The critical points to the right of `I_l`: none for `I_1`, an odd number for `l ≥ 2`. -/
private lemma str_lo (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {s : ℝ} (hs : s ∈ posVals σ) :
    (s = (posVals σ).max' hS ∧ strA N σ (strR σ s) = 0 ∧
        Multiset.card ((innerCrit N σ).filter (strK σ s)) = 1) ∨
      (s ≠ (posVals σ).max' hS ∧ Odd (strA N σ (strR σ s)) ∧
        (Multiset.card ((innerCrit N σ).filter (strK σ s)) = 0 ∨
          Multiset.card ((innerCrit N σ).filter (strK σ s)) = 2)) := by
  by_cases hmax : s = (posVals σ).max' hS
  · left
    subst hmax
    exact ⟨rfl, by rw [str_R_max, str_A_zero N σ hσ hN], str_card_K_max N σ hσ hN hS⟩
  · right
    obtain ⟨s', hs', -, -, hR⟩ := str_R_next σ hS hs hmax
    refine ⟨hmax, ?_, str_card_K_inner N σ hσ hN hS hs hmax⟩
    rw [hR]
    exact str_A_odd N σ hσ hN hS _ s' hs' rfl

/-- `x_k ∈ I_l` iff the position `k` lies in the block of `I_l`. -/
private lemma str_block (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {s : ℝ} (hs : s ∈ posVals σ) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k < 2 * numBands N σ) :
    strK σ s (xCrit N σ k) ↔ strA N σ (strR σ s) < k ∧ k ≤ strA N σ (-s⁻¹) := by
  obtain ⟨hmem, hspec⟩ := str_xCrit_spec N σ hσ hN hS hk1 hk
  have hne := str_ne_R N σ hσ hN hS hs hmem
  unfold strK
  rw [hspec (-s⁻¹)]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1⟩
    by_contra h
    have := (hspec (strR σ s)).2 (not_lt.1 h)
    linarith
  · rintro ⟨h1, h2⟩
    refine ⟨h2, ?_⟩
    rcases lt_or_gt_of_ne hne with h | h
    · exact h
    · have := (hspec (strR σ s)).1 h
      omega

/-- `x_1 ∈ I_1`. -/
private lemma str_first (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) : strK σ ((posVals σ).max' hS) (xCrit N σ 1) := by
  have hp := (card_innerCrit N σ hσ hN hS).2
  obtain ⟨hmem, -⟩ := str_xCrit_spec N σ hσ hN hS le_rfl (by omega)
  obtain ⟨s, hs, hK⟩ := str_mem_K N σ hσ hN hS hmem
  have hb := (str_block N σ hσ hN hS hs le_rfl (by omega)).1 hK
  rcases str_lo N σ hσ hN hS hs with ⟨hmax, -, -⟩ | ⟨-, ⟨c, hc⟩, -⟩
  · rw [← hmax]
    exact hK
  · omega

/-! ## The shape of `f` on `I_1, …, I_n` -/

private lemma str_sign {g : ℝ → ℝ} {a b : ℝ} (hc : ContinuousOn g (Set.Ioo a b))
    (hne : ∀ x ∈ Set.Ioo a b, g x ≠ 0) {y z : ℝ} (hy : y ∈ Set.Ioo a b) (hz : z ∈ Set.Ioo a b)
    (hgy : 0 < g y) : 0 < g z := by
  by_contra h
  have hz' : g z < 0 := lt_of_le_of_ne (not_lt.1 h) (hne z hz)
  obtain ⟨w, hw, hw0⟩ := isPreconnected_Ioo.intermediate_value hz hy hc ⟨hz'.le, hgy.le⟩
  exact hne w hw hw0

/-- If `g → +∞` at the left end of an interval on which `g'` has no zero, then `g' < 0`. -/
private lemma str_neg_of_atTop_left {g g' : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt g (g' x) x) (hc : ContinuousOn g' (Set.Ioo a b))
    (hne : ∀ x ∈ Set.Ioo a b, g' x ≠ 0) (hlim : Tendsto g (𝓝[>] a) atTop) :
    ∀ x ∈ Set.Ioo a b, g' x < 0 := by
  intro x hx
  by_contra hneg
  have hpos : 0 < g' x := lt_of_le_of_ne (not_lt.1 hneg) (hne x hx).symm
  have hmono : StrictMonoOn g (Set.Ioo a b) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioo a b)
      (fun z hz => (hd z hz).continuousAt.continuousWithinAt) fun z hz => ?_
    rw [interior_Ioo] at hz
    rw [(hd z hz).deriv]
    exact str_sign hc hne hx hz hpos
  obtain ⟨z, h1, h2⟩ := ((hlim.eventually (eventually_gt_atTop (g x))).and
    (Ioo_mem_nhdsGT hx.1)).exists
  have := hmono ⟨h2.1, h2.2.trans hx.2⟩ hx h2.2
  linarith

/-- If `g → +∞` at the right end of an interval on which `g'` has no zero, then `g' > 0`. -/
private lemma str_pos_of_atTop_right {g g' : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt g (g' x) x) (hc : ContinuousOn g' (Set.Ioo a b))
    (hne : ∀ x ∈ Set.Ioo a b, g' x ≠ 0) (hlim : Tendsto g (𝓝[<] b) atTop) :
    ∀ x ∈ Set.Ioo a b, 0 < g' x := by
  intro x hx
  by_contra hpos
  have hneg : g' x < 0 := lt_of_le_of_ne (not_lt.1 hpos) (hne x hx)
  have hanti : StrictAntiOn g (Set.Ioo a b) := by
    refine strictAntiOn_of_deriv_neg (convex_Ioo a b)
      (fun z hz => (hd z hz).continuousAt.continuousWithinAt) fun z hz => ?_
    rw [interior_Ioo] at hz
    rw [(hd z hz).deriv]
    have := str_sign (g := fun x => -g' x) hc.neg (fun x hx h => hne x hx (neg_eq_zero.1 h))
      hx hz (neg_pos.2 hneg)
    linarith
  obtain ⟨z, h1, h2⟩ := ((hlim.eventually (eventually_gt_atTop (g x))).and
    (Ioo_mem_nhdsLT hx.2)).exists
  have := hanti hx ⟨hx.1.trans h2.1, h2.2⟩ h2.1
  linarith

private lemma str_hasDerivAt_K (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i)
    (hS : (posVals σ).Nonempty) {s : ℝ} (hs : s ∈ posVals σ) {x : ℝ} (hx : strK σ s x) :
    HasDerivAt (fR N σ) (fR1 N σ x) x ∧ HasDerivAt (fR1 N σ) (fR2 N σ x) x := by
  obtain ⟨h0, h1⟩ := str_K_good σ hS hs hx
  exact ⟨hasDerivAt_fR N σ h0 (str_nonpole_all σ hσ h1),
    hasDerivAt_fR1 N σ h0 (str_nonpole_all σ hσ h1)⟩

private lemma str_contOn_K (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i)
    (hS : (posVals σ).Nonempty) {s : ℝ} (hs : s ∈ posVals σ) {a b : ℝ}
    (h : ∀ x ∈ Set.Ioo a b, strK σ s x) : ContinuousOn (fR1 N σ) (Set.Ioo a b) :=
  fun x hx => (str_hasDerivAt_K N σ hσ hS hs (h x hx)).2.continuousAt.continuousWithinAt

private lemma str_tendsto_fR_pole (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    {s : ℝ} (hs : s ∈ posVals σ) : Tendsto (fR N σ) (𝓝[>] (-s⁻¹)) atTop := by
  rw [str_fR_eq N σ hσ]
  exact (str_tendsto_pole N σ hN hs one_pos).1

/-- Lemma 2.4–2.5: in `I_l`, `l ≥ 2`, with two distinct critical points `c < d`, `f' > 0` on
`(c, d)`, so `f(c) < f(d)`. -/
private lemma str_pair_lt (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {s : ℝ} (hs : s ∈ posVals σ)
    (hcard : Multiset.card ((innerCrit N σ).filter (strK σ s)) ≤ 2) {c d : ℝ}
    (hc : strK σ s c) (hd : strK σ s d) (hcd : c < d) (hfc : fR1 N σ c = 0)
    (hfd : fR1 N σ d = 0) : fR N σ c < fR N σ d := by
  have hcm : c ∈ (innerCrit N σ).filter (strK σ s) :=
    Multiset.mem_filter.2 ⟨str_mem_innerCrit_of N σ hσ hS hs hc hfc, hc⟩
  have hdm : d ∈ (innerCrit N σ).filter (strK σ s) :=
    Multiset.mem_filter.2 ⟨str_mem_innerCrit_of N σ hσ hS hs hd hfd, hd⟩
  have honly : ∀ z, strK σ s z → fR1 N σ z = 0 → z = c ∨ z = d := by
    intro z hz hfz
    by_contra h
    rw [not_or] at h
    have hzm : z ∈ (innerCrit N σ).filter (strK σ s) :=
      Multiset.mem_filter.2 ⟨str_mem_innerCrit_of N σ hσ hS hs hz hfz, hz⟩
    have hsum := str_sum_count_le ((innerCrit N σ).filter (strK σ s)) {c, d, z}
    rw [Finset.sum_insert (by simp [hcd.ne, Ne.symm h.1]), Finset.sum_pair (Ne.symm h.2)]
      at hsum
    have := Multiset.count_pos.2 hcm
    have := Multiset.count_pos.2 hdm
    have := Multiset.count_pos.2 hzm
    omega
  have hcount : (innerCrit N σ).count c = 1 := by
    have hsum := str_sum_count_le ((innerCrit N σ).filter (strK σ s)) {c, d}
    rw [Finset.sum_pair hcd.ne] at hsum
    have h1 := Multiset.count_pos.2 hcm
    have h2 := Multiset.count_pos.2 hdm
    rw [Multiset.count_filter_of_pos hc] at h1 hsum
    omega
  obtain ⟨hc0, hcp⟩ := str_K_good σ hS hs hc
  have hf2 : fR2 N σ c ≠ 0 := by
    intro h
    have hin : InInner σ c := ⟨(str_K_sign σ hS hs hc).1, s, hs, (str_lt_iff
      (str_pos_of_mem σ hs)).1 hc.1⟩
    have := count_innerCrit N σ hσ hN hin hcp
    rw [ite_eq_left hfc, ite_eq_left h] at this
    omega
  have hKleft : ∀ x ∈ Set.Ioo (-s⁻¹) c, strK σ s x := fun x hx => ⟨hx.1, hx.2.trans hc.2⟩
  have hleft : ∀ x ∈ Set.Ioo (-s⁻¹) c, fR1 N σ x < 0 :=
    str_neg_of_atTop_left (fun x hx => (str_hasDerivAt_K N σ hσ hS hs (hKleft x hx)).1)
      (str_contOn_K N σ hσ hS hs hKleft)
      (fun x hx h0 => by rcases honly x (hKleft x hx) h0 with h | h <;> linarith [hx.2])
      (str_tendsto_fR_pole N σ hσ hN hs)
  have hd2c := (str_hasDerivAt_K N σ hσ hS hs hc).2
  have hf2pos : 0 < fR2 N σ c := by
    rcases lt_or_gt_of_ne hf2 with h | h
    · exfalso
      obtain ⟨y, hy, hyv⟩ := str_deriv_left hd2c.neg (neg_pos.2 h) hc.1
      have := hleft y hy
      simp only [Pi.neg_apply, hfc] at hyv
      linarith
    · exact h
  obtain ⟨y, hy, hyv⟩ := str_deriv_right hd2c hf2pos hcd
  rw [hfc] at hyv
  have hKcd : ∀ x ∈ Set.Ioo c d, strK σ s x := fun x hx => ⟨hc.1.trans hx.1, hx.2.trans hd.2⟩
  have hmid : ∀ x ∈ Set.Ioo c d, 0 < fR1 N σ x := fun x hx =>
    str_sign (str_contOn_K N σ hσ hS hs hKcd)
      (fun z hz h0 => by rcases honly z (hKcd z hz) h0 with h | h <;> linarith [hz.1, hz.2])
      hy hx hyv
  have hmono : StrictMonoOn (fR N σ) (Set.Icc c d) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc c d) (fun x hx =>
      (str_hasDerivAt_K N σ hσ hS hs ⟨lt_of_lt_of_le hc.1 hx.1,
        lt_of_le_of_lt hx.2 hd.2⟩).1.continuousAt.continuousWithinAt) fun x hx => ?_
    rw [interior_Icc] at hx
    rw [(str_hasDerivAt_K N σ hσ hS hs (hKcd x hx)).1.deriv]
    exact hmid x hx
  exact hmono ⟨le_rfl, hcd.le⟩ ⟨hcd.le, le_rfl⟩ hcd

/-- The pairs `x_{2j} ≥ x_{2j+1}` lie in one `I_l`, `l ≥ 2`; either they are distinct and
`f(x_{2j+1}) < f(x_{2j})`, or they coincide and `f'' = 0` there. -/
private lemma str_pair (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {j : ℕ} (hj : 1 ≤ j) (hj' : 2 * j + 1 < 2 * numBands N σ) :
    ∃ s ∈ posVals σ, s ≠ (posVals σ).max' hS ∧ strK σ s (xCrit N σ (2 * j)) ∧
      strK σ s (xCrit N σ (2 * j + 1)) ∧ strA N σ (strR σ s) = 2 * j - 1 ∧
      ((xCrit N σ (2 * j + 1) < xCrit N σ (2 * j) ∧
          fR N σ (xCrit N σ (2 * j + 1)) < fR N σ (xCrit N σ (2 * j))) ∨
        (xCrit N σ (2 * j + 1) = xCrit N σ (2 * j) ∧ fR2 N σ (xCrit N σ (2 * j)) = 0)) := by
  obtain ⟨hmem, -⟩ := str_xCrit_spec N σ hσ hN hS (k := 2 * j) (by omega) (by omega)
  obtain ⟨hmem', -⟩ := str_xCrit_spec N σ hσ hN hS (k := 2 * j + 1) (by omega) hj'
  obtain ⟨s, hs, hK⟩ := str_mem_K N σ hσ hN hS hmem
  have hb := (str_block N σ hσ hN hS hs (k := 2 * j) (by omega) (by omega)).1 hK
  have hsplit := str_A_split N σ hσ hN hS hs
  rcases str_lo N σ hσ hN hS hs with ⟨-, hlo, hcard⟩ | ⟨hmax, ⟨c, hc⟩, hcard⟩
  · exfalso
    omega
  rcases hcard with hcard | hcard
  · exfalso
    omega
  have hlo : strA N σ (strR σ s) = 2 * j - 1 := by omega
  have hK' : strK σ s (xCrit N σ (2 * j + 1)) :=
    (str_block N σ hσ hN hS hs (k := 2 * j + 1) (by omega) hj').2 ⟨by omega, by omega⟩
  refine ⟨s, hs, hmax, hK, hK', hlo, ?_⟩
  have hle := str_xCrit_anti N σ hσ hN hS (k := 2 * j) (k' := 2 * j + 1) (by omega) (by omega) hj'
  have hf1 := (str_mem_innerCrit N σ hσ hN hmem).2.2
  have hf1' := (str_mem_innerCrit N σ hσ hN hmem').2.2
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact Or.inl ⟨hlt, str_pair_lt N σ hσ hN hS hs hcard.le hK' hK hlt hf1' hf1⟩
  · refine Or.inr ⟨heq, ?_⟩
    obtain ⟨hin, hnp, -⟩ := str_mem_innerCrit N σ hσ hN hmem
    by_contra hf2
    have hcount : (innerCrit N σ).count (xCrit N σ (2 * j)) = 1 := by
      rw [count_innerCrit N σ hσ hN hin hnp, ite_eq_left hf1, ite_eq_right hf2]
    have hcm' : ((innerCrit N σ).filter (strK σ s)).count (xCrit N σ (2 * j)) = 1 := by
      rw [Multiset.count_filter_of_pos hK]
      exact hcount
    obtain ⟨d, hdm, hdc⟩ : ∃ d ∈ (innerCrit N σ).filter (strK σ s), d ≠ xCrit N σ (2 * j) := by
      by_contra h
      have h' : ∀ b ∈ (innerCrit N σ).filter (strK σ s), b = xCrit N σ (2 * j) :=
        fun b hb => by
          by_contra hb'
          exact h ⟨b, hb, hb'⟩
      have := Multiset.eq_replicate_of_mem h'
      rw [hcard] at this
      rw [this, Multiset.count_replicate_self] at hcm'
      omega
    obtain ⟨hdm0, hdK⟩ := Multiset.mem_filter.1 hdm
    obtain ⟨k, hk1, hk, hxk⟩ := str_xCrit_surj N σ hσ hN hS hdm0
    have hbk := (str_block N σ hσ hN hS hs hk1 hk).1 (hxk ▸ hdK)
    have : k = 2 * j ∨ k = 2 * j + 1 := by omega
    rcases this with rfl | rfl
    · exact hdc hxk.symm
    · exact hdc (hxk.symm.trans heq)

/-! ## The chart of `I_0` -/

/-- At the critical point `y` of `F` in the chart, `F(y) = y² Σ_s r_s s / (y + s)² ≥ 0`. -/
private lemma str_FChart_nonneg (N : ℕ) (σ : Fin M → ℝ) {y : ℝ} (hy : InChart σ y)
    (h1 : FChart1 N σ y = 0) : 0 ≤ FChart N σ y := by
  have h1' : ∑ s ∈ posVals σ, weight N σ s * s ^ 2 / (y + s) ^ 2 = 1 := by
    unfold FChart1 at h1
    linarith
  have e : FChart N σ y = ∑ s ∈ posVals σ, y ^ 2 * (weight N σ s * s / (y + s) ^ 2) := by
    unfold FChart
    rw [show -y = -y * ∑ s ∈ posVals σ, weight N σ s * s ^ 2 / (y + s) ^ 2 by rw [h1']; ring,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s hs => ?_
    have := (hy s hs).ne'
    field_simp
    ring
  rw [e]
  refine Finset.sum_nonneg fun s hs => ?_
  have := hy s hs
  have := str_pos_of_mem σ hs
  have hw : 0 ≤ weight N σ s := by unfold weight; positivity
  positivity

/-- `f'(1/y) = -y² F'(y)`. -/
private lemma str_fR1_inv (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {y : ℝ} (hy0 : y ≠ 0)
    (hy : InChart σ y) : fR1 N σ y⁻¹ = -(y ^ 2) * FChart1 N σ y := by
  rw [str_fR1_eq N σ hσ, strF1, strH, FChart1, one_mul]
  have hterm : ∀ s ∈ posVals σ, weight N σ s * s ^ 2 / (1 + s * y⁻¹) ^ 2 =
      y ^ 2 * (weight N σ s * s ^ 2 / (y + s) ^ 2) := by
    intro s hs
    have := (hy s hs).ne'
    have e : 1 + s * y⁻¹ = (y + s) / y := by field_simp
    rw [e]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, inv_pow, inv_inv]
  ring

private lemma str_I0_inv (σ : Fin M → ℝ) {y : ℝ} (hy0 : y ≠ 0) (hy : InChart σ y) :
    strI0 σ y⁻¹ := by
  rcases lt_or_gt_of_ne hy0 with h | h
  · right
    intro s hs
    have e : 1 + s * y⁻¹ = (y + s) / y := by field_simp
    rw [e]
    exact div_neg_of_pos_of_neg (hy s hs) h
  · left
    exact inv_pos.2 h

/-! ## The critical values `a_k` -/

private lemma str_edgeVal_ne (N : ℕ) (σ : Fin M → ℝ) {k : ℕ} (hk : k ≠ 2 * numBands N σ) :
    edgeVal N σ k = fR N σ (xCrit N σ k) := by
  unfold edgeVal
  rw [ite_eq_right hk]

private lemma str_edgeVal_last (N : ℕ) (σ : Fin M → ℝ) :
    edgeVal N σ (2 * numBands N σ) = FChart N σ (yEdge N σ) := by
  unfold edgeVal
  rw [ite_eq_left rfl]

/-! ## Ordering of the critical values -/

/-- `a_{k'} ≤ a_k` for `1 ≤ k ≤ k' ≤ 2p` (Lemma 2.5). -/
private lemma str_chain (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {k k' : ℕ} (hk : 1 ≤ k) (hkk : k ≤ k')
    (hk' : k' ≤ 2 * numBands N σ) : edgeVal N σ k' ≤ edgeVal N σ k := by
  have h : ∀ j k, 1 ≤ k → k + j ≤ 2 * numBands N σ → edgeVal N σ (k + j) ≤ edgeVal N σ k := by
    intro j
    induction j with
    | zero => intro k _ _; simp
    | succ j ih =>
      intro k hk1 hkj
      exact (edgeVal_succ_le N σ hσ hN hS (k := k + j) (by omega) (by omega)).trans
        (ih k hk1 (by omega))
  have := h (k' - k) k hk (by omega)
  rwa [show k + (k' - k) = k' by omega] at this

/-- At the critical point `y ≠ 0` of `F` in the chart, `F(y) = y² Σ_s r_s s / (y + s)² > 0`. -/
private lemma str_FChart_pos (N : ℕ) (σ : Fin M → ℝ) (hN : 0 < N) (hS : (posVals σ).Nonempty)
    {y : ℝ} (hy : InChart σ y) (hy0 : y ≠ 0) (h1 : FChart1 N σ y = 0) : 0 < FChart N σ y := by
  have h1' : ∑ s ∈ posVals σ, weight N σ s * s ^ 2 / (y + s) ^ 2 = 1 := by
    unfold FChart1 at h1
    linarith
  have e : FChart N σ y = ∑ s ∈ posVals σ, y ^ 2 * (weight N σ s * s / (y + s) ^ 2) := by
    unfold FChart
    rw [show -y = -y * ∑ s ∈ posVals σ, weight N σ s * s ^ 2 / (y + s) ^ 2 by rw [h1']; ring,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s hs => ?_
    have := (hy s hs).ne'
    field_simp
    ring
  rw [e]
  refine Finset.sum_pos (fun s hs => ?_) hS
  have := hy s hs
  have := str_pos_of_mem σ hs
  have := str_weight_pos N σ hN hs
  have : 0 < y ^ 2 := pow_two_pos_of_ne_zero hy0
  positivity

/-- `a_{2p} ≥ 0`. -/
private lemma str_edgeVal_last_nonneg (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) : 0 ≤ edgeVal N σ (2 * numBands N σ) := by
  rw [str_edgeVal_last]
  obtain ⟨hyC, hyF⟩ := yEdge_spec N σ hσ hN hS
  exact str_FChart_nonneg N σ hyC hyF

/-- `a_k > 0` for every finite `x_k`. -/
private lemma str_edgeVal_pos (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {k : ℕ} (hk₁ : 1 ≤ k) (hk : k ≤ 2 * numBands N σ)
    (hfin : ¬ (k = 2 * numBands N σ ∧ yEdge N σ = 0)) : 0 < edgeVal N σ k := by
  have hp := card_innerCrit N σ hσ hN hS
  by_cases hlast : k = 2 * numBands N σ
  · have hy0 : yEdge N σ ≠ 0 := fun h0 => hfin ⟨hlast, h0⟩
    rw [hlast, str_edgeVal_last]
    obtain ⟨hyC, hyF⟩ := yEdge_spec N σ hσ hN hS
    exact str_FChart_pos N σ hN hS hyC hy0 hyF
  · have h1 := str_chain N σ hσ hN hS hk₁ (show k ≤ 2 * numBands N σ - 1 by omega) (by omega)
    have h2 := edgeVal_band_lt N σ hσ hN hS (k := numBands N σ) hp.2 le_rfl
    have h3 := str_edgeVal_last_nonneg N σ hσ hN hS
    linarith

/-! ## The shape of `f` (Lemmas 2.4 and 2.5) -/

/-- If `g → -∞` at the right end of an interval on which `g'` has no zero, then `g' < 0`. -/
private lemma str_neg_of_atBot_right {g g' : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt g (g' x) x) (hc : ContinuousOn g' (Set.Ioo a b))
    (hne : ∀ x ∈ Set.Ioo a b, g' x ≠ 0) (hlim : Tendsto g (𝓝[<] b) atBot) :
    ∀ x ∈ Set.Ioo a b, g' x < 0 := by
  intro x hx
  by_contra hneg
  have hpos : 0 < g' x := lt_of_le_of_ne (not_lt.1 hneg) (hne x hx).symm
  have hmono : StrictMonoOn g (Set.Ioo a b) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioo a b)
      (fun z hz => (hd z hz).continuousAt.continuousWithinAt) fun z hz => ?_
    rw [interior_Ioo] at hz
    rw [(hd z hz).deriv]
    exact str_sign hc hne hx hz hpos
  obtain ⟨z, h1, h2⟩ := ((hlim.eventually (eventually_lt_atBot (g x))).and
    (Ioo_mem_nhdsLT hx.2)).exists
  have := hmono hx ⟨hx.1.trans h2.1, h2.2⟩ h2.1
  linarith

/-- `f` is strictly increasing on `[a, b] ⊂ I_l` when `f' > 0` on `(a, b)`. -/
private lemma str_strictMonoOn (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i)
    (hS : (posVals σ).Nonempty) {s : ℝ} (hs : s ∈ posVals σ) {a b : ℝ} (ha : strK σ s a)
    (hb : strK σ s b) (hpos : ∀ x ∈ Set.Ioo a b, 0 < fR1 N σ x) :
    StrictMonoOn (fR N σ) (Set.Icc a b) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc a b) (fun x hx =>
    (str_hasDerivAt_K N σ hσ hS hs ⟨lt_of_lt_of_le ha.1 hx.1,
      lt_of_le_of_lt hx.2 hb.2⟩).1.continuousAt.continuousWithinAt) fun x hx => ?_
  rw [interior_Icc] at hx
  rw [(str_hasDerivAt_K N σ hσ hS hs ⟨ha.1.trans hx.1, hx.2.trans hb.2⟩).1.deriv]
  exact hpos x hx

/-- On `I_1`: `f' < 0` on `(-1/s_1, x_1)` and `f' > 0` on `(x_1, 0)`. -/
private lemma str_first_shape (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) :
    (∀ x ∈ Set.Ioo (-((posVals σ).max' hS)⁻¹) (xCrit N σ 1), fR1 N σ x < 0) ∧
      ∀ x ∈ Set.Ioo (xCrit N σ 1) 0, 0 < fR1 N σ x := by
  have hp := (card_innerCrit N σ hσ hN hS).2
  have hm := (posVals σ).max'_mem hS
  have hc := str_first N σ hσ hN hS
  obtain ⟨hmem, -⟩ := str_xCrit_spec N σ hσ hN hS le_rfl (by omega)
  have hcm : xCrit N σ 1 ∈ (innerCrit N σ).filter (strK σ ((posVals σ).max' hS)) :=
    Multiset.mem_filter.2 ⟨hmem, hc⟩
  have hcard := str_card_K_max N σ hσ hN hS
  have honly : ∀ z, strK σ ((posVals σ).max' hS) z → fR1 N σ z = 0 → z = xCrit N σ 1 := by
    intro z hz hfz
    by_contra h
    have hzm : z ∈ (innerCrit N σ).filter (strK σ ((posVals σ).max' hS)) :=
      Multiset.mem_filter.2 ⟨str_mem_innerCrit_of N σ hσ hS hm hz hfz, hz⟩
    have hsum := str_sum_count_le ((innerCrit N σ).filter (strK σ ((posVals σ).max' hS)))
      {xCrit N σ 1, z}
    rw [Finset.sum_pair (Ne.symm h)] at hsum
    have := Multiset.count_pos.2 hcm
    have := Multiset.count_pos.2 hzm
    omega
  have hR := str_R_max σ hS
  have hKleft : ∀ x ∈ Set.Ioo (-((posVals σ).max' hS)⁻¹) (xCrit N σ 1),
      strK σ ((posVals σ).max' hS) x := fun x hx => ⟨hx.1, hx.2.trans hc.2⟩
  have hKright : ∀ x ∈ Set.Ioo (xCrit N σ 1) 0, strK σ ((posVals σ).max' hS) x :=
    fun x hx => ⟨hc.1.trans hx.1, by rw [hR]; exact hx.2⟩
  refine ⟨?_, ?_⟩
  · exact str_neg_of_atTop_left (fun x hx => (str_hasDerivAt_K N σ hσ hS hm (hKleft x hx)).1)
      (str_contOn_K N σ hσ hS hm hKleft)
      (fun x hx h0 => by have := honly x (hKleft x hx) h0; linarith [hx.2])
      (str_tendsto_fR_pole N σ hσ hN hm)
  · exact str_pos_of_atTop_right (fun x hx => (str_hasDerivAt_K N σ hσ hS hm (hKright x hx)).1)
      (str_contOn_K N σ hσ hS hm hKright)
      (fun x hx h0 => by have := honly x (hKright x hx) h0; linarith [hx.1])
      (by rw [str_fR_eq N σ hσ]; exact str_tendsto_zero N σ 1)

/-- On the interval `I_l ∋ x_{2j}, x_{2j+1}`, `l ≥ 2`: `x_{2j+1} ≤ x_{2j}`, `f' < 0` on
`(-1/s, x_{2j+1})` and on `(x_{2j}, ·)`, and `f' > 0` on `(x_{2j+1}, x_{2j})`. -/
private lemma str_pair_shape (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {s : ℝ} (hs : s ∈ posVals σ) {j : ℕ} (hj : 1 ≤ j)
    (hj' : 2 * j + 1 < 2 * numBands N σ) (hK1 : strK σ s (xCrit N σ (2 * j)))
    (hK2 : strK σ s (xCrit N σ (2 * j + 1))) :
    s ≠ (posVals σ).max' hS ∧ xCrit N σ (2 * j + 1) ≤ xCrit N σ (2 * j) ∧
      (∀ x ∈ Set.Ioo (-s⁻¹) (xCrit N σ (2 * j + 1)), fR1 N σ x < 0) ∧
      (∀ x ∈ Set.Ioo (xCrit N σ (2 * j + 1)) (xCrit N σ (2 * j)), 0 < fR1 N σ x) ∧
      (∀ x ∈ Set.Ioo (xCrit N σ (2 * j)) (strR σ s), fR1 N σ x < 0) := by
  obtain ⟨s', hs', hmax, hK1', -, -, hcase⟩ := str_pair N σ hσ hN hS (j := j) hj hj'
  have hss : s' = s := by
    by_contra h
    exact str_K_disj σ hS hs' hs h hK1' hK1
  subst hss
  set c := xCrit N σ (2 * j + 1) with hcdef
  set d := xCrit N σ (2 * j) with hddef
  obtain ⟨hmemd, -⟩ := str_xCrit_spec N σ hσ hN hS (k := 2 * j) (by omega) (by omega)
  obtain ⟨hmemc, -⟩ := str_xCrit_spec N σ hσ hN hS (k := 2 * j + 1) (by omega) hj'
  have hfd := (str_mem_innerCrit N σ hσ hN hmemd).2.2
  have hfc := (str_mem_innerCrit N σ hσ hN hmemc).2.2
  have hdm : d ∈ (innerCrit N σ).filter (strK σ s') := Multiset.mem_filter.2 ⟨hmemd, hK1⟩
  have hcm : c ∈ (innerCrit N σ).filter (strK σ s') := Multiset.mem_filter.2 ⟨hmemc, hK2⟩
  have hcard : Multiset.card ((innerCrit N σ).filter (strK σ s')) = 2 := by
    rcases str_card_K_inner N σ hσ hN hS hs' hmax with h | h
    · rw [Multiset.card_eq_zero] at h
      rw [h] at hdm
      simp at hdm
    · exact h
  have hle : c ≤ d := by
    rcases hcase with ⟨h, -⟩ | ⟨h, -⟩
    · exact h.le
    · exact h.le
  have honly : ∀ z, strK σ s' z → fR1 N σ z = 0 → z = c ∨ z = d := by
    intro z hz hfz
    by_contra h
    rw [not_or] at h
    have hzm : z ∈ (innerCrit N σ).filter (strK σ s') :=
      Multiset.mem_filter.2 ⟨str_mem_innerCrit_of N σ hσ hS hs' hz hfz, hz⟩
    rcases hcase with ⟨hlt, -⟩ | ⟨heq, hf2⟩
    · have hsum := str_sum_count_le ((innerCrit N σ).filter (strK σ s')) {c, d, z}
      rw [Finset.sum_insert (by simp [hlt.ne, Ne.symm h.1]), Finset.sum_pair (Ne.symm h.2)]
        at hsum
      have := Multiset.count_pos.2 hcm
      have := Multiset.count_pos.2 hdm
      have := Multiset.count_pos.2 hzm
      omega
    · obtain ⟨hin, hnp, -⟩ := str_mem_innerCrit N σ hσ hN hmemd
      have hcount : (innerCrit N σ).count d = 2 := by
        rw [count_innerCrit N σ hσ hN hin hnp, ite_eq_left hfd, ite_eq_left hf2]
      have hsum := str_sum_count_le ((innerCrit N σ).filter (strK σ s')) {d, z}
      rw [Finset.sum_pair (Ne.symm h.2), Multiset.count_filter_of_pos hK1, hcount] at hsum
      have := Multiset.count_pos.2 hzm
      omega
  have hKleft : ∀ x ∈ Set.Ioo (-s'⁻¹) c, strK σ s' x := fun x hx => ⟨hx.1, hx.2.trans hK2.2⟩
  have hleft : ∀ x ∈ Set.Ioo (-s'⁻¹) c, fR1 N σ x < 0 :=
    str_neg_of_atTop_left (fun x hx => (str_hasDerivAt_K N σ hσ hS hs' (hKleft x hx)).1)
      (str_contOn_K N σ hσ hS hs' hKleft)
      (fun x hx h0 => by rcases honly x (hKleft x hx) h0 with h | h <;> linarith [hx.2])
      (str_tendsto_fR_pole N σ hσ hN hs')
  have hKright : ∀ x ∈ Set.Ioo d (strR σ s'), strK σ s' x :=
    fun x hx => ⟨hK1.1.trans hx.1, hx.2⟩
  obtain ⟨s'', hs'', -, -, hR⟩ := str_R_next σ hS hs' hmax
  have hright : ∀ x ∈ Set.Ioo d (strR σ s'), fR1 N σ x < 0 :=
    str_neg_of_atBot_right (fun x hx => (str_hasDerivAt_K N σ hσ hS hs' (hKright x hx)).1)
      (str_contOn_K N σ hσ hS hs' hKright)
      (fun x hx h0 => by rcases honly x (hKright x hx) h0 with h | h <;> linarith [hx.1])
      (by rw [hR, str_fR_eq N σ hσ]; exact (str_tendsto_pole N σ hN hs'' one_pos).2)
  refine ⟨hmax, hle, hleft, ?_, hright⟩
  rcases hcase with ⟨hlt, -⟩ | ⟨heq, -⟩
  · have hcount : (innerCrit N σ).count c = 1 := by
      have hsum := str_sum_count_le ((innerCrit N σ).filter (strK σ s')) {c, d}
      rw [Finset.sum_pair hlt.ne] at hsum
      have h1 := Multiset.count_pos.2 hcm
      have h2 := Multiset.count_pos.2 hdm
      rw [Multiset.count_filter_of_pos hK2] at h1 hsum
      omega
    obtain ⟨hc0, hcp⟩ := str_K_good σ hS hs' hK2
    have hf2 : fR2 N σ c ≠ 0 := by
      intro h
      have hin : InInner σ c := ⟨(str_K_sign σ hS hs' hK2).1, s', hs', (str_lt_iff
        (str_pos_of_mem σ hs')).1 hK2.1⟩
      have := count_innerCrit N σ hσ hN hin hcp
      rw [ite_eq_left hfc, ite_eq_left h] at this
      omega
    have hd2c := (str_hasDerivAt_K N σ hσ hS hs' hK2).2
    have hf2pos : 0 < fR2 N σ c := by
      rcases lt_or_gt_of_ne hf2 with h | h
      · exfalso
        obtain ⟨y, hy, hyv⟩ := str_deriv_left hd2c.neg (neg_pos.2 h) hK2.1
        have := hleft y hy
        simp only [Pi.neg_apply] at hyv
        linarith
      · exact h
    obtain ⟨y, hy, hyv⟩ := str_deriv_right hd2c hf2pos hlt
    rw [hfc] at hyv
    have hKcd : ∀ x ∈ Set.Ioo c d, strK σ s' x := fun x hx => ⟨hK2.1.trans hx.1, hx.2.trans hK1.2⟩
    exact fun x hx => str_sign (str_contOn_K N σ hσ hS hs' hKcd)
      (fun z hz h0 => by rcases honly z (hKcd z hz) h0 with h | h <;> linarith [hz.1, hz.2])
      hy hx hyv
  · intro x hx
    exfalso
    have := hx.1.trans hx.2
    rw [heq] at this
    exact lt_irrefl _ this

/-- An interval `I_l`, `l ≥ 2`, with two critical points contains `x_{2j}, x_{2j+1}` for some
`j ≥ 1` with `2j + 1 < 2p`. -/
private lemma str_K_index (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {s : ℝ} (hs : s ∈ posVals σ) (hne : s ≠ (posVals σ).max' hS)
    (hcard : Multiset.card ((innerCrit N σ).filter (strK σ s)) = 2) :
    ∃ j, 1 ≤ j ∧ 2 * j + 1 < 2 * numBands N σ ∧ strK σ s (xCrit N σ (2 * j)) ∧
      strK σ s (xCrit N σ (2 * j + 1)) := by
  have hp := card_innerCrit N σ hσ hN hS
  rcases str_lo N σ hσ hN hS hs with ⟨h, -, -⟩ | ⟨-, ⟨c, hc⟩, -⟩
  · exact absurd h hne
  have hsplit := str_A_split N σ hσ hN hS hs
  have hA : strA N σ (-s⁻¹) ≤ Multiset.card (innerCrit N σ) :=
    Multiset.card_le_card (Multiset.filter_le _ _)
  refine ⟨c + 1, by omega, by omega, ?_, ?_⟩
  · exact (str_block N σ hσ hN hS hs (k := 2 * (c + 1)) (by omega) (by omega)).2
      ⟨by omega, by omega⟩
  · exact (str_block N σ hσ hN hS hs (k := 2 * (c + 1) + 1) (by omega) (by omega)).2
      ⟨by omega, by omega⟩

/-- In `I_1, …, I_n`, the values of `f` at points with `f' > 0` lie in the gaps `(a_1, ∞)` and
`(a_{2j+1}, a_{2j})`. -/
private lemma str_K_gap (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {s : ℝ} (hs : s ∈ posVals σ) {x : ℝ} (hx : strK σ s x)
    (hd : 0 < fR1 N σ x) :
    edgeVal N σ 1 < fR N σ x ∨ ∃ j, 1 ≤ j ∧ 2 * j + 1 < 2 * numBands N σ ∧
      edgeVal N σ (2 * j + 1) < fR N σ x ∧ fR N σ x < edgeVal N σ (2 * j) := by
  have hp := card_innerCrit N σ hσ hN hS
  by_cases hmax : s = (posVals σ).max' hS
  · subst hmax
    left
    have hm := (posVals σ).max'_mem hS
    have hc := str_first N σ hσ hN hS
    obtain ⟨hmem, -⟩ := str_xCrit_spec N σ hσ hN hS le_rfl (by omega)
    have hfc := (str_mem_innerCrit N σ hσ hN hmem).2.2
    obtain ⟨hleft, hright⟩ := str_first_shape N σ hσ hN hS
    have hR := str_R_max σ hS
    rw [str_edgeVal_ne N σ (by omega : 1 ≠ 2 * numBands N σ)]
    rcases lt_trichotomy x (xCrit N σ 1) with h | h | h
    · exact absurd (hleft x ⟨hx.1, h⟩) (not_lt.2 hd.le)
    · rw [h] at hd
      exact absurd hfc hd.ne'
    · have hx0 : x < 0 := by have := hx.2; rwa [hR] at this
      have hmono := str_strictMonoOn N σ hσ hS hm hc hx fun z hz => hright z ⟨hz.1, hz.2.trans hx0⟩
      exact hmono ⟨le_rfl, h.le⟩ ⟨h.le, le_rfl⟩ h
  · right
    rcases str_card_K_inner N σ hσ hN hS hs hmax with h0 | h2
    · exfalso
      have hK : ∀ z ∈ Set.Ioo (-s⁻¹) (strR σ s), strK σ s z := fun z hz => hz
      have hneg := str_neg_of_atTop_left
        (fun z hz => (str_hasDerivAt_K N σ hσ hS hs (hK z hz)).1) (str_contOn_K N σ hσ hS hs hK)
        (fun z hz hz0 => by
          have hzm : z ∈ (innerCrit N σ).filter (strK σ s) :=
            Multiset.mem_filter.2 ⟨str_mem_innerCrit_of N σ hσ hS hs hz hz0, hz⟩
          rw [Multiset.card_eq_zero] at h0
          rw [h0] at hzm
          simp at hzm)
        (str_tendsto_fR_pole N σ hσ hN hs) x hx
      linarith
    · obtain ⟨j, hj, hj', hK1, hK2⟩ := str_K_index N σ hσ hN hS hs hmax h2
      obtain ⟨-, hle, hleft, hmid, hright⟩ := str_pair_shape N σ hσ hN hS hs hj hj' hK1 hK2
      obtain ⟨hmemd, -⟩ := str_xCrit_spec N σ hσ hN hS (k := 2 * j) (by omega) (by omega)
      obtain ⟨hmemc, -⟩ := str_xCrit_spec N σ hσ hN hS (k := 2 * j + 1) (by omega) hj'
      have hfd := (str_mem_innerCrit N σ hσ hN hmemd).2.2
      have hfc := (str_mem_innerCrit N σ hσ hN hmemc).2.2
      refine ⟨j, hj, hj', ?_⟩
      rw [str_edgeVal_ne N σ (by omega : 2 * j + 1 ≠ 2 * numBands N σ),
        str_edgeVal_ne N σ (by omega : 2 * j ≠ 2 * numBands N σ)]
      have h1 : xCrit N σ (2 * j + 1) < x := by
        rcases lt_trichotomy x (xCrit N σ (2 * j + 1)) with h | h | h
        · exact absurd (hleft x ⟨hx.1, h⟩) (not_lt.2 hd.le)
        · rw [h] at hd
          exact absurd hfc hd.ne'
        · exact h
      have h2 : x < xCrit N σ (2 * j) := by
        rcases lt_trichotomy x (xCrit N σ (2 * j)) with h | h | h
        · exact h
        · rw [h] at hd
          exact absurd hfd hd.ne'
        · exact absurd (hright x ⟨h, hx.2⟩) (not_lt.2 hd.le)
      have hmono := str_strictMonoOn N σ hσ hS hs hK2 hK1 hmid
      exact ⟨hmono ⟨le_rfl, hle⟩ ⟨h1.le, h2.le⟩ h1, hmono ⟨h1.le, h2.le⟩ ⟨hle, le_rfl⟩ h2⟩

/-- A gap value in `(a_1, ∞)` is `f(x)` with `x ∈ (x_1, 0)`, `f'(x) > 0`. -/
private lemma str_first_preimage (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {E : ℝ} (hE : edgeVal N σ 1 < E) :
    ∃ x, strK σ ((posVals σ).max' hS) x ∧ fR N σ x = E ∧ 0 < fR1 N σ x := by
  have hp := card_innerCrit N σ hσ hN hS
  have hm := (posVals σ).max'_mem hS
  have hc := str_first N σ hσ hN hS
  have hR := str_R_max σ hS
  obtain ⟨-, hright⟩ := str_first_shape N σ hσ hN hS
  rw [str_edgeVal_ne N σ (by omega : 1 ≠ 2 * numBands N σ)] at hE
  have hc0 : xCrit N σ 1 < 0 := by have := hc.2; rwa [hR] at this
  obtain ⟨z, h1, h2⟩ := (((str_tendsto_zero N σ 1).eventually (eventually_gt_atTop E)).and
    (Ioo_mem_nhdsLT hc0)).exists
  rw [← str_fR_eq N σ hσ] at h1
  have hzK : strK σ ((posVals σ).max' hS) z := ⟨hc.1.trans h2.1, by rw [hR]; exact h2.2⟩
  obtain ⟨x, hx, hxE⟩ := str_ivt h2.1.le (str_cont_K N σ hS 1 hm hc hzK) (Or.inl
    ⟨by rw [← str_fR_eq N σ hσ]; exact hE, by rw [← str_fR_eq N σ hσ]; exact h1⟩)
  rw [← str_fR_eq N σ hσ] at hxE
  exact ⟨x, ⟨hc.1.trans hx.1, hx.2.trans hzK.2⟩, hxE, hright x ⟨hx.1, hx.2.trans h2.2⟩⟩

/-- A gap value in `(a_{2j+1}, a_{2j})` is `f(x)` with `x ∈ (x_{2j+1}, x_{2j})`, `f'(x) > 0`. -/
private lemma str_pair_preimage (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {j : ℕ} (hj : 1 ≤ j) (hj' : 2 * j + 1 < 2 * numBands N σ)
    {E : ℝ} (hE1 : edgeVal N σ (2 * j + 1) < E) (hE2 : E < edgeVal N σ (2 * j)) :
    ∃ x, x ≠ 0 ∧ (∀ s ∈ posVals σ, 1 + s * x ≠ 0) ∧ fR N σ x = E ∧ 0 < fR1 N σ x := by
  obtain ⟨s, hs, -, hK1, hK2, -, -⟩ := str_pair N σ hσ hN hS (j := j) hj hj'
  obtain ⟨-, hle, -, hmid, -⟩ := str_pair_shape N σ hσ hN hS hs hj hj' hK1 hK2
  rw [str_edgeVal_ne N σ (by omega : 2 * j + 1 ≠ 2 * numBands N σ)] at hE1
  rw [str_edgeVal_ne N σ (by omega : 2 * j ≠ 2 * numBands N σ)] at hE2
  rw [str_fR_eq N σ hσ] at hE1 hE2
  obtain ⟨x, hx, hxE⟩ := str_ivt hle (str_cont_K N σ hS 1 hs hK2 hK1) (Or.inl ⟨hE1, hE2⟩)
  rw [← str_fR_eq N σ hσ] at hxE
  have hxK : strK σ s x := ⟨hK2.1.trans hx.1, hx.2.trans hK1.2⟩
  obtain ⟨h0, hp⟩ := str_K_good σ hS hs hxK
  exact ⟨x, h0, hp, hxE, hmid x hx⟩

/-! ## Gap values in `I_0` -/

private lemma str_hasDerivAt_FChart (N : ℕ) (σ : Fin M → ℝ) {y : ℝ} (hy : InChart σ y) :
    HasDerivAt (FChart N σ) (FChart1 N σ y) y := by
  have hterm : ∀ s ∈ posVals σ, HasDerivAt (fun t : ℝ => weight N σ s * s * t / (t + s))
      (weight N σ s * s ^ 2 / (y + s) ^ 2) y := by
    intro s hs
    have hne := (hy s hs).ne'
    have h1 : HasDerivAt (fun t : ℝ => weight N σ s * s * t) (weight N σ s * s) y := by
      simpa using (hasDerivAt_id y).const_mul (weight N σ s * s)
    have h2 : HasDerivAt (fun t : ℝ => t + s) 1 y := by
      simpa using (hasDerivAt_id y).add_const s
    convert h1.div h2 hne using 1
    field_simp
    ring
  have h := (hasDerivAt_id y).neg.add (HasDerivAt.fun_sum hterm)
  unfold FChart FChart1
  convert h using 1
  funext t
  simp

/-- `F'` is strictly decreasing on the chart. -/
private lemma str_FChart1_lt (N : ℕ) (σ : Fin M → ℝ) (hN : 0 < N) (hS : (posVals σ).Nonempty)
    {y y' : ℝ} (hy : InChart σ y) (hyy : y < y') : FChart1 N σ y' < FChart1 N σ y := by
  unfold FChart1
  have : ∑ s ∈ posVals σ, weight N σ s * s ^ 2 / (y' + s) ^ 2 <
      ∑ s ∈ posVals σ, weight N σ s * s ^ 2 / (y + s) ^ 2 := by
    refine Finset.sum_lt_sum_of_nonempty hS fun s hs => ?_
    have h0 := hy s hs
    have hw := str_weight_pos N σ hN hs
    have hs0 := str_pos_of_mem σ hs
    have hsq : (y + s) ^ 2 < (y' + s) ^ 2 := by nlinarith
    exact div_lt_div_of_pos_left (by positivity) (by positivity) hsq
  linarith

private lemma str_InChart_of_le {σ : Fin M → ℝ} {y y' : ℝ} (hy : InChart σ y) (hyy : y ≤ y') :
    InChart σ y' := fun s hs => by have := hy s hs; linarith

/-- In `I_0`, the values of `f` at points with `f' > 0` lie in `(-∞, a_{2p})`. -/
private lemma str_I0_gap (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {x : ℝ} (hx : strI0 σ x) (hd : 0 < fR1 N σ x) :
    fR N σ x < edgeVal N σ (2 * numBands N σ) := by
  obtain ⟨hyC, hyF⟩ := yEdge_spec N σ hσ hN hS
  obtain ⟨hx0, -⟩ := str_I0_good σ hS hx
  set y := x⁻¹ with hydef
  have hy0 : y ≠ 0 := inv_ne_zero hx0
  have hyc : InChart σ y := by
    intro s hs
    have hs0 := str_pos_of_mem σ hs
    rcases hx with h | h
    · have : 0 < y := inv_pos.2 h
      linarith
    · have h1 := h s hs
      have hxn : x < 0 := by
        by_contra hc
        have := mul_nonneg hs0.le (not_lt.1 hc)
        linarith
      have e : y + s = (1 + s * x) / x := by rw [hydef]; field_simp
      rw [e]
      exact div_pos_of_neg_of_neg h1 hxn
  have hxy : x = y⁻¹ := by rw [hydef, inv_inv]
  rw [hxy, str_fR1_inv N σ hσ hy0 hyc] at hd
  have hF1 : FChart1 N σ y < 0 := by
    have : 0 < y ^ 2 := pow_two_pos_of_ne_zero hy0
    nlinarith
  have hlt : yEdge N σ < y := by
    by_contra h
    rcases (not_lt.1 h).lt_or_eq with h | h
    · have := str_FChart1_lt N σ hN hS hyc h
      linarith
    · rw [← h] at hyF
      linarith
  have hanti : StrictAntiOn (FChart N σ) (Set.Icc (yEdge N σ) y) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _) (fun t ht =>
      (str_hasDerivAt_FChart N σ (str_InChart_of_le hyC ht.1)).continuousAt.continuousWithinAt)
      fun t ht => ?_
    rw [interior_Icc] at ht
    rw [(str_hasDerivAt_FChart N σ (str_InChart_of_le hyC ht.1.le)).deriv]
    have := str_FChart1_lt N σ hN hS hyC ht.1
    linarith
  rw [hxy, fR_inv_eq_FChart N σ hσ hy0, str_edgeVal_last]
  exact hanti ⟨le_rfl, hlt.le⟩ ⟨hlt.le, le_rfl⟩ hlt

/-- A gap value in `(0, a_{2p})` is `f(x)` with `x ∈ I_0`, `f'(x) > 0`. -/
private lemma str_I0_preimage (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {E : ℝ} (hE0 : 0 < E)
    (hE : E < edgeVal N σ (2 * numBands N σ)) :
    ∃ x, x ≠ 0 ∧ (∀ s ∈ posVals σ, 1 + s * x ≠ 0) ∧ fR N σ x = E ∧ 0 < fR1 N σ x := by
  obtain ⟨hyC, hyF⟩ := yEdge_spec N σ hσ hN hS
  rw [str_edgeVal_last] at hE
  set C := ∑ s ∈ posVals σ, weight N σ s * s with hC
  set Y := max (yEdge N σ) 0 + C + |E| + 1 with hY
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun s hs => by
    have := str_pos_of_mem σ hs
    have : 0 ≤ weight N σ s := by unfold weight; positivity
    positivity
  have hY0 : 0 < Y := by have := le_max_right (yEdge N σ) 0; have := abs_nonneg E; linarith
  have hyY : yEdge N σ < Y := by have := le_max_left (yEdge N σ) 0; have := abs_nonneg E; linarith
  have hFY : FChart N σ Y < E := by
    have hle : ∑ s ∈ posVals σ, weight N σ s * s * Y / (Y + s) ≤ C := by
      refine Finset.sum_le_sum fun s hs => ?_
      have hs0 := str_pos_of_mem σ hs
      have hw : 0 ≤ weight N σ s := by unfold weight; positivity
      rw [div_le_iff₀ (by linarith)]
      nlinarith [mul_nonneg hw hs0.le]
    unfold FChart
    have := le_max_right (yEdge N σ) 0
    have := le_abs_self E
    linarith
  have hcont : ContinuousOn (FChart N σ) (Set.Icc (yEdge N σ) Y) := fun t ht =>
    (str_hasDerivAt_FChart N σ (str_InChart_of_le hyC ht.1)).continuousAt.continuousWithinAt
  obtain ⟨y, hy, hyE⟩ := intermediate_value_Ioo' hyY.le hcont ⟨hFY, hE⟩
  have hyc : InChart σ y := str_InChart_of_le hyC hy.1.le
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp [FChart] at hyE
    linarith
  have hF1 : FChart1 N σ y < 0 := by
    have := str_FChart1_lt N σ hN hS hyC hy.1
    linarith
  obtain ⟨h0, hp⟩ := str_I0_good σ hS (str_I0_inv σ hy0 hyc)
  refine ⟨y⁻¹, h0, hp, by rw [fR_inv_eq_FChart N σ hσ hy0]; exact hyE, ?_⟩
  rw [str_fR1_inv N σ hσ hy0 hyc]
  have : 0 < y ^ 2 := pow_two_pos_of_ne_zero hy0
  nlinarith

/-! ## Values of `f` at points with `f' ≥ 0` -/

/-- A real point off `0` and the poles lies in `I_0` or in one of `I_1, …, I_n`. -/
private lemma str_classify (σ : Fin M → ℝ) (hS : (posVals σ).Nonempty) {x : ℝ} (hx : x ≠ 0)
    (hx' : ∀ s ∈ posVals σ, 1 + s * x ≠ 0) : strI0 σ x ∨ ∃ s ∈ posVals σ, strK σ s x := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · by_cases h : ∃ s ∈ posVals σ, 0 < 1 + s * x
    · exact Or.inr (str_exists_K σ hS hneg hx' h)
    · push Not at h
      exact Or.inl (Or.inr fun s hs => lt_of_le_of_ne (h s hs) (hx' s hs))
  · exact Or.inl (Or.inl hpos)

/-- Gap values: `f'(x) > 0` puts `f(x)` in `(a_1, ∞)`, in some `(a_{2j+1}, a_{2j})`, or in
`(-∞, a_{2p})`. -/
private lemma str_gap (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {x : ℝ} (hx : x ≠ 0) (hx' : ∀ s ∈ posVals σ, 1 + s * x ≠ 0)
    (hd : 0 < fR1 N σ x) :
    edgeVal N σ 1 < fR N σ x ∨ (∃ j, 1 ≤ j ∧ 2 * j + 1 < 2 * numBands N σ ∧
      edgeVal N σ (2 * j + 1) < fR N σ x ∧ fR N σ x < edgeVal N σ (2 * j)) ∨
      fR N σ x < edgeVal N σ (2 * numBands N σ) := by
  rcases str_classify σ hS hx hx' with h | ⟨s, hs, hK⟩
  · exact Or.inr (Or.inr (str_I0_gap N σ hσ hN hS h hd))
  · rcases str_K_gap N σ hσ hN hS hs hK hd with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

/-- Critical values: `f'(x) = 0` gives `f(x) = a_i` for some `i ≤ 2p`. -/
private lemma str_crit_value (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {x : ℝ} (hx : x ≠ 0) (hx' : ∀ s ∈ posVals σ, 1 + s * x ≠ 0)
    (hd : fR1 N σ x = 0) : ∃ i, 1 ≤ i ∧ i ≤ 2 * numBands N σ ∧ fR N σ x = edgeVal N σ i := by
  rcases str_classify σ hS hx hx' with h | ⟨s, hs, hK⟩
  · have hp := card_innerCrit N σ hσ hN hS
    refine ⟨2 * numBands N σ, by omega, le_rfl, ?_⟩
    set y := x⁻¹ with hydef
    have hy0 : y ≠ 0 := inv_ne_zero hx
    have hyc : InChart σ y := by
      intro s hs
      have hs0 := str_pos_of_mem σ hs
      rcases h with h | h
      · have : 0 < y := inv_pos.2 h
        linarith
      · have h1 := h s hs
        have hxn : x < 0 := by
          by_contra hc
          have := mul_nonneg hs0.le (not_lt.1 hc)
          linarith
        have e : y + s = (1 + s * x) / x := by rw [hydef]; field_simp
        rw [e]
        exact div_pos_of_neg_of_neg h1 hxn
    have hxy : x = y⁻¹ := by rw [hydef, inv_inv]
    rw [hxy, str_fR1_inv N σ hσ hy0 hyc] at hd
    have hF1 : FChart1 N σ y = 0 := by
      rcases mul_eq_zero.1 hd with h | h
      · exact absurd (neg_eq_zero.1 h) (pow_ne_zero 2 hy0)
      · exact h
    have hyy : y = yEdge N σ :=
      (existsUnique_yEdge N σ hσ hN hS).unique ⟨hyc, hF1⟩ (yEdge_spec N σ hσ hN hS)
    rw [hxy, fR_inv_eq_FChart N σ hσ hy0, str_edgeVal_last, hyy]
  · have hmem := str_mem_innerCrit_of N σ hσ hS hs hK hd
    obtain ⟨k, hk1, hk, hxk⟩ := str_xCrit_surj N σ hσ hN hS hmem
    exact ⟨k, hk1, hk.le, by rw [str_edgeVal_ne N σ hk.ne, hxk]⟩

/-! ## Real roots of `P_E` -/

/-- `P_E` for real `E` is the complexification of the real polynomial `P^1_E`. -/
private lemma str_scPoly_eq_map (N : ℕ) (σ : Fin M → ℝ) (E : ℝ) :
    scPoly N σ (E : ℂ) = (strP N σ 1 E).map (algebraMap ℝ ℂ) := by
  simp [scPoly, strP, Polynomial.map_prod, Polynomial.map_sum]

/-- If the multiplicities of the real roots in `T` fill the degree, every complex root of `P` is
one of the points of `T`. -/
private lemma str_root_mem (P : ℝ[X]) (hP : P ≠ 0) (T : Finset ℝ)
    (hT : P.natDegree ≤ ∑ x ∈ T, P.rootMultiplicity x) {w : ℂ}
    (hw : (P.map (algebraMap ℝ ℂ)).eval w = 0) : ∃ x ∈ T, w = (x : ℂ) := by
  have hsum : ∑ x ∈ T, P.roots.count x ≤ Multiset.card P.roots := str_sum_count_le _ _
  simp_rw [count_roots] at hsum
  have hcard : Multiset.card P.roots = P.natDegree := le_antisymm (card_roots' P) (hT.trans hsum)
  have hsplit := C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  have hev := congrArg (fun q : ℝ[X] => (q.map (algebraMap ℝ ℂ)).eval w) hsplit
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_multiset_prod,
    Multiset.map_map, Function.comp_def, Polynomial.map_sub, Polynomial.map_X, eval_mul,
    eval_C, eval_multiset_prod, eval_sub, eval_X] at hev
  rw [hw] at hev
  have hlc : (algebraMap ℝ ℂ) P.leadingCoeff ≠ 0 := by
    rw [map_ne_zero_iff _ (algebraMap ℝ ℂ).injective]
    exact leadingCoeff_ne_zero.2 hP
  obtain ⟨a, ha, hwa⟩ : ∃ a ∈ P.roots, w - (algebraMap ℝ ℂ) a = 0 := by
    have h0 := (mul_eq_zero.1 hev).resolve_left hlc
    obtain ⟨a, ha, hb0⟩ := Multiset.mem_map.1 (Multiset.prod_eq_zero_iff.1 h0)
    exact ⟨a, ha, hb0⟩
  refine ⟨a, ?_, by rw [sub_eq_zero] at hwa; simpa using hwa⟩
  by_contra haT
  have h2 := str_sum_count_le P.roots (insert a T)
  rw [Finset.sum_insert haT] at h2
  have h3 := Multiset.count_pos.2 ha
  simp_rw [count_roots] at h2
  rw [count_roots] at h3
  omega

/-- The root budget with lower bounds `default + e(u)` on the multiplicities in each `I_l`. -/
private lemma str_count_lb (N : ℕ) (σ : Fin M → ℝ) (hS : (posVals σ).Nonempty) (E : ℝ)
    (A : ℝ → Finset ℝ) (hA : ∀ u ∈ posVals σ, ∀ x ∈ A u, strK σ u x) (e : ℝ → ℕ)
    (he : ∀ u ∈ posVals σ, (if u = (posVals σ).max' hS then 0 else 1) + e u ≤
      ∑ x ∈ A u, (strP N σ 1 E).rootMultiplicity x) :
    (posVals σ).card - 1 + ∑ u ∈ posVals σ, e u ≤
      ∑ x ∈ (posVals σ).biUnion A, (strP N σ 1 E).rootMultiplicity x := by
  have hpd : ((posVals σ : Set ℝ)).PairwiseDisjoint A := by
    intro s hs s' hs' hne
    change Disjoint (A s) (A s')
    refine Finset.disjoint_left.2 fun x hx hx' => ?_
    exact str_K_disj σ hS hs hs' hne (hA s hs x hx) (hA s' hs' x hx')
  rw [Finset.sum_biUnion hpd]
  exact str_sum_lb (posVals σ) hS _ e he

/-- A real root `x` of `P_E`, `E ≠ 0`, is a point off `0` and the poles with `f(x) = E`. -/
private lemma str_real_root (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {E : ℝ}
    {x : ℝ} (hx : (scPoly N σ E).eval (x : ℂ) = 0) :
    x ≠ 0 ∧ (∀ s ∈ posVals σ, 1 + s * x ≠ 0) ∧ fR N σ x = E := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [Complex.ofReal_zero, scPoly_eval_zero] at hx
    norm_num at hx
  have hxp : ∀ s ∈ posVals σ, 1 + s * x ≠ 0 := by
    intro s hs h
    have hs0 := str_pos_of_mem σ hs
    have e : (x : ℂ) = -((s : ℂ))⁻¹ := by
      have : x = -s⁻¹ := by field_simp; linarith
      rw [this]
      push_cast
      ring
    rw [e] at hx
    exact scPoly_eval_pole N σ hN _ hs hx
  refine ⟨hx0, hxp, ?_⟩
  have hxpC : ∀ s ∈ posVals σ, 1 + (s : ℂ) * x ≠ 0 := fun s hs => by exact_mod_cast hxp s hs
  rw [scPoly_eval N σ hσ _ (by exact_mod_cast hx0) hxpC] at hx
  have hprod : (x : ℂ) * ∏ s ∈ posVals σ, (1 + (s : ℂ) * x) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hx0) (Finset.prod_ne_zero_iff.2 hxpC)
  have := sub_eq_zero.1 ((mul_eq_zero.1 hx).resolve_left hprod)
  rw [fC_ofReal] at this
  exact_mod_cast this

/-! ## `x_k = m(a_k)` (Lemma 2.5) -/

/-- If `x(t) → ξ` along a nontrivial filter with `f'(x(t)) > 0` and `f(x(t)) → E ≠ 0`, then
`m(E) = ξ`: `m(f(x(t))) = x(t)` by the sign lemma, and `m` is continuous at `E`. -/
private lemma str_mExt_eq_of_tendsto (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    {L : Filter ℝ} [L.NeBot] {g : ℝ → ℝ} {ξ E : ℝ} (hE : E ≠ 0) (hg : Tendsto g L (𝓝 ξ))
    (hfg : Tendsto (fun t => fR N σ (g t)) L (𝓝 E))
    (hev : ∀ᶠ t in L, g t ≠ 0 ∧ (∀ i, 1 + σ i * g t ≠ 0) ∧ fR N σ (g t) ≠ 0 ∧
      0 < fR1 N σ (g t)) :
    mExt N σ E = ξ := by
  have hmem : ((E : ℂ)) ∈ upperHalf ∪ {z : ℂ | z.im = 0 ∧ z ≠ 0} :=
    Or.inr ⟨Complex.ofReal_im E, Complex.ofReal_ne_zero.mpr hE⟩
  have hc := (continuousOn_mExt N σ hσ _ hmem).tendsto
  have h1 : Tendsto (fun t => ((fR N σ (g t) : ℝ) : ℂ)) L
      (𝓝[upperHalf ∪ {z : ℂ | z.im = 0 ∧ z ≠ 0}] (E : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨(Complex.continuous_ofReal.tendsto E).comp hfg, ?_⟩
    filter_upwards [hev] with t ht
    exact Or.inr ⟨Complex.ofReal_im _, Complex.ofReal_ne_zero.mpr ht.2.2.1⟩
  have h3 : Tendsto (fun t => mExt N σ ((fR N σ (g t) : ℝ) : ℂ)) L (𝓝 (ξ : ℂ)) := by
    refine ((Complex.continuous_ofReal.tendsto ξ).comp hg).congr' ?_
    filter_upwards [hev] with t ht
    exact (mExt_fR_of_pos N σ hσ hN ht.1 ht.2.1 ht.2.2.1 ht.2.2.2).symm
  exact tendsto_nhds_unique (hc.comp h1) h3

/-- `m(f(ξ)) = ξ` at a critical point `ξ` with `f''(ξ) ≠ 0` and `f(ξ) ≠ 0`. -/
private lemma str_mExt_crit (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {ξ : ℝ}
    (hx : ξ ≠ 0) (hx' : ∀ i, 1 + σ i * ξ ≠ 0) (h1 : fR1 N σ ξ = 0) (h2 : fR2 N σ ξ ≠ 0)
    (hf : fR N σ ξ ≠ 0) : mExt N σ (fR N σ ξ) = ξ := by
  have hd1 := hasDerivAt_fR1 N σ hx hx'
  have hcf := (hasDerivAt_fR N σ hx hx').continuousAt
  have hgood : ∀ᶠ t in 𝓝 ξ, t ≠ 0 ∧ (∀ i, 1 + σ i * t ≠ 0) ∧ fR N σ t ≠ 0 := by
    refine (eventually_ne_nhds hx).and ((Filter.eventually_all.2 fun i => ?_).and
      (hcf.eventually_ne hf))
    have hc : Continuous fun t : ℝ => 1 + σ i * t := by fun_prop
    exact hc.continuousAt.eventually_ne (hx' i)
  have hs := hasDerivAt_iff_tendsto_slope.mp hd1
  rcases lt_or_gt_of_ne h2 with hneg | hpos
  · have hsl : ∀ᶠ t in 𝓝[<] ξ, slope (fR1 N σ) ξ t < 0 :=
      (hs.mono_left (nhdsWithin_mono _ fun y hy => ne_of_lt hy)).eventually (gt_mem_nhds hneg)
    refine str_mExt_eq_of_tendsto N σ hσ hN (L := 𝓝[<] ξ) (g := id) hf nhdsWithin_le_nhds
      (hcf.tendsto.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [hsl, nhdsWithin_le_nhds hgood, self_mem_nhdsWithin] with t ht hg hlt
    refine ⟨hg.1, hg.2.1, hg.2.2, ?_⟩
    rw [slope_def_field, h1, sub_zero] at ht
    have : t - ξ < 0 := by linarith [show t < ξ from hlt]
    rcases div_neg_iff.mp ht with ⟨h, _⟩ | ⟨_, h⟩
    · exact h
    · linarith
  · have hsl : ∀ᶠ t in 𝓝[>] ξ, 0 < slope (fR1 N σ) ξ t :=
      (hs.mono_left (nhdsWithin_mono _ fun y hy => ne_of_gt hy)).eventually (lt_mem_nhds hpos)
    refine str_mExt_eq_of_tendsto N σ hσ hN (L := 𝓝[>] ξ) (g := id) hf nhdsWithin_le_nhds
      (hcf.tendsto.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [hsl, nhdsWithin_le_nhds hgood, self_mem_nhdsWithin] with t ht hg hlt
    refine ⟨hg.1, hg.2.1, hg.2.2, ?_⟩
    rw [slope_def_field, h1, sub_zero] at ht
    have : 0 < t - ξ := by linarith [show ξ < t from hlt]
    rcases div_pos_iff.mp ht with ⟨h, _⟩ | ⟨_, h⟩
    · exact h
    · linarith

/-- `m(a_{2p}) = x_{2p}` when `x_{2p} = 1/y_{2p}` is finite. -/
private lemma str_mExt_last (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) (hy0 : yEdge N σ ≠ 0) :
    mExt N σ (FChart N σ (yEdge N σ)) = (yEdge N σ)⁻¹ := by
  obtain ⟨hyC, hyF⟩ := yEdge_spec N σ hσ hN hS
  set y := yEdge N σ with hydef
  have hE := str_FChart_pos N σ hN hS hyC hy0 hyF
  have hcF := (str_hasDerivAt_FChart N σ hyC).continuousAt
  have hchart : ∀ᶠ t in 𝓝 y, InChart σ t := by
    rw [show (∀ᶠ t in 𝓝 y, InChart σ t) ↔ ∀ᶠ t in 𝓝 y, ∀ s ∈ posVals σ, 0 < t + s from Iff.rfl,
      Filter.eventually_all_finset]
    intro s hs
    have hc : Continuous fun t : ℝ => t + s := by fun_prop
    exact hc.continuousAt.eventually (lt_mem_nhds (hyC s hs))
  have hgood : ∀ᶠ t in 𝓝 y, t ≠ 0 ∧ InChart σ t ∧ FChart N σ t ≠ 0 :=
    (eventually_ne_nhds hy0).and (hchart.and (hcF.eventually_ne hE.ne'))
  have hfg : Tendsto (fun t => fR N σ t⁻¹) (𝓝[>] y) (𝓝 (FChart N σ y)) := by
    refine (hcF.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [nhdsWithin_le_nhds hgood] with t ht
    exact (fR_inv_eq_FChart N σ hσ ht.1).symm
  refine str_mExt_eq_of_tendsto N σ hσ hN (L := 𝓝[>] y) (g := fun t => t⁻¹) hE.ne'
    (((continuousAt_inv₀ hy0).tendsto).mono_left nhdsWithin_le_nhds) hfg ?_
  filter_upwards [nhdsWithin_le_nhds hgood, self_mem_nhdsWithin] with t ht hlt
  obtain ⟨h0, hp⟩ := str_I0_good σ hS (str_I0_inv σ ht.1 ht.2.1)
  refine ⟨h0, str_nonpole_all σ hσ hp, by rw [fR_inv_eq_FChart N σ hσ ht.1]; exact ht.2.2, ?_⟩
  rw [str_fR1_inv N σ hσ ht.1 ht.2.1]
  have := str_FChart1_lt N σ hN hS hyC (show y < t from hlt)
  have : 0 < t ^ 2 := pow_two_pos_of_ne_zero ht.1
  nlinarith

/-- `m(f(ξ)) = ξ` at a degenerate critical point `ξ` (`f'(ξ) = f''(ξ) = 0`) with `f(ξ) ≠ 0`:
`ξ` is a triple root of `P_{f(ξ)}`, the `n - 2` default roots fill the degree, so every root is
real; a default root `x` with `f'(x) < 0` is excluded by the sign lemma, and `f'(x) ≥ 0` would
exceed the root budget. -/
private lemma str_mExt_degen (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {ξ : ℝ} (hξ : ξ ∈ innerCrit N σ) (h2 : fR2 N σ ξ = 0)
    (hE : fR N σ ξ ≠ 0) : mExt N σ (fR N σ ξ) = ξ := by
  obtain ⟨hin, hnp, h1⟩ := str_mem_innerCrit N σ hσ hN hξ
  obtain ⟨s, hs, hK⟩ := str_mem_K N σ hσ hN hS hξ
  set E := fR N σ ξ with hEdef
  set P := strP N σ 1 E with hPdef
  have hm3 : 3 ≤ P.rootMultiplicity ξ := (str_mult_crit N σ hσ E hin.1.ne hnp rfl h1).2 h2
  have hdef : ∀ u ∈ posVals σ, u ≠ (posVals σ).max' hS → ∃ r, strK σ u r ∧ strF N σ 1 r = E :=
    fun u hu hne => str_root_default N σ hN hS one_pos E hu hne
  choose! rd hrd using hdef
  have hrdμ : ∀ u ∈ posVals σ, u ≠ (posVals σ).max' hS → 1 ≤ P.rootMultiplicity (rd u) := by
    intro u hu hne
    obtain ⟨h0, h1'⟩ := str_K_good σ hS hu (hrd u hu hne).1
    exact str_mult_one N σ 1 E h0 h1' (hrd u hu hne).2
  have hcard1 : 1 ≤ (posVals σ).card := Finset.card_pos.2 hS
  have hdeg := (str_natDegree_P N σ 1 E).1
  let A : ℝ → Finset ℝ := fun u => if u = s then {ξ} else
    if u = (posVals σ).max' hS then ∅ else {rd u}
  have hA : ∀ u ∈ posVals σ, ∀ x ∈ A u, strK σ u x := by
    intro u hu x hx
    simp only [A] at hx
    split_ifs at hx with hus hum
    · rw [Finset.mem_singleton] at hx
      rw [hx, hus]
      exact hK
    · simp at hx
    · rw [Finset.mem_singleton] at hx
      subst hx
      exact (hrd u hu hum).1
  have hAs : (if s = (posVals σ).max' hS then 0 else 1) + 2 ≤ ∑ x ∈ A s, P.rootMultiplicity x := by
    simp only [A, ite_eq_left rfl, Finset.sum_singleton]
    split_ifs <;> omega
  have hAu : ∀ u ∈ posVals σ, u ≠ s →
      (if u = (posVals σ).max' hS then 0 else 1) ≤ ∑ x ∈ A u, P.rootMultiplicity x := by
    intro u hu h1
    simp only [A, ite_eq_right h1]
    by_cases h4 : u = (posVals σ).max' hS
    · simp [h4]
    · simpa [h4] using hrdμ u hu h4
  have htight : P.natDegree ≤ ∑ x ∈ (posVals σ).biUnion A, P.rootMultiplicity x := by
    have := str_count_lb N σ hS E A hA (fun u => if u = s then 2 else 0) (by
      intro u hu
      by_cases h1 : u = s
      · subst h1
        simpa using hAs
      · simpa [h1] using hAu u hu h1)
    rw [Finset.sum_ite_eq', ite_eq_left hs, ← hPdef] at this
    rw [← hPdef] at hdeg
    omega
  have hev := scPoly_eval_mExt N σ hσ hE
  rw [str_scPoly_eq_map] at hev
  obtain ⟨x, hxT, hxm⟩ := str_root_mem P (str_P_ne_zero N σ 1 E) _ htight hev
  obtain ⟨u, hu, hxu⟩ := Finset.mem_biUnion.1 hxT
  by_cases hus : u = s
  · simp only [A, ite_eq_left hus, Finset.mem_singleton] at hxu
    rw [hxm, hxu]
  exfalso
  have hmax : u ≠ (posVals σ).max' hS := by
    intro h
    have hAu0 : A u = ∅ := by
      simp only [A]
      rw [ite_eq_right hus, ite_eq_left h]
    rw [hAu0] at hxu
    simp at hxu
  have hAx : A u = {rd u} := by
    simp only [A]
    rw [ite_eq_right hus, ite_eq_right hmax]
  rw [hAx, Finset.mem_singleton] at hxu
  obtain ⟨hxK, hxE⟩ := hrd u hu hmax
  rw [← hxu] at hxK hxE
  have hxE' : fR N σ x = E := by rw [str_fR_eq N σ hσ]; exact hxE
  obtain ⟨hx0, hxp⟩ := str_K_good σ hS hu hxK
  rcases lt_trichotomy (fR1 N σ x) 0 with hneg | hzero | hpos
  · have := mExt_fR_ne_of_neg N σ hσ hN hx0 (str_nonpole_all σ hσ hxp) (by rw [hxE']; exact hE)
      hneg
    rw [hxE'] at this
    exact this hxm
  · have hm2 : 2 ≤ P.rootMultiplicity x := (str_mult_crit N σ hσ E hx0 hxp hxE' hzero).1
    have := str_count_lb N σ hS E A hA (fun v => (if v = s then 2 else 0) +
      (if v = u then 1 else 0)) (by
        intro v hv
        by_cases h1 : v = s
        · subst h1
          simpa [Ne.symm hus] using hAs
        · by_cases h3 : v = u
          · subst h3
            rw [hAx, Finset.sum_singleton, ← hxu, ite_eq_right hmax, ite_eq_right h1]
            simp only [ite_true]
            exact hm2
          · simpa [h1, h3] using hAu v hv h1)
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq', ite_eq_left hs,
      ite_eq_left hu, ← hPdef] at this
    have := str_budget P ((posVals σ).biUnion A)
    rw [← hPdef] at hdeg
    omega
  · obtain ⟨T2, hT2, hc2⟩ := str_special_K N σ hN hS one_pos (E := E) hu hxK hxE
      (by rw [← str_fR1_eq N σ hσ]; exact hpos)
    rw [ite_eq_right hmax] at hc2
    let A' : ℝ → Finset ℝ := fun v => if v = u then T2 else A v
    have hA' : ∀ v ∈ posVals σ, ∀ y ∈ A' v, strK σ v y := by
      intro v hv y hy
      simp only [A'] at hy
      split_ifs at hy with h
      · subst h
        exact (hT2 y hy).1
      · exact hA v hv y hy
    have hT2μ : T2.card ≤ ∑ y ∈ T2, P.rootMultiplicity y := by
      rw [Finset.card_eq_sum_ones]
      refine Finset.sum_le_sum fun y hy => ?_
      obtain ⟨h0, h1'⟩ := str_K_good σ hS hu (hT2 y hy).1
      exact str_mult_one N σ 1 E h0 h1' (hT2 y hy).2
    have := str_count_lb N σ hS E A' hA' (fun v => (if v = s then 2 else 0) +
      (if v = u then 2 else 0)) (by
        intro v hv
        by_cases h1 : v = s
        · subst h1
          simpa [A', Ne.symm hus] using hAs
        · by_cases h3 : v = u
          · subst h3
            simp only [A', ite_true, ite_eq_right h1, ite_eq_right hmax, zero_add]
            rw [← hPdef]
            omega
          · simpa [A', h1, h3] using hAu v hv h1)
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq', ite_eq_left hs,
      ite_eq_left hu, ← hPdef] at this
    have := str_budget P ((posVals σ).biUnion A')
    rw [← hPdef] at hdeg
    omega

/-! ## The convention `m(0) = ∞` (Lemma 2.5) -/

/-! ## The structure of `ϱ` (Lemma 2.6) -/

private lemma str_continuousAt_rhoDens (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {E : ℝ}
    (hE : E ≠ 0) : ContinuousAt (rhoDens N σ) E := by
  have hmem : ((E : ℂ)) ∈ upperHalf ∪ {z : ℂ | z.im = 0 ∧ z ≠ 0} :=
    Or.inr ⟨Complex.ofReal_im E, Complex.ofReal_ne_zero.mpr hE⟩
  have hc := (continuousOn_mExt N σ hσ _ hmem).tendsto
  have h1 : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝 E)
      (𝓝[upperHalf ∪ {z : ℂ | z.im = 0 ∧ z ≠ 0}] (E : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨Complex.continuous_ofReal.tendsto E, ?_⟩
    filter_upwards [eventually_ne_nhds hE] with x hx
    exact Or.inr ⟨Complex.ofReal_im x, Complex.ofReal_ne_zero.mpr hx⟩
  exact ((Complex.continuous_im.tendsto _).comp (hc.comp h1)).div_const Real.pi

/-- `ϱ(U) = 0` for `U` avoiding `0` with density `0` on `U ∩ (0, ∞)`. -/
private lemma str_varrho_eq_zero (N : ℕ) (σ : Fin M → ℝ) {U : Set ℝ} (hU : MeasurableSet U)
    (h0 : (0 : ℝ) ∉ U) (h : ∀ x ∈ U, 0 < x → rhoDens N σ x = 0) : varrho N σ U = 0 := by
  rw [varrho, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hU,
    Set.indicator_of_notMem h0, smul_zero, zero_add, withDensity_apply _ hU,
    Measure.restrict_restrict hU]
  refine setLIntegral_eq_zero (hU.inter measurableSet_Ioi) fun x ⟨hx1, hx2⟩ => ?_
  simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero]
  exact (h x hx1 hx2).le

/-- Every neighbourhood of a point `E > 0` with `ρ(E) > 0` has positive `ϱ`-measure. -/
private lemma str_varrho_pos (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {E : ℝ} (hE : 0 < E)
    (hρ : 0 < rhoDens N σ E) {U : Set ℝ} (hU : U ∈ 𝓝 E) : 0 < varrho N σ U := by
  have hc := str_continuousAt_rhoDens N σ hσ hE.ne'
  have hev : ∀ᶠ x in 𝓝 E, rhoDens N σ E / 2 < rhoDens N σ x ∧ 0 < x ∧ x ∈ U :=
    (hc.eventually (lt_mem_nhds (half_lt_self hρ))).and ((lt_mem_nhds hE).and hU)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hev
  rw [Real.ball_eq_Ioo] at hball
  have hIU : Set.Ioo (E - δ) (E + δ) ⊆ U := fun x hx => (hball hx).2.2
  have hI0 : Set.Ioo (E - δ) (E + δ) ⊆ Set.Ioi 0 := fun x hx => (hball hx).2.1
  calc 0 < ENNReal.ofReal (rhoDens N σ E / 2) * volume (Set.Ioo (E - δ) (E + δ)) := by
        rw [Real.volume_Ioo]
        exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 (half_pos hρ)).ne'
          (ENNReal.ofReal_pos.2 (by linarith)).ne'
    _ = ∫⁻ _ in Set.Ioo (E - δ) (E + δ), ENNReal.ofReal (rhoDens N σ E / 2) :=
        (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ x in Set.Ioo (E - δ) (E + δ), ENNReal.ofReal (rhoDens N σ x) := by
        refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioo).2
          (ae_of_all _ fun x hx => ?_))
        exact ENNReal.ofReal_le_ofReal (hball hx).1.le
    _ = ((volume.restrict (Set.Ioi 0)).withDensity
          (fun x => ENNReal.ofReal (rhoDens N σ x))) (Set.Ioo (E - δ) (E + δ)) := by
        rw [withDensity_apply _ measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
          Set.inter_eq_left.2 hI0]
    _ ≤ varrho N σ (Set.Ioo (E - δ) (E + δ)) := by
        rw [varrho]
        exact Measure.le_iff'.1 (Measure.le_add_left le_rfl) _
    _ ≤ varrho N σ U := measure_mono hIU

/-- `ρ(f(y)) = 0` when `f'(y) > 0`. -/
private lemma str_rhoDens_zero (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    {y x : ℝ} (hy0 : y ≠ 0) (hyp : ∀ i, 1 + σ i * y ≠ 0) (hyE : fR N σ y = x)
    (hd : 0 < fR1 N σ y) (hx : x ≠ 0) : rhoDens N σ x = 0 := by
  subst hyE
  unfold rhoDens
  rw [mExt_fR_of_pos N σ hσ hN hy0 hyp hx hd, Complex.ofReal_im, zero_div]

/-- A point `E` outside all bands lies in a gap `(a_1, ∞)`, `(a_{2j+1}, a_{2j})` or
`(-∞, a_{2p})`. -/
private lemma str_gap_cases (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {E : ℝ} (hE : ¬ ∃ k, 1 ≤ k ∧ k ≤ numBands N σ ∧
      E ∈ Set.Icc (edgeVal N σ (2 * k)) (edgeVal N σ (2 * k - 1))) :
    edgeVal N σ 1 < E ∨ (∃ j, 1 ≤ j ∧ 2 * j + 1 < 2 * numBands N σ ∧
      edgeVal N σ (2 * j + 1) < E ∧ E < edgeVal N σ (2 * j)) ∨
      E < edgeVal N σ (2 * numBands N σ) := by
  have hp := card_innerCrit N σ hσ hN hS
  by_cases h1 : edgeVal N σ 1 < E
  · exact Or.inl h1
  by_cases h2 : E < edgeVal N σ (2 * numBands N σ)
  · exact Or.inr (Or.inr h2)
  right
  left
  rw [not_lt] at h1 h2
  have hband : ∀ k, 1 ≤ k → k ≤ numBands N σ → edgeVal N σ (2 * k) ≤ E →
      E ≤ edgeVal N σ (2 * k - 1) → False :=
    fun k hk1 hk h3 h4 => hE ⟨k, hk1, hk, h3, h4⟩
  have hlast : edgeVal N σ (2 * numBands N σ) < E := by
    refine lt_of_le_of_ne h2 fun h => hband (numBands N σ) hp.2 le_rfl h2 ?_
    rw [← h]
    exact str_chain N σ hσ hN hS (by omega) (by omega) le_rfl
  have hex : ∃ i, 1 ≤ i ∧ edgeVal N σ i < E := ⟨2 * numBands N σ, by omega, hlast⟩
  have hspec := Nat.find_spec hex
  have hmin := fun m (hm : m < Nat.find hex) => Nat.find_min hex hm
  have hle : Nat.find hex ≤ 2 * numBands N σ := Nat.find_min' hex ⟨by omega, hlast⟩
  have hne1 : Nat.find hex ≠ 1 := fun h => by
    have := hspec.2
    rw [h] at this
    linarith
  have hprev : E ≤ edgeVal N σ (Nat.find hex - 1) := by
    have := hmin (Nat.find hex - 1) (by omega)
    rw [not_and, not_lt] at this
    exact this (by omega)
  rcases Nat.even_or_odd (Nat.find hex) with ⟨k, hk⟩ | ⟨j, hj⟩
  · exfalso
    refine hband k (by omega) (by omega) ?_ ?_
    · have := hspec.2
      rw [hk, ← two_mul] at this
      exact this.le
    · rw [show 2 * k - 1 = Nat.find hex - 1 by omega]
      exact hprev
  · have hj1 : 1 ≤ j := by omega
    have hj' : 2 * j + 1 < 2 * numBands N σ := by omega
    refine ⟨j, hj1, hj', by rw [← hj]; exact hspec.2, ?_⟩
    rw [show Nat.find hex - 1 = 2 * j by omega] at hprev
    refine lt_of_le_of_ne hprev fun h => hband j hj1 (by omega) h.ge ?_
    rw [h]
    exact str_chain N σ hσ hN hS (by omega) (by omega) (by omega)

/-- The density is positive on the open bands (Lemma 2.6). -/
private lemma str_rhoDens_pos (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {k : ℕ} (hk₁ : 1 ≤ k) (hk : k ≤ numBands N σ) {E : ℝ}
    (hE : 0 < E) (hEk : E ∈ Set.Ioo (edgeVal N σ (2 * k)) (edgeVal N σ (2 * k - 1))) :
    0 < rhoDens N σ E := by
  have hp := card_innerCrit N σ hσ hN hS
  unfold rhoDens
  refine div_pos ?_ Real.pi_pos
  rcases (im_mExt_nonneg N σ hσ hE.ne').lt_or_eq with h | h
  · exact h
  exfalso
  have hw : mExt N σ E = (((mExt N σ E).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [← h])
  have hev := scPoly_eval_mExt N σ hσ hE.ne'
  rw [hw] at hev
  obtain ⟨hx0, hxp, hfx⟩ := str_real_root N σ hσ hN hev
  set x := (mExt N σ E).re with hxdef
  have hc1 : ∀ i, 1 ≤ i → i ≤ 2 * k - 1 → edgeVal N σ (2 * k - 1) ≤ edgeVal N σ i :=
    fun i h1 h2 => str_chain N σ hσ hN hS h1 h2 (by omega)
  have hc2 : ∀ i, 2 * k ≤ i → i ≤ 2 * numBands N σ → edgeVal N σ i ≤ edgeVal N σ (2 * k) :=
    fun i h1 h2 => str_chain N σ hσ hN hS (by omega) h1 h2
  rcases lt_trichotomy (fR1 N σ x) 0 with hneg | hzero | hpos
  · have := mExt_fR_ne_of_neg N σ hσ hN hx0 (str_nonpole_all σ hσ hxp)
      (by rw [hfx]; exact hE.ne') hneg
    rw [hfx] at this
    exact this hw
  · obtain ⟨i, hi1, hi2, hfi⟩ := str_crit_value N σ hσ hN hS hx0 hxp hzero
    rw [hfx] at hfi
    by_cases hik : i ≤ 2 * k - 1
    · have := hc1 i hi1 hik
      linarith [hEk.2]
    · have := hc2 i (by omega) hi2
      linarith [hEk.1]
  · rcases str_gap N σ hσ hN hS hx0 hxp hpos with h1 | ⟨j, hj, hj', h1, h2⟩ | h1
    · rw [hfx] at h1
      have := hc1 1 le_rfl (by omega)
      linarith [hEk.2]
    · rw [hfx] at h1 h2
      by_cases hjk : j < k
      · have := hc1 (2 * j + 1) (by omega) (by omega)
        linarith [hEk.2]
      · have := hc2 (2 * j) (by omega) (by omega)
        linarith [hEk.1]
    · rw [hfx] at h1
      have := hc2 (2 * numBands N σ) (by omega) le_rfl
      linarith [hEk.1]

/-! ## Lemma 2.5 -/

/-- Lemma 2.5, `x_k = m(a_k)` when `x_k` is finite. -/
theorem mExt_edgeVal (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {k : ℕ} (hk₁ : 1 ≤ k) (hk : k ≤ 2 * numBands N σ)
    (hfin : ¬ (k = 2 * numBands N σ ∧ yEdge N σ = 0)) :
    mExt N σ (edgeVal N σ k) = xCrit N σ k := by
  have hE := str_edgeVal_pos N σ hσ hN hS hk₁ hk hfin
  by_cases hlast : k = 2 * numBands N σ
  · have hy0 : yEdge N σ ≠ 0 := fun h0 => hfin ⟨hlast, h0⟩
    have hx : xCrit N σ k = (yEdge N σ)⁻¹ := by
      unfold xCrit
      rw [ite_eq_left hlast]
    rw [hx, hlast, str_edgeVal_last]
    exact str_mExt_last N σ hσ hN hS hy0
  · obtain ⟨hmem, -⟩ := str_xCrit_spec N σ hσ hN hS hk₁ (lt_of_le_of_ne hk hlast)
    rw [str_edgeVal_ne N σ hlast] at hE ⊢
    obtain ⟨hin, hnp, h1⟩ := str_mem_innerCrit N σ hσ hN hmem
    by_cases h2 : fR2 N σ (xCrit N σ k) = 0
    · exact str_mExt_degen N σ hσ hN hS hmem h2 hE.ne'
    · exact str_mExt_crit N σ hσ hN hin.1.ne (str_nonpole_all σ hσ hnp) h1 h2 hE.ne'


/-! ## Lemma 2.6 and Lemma A.1 -/

/-- Lemma 2.6, (rho_supp). -/
theorem mem_support_varrho_iff (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {E : ℝ} (hE : 0 < E) :
    E ∈ (varrho N σ).support ↔ ∃ k, 1 ≤ k ∧ k ≤ numBands N σ ∧
      E ∈ Set.Icc (edgeVal N σ (2 * k)) (edgeVal N σ (2 * k - 1)) := by
  have hp := card_innerCrit N σ hσ hN hS
  have hlast := str_edgeVal_last_nonneg N σ hσ hN hS
  constructor
  · intro hmem
    by_contra hno
    rcases str_gap_cases N σ hσ hN hS hno with h | ⟨j, hj, hj', h1, h2⟩ | h
    · refine (Measure.notMem_support_iff_exists.2 ⟨Set.Ioi (edgeVal N σ 1), Ioi_mem_nhds h,
        str_varrho_eq_zero N σ measurableSet_Ioi (fun h0 => ?_) fun x hx hx0 => ?_⟩) hmem
      · have := str_chain N σ hσ hN hS le_rfl (show 1 ≤ 2 * numBands N σ by omega) le_rfl
        simp only [Set.mem_Ioi] at h0
        linarith
      · obtain ⟨y, hyK, hyE, hyd⟩ := str_first_preimage N σ hσ hN hS hx
        obtain ⟨h0, hp'⟩ := str_K_good σ hS ((posVals σ).max'_mem hS) hyK
        exact str_rhoDens_zero N σ hσ hN h0 (str_nonpole_all σ hσ hp') hyE hyd hx0.ne'
    · refine (Measure.notMem_support_iff_exists.2 ⟨Set.Ioo (edgeVal N σ (2 * j + 1))
        (edgeVal N σ (2 * j)), Ioo_mem_nhds h1 h2,
        str_varrho_eq_zero N σ measurableSet_Ioo (fun h0 => ?_) fun x hx hx0 => ?_⟩) hmem
      · have := str_chain N σ hσ hN hS (show 1 ≤ 2 * j + 1 by omega) hj'.le le_rfl
        linarith [h0.1]
      · obtain ⟨y, h0, hp', hyE, hyd⟩ := str_pair_preimage N σ hσ hN hS hj hj' hx.1 hx.2
        exact str_rhoDens_zero N σ hσ hN h0 (str_nonpole_all σ hσ hp') hyE hyd hx0.ne'
    · refine (Measure.notMem_support_iff_exists.2 ⟨Set.Ioo 0 (edgeVal N σ (2 * numBands N σ)),
        Ioo_mem_nhds hE h, str_varrho_eq_zero N σ measurableSet_Ioo (fun h0 => ?_)
        fun x hx hx0 => ?_⟩) hmem
      · exact lt_irrefl _ h0.1
      · obtain ⟨y, h0, hp', hyE, hyd⟩ := str_I0_preimage N σ hσ hN hS hx0 hx.2
        exact str_rhoDens_zero N σ hσ hN h0 (str_nonpole_all σ hσ hp') hyE hyd hx0.ne'
  · rintro ⟨k, hk1, hk, hEk⟩
    rw [Measure.mem_support_iff_forall]
    intro U hU
    obtain ⟨V, hVU, hVo, hEV⟩ := mem_nhds_iff.1 hU
    have hlt := edgeVal_band_lt N σ hσ hN hS hk1 hk
    have hcl : E ∈ closure (Set.Ioo (edgeVal N σ (2 * k)) (edgeVal N σ (2 * k - 1))) := by
      rw [closure_Ioo hlt.ne]
      exact hEk
    obtain ⟨E', hE'V, hE'I⟩ := mem_closure_iff.1 hcl V hVo hEV
    have h0 : 0 ≤ edgeVal N σ (2 * k) :=
      hlast.trans (str_chain N σ hσ hN hS (by omega) (by omega) le_rfl)
    have hE'0 : 0 < E' := lt_of_le_of_lt h0 hE'I.1
    exact str_varrho_pos N σ hσ hE'0 (str_rhoDens_pos N σ hσ hN hS hk1 hk hE'0 hE'I)
      (Filter.mem_of_superset (hVo.mem_nhds hE'V) hVU)

theorem rhoDens_pos (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {k : ℕ} (hk₁ : 1 ≤ k) (hk : k ≤ numBands N σ) {E : ℝ}
    (hE : 0 < E) (hEk : E ∈ Set.Ioo (edgeVal N σ (2 * k)) (edgeVal N σ (2 * k - 1))) :
    0 < rhoDens N σ E :=
  str_rhoDens_pos N σ hσ hN hS hk₁ hk hE hEk

theorem varrho_compl_Icc_edgeVal (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) : varrho N σ (Set.Icc 0 (edgeVal N σ 1))ᶜ = 0 := by
  have hp := card_innerCrit N σ hσ hN hS
  have ha1 : 0 ≤ edgeVal N σ 1 := (str_edgeVal_last_nonneg N σ hσ hN hS).trans
    (str_chain N σ hσ hN hS le_rfl (by omega) le_rfl)
  refine str_varrho_eq_zero N σ measurableSet_Icc.compl (fun h => h ⟨le_rfl, ha1⟩)
    fun x hx hx0 => ?_
  have hx1 : edgeVal N σ 1 < x := by
    by_contra h
    exact hx ⟨hx0.le, not_lt.1 h⟩
  obtain ⟨y, hyK, hyE, hyd⟩ := str_first_preimage N σ hσ hN hS hx1
  obtain ⟨h0, hp'⟩ := str_K_good σ hS ((posVals σ).max'_mem hS) hyK
  exact str_rhoDens_zero N σ hσ hN h0 (str_nonpole_all σ hσ hp') hyE hyd hx0.ne'

/-! ## Concrete instances (Marchenko–Pastur: `M = 1`, `σ = 1`) -/

end Anisotropic
