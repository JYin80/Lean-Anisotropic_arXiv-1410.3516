module

public import Anisotropic.Density.Critical

@[expose] public section

/-!
# Ordering of the critical values

The critical values `a_1 ≥ a_2 ≥ ⋯ ≥ a_{2p}` of Lemma 2.5, the nondegeneracy `a_{2k} < a_{2k-1}`
of the bands, the identity `a_k = f(x_k)` for finite `x_k`, and the bound `a_k ∈ [0, C]` under
(phi_bounded) and (bound_Sigma).

The proof counts real roots of the polynomial `P_E(w) = w Π_s (1 + s w) (f(w) - E)` of
Appendix A.1, which has degree at most `n + 1` (at most `n` for `E = 0`), for the functions
`f^t(x) = -1/x + t Σ_s r_s s / (1 + s x)`, `t ∈ (0, 1]`, of the proof of Lemma 2.5
(`f^1 = f`, (def_fx)).
-/

open MeasureTheory Polynomial Filter Topology
open scoped ENNReal

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! ## The functions `f^t` -/

/-- `g(x) = Σ_s r_s s / (1 + s x)`, so that `f(x) = -1/x + g(x)`. -/
private def ordG (N : ℕ) (σ : Fin M → ℝ) (x : ℝ) : ℝ :=
  ∑ s ∈ posVals σ, weight N σ s * s / (1 + s * x)

/-- `f^t(x) = -1/x + t g(x)`; `f^1 = f`. -/
private def ordF (N : ℕ) (σ : Fin M → ℝ) (t x : ℝ) : ℝ := -x⁻¹ + t * ordG N σ x

/-- `G(x) = Σ_s r_s s² / (1 + s x)²`. -/
private def ordH (N : ℕ) (σ : Fin M → ℝ) (x : ℝ) : ℝ :=
  ∑ s ∈ posVals σ, weight N σ s * s ^ 2 / (1 + s * x) ^ 2

/-- `(f^t)'(x) = 1/x² - t G(x)`. -/
private def ordF1 (N : ℕ) (σ : Fin M → ℝ) (t x : ℝ) : ℝ := (x ^ 2)⁻¹ - t * ordH N σ x

private lemma ord_sum_group (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (g : ℝ → ℝ) (hg : g 0 = 0) :
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

private lemma ord_sum_pow (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {k : ℕ} (hk : 0 < k)
    (x : ℝ) :
    ∑ i, σ i ^ k / ((N : ℝ) * (1 + σ i * x) ^ k) =
      ∑ s ∈ posVals σ, weight N σ s * s ^ k / (1 + s * x) ^ k := by
  rw [ord_sum_group σ hσ (fun a => a ^ k / ((N : ℝ) * (1 + a * x) ^ k))
    (by simp [zero_pow hk.ne'])]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [weight, div_eq_mul_inv, mul_inv]
  ring

private lemma ord_fR_eq (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) :
    fR N σ = ordF N σ 1 := by
  funext x
  have h := ord_sum_pow N σ hσ (k := 1) one_pos x
  simp only [pow_one] at h
  rw [fR, h, ordF, ordG, one_mul]

private lemma ord_fR1_eq (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) :
    fR1 N σ = ordF1 N σ 1 := by
  funext x
  rw [fR1, ord_sum_pow N σ hσ (k := 2) two_pos x, ordF1, ordH, one_mul]

private lemma ord_pos_of_mem (σ : Fin M → ℝ) {s : ℝ} (hs : s ∈ posVals σ) : 0 < s :=
  (Finset.mem_filter.mp hs).2

private lemma ord_weight_pos (N : ℕ) (σ : Fin M → ℝ) (hN : 0 < N) {s : ℝ}
    (hs : s ∈ posVals σ) : 0 < weight N σ s := by
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hs).1
  unfold weight
  have hc : 0 < (Finset.univ.filter fun j => σ j = s).card :=
    Finset.card_pos.mpr ⟨i, by simp [hi]⟩
  positivity

private lemma ord_nonpole_all (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {x : ℝ}
    (hx : ∀ s ∈ posVals σ, 1 + s * x ≠ 0) : ∀ i, 1 + σ i * x ≠ 0 := by
  intro i
  rcases (hσ i).eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · exact hx (σ i) (by simp [posVals, hpos])

private lemma ord_H_pos (N : ℕ) (σ : Fin M → ℝ) (hN : 0 < N) (hS : (posVals σ).Nonempty)
    {x : ℝ} (hx : ∀ s ∈ posVals σ, 1 + s * x ≠ 0) : 0 < ordH N σ x := by
  refine Finset.sum_pos (fun s hs => ?_) hS
  have hw := ord_weight_pos N σ hN hs
  have hs0 := ord_pos_of_mem σ hs
  exact div_pos (mul_pos hw (pow_pos hs0 2)) (pow_two_pos_of_ne_zero (hx s hs))

/-- For `s > 0`: `-1/s < x ↔ 0 < 1 + s x`. -/
private lemma ord_lt_iff {s x : ℝ} (hs : 0 < s) : -s⁻¹ < x ↔ 0 < 1 + s * x := by
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
private lemma ord_gt_iff {s x : ℝ} (hs : 0 < s) : x < -s⁻¹ ↔ 1 + s * x < 0 := by
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

private lemma ord_hasDerivAt_term (c s : ℝ) {x : ℝ} (h : 1 + s * x ≠ 0) :
    HasDerivAt (fun y : ℝ => c * s / (1 + s * y)) (-(c * s ^ 2 / (1 + s * x) ^ 2)) x := by
  have h1 : HasDerivAt (fun y : ℝ => 1 + s * y) s x := by
    simpa using ((hasDerivAt_id x).const_mul s).const_add 1
  have h2 := (hasDerivAt_const x (c * s)).fun_div h1 h
  convert h2 using 1
  field_simp
  ring

private lemma ord_hasDerivAt_F (N : ℕ) (σ : Fin M → ℝ) (t : ℝ) {x : ℝ} (hx : x ≠ 0)
    (hx' : ∀ s ∈ posVals σ, 1 + s * x ≠ 0) : HasDerivAt (ordF N σ t) (ordF1 N σ t x) x := by
  have h0 : HasDerivAt (fun y : ℝ => -y⁻¹) ((x ^ 2)⁻¹) x := by
    have := (hasDerivAt_inv hx).neg
    convert this using 1
    ring
  have hs : HasDerivAt (fun y => ∑ s ∈ posVals σ, weight N σ s * s / (1 + s * y))
      (∑ s ∈ posVals σ, -(weight N σ s * s ^ 2 / (1 + s * x) ^ 2)) x :=
    HasDerivAt.fun_sum fun s hs => ord_hasDerivAt_term _ _ (hx' s hs)
  have h := h0.add (hs.const_mul t)
  unfold ordF ordF1 ordH ordG
  convert h using 1
  rw [Finset.sum_neg_distrib]
  ring

/-! ## The polynomial `P_E` for `f^t` -/

/-- `P^t_E(w) = w Π_s (1 + s w) (f^t(w) - E)` (Appendix A.1, weights `t r_s`). -/
private def ordP (N : ℕ) (σ : Fin M → ℝ) (t E : ℝ) : ℝ[X] :=
  -(∏ s ∈ posVals σ, (1 + C s * X)) +
    C t * X * ∑ s ∈ posVals σ, C (weight N σ s * s) *
      ∏ s' ∈ (posVals σ).erase s, (1 + C s' * X) -
    C E * X * ∏ s ∈ posVals σ, (1 + C s * X)

private lemma ord_eval_P (N : ℕ) (σ : Fin M → ℝ) (t E : ℝ) {x : ℝ} (hx : x ≠ 0)
    (hx' : ∀ s ∈ posVals σ, 1 + s * x ≠ 0) :
    (ordP N σ t E).eval x = x * (∏ s ∈ posVals σ, (1 + s * x)) * (ordF N σ t x - E) := by
  have hev : (ordP N σ t E).eval x = -(∏ s ∈ posVals σ, (1 + s * x)) +
      t * x * ∑ s ∈ posVals σ, weight N σ s * s * ∏ s' ∈ (posVals σ).erase s, (1 + s' * x) -
      E * x * ∏ s ∈ posVals σ, (1 + s * x) := by
    simp only [ordP, eval_sub, eval_add, eval_neg, eval_mul, eval_X, eval_C, eval_prod,
      eval_one, eval_finsetSum]
  have hterm : ∀ s ∈ posVals σ, (∏ u ∈ posVals σ, (1 + u * x)) *
      (weight N σ s * s / (1 + s * x)) =
      weight N σ s * s * ∏ s' ∈ (posVals σ).erase s, (1 + s' * x) := by
    intro s hs
    rw [← Finset.mul_prod_erase _ _ hs]
    have := hx' s hs
    field_simp
  have hsum : (∏ u ∈ posVals σ, (1 + u * x)) * ordG N σ x =
      ∑ s ∈ posVals σ, weight N σ s * s * ∏ s' ∈ (posVals σ).erase s, (1 + s' * x) := by
    unfold ordG
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hterm
  rw [hev, ← hsum]
  unfold ordF
  have hinv : x * x⁻¹ = 1 := mul_inv_cancel₀ hx
  linear_combination (∏ u ∈ posVals σ, (1 + u * x)) * hinv

private lemma ord_P_ne_zero (N : ℕ) (σ : Fin M → ℝ) (t E : ℝ) : ordP N σ t E ≠ 0 := by
  intro h
  have : (ordP N σ t E).eval 0 = -1 := by simp [ordP, eval_prod]
  rw [h] at this
  simp at this

private lemma ord_natDegree_prod_le (S : Finset ℝ) :
    natDegree (∏ s ∈ S, (1 + C s * X : ℝ[X])) ≤ S.card := by
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ s ∈ S, natDegree (1 + C s * X : ℝ[X]) ≤ ∑ _s ∈ S, 1 :=
        Finset.sum_le_sum fun s _ => by compute_degree
    _ = S.card := by simp

/-- `deg P^t_E ≤ n + 1`, and `deg P^t_0 ≤ n`. -/
private lemma ord_natDegree_P (N : ℕ) (σ : Fin M → ℝ) (t E : ℝ) :
    (ordP N σ t E).natDegree ≤ (posVals σ).card + 1 ∧
      (E = 0 → (ordP N σ t E).natDegree ≤ (posVals σ).card) := by
  have h1 := ord_natDegree_prod_le (posVals σ)
  have hsum : natDegree (∑ s ∈ posVals σ, C (weight N σ s * s) *
      ∏ s' ∈ (posVals σ).erase s, (1 + C s' * X)) ≤ (posVals σ).card - 1 := by
    refine natDegree_sum_le_of_forall_le _ _ fun s hs => ?_
    refine (natDegree_C_mul_le _ _).trans ?_
    refine (ord_natDegree_prod_le _).trans ?_
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
  · unfold ordP
    exact (natDegree_sub_le_of_le h12 h3).trans (max_le (by omega) le_rfl)
  · subst hE
    unfold ordP
    rw [C_0, zero_mul, zero_mul, sub_zero]
    exact h12

/-! ## Root budget -/

private lemma ord_sum_count_le (m : Multiset ℝ) (T : Finset ℝ) :
    ∑ x ∈ T, m.count x ≤ Multiset.card m := by
  calc ∑ x ∈ T, m.count x = ∑ x ∈ T, (m.filter (· ∈ T)).count x :=
        Finset.sum_congr rfl fun x hx => by rw [Multiset.count_filter_of_pos hx]
    _ = Multiset.card (m.filter (· ∈ T)) :=
        Multiset.sum_count_eq_card fun x hx => (Multiset.mem_filter.1 hx).2
    _ ≤ Multiset.card m := Multiset.card_le_card (Multiset.filter_le _ _)

/-- The root budget: the root multiplicities of a polynomial over any finite set of points sum
to at most its degree. -/
private lemma ord_budget (P : ℝ[X]) (T : Finset ℝ) :
    ∑ x ∈ T, P.rootMultiplicity x ≤ P.natDegree := by
  calc ∑ x ∈ T, P.rootMultiplicity x = ∑ x ∈ T, P.roots.count x :=
        Finset.sum_congr rfl fun x _ => by rw [count_roots]
    _ ≤ Multiset.card P.roots := ord_sum_count_le _ _
    _ ≤ P.natDegree := card_roots' P

private lemma ord_mult_one (N : ℕ) (σ : Fin M → ℝ) (t E : ℝ) {x : ℝ} (hx : x ≠ 0)
    (hx' : ∀ s ∈ posVals σ, 1 + s * x ≠ 0) (hr : ordF N σ t x = E) :
    1 ≤ (ordP N σ t E).rootMultiplicity x := by
  have := (rootMultiplicity_pos (ord_P_ne_zero N σ t E) (x := x)).2
    (by simp [IsRoot, ord_eval_P N σ t E hx hx', hr])
  omega

/-- The first and second derivatives of a polynomial that agrees with `G f₁` near `x`. -/
private lemma ord_local_derivs (Q G : ℝ[X]) (f1 f2 : ℝ → ℝ) (f3 : ℝ) {x : ℝ}
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
private lemma ord_eventually_good (σ : Fin M → ℝ) {x : ℝ} (hx : x ≠ 0)
    (hx' : ∀ s ∈ posVals σ, 1 + s * x ≠ 0) :
    ∀ᶠ y in 𝓝 x, y ≠ 0 ∧ ∀ s ∈ posVals σ, 1 + s * y ≠ 0 := by
  refine (eventually_ne_nhds hx).and ?_
  rw [Filter.eventually_all_finset]
  intro s hs
  have hc : Continuous fun y : ℝ => 1 + s * y := by fun_prop
  exact hc.continuousAt.eventually_ne (hx' s hs)

/-- At a critical point `x` of `f` with `f(x) = E`, `f - E` has a root of order `≥ 2`, and of
order `≥ 3` if also `f''(x) = 0`. -/
private lemma ord_mult_crit (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (E : ℝ) {x : ℝ}
    (hx : x ≠ 0) (hx' : ∀ s ∈ posVals σ, 1 + s * x ≠ 0) (hr : fR N σ x = E)
    (h1 : fR1 N σ x = 0) :
    2 ≤ (ordP N σ 1 E).rootMultiplicity x ∧
      (fR2 N σ x = 0 → 3 ≤ (ordP N σ 1 E).rootMultiplicity x) := by
  set P := ordP N σ 1 E with hPdef
  have hP0 : P ≠ 0 := ord_P_ne_zero N σ 1 E
  set G : ℝ[X] := X * ∏ s ∈ posVals σ, (1 + C s * X) with hG
  have hGeval : ∀ y : ℝ, G.eval y = y * ∏ s ∈ posVals σ, (1 + s * y) := by
    intro y
    simp [hG, eval_prod]
  have hgood := ord_eventually_good σ hx hx'
  have hQloc : ∀ᶠ y in 𝓝 x, P.eval y = G.eval y * (fR N σ y - E) := by
    filter_upwards [hgood] with y hy
    rw [hPdef, ord_eval_P N σ 1 E hy.1 hy.2, hGeval, ord_fR_eq N σ hσ]
  have h1loc : ∀ᶠ y in 𝓝 x, HasDerivAt (fun z => fR N σ z - E) (fR1 N σ y) y := by
    filter_upwards [hgood] with y hy
    exact (hasDerivAt_fR N σ hy.1 (ord_nonpole_all σ hσ hy.2)).sub_const E
  have h2 := hasDerivAt_fR1 N σ hx (ord_nonpole_all σ hσ hx')
  obtain ⟨hD1, hD2⟩ := ord_local_derivs P G (fun z => fR N σ z - E) (fR1 N σ) (fR2 N σ x)
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
private def ordR (σ : Fin M → ℝ) (s : ℝ) : ℝ :=
  if h : ((posVals σ).filter (fun u => s < u)).Nonempty then
    -(((posVals σ).filter (fun u => s < u)).min' h)⁻¹ else 0

/-- `x ∈ (-1/s, ordR s)`, the interval `I_l` with left end `-1/s`. -/
private def ordK (σ : Fin M → ℝ) (s x : ℝ) : Prop := -s⁻¹ < x ∧ x < ordR σ s

/-- `x ∈ (-∞, -1/s_n) ∪ (0, ∞)`, the finite points of `I_0`. -/
private def ordI0 (σ : Fin M → ℝ) (x : ℝ) : Prop := 0 < x ∨ ∀ s ∈ posVals σ, 1 + s * x < 0

private lemma ord_ne_max_iff (σ : Fin M → ℝ) (hS : (posVals σ).Nonempty) {s : ℝ}
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

private lemma ord_R_max (σ : Fin M → ℝ) (hS : (posVals σ).Nonempty) :
    ordR σ ((posVals σ).max' hS) = 0 := by
  unfold ordR
  rw [dite_eq_right]
  rw [ord_ne_max_iff σ hS ((posVals σ).max'_mem hS)]
  simp

private lemma ord_R_next (σ : Fin M → ℝ) (hS : (posVals σ).Nonempty) {s : ℝ}
    (hs : s ∈ posVals σ) (hne : s ≠ (posVals σ).max' hS) :
    ∃ s' ∈ posVals σ, s < s' ∧ (∀ u ∈ posVals σ, ¬ (s < u ∧ u < s')) ∧ ordR σ s = -s'⁻¹ := by
  have hA := (ord_ne_max_iff σ hS hs).2 hne
  have hm := Finset.min'_mem _ hA
  refine ⟨_, (Finset.mem_filter.mp hm).1, (Finset.mem_filter.mp hm).2, ?_, ?_⟩
  · rintro u hu ⟨h1, h2⟩
    have := Finset.min'_le _ u (Finset.mem_filter.mpr ⟨hu, h1⟩)
    linarith
  · unfold ordR
    rw [dite_eq_left hA]

private lemma ord_left_lt_R (σ : Fin M → ℝ) (hS : (posVals σ).Nonempty) {s : ℝ}
    (hs : s ∈ posVals σ) : -s⁻¹ < ordR σ s := by
  have hs0 := ord_pos_of_mem σ hs
  by_cases hmax : s = (posVals σ).max' hS
  · rw [hmax, ord_R_max]
    rw [← hmax]
    simpa using hs0
  · obtain ⟨s', hs', hss', -, hR⟩ := ord_R_next σ hS hs hmax
    rw [hR]
    have : s'⁻¹ < s⁻¹ := inv_strictAnti₀ hs0 hss'
    linarith

/-- On `I_l = (-1/s, ordR s)`: `x < 0`, `1 + u x > 0` for `u ≤ s` and `1 + u x < 0` for `u > s`. -/
private lemma ord_K_sign (σ : Fin M → ℝ) (hS : (posVals σ).Nonempty) {s : ℝ}
    (hs : s ∈ posVals σ) {x : ℝ} (hx : ordK σ s x) :
    x < 0 ∧ ∀ u ∈ posVals σ, (u ≤ s → 0 < 1 + u * x) ∧ (s < u → 1 + u * x < 0) := by
  have hs0 := ord_pos_of_mem σ hs
  have h1 : 0 < 1 + s * x := (ord_lt_iff hs0).1 hx.1
  by_cases hmax : s = (posVals σ).max' hS
  · have hR : ordR σ s = 0 := by rw [hmax]; exact ord_R_max σ hS
    have hx0 : x < 0 := hR ▸ hx.2
    refine ⟨hx0, fun u hu => ⟨fun hus => ?_, fun hsu => ?_⟩⟩
    · have := mul_le_mul_of_nonpos_right hus hx0.le
      linarith
    · have := (posVals σ).le_max' u hu
      rw [← hmax] at this
      linarith
  · obtain ⟨s', hs', hss', hcons, hR⟩ := ord_R_next σ hS hs hmax
    have hs'0 := ord_pos_of_mem σ hs'
    have h2 : 1 + s' * x < 0 := (ord_gt_iff hs'0).1 (hR ▸ hx.2)
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

private lemma ord_K_good (σ : Fin M → ℝ) (hS : (posVals σ).Nonempty) {s : ℝ}
    (hs : s ∈ posVals σ) {x : ℝ} (hx : ordK σ s x) :
    x ≠ 0 ∧ ∀ u ∈ posVals σ, 1 + u * x ≠ 0 := by
  obtain ⟨hx0, h⟩ := ord_K_sign σ hS hs hx
  refine ⟨hx0.ne, fun u hu => ?_⟩
  rcases le_or_gt u s with hus | hsu
  · exact ((h u hu).1 hus).ne'
  · exact ((h u hu).2 hsu).ne

private lemma ord_K_disj (σ : Fin M → ℝ) (hS : (posVals σ).Nonempty) {s s' : ℝ}
    (hs : s ∈ posVals σ) (hs' : s' ∈ posVals σ) (hne : s ≠ s') {x : ℝ} (hx : ordK σ s x)
    (hx' : ordK σ s' x) : False := by
  rcases lt_or_gt_of_ne hne with h | h
  · have a := ((ord_K_sign σ hS hs hx).2 s' hs').2 h
    have b := ((ord_K_sign σ hS hs' hx').2 s' hs').1 le_rfl
    linarith
  · have a := ((ord_K_sign σ hS hs' hx').2 s hs).2 h
    have b := ((ord_K_sign σ hS hs hx).2 s hs).1 le_rfl
    linarith

private lemma ord_I0_good (σ : Fin M → ℝ) (hS : (posVals σ).Nonempty) {x : ℝ}
    (hx : ordI0 σ x) : x ≠ 0 ∧ ∀ u ∈ posVals σ, 1 + u * x ≠ 0 := by
  rcases hx with hx | hx
  · refine ⟨hx.ne', fun u hu => ?_⟩
    have := ord_pos_of_mem σ hu
    have : 0 < 1 + u * x := by positivity
    exact this.ne'
  · obtain ⟨s, hs⟩ := hS
    refine ⟨?_, fun u hu => (hx u hu).ne⟩
    rintro rfl
    have := hx s hs
    norm_num at this

private lemma ord_I0_not_K (σ : Fin M → ℝ) (hS : (posVals σ).Nonempty) {s : ℝ}
    (hs : s ∈ posVals σ) {x : ℝ} (h0 : ordI0 σ x) (hK : ordK σ s x) : False := by
  have h1 := (ord_lt_iff (ord_pos_of_mem σ hs)).1 hK.1
  have hx0 := (ord_K_sign σ hS hs hK).1
  rcases h0 with h | h
  · linarith
  · linarith [h s hs]

/-- Points of `(-1/s_n, 0)` off the poles lie in one of `I_1, …, I_n`. -/
private lemma ord_exists_K (σ : Fin M → ℝ) (hS : (posVals σ).Nonempty) {x : ℝ} (hx0 : x < 0)
    (hx' : ∀ u ∈ posVals σ, 1 + u * x ≠ 0) (hin : ∃ s ∈ posVals σ, 0 < 1 + s * x) :
    ∃ s ∈ posVals σ, ordK σ s x := by
  have hU : ((posVals σ).filter (fun u => 0 < 1 + u * x)).Nonempty := by
    obtain ⟨s, hs, h⟩ := hin
    exact ⟨s, Finset.mem_filter.mpr ⟨hs, h⟩⟩
  have hm := Finset.max'_mem _ hU
  obtain ⟨hmS, hm1⟩ := Finset.mem_filter.mp hm
  refine ⟨_, hmS, (ord_lt_iff (ord_pos_of_mem σ hmS)).2 hm1, ?_⟩
  by_cases hmax : ((posVals σ).filter (fun u => 0 < 1 + u * x)).max' hU = (posVals σ).max' hS
  · rw [hmax, ord_R_max]
    exact hx0
  · obtain ⟨s', hs', hlt, -, hR⟩ := ord_R_next σ hS hmS hmax
    rw [hR]
    apply (ord_gt_iff (ord_pos_of_mem σ hs')).2
    have hnot : ¬ 0 < 1 + s' * x := by
      intro h
      have := Finset.le_max' ((posVals σ).filter (fun u => 0 < 1 + u * x)) s'
        (Finset.mem_filter.mpr ⟨hs', h⟩)
      linarith
    exact lt_of_le_of_ne (not_lt.1 hnot) (hx' s' hs')

private lemma ord_lt_min (σ : Fin M → ℝ) (hS : (posVals σ).Nonempty) {x : ℝ}
    (hx : x < -((posVals σ).min' hS)⁻¹) : ∀ u ∈ posVals σ, 1 + u * x < 0 := by
  intro u hu
  have hm0 := ord_pos_of_mem σ ((posVals σ).min'_mem hS)
  have hu0 := ord_pos_of_mem σ hu
  have : u⁻¹ ≤ ((posVals σ).min' hS)⁻¹ := inv_anti₀ hm0 ((posVals σ).min'_le u hu)
  exact (ord_gt_iff hu0).1 (by linarith)

/-! ## Limits of `f^t` -/

private lemma ord_tendsto_pole (N : ℕ) (σ : Fin M → ℝ) (hN : 0 < N) {s : ℝ}
    (hs : s ∈ posVals σ) {t : ℝ} (ht : 0 < t) :
    Tendsto (ordF N σ t) (𝓝[>] (-s⁻¹)) atTop ∧ Tendsto (ordF N σ t) (𝓝[<] (-s⁻¹)) atBot := by
  have hs0 := ord_pos_of_mem σ hs
  have ha0 : (-s⁻¹ : ℝ) ≠ 0 := by simp [hs0.ne']
  have hcpos : 0 < t * (weight N σ s * s) := by
    have := ord_weight_pos N σ hN hs
    positivity
  have hdec : ∀ y : ℝ, ordF N σ t y =
      (-y⁻¹ + t * ∑ u ∈ (posVals σ).erase s, weight N σ u * u / (1 + u * y)) +
        t * (weight N σ s * s) * (1 + s * y)⁻¹ := by
    intro y
    rw [ordF, ordG, ← Finset.add_sum_erase _ _ hs]
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
      exact (ord_lt_iff hs0).1 hy
    have h2 := (tendsto_inv_nhdsGT_zero.comp h1).const_mul_atTop hcpos
    have h3 := (hg.tendsto.mono_left nhdsWithin_le_nhds).add_atTop h2
    refine h3.congr fun y => ?_
    simp only [Function.comp, hdec y]
  · have h1 : Tendsto (fun y : ℝ => 1 + s * y) (𝓝[<] (-s⁻¹)) (𝓝[<] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨hlin.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (ord_gt_iff hs0).1 hy
    have h2 := (tendsto_inv_nhdsLT_zero.comp h1).const_mul_atBot hcpos
    have h3 := (hg.tendsto.mono_left nhdsWithin_le_nhds).add_atBot h2
    refine h3.congr fun y => ?_
    simp only [Function.comp, hdec y]

private lemma ord_tendsto_zero (N : ℕ) (σ : Fin M → ℝ) (t : ℝ) :
    Tendsto (ordF N σ t) (𝓝[<] 0) atTop := by
  have hg : ContinuousAt (fun y => t * ordG N σ y) 0 := by
    refine ContinuousAt.mul continuousAt_const ?_
    show ContinuousAt (fun y => ∑ u ∈ posVals σ, weight N σ u * u / (1 + u * y)) 0
    refine tendsto_finsetSum _ fun u _ => ?_
    exact ContinuousAt.div continuousAt_const (by fun_prop) (by simp)
  have h1 : Tendsto (fun y : ℝ => -y⁻¹) (𝓝[<] 0) atTop :=
    tendsto_neg_atBot_atTop.comp tendsto_inv_nhdsLT_zero
  exact h1.atTop_add (hg.tendsto.mono_left nhdsWithin_le_nhds)

private lemma ord_tendsto_inf (N : ℕ) (σ : Fin M → ℝ) (t : ℝ) :
    Tendsto (ordF N σ t) atTop (𝓝 0) ∧ Tendsto (ordF N σ t) atBot (𝓝 0) := by
  have hterm : ∀ u ∈ posVals σ,
      Tendsto (fun y : ℝ => weight N σ u * u / (1 + u * y)) atTop (𝓝 0) ∧
      Tendsto (fun y : ℝ => weight N σ u * u / (1 + u * y)) atBot (𝓝 0) := by
    intro u hu
    have hu0 := ord_pos_of_mem σ hu
    constructor
    · exact tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_left _ 1 (tendsto_id.const_mul_atTop hu0))
    · exact tendsto_const_nhds.div_atBot
        (tendsto_atBot_add_const_left _ 1 (tendsto_id.const_mul_atBot hu0))
  constructor
  · have h := (tendsto_inv_atTop_zero.neg).add
      ((tendsto_finsetSum _ fun u hu => (hterm u hu).1).const_mul t)
    simp only [neg_zero, Finset.sum_const_zero, mul_zero, add_zero] at h
    exact h
  · have h := (tendsto_inv_atBot_zero.neg).add
      ((tendsto_finsetSum _ fun u hu => (hterm u hu).2).const_mul t)
    simp only [neg_zero, Finset.sum_const_zero, mul_zero, add_zero] at h
    exact h

/-! ## Roots of `f^t = E` -/

private lemma ord_deriv_left {g : ℝ → ℝ} {d x a : ℝ} (hg : HasDerivAt g d x) (hd : 0 < d)
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

private lemma ord_deriv_right {g : ℝ → ℝ} {d x b : ℝ} (hg : HasDerivAt g d x) (hd : 0 < d)
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

private lemma ord_ivt {g : ℝ → ℝ} {a b E : ℝ} (hab : a ≤ b)
    (hc : ∀ x ∈ Set.Icc a b, ContinuousAt g x)
    (h : (g a < E ∧ E < g b) ∨ (g b < E ∧ E < g a)) : ∃ x ∈ Set.Ioo a b, g x = E := by
  have hcont : ContinuousOn g (Set.Icc a b) := fun x hx => (hc x hx).continuousWithinAt
  rcases h with h | h
  · exact intermediate_value_Ioo hab hcont h
  · exact intermediate_value_Ioo' hab hcont h

private lemma ord_cont_K (N : ℕ) (σ : Fin M → ℝ) (hS : (posVals σ).Nonempty) (t : ℝ) {s : ℝ}
    (hs : s ∈ posVals σ) {a b : ℝ} (ha : ordK σ s a) (hb : ordK σ s b) :
    ∀ x ∈ Set.Icc a b, ContinuousAt (ordF N σ t) x := by
  intro x hx
  have hK : ordK σ s x := ⟨lt_of_lt_of_le ha.1 hx.1, lt_of_le_of_lt hx.2 hb.2⟩
  obtain ⟨h0, h1⟩ := ord_K_good σ hS hs hK
  exact (ord_hasDerivAt_F N σ t h0 h1).continuousAt

/-- A root of `f^t = E` in `I_l` to the left of a point where `f^t < E`. -/
private lemma ord_root_left (N : ℕ) (σ : Fin M → ℝ) (hN : 0 < N) (hS : (posVals σ).Nonempty)
    {t : ℝ} (ht : 0 < t) {E s : ℝ} (hs : s ∈ posVals σ) {z : ℝ} (hz : ordK σ s z)
    (hzE : ordF N σ t z < E) : ∃ r, -s⁻¹ < r ∧ r < z ∧ ordF N σ t r = E := by
  obtain ⟨y, hy, hyE⟩ : ∃ y ∈ Set.Ioo (-s⁻¹) z, E < ordF N σ t y := by
    obtain ⟨y, h1, h2⟩ := (((ord_tendsto_pole N σ hN hs ht).1.eventually
      (eventually_gt_atTop E)).and (Ioo_mem_nhdsGT hz.1)).exists
    exact ⟨y, h2, h1⟩
  have hyK : ordK σ s y := ⟨hy.1, hy.2.trans hz.2⟩
  obtain ⟨r, hr, hrE⟩ := ord_ivt hy.2.le (ord_cont_K N σ hS t hs hyK hz) (Or.inr ⟨hzE, hyE⟩)
  exact ⟨r, hy.1.trans hr.1, hr.2, hrE⟩

/-- A root of `f^t = E` in `I_l`, `l ≥ 2`, to the right of a point where `f^t > E`. -/
private lemma ord_root_right (N : ℕ) (σ : Fin M → ℝ) (hN : 0 < N) (hS : (posVals σ).Nonempty)
    {t : ℝ} (ht : 0 < t) {E s : ℝ} (hs : s ∈ posVals σ) (hne : s ≠ (posVals σ).max' hS) {z : ℝ}
    (hz : ordK σ s z) (hzE : E < ordF N σ t z) :
    ∃ r, z < r ∧ r < ordR σ s ∧ ordF N σ t r = E := by
  obtain ⟨s', hs', -, -, hR⟩ := ord_R_next σ hS hs hne
  have hz2 : z < -s'⁻¹ := hR ▸ hz.2
  obtain ⟨y, hy, hyE⟩ : ∃ y ∈ Set.Ioo z (-s'⁻¹), ordF N σ t y < E := by
    obtain ⟨y, h1, h2⟩ := (((ord_tendsto_pole N σ hN hs' ht).2.eventually
      (eventually_lt_atBot E)).and (Ioo_mem_nhdsLT hz2)).exists
    exact ⟨y, h2, h1⟩
  have hyK : ordK σ s y := ⟨hz.1.trans hy.1, hR ▸ hy.2⟩
  obtain ⟨r, hr, hrE⟩ := ord_ivt hy.1.le (ord_cont_K N σ hS t hs hz hyK) (Or.inr ⟨hyE, hzE⟩)
  exact ⟨r, hr.1, hr.2.trans hyK.2, hrE⟩

/-- Every `I_l`, `l ≥ 2`, contains a root of `f^t = E`. -/
private lemma ord_root_default (N : ℕ) (σ : Fin M → ℝ) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {t : ℝ} (ht : 0 < t) (E : ℝ) {s : ℝ} (hs : s ∈ posVals σ)
    (hne : s ≠ (posVals σ).max' hS) : ∃ r, ordK σ s r ∧ ordF N σ t r = E := by
  have hlt := ord_left_lt_R σ hS hs
  have hmid : ordK σ s ((-s⁻¹ + ordR σ s) / 2) := ⟨by linarith, by linarith⟩
  rcases lt_trichotomy (ordF N σ t ((-s⁻¹ + ordR σ s) / 2)) E with h | h | h
  · obtain ⟨r, h1, h2, h3⟩ := ord_root_left N σ hN hS ht hs hmid h
    exact ⟨r, ⟨h1, h2.trans hmid.2⟩, h3⟩
  · exact ⟨_, hmid, h⟩
  · obtain ⟨r, h1, h2, h3⟩ := ord_root_right N σ hN hS ht hs hne hmid h
    exact ⟨r, ⟨hmid.1.trans h1, h2⟩, h3⟩

private lemma ord_cont_left (N : ℕ) (σ : Fin M → ℝ) (hS : (posVals σ).Nonempty) (t : ℝ)
    {a b : ℝ} (hb : b < -((posVals σ).min' hS)⁻¹) :
    ∀ x ∈ Set.Icc a b, ContinuousAt (ordF N σ t) x := by
  intro x hx
  have h := ord_lt_min σ hS (lt_of_le_of_lt hx.2 hb)
  obtain ⟨h0, h1⟩ := ord_I0_good σ hS (Or.inr h)
  exact (ord_hasDerivAt_F N σ t h0 h1).continuousAt

/-- A root of `f^t = E` in `(z, -1/s_n)` when `z < -1/s_n` and `f^t(z) > E`. -/
private lemma ord_root_I0_left (N : ℕ) (σ : Fin M → ℝ) (hN : 0 < N) (hS : (posVals σ).Nonempty)
    {t : ℝ} (ht : 0 < t) {E z : ℝ} (hz : z < -((posVals σ).min' hS)⁻¹)
    (hzE : E < ordF N σ t z) :
    ∃ r, z < r ∧ r < -((posVals σ).min' hS)⁻¹ ∧ ordF N σ t r = E := by
  obtain ⟨y, hy, hyE⟩ : ∃ y ∈ Set.Ioo z (-((posVals σ).min' hS)⁻¹), ordF N σ t y < E := by
    obtain ⟨y, h1, h2⟩ := (((ord_tendsto_pole N σ hN ((posVals σ).min'_mem hS) ht).2.eventually
      (eventually_lt_atBot E)).and (Ioo_mem_nhdsLT hz)).exists
    exact ⟨y, h2, h1⟩
  obtain ⟨r, hr, hrE⟩ := ord_ivt hy.1.le (ord_cont_left N σ hS t hy.2) (Or.inr ⟨hyE, hzE⟩)
  exact ⟨r, hr.1, hr.2.trans hy.2, hrE⟩

/-- For `E < 0`, a root of `f^t = E` in `(-∞, -1/s_n)`. -/
private lemma ord_root_I0_far_left (N : ℕ) (σ : Fin M → ℝ) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {t : ℝ} (ht : 0 < t) {E : ℝ} (hE : E < 0) :
    ∃ r, r < -((posVals σ).min' hS)⁻¹ ∧ ordF N σ t r = E := by
  obtain ⟨z, h1, h2⟩ := (((ord_tendsto_inf N σ t).2.eventually (lt_mem_nhds hE)).and
    (eventually_lt_atBot (-((posVals σ).min' hS)⁻¹))).exists
  obtain ⟨r, -, hr, hrE⟩ := ord_root_I0_left N σ hN hS ht h2 h1
  exact ⟨r, hr, hrE⟩

/-- For `E > 0`, a root of `f^t = E` in `(z, ∞)` when `z > 0` and `f^t(z) > E`. -/
private lemma ord_root_I0_far_right (N : ℕ) (σ : Fin M → ℝ) (hS : (posVals σ).Nonempty)
    (t : ℝ) {E z : ℝ} (hz : 0 < z) (hzE : E < ordF N σ t z) (hE : 0 < E) :
    ∃ r, z < r ∧ ordF N σ t r = E := by
  obtain ⟨y, h1, h2⟩ := (((ord_tendsto_inf N σ t).1.eventually (gt_mem_nhds hE)).and
    (eventually_gt_atTop z)).exists
  have hc : ∀ x ∈ Set.Icc z y, ContinuousAt (ordF N σ t) x := by
    intro x hx
    obtain ⟨h0, h1⟩ := ord_I0_good σ hS (Or.inl (lt_of_lt_of_le hz hx.1))
    exact (ord_hasDerivAt_F N σ t h0 h1).continuousAt
  obtain ⟨r, hr, hrE⟩ := ord_ivt h2.le hc (Or.inr ⟨h1, hzE⟩)
  exact ⟨r, hr.1, hrE⟩

/-! ## Root counts for `f^t` -/

/-- An increasing crossing of the level `E` in `I_l` gives `2` roots of `f^t = E` in `I_1` and
`3` in `I_l`, `l ≥ 2`. -/
private lemma ord_special_K (N : ℕ) (σ : Fin M → ℝ) (hN : 0 < N) (hS : (posVals σ).Nonempty)
    {t : ℝ} (ht : 0 < t) {E s : ℝ} (hs : s ∈ posVals σ) {ξ : ℝ} (hξ : ordK σ s ξ)
    (hE : ordF N σ t ξ = E) (hd : 0 < ordF1 N σ t ξ) :
    ∃ T : Finset ℝ, (∀ x ∈ T, ordK σ s x ∧ ordF N σ t x = E) ∧
      (if s = (posVals σ).max' hS then 0 else 1) + 2 ≤ T.card := by
  obtain ⟨h0, h1⟩ := ord_K_good σ hS hs hξ
  have hder := ord_hasDerivAt_F N σ t h0 h1
  obtain ⟨y1, hy1, hy1E⟩ := ord_deriv_left hder hd hξ.1
  have hy1K : ordK σ s y1 := ⟨hy1.1, hy1.2.trans hξ.2⟩
  obtain ⟨r1, hr1a, hr1b, hr1E⟩ := ord_root_left N σ hN hS ht hs hy1K (hE ▸ hy1E)
  have hr1K : ordK σ s r1 := ⟨hr1a, (hr1b.trans hy1.2).trans hξ.2⟩
  have hr1ξ : r1 < ξ := hr1b.trans hy1.2
  by_cases hmax : s = (posVals σ).max' hS
  · refine ⟨{r1, ξ}, ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ⟨hr1K, hr1E⟩
      · exact ⟨hξ, hE⟩
    · rw [ite_eq_left hmax, Finset.card_pair hr1ξ.ne]
  · obtain ⟨y2, hy2, hy2E⟩ := ord_deriv_right hder hd hξ.2
    have hy2K : ordK σ s y2 := ⟨hξ.1.trans hy2.1, hy2.2⟩
    obtain ⟨r2, hr2a, hr2b, hr2E⟩ := ord_root_right N σ hN hS ht hs hmax hy2K (hE ▸ hy2E)
    have hr2K : ordK σ s r2 := ⟨(hξ.1.trans hy2.1).trans hr2a, hr2b⟩
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

/-- An increasing crossing of the level `E ≠ 0` at a finite point of `I_0` gives `2` roots of
`f^t = E` in `I_0`. -/
private lemma ord_special_I0 (N : ℕ) (σ : Fin M → ℝ) (hN : 0 < N) (hS : (posVals σ).Nonempty)
    {t : ℝ} (ht : 0 < t) {E ξ : ℝ} (hξ : ordI0 σ ξ) (hE : ordF N σ t ξ = E)
    (hd : 0 < ordF1 N σ t ξ) :
    ∃ T : Finset ℝ, (∀ x ∈ T, ordI0 σ x ∧ ordF N σ t x = E) ∧
      (if E = 0 then 1 else 2) ≤ T.card := by
  by_cases hE0 : E = 0
  · refine ⟨{ξ}, ?_, by simp [hE0]⟩
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    exact ⟨hξ, hE⟩
  · rw [ite_eq_right hE0]
    obtain ⟨h0, h1⟩ := ord_I0_good σ hS hξ
    have hder := ord_hasDerivAt_F N σ t h0 h1
    suffices h : ∃ r, r ≠ ξ ∧ ordI0 σ r ∧ ordF N σ t r = E by
      obtain ⟨r, hne, hr, hrE⟩ := h
      refine ⟨{ξ, r}, ?_, by rw [Finset.card_pair hne.symm]⟩
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ⟨hξ, hE⟩
      · exact ⟨hr, hrE⟩
    have hm0 := ord_pos_of_mem σ ((posVals σ).min'_mem hS)
    rcases hξ with hpos | hneg
    · rcases lt_or_gt_of_ne hE0 with hlt | hgt
      · obtain ⟨r, hr, hrE⟩ := ord_root_I0_far_left N σ hN hS ht hlt
        have hr0 : r < 0 := hr.trans (by simpa using hm0)
        exact ⟨r, (hr0.trans hpos).ne, Or.inr (ord_lt_min σ hS hr), hrE⟩
      · obtain ⟨y2, hy2, hy2E⟩ := ord_deriv_right hder hd (lt_add_one ξ)
        obtain ⟨r, hr, hrE⟩ := ord_root_I0_far_right N σ hS t (hpos.trans hy2.1) (hE ▸ hy2E) hgt
        exact ⟨r, (hy2.1.trans hr).ne', Or.inl ((hpos.trans hy2.1).trans hr), hrE⟩
    · have hξlt : ξ < -((posVals σ).min' hS)⁻¹ :=
        (ord_gt_iff hm0).2 (hneg _ ((posVals σ).min'_mem hS))
      obtain ⟨y2, hy2, hy2E⟩ := ord_deriv_right hder hd hξlt
      obtain ⟨r, hr1, hr2, hrE⟩ := ord_root_I0_left N σ hN hS ht hy2.2 (hE ▸ hy2E)
      exact ⟨r, (hy2.1.trans hr1).ne', Or.inr (ord_lt_min σ hS hr2), hrE⟩

/-- Sum of root multiplicities over finite sets of points in `I_1, …, I_n` and in `I_0`. -/
private lemma ord_count (N : ℕ) (σ : Fin M → ℝ) (hS : (posVals σ).Nonempty) (t E : ℝ)
    (A : ℝ → Finset ℝ) (hA : ∀ s ∈ posVals σ, ∀ x ∈ A s, ordK σ s x) (B : Finset ℝ)
    (hB : ∀ x ∈ B, ordI0 σ x) :
    ∑ s ∈ posVals σ, ∑ x ∈ A s, (ordP N σ t E).rootMultiplicity x +
      ∑ x ∈ B, (ordP N σ t E).rootMultiplicity x ≤ (ordP N σ t E).natDegree := by
  have hpd : ((posVals σ : Set ℝ)).PairwiseDisjoint A := by
    intro s hs s' hs' hne
    change Disjoint (A s) (A s')
    refine Finset.disjoint_left.2 fun x hx hx' => ?_
    exact ord_K_disj σ hS hs hs' hne (hA s hs x hx) (hA s' hs' x hx')
  have hdisj : Disjoint ((posVals σ).biUnion A) B := by
    refine Finset.disjoint_left.2 fun x hx hxB => ?_
    obtain ⟨s, hs, hxs⟩ := Finset.mem_biUnion.1 hx
    exact ord_I0_not_K σ hS hs (hB x hxB) (hA s hs x hxs)
  rw [← Finset.sum_biUnion hpd, ← Finset.sum_union hdisj]
  exact ord_budget _ _

/-- Number of roots of `f^t = E` over finite sets of roots in `I_1, …, I_n` and in `I_0`. -/
private lemma ord_count_card (N : ℕ) (σ : Fin M → ℝ) (hS : (posVals σ).Nonempty) (t E : ℝ)
    (A : ℝ → Finset ℝ) (hA : ∀ s ∈ posVals σ, ∀ x ∈ A s, ordK σ s x ∧ ordF N σ t x = E)
    (B : Finset ℝ) (hB : ∀ x ∈ B, ordI0 σ x ∧ ordF N σ t x = E) :
    ∑ s ∈ posVals σ, (A s).card + B.card ≤ (ordP N σ t E).natDegree := by
  refine le_trans ?_ (ord_count N σ hS t E A (fun s hs x hx => (hA s hs x hx).1) B
    (fun x hx => (hB x hx).1))
  refine add_le_add (Finset.sum_le_sum fun s hs => ?_) ?_
  · rw [Finset.card_eq_sum_ones]
    refine Finset.sum_le_sum fun x hx => ?_
    obtain ⟨h0, h1⟩ := ord_K_good σ hS hs (hA s hs x hx).1
    exact ord_mult_one N σ t E h0 h1 (hA s hs x hx).2
  · rw [Finset.card_eq_sum_ones]
    refine Finset.sum_le_sum fun x hx => ?_
    obtain ⟨h0, h1⟩ := ord_I0_good σ hS (hB x hx).1
    exact ord_mult_one N σ t E h0 h1 (hB x hx).2

private lemma ord_sum_base (S : Finset ℝ) (hS : S.Nonempty) :
    ∑ s ∈ S, (if s = S.max' hS then 0 else 1) = S.card - 1 := by
  have h : ∀ s ∈ S, (if s = S.max' hS then 0 else 1 : ℕ) = if s ≠ S.max' hS then 1 else 0 := by
    intro s _
    by_cases h : s = S.max' hS <;> simp [h]
  rw [Finset.sum_congr rfl h, Finset.sum_boole, Finset.filter_ne',
    Finset.card_erase_of_mem (S.max'_mem hS)]
  simp

private lemma ord_sum_lb (S : Finset ℝ) (hS : S.Nonempty) (c e : ℝ → ℕ)
    (h : ∀ s ∈ S, (if s = S.max' hS then 0 else 1) + e s ≤ c s) :
    S.card - 1 + ∑ s ∈ S, e s ≤ ∑ s ∈ S, c s := by
  rw [← ord_sum_base S hS, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum h

/-- For `t ∈ (0, 1]`, two increasing crossings of one level `E` by `f^t` in two different
intervals among `I_0, I_1, …, I_n` would give more than `deg P^t_E` roots. -/
private lemma ord_disjoint (N : ℕ) (σ : Fin M → ℝ) (hN : 0 < N) (hS : (posVals σ).Nonempty)
    {t : ℝ} (ht : 0 < t) {E s : ℝ} (hs : s ∈ posVals σ) {ξ ξ' : ℝ} (hξ : ordK σ s ξ)
    (hE : ordF N σ t ξ = E) (hd : 0 < ordF1 N σ t ξ) (hE' : ordF N σ t ξ' = E)
    (hd' : 0 < ordF1 N σ t ξ')
    (hξ' : (∃ s' ∈ posVals σ, s' ≠ s ∧ ordK σ s' ξ') ∨ ordI0 σ ξ') : False := by
  obtain ⟨T1, hT1, hc1⟩ := ord_special_K N σ hN hS ht hs hξ hE hd
  have hdef : ∀ u ∈ posVals σ, u ≠ (posVals σ).max' hS → ∃ r, ordK σ u r ∧ ordF N σ t r = E :=
    fun u hu hne => ord_root_default N σ hN hS ht E hu hne
  choose! rd hrd using hdef
  have hdeg := ord_natDegree_P N σ t E
  have hcard1 : 1 ≤ (posVals σ).card := Finset.card_pos.2 hS
  rcases hξ' with ⟨s', hs', hss', hξ'K⟩ | hI0
  · obtain ⟨T2, hT2, hc2⟩ := ord_special_K N σ hN hS ht hs' hξ'K hE' hd'
    let A : ℝ → Finset ℝ := fun u => if u = s then T1 else if u = s' then T2 else
      if u = (posVals σ).max' hS then ∅ else {rd u}
    have hA : ∀ u ∈ posVals σ, ∀ x ∈ A u, ordK σ u x ∧ ordF N σ t x = E := by
      intro u hu x hx
      simp only [A] at hx
      split_ifs at hx with h1 h2 h3
      · subst h1; exact hT1 x hx
      · subst h2; exact hT2 x hx
      · simp at hx
      · rw [Finset.mem_singleton] at hx
        subst hx
        exact hrd u hu h3
    have hcount := ord_count_card N σ hS t E A hA ∅ (by simp)
    have hlb := ord_sum_lb (posVals σ) hS (fun u => (A u).card)
      (fun u => (if u = s then 2 else 0) + (if u = s' then 2 else 0)) (by
        intro u hu
        simp only [A]
        by_cases h1 : u = s
        · subst h1
          rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_right hss'.symm]
          simpa using hc1
        · by_cases h2 : u = s'
          · subst h2
            rw [ite_eq_right h1, ite_eq_left rfl, ite_eq_right h1, ite_eq_left rfl]
            simpa using hc2
          · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h1, ite_eq_right h2]
            by_cases h3 : u = (posVals σ).max' hS
            · simp [h3]
            · simp [h3])
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq', ite_eq_left hs,
      ite_eq_left hs'] at hlb
    simp only [Finset.card_empty, add_zero] at hcount
    omega
  · obtain ⟨T2, hT2, hc2⟩ := ord_special_I0 N σ hN hS ht hI0 hE' hd'
    let A : ℝ → Finset ℝ := fun u => if u = s then T1 else
      if u = (posVals σ).max' hS then ∅ else {rd u}
    have hA : ∀ u ∈ posVals σ, ∀ x ∈ A u, ordK σ u x ∧ ordF N σ t x = E := by
      intro u hu x hx
      simp only [A] at hx
      split_ifs at hx with h1 h3
      · subst h1; exact hT1 x hx
      · simp at hx
      · rw [Finset.mem_singleton] at hx
        subst hx
        exact hrd u hu h3
    have hcount := ord_count_card N σ hS t E A hA T2 hT2
    have hlb := ord_sum_lb (posVals σ) hS (fun u => (A u).card)
      (fun u => if u = s then 2 else 0) (by
        intro u hu
        simp only [A]
        by_cases h1 : u = s
        · subst h1
          rw [ite_eq_left rfl, ite_eq_left rfl]
          exact hc1
        · rw [ite_eq_right h1, ite_eq_right h1]
          by_cases h3 : u = (posVals σ).max' hS
          · simp [h3]
          · simp [h3])
    rw [Finset.sum_ite_eq', ite_eq_left hs] at hlb
    by_cases hE0 : E = 0
    · rw [ite_eq_left hE0] at hc2
      have := hdeg.2 hE0
      omega
    · rw [ite_eq_right hE0] at hc2
      have := hdeg.1
      omega

private lemma ord_affine {A B : ℝ} (hA : 0 < A) (hAB : A + B < 0) :
    ∃ t, 0 < t ∧ t < 1 ∧ A + t * B = 0 := by
  have hB : 0 < -B := by linarith
  refine ⟨A / (-B), div_pos hA hB, (div_lt_one hB).2 (by linarith), ?_⟩
  have hB0 : B ≠ 0 := by linarith
  field_simp
  ring

/-- Lemma 2.5, interpolation step: if `ξ ∈ I_i` and `ξ' ∈ I_j` are finite points with
`f'(ξ) ≥ 0` and `f'(ξ') ≥ 0`, and `I_i` comes before `I_j` in the order
`I_1, I_2, …, I_n, I_0`, then `f(ξ) ≥ f(ξ')`. -/
private lemma ord_interp (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {s : ℝ} (hs : s ∈ posVals σ) {ξ ξ' : ℝ} (hξ : ordK σ s ξ)
    (h1 : 0 ≤ fR1 N σ ξ) (h1' : 0 ≤ fR1 N σ ξ')
    (hξ' : (∃ s' ∈ posVals σ, s' ≠ s ∧ ordK σ s' ξ' ∧ ξ' < ξ) ∨ ordI0 σ ξ') :
    fR N σ ξ' ≤ fR N σ ξ := by
  by_contra hlt
  rw [not_le, ord_fR_eq N σ hσ] at hlt
  rw [ord_fR1_eq N σ hσ] at h1 h1'
  obtain ⟨hξ0, hξp⟩ := ord_K_good σ hS hs hξ
  have hgood' : ξ' ≠ 0 ∧ ∀ u ∈ posVals σ, 1 + u * ξ' ≠ 0 := by
    rcases hξ' with ⟨s', hs', -, hK, -⟩ | h
    · exact ord_K_good σ hS hs' hK
    · exact ord_I0_good σ hS h
  have hξneg : ξ < 0 := (ord_K_sign σ hS hs hξ).1
  have hh0 : 0 < -ξ⁻¹ + ξ'⁻¹ := by
    have hcase : (ξ' < ξ) ∨ 0 < ξ' := by
      rcases hξ' with ⟨-, -, -, -, h⟩ | h | h
      · exact Or.inl h
      · exact Or.inr h
      · left
        have := (ord_gt_iff (ord_pos_of_mem σ hs)).2 (h s hs)
        exact this.trans hξ.1
    rcases hcase with h | h
    · have := (inv_lt_inv_of_neg hξneg (h.trans hξneg)).2 h
      linarith
    · have := inv_pos.2 h
      have := inv_lt_zero.2 hξneg
      linarith
  have hab : (-ξ⁻¹ + ξ'⁻¹) + (ordG N σ ξ - ordG N σ ξ') < 0 := by
    simp only [ordF, one_mul] at hlt
    linarith
  obtain ⟨t, ht0, ht1, hht⟩ := ord_affine hh0 hab
  have hEq : ordF N σ t ξ' = ordF N σ t ξ := by
    unfold ordF
    linear_combination (-1 : ℝ) * hht
  have hd : 0 < ordF1 N σ t ξ := by
    have hH := ord_H_pos N σ hN hS hξp
    have := mul_pos (sub_pos.2 ht1) hH
    unfold ordF1 at h1 ⊢
    linarith [show (1 - t) * ordH N σ ξ = ordH N σ ξ - t * ordH N σ ξ by ring]
  have hd' : 0 < ordF1 N σ t ξ' := by
    have hH := ord_H_pos N σ hN hS hgood'.2
    have := mul_pos (sub_pos.2 ht1) hH
    unfold ordF1 at h1' ⊢
    linarith [show (1 - t) * ordH N σ ξ' = ordH N σ ξ' - t * ordH N σ ξ' by ring]
  refine ord_disjoint N σ hN hS ht0 hs hξ rfl hd hEq hd' ?_
  rcases hξ' with ⟨s', hs', hne, hK, -⟩ | h
  · exact Or.inl ⟨s', hs', hne, hK⟩
  · exact Or.inr h

/-! ## The ordered critical points `x_1 ≥ ⋯ ≥ x_{2p-1}` -/

/-- The number of critical points in `(y, 0)` counted with multiplicity. -/
private def ordA (N : ℕ) (σ : Fin M → ℝ) (y : ℝ) : ℕ :=
  Multiset.card ((innerCrit N σ).filter (fun x => y < x))

private lemma ord_critPoly_ne_zero (N : ℕ) (σ : Fin M → ℝ) : critPoly N σ ≠ 0 := by
  intro h
  have := critPoly_eval_zero N σ
  rw [h] at this
  simp at this

/-- `Q(-1/u) ≠ 0` at the poles. -/
private lemma ord_critPoly_pole (N : ℕ) (σ : Fin M → ℝ) (hN : 0 < N) {u : ℝ}
    (hu : u ∈ posVals σ) : (critPoly N σ).eval (-u⁻¹) ≠ 0 := by
  have hu0 := ord_pos_of_mem σ hu
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
    (mul_ne_zero (mul_ne_zero (ord_weight_pos N σ hN hu).ne' (pow_ne_zero 2 hu0.ne')) ?_)
  refine Finset.prod_ne_zero_iff.mpr fun t ht => ?_
  have htu : t ≠ u := (Finset.mem_erase.mp ht).1
  have : 1 + t * (-u⁻¹) = (u - t) / u := by field_simp; ring
  rw [this]
  exact pow_ne_zero 2 (div_ne_zero (sub_ne_zero.mpr htu.symm) hu0.ne')

private lemma ord_mem_innerCrit (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    {x : ℝ} (hx : x ∈ innerCrit N σ) :
    InInner σ x ∧ (∀ u ∈ posVals σ, 1 + u * x ≠ 0) ∧ fR1 N σ x = 0 := by
  unfold innerCrit at hx
  rw [Multiset.mem_filter, mem_roots (ord_critPoly_ne_zero N σ)] at hx
  obtain ⟨hroot, hin⟩ := hx
  have h0 : (critPoly N σ).eval x = 0 := hroot
  have hnp : ∀ u ∈ posVals σ, 1 + u * x ≠ 0 := by
    intro u hu h
    have hu0 := ord_pos_of_mem σ hu
    have hx' : x = -u⁻¹ := by
      field_simp
      linear_combination h
    rw [hx'] at h0
    exact ord_critPoly_pole N σ hN hu h0
  refine ⟨hin, hnp, ?_⟩
  rw [critPoly_eval N σ hσ hin.1.ne (ord_nonpole_all σ hσ hnp)] at h0
  have hpre : x ^ 2 * ∏ s ∈ posVals σ, (1 + s * x) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hin.1.ne)
      (Finset.prod_ne_zero_iff.mpr fun s hs => pow_ne_zero 2 (hnp s hs))
  exact (mul_eq_zero.mp h0).resolve_left hpre

private lemma ord_mem_innerCrit_of (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i)
    (hS : (posVals σ).Nonempty) {s : ℝ} (hs : s ∈ posVals σ) {x : ℝ} (hx : ordK σ s x)
    (h1 : fR1 N σ x = 0) : x ∈ innerCrit N σ := by
  obtain ⟨hx0, hsgn⟩ := ord_K_sign σ hS hs hx
  obtain ⟨-, hnp⟩ := ord_K_good σ hS hs hx
  unfold innerCrit
  rw [Multiset.mem_filter, mem_roots (ord_critPoly_ne_zero N σ)]
  refine ⟨?_, hx0, s, hs, (hsgn s hs).1 le_rfl⟩
  show (critPoly N σ).eval x = 0
  rw [critPoly_eval N σ hσ hx0.ne (ord_nonpole_all σ hσ hnp), h1, mul_zero]

private lemma ord_mem_K (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {x : ℝ} (hx : x ∈ innerCrit N σ) :
    ∃ s ∈ posVals σ, ordK σ s x := by
  obtain ⟨hin, hnp, -⟩ := ord_mem_innerCrit N σ hσ hN hx
  exact ord_exists_K σ hS hin.1 hnp hin.2

/-- In a list sorted in decreasing order, the entries `> y` form an initial segment. -/
private lemma ord_list_prefix (y : ℝ) : ∀ (L : List ℝ), L.Pairwise (fun a b => b ≤ a) →
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
      have ih := ord_list_prefix y L hpw.2 j hj
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

private lemma ord_sort_spec (m : Multiset ℝ) {i : ℕ} (hi : i < Multiset.card m) :
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
  · rw [ord_list_prefix y _ hpw i hi', ← Multiset.countP_eq_card_filter,
      ← Multiset.coe_countP, Multiset.coe_reverse, Multiset.sort_eq]

private lemma ord_sort_surj (m : Multiset ℝ) {d : ℝ} (hd : d ∈ m) :
    ∃ i < Multiset.card m, (m.sort (· ≤ ·)).reverse.getD i 0 = d := by
  have hd' : d ∈ (m.sort (· ≤ ·)).reverse := by
    rwa [List.mem_reverse, Multiset.mem_sort]
  obtain ⟨i, hi, hid⟩ := List.mem_iff_getElem.1 hd'
  have hlen : (m.sort (· ≤ ·)).reverse.length = Multiset.card m := by
    rw [List.length_reverse, Multiset.length_sort]
  exact ⟨i, hlen ▸ hi, by rw [List.getD_eq_getElem _ _ hi, hid]⟩

/-- `x_k ∈ 𝒞`, and `y < x_k` iff at least `k` critical points lie in `(y, 0)`. -/
private lemma ord_xCrit_spec (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {k : ℕ} (hk1 : 1 ≤ k) (hk : k < 2 * numBands N σ) :
    xCrit N σ k ∈ innerCrit N σ ∧ ∀ y, (y < xCrit N σ k ↔ k ≤ ordA N σ y) := by
  have hc := (card_innerCrit N σ hσ hN hS).1
  have hx : xCrit N σ k = ((innerCrit N σ).sort (· ≤ ·)).reverse.getD (k - 1) 0 := by
    unfold xCrit
    rw [ite_eq_right (by omega)]
  obtain ⟨hmem, hspec⟩ := ord_sort_spec (innerCrit N σ) (i := k - 1) (by omega)
  rw [hx]
  refine ⟨hmem, fun y => ?_⟩
  rw [hspec y, ordA]
  omega

private lemma ord_xCrit_surj (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {d : ℝ} (hd : d ∈ innerCrit N σ) :
    ∃ k, 1 ≤ k ∧ k < 2 * numBands N σ ∧ xCrit N σ k = d := by
  have hc := (card_innerCrit N σ hσ hN hS).1
  obtain ⟨i, hi, hid⟩ := ord_sort_surj _ hd
  refine ⟨i + 1, by omega, by omega, ?_⟩
  unfold xCrit
  rw [ite_eq_right (by omega), Nat.add_sub_cancel]
  exact hid

private lemma ord_xCrit_anti (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {k k' : ℕ} (hk1 : 1 ≤ k) (hkk : k ≤ k')
    (hk' : k' < 2 * numBands N σ) : xCrit N σ k' ≤ xCrit N σ k := by
  by_contra h
  rw [not_le] at h
  have h1 := ((ord_xCrit_spec N σ hσ hN hS (k := k') (by omega) hk').2 (xCrit N σ k)).1 h
  have h2 := ((ord_xCrit_spec N σ hσ hN hS hk1 (by omega)).2 (xCrit N σ k)).2 (by omega)
  exact lt_irrefl _ h2

private lemma ord_ne_R (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {s : ℝ} (hs : s ∈ posVals σ) {x : ℝ}
    (hx : x ∈ innerCrit N σ) : x ≠ ordR σ s := by
  obtain ⟨hin, hnp, -⟩ := ord_mem_innerCrit N σ hσ hN hx
  intro h
  by_cases hmax : s = (posVals σ).max' hS
  · rw [hmax, ord_R_max] at h
    linarith [hin.1]
  · obtain ⟨s', hs', -, -, hR⟩ := ord_R_next σ hS hs hmax
    rw [hR] at h
    apply hnp s' hs'
    rw [h]
    have := ord_pos_of_mem σ hs'
    field_simp
    ring

private lemma ord_A_split (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {s : ℝ} (hs : s ∈ posVals σ) :
    ordA N σ (-s⁻¹) =
      ordA N σ (ordR σ s) + Multiset.card ((innerCrit N σ).filter (ordK σ s)) := by
  have hlt := ord_left_lt_R σ hS hs
  have hne := fun x (hx : x ∈ innerCrit N σ) => ord_ne_R N σ hσ hN hS hs hx
  unfold ordA
  have h1 := Multiset.filter_add_not (fun x : ℝ => x < ordR σ s)
    ((innerCrit N σ).filter (fun x => -s⁻¹ < x))
  have e1 : ((innerCrit N σ).filter (fun x => -s⁻¹ < x)).filter (fun x => x < ordR σ s) =
      (innerCrit N σ).filter (ordK σ s) := by
    rw [Multiset.filter_filter]
    exact Multiset.filter_congr fun x _ => by simp only [ordK, and_comm]
  have e2 : ((innerCrit N σ).filter (fun x => -s⁻¹ < x)).filter (fun x => ¬ x < ordR σ s) =
      (innerCrit N σ).filter (fun x => ordR σ s < x) := by
    rw [Multiset.filter_filter]
    refine Multiset.filter_congr fun x hx => ?_
    constructor
    · rintro ⟨h1, -⟩
      exact lt_of_le_of_ne (not_lt.mp h1) (hne x hx).symm
    · intro h
      exact ⟨not_lt.mpr h.le, lt_trans hlt h⟩
  rw [← h1, Multiset.card_add, e1, e2, add_comm]

private lemma ord_A_zero (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) :
    ordA N σ 0 = 0 := by
  unfold ordA
  rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
  intro x hx
  exact not_lt.2 (ord_mem_innerCrit N σ hσ hN hx).1.1.le

private lemma ord_card_K_max (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) :
    Multiset.card ((innerCrit N σ).filter (ordK σ ((posVals σ).max' hS))) = 1 := by
  rw [← card_innerCrit_I1 N σ hσ hN hS]
  congr 1
  refine Multiset.filter_congr fun x hx => ?_
  have hin := (ord_mem_innerCrit N σ hσ hN hx).1
  have hm := (posVals σ).max'_mem hS
  constructor
  · intro hK s hs
    exact ((ord_K_sign σ hS hm hK).2 s hs).1 ((posVals σ).le_max' s hs)
  · intro h
    refine ⟨(ord_lt_iff (ord_pos_of_mem σ hm)).2 (h _ hm), ?_⟩
    rw [ord_R_max]
    exact hin.1

private lemma ord_card_K_inner (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {s : ℝ} (hs : s ∈ posVals σ) (hne : s ≠ (posVals σ).max' hS) :
    Multiset.card ((innerCrit N σ).filter (ordK σ s)) = 0 ∨
      Multiset.card ((innerCrit N σ).filter (ordK σ s)) = 2 := by
  obtain ⟨s', hs', hss', hcons, hR⟩ := ord_R_next σ hS hs hne
  have e : (innerCrit N σ).filter (ordK σ s) =
      (innerCrit N σ).filter (fun x => -s⁻¹ < x ∧ x < -s'⁻¹) :=
    Multiset.filter_congr fun x _ => by rw [ordK, hR]
  rw [e]
  exact card_innerCrit_Ii N σ hσ hN hs hs' hss' hcons

private lemma ord_A_odd (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) (n : ℕ) : ∀ s ∈ posVals σ,
    ((posVals σ).filter (fun u => s < u)).card = n → Odd (ordA N σ (-s⁻¹)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs hcard
    rw [ord_A_split N σ hσ hN hS hs]
    by_cases hmax : s = (posVals σ).max' hS
    · subst hmax
      rw [ord_R_max, ord_A_zero N σ hσ hN, ord_card_K_max N σ hσ hN hS]
      exact odd_one
    · obtain ⟨s', hs', hss', -, hR⟩ := ord_R_next σ hS hs hmax
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
      rcases ord_card_K_inner N σ hσ hN hS hs hmax with h | h
      · rw [h, add_zero]
        exact ho
      · rw [h]
        exact ho.add_even even_two

/-- The critical points to the right of `I_l`: none for `I_1`, an odd number for `l ≥ 2`. -/
private lemma ord_lo (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {s : ℝ} (hs : s ∈ posVals σ) :
    (s = (posVals σ).max' hS ∧ ordA N σ (ordR σ s) = 0 ∧
        Multiset.card ((innerCrit N σ).filter (ordK σ s)) = 1) ∨
      (s ≠ (posVals σ).max' hS ∧ Odd (ordA N σ (ordR σ s)) ∧
        (Multiset.card ((innerCrit N σ).filter (ordK σ s)) = 0 ∨
          Multiset.card ((innerCrit N σ).filter (ordK σ s)) = 2)) := by
  by_cases hmax : s = (posVals σ).max' hS
  · left
    subst hmax
    exact ⟨rfl, by rw [ord_R_max, ord_A_zero N σ hσ hN], ord_card_K_max N σ hσ hN hS⟩
  · right
    obtain ⟨s', hs', -, -, hR⟩ := ord_R_next σ hS hs hmax
    refine ⟨hmax, ?_, ord_card_K_inner N σ hσ hN hS hs hmax⟩
    rw [hR]
    exact ord_A_odd N σ hσ hN hS _ s' hs' rfl

/-- `x_k ∈ I_l` iff the position `k` lies in the block of `I_l`. -/
private lemma ord_block (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {s : ℝ} (hs : s ∈ posVals σ) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k < 2 * numBands N σ) :
    ordK σ s (xCrit N σ k) ↔ ordA N σ (ordR σ s) < k ∧ k ≤ ordA N σ (-s⁻¹) := by
  obtain ⟨hmem, hspec⟩ := ord_xCrit_spec N σ hσ hN hS hk1 hk
  have hne := ord_ne_R N σ hσ hN hS hs hmem
  unfold ordK
  rw [hspec (-s⁻¹)]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1⟩
    by_contra h
    have := (hspec (ordR σ s)).2 (not_lt.1 h)
    linarith
  · rintro ⟨h1, h2⟩
    refine ⟨h2, ?_⟩
    rcases lt_or_gt_of_ne hne with h | h
    · exact h
    · have := (hspec (ordR σ s)).1 h
      omega

/-- `x_1 ∈ I_1`. -/
private lemma ord_first (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) : ordK σ ((posVals σ).max' hS) (xCrit N σ 1) := by
  have hp := (card_innerCrit N σ hσ hN hS).2
  obtain ⟨hmem, -⟩ := ord_xCrit_spec N σ hσ hN hS le_rfl (by omega)
  obtain ⟨s, hs, hK⟩ := ord_mem_K N σ hσ hN hS hmem
  have hb := (ord_block N σ hσ hN hS hs le_rfl (by omega)).1 hK
  rcases ord_lo N σ hσ hN hS hs with ⟨hmax, -, -⟩ | ⟨-, ⟨c, hc⟩, -⟩
  · rw [← hmax]
    exact hK
  · omega

/-! ## The shape of `f` on `I_1, …, I_n` -/

private lemma ord_sign {g : ℝ → ℝ} {a b : ℝ} (hc : ContinuousOn g (Set.Ioo a b))
    (hne : ∀ x ∈ Set.Ioo a b, g x ≠ 0) {y z : ℝ} (hy : y ∈ Set.Ioo a b) (hz : z ∈ Set.Ioo a b)
    (hgy : 0 < g y) : 0 < g z := by
  by_contra h
  have hz' : g z < 0 := lt_of_le_of_ne (not_lt.1 h) (hne z hz)
  obtain ⟨w, hw, hw0⟩ := isPreconnected_Ioo.intermediate_value hz hy hc ⟨hz'.le, hgy.le⟩
  exact hne w hw hw0

/-- If `g → +∞` at the left end of an interval on which `g'` has no zero, then `g' < 0`. -/
private lemma ord_neg_of_atTop_left {g g' : ℝ → ℝ} {a b : ℝ}
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
    exact ord_sign hc hne hx hz hpos
  obtain ⟨z, h1, h2⟩ := ((hlim.eventually (eventually_gt_atTop (g x))).and
    (Ioo_mem_nhdsGT hx.1)).exists
  have := hmono ⟨h2.1, h2.2.trans hx.2⟩ hx h2.2
  linarith

/-- If `g → +∞` at the right end of an interval on which `g'` has no zero, then `g' > 0`. -/
private lemma ord_pos_of_atTop_right {g g' : ℝ → ℝ} {a b : ℝ}
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
    have := ord_sign (g := fun x => -g' x) hc.neg (fun x hx h => hne x hx (neg_eq_zero.1 h))
      hx hz (neg_pos.2 hneg)
    linarith
  obtain ⟨z, h1, h2⟩ := ((hlim.eventually (eventually_gt_atTop (g x))).and
    (Ioo_mem_nhdsLT hx.2)).exists
  have := hanti hx ⟨hx.1.trans h2.1, h2.2⟩ h2.1
  linarith

private lemma ord_hasDerivAt_K (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i)
    (hS : (posVals σ).Nonempty) {s : ℝ} (hs : s ∈ posVals σ) {x : ℝ} (hx : ordK σ s x) :
    HasDerivAt (fR N σ) (fR1 N σ x) x ∧ HasDerivAt (fR1 N σ) (fR2 N σ x) x := by
  obtain ⟨h0, h1⟩ := ord_K_good σ hS hs hx
  exact ⟨hasDerivAt_fR N σ h0 (ord_nonpole_all σ hσ h1),
    hasDerivAt_fR1 N σ h0 (ord_nonpole_all σ hσ h1)⟩

private lemma ord_contOn_K (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i)
    (hS : (posVals σ).Nonempty) {s : ℝ} (hs : s ∈ posVals σ) {a b : ℝ}
    (h : ∀ x ∈ Set.Ioo a b, ordK σ s x) : ContinuousOn (fR1 N σ) (Set.Ioo a b) :=
  fun x hx => (ord_hasDerivAt_K N σ hσ hS hs (h x hx)).2.continuousAt.continuousWithinAt

private lemma ord_tendsto_fR_pole (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    {s : ℝ} (hs : s ∈ posVals σ) : Tendsto (fR N σ) (𝓝[>] (-s⁻¹)) atTop := by
  rw [ord_fR_eq N σ hσ]
  exact (ord_tendsto_pole N σ hN hs one_pos).1

/-- Lemma 2.4–2.5: in `I_l`, `l ≥ 2`, with two distinct critical points `c < d`, `f' > 0` on
`(c, d)`, so `f(c) < f(d)`. -/
private lemma ord_pair_lt (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {s : ℝ} (hs : s ∈ posVals σ)
    (hcard : Multiset.card ((innerCrit N σ).filter (ordK σ s)) ≤ 2) {c d : ℝ}
    (hc : ordK σ s c) (hd : ordK σ s d) (hcd : c < d) (hfc : fR1 N σ c = 0)
    (hfd : fR1 N σ d = 0) : fR N σ c < fR N σ d := by
  have hcm : c ∈ (innerCrit N σ).filter (ordK σ s) :=
    Multiset.mem_filter.2 ⟨ord_mem_innerCrit_of N σ hσ hS hs hc hfc, hc⟩
  have hdm : d ∈ (innerCrit N σ).filter (ordK σ s) :=
    Multiset.mem_filter.2 ⟨ord_mem_innerCrit_of N σ hσ hS hs hd hfd, hd⟩
  have honly : ∀ z, ordK σ s z → fR1 N σ z = 0 → z = c ∨ z = d := by
    intro z hz hfz
    by_contra h
    rw [not_or] at h
    have hzm : z ∈ (innerCrit N σ).filter (ordK σ s) :=
      Multiset.mem_filter.2 ⟨ord_mem_innerCrit_of N σ hσ hS hs hz hfz, hz⟩
    have hsum := ord_sum_count_le ((innerCrit N σ).filter (ordK σ s)) {c, d, z}
    rw [Finset.sum_insert (by simp [hcd.ne, Ne.symm h.1]), Finset.sum_pair (Ne.symm h.2)]
      at hsum
    have := Multiset.count_pos.2 hcm
    have := Multiset.count_pos.2 hdm
    have := Multiset.count_pos.2 hzm
    omega
  have hcount : (innerCrit N σ).count c = 1 := by
    have hsum := ord_sum_count_le ((innerCrit N σ).filter (ordK σ s)) {c, d}
    rw [Finset.sum_pair hcd.ne] at hsum
    have h1 := Multiset.count_pos.2 hcm
    have h2 := Multiset.count_pos.2 hdm
    rw [Multiset.count_filter_of_pos hc] at h1 hsum
    omega
  obtain ⟨hc0, hcp⟩ := ord_K_good σ hS hs hc
  have hf2 : fR2 N σ c ≠ 0 := by
    intro h
    have hin : InInner σ c := ⟨(ord_K_sign σ hS hs hc).1, s, hs, (ord_lt_iff
      (ord_pos_of_mem σ hs)).1 hc.1⟩
    have := count_innerCrit N σ hσ hN hin hcp
    rw [ite_eq_left hfc, ite_eq_left h] at this
    omega
  have hKleft : ∀ x ∈ Set.Ioo (-s⁻¹) c, ordK σ s x := fun x hx => ⟨hx.1, hx.2.trans hc.2⟩
  have hleft : ∀ x ∈ Set.Ioo (-s⁻¹) c, fR1 N σ x < 0 :=
    ord_neg_of_atTop_left (fun x hx => (ord_hasDerivAt_K N σ hσ hS hs (hKleft x hx)).1)
      (ord_contOn_K N σ hσ hS hs hKleft)
      (fun x hx h0 => by rcases honly x (hKleft x hx) h0 with h | h <;> linarith [hx.2])
      (ord_tendsto_fR_pole N σ hσ hN hs)
  have hd2c := (ord_hasDerivAt_K N σ hσ hS hs hc).2
  have hf2pos : 0 < fR2 N σ c := by
    rcases lt_or_gt_of_ne hf2 with h | h
    · exfalso
      obtain ⟨y, hy, hyv⟩ := ord_deriv_left hd2c.neg (neg_pos.2 h) hc.1
      have := hleft y hy
      simp only [Pi.neg_apply, hfc] at hyv
      linarith
    · exact h
  obtain ⟨y, hy, hyv⟩ := ord_deriv_right hd2c hf2pos hcd
  rw [hfc] at hyv
  have hKcd : ∀ x ∈ Set.Ioo c d, ordK σ s x := fun x hx => ⟨hc.1.trans hx.1, hx.2.trans hd.2⟩
  have hmid : ∀ x ∈ Set.Ioo c d, 0 < fR1 N σ x := fun x hx =>
    ord_sign (ord_contOn_K N σ hσ hS hs hKcd)
      (fun z hz h0 => by rcases honly z (hKcd z hz) h0 with h | h <;> linarith [hz.1, hz.2])
      hy hx hyv
  have hmono : StrictMonoOn (fR N σ) (Set.Icc c d) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc c d) (fun x hx =>
      (ord_hasDerivAt_K N σ hσ hS hs ⟨lt_of_lt_of_le hc.1 hx.1,
        lt_of_le_of_lt hx.2 hd.2⟩).1.continuousAt.continuousWithinAt) fun x hx => ?_
    rw [interior_Icc] at hx
    rw [(ord_hasDerivAt_K N σ hσ hS hs (hKcd x hx)).1.deriv]
    exact hmid x hx
  exact hmono ⟨le_rfl, hcd.le⟩ ⟨hcd.le, le_rfl⟩ hcd

/-- The pairs `x_{2j} ≥ x_{2j+1}` lie in one `I_l`, `l ≥ 2`; either they are distinct and
`f(x_{2j+1}) < f(x_{2j})`, or they coincide and `f'' = 0` there. -/
private lemma ord_pair (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {j : ℕ} (hj : 1 ≤ j) (hj' : 2 * j + 1 < 2 * numBands N σ) :
    ∃ s ∈ posVals σ, s ≠ (posVals σ).max' hS ∧ ordK σ s (xCrit N σ (2 * j)) ∧
      ordK σ s (xCrit N σ (2 * j + 1)) ∧ ordA N σ (ordR σ s) = 2 * j - 1 ∧
      ((xCrit N σ (2 * j + 1) < xCrit N σ (2 * j) ∧
          fR N σ (xCrit N σ (2 * j + 1)) < fR N σ (xCrit N σ (2 * j))) ∨
        (xCrit N σ (2 * j + 1) = xCrit N σ (2 * j) ∧ fR2 N σ (xCrit N σ (2 * j)) = 0)) := by
  obtain ⟨hmem, -⟩ := ord_xCrit_spec N σ hσ hN hS (k := 2 * j) (by omega) (by omega)
  obtain ⟨hmem', -⟩ := ord_xCrit_spec N σ hσ hN hS (k := 2 * j + 1) (by omega) hj'
  obtain ⟨s, hs, hK⟩ := ord_mem_K N σ hσ hN hS hmem
  have hb := (ord_block N σ hσ hN hS hs (k := 2 * j) (by omega) (by omega)).1 hK
  have hsplit := ord_A_split N σ hσ hN hS hs
  rcases ord_lo N σ hσ hN hS hs with ⟨-, hlo, hcard⟩ | ⟨hmax, ⟨c, hc⟩, hcard⟩
  · exfalso
    omega
  rcases hcard with hcard | hcard
  · exfalso
    omega
  have hlo : ordA N σ (ordR σ s) = 2 * j - 1 := by omega
  have hK' : ordK σ s (xCrit N σ (2 * j + 1)) :=
    (ord_block N σ hσ hN hS hs (k := 2 * j + 1) (by omega) hj').2 ⟨by omega, by omega⟩
  refine ⟨s, hs, hmax, hK, hK', hlo, ?_⟩
  have hle := ord_xCrit_anti N σ hσ hN hS (k := 2 * j) (k' := 2 * j + 1) (by omega) (by omega) hj'
  have hf1 := (ord_mem_innerCrit N σ hσ hN hmem).2.2
  have hf1' := (ord_mem_innerCrit N σ hσ hN hmem').2.2
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact Or.inl ⟨hlt, ord_pair_lt N σ hσ hN hS hs hcard.le hK' hK hlt hf1' hf1⟩
  · refine Or.inr ⟨heq, ?_⟩
    obtain ⟨hin, hnp, -⟩ := ord_mem_innerCrit N σ hσ hN hmem
    by_contra hf2
    have hcount : (innerCrit N σ).count (xCrit N σ (2 * j)) = 1 := by
      rw [count_innerCrit N σ hσ hN hin hnp, ite_eq_left hf1, ite_eq_right hf2]
    have hcm' : ((innerCrit N σ).filter (ordK σ s)).count (xCrit N σ (2 * j)) = 1 := by
      rw [Multiset.count_filter_of_pos hK]
      exact hcount
    obtain ⟨d, hdm, hdc⟩ : ∃ d ∈ (innerCrit N σ).filter (ordK σ s), d ≠ xCrit N σ (2 * j) := by
      by_contra h
      have h' : ∀ b ∈ (innerCrit N σ).filter (ordK σ s), b = xCrit N σ (2 * j) :=
        fun b hb => by
          by_contra hb'
          exact h ⟨b, hb, hb'⟩
      have := Multiset.eq_replicate_of_mem h'
      rw [hcard] at this
      rw [this, Multiset.count_replicate_self] at hcm'
      omega
    obtain ⟨hdm0, hdK⟩ := Multiset.mem_filter.1 hdm
    obtain ⟨k, hk1, hk, hxk⟩ := ord_xCrit_surj N σ hσ hN hS hdm0
    have hbk := (ord_block N σ hσ hN hS hs hk1 hk).1 (hxk ▸ hdK)
    have : k = 2 * j ∨ k = 2 * j + 1 := by omega
    rcases this with rfl | rfl
    · exact hdc hxk.symm
    · exact hdc (hxk.symm.trans heq)

/-- `x_1` minimizes `f` on `I_1`. -/
private lemma ord_first_min (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {x₀ : ℝ} (hx₀ : ordK σ ((posVals σ).max' hS) x₀) :
    fR N σ (xCrit N σ 1) ≤ fR N σ x₀ := by
  have hp := (card_innerCrit N σ hσ hN hS).2
  have hm := (posVals σ).max'_mem hS
  have hc := ord_first N σ hσ hN hS
  obtain ⟨hmem, -⟩ := ord_xCrit_spec N σ hσ hN hS le_rfl (by omega)
  have hfc := (ord_mem_innerCrit N σ hσ hN hmem).2.2
  have hcm : xCrit N σ 1 ∈ (innerCrit N σ).filter (ordK σ ((posVals σ).max' hS)) :=
    Multiset.mem_filter.2 ⟨hmem, hc⟩
  have hcard := ord_card_K_max N σ hσ hN hS
  have honly : ∀ z, ordK σ ((posVals σ).max' hS) z → fR1 N σ z = 0 → z = xCrit N σ 1 := by
    intro z hz hfz
    by_contra h
    have hzm : z ∈ (innerCrit N σ).filter (ordK σ ((posVals σ).max' hS)) :=
      Multiset.mem_filter.2 ⟨ord_mem_innerCrit_of N σ hσ hS hm hz hfz, hz⟩
    have hsum := ord_sum_count_le ((innerCrit N σ).filter (ordK σ ((posVals σ).max' hS)))
      {xCrit N σ 1, z}
    rw [Finset.sum_pair (Ne.symm h)] at hsum
    have := Multiset.count_pos.2 hcm
    have := Multiset.count_pos.2 hzm
    omega
  have hR := ord_R_max σ hS
  set c := xCrit N σ 1 with hcdef
  have hKleft : ∀ x ∈ Set.Ioo (-((posVals σ).max' hS)⁻¹) c, ordK σ ((posVals σ).max' hS) x :=
    fun x hx => ⟨hx.1, hx.2.trans hc.2⟩
  have hKright : ∀ x ∈ Set.Ioo c 0, ordK σ ((posVals σ).max' hS) x :=
    fun x hx => ⟨hc.1.trans hx.1, by rw [hR]; exact hx.2⟩
  have hleft : ∀ x ∈ Set.Ioo (-((posVals σ).max' hS)⁻¹) c, fR1 N σ x < 0 :=
    ord_neg_of_atTop_left (fun x hx => (ord_hasDerivAt_K N σ hσ hS hm (hKleft x hx)).1)
      (ord_contOn_K N σ hσ hS hm hKleft)
      (fun x hx h0 => by have := honly x (hKleft x hx) h0; linarith [hx.2])
      (ord_tendsto_fR_pole N σ hσ hN hm)
  have hright : ∀ x ∈ Set.Ioo c 0, 0 < fR1 N σ x :=
    ord_pos_of_atTop_right (fun x hx => (ord_hasDerivAt_K N σ hσ hS hm (hKright x hx)).1)
      (ord_contOn_K N σ hσ hS hm hKright)
      (fun x hx h0 => by have := honly x (hKright x hx) h0; linarith [hx.1])
      (by rw [ord_fR_eq N σ hσ]; exact ord_tendsto_zero N σ 1)
  have hx₀0 : x₀ < 0 := by
    have := hx₀.2
    rwa [hR] at this
  rcases lt_trichotomy x₀ c with h | h | h
  · have hanti : StrictAntiOn (fR N σ) (Set.Icc x₀ c) := by
      refine strictAntiOn_of_deriv_neg (convex_Icc x₀ c) (fun x hx =>
        (ord_hasDerivAt_K N σ hσ hS hm ⟨lt_of_lt_of_le hx₀.1 hx.1,
          lt_of_le_of_lt hx.2 hc.2⟩).1.continuousAt.continuousWithinAt) fun x hx => ?_
      rw [interior_Icc] at hx
      have hx' : x ∈ Set.Ioo (-((posVals σ).max' hS)⁻¹) c := ⟨hx₀.1.trans hx.1, hx.2⟩
      rw [(ord_hasDerivAt_K N σ hσ hS hm (hKleft x hx')).1.deriv]
      exact hleft x hx'
    exact (hanti ⟨le_rfl, h.le⟩ ⟨h.le, le_rfl⟩ h).le
  · rw [h]
  · have hmono : StrictMonoOn (fR N σ) (Set.Icc c x₀) := by
      refine strictMonoOn_of_deriv_pos (convex_Icc c x₀) (fun x hx =>
        (ord_hasDerivAt_K N σ hσ hS hm ⟨lt_of_lt_of_le hc.1 hx.1,
          lt_of_le_of_lt hx.2 hx₀.2⟩).1.continuousAt.continuousWithinAt) fun x hx => ?_
      rw [interior_Icc] at hx
      have hx' : x ∈ Set.Ioo c 0 := ⟨hx.1, hx.2.trans hx₀0⟩
      rw [(ord_hasDerivAt_K N σ hσ hS hm (hKright x hx')).1.deriv]
      exact hright x hx'
    exact (hmono ⟨le_rfl, h.le⟩ ⟨h.le, le_rfl⟩ h).le

/-! ## The chart of `I_0` -/

/-- At the critical point `y` of `F` in the chart, `F(y) = y² Σ_s r_s s / (y + s)² ≥ 0`. -/
private lemma ord_FChart_nonneg (N : ℕ) (σ : Fin M → ℝ) {y : ℝ} (hy : InChart σ y)
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
  have := ord_pos_of_mem σ hs
  have hw : 0 ≤ weight N σ s := by unfold weight; positivity
  positivity

/-- `f'(1/y) = -y² F'(y)`. -/
private lemma ord_fR1_inv (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {y : ℝ} (hy0 : y ≠ 0)
    (hy : InChart σ y) : fR1 N σ y⁻¹ = -(y ^ 2) * FChart1 N σ y := by
  rw [ord_fR1_eq N σ hσ, ordF1, ordH, FChart1, one_mul]
  have hterm : ∀ s ∈ posVals σ, weight N σ s * s ^ 2 / (1 + s * y⁻¹) ^ 2 =
      y ^ 2 * (weight N σ s * s ^ 2 / (y + s) ^ 2) := by
    intro s hs
    have := (hy s hs).ne'
    have e : 1 + s * y⁻¹ = (y + s) / y := by field_simp
    rw [e]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, inv_pow, inv_inv]
  ring

private lemma ord_I0_inv (σ : Fin M → ℝ) {y : ℝ} (hy0 : y ≠ 0) (hy : InChart σ y) :
    ordI0 σ y⁻¹ := by
  rcases lt_or_gt_of_ne hy0 with h | h
  · right
    intro s hs
    have e : 1 + s * y⁻¹ = (y + s) / y := by field_simp
    rw [e]
    exact div_neg_of_pos_of_neg (hy s hs) h
  · left
    exact inv_pos.2 h

/-- For `φ π((0, ∞)) ≤ 1`, `f' ≥ 0` on `(0, ∞)`. -/
private lemma ord_fR1_nonneg_pos (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i)
    (hR : massRatio N σ ≤ 1) {x : ℝ} (hx : 0 < x) : 0 ≤ fR1 N σ x := by
  rw [ord_fR1_eq N σ hσ, ordF1, ordH, one_mul]
  have hle : ∑ s ∈ posVals σ, weight N σ s * s ^ 2 / (1 + s * x) ^ 2 ≤
      ∑ s ∈ posVals σ, weight N σ s * (x ^ 2)⁻¹ := by
    refine Finset.sum_le_sum fun s hs => ?_
    have hs0 := ord_pos_of_mem σ hs
    have hw : 0 ≤ weight N σ s := by unfold weight; positivity
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hw
    have hpos : 0 < (1 + s * x) ^ 2 := by positivity
    rw [div_le_iff₀ hpos, inv_mul_eq_div, le_div_iff₀ (by positivity)]
    nlinarith [mul_pos hs0 hx]
  rw [← Finset.sum_mul, sum_weight] at hle
  have hx2 : 0 < (x ^ 2)⁻¹ := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hR hx2.le]

private lemma ord_fR_ge (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {x : ℝ} (hx : 0 < x) :
    -x⁻¹ ≤ fR N σ x := by
  rw [ord_fR_eq N σ hσ, ordF, ordG, one_mul]
  have : 0 ≤ ∑ s ∈ posVals σ, weight N σ s * s / (1 + s * x) := by
    refine Finset.sum_nonneg fun s hs => ?_
    have := ord_pos_of_mem σ hs
    have hw : 0 ≤ weight N σ s := by unfold weight; positivity
    positivity
  linarith

/-! ## Root counts at a critical value -/

/-- The roots of `f = a_i`, `i` odd, in the interval `I_l` of `x_i`, with multiplicity: at
least `2` in `I_1` and at least `3` in `I_l`, `l ≥ 2`. -/
private lemma ord_strict_left (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {i : ℕ} (hi : Odd i) (hip : i < 2 * numBands N σ) :
    ∃ s ∈ posVals σ, ordK σ s (xCrit N σ i) ∧ ∃ T : Finset ℝ, (∀ x ∈ T, ordK σ s x) ∧
      (if s = (posVals σ).max' hS then 0 else 1) + 2 ≤
        ∑ x ∈ T, (ordP N σ 1 (fR N σ (xCrit N σ i))).rootMultiplicity x := by
  obtain ⟨j, rfl⟩ := hi
  obtain ⟨hmem, -⟩ := ord_xCrit_spec N σ hσ hN hS (k := 2 * j + 1) (by omega) hip
  have hf1 := (ord_mem_innerCrit N σ hσ hN hmem).2.2
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    have hm := (posVals σ).max'_mem hS
    have hK := ord_first N σ hσ hN hS
    refine ⟨_, hm, hK, {xCrit N σ (2 * 0 + 1)}, by simpa using hK, ?_⟩
    obtain ⟨h0, hp'⟩ := ord_K_good σ hS hm hK
    rw [ite_eq_left rfl, Finset.sum_singleton]
    exact (ord_mult_crit N σ hσ _ h0 hp' rfl hf1).1
  · obtain ⟨s, hs, hmax, hK1, hK2, -, hcase⟩ := ord_pair N σ hσ hN hS (j := j) hj hip
    obtain ⟨h0, hp'⟩ := ord_K_good σ hS hs hK2
    have hm2 := ord_mult_crit N σ hσ (fR N σ (xCrit N σ (2 * j + 1))) h0 hp' rfl hf1
    refine ⟨s, hs, hK2, ?_⟩
    rw [ite_eq_right hmax]
    rcases hcase with ⟨hlt, hflt⟩ | ⟨heq, hf2⟩
    · obtain ⟨r, hr1, hr2, hrE⟩ := ord_root_right N σ hN hS one_pos hs hmax hK1
        (show fR N σ (xCrit N σ (2 * j + 1)) < ordF N σ 1 (xCrit N σ (2 * j)) by
          rw [← ord_fR_eq N σ hσ]; exact hflt)
      have hrK : ordK σ s r := ⟨hK1.1.trans hr1, hr2⟩
      obtain ⟨hr0, hrp⟩ := ord_K_good σ hS hs hrK
      have hne : xCrit N σ (2 * j + 1) ≠ r := (hlt.trans hr1).ne
      refine ⟨{xCrit N σ (2 * j + 1), r}, ?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hK2
        · exact hrK
      · rw [Finset.sum_pair hne]
        have := ord_mult_one N σ 1 _ hr0 hrp hrE
        omega
    · refine ⟨{xCrit N σ (2 * j + 1)}, by simpa using hK2, ?_⟩
      rw [Finset.sum_singleton]
      exact hm2.2 (by rw [heq]; exact hf2)

/-- The roots of `f = a_{2j}`, `2j < 2p`, in the interval `I_l` of `x_{2j}`, with
multiplicity: at least `3`. -/
private lemma ord_strict_right (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {j : ℕ} (hj : 1 ≤ j) (hj' : 2 * j + 1 < 2 * numBands N σ) :
    ∃ s ∈ posVals σ, s ≠ (posVals σ).max' hS ∧ ordK σ s (xCrit N σ (2 * j)) ∧
      ordA N σ (ordR σ s) = 2 * j - 1 ∧ ∃ T : Finset ℝ, (∀ x ∈ T, ordK σ s x) ∧
        1 + 2 ≤ ∑ x ∈ T, (ordP N σ 1 (fR N σ (xCrit N σ (2 * j)))).rootMultiplicity x := by
  obtain ⟨hmem, -⟩ := ord_xCrit_spec N σ hσ hN hS (k := 2 * j) (by omega) (by omega)
  have hf1 := (ord_mem_innerCrit N σ hσ hN hmem).2.2
  obtain ⟨s, hs, hmax, hK1, hK2, hlo, hcase⟩ := ord_pair N σ hσ hN hS (j := j) hj hj'
  obtain ⟨h0, hp'⟩ := ord_K_good σ hS hs hK1
  have hm2 := ord_mult_crit N σ hσ (fR N σ (xCrit N σ (2 * j))) h0 hp' rfl hf1
  refine ⟨s, hs, hmax, hK1, hlo, ?_⟩
  rcases hcase with ⟨hlt, hflt⟩ | ⟨heq, hf2⟩
  · obtain ⟨r, hr1, hr2, hrE⟩ := ord_root_left N σ hN hS one_pos hs hK2
      (show ordF N σ 1 (xCrit N σ (2 * j + 1)) < fR N σ (xCrit N σ (2 * j)) by
        rw [← ord_fR_eq N σ hσ]; exact hflt)
    have hrK : ordK σ s r := ⟨hr1, hr2.trans hK2.2⟩
    obtain ⟨hr0, hrp⟩ := ord_K_good σ hS hs hrK
    have hne : r ≠ xCrit N σ (2 * j) := (hr2.trans hlt).ne
    refine ⟨{r, xCrit N σ (2 * j)}, ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hrK
      · exact hK1
    · rw [Finset.sum_pair hne]
      have := ord_mult_one N σ 1 _ hr0 hrp hrE
      omega
  · refine ⟨{xCrit N σ (2 * j)}, by simpa using hK1, ?_⟩
    rw [Finset.sum_singleton]
    exact hm2.2 hf2

/-- A level `E` of `f` with roots of total multiplicity `≥ 2` beyond the default in one interval
`I_l`, and either the same in a second interval, or `≥ 2` in `I_0`, or `E = 0`, exceeds the
root budget of `P_E`. -/
private lemma ord_count_one (N : ℕ) (σ : Fin M → ℝ) (hN : 0 < N) (hS : (posVals σ).Nonempty)
    (E : ℝ) {s : ℝ} (hs : s ∈ posVals σ) (T1 : Finset ℝ) (hT1 : ∀ x ∈ T1, ordK σ s x)
    (hc1 : (if s = (posVals σ).max' hS then 0 else 1) + 2 ≤
      ∑ x ∈ T1, (ordP N σ 1 E).rootMultiplicity x)
    (hext : (∃ s' ∈ posVals σ, s' ≠ s ∧ ∃ T2 : Finset ℝ, (∀ x ∈ T2, ordK σ s' x) ∧
        (if s' = (posVals σ).max' hS then 0 else 1) + 2 ≤
          ∑ x ∈ T2, (ordP N σ 1 E).rootMultiplicity x) ∨
      (∃ B : Finset ℝ, (∀ x ∈ B, ordI0 σ x) ∧ 2 ≤ ∑ x ∈ B, (ordP N σ 1 E).rootMultiplicity x) ∨
      E = 0) : False := by
  have hdef : ∀ u ∈ posVals σ, u ≠ (posVals σ).max' hS → ∃ r, ordK σ u r ∧ ordF N σ 1 r = E :=
    fun u hu hne => ord_root_default N σ hN hS one_pos E hu hne
  choose! rd hrd using hdef
  have hrdμ : ∀ u ∈ posVals σ, u ≠ (posVals σ).max' hS →
      1 ≤ (ordP N σ 1 E).rootMultiplicity (rd u) := by
    intro u hu hne
    obtain ⟨h0, h1⟩ := ord_K_good σ hS hu (hrd u hu hne).1
    exact ord_mult_one N σ 1 E h0 h1 (hrd u hu hne).2
  have hdeg := ord_natDegree_P N σ 1 E
  have hcard1 : 1 ≤ (posVals σ).card := Finset.card_pos.2 hS
  rcases hext with ⟨s', hs', hss', T2, hT2, hc2⟩ | ⟨B, hB, hcB⟩ | hE0
  · let A : ℝ → Finset ℝ := fun u => if u = s then T1 else if u = s' then T2 else
      if u = (posVals σ).max' hS then ∅ else {rd u}
    have hA : ∀ u ∈ posVals σ, ∀ x ∈ A u, ordK σ u x := by
      intro u hu x hx
      simp only [A] at hx
      split_ifs at hx with h1 h2 h3
      · subst h1; exact hT1 x hx
      · subst h2; exact hT2 x hx
      · simp at hx
      · rw [Finset.mem_singleton] at hx
        subst hx
        exact (hrd u hu h3).1
    have hcount := ord_count N σ hS 1 E A hA ∅ (by simp)
    have hlb := ord_sum_lb (posVals σ) hS
      (fun u => ∑ x ∈ A u, (ordP N σ 1 E).rootMultiplicity x)
      (fun u => (if u = s then 2 else 0) + (if u = s' then 2 else 0)) (by
        intro u hu
        simp only [A]
        by_cases h1 : u = s
        · subst h1
          rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_right hss'.symm]
          simpa using hc1
        · by_cases h2 : u = s'
          · subst h2
            rw [ite_eq_right h1, ite_eq_left rfl, ite_eq_right h1, ite_eq_left rfl]
            simpa using hc2
          · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h1, ite_eq_right h2]
            by_cases h3 : u = (posVals σ).max' hS
            · simp [h3]
            · simpa [h3] using hrdμ u hu h3)
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq', ite_eq_left hs,
      ite_eq_left hs'] at hlb
    simp only [Finset.sum_empty, add_zero] at hcount
    have := hdeg.1
    omega
  · let A : ℝ → Finset ℝ := fun u => if u = s then T1 else
      if u = (posVals σ).max' hS then ∅ else {rd u}
    have hA : ∀ u ∈ posVals σ, ∀ x ∈ A u, ordK σ u x := by
      intro u hu x hx
      simp only [A] at hx
      split_ifs at hx with h1 h3
      · subst h1; exact hT1 x hx
      · simp at hx
      · rw [Finset.mem_singleton] at hx
        subst hx
        exact (hrd u hu h3).1
    have hcount := ord_count N σ hS 1 E A hA B hB
    have hlb := ord_sum_lb (posVals σ) hS
      (fun u => ∑ x ∈ A u, (ordP N σ 1 E).rootMultiplicity x)
      (fun u => if u = s then 2 else 0) (by
        intro u hu
        simp only [A]
        by_cases h1 : u = s
        · subst h1
          rw [ite_eq_left rfl, ite_eq_left rfl]
          exact hc1
        · rw [ite_eq_right h1, ite_eq_right h1]
          by_cases h3 : u = (posVals σ).max' hS
          · simp [h3]
          · simpa [h3] using hrdμ u hu h3)
    rw [Finset.sum_ite_eq', ite_eq_left hs] at hlb
    have := hdeg.1
    omega
  · let A : ℝ → Finset ℝ := fun u => if u = s then T1 else
      if u = (posVals σ).max' hS then ∅ else {rd u}
    have hA : ∀ u ∈ posVals σ, ∀ x ∈ A u, ordK σ u x := by
      intro u hu x hx
      simp only [A] at hx
      split_ifs at hx with h1 h3
      · subst h1; exact hT1 x hx
      · simp at hx
      · rw [Finset.mem_singleton] at hx
        subst hx
        exact (hrd u hu h3).1
    have hcount := ord_count N σ hS 1 E A hA ∅ (by simp)
    have hlb := ord_sum_lb (posVals σ) hS
      (fun u => ∑ x ∈ A u, (ordP N σ 1 E).rootMultiplicity x)
      (fun u => if u = s then 2 else 0) (by
        intro u hu
        simp only [A]
        by_cases h1 : u = s
        · subst h1
          rw [ite_eq_left rfl, ite_eq_left rfl]
          exact hc1
        · rw [ite_eq_right h1, ite_eq_right h1]
          by_cases h3 : u = (posVals σ).max' hS
          · simp [h3]
          · simpa [h3] using hrdμ u hu h3)
    rw [Finset.sum_ite_eq', ite_eq_left hs] at hlb
    simp only [Finset.sum_empty, add_zero] at hcount
    have := hdeg.2 hE0
    omega

/-! ## Lemma 2.5 -/

private lemma ord_edgeVal_ne (N : ℕ) (σ : Fin M → ℝ) {k : ℕ} (hk : k ≠ 2 * numBands N σ) :
    edgeVal N σ k = fR N σ (xCrit N σ k) := by
  unfold edgeVal
  rw [ite_eq_right hk]

private lemma ord_edgeVal_last (N : ℕ) (σ : Fin M → ℝ) :
    edgeVal N σ (2 * numBands N σ) = FChart N σ (yEdge N σ) := by
  unfold edgeVal
  rw [ite_eq_left rfl]

/-- Lemma 2.5, `a_1 ≥ a_2 ≥ ⋯ ≥ a_{2p}`. -/
theorem edgeVal_succ_le (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {k : ℕ} (hk₁ : 1 ≤ k) (hk : k < 2 * numBands N σ) :
    edgeVal N σ (k + 1) ≤ edgeVal N σ k := by
  have hp := card_innerCrit N σ hσ hN hS
  by_cases hlast : k + 1 = 2 * numBands N σ
  · rw [hlast, ord_edgeVal_last, ord_edgeVal_ne N σ (by omega : k ≠ 2 * numBands N σ)]
    obtain ⟨hmem, -⟩ := ord_xCrit_spec N σ hσ hN hS hk₁ hk
    have hf1 := (ord_mem_innerCrit N σ hσ hN hmem).2.2
    obtain ⟨s, hs, hK⟩ := ord_mem_K N σ hσ hN hS hmem
    obtain ⟨hyC, hyF⟩ := yEdge_spec N σ hσ hN hS
    by_cases hy0 : yEdge N σ = 0
    · rw [hy0, show FChart N σ 0 = 0 by simp [FChart]]
      have hR : massRatio N σ = 1 := (yEdge_eq_zero_iff N σ hσ hN hS).1 hy0
      by_contra hneg
      rw [not_le] at hneg
      have hξ' : 0 < -2 / fR N σ (xCrit N σ k) := div_pos_of_neg_of_neg (by norm_num) hneg
      have h1 := ord_interp N σ hσ hN hS hs hK hf1.ge
        (ord_fR1_nonneg_pos N σ hσ hR.le hξ') (Or.inr (Or.inl hξ'))
      have h2 := ord_fR_ge N σ hσ hξ'
      have e : -(-2 / fR N σ (xCrit N σ k))⁻¹ = fR N σ (xCrit N σ k) / 2 := by
        rw [inv_div]
        ring
      rw [e] at h2
      linarith
    · rw [← fR_inv_eq_FChart N σ hσ hy0]
      exact ord_interp N σ hσ hN hS hs hK hf1.ge
        (by rw [ord_fR1_inv N σ hσ hy0 hyC, hyF, mul_zero]) (Or.inr (ord_I0_inv σ hy0 hyC))
  · have hk' : k + 1 < 2 * numBands N σ := by omega
    rw [ord_edgeVal_ne N σ (by omega : k + 1 ≠ 2 * numBands N σ),
      ord_edgeVal_ne N σ (by omega : k ≠ 2 * numBands N σ)]
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · obtain ⟨s, hs, -, hK1, hK2, -, hcase⟩ :=
        ord_pair N σ hσ hN hS (j := j) (by omega) (by omega)
      have e : k = 2 * j := by omega
      subst e
      rcases hcase with ⟨-, h⟩ | ⟨h, -⟩
      · exact h.le
      · rw [h]
    · obtain ⟨s, hs, -, hK1, -, hlo, -⟩ :=
        ord_pair N σ hσ hN hS (j := j + 1) (by omega) (by omega)
      have e : k + 1 = 2 * (j + 1) := by omega
      obtain ⟨hmem, hspec⟩ := ord_xCrit_spec N σ hσ hN hS hk₁ hk
      have hf1 := (ord_mem_innerCrit N σ hσ hN hmem).2.2
      obtain ⟨s'', hs'', hK''⟩ := ord_mem_K N σ hσ hN hS hmem
      obtain ⟨hmem', -⟩ := ord_xCrit_spec N σ hσ hN hS (k := k + 1) (by omega) hk'
      have hf1' := (ord_mem_innerCrit N σ hσ hN hmem').2.2
      have hlt : ordR σ s < xCrit N σ k := (hspec (ordR σ s)).2 (by omega)
      have hne : s ≠ s'' := by
        rintro rfl
        have := (ord_block N σ hσ hN hS hs hk₁ hk).1 hK''
        omega
      rw [e] at hf1' ⊢
      exact ord_interp N σ hσ hN hS hs'' hK'' hf1.ge hf1'.ge
        (Or.inl ⟨s, hs, hne, hK1, hK1.2.trans hlt⟩)

/-- The bands are nondegenerate: `a_{2k} < a_{2k-1}`. -/
theorem edgeVal_band_lt (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {k : ℕ} (hk₁ : 1 ≤ k) (hk : k ≤ numBands N σ) :
    edgeVal N σ (2 * k) < edgeVal N σ (2 * k - 1) := by
  have hp := card_innerCrit N σ hσ hN hS
  have hle : edgeVal N σ (2 * k) ≤ edgeVal N σ (2 * k - 1) := by
    have := edgeVal_succ_le N σ hσ hN hS (k := 2 * k - 1) (by omega) (by omega)
    rwa [show 2 * k - 1 + 1 = 2 * k by omega] at this
  refine lt_of_le_of_ne hle fun heq => ?_
  have hodd : Odd (2 * k - 1) := ⟨k - 1, by omega⟩
  obtain ⟨s, hs, hK, T1, hT1, hc1⟩ := ord_strict_left N σ hσ hN hS hodd (by omega)
  rw [ord_edgeVal_ne N σ (by omega : 2 * k - 1 ≠ 2 * numBands N σ)] at heq
  refine ord_count_one N σ hN hS _ hs T1 hT1 hc1 ?_
  by_cases hkp : k = numBands N σ
  · have e : edgeVal N σ (2 * k) = FChart N σ (yEdge N σ) := by
      rw [show 2 * k = 2 * numBands N σ by omega, ord_edgeVal_last]
    rw [e] at heq
    obtain ⟨hyC, hyF⟩ := yEdge_spec N σ hσ hN hS
    by_cases hy0 : yEdge N σ = 0
    · right
      right
      rw [← heq, hy0]
      simp [FChart]
    · right
      left
      have hI := ord_I0_inv σ hy0 hyC
      refine ⟨{(yEdge N σ)⁻¹}, by simpa using hI, ?_⟩
      rw [Finset.sum_singleton]
      obtain ⟨h0, hp'⟩ := ord_I0_good σ hS hI
      exact (ord_mult_crit N σ hσ _ h0 hp' (by rw [fR_inv_eq_FChart N σ hσ hy0]; exact heq)
        (by rw [ord_fR1_inv N σ hσ hy0 hyC, hyF, mul_zero])).1
  · left
    obtain ⟨s', hs', hmax', hK', hlo', T2, hT2, hc2⟩ :=
      ord_strict_right N σ hσ hN hS (j := k) hk₁ (by omega)
    rw [ord_edgeVal_ne N σ (by omega : 2 * k ≠ 2 * numBands N σ)] at heq
    rw [heq] at hc2
    have hss' : s' ≠ s := by
      rintro rfl
      have := (ord_block N σ hσ hN hS hs (k := 2 * k - 1) (by omega) (by omega)).1 hK
      omega
    exact ⟨s', hs', hss', T2, hT2, by rw [ite_eq_right hmax']; exact hc2⟩

/-- Lemma 2.5, `a_k = f(x_k)` when `x_k` is finite. -/
theorem edgeVal_eq_fR (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {k : ℕ} (hk₁ : 1 ≤ k) (hk : k ≤ 2 * numBands N σ)
    (hfin : ¬ (k = 2 * numBands N σ ∧ yEdge N σ = 0)) :
    edgeVal N σ k = fR N σ (xCrit N σ k) := by
  by_cases h : k = 2 * numBands N σ
  · have hy0 : yEdge N σ ≠ 0 := fun h0 => hfin ⟨h, h0⟩
    unfold edgeVal xCrit
    rw [ite_eq_left h, ite_eq_left h, fR_inv_eq_FChart N σ hσ hy0]
  · exact ord_edgeVal_ne N σ h


/-- Lemma 2.5, `a_k ∈ [0, C]` under (phi_bounded) and (bound_Sigma), `C = 2τ⁻¹(1 + τ⁻¹)`. -/
theorem edgeVal_mem_Icc (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {τ : ℝ} (hτ : 0 < τ) (hφ₁ : τ ≤ phiRatio M N)
    (hφ₂ : phiRatio M N ≤ τ⁻¹) (hb : ∀ i, σ i ≤ τ⁻¹) {k : ℕ} (hk₁ : 1 ≤ k)
    (hk : k ≤ 2 * numBands N σ) : edgeVal N σ k ∈ Set.Icc 0 (2 * τ⁻¹ * (1 + τ⁻¹)) := by
  have hp := card_innerCrit N σ hσ hN hS
  have hchain : ∀ j k, 1 ≤ k → k + j ≤ 2 * numBands N σ → edgeVal N σ (k + j) ≤ edgeVal N σ k := by
    intro j
    induction j with
    | zero => intro k _ _; simp
    | succ j ih =>
      intro k hk1 hkj
      exact (edgeVal_succ_le N σ hσ hN hS (k := k + j) (by omega) (by omega)).trans
        (ih k hk1 (by omega))
  have hlow : edgeVal N σ (2 * numBands N σ) ≤ edgeVal N σ k := by
    have := hchain (2 * numBands N σ - k) k hk₁ (by omega)
    rwa [show k + (2 * numBands N σ - k) = 2 * numBands N σ by omega] at this
  have hup : edgeVal N σ k ≤ edgeVal N σ 1 := by
    have := hchain (k - 1) 1 le_rfl (by omega)
    rwa [show 1 + (k - 1) = k by omega] at this
  have h0 : 0 ≤ edgeVal N σ (2 * numBands N σ) := by
    rw [ord_edgeVal_last]
    obtain ⟨hyC, hyF⟩ := yEdge_spec N σ hσ hN hS
    exact ord_FChart_nonneg N σ hyC hyF
  have h1 : edgeVal N σ 1 ≤ 2 * τ⁻¹ * (1 + τ⁻¹) := by
    rw [ord_edgeVal_ne N σ (by omega : 1 ≠ 2 * numBands N σ)]
    have hm := (posVals σ).max'_mem hS
    have hm0 := ord_pos_of_mem σ hm
    have hx₀ : ordK σ ((posVals σ).max' hS) (-(2 * (posVals σ).max' hS)⁻¹) := by
      refine ⟨?_, ?_⟩
      · have : (2 * (posVals σ).max' hS)⁻¹ < ((posVals σ).max' hS)⁻¹ :=
          inv_strictAnti₀ hm0 (by linarith)
        linarith
      · rw [ord_R_max]
        have : 0 < (2 * (posVals σ).max' hS)⁻¹ := by positivity
        linarith
    refine (ord_first_min N σ hσ hN hS hx₀).trans ?_
    rw [ord_fR_eq N σ hσ, ordF, ordG, one_mul]
    have hterm : ∀ s ∈ posVals σ, weight N σ s * s / (1 + s * -(2 * (posVals σ).max' hS)⁻¹) ≤
        weight N σ s * (2 * (posVals σ).max' hS) := by
      intro s hs
      have hs0 := ord_pos_of_mem σ hs
      have hsle := (posVals σ).le_max' s hs
      have hw : 0 ≤ weight N σ s := by unfold weight; positivity
      have e : 1 + s * -(2 * (posVals σ).max' hS)⁻¹ = 1 - s / (2 * (posVals σ).max' hS) := by
        ring
      have hhalf : s / (2 * (posVals σ).max' hS) ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]
        linarith
      rw [e, mul_div_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hw
      rw [div_le_iff₀ (by linarith)]
      have : s / (2 * (posVals σ).max' hS) * (2 * (posVals σ).max' hS) = s := by
        field_simp
      nlinarith
    have hsum := Finset.sum_le_sum hterm
    rw [← Finset.sum_mul, sum_weight] at hsum
    have hinv : -(-(2 * (posVals σ).max' hS)⁻¹)⁻¹ = 2 * (posVals σ).max' hS := by
      rw [inv_neg, inv_inv, neg_neg]
    rw [hinv]
    have hsτ : (posVals σ).max' hS ≤ τ⁻¹ := by
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hm).1
      rw [← hi]
      exact hb i
    have hRτ : massRatio N σ ≤ τ⁻¹ := (massRatio_le_phiRatio N σ).trans hφ₂
    have hR0 : 0 ≤ massRatio N σ := by unfold massRatio; positivity
    nlinarith [mul_le_mul hRτ hsτ hm0.le (inv_nonneg.2 hτ.le)]
  exact ⟨h0.trans hlow, hup.trans h1⟩

/-! ## Concrete instance (Marchenko–Pastur: `M = 1`, `N = 2`, `σ = 1`) -/

end Anisotropic
