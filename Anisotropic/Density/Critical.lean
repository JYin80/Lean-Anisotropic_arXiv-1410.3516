module

public import Anisotropic.MainDefs
public import Anisotropic.Density.Poly

@[expose] public section

/-!
# Critical points of `f`

The polynomial `Q(x) = x² Π_s (1 + s x)² f'(x)`, the multiset of critical points of `f` in
`(-s_n⁻¹, 0)` counted with the multiplicity convention of §2.2, the chart `y = 1/x` of `I_0`,
the counts of Lemma 2.4 on `I_0, I_1, …, I_n`, and the identity `f(1/y) = F(y)`.
-/

open MeasureTheory Polynomial Filter Topology
open scoped ENNReal

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! ## Critical points and critical values (Lemmas 2.4, 2.5) -/

/-! ## Grouping the indices by value -/

/-- For `σ ≥ 0` and `g 0 = 0`, `Σ_i g(σ_i) = Σ_{s} #{i | σ_i = s} g(s)` over the positive values. -/
private lemma crit_sum_group (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (g : ℝ → ℝ) (hg : g 0 = 0) :
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

/-- The sum over all indices of `σ_i^k / (N (1 + σ_i x)^k)` grouped by value, `k ≥ 1`. -/
private lemma crit_sum_pow (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {k : ℕ} (hk : 0 < k)
    (x : ℝ) :
    ∑ i, σ i ^ k / ((N : ℝ) * (1 + σ i * x) ^ k) =
      ∑ s ∈ posVals σ, weight N σ s * s ^ k / (1 + s * x) ^ k := by
  rw [crit_sum_group σ hσ (fun a => a ^ k / ((N : ℝ) * (1 + a * x) ^ k))
    (by simp [zero_pow hk.ne'])]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [weight, div_eq_mul_inv, mul_inv]
  ring

private lemma crit_fR_eq (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (x : ℝ) :
    fR N σ x = -x⁻¹ + ∑ s ∈ posVals σ, weight N σ s * s / (1 + s * x) := by
  have h := crit_sum_pow N σ hσ (k := 1) one_pos x
  simp only [pow_one] at h
  rw [fR, h]

private lemma crit_fR1_eq (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (x : ℝ) :
    fR1 N σ x = (x ^ 2)⁻¹ - ∑ s ∈ posVals σ, weight N σ s * s ^ 2 / (1 + s * x) ^ 2 := by
  rw [fR1, crit_sum_pow N σ hσ (k := 2) two_pos x]

private lemma crit_fR2_eq (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (x : ℝ) :
    fR2 N σ x =
      -2 * (x ^ 3)⁻¹ + 2 * ∑ s ∈ posVals σ, weight N σ s * s ^ 3 / (1 + s * x) ^ 3 := by
  rw [fR2, crit_sum_pow N σ hσ (k := 3) (by norm_num) x]

/-- A point that is not a pole of any `s ∈ posVals σ` is not a pole of any `σ i`, for `σ ≥ 0`. -/
private lemma crit_nonpole_all (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {x : ℝ}
    (hx : ∀ s ∈ posVals σ, 1 + s * x ≠ 0) : ∀ i, 1 + σ i * x ≠ 0 := by
  intro i
  rcases (hσ i).eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · exact hx (σ i) (by simp [posVals, hpos])

private lemma crit_weight_pos (N : ℕ) (σ : Fin M → ℝ) (hN : 0 < N) {s : ℝ}
    (hs : s ∈ posVals σ) : 0 < weight N σ s := by
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hs).1
  unfold weight
  have hc : 0 < (Finset.univ.filter fun j => σ j = s).card :=
    Finset.card_pos.mpr ⟨i, by simp [hi]⟩
  positivity

private lemma crit_pos_of_mem (σ : Fin M → ℝ) {s : ℝ} (hs : s ∈ posVals σ) : 0 < s :=
  (Finset.mem_filter.mp hs).2

/-! ## The polynomial `Q` -/

theorem critPoly_eval_zero (N : ℕ) (σ : Fin M → ℝ) : (critPoly N σ).eval 0 = 1 := by
  simp [critPoly, eval_prod]

theorem critPoly_eval (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {x : ℝ} (hx : x ≠ 0)
    (hx' : ∀ i, 1 + σ i * x ≠ 0) :
    (critPoly N σ).eval x = x ^ 2 * (∏ s ∈ posVals σ, (1 + s * x) ^ 2) * fR1 N σ x := by
  have hnp : ∀ s ∈ posVals σ, 1 + s * x ≠ 0 := by
    intro s hs
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hs).1
    rw [← hi]; exact hx' i
  have hterm : ∀ s ∈ posVals σ, (∏ t ∈ posVals σ, (1 + t * x) ^ 2) *
      (weight N σ s * s ^ 2 / (1 + s * x) ^ 2) =
      weight N σ s * s ^ 2 * ∏ s' ∈ (posVals σ).erase s, (1 + s' * x) ^ 2 := by
    intro s hs
    rw [← Finset.mul_prod_erase _ _ hs]
    have := hnp s hs
    field_simp
  have hsum : (∏ t ∈ posVals σ, (1 + t * x) ^ 2) *
      ∑ s ∈ posVals σ, weight N σ s * s ^ 2 / (1 + s * x) ^ 2 =
      ∑ s ∈ posVals σ, weight N σ s * s ^ 2 * ∏ s' ∈ (posVals σ).erase s, (1 + s' * x) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hterm
  have hev : (critPoly N σ).eval x = (∏ t ∈ posVals σ, (1 + t * x) ^ 2) -
      x ^ 2 * ∑ s ∈ posVals σ, weight N σ s * s ^ 2 *
        ∏ s' ∈ (posVals σ).erase s, (1 + s' * x) ^ 2 := by
    simp only [critPoly, eval_sub, eval_mul, eval_prod, eval_pow, eval_add, eval_one, eval_C,
      eval_X, eval_finsetSum]
  rw [hev, crit_fR1_eq N σ hσ x, ← hsum]
  have hx2 : x ^ 2 * (x ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero 2 hx)
  linear_combination (-(∏ t ∈ posVals σ, (1 + t * x) ^ 2)) * hx2

/-! ## Third derivative and sign analysis -/

/-- `f'''` on `ℝ`, written in grouped form. -/
private def crit_fR3 (N : ℕ) (σ : Fin M → ℝ) (x : ℝ) : ℝ :=
  6 * (x ^ 4)⁻¹ - 6 * ∑ s ∈ posVals σ, weight N σ s * s ^ 4 / (1 + s * x) ^ 4

private lemma crit_hasDerivAt_term (c s : ℝ) (n : ℕ) {x : ℝ} (h : 1 + s * x ≠ 0) :
    HasDerivAt (fun w : ℝ => c / (1 + s * w) ^ (n + 1))
      (-(c * (n + 1) * s) / (1 + s * x) ^ (n + 2)) x := by
  have h1 : HasDerivAt (fun w : ℝ => 1 + s * w) s x := by
    simpa using ((hasDerivAt_id x).const_mul s).const_add 1
  have h2 := h1.fun_pow (n + 1)
  have h3 := (hasDerivAt_const x c).fun_div h2 (pow_ne_zero (n + 1) h)
  convert h3 using 1
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

private lemma crit_hasDerivAt_fR2 (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {x : ℝ}
    (hx : x ≠ 0) (hx' : ∀ s ∈ posVals σ, 1 + s * x ≠ 0) :
    HasDerivAt (fR2 N σ) (crit_fR3 N σ x) x := by
  have hfun : fR2 N σ = fun w : ℝ => -2 * (w ^ 3)⁻¹ +
      2 * ∑ s ∈ posVals σ, weight N σ s * s ^ 3 / (1 + s * w) ^ 3 :=
    funext (crit_fR2_eq N σ hσ)
  rw [hfun]
  have hA : HasDerivAt (fun w : ℝ => (w ^ 3)⁻¹) (-(((3 : ℕ) : ℝ) * x ^ (3 - 1)) / (x ^ 3) ^ 2) x :=
    (hasDerivAt_pow 3 x).fun_inv (pow_ne_zero 3 hx)
  have hB : HasDerivAt (fun w : ℝ => ∑ s ∈ posVals σ, weight N σ s * s ^ 3 / (1 + s * w) ^ 3)
      (∑ s ∈ posVals σ, -(weight N σ s * s ^ 3 * ((2 : ℕ) + 1) * s) / (1 + s * x) ^ (2 + 2)) x :=
    HasDerivAt.fun_sum fun s hs => crit_hasDerivAt_term (weight N σ s * s ^ 3) s 2 (hx' s hs)
  have h := (hA.const_mul (-2)).add (hB.const_mul 2)
  convert h using 1
  unfold crit_fR3
  have e1 : -2 * (-(((3 : ℕ) : ℝ) * x ^ (3 - 1)) / (x ^ 3) ^ 2) = 6 * (x ^ 4)⁻¹ := by
    field_simp
    norm_num
    ring
  have e2 : ∑ s ∈ posVals σ, -(weight N σ s * s ^ 3 * ((2 : ℕ) + 1) * s) / (1 + s * x) ^ (2 + 2) =
      -3 * ∑ s ∈ posVals σ, weight N σ s * s ^ 4 / (1 + s * x) ^ 4 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    have := hx' s hs
    push_cast
    field_simp
    ring
  rw [e1, e2]
  ring

private lemma crit_dK_pos (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {x : ℝ} (hx : x < 0) (hx' : ∀ s ∈ posVals σ, 0 < 1 + s * x) :
    0 < 2 * x * fR1 N σ x + x ^ 2 * fR2 N σ x := by
  have hx0 : x ≠ 0 := hx.ne
  have h0 : 2 * x * (x ^ 2)⁻¹ + x ^ 2 * (-2 * (x ^ 3)⁻¹) = 0 := by
    field_simp
    ring
  have h1 : ∑ s ∈ posVals σ, -2 * x * (weight N σ s * s ^ 2 / (1 + s * x) ^ 3) =
      -(2 * x) * ∑ s ∈ posVals σ, weight N σ s * s ^ 2 / (1 + s * x) ^ 2 +
        x ^ 2 * (2 * ∑ s ∈ posVals σ, weight N σ s * s ^ 3 / (1 + s * x) ^ 3) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s hs => ?_
    have := (hx' s hs).ne'
    field_simp
    ring
  have key : 2 * x * fR1 N σ x + x ^ 2 * fR2 N σ x =
      ∑ s ∈ posVals σ, -2 * x * (weight N σ s * s ^ 2 / (1 + s * x) ^ 3) := by
    rw [h1, crit_fR1_eq N σ hσ x, crit_fR2_eq N σ hσ x]
    linear_combination h0
  rw [key]
  refine Finset.sum_pos (fun s hs => ?_) hS
  have hs0 := crit_pos_of_mem σ hs
  have hr := crit_weight_pos N σ hN hs
  have := hx' s hs
  have : 0 < weight N σ s * s ^ 2 / (1 + s * x) ^ 3 := by positivity
  nlinarith

private lemma crit_dh_pos (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {x : ℝ} (hx : x ≠ 0) (hx' : ∀ s ∈ posVals σ, 1 + s * x ≠ 0) :
    0 < 3 * x ^ 2 * fR2 N σ x + x ^ 3 * crit_fR3 N σ x := by
  have h0 : 3 * x ^ 2 * (-2 * (x ^ 3)⁻¹) + x ^ 3 * (6 * (x ^ 4)⁻¹) = 0 := by
    field_simp
    ring
  have h1 : ∑ s ∈ posVals σ, 6 * x ^ 2 * (weight N σ s * s ^ 3 / (1 + s * x) ^ 4) =
      3 * x ^ 2 * (2 * ∑ s ∈ posVals σ, weight N σ s * s ^ 3 / (1 + s * x) ^ 3) +
        x ^ 3 * (-6 * ∑ s ∈ posVals σ, weight N σ s * s ^ 4 / (1 + s * x) ^ 4) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s hs => ?_
    have := hx' s hs
    field_simp
    ring
  have key : 3 * x ^ 2 * fR2 N σ x + x ^ 3 * crit_fR3 N σ x =
      ∑ s ∈ posVals σ, 6 * x ^ 2 * (weight N σ s * s ^ 3 / (1 + s * x) ^ 4) := by
    rw [h1, crit_fR2_eq N σ hσ x, crit_fR3]
    linear_combination h0
  rw [key]
  refine Finset.sum_pos (fun s hs => ?_) hS
  have hs0 := crit_pos_of_mem σ hs
  have hr := crit_weight_pos N σ hN hs
  have := hx' s hs
  positivity

/-! ## Limits at the poles -/

/-- `c / (1 + u y)²` tends to `+∞` as `y → -u⁻¹`, `y ≠ -u⁻¹`, for `c, u > 0`. -/
private lemma crit_tendsto_pole_term {c u : ℝ} (hc : 0 < c) (hu : 0 < u) :
    Tendsto (fun y : ℝ => c / (1 + u * y) ^ 2) (𝓝[≠] (-u⁻¹)) atTop := by
  have h1 : Tendsto (fun y : ℝ => (1 + u * y) ^ 2) (𝓝[≠] (-u⁻¹)) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : Continuous fun y : ℝ => (1 + u * y) ^ 2 := by fun_prop
      have := hc.tendsto (-u⁻¹)
      have e : (1 + u * (-u⁻¹)) ^ 2 = 0 := by field_simp; ring
      rw [e] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      have : 1 + u * y ≠ 0 := by
        intro h
        apply hy
        have : y = -u⁻¹ := by field_simp; linarith
        exact this
      change 0 < (1 + u * y) ^ 2
      positivity
  have h2 := (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).comp h1
  have h3 := h2.const_mul_atTop hc
  refine h3.congr fun y => ?_
  simp [div_eq_mul_inv]

private lemma crit_tendsto_fR1_pole (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    {u : ℝ} (hu : u ∈ posVals σ) : Tendsto (fR1 N σ) (𝓝[≠] (-u⁻¹)) atBot := by
  have hu0 : 0 < u := crit_pos_of_mem σ hu
  have ha0 : (-u⁻¹ : ℝ) ≠ 0 := by simp [hu0.ne']
  have hdec : ∀ y : ℝ, fR1 N σ y =
      ((y ^ 2)⁻¹ - ∑ s ∈ (posVals σ).erase u, weight N σ s * s ^ 2 / (1 + s * y) ^ 2) -
        weight N σ u * u ^ 2 / (1 + u * y) ^ 2 := by
    intro y
    rw [crit_fR1_eq N σ hσ y, ← Finset.add_sum_erase _ _ hu]
    ring
  have hg : ContinuousAt (fun y : ℝ =>
      (y ^ 2)⁻¹ - ∑ s ∈ (posVals σ).erase u, weight N σ s * s ^ 2 / (1 + s * y) ^ 2) (-u⁻¹) := by
    refine ContinuousAt.sub (ContinuousAt.inv₀ (by fun_prop) (pow_ne_zero 2 ha0)) ?_
    refine tendsto_finsetSum _ fun s hs => ?_
    have hsu : s ≠ u := (Finset.mem_erase.mp hs).1
    have hne : (1 + s * (-u⁻¹)) ^ 2 ≠ 0 := by
      have : 1 + s * (-u⁻¹) = (u - s) / u := by field_simp; ring
      rw [this]
      exact pow_ne_zero 2 (div_ne_zero (sub_ne_zero.mpr hsu.symm) hu0.ne')
    exact ContinuousAt.div continuousAt_const (by fun_prop) hne
  have ht := crit_tendsto_pole_term (mul_pos (crit_weight_pos N σ hN hu) (pow_pos hu0 2)) hu0
  have h := (hg.tendsto.mono_left nhdsWithin_le_nhds).add_atBot (tendsto_neg_atTop_atBot.comp ht)
  refine h.congr fun y => ?_
  simp only [Function.comp, hdec y]
  ring

/-! ## Roots of `Q` and the multiplicity convention -/

private lemma crit_Q_ne_zero (N : ℕ) (σ : Fin M → ℝ) : critPoly N σ ≠ 0 := by
  intro h
  have := critPoly_eval_zero N σ
  rw [h] at this
  simp at this

private lemma crit_mem_innerCrit_iff (N : ℕ) (σ : Fin M → ℝ) {x : ℝ} :
    x ∈ innerCrit N σ ↔ (critPoly N σ).eval x = 0 ∧ InInner σ x := by
  unfold innerCrit
  rw [Multiset.mem_filter, mem_roots (crit_Q_ne_zero N σ)]
  rfl

private lemma crit_eval_eq_zero_iff (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {x : ℝ}
    (hx : x ≠ 0) (hx' : ∀ s ∈ posVals σ, 1 + s * x ≠ 0) :
    (critPoly N σ).eval x = 0 ↔ fR1 N σ x = 0 := by
  rw [critPoly_eval N σ hσ hx (crit_nonpole_all σ hσ hx')]
  have : x ^ 2 * ∏ s ∈ posVals σ, (1 + s * x) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hx)
      (Finset.prod_ne_zero_iff.mpr fun s hs => pow_ne_zero 2 (hx' s hs))
  simp [this]

/-- Near a point that is neither `0` nor a pole, `x` stays away from `0` and from every pole. -/
private lemma crit_eventually_good (σ : Fin M → ℝ) {x : ℝ} (hx : x ≠ 0)
    (hx' : ∀ s ∈ posVals σ, 1 + s * x ≠ 0) :
    ∀ᶠ y in 𝓝 x, y ≠ 0 ∧ ∀ s ∈ posVals σ, 1 + s * y ≠ 0 := by
  refine (eventually_ne_nhds hx).and ?_
  rw [Filter.eventually_all_finset]
  intro s hs
  have hc : Continuous fun y : ℝ => 1 + s * y := by fun_prop
  exact hc.continuousAt.eventually_ne (hx' s hs)

/-- The first and second derivatives of a polynomial that agrees with `G f₁` near `x`. -/
private lemma crit_local_derivs (Q G : ℝ[X]) (f1 f2 : ℝ → ℝ) (f3 : ℝ) {x : ℝ}
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

/-- The multiplicity convention of §2.2. -/
theorem count_innerCrit (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {x : ℝ}
    (hx : InInner σ x) (hx' : ∀ s ∈ posVals σ, 1 + s * x ≠ 0) :
    (innerCrit N σ).count x =
      if fR1 N σ x = 0 then (if fR2 N σ x = 0 then 2 else 1) else 0 := by
  have hx0 : x ≠ 0 := hx.1.ne
  have hS : (posVals σ).Nonempty := by
    obtain ⟨s, hs, _⟩ := hx.2
    exact ⟨s, hs⟩
  have hQ0 := crit_Q_ne_zero N σ
  have hcount : (innerCrit N σ).count x = rootMultiplicity x (critPoly N σ) := by
    unfold innerCrit
    rw [Multiset.count_filter, ite_eq_left hx, count_roots]
  rw [hcount]
  by_cases h1 : fR1 N σ x = 0
  · rw [ite_eq_left h1]
    have hroot : (critPoly N σ).IsRoot x :=
      (crit_eval_eq_zero_iff N σ hσ hx0 hx').2 h1
    set G : ℝ[X] := X ^ 2 * ∏ s ∈ posVals σ, (1 + C s * X) ^ 2 with hG
    have hGeval : ∀ y : ℝ, G.eval y = y ^ 2 * ∏ s ∈ posVals σ, (1 + s * y) ^ 2 := by
      intro y
      simp [hG, eval_prod]
    have hGx : G.eval x ≠ 0 := by
      rw [hGeval]
      exact mul_ne_zero (pow_ne_zero 2 hx0)
        (Finset.prod_ne_zero_iff.mpr fun s hs => pow_ne_zero 2 (hx' s hs))
    have hgood := crit_eventually_good σ hx0 hx'
    have hQloc : ∀ᶠ y in 𝓝 x, (critPoly N σ).eval y = G.eval y * fR1 N σ y := by
      filter_upwards [hgood] with y hy
      rw [critPoly_eval N σ hσ hy.1 (crit_nonpole_all σ hσ hy.2), hGeval]
    have h1loc : ∀ᶠ y in 𝓝 x, HasDerivAt (fR1 N σ) (fR2 N σ y) y := by
      filter_upwards [hgood] with y hy
      exact hasDerivAt_fR1 N σ hy.1 (crit_nonpole_all σ hσ hy.2)
    have h2 := crit_hasDerivAt_fR2 N σ hσ hx0 hx'
    obtain ⟨hD1, hD2⟩ := crit_local_derivs (critPoly N σ) G (fR1 N σ) (fR2 N σ)
      (crit_fR3 N σ x) hQloc h1loc h2
    have key := fun n => lt_rootMultiplicity_iff_isRoot_iterate_derivative (t := x) (n := n) hQ0
    have hpos : 0 < rootMultiplicity x (critPoly N σ) := by
      rw [key 0]
      intro m hm
      obtain rfl := Nat.le_zero.mp hm
      simpa using hroot
    have hD1' : (derivative (critPoly N σ)).eval x = G.eval x * fR2 N σ x := by
      rw [hD1, h1]; ring
    by_cases h2' : fR2 N σ x = 0
    · rw [ite_eq_left h2']
      have hD1z : (derivative (critPoly N σ)).IsRoot x := by
        change (derivative (critPoly N σ)).eval x = 0
        rw [hD1', h2', mul_zero]
      have hgt1 : 1 < rootMultiplicity x (critPoly N σ) := by
        rw [key 1]
        intro m hm
        interval_cases m
        · simpa using hroot
        · simpa using hD1z
      have hnot : ¬ 2 < rootMultiplicity x (critPoly N σ) := by
        rw [key 2]
        intro hall
        have h := hall 2 le_rfl
        have h' : (derivative (derivative (critPoly N σ))).eval x = 0 := by simpa using h
        rw [hD2, h1, h2'] at h'
        have hdh := crit_dh_pos N σ hσ hN hS hx0 hx'
        rw [h2'] at hdh
        have h3 : crit_fR3 N σ x ≠ 0 := by
          intro h3
          rw [h3] at hdh
          simp at hdh
        have : G.eval x * crit_fR3 N σ x ≠ 0 := mul_ne_zero hGx h3
        apply this
        linarith
      omega
    · rw [ite_eq_right h2']
      have hnot : ¬ 1 < rootMultiplicity x (critPoly N σ) := by
        rw [key 1]
        intro hall
        have h := hall 1 le_rfl
        have h' : (derivative (critPoly N σ)).eval x = 0 := by simpa using h
        rw [hD1'] at h'
        exact mul_ne_zero hGx h2' h'
      omega
  · rw [ite_eq_right h1]
    exact rootMultiplicity_eq_zero fun h => h1 ((crit_eval_eq_zero_iff N σ hσ hx0 hx').1 h)

/-! ## The interval `I_1` -/

private lemma crit_I1_iff (σ : Fin M → ℝ) (hS : (posVals σ).Nonempty) (x : ℝ) :
    (x < 0 ∧ ∀ s ∈ posVals σ, 0 < 1 + s * x) ↔
      x ∈ Set.Ioo (-((posVals σ).max' hS)⁻¹) 0 := by
  have hs1 := (posVals σ).max'_mem hS
  have hs10 := crit_pos_of_mem σ hs1
  have e : (posVals σ).max' hS * (-((posVals σ).max' hS)⁻¹) = -1 := by
    field_simp
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨?_, hx⟩
    have h1 := h _ hs1
    by_contra hcon
    rw [not_lt] at hcon
    have := mul_le_mul_of_nonneg_left hcon hs10.le
    linarith
  · rintro ⟨h1, h2⟩
    refine ⟨h2, fun s hs => ?_⟩
    have hle : s ≤ (posVals σ).max' hS := (posVals σ).le_max' s hs
    have := mul_lt_mul_of_pos_left h1 hs10
    nlinarith

private lemma crit_I1_existsUnique (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) :
    ∃! x : ℝ, (x < 0 ∧ ∀ s ∈ posVals σ, 0 < 1 + s * x) ∧ fR1 N σ x = 0 := by
  set s1 := (posVals σ).max' hS with hs1def
  have hs1 : s1 ∈ posVals σ := (posVals σ).max'_mem hS
  have hs10 : 0 < s1 := crit_pos_of_mem σ hs1
  set a : ℝ := -s1⁻¹ with ha
  have ha0 : a < 0 := by rw [ha]; exact neg_neg_of_pos (inv_pos.2 hs10)
  have hD : ∀ x, (x < 0 ∧ ∀ s ∈ posVals σ, 0 < 1 + s * x) ↔ x ∈ Set.Ioo a 0 :=
    crit_I1_iff σ hS
  set K : ℝ → ℝ := fun x => x ^ 2 * fR1 N σ x with hK
  have hKd : ∀ x ∈ Set.Ioo a 0,
      HasDerivAt K (2 * x * fR1 N σ x + x ^ 2 * fR2 N σ x) x := by
    intro x hx
    have hxP := (hD x).2 hx
    have hx0 : x ≠ 0 := hxP.1.ne
    have hnp : ∀ i, 1 + σ i * x ≠ 0 :=
      crit_nonpole_all σ hσ (fun s hs => (hxP.2 s hs).ne')
    have h1 := hasDerivAt_fR1 N σ hx0 hnp
    have := (hasDerivAt_pow 2 x).mul h1
    convert this using 1
    simp
  have hKmono : StrictMonoOn K (Set.Ioo a 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioo a 0) ?_ ?_
    · exact fun x hx => (hKd x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioo] at hx
      rw [(hKd x hx).deriv]
      have hxP := (hD x).2 hx
      exact crit_dK_pos N σ hσ hN hS hxP.1 hxP.2
  have hKleft : Tendsto K (𝓝[>] a) atBot := by
    have hf : Tendsto (fun x : ℝ => x ^ 2) (𝓝[>] a) (𝓝 (a ^ 2)) :=
      ((continuous_pow 2).tendsto a).mono_left nhdsWithin_le_nhds
    have hg : Tendsto (fR1 N σ) (𝓝[>] a) atBot :=
      (crit_tendsto_fR1_pole N σ hσ hN hs1).mono_left
        (nhdsWithin_mono _ fun y hy => ne_of_gt hy)
    exact hf.pos_mul_atBot (by nlinarith) hg
  have hKright : Tendsto K (𝓝[<] 0) (𝓝 1) := by
    have hc : ContinuousAt (fun x : ℝ =>
        1 - x ^ 2 * ∑ s ∈ posVals σ, weight N σ s * s ^ 2 / (1 + s * x) ^ 2) 0 := by
      refine continuousAt_const.sub (ContinuousAt.mul (by fun_prop) ?_)
      refine tendsto_finsetSum _ fun s hs => ?_
      exact ContinuousAt.div continuousAt_const (by fun_prop) (by simp)
    have h' : Tendsto (fun x : ℝ =>
        1 - x ^ 2 * ∑ s ∈ posVals σ, weight N σ s * s ^ 2 / (1 + s * x) ^ 2) (𝓝[<] 0)
        (𝓝 1) := by
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    refine h'.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := (Set.mem_Iio.mp hx).ne
    simp only [hK]
    rw [crit_fR1_eq N σ hσ x, mul_sub, mul_inv_cancel₀ (pow_ne_zero 2 hx0)]
  obtain ⟨a', ha'D, ha'K⟩ : ∃ a' ∈ Set.Ioo a 0, K a' < 0 := by
    have h1 : ∀ᶠ x in 𝓝[>] a, K x < 0 := hKleft.eventually (eventually_lt_atBot 0)
    have h2 : Set.Ioo a 0 ∈ 𝓝[>] a := Ioo_mem_nhdsGT ha0
    obtain ⟨x, hx1, hx2⟩ := (h1.and h2).exists
    exact ⟨x, hx2, hx1⟩
  obtain ⟨b', hb'D, hb'K⟩ : ∃ b' ∈ Set.Ioo a 0, 0 < K b' := by
    have h1 : ∀ᶠ x in 𝓝[<] (0 : ℝ), 0 < K x := hKright.eventually (lt_mem_nhds one_pos)
    have h2 : Set.Ioo a 0 ∈ 𝓝[<] (0 : ℝ) := Ioo_mem_nhdsLT ha0
    obtain ⟨x, hx1, hx2⟩ := (h1.and h2).exists
    exact ⟨x, hx2, hx1⟩
  have hab : a' < b' := by
    by_contra h
    rw [not_lt] at h
    have := hKmono.monotoneOn hb'D ha'D h
    linarith
  have hcont : ContinuousOn K (Set.Icc a' b') := fun x hx =>
    (hKd x ⟨lt_of_lt_of_le ha'D.1 hx.1, lt_of_le_of_lt hx.2 hb'D.2⟩).continuousAt.continuousWithinAt
  obtain ⟨x0, hx0, hKx0⟩ := intermediate_value_Ioo hab.le hcont
    (show (0 : ℝ) ∈ Set.Ioo (K a') (K b') from ⟨ha'K, hb'K⟩)
  have hx0D : x0 ∈ Set.Ioo a 0 := ⟨lt_trans ha'D.1 hx0.1, lt_trans hx0.2 hb'D.2⟩
  have hx0ne : x0 ≠ 0 := hx0D.2.ne
  refine ⟨x0, ⟨(hD x0).2 hx0D, ?_⟩, ?_⟩
  · have : x0 ^ 2 * fR1 N σ x0 = 0 := hKx0
    exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero 2 hx0ne)
  · rintro y ⟨hyP, hyf⟩
    have hyD := (hD y).1 hyP
    refine hKmono.injOn hyD hx0D ?_
    change y ^ 2 * fR1 N σ y = x0 ^ 2 * fR1 N σ x0
    rw [hyf, show x0 ^ 2 * fR1 N σ x0 = 0 from hKx0]
    ring

/-- A multiset all of whose elements lie in a finset has its cardinality equal to the sum of
the counts over that finset. -/
private lemma crit_card_eq_sum (m : Multiset ℝ) (A : Finset ℝ) (h : ∀ x ∈ m, x ∈ A) :
    Multiset.card m = ∑ x ∈ A, m.count x :=
  (Multiset.sum_count_eq_card h).symm

/-- Lemma 2.4, `|𝒞 ∩ I_1| = 1`. -/
theorem card_innerCrit_I1 (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) :
    Multiset.card ((innerCrit N σ).filter (fun x => ∀ s ∈ posVals σ, 0 < 1 + s * x)) = 1 := by
  obtain ⟨x0, ⟨hx0P, hx0f⟩, huniq⟩ := crit_I1_existsUnique N σ hσ hN hS
  have hInner : InInner σ x0 :=
    ⟨hx0P.1, by obtain ⟨s, hs⟩ := hS; exact ⟨s, hs, hx0P.2 s hs⟩⟩
  have hf2 : fR2 N σ x0 ≠ 0 := by
    have := crit_dK_pos N σ hσ hN hS hx0P.1 hx0P.2
    rw [hx0f] at this
    intro h2
    rw [h2] at this
    simp at this
  have hcount : (innerCrit N σ).count x0 = 1 := by
    rw [count_innerCrit N σ hσ hN hInner (fun s hs => (hx0P.2 s hs).ne'), ite_eq_left hx0f,
      ite_eq_right hf2]
  rw [crit_card_eq_sum _ {x0}]
  · rw [Finset.sum_singleton, Multiset.count_filter, ite_eq_left hx0P.2, hcount]
  · intro x hx
    rw [Multiset.mem_filter, crit_mem_innerCrit_iff] at hx
    obtain ⟨⟨hxQ, hxI⟩, hxP⟩ := hx
    have hxnp : ∀ s ∈ posVals σ, 1 + s * x ≠ 0 := fun s hs => (hxP s hs).ne'
    have hxf : fR1 N σ x = 0 := (crit_eval_eq_zero_iff N σ hσ hxI.1.ne hxnp).1 hxQ
    exact Finset.mem_singleton.2 (huniq x ⟨⟨hxI.1, hxP⟩, hxf⟩)

/-! ## The intervals `I_i`, `i ≥ 2` -/

/-- On an interval `(L, R)` free of poles on which `f'` tends to `-∞` at both ends, the zeros of
`f'` form either no point, one point where `f''` vanishes, or two points where it does not,
because `x³ f''` is strictly increasing. -/
private lemma crit_Ii_structure (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {L R : ℝ} (hLR : L < R)
    (hI : ∀ x ∈ Set.Ioo L R, x < 0 ∧ ∀ u ∈ posVals σ, 1 + u * x ≠ 0)
    (hLt : Tendsto (fR1 N σ) (𝓝[>] L) atBot) (hRt : Tendsto (fR1 N σ) (𝓝[<] R) atBot) :
    (∀ x ∈ Set.Ioo L R, fR1 N σ x ≠ 0) ∨
    (∃ y ∈ Set.Ioo L R, fR1 N σ y = 0 ∧ fR2 N σ y = 0 ∧
      ∀ x ∈ Set.Ioo L R, fR1 N σ x = 0 → x = y) ∨
    (∃ y1 y2, y1 ∈ Set.Ioo L R ∧ y2 ∈ Set.Ioo L R ∧ y1 ≠ y2 ∧ fR1 N σ y1 = 0 ∧
      fR1 N σ y2 = 0 ∧ fR2 N σ y1 ≠ 0 ∧ fR2 N σ y2 ≠ 0 ∧
      ∀ x ∈ Set.Ioo L R, fR1 N σ x = 0 → x = y1 ∨ x = y2) := by
  have hd1 : ∀ x ∈ Set.Ioo L R, HasDerivAt (fR1 N σ) (fR2 N σ x) x := fun x hx =>
    hasDerivAt_fR1 N σ (hI x hx).1.ne (crit_nonpole_all σ hσ (hI x hx).2)
  set h : ℝ → ℝ := fun x => x ^ 3 * fR2 N σ x with hh
  have hdh : ∀ x ∈ Set.Ioo L R,
      HasDerivAt h (3 * x ^ 2 * fR2 N σ x + x ^ 3 * crit_fR3 N σ x) x := by
    intro x hx
    have := (hasDerivAt_pow 3 x).mul
      (crit_hasDerivAt_fR2 N σ hσ (hI x hx).1.ne (hI x hx).2)
    convert this using 1
  have hmonoh : StrictMonoOn h (Set.Ioo L R) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioo L R)
      (fun x hx => (hdh x hx).continuousAt.continuousWithinAt) ?_
    intro x hx
    rw [interior_Ioo] at hx
    rw [(hdh x hx).deriv]
    exact crit_dh_pos N σ hσ hN hS (hI x hx).1.ne (hI x hx).2
  -- an interior maximum of `f'`
  set y0 : ℝ := (L + R) / 2 with hy0def
  have hy0 : y0 ∈ Set.Ioo L R := ⟨by linarith, by linarith⟩
  obtain ⟨a', ha'⟩ : ∃ a' ∈ Set.Ioo L y0, fR1 N σ a' < fR1 N σ y0 := by
    have h1 : ∀ᶠ x in 𝓝[>] L, fR1 N σ x < fR1 N σ y0 :=
      hLt.eventually (eventually_lt_atBot _)
    have h2 : Set.Ioo L y0 ∈ 𝓝[>] L := Ioo_mem_nhdsGT hy0.1
    obtain ⟨x, hx1, hx2⟩ := (h1.and h2).exists
    exact ⟨x, hx2, hx1⟩
  obtain ⟨b', hb'⟩ : ∃ b' ∈ Set.Ioo y0 R, fR1 N σ b' < fR1 N σ y0 := by
    have h1 : ∀ᶠ x in 𝓝[<] R, fR1 N σ x < fR1 N σ y0 :=
      hRt.eventually (eventually_lt_atBot _)
    have h2 : Set.Ioo y0 R ∈ 𝓝[<] R := Ioo_mem_nhdsLT hy0.2
    obtain ⟨x, hx1, hx2⟩ := (h1.and h2).exists
    exact ⟨x, hx2, hx1⟩
  have hab' : a' ≤ b' := le_trans ha'.1.2.le hb'.1.1.le
  have hcontIcc : ContinuousOn (fR1 N σ) (Set.Icc a' b') := fun x hx =>
    (hd1 x ⟨lt_of_lt_of_le ha'.1.1 hx.1, lt_of_le_of_lt hx.2 hb'.1.2⟩).continuousAt
      |>.continuousWithinAt
  obtain ⟨xs, hxsIcc, hxsmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 hab') hcontIcc
  have hy0Icc : y0 ∈ Set.Icc a' b' := ⟨ha'.1.2.le, hb'.1.1.le⟩
  have hxsy0 : fR1 N σ y0 ≤ fR1 N σ xs := isMaxOn_iff.mp hxsmax y0 hy0Icc
  have hxsa : xs ≠ a' := by
    rintro rfl
    linarith [ha'.2]
  have hxsb : xs ≠ b' := by
    rintro rfl
    linarith [hb'.2]
  have hxsmem : xs ∈ Set.Ioo a' b' := ⟨lt_of_le_of_ne hxsIcc.1 hxsa.symm,
    lt_of_le_of_ne hxsIcc.2 hxsb⟩
  have hxsI : xs ∈ Set.Ioo L R := ⟨lt_trans ha'.1.1 hxsmem.1, lt_trans hxsmem.2 hb'.1.2⟩
  have hloc : IsLocalMax (fR1 N σ) xs :=
    hxsmax.isLocalMax (Icc_mem_nhds hxsmem.1 hxsmem.2)
  have hf2xs : fR2 N σ xs = 0 := hloc.hasDerivAt_eq_zero (hd1 xs hxsI)
  have hhxs : h xs = 0 := by simp [hh, hf2xs]
  -- signs of `f''`
  have hf2pos : ∀ y ∈ Set.Ioo L xs, 0 < fR2 N σ y := by
    intro y hy
    have hyI : y ∈ Set.Ioo L R := ⟨hy.1, lt_trans hy.2 hxsI.2⟩
    have hlt : h y < h xs := hmonoh hyI hxsI hy.2
    rw [hhxs] at hlt
    have hy3 : y ^ 3 < 0 := Odd.pow_neg (by decide) (hI y hyI).1
    by_contra hc
    rw [not_lt] at hc
    have : 0 ≤ y ^ 3 * fR2 N σ y := mul_nonneg_of_nonpos_of_nonpos hy3.le hc
    exact absurd hlt (not_lt.2 this)
  have hf2neg : ∀ y ∈ Set.Ioo xs R, fR2 N σ y < 0 := by
    intro y hy
    have hyI : y ∈ Set.Ioo L R := ⟨lt_trans hxsI.1 hy.1, hy.2⟩
    have hlt : h xs < h y := hmonoh hxsI hyI hy.1
    rw [hhxs] at hlt
    have hy3 : y ^ 3 < 0 := Odd.pow_neg (by decide) (hI y hyI).1
    by_contra hc
    rw [not_lt] at hc
    have : y ^ 3 * fR2 N σ y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hy3.le hc
    exact absurd hlt (not_lt.2 this)
  -- monotonicity of `f'` on both sides of `xs`
  have hmono1 : StrictMonoOn (fR1 N σ) (Set.Ioc L xs) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioc L xs) ?_ ?_
    · intro x hx
      exact (hd1 x ⟨hx.1, lt_of_le_of_lt hx.2 hxsI.2⟩).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioc] at hx
      rw [(hd1 x ⟨hx.1, lt_trans hx.2 hxsI.2⟩).deriv]
      exact hf2pos x hx
  have hanti1 : StrictAntiOn (fR1 N σ) (Set.Ico xs R) := by
    refine strictAntiOn_of_deriv_neg (convex_Ico xs R) ?_ ?_
    · intro x hx
      exact (hd1 x ⟨lt_of_lt_of_le hxsI.1 hx.1, hx.2⟩).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ico] at hx
      rw [(hd1 x ⟨lt_trans hxsI.1 hx.1, hx.2⟩).deriv]
      exact hf2neg x hx
  have hle : ∀ y ∈ Set.Ioo L R, fR1 N σ y ≤ fR1 N σ xs := by
    intro y hy
    rcases le_or_gt y xs with hyx | hyx
    · exact hmono1.monotoneOn ⟨hy.1, hyx⟩ ⟨hxsI.1, le_rfl⟩ hyx
    · exact hanti1.antitoneOn ⟨le_rfl, hxsI.2⟩ ⟨hyx.le, hy.2⟩ hyx.le
  rcases lt_trichotomy (fR1 N σ xs) 0 with hneg | hzero | hpos
  · exact Or.inl fun x hx => (lt_of_le_of_lt (hle x hx) hneg).ne
  · refine Or.inr (Or.inl ⟨xs, hxsI, hzero, hf2xs, ?_⟩)
    intro x hx hfx
    rcases lt_trichotomy x xs with hlt | heq | hgt
    · have := hmono1 ⟨hx.1, hlt.le⟩ ⟨hxsI.1, le_rfl⟩ hlt
      rw [hfx, hzero] at this
      exact absurd this (lt_irrefl _)
    · exact heq
    · have := hanti1 ⟨le_rfl, hxsI.2⟩ ⟨hgt.le, hx.2⟩ hgt
      rw [hfx, hzero] at this
      exact absurd this (lt_irrefl _)
  · refine Or.inr (Or.inr ?_)
    obtain ⟨a'', ha''⟩ : ∃ a'' ∈ Set.Ioo L xs, fR1 N σ a'' < 0 := by
      have h1 : ∀ᶠ x in 𝓝[>] L, fR1 N σ x < 0 := hLt.eventually (eventually_lt_atBot _)
      have h2 : Set.Ioo L xs ∈ 𝓝[>] L := Ioo_mem_nhdsGT hxsI.1
      obtain ⟨x, hx1, hx2⟩ := (h1.and h2).exists
      exact ⟨x, hx2, hx1⟩
    obtain ⟨b'', hb''⟩ : ∃ b'' ∈ Set.Ioo xs R, fR1 N σ b'' < 0 := by
      have h1 : ∀ᶠ x in 𝓝[<] R, fR1 N σ x < 0 := hRt.eventually (eventually_lt_atBot _)
      have h2 : Set.Ioo xs R ∈ 𝓝[<] R := Ioo_mem_nhdsLT hxsI.2
      obtain ⟨x, hx1, hx2⟩ := (h1.and h2).exists
      exact ⟨x, hx2, hx1⟩
    obtain ⟨y1, hy1, hfy1⟩ := intermediate_value_Ioo ha''.1.2.le
      (fun x hx => (hd1 x ⟨lt_of_lt_of_le ha''.1.1 hx.1,
        lt_of_le_of_lt hx.2 hxsI.2⟩).continuousAt.continuousWithinAt)
      (show (0 : ℝ) ∈ Set.Ioo (fR1 N σ a'') (fR1 N σ xs) from ⟨ha''.2, hpos⟩)
    obtain ⟨y2, hy2, hfy2⟩ := intermediate_value_Ioo' hb''.1.1.le
      (fun x hx => (hd1 x ⟨lt_of_lt_of_le hxsI.1 hx.1,
        lt_of_le_of_lt hx.2 hb''.1.2⟩).continuousAt.continuousWithinAt)
      (show (0 : ℝ) ∈ Set.Ioo (fR1 N σ b'') (fR1 N σ xs) from ⟨hb''.2, hpos⟩)
    have hy1L : y1 ∈ Set.Ioo L xs := ⟨lt_trans ha''.1.1 hy1.1, hy1.2⟩
    have hy2R : y2 ∈ Set.Ioo xs R := ⟨hy2.1, lt_trans hy2.2 hb''.1.2⟩
    have hy1I : y1 ∈ Set.Ioo L R := ⟨hy1L.1, lt_trans hy1L.2 hxsI.2⟩
    have hy2I : y2 ∈ Set.Ioo L R := ⟨lt_trans hxsI.1 hy2R.1, hy2R.2⟩
    refine ⟨y1, y2, hy1I, hy2I, (lt_trans hy1L.2 hy2R.1).ne, hfy1, hfy2,
      (hf2pos y1 hy1L).ne', (hf2neg y2 hy2R).ne, ?_⟩
    intro x hx hfx
    rcases lt_trichotomy x xs with hlt | heq | hgt
    · left
      exact hmono1.injOn ⟨hx.1, hlt.le⟩ ⟨hy1L.1, hy1L.2.le⟩ (hfx.trans hfy1.symm)
    · have h0 : fR1 N σ xs = 0 := heq ▸ hfx
      rw [h0] at hpos
      exact absurd hpos (lt_irrefl _)
    · right
      exact hanti1.injOn ⟨hgt.le, hx.2⟩ ⟨hy2R.1.le, hy2R.2⟩ (hfx.trans hfy2.symm)

/-- On `(-s⁻¹, -s'⁻¹)` for consecutive `s < s'`, `x < 0`, `1 + s x > 0` and no `u` is at a pole. -/
private lemma crit_Ii_good (σ : Fin M → ℝ) {s s' : ℝ} (hs : s ∈ posVals σ)
    (hs' : s' ∈ posVals σ) (hcons : ∀ u ∈ posVals σ, ¬ (s < u ∧ u < s')) {x : ℝ}
    (hx : x ∈ Set.Ioo (-s⁻¹) (-s'⁻¹)) :
    x < 0 ∧ 0 < 1 + s * x ∧ ∀ u ∈ posVals σ, 1 + u * x ≠ 0 := by
  have hs0 := crit_pos_of_mem σ hs
  have hs'0 := crit_pos_of_mem σ hs'
  have hx0 : x < 0 := lt_trans hx.2 (neg_neg_of_pos (inv_pos.2 hs'0))
  have e : s * (-s⁻¹) = -1 := by field_simp
  have e' : s' * (-s'⁻¹) = -1 := by field_simp
  have h1 : -1 < s * x := by
    have := mul_lt_mul_of_pos_left hx.1 hs0
    linarith
  have h2 : s' * x < -1 := by
    have := mul_lt_mul_of_pos_left hx.2 hs'0
    linarith
  refine ⟨hx0, by linarith, fun u hu => ?_⟩
  by_cases hus : u ≤ s
  · have := mul_le_mul_of_nonpos_right hus hx0.le
    intro h
    linarith
  · have hsu : s < u := lt_of_not_ge hus
    have hus' : s' ≤ u := by
      by_contra hcon
      exact hcons u hu ⟨hsu, lt_of_not_ge hcon⟩
    have := mul_le_mul_of_nonpos_right hus' hx0.le
    intro h
    linarith

/-- Lemma 2.4, `|𝒞 ∩ I_i| ∈ {0, 2}` for `I_i = (-s⁻¹, -s'⁻¹)`, `s < s'` consecutive. -/
theorem card_innerCrit_Ii (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    {s s' : ℝ} (hs : s ∈ posVals σ) (hs' : s' ∈ posVals σ) (hlt : s < s')
    (hcons : ∀ u ∈ posVals σ, ¬ (s < u ∧ u < s')) :
    Multiset.card ((innerCrit N σ).filter (fun x => -s⁻¹ < x ∧ x < -s'⁻¹)) = 0 ∨
      Multiset.card ((innerCrit N σ).filter (fun x => -s⁻¹ < x ∧ x < -s'⁻¹)) = 2 := by
  have hs0 := crit_pos_of_mem σ hs
  have hS : (posVals σ).Nonempty := ⟨s, hs⟩
  have hLR : -s⁻¹ < -s'⁻¹ := by
    have : s'⁻¹ < s⁻¹ := inv_strictAnti₀ hs0 hlt
    linarith
  have hgood : ∀ x ∈ Set.Ioo (-s⁻¹) (-s'⁻¹), x < 0 ∧ 0 < 1 + s * x ∧
      ∀ u ∈ posVals σ, 1 + u * x ≠ 0 := fun x hx => crit_Ii_good σ hs hs' hcons hx
  have hLt : Tendsto (fR1 N σ) (𝓝[>] (-s⁻¹)) atBot :=
    (crit_tendsto_fR1_pole N σ hσ hN hs).mono_left (nhdsWithin_mono _ fun y hy => ne_of_gt hy)
  have hRt : Tendsto (fR1 N σ) (𝓝[<] (-s'⁻¹)) atBot :=
    (crit_tendsto_fR1_pole N σ hσ hN hs').mono_left (nhdsWithin_mono _ fun y hy => ne_of_lt hy)
  have hinner : ∀ x ∈ Set.Ioo (-s⁻¹) (-s'⁻¹), InInner σ x := fun x hx =>
    ⟨(hgood x hx).1, s, hs, (hgood x hx).2.1⟩
  have hmem : ∀ x ∈ (innerCrit N σ).filter (fun x => -s⁻¹ < x ∧ x < -s'⁻¹),
      x ∈ Set.Ioo (-s⁻¹) (-s'⁻¹) ∧ fR1 N σ x = 0 := by
    intro x hx
    rw [Multiset.mem_filter, crit_mem_innerCrit_iff] at hx
    obtain ⟨⟨hxQ, hxI⟩, hxP⟩ := hx
    exact ⟨hxP, (crit_eval_eq_zero_iff N σ hσ hxI.1.ne (hgood x hxP).2.2).1 hxQ⟩
  have hcnt : ∀ y ∈ Set.Ioo (-s⁻¹) (-s'⁻¹),
      ((innerCrit N σ).filter (fun x => -s⁻¹ < x ∧ x < -s'⁻¹)).count y =
        if fR1 N σ y = 0 then (if fR2 N σ y = 0 then 2 else 1) else 0 := by
    intro y hy
    rw [Multiset.count_filter, ite_eq_left (show -s⁻¹ < y ∧ y < -s'⁻¹ from hy)]
    exact count_innerCrit N σ hσ hN (hinner y hy) (hgood y hy).2.2
  rcases crit_Ii_structure N σ hσ hN hS hLR (fun x hx => ⟨(hgood x hx).1, (hgood x hx).2.2⟩)
    hLt hRt with
    hA | ⟨y, hy, hf1, hf2, huniq⟩ | ⟨y1, y2, hy1, hy2, hne, hf1, hf1', hf2, hf2', huniq⟩
  · left
    rw [crit_card_eq_sum _ ∅]
    · simp
    · intro x hx
      exact absurd (hmem x hx).2 (hA x (hmem x hx).1)
  · right
    rw [crit_card_eq_sum _ {y}]
    · rw [Finset.sum_singleton, hcnt y hy, ite_eq_left hf1, ite_eq_left hf2]
    · intro x hx
      exact Finset.mem_singleton.2 (huniq x (hmem x hx).1 (hmem x hx).2)
  · right
    rw [crit_card_eq_sum _ {y1, y2}]
    · rw [Finset.sum_pair hne, hcnt y1 hy1, hcnt y2 hy2, ite_eq_left hf1, ite_eq_left hf1',
        ite_eq_right hf2, ite_eq_right hf2']
    · intro x hx
      rcases huniq x (hmem x hx).1 (hmem x hx).2 with h | h
      · simp [h]
      · simp [h]

/-! ## The chart of `I_0` -/

/-- `F''`, the derivative of `F'`. -/
private def crit_FChart2 (N : ℕ) (σ : Fin M → ℝ) (y : ℝ) : ℝ :=
  -2 * ∑ s ∈ posVals σ, weight N σ s * s ^ 2 / (y + s) ^ 3

private lemma crit_hasDerivAt_term_chart (c s : ℝ) (n : ℕ) {x : ℝ} (h : x + s ≠ 0) :
    HasDerivAt (fun w : ℝ => c / (w + s) ^ (n + 1)) (-(c * (n + 1)) / (x + s) ^ (n + 2)) x := by
  have h1 : HasDerivAt (fun w : ℝ => w + s) 1 x := (hasDerivAt_id x).add_const s
  have h2 := h1.fun_pow (n + 1)
  have h3 := (hasDerivAt_const x c).fun_div h2 (pow_ne_zero (n + 1) h)
  convert h3 using 1
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

private lemma crit_hasDerivAt_FChart1 (N : ℕ) (σ : Fin M → ℝ) {y : ℝ}
    (hy : ∀ s ∈ posVals σ, y + s ≠ 0) :
    HasDerivAt (FChart1 N σ) (crit_FChart2 N σ y) y := by
  have hB : HasDerivAt (fun w : ℝ => ∑ s ∈ posVals σ, weight N σ s * s ^ 2 / (w + s) ^ 2)
      (∑ s ∈ posVals σ, -(weight N σ s * s ^ 2 * ((1 : ℕ) + 1)) / (y + s) ^ (1 + 2)) y :=
    HasDerivAt.fun_sum fun s hs => crit_hasDerivAt_term_chart (weight N σ s * s ^ 2) s 1 (hy s hs)
  have h := hB.const_add (-1)
  unfold FChart1
  convert h using 1
  unfold crit_FChart2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  push_cast
  ring

private lemma crit_FChart2_neg (N : ℕ) (σ : Fin M → ℝ) (hN : 0 < N) (hS : (posVals σ).Nonempty)
    {y : ℝ} (hy : InChart σ y) : crit_FChart2 N σ y < 0 := by
  unfold crit_FChart2
  have : 0 < ∑ s ∈ posVals σ, weight N σ s * s ^ 2 / (y + s) ^ 3 := by
    refine Finset.sum_pos (fun s hs => ?_) hS
    have := hy s hs
    have := crit_weight_pos N σ hN hs
    have := crit_pos_of_mem σ hs
    positivity
  linarith

private lemma crit_InChart_iff (σ : Fin M → ℝ) (hS : (posVals σ).Nonempty) (y : ℝ) :
    InChart σ y ↔ y ∈ Set.Ioi (-(posVals σ).min' hS) := by
  have hmin := (posVals σ).min'_mem hS
  constructor
  · intro h
    have := h _ hmin
    simp only [Set.mem_Ioi]
    linarith
  · intro h s hs
    have := (posVals σ).min'_le s hs
    simp only [Set.mem_Ioi] at h
    linarith

private lemma crit_tendsto_pole_term_chart {c m : ℝ} (hc : 0 < c) :
    Tendsto (fun y : ℝ => c / (y + m) ^ 2) (𝓝[≠] (-m)) atTop := by
  have h1 : Tendsto (fun y : ℝ => (y + m) ^ 2) (𝓝[≠] (-m)) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : Continuous fun y : ℝ => (y + m) ^ 2 := by fun_prop
      have := hc.tendsto (-m)
      have e : (-m + m) ^ 2 = 0 := by ring
      rw [e] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      have : y + m ≠ 0 := by
        intro h
        exact hy (Set.mem_singleton_iff.mpr (by linarith))
      change 0 < (y + m) ^ 2
      positivity
  have h2 := (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).comp h1
  have h3 := h2.const_mul_atTop hc
  refine h3.congr fun y => ?_
  simp [div_eq_mul_inv]

/-- Lemma 2.4, `|𝒞 ∩ I_0| = 1`, in the chart. -/
theorem existsUnique_yEdge (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) : ∃! y, InChart σ y ∧ FChart1 N σ y = 0 := by
  have _hσ := hσ
  set m := (posVals σ).min' hS with hm
  have hm1 : m ∈ posVals σ := (posVals σ).min'_mem hS
  have hD : ∀ y, InChart σ y ↔ y ∈ Set.Ioi (-m) := crit_InChart_iff σ hS
  have hd : ∀ y ∈ Set.Ioi (-m), HasDerivAt (FChart1 N σ) (crit_FChart2 N σ y) y := by
    intro y hy
    have hyc := (hD y).2 hy
    exact crit_hasDerivAt_FChart1 N σ fun s hs => (hyc s hs).ne'
  have hanti : StrictAntiOn (FChart1 N σ) (Set.Ioi (-m)) := by
    refine strictAntiOn_of_deriv_neg (convex_Ioi (-m))
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt) ?_
    intro y hy
    rw [interior_Ioi] at hy
    rw [(hd y hy).deriv]
    exact crit_FChart2_neg N σ hN hS ((hD y).2 hy)
  -- the limits at the two ends of the chart
  have hleft : Tendsto (FChart1 N σ) (𝓝[>] (-m)) atTop := by
    have hdec : ∀ y : ℝ, FChart1 N σ y =
        (-1 + ∑ s ∈ (posVals σ).erase m, weight N σ s * s ^ 2 / (y + s) ^ 2) +
          weight N σ m * m ^ 2 / (y + m) ^ 2 := by
      intro y
      rw [FChart1, ← Finset.add_sum_erase _ _ hm1]
      ring
    have hg : ContinuousAt (fun y : ℝ =>
        -1 + ∑ s ∈ (posVals σ).erase m, weight N σ s * s ^ 2 / (y + s) ^ 2) (-m) := by
      refine continuousAt_const.add ?_
      refine tendsto_finsetSum _ fun s hs => ?_
      have hsm : s ≠ m := (Finset.mem_erase.mp hs).1
      have hne : (-m + s) ^ 2 ≠ 0 := by
        have : -m + s ≠ 0 := by
          intro h
          exact hsm (by linarith)
        exact pow_ne_zero 2 this
      exact ContinuousAt.div continuousAt_const (by fun_prop) hne
    have ht := crit_tendsto_pole_term_chart (m := m)
      (mul_pos (crit_weight_pos N σ hN hm1) (pow_pos (crit_pos_of_mem σ hm1) 2))
    have hsub : Set.Ioi (-m) ⊆ {-m}ᶜ := fun y hy => ne_of_gt hy
    have h := (hg.tendsto.mono_left nhdsWithin_le_nhds).add_atTop
      (ht.mono_left (nhdsWithin_mono (-m) hsub))
    refine h.congr fun y => ?_
    simp only [hdec y]
  have hright : Tendsto (FChart1 N σ) atTop (𝓝 (-1)) := by
    have hterm : ∀ s ∈ posVals σ, Tendsto (fun y : ℝ => weight N σ s * s ^ 2 / (y + s) ^ 2)
        atTop (𝓝 0) := by
      intro s hs
      refine tendsto_const_nhds.div_atTop ?_
      exact (tendsto_pow_atTop (two_ne_zero)).comp (tendsto_atTop_add_const_right _ _ tendsto_id)
    have := (tendsto_finsetSum _ hterm).const_add (-1)
    change Tendsto (fun y : ℝ => -1 + ∑ s ∈ posVals σ, weight N σ s * s ^ 2 / (y + s) ^ 2)
      atTop (𝓝 (-1))
    simpa using this
  obtain ⟨y1, hy1, hy1pos⟩ : ∃ y1 ∈ Set.Ioi (-m), 0 < FChart1 N σ y1 := by
    obtain ⟨y, h1, h2⟩ := ((hleft.eventually (eventually_gt_atTop 0)).and
      self_mem_nhdsWithin).exists
    exact ⟨y, h2, h1⟩
  obtain ⟨y2, hy2, hy2neg⟩ : ∃ y2, y1 < y2 ∧ FChart1 N σ y2 < 0 := by
    obtain ⟨y, h1, h2⟩ := ((hright.eventually (gt_mem_nhds (show (-1 : ℝ) < 0 by norm_num))).and
      (eventually_gt_atTop y1)).exists
    exact ⟨y, h2, h1⟩
  have hcont : ContinuousOn (FChart1 N σ) (Set.Icc y1 y2) := fun y hy =>
    (hd y (lt_of_lt_of_le hy1 hy.1)).continuousAt.continuousWithinAt
  obtain ⟨y0, hy0, hFy0⟩ := intermediate_value_Ioo' hy2.le hcont
    (show (0 : ℝ) ∈ Set.Ioo (FChart1 N σ y2) (FChart1 N σ y1) from ⟨hy2neg, hy1pos⟩)
  have hy0m : y0 ∈ Set.Ioi (-m) := lt_trans hy1 hy0.1
  refine ⟨y0, ⟨(hD y0).2 hy0m, hFy0⟩, ?_⟩
  rintro y ⟨hyc, hyF⟩
  exact hanti.injOn ((hD y).1 hyc) hy0m (hyF.trans hFy0.symm)

theorem yEdge_spec (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) : InChart σ (yEdge N σ) ∧ FChart1 N σ (yEdge N σ) = 0 := by
  have hex : ∃ y, InChart σ y ∧ FChart1 N σ y = 0 := (existsUnique_yEdge N σ hσ hN hS).exists
  unfold yEdge
  rw [dite_eq_left hex]
  exact hex.choose_spec

/-- `x_{2p} = ∞` iff `φ π((0,∞)) = 1`. -/
theorem yEdge_eq_zero_iff (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) : yEdge N σ = 0 ↔ massRatio N σ = 1 := by
  have h0 : InChart σ 0 := fun s hs => by
    have := crit_pos_of_mem σ hs
    linarith
  have hF0 : FChart1 N σ 0 = massRatio N σ - 1 := by
    rw [← sum_weight N σ, FChart1]
    have : ∑ s ∈ posVals σ, weight N σ s * s ^ 2 / (0 + s) ^ 2 =
        ∑ s ∈ posVals σ, weight N σ s := by
      refine Finset.sum_congr rfl fun s hs => ?_
      have := (crit_pos_of_mem σ hs).ne'
      rw [zero_add]
      field_simp
    rw [this]
    ring
  have hspec := yEdge_spec N σ hσ hN hS
  constructor
  · intro h
    have := hspec.2
    rw [h, hF0] at this
    linarith
  · intro h
    have hF : FChart1 N σ 0 = 0 := by rw [hF0, h]; ring
    exact (existsUnique_yEdge N σ hσ hN hS).unique hspec ⟨h0, hF⟩

/-! ## The chart identity -/

private lemma crit_fR_inv_term (y s : ℝ) (hy : y ≠ 0) :
    s / (1 + s * y⁻¹) = s * y / (y + s) := by
  by_cases h : y + s = 0
  · have : 1 + s * y⁻¹ = 0 := by
      have : 1 + s * y⁻¹ = (y + s) / y := by field_simp
      rw [this, h, zero_div]
    rw [this, h]; simp
  · have : 1 + s * y⁻¹ = (y + s) / y := by field_simp
    rw [this]
    field_simp

theorem fR_inv_eq_FChart (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {y : ℝ} (hy : y ≠ 0) :
    fR N σ y⁻¹ = FChart N σ y := by
  rw [crit_fR_eq N σ hσ, FChart, inv_inv]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mul_div_assoc, crit_fR_inv_term y s hy]
  ring

/-! ## The total count -/

/-- `Q` does not vanish at a pole `-u⁻¹`, `u` a positive value of `σ`. -/
private lemma crit_eval_pole (N : ℕ) (σ : Fin M → ℝ) (hN : 0 < N) {u : ℝ}
    (hu : u ∈ posVals σ) : (critPoly N σ).eval (-u⁻¹) ≠ 0 := by
  have hu0 := crit_pos_of_mem σ hu
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
    (mul_ne_zero (mul_ne_zero (crit_weight_pos N σ hN hu).ne' (pow_ne_zero 2 hu0.ne')) ?_)
  refine Finset.prod_ne_zero_iff.mpr fun t ht => ?_
  have htu : t ≠ u := (Finset.mem_erase.mp ht).1
  have : 1 + t * (-u⁻¹) = (u - t) / u := by field_simp; ring
  rw [this]
  exact pow_ne_zero 2 (div_ne_zero (sub_ne_zero.mpr htu.symm) hu0.ne')

/-- No element of `innerCrit` is an interior pole. -/
private lemma crit_innerCrit_ne_pole (N : ℕ) (σ : Fin M → ℝ) (hN : 0 < N) {x : ℝ}
    (hx : x ∈ innerCrit N σ) {u : ℝ} (hu : u ∈ posVals σ) : x ≠ -u⁻¹ := by
  rintro rfl
  exact crit_eval_pole N σ hN hu ((crit_mem_innerCrit_iff N σ).1 hx).1

/-- Every element of `innerCrit` is negative. -/
private lemma crit_innerCrit_neg (N : ℕ) (σ : Fin M → ℝ) {x : ℝ} (hx : x ∈ innerCrit N σ) :
    x < 0 := ((crit_mem_innerCrit_iff N σ).1 hx).2.1

private lemma crit_card_odd (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) (n : ℕ) : ∀ c ∈ posVals σ,
    ((posVals σ).filter (fun u => c < u)).card = n →
      ∃ k, Multiset.card ((innerCrit N σ).filter (fun x => -c⁻¹ < x)) = 2 * k + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c hc hcard
    have hc0 := crit_pos_of_mem σ hc
    have ec : c * (-c⁻¹) = -1 := by field_simp
    by_cases hA : ((posVals σ).filter (fun u => c < u)).Nonempty
    · -- the next larger value `c'`
      set c' := ((posVals σ).filter (fun u => c < u)).min' hA with hc'def
      have hc'A : c' ∈ (posVals σ).filter (fun u => c < u) := Finset.min'_mem _ hA
      have hc'T : c' ∈ posVals σ := (Finset.mem_filter.mp hc'A).1
      have hcc' : c < c' := (Finset.mem_filter.mp hc'A).2
      have hc'0 := crit_pos_of_mem σ hc'T
      have hcons : ∀ u ∈ posVals σ, ¬ (c < u ∧ u < c') := by
        rintro u hu ⟨h1, h2⟩
        have : c' ≤ u := Finset.min'_le _ u (Finset.mem_filter.mpr ⟨hu, h1⟩)
        exact absurd h2 (not_lt.mpr this)
      have hsub : (posVals σ).filter (fun u => c' < u) ⊆ (posVals σ).filter (fun u => c < u) := by
        intro u hu
        obtain ⟨huT, hu'⟩ := Finset.mem_filter.mp hu
        exact Finset.mem_filter.mpr ⟨huT, lt_trans hcc' hu'⟩
      have hlt : ((posVals σ).filter (fun u => c' < u)).card < n := by
        rw [← hcard]
        exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).2
          ⟨c', hc'A, fun h => lt_irrefl _ (Finset.mem_filter.mp h).2⟩)
      obtain ⟨k, hk⟩ := ih _ hlt c' hc'T rfl
      have hLR : -c⁻¹ < -c'⁻¹ := by
        have : c'⁻¹ < c⁻¹ := inv_strictAnti₀ hc0 hcc'
        linarith
      set m := innerCrit N σ with hm
      have h1 := Multiset.filter_add_not (fun x : ℝ => x < -c'⁻¹)
        (m.filter (fun x => -c⁻¹ < x))
      have e1 : (m.filter (fun x => -c⁻¹ < x)).filter (fun x => x < -c'⁻¹) =
          m.filter (fun x => -c⁻¹ < x ∧ x < -c'⁻¹) := by
        rw [Multiset.filter_filter]
        exact Multiset.filter_congr fun x _ => and_comm
      have e2 : (m.filter (fun x => -c⁻¹ < x)).filter (fun x => ¬ x < -c'⁻¹) =
          m.filter (fun x => -c'⁻¹ < x) := by
        rw [Multiset.filter_filter]
        refine Multiset.filter_congr fun x hx => ?_
        have hne := crit_innerCrit_ne_pole N σ hN hx hc'T
        constructor
        · rintro ⟨h1, h2⟩
          exact lt_of_le_of_ne (not_lt.mp h1) (Ne.symm hne)
        · intro h
          exact ⟨not_lt.mpr h.le, lt_trans hLR h⟩
      have hsplit : Multiset.card (m.filter (fun x => -c⁻¹ < x)) =
          Multiset.card (m.filter (fun x => -c⁻¹ < x ∧ x < -c'⁻¹)) +
            Multiset.card (m.filter (fun x => -c'⁻¹ < x)) := by
        rw [← e1, ← e2, ← Multiset.card_add, h1]
      rcases card_innerCrit_Ii N σ hσ hN hc hc'T hcc' hcons with h0 | h2
      · exact ⟨k, by rw [hsplit, h0, hk]; ring⟩
      · exact ⟨k + 1, by rw [hsplit, h2, hk]; ring⟩
    · -- `c` is the largest value
      have hmax : ∀ u ∈ posVals σ, u ≤ c := by
        intro u hu
        by_contra hcon
        exact hA ⟨u, Finset.mem_filter.mpr ⟨hu, lt_of_not_ge hcon⟩⟩
      have heq : (innerCrit N σ).filter (fun x => -c⁻¹ < x) =
          (innerCrit N σ).filter (fun x => ∀ s ∈ posVals σ, 0 < 1 + s * x) := by
        refine Multiset.filter_congr fun x hx => ?_
        have hx0 := crit_innerCrit_neg N σ hx
        constructor
        · intro h s hs
          have h1 := mul_lt_mul_of_pos_left h hc0
          have h2 := mul_le_mul_of_nonpos_right (hmax s hs) hx0.le
          linarith
        · intro h
          have h1 := h c hc
          by_contra hcon
          rw [not_lt] at hcon
          have := mul_le_mul_of_nonneg_left hcon hc0.le
          linarith
      exact ⟨0, by rw [heq, card_innerCrit_I1 N σ hσ hN hS]⟩

/-- `|𝒞| = 2p`, `p ≥ 1`. -/
theorem card_innerCrit (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) :
    Multiset.card (innerCrit N σ) + 1 = 2 * numBands N σ ∧ 1 ≤ numBands N σ := by
  set c := (posVals σ).min' hS with hcdef
  have hc : c ∈ posVals σ := (posVals σ).min'_mem hS
  have hc0 := crit_pos_of_mem σ hc
  have hall : (innerCrit N σ).filter (fun x => -c⁻¹ < x) = innerCrit N σ := by
    rw [Multiset.filter_eq_self]
    intro x hx
    obtain ⟨hx0, s, hs, hsx⟩ := ((crit_mem_innerCrit_iff N σ).1 hx).2
    have hs0 := crit_pos_of_mem σ hs
    have hcs : c ≤ s := (posVals σ).min'_le s hs
    have e : s * (-s⁻¹) = -1 := by field_simp
    have h1 : -s⁻¹ < x := by
      by_contra hcon
      rw [not_lt] at hcon
      have := mul_le_mul_of_nonneg_left hcon hs0.le
      linarith
    have h2 : -c⁻¹ ≤ -s⁻¹ := by
      have : s⁻¹ ≤ c⁻¹ := inv_anti₀ hc0 hcs
      linarith
    exact lt_of_le_of_lt h2 h1
  obtain ⟨k, hk⟩ := crit_card_odd N σ hσ hN hS _ c hc rfl
  rw [hall] at hk
  unfold numBands
  rw [hk]
  omega

/-! ## Concrete instances -/

/-- MP: `x_1 = -1/(1 + √φ)` is critical and `a_1 = f(x_1) = (1 + √φ)²`. -/
example : fR1 2 (fun _ : Fin 1 => (1 : ℝ)) (-1 / (1 + √(1 / 2))) = 0 := by
  have hc : √(1 / 2 : ℝ) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have hc0 : 0 < √(1 / 2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  simp only [fR1, Finset.univ_unique, Finset.sum_singleton]
  have h1 : (1 : ℝ) + 1 * (-1 / (1 + √(1 / 2))) = √(1 / 2) / (1 + √(1 / 2)) := by
    field_simp; ring
  rw [h1]
  field_simp
  rw [hc]; ring

example : fR 2 (fun _ : Fin 1 => (1 : ℝ)) (-1 / (1 + √(1 / 2))) = (1 + √(1 / 2)) ^ 2 := by
  have hc : √(1 / 2 : ℝ) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have hc0 : 0 < √(1 / 2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  simp only [fR, Finset.univ_unique, Finset.sum_singleton]
  have h1 : (1 : ℝ) + 1 * (-1 / (1 + √(1 / 2))) = √(1 / 2) / (1 + √(1 / 2)) := by
    field_simp; ring
  rw [h1]
  field_simp
  nlinarith [hc]

/-- MP, chart of `I_0`: `y_2 = √φ - 1` is critical and `a_2 = F(y_2) = (1 - √φ)²`. -/
example : FChart1 2 (fun _ : Fin 1 => (1 : ℝ)) (√(1 / 2) - 1) = 0 := by
  have hS : posVals (fun _ : Fin 1 => (1 : ℝ)) = {1} := by
    ext s; simp [posVals]; rintro rfl; norm_num
  simp [FChart1, hS, weight]

example : FChart 2 (fun _ : Fin 1 => (1 : ℝ)) (√(1 / 2) - 1) = (1 - √(1 / 2)) ^ 2 := by
  have hS : posVals (fun _ : Fin 1 => (1 : ℝ)) = {1} := by
    ext s; simp [posVals]; rintro rfl; norm_num
  have hc : √(1 / 2 : ℝ) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have hc0 : 0 < √(1 / 2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have h2 : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [FChart, hS, Finset.sum_singleton, weight]
  simp
  field_simp
  nlinarith [h2]

/-- MP: `x_1` is a root of `Q`, `Q = (1 + x)² - x²/2`. -/
example : (critPoly 2 (fun _ : Fin 1 => (1 : ℝ))).eval (-1 / (1 + √(1 / 2))) = 0 := by
  have hS : posVals (fun _ : Fin 1 => (1 : ℝ)) = {1} := by
    ext s; simp [posVals]; rintro rfl; norm_num
  have hc : √(1 / 2 : ℝ) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have hc0 : 0 < √(1 / 2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have h2 : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp [critPoly, hS, weight]
  field_simp
  nlinarith [h2]

/-- MP: `y_2 = √φ - 1` lies in the chart `(-1, ∞)`. -/
example : InChart (fun _ : Fin 1 => (1 : ℝ)) (√(1 / 2) - 1) := by
  have hS : posVals (fun _ : Fin 1 => (1 : ℝ)) = {1} := by
    ext s; simp [posVals]; rintro rfl; norm_num
  have hc0 : 0 < √(1 / 2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  intro s hs; rw [hS, Finset.mem_singleton] at hs; subst hs; linarith

/-! ### Each theorem at one instance -/

example : (critPoly 2 (fun _ : Fin 1 => (1 : ℝ))).eval 0 = 1 := critPoly_eval_zero 2 _

example : (critPoly 2 (fun _ : Fin 1 => (1 : ℝ))).eval (-1 / 2) =
    (-1 / 2) ^ 2 * (∏ s ∈ posVals (fun _ : Fin 1 => (1 : ℝ)), (1 + s * (-1 / 2)) ^ 2) *
      fR1 2 (fun _ : Fin 1 => (1 : ℝ)) (-1 / 2) :=
  critPoly_eval 2 _ (fun _ => by norm_num) (by norm_num) (fun _ => by norm_num)

example : fR 2 (fun _ : Fin 1 => (1 : ℝ)) (1 : ℝ)⁻¹ = FChart 2 (fun _ : Fin 1 => (1 : ℝ)) 1 :=
  fR_inv_eq_FChart 2 _ (fun _ => by norm_num) one_ne_zero

end Anisotropic
