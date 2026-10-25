import Anisotropic.Density.Stability.Quadratic
import Anisotropic.Density.Structure
import Anisotropic.Density.Count

/-!
# Lemma A.3: `f` near a regular edge

Lemma A.3 (`lem:edge_tools`) with explicit constants depending on `τ` only: the identity
(f''_expr) at a critical point, the estimates (f_der_est) `c_x ≤ |x_k| ≤ C_x`,
`c₂ ≤ (-1)^{k+1} f''(x_k)`, `|f''(x_k)| ≤ C₂` and `|f'''| ≤ C₃` on the disk of radius `ρ₀`
around `x_k`, the Taylor expansion of `f`, `f'`, `f''` at `x_k` on that disk in mean-value form,
and the resulting lower bounds on `|f(ζ) - a_k|` and `|f'(ζ)|` on the disk of radius `ρ₁`.

Proofs (Appendix A).
* `x_k` is finite and off the poles by (reg: edge), and `f'(x_k) = 0`.
* `|x_k| ≤ C_x`: `x_k = m(a_k)` is a limit of `m(a_k + iη)`, and `|m(z)| ≤ (1 + √R)/|z|`.
* `|x| ≥ c_x` at every nonzero critical point `x`: from `1 = Σ_i σ_i² x² / (N (1 + σ_i x)²)`.
* The lower bound on `(-1)^{k+1} f''(x_k)`: for `k = 1` and `k = 2p` all terms of (f''_expr)
  have one sign. For `2 ≤ k ≤ 2p - 1`, the critical points `x_{2j+1} ≤ x_{2j}` lie between
  the same two consecutive poles (the number of critical points in `(-1/s, 0)` is odd for every
  pole `-1/s`), `y ↦ y³ f''(y)` is nondecreasing there, and `a_{2j} - a_{2j+1} ≥ τ` bounds
  `f''` at `x_{2j+1}` from below and `-f''` at `x_{2j}` from below.
-/

open MeasureTheory Polynomial Filter Topology
open scoped ENNReal

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! ## Lemma A.3 (`lem:edge_tools`), (f''_expr), (z-a_taylor) -/

/-- Upper bound `C_x = (1 + τ^{-1/2})/τ` on `|x_k|`. -/
def edgeCx (τ : ℝ) : ℝ := (1 + (√τ)⁻¹) / τ
/-- Lower bound `c_x = τ^{3/2}/(1 + τ^{1/2})` on `|x_k|`. -/
def edgecx (τ : ℝ) : ℝ := τ * √τ / (1 + √τ)
/-- Upper bound on `|f''(x_k)|`. -/
def edgeC2 (τ : ℝ) : ℝ := 2 / edgecx τ * τ⁻¹ * (τ⁻¹ ^ 2 + edgeCx τ * τ⁻¹ ^ 3)
/-- Lower bound on `|f''(x_k)|`: the cases `k ∈ {1, 2p}`, interior odd `k`, interior even `k`. -/
def edgec2 (τ : ℝ) : ℝ :=
  min (2 * τ / ((edgeCx τ + τ) * edgeCx τ ^ 3))
    (min (τ * edgecx τ ^ 3 / (2 * edgeCx τ ^ 5)) (τ ^ 3 / 4))
/-- Radius of the disk around `x_k` free of `0` and of the poles. -/
def edgeRho0 (τ : ℝ) : ℝ := min (edgecx τ) τ / 2
/-- Bound on `|f'''|` on that disk. -/
def edgeC3 (τ : ℝ) : ℝ := 6 * (2 / edgecx τ) ^ 4 + 6 * τ⁻¹ * (2 / τ) ^ 4
/-- Radius of the Taylor disk. -/
def edgeRho1 (τ : ℝ) : ℝ := min (edgeRho0 τ) (edgec2 τ / (4 * edgeC3 τ))
/-- Radius of the half-disk around `a_k` of (z-a_taylor). -/
def edgeTau0 (τ : ℝ) : ℝ := edgec2 τ * edgeRho1 τ ^ 2 / 8
/-- The window `τ'(τ)` of Lemmas A.4 and A.5. -/
def edgeTau' (τ : ℝ) : ℝ := edgeTau0 τ / 4

/-! ## Elementary facts on the values of `σ` -/

private lemma et_pos_of_mem (σ : Fin M → ℝ) {s : ℝ} (hs : s ∈ posVals σ) : 0 < s :=
  (Finset.mem_filter.mp hs).2

private lemma et_weight_pos (N : ℕ) (σ : Fin M → ℝ) (hN : 0 < N) {s : ℝ}
    (hs : s ∈ posVals σ) : 0 < weight N σ s := by
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hs).1
  unfold weight
  have hc : 0 < (Finset.univ.filter fun j => σ j = s).card :=
    Finset.card_pos.mpr ⟨i, by simp [hi]⟩
  positivity

private lemma et_nonpole_all (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {x : ℝ}
    (hx : ∀ s ∈ posVals σ, 1 + s * x ≠ 0) : ∀ i, 1 + σ i * x ≠ 0 := by
  intro i
  rcases (hσ i).eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · exact hx (σ i) (by simp [posVals, hpos])

/-- For `s > 0`: `-1/s < x ↔ 0 < 1 + s x`. -/
private lemma et_lt_iff {s x : ℝ} (hs : 0 < s) : -s⁻¹ < x ↔ 0 < 1 + s * x := by
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
private lemma et_gt_iff {s x : ℝ} (hs : 0 < s) : x < -s⁻¹ ↔ 1 + s * x < 0 := by
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

/-! ## The intervals `I_1, …, I_n` between consecutive poles -/

/-- The right end of the interval `I_l` with left end `-1/s`: the pole `-1/s'` of the next larger
value `s'`, or `0` when `s = s_1` is the largest value. -/
private def etR (σ : Fin M → ℝ) (s : ℝ) : ℝ :=
  if h : ((posVals σ).filter (fun u => s < u)).Nonempty then
    -(((posVals σ).filter (fun u => s < u)).min' h)⁻¹ else 0

/-- `x ∈ (-1/s, etR s)`, the interval `I_l` with left end `-1/s`. -/
private def etK (σ : Fin M → ℝ) (s x : ℝ) : Prop := -s⁻¹ < x ∧ x < etR σ s

private lemma et_ne_max_iff (σ : Fin M → ℝ) (hS : (posVals σ).Nonempty) {s : ℝ}
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

private lemma et_R_max (σ : Fin M → ℝ) (hS : (posVals σ).Nonempty) :
    etR σ ((posVals σ).max' hS) = 0 := by
  unfold etR
  rw [dite_eq_right]
  rw [et_ne_max_iff σ hS ((posVals σ).max'_mem hS)]
  simp

private lemma et_R_next (σ : Fin M → ℝ) (hS : (posVals σ).Nonempty) {s : ℝ}
    (hs : s ∈ posVals σ) (hne : s ≠ (posVals σ).max' hS) :
    ∃ s' ∈ posVals σ, s < s' ∧ (∀ u ∈ posVals σ, ¬ (s < u ∧ u < s')) ∧ etR σ s = -s'⁻¹ := by
  have hA := (et_ne_max_iff σ hS hs).2 hne
  have hm := Finset.min'_mem _ hA
  refine ⟨_, (Finset.mem_filter.mp hm).1, (Finset.mem_filter.mp hm).2, ?_, ?_⟩
  · rintro u hu ⟨h1, h2⟩
    have := Finset.min'_le _ u (Finset.mem_filter.mpr ⟨hu, h1⟩)
    linarith
  · unfold etR
    rw [dite_eq_left hA]

private lemma et_left_lt_R (σ : Fin M → ℝ) (hS : (posVals σ).Nonempty) {s : ℝ}
    (hs : s ∈ posVals σ) : -s⁻¹ < etR σ s := by
  have hs0 := et_pos_of_mem σ hs
  by_cases hmax : s = (posVals σ).max' hS
  · rw [hmax, et_R_max]
    rw [← hmax]
    simpa using hs0
  · obtain ⟨s', hs', hss', -, hR⟩ := et_R_next σ hS hs hmax
    rw [hR]
    have : s'⁻¹ < s⁻¹ := inv_strictAnti₀ hs0 hss'
    linarith

/-- On `I_l = (-1/s, etR s)`: `x < 0`, `1 + u x > 0` for `u ≤ s` and `1 + u x < 0` for `u > s`. -/
private lemma et_K_sign (σ : Fin M → ℝ) (hS : (posVals σ).Nonempty) {s : ℝ}
    (hs : s ∈ posVals σ) {x : ℝ} (hx : etK σ s x) :
    x < 0 ∧ ∀ u ∈ posVals σ, (u ≤ s → 0 < 1 + u * x) ∧ (s < u → 1 + u * x < 0) := by
  have hs0 := et_pos_of_mem σ hs
  have h1 : 0 < 1 + s * x := (et_lt_iff hs0).1 hx.1
  by_cases hmax : s = (posVals σ).max' hS
  · have hR : etR σ s = 0 := by rw [hmax]; exact et_R_max σ hS
    have hx0 : x < 0 := hR ▸ hx.2
    refine ⟨hx0, fun u hu => ⟨fun hus => ?_, fun hsu => ?_⟩⟩
    · have := mul_le_mul_of_nonpos_right hus hx0.le
      linarith
    · have := (posVals σ).le_max' u hu
      rw [← hmax] at this
      linarith
  · obtain ⟨s', hs', hss', hcons, hR⟩ := et_R_next σ hS hs hmax
    have hs'0 := et_pos_of_mem σ hs'
    have h2 : 1 + s' * x < 0 := (et_gt_iff hs'0).1 (hR ▸ hx.2)
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

/-! ## The ordered critical points `x_1 ≥ ⋯ ≥ x_{2p-1}` and their positions -/

/-- The number of critical points in `(y, 0)` counted with multiplicity. -/
private def etA (N : ℕ) (σ : Fin M → ℝ) (y : ℝ) : ℕ :=
  Multiset.card ((innerCrit N σ).filter (fun x => y < x))

private lemma et_critPoly_ne_zero (N : ℕ) (σ : Fin M → ℝ) : critPoly N σ ≠ 0 := by
  intro h
  have := critPoly_eval_zero N σ
  rw [h] at this
  simp at this

/-- `Q(-1/u) ≠ 0` at the poles. -/
private lemma et_critPoly_pole (N : ℕ) (σ : Fin M → ℝ) (hN : 0 < N) {u : ℝ}
    (hu : u ∈ posVals σ) : (critPoly N σ).eval (-u⁻¹) ≠ 0 := by
  have hu0 := et_pos_of_mem σ hu
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
    (mul_ne_zero (mul_ne_zero (et_weight_pos N σ hN hu).ne' (pow_ne_zero 2 hu0.ne')) ?_)
  refine Finset.prod_ne_zero_iff.mpr fun t ht => ?_
  have htu : t ≠ u := (Finset.mem_erase.mp ht).1
  have : 1 + t * (-u⁻¹) = (u - t) / u := by field_simp; ring
  rw [this]
  exact pow_ne_zero 2 (div_ne_zero (sub_ne_zero.mpr htu.symm) hu0.ne')

private lemma et_mem_innerCrit (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    {x : ℝ} (hx : x ∈ innerCrit N σ) :
    InInner σ x ∧ (∀ u ∈ posVals σ, 1 + u * x ≠ 0) ∧ fR1 N σ x = 0 := by
  unfold innerCrit at hx
  rw [Multiset.mem_filter, mem_roots (et_critPoly_ne_zero N σ)] at hx
  obtain ⟨hroot, hin⟩ := hx
  have h0 : (critPoly N σ).eval x = 0 := hroot
  have hnp : ∀ u ∈ posVals σ, 1 + u * x ≠ 0 := by
    intro u hu h
    have hu0 := et_pos_of_mem σ hu
    have hx' : x = -u⁻¹ := by
      field_simp
      linear_combination h
    rw [hx'] at h0
    exact et_critPoly_pole N σ hN hu h0
  refine ⟨hin, hnp, ?_⟩
  rw [critPoly_eval N σ hσ hin.1.ne (et_nonpole_all σ hσ hnp)] at h0
  have hpre : x ^ 2 * ∏ s ∈ posVals σ, (1 + s * x) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hin.1.ne)
      (Finset.prod_ne_zero_iff.mpr fun s hs => pow_ne_zero 2 (hnp s hs))
  exact (mul_eq_zero.mp h0).resolve_left hpre

/-- In a list sorted in decreasing order, the entries `> y` form an initial segment. -/
private lemma et_list_prefix (y : ℝ) : ∀ (L : List ℝ), L.Pairwise (fun a b => b ≤ a) →
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
      have ih := et_list_prefix y L hpw.2 j hj
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

private lemma et_sort_spec (m : Multiset ℝ) {i : ℕ} (hi : i < Multiset.card m) :
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
  · rw [et_list_prefix y _ hpw i hi', ← Multiset.countP_eq_card_filter,
      ← Multiset.coe_countP, Multiset.coe_reverse, Multiset.sort_eq]

/-- `x_k ∈ 𝒞`, and `y < x_k` iff at least `k` critical points lie in `(y, 0)`. -/
private lemma et_xCrit_spec (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {k : ℕ} (hk1 : 1 ≤ k) (hk : k < 2 * numBands N σ) :
    xCrit N σ k ∈ innerCrit N σ ∧ ∀ y, (y < xCrit N σ k ↔ k ≤ etA N σ y) := by
  have hc := (card_innerCrit N σ hσ hN hS).1
  have hx : xCrit N σ k = ((innerCrit N σ).sort (· ≤ ·)).reverse.getD (k - 1) 0 := by
    unfold xCrit
    rw [ite_eq_right (by omega)]
  obtain ⟨hmem, hspec⟩ := et_sort_spec (innerCrit N σ) (i := k - 1) (by omega)
  rw [hx]
  refine ⟨hmem, fun y => ?_⟩
  rw [hspec y, etA]
  omega

private lemma et_ne_R (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {s : ℝ} (hs : s ∈ posVals σ) {x : ℝ}
    (hx : x ∈ innerCrit N σ) : x ≠ etR σ s := by
  obtain ⟨hin, hnp, -⟩ := et_mem_innerCrit N σ hσ hN hx
  intro h
  by_cases hmax : s = (posVals σ).max' hS
  · rw [hmax, et_R_max] at h
    linarith [hin.1]
  · obtain ⟨s', hs', -, -, hR⟩ := et_R_next σ hS hs hmax
    rw [hR] at h
    apply hnp s' hs'
    rw [h]
    have := et_pos_of_mem σ hs'
    field_simp
    ring

private lemma et_A_split (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {s : ℝ} (hs : s ∈ posVals σ) :
    etA N σ (-s⁻¹) =
      etA N σ (etR σ s) + Multiset.card ((innerCrit N σ).filter (etK σ s)) := by
  have hlt := et_left_lt_R σ hS hs
  have hne := fun x (hx : x ∈ innerCrit N σ) => et_ne_R N σ hσ hN hS hs hx
  unfold etA
  have h1 := Multiset.filter_add_not (fun x : ℝ => x < etR σ s)
    ((innerCrit N σ).filter (fun x => -s⁻¹ < x))
  have e1 : ((innerCrit N σ).filter (fun x => -s⁻¹ < x)).filter (fun x => x < etR σ s) =
      (innerCrit N σ).filter (etK σ s) := by
    rw [Multiset.filter_filter]
    exact Multiset.filter_congr fun x _ => by simp only [etK, and_comm]
  have e2 : ((innerCrit N σ).filter (fun x => -s⁻¹ < x)).filter (fun x => ¬ x < etR σ s) =
      (innerCrit N σ).filter (fun x => etR σ s < x) := by
    rw [Multiset.filter_filter]
    refine Multiset.filter_congr fun x hx => ?_
    constructor
    · rintro ⟨h1, -⟩
      exact lt_of_le_of_ne (not_lt.mp h1) (hne x hx).symm
    · intro h
      exact ⟨not_lt.mpr h.le, lt_trans hlt h⟩
  rw [← h1, Multiset.card_add, e1, e2, add_comm]

private lemma et_A_zero (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) :
    etA N σ 0 = 0 := by
  unfold etA
  rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
  intro x hx
  exact not_lt.2 (et_mem_innerCrit N σ hσ hN hx).1.1.le

private lemma et_card_K_max (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) :
    Multiset.card ((innerCrit N σ).filter (etK σ ((posVals σ).max' hS))) = 1 := by
  rw [← card_innerCrit_I1 N σ hσ hN hS]
  congr 1
  refine Multiset.filter_congr fun x hx => ?_
  have hin := (et_mem_innerCrit N σ hσ hN hx).1
  have hm := (posVals σ).max'_mem hS
  constructor
  · intro hK s hs
    exact ((et_K_sign σ hS hm hK).2 s hs).1 ((posVals σ).le_max' s hs)
  · intro h
    refine ⟨(et_lt_iff (et_pos_of_mem σ hm)).2 (h _ hm), ?_⟩
    rw [et_R_max]
    exact hin.1

private lemma et_card_K_inner (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {s : ℝ} (hs : s ∈ posVals σ) (hne : s ≠ (posVals σ).max' hS) :
    Multiset.card ((innerCrit N σ).filter (etK σ s)) = 0 ∨
      Multiset.card ((innerCrit N σ).filter (etK σ s)) = 2 := by
  obtain ⟨s', hs', hss', hcons, hR⟩ := et_R_next σ hS hs hne
  have e : (innerCrit N σ).filter (etK σ s) =
      (innerCrit N σ).filter (fun x => -s⁻¹ < x ∧ x < -s'⁻¹) :=
    Multiset.filter_congr fun x _ => by rw [etK, hR]
  rw [e]
  exact card_innerCrit_Ii N σ hσ hN hs hs' hss' hcons

private lemma et_A_odd (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) (n : ℕ) : ∀ s ∈ posVals σ,
    ((posVals σ).filter (fun u => s < u)).card = n → Odd (etA N σ (-s⁻¹)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs hcard
    rw [et_A_split N σ hσ hN hS hs]
    by_cases hmax : s = (posVals σ).max' hS
    · subst hmax
      rw [et_R_max, et_A_zero N σ hσ hN, et_card_K_max N σ hσ hN hS]
      exact odd_one
    · obtain ⟨s', hs', hss', -, hR⟩ := et_R_next σ hS hs hmax
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
      rcases et_card_K_inner N σ hσ hN hS hs hmax with h | h
      · rw [h, add_zero]
        exact ho
      · rw [h]
        exact ho.add_even even_two

/-! ## The chart of `I_0` -/

/-- For `σ ≥ 0` and `g 0 = 0`, `Σ_i g(σ_i) = Σ_{s} #{i | σ_i = s} g(s)` over the positive values. -/
private lemma et_sum_group (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (g : ℝ → ℝ) (hg : g 0 = 0) :
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

/-- `f'(1/y) = -y² F'(y)` in the chart of `I_0`. -/
private lemma et_fR1_inv (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {y : ℝ} (hy0 : y ≠ 0)
    (hy : InChart σ y) : fR1 N σ y⁻¹ = -(y ^ 2) * FChart1 N σ y := by
  have hg : ∑ i, σ i ^ 2 / ((N : ℝ) * (1 + σ i * y⁻¹) ^ 2) =
      ∑ s ∈ posVals σ, ((Finset.univ.filter fun i => σ i = s).card : ℝ) *
        (s ^ 2 / ((N : ℝ) * (1 + s * y⁻¹) ^ 2)) :=
    et_sum_group σ hσ (fun a => a ^ 2 / ((N : ℝ) * (1 + a * y⁻¹) ^ 2)) (by simp)
  have hterm : ∀ s ∈ posVals σ, ((Finset.univ.filter fun i => σ i = s).card : ℝ) *
      (s ^ 2 / ((N : ℝ) * (1 + s * y⁻¹) ^ 2)) =
      y ^ 2 * (weight N σ s * s ^ 2 / (y + s) ^ 2) := by
    intro s hs
    have h1 := (hy s hs).ne'
    have e : 1 + s * y⁻¹ = (y + s) / y := by field_simp
    rw [e, weight]
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp
    · have hNr : (N : ℝ) ≠ 0 := by positivity
      field_simp
  unfold fR1 FChart1
  rw [hg, Finset.sum_congr rfl hterm, ← Finset.mul_sum, inv_pow, inv_inv]
  ring

/-! ## Consequences of the assumptions -/

private lemma et_empMeasure_apply (σ : Fin M → ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    empMeasure σ s = (M : ℝ≥0∞)⁻¹ * ((Finset.univ.filter fun i => σ i ∈ s).card : ℝ≥0∞) := by
  simp only [empMeasure, Measure.smul_apply, Measure.finsetSum_apply,
    Measure.dirac_apply' _ hs, smul_eq_mul]
  congr 1
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Set.indicator]

/-- (phi_bounded) and (Sigma_gap) give `N > 0` and some positive `σ i`. -/
private lemma et_facts {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) :
    0 < N ∧ (posVals σ).Nonempty := by
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · exfalso
      have := h.phi_lower
      simp [phiRatio, h0] at this
      linarith [h.pos]
    · exact h0
  refine ⟨hN, ?_⟩
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have hM : M ≠ 0 := by
    rintro rfl
    have := h.phi_lower
    simp [phiRatio] at this
    linarith [h.pos]
  have hall : ∀ i, σ i = 0 := by
    intro i
    by_contra hi
    have hpos : 0 < σ i := lt_of_le_of_ne (h.nonneg i) (Ne.symm hi)
    have : σ i ∈ posVals σ := by
      simp only [posVals, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨i, rfl⟩, hpos⟩
    rw [hne] at this
    simp at this
  have hgap := h.Sigma_gap
  rw [et_empMeasure_apply σ measurableSet_Icc] at hgap
  simp only [hall, Set.mem_Icc, le_refl, h.pos.le, and_self, Finset.filter_true,
    Finset.card_univ, Fintype.card_fin] at hgap
  have hM' : (M : ℝ≥0∞)⁻¹ * (M : ℝ≥0∞) = 1 :=
    ENNReal.inv_mul_cancel (by exact_mod_cast hM) (ENNReal.natCast_ne_top _)
  rw [hM', ENNReal.toReal_one] at hgap
  linarith [h.pos]

/-- `Σ_i t_i ≤ τ⁻¹ c` when every `t_i ≤ c / N`, by `M / N ≤ τ⁻¹`. -/
private lemma et_sum_le {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) {c : ℝ}
    (hc : 0 ≤ c) (t : Fin M → ℝ) (ht : ∀ i, t i ≤ c / N) : ∑ i, t i ≤ τ⁻¹ * c := by
  refine (Finset.sum_le_sum fun i _ => ht i).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hφ := h.phi_upper
  unfold phiRatio at hφ
  have e : (M : ℝ) * (c / N) = (M / N) * c := by ring
  rw [e]
  exact mul_le_mul_of_nonneg_right hφ hc

/-- Positivity of the constants, and `c_x ≤ τ`. -/
private lemma et_consts {τ : ℝ} (hτ : 0 < τ) :
    0 < edgecx τ ∧ 0 < edgeCx τ ∧ edgecx τ ≤ τ ∧ 0 < edgec2 τ ∧ 0 < edgeC3 τ ∧
      0 < edgeRho0 τ ∧ 0 < edgeRho1 τ := by
  have hs := Real.sqrt_pos.2 hτ
  have h1 : 0 < edgecx τ := by unfold edgecx; positivity
  have h2 : 0 < edgeCx τ := by unfold edgeCx; positivity
  have h3 : edgecx τ ≤ τ := by
    unfold edgecx
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have h4 : 0 < edgec2 τ := by unfold edgec2; positivity
  have h5 : 0 < edgeC3 τ := by unfold edgeC3; positivity
  have h6 : 0 < edgeRho0 τ := by unfold edgeRho0; positivity
  have h7 : 0 < edgeRho1 τ := by unfold edgeRho1; positivity
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-! ## The critical points `x_{2j+1} ≤ x_{2j}` lie between the same two poles -/

private lemma et_pair (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {j : ℕ} (hj : 1 ≤ j) (hj' : 2 * j + 1 < 2 * numBands N σ) :
    xCrit N σ (2 * j + 1) ≤ xCrit N σ (2 * j) ∧
      ∀ i, 0 < (1 + σ i * xCrit N σ (2 * j + 1)) * (1 + σ i * xCrit N σ (2 * j)) := by
  obtain ⟨hmem, hspec⟩ := et_xCrit_spec N σ hσ hN hS (k := 2 * j) (by omega) (by omega)
  obtain ⟨hmem', hspec'⟩ := et_xCrit_spec N σ hσ hN hS (k := 2 * j + 1) (by omega) hj'
  have hle : xCrit N σ (2 * j + 1) ≤ xCrit N σ (2 * j) := by
    by_contra h
    rw [not_le] at h
    have h1 := (hspec' (xCrit N σ (2 * j))).1 h
    have h2 := (hspec (xCrit N σ (2 * j))).2 (by omega)
    exact lt_irrefl _ h2
  refine ⟨hle, fun i => ?_⟩
  obtain ⟨-, hnp, -⟩ := et_mem_innerCrit N σ hσ hN hmem
  obtain ⟨-, hnp', -⟩ := et_mem_innerCrit N σ hσ hN hmem'
  rcases (hσ i).eq_or_lt with h0 | hpos
  · rw [← h0]; norm_num
  have hu : σ i ∈ posVals σ := by simp [posVals, hpos]
  have ha := hnp' (σ i) hu
  have hb := hnp (σ i) hu
  have hmono : σ i * xCrit N σ (2 * j + 1) ≤ σ i * xCrit N σ (2 * j) :=
    mul_le_mul_of_nonneg_left hle hpos.le
  by_contra hneg
  rw [not_lt] at hneg
  have hc : 1 + σ i * xCrit N σ (2 * j + 1) < 0 := by
    rcases lt_or_gt_of_ne ha with h | h
    · exact h
    · exfalso
      have h' : 0 < 1 + σ i * xCrit N σ (2 * j) := by linarith
      linarith [mul_pos h h']
  have hd : 0 < 1 + σ i * xCrit N σ (2 * j) := by
    rcases lt_or_gt_of_ne hb with h | h
    · exfalso
      linarith [mul_pos_of_neg_of_neg hc h]
    · exact h
  have hl : xCrit N σ (2 * j + 1) < -(σ i)⁻¹ := (et_gt_iff hpos).2 hc
  have hr : -(σ i)⁻¹ < xCrit N σ (2 * j) := (et_lt_iff hpos).2 hd
  have hA1 := (hspec (-(σ i)⁻¹)).1 hr
  have hA2 : ¬ (2 * j + 1 ≤ etA N σ (-(σ i)⁻¹)) := fun h => lt_asymm hl ((hspec' _).2 h)
  obtain ⟨m, hm⟩ := et_A_odd N σ hσ hN hS _ (σ i) hu rfl
  omega

/-- `x_1 < 0` and `1 + σ_i x_1 > 0` for all `i`: `x_1 ∈ I_1`. -/
private lemma et_first (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) : xCrit N σ 1 < 0 ∧ ∀ i, 0 < 1 + σ i * xCrit N σ 1 := by
  have hp := (card_innerCrit N σ hσ hN hS).2
  obtain ⟨hmem, hspec⟩ := et_xCrit_spec N σ hσ hN hS le_rfl (by omega)
  have h1 := card_innerCrit_I1 N σ hσ hN hS
  obtain ⟨z, hz⟩ := Multiset.card_pos_iff_exists_mem.1 (by rw [h1]; norm_num)
  rw [Multiset.mem_filter] at hz
  have hzx : z ≤ xCrit N σ 1 := by
    by_contra hlt
    rw [not_le] at hlt
    have : 1 ≤ etA N σ (xCrit N σ 1) := by
      unfold etA
      exact Multiset.card_pos_iff_exists_mem.2 ⟨z, Multiset.mem_filter.2 ⟨hz.1, hlt⟩⟩
    exact lt_irrefl _ ((hspec _).2 this)
  refine ⟨(et_mem_innerCrit N σ hσ hN hmem).1.1, fun i => ?_⟩
  rcases (hσ i).eq_or_lt with h0 | hpos
  · rw [← h0]; norm_num
  · have hu : σ i ∈ posVals σ := by simp [posVals, hpos]
    have := hz.2 (σ i) hu
    nlinarith [mul_le_mul_of_nonneg_left hzx hpos.le]

/-! ## Facts at a regular edge -/

/-- At a regular edge, `x_k` is finite and nonzero, `σ_i τ ≤ |1 + σ_i x_k|`, `x_k` is no pole,
`f'(x_k) = 0`, and `a_k = f(x_k)`. -/
private lemma et_reg {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ} (h : DensityAssumptions τ N σ)
    (hk : RegularEdge τ N σ k) :
    ¬ (k = 2 * numBands N σ ∧ yEdge N σ = 0) ∧ xCrit N σ k ≠ 0 ∧
      (∀ i, σ i * τ ≤ |1 + σ i * xCrit N σ k|) ∧ (∀ i, 1 + σ i * xCrit N σ k ≠ 0) ∧
      fR1 N σ (xCrit N σ k) = 0 ∧ edgeVal N σ k = fR N σ (xCrit N σ k) := by
  obtain ⟨hN, hS⟩ := et_facts h
  have hσ := h.nonneg
  obtain ⟨hk1, hk2, hτa, -, hpole⟩ := hk
  have hfin : ¬ (k = 2 * numBands N σ ∧ yEdge N σ = 0) := by
    rintro ⟨hk', hy⟩
    have : edgeVal N σ k = 0 := by
      unfold edgeVal
      simp only [hk', ↓reduceIte, hy]
      simp [FChart]
    linarith [h.pos]
  have hp := hpole hfin
  have hpb : ∀ i, σ i * τ ≤ |1 + σ i * xCrit N σ k| := by
    intro i
    rcases (hσ i).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · have hu : σ i ∈ posVals σ := by simp [posVals, hpos]
      have e : 1 + σ i * xCrit N σ k = σ i * (xCrit N σ k + (σ i)⁻¹) := by
        field_simp
        ring
      rw [e, abs_mul, abs_of_pos hpos]
      exact mul_le_mul_of_nonneg_left (hp _ hu) hpos.le
  have hnp : ∀ i, 1 + σ i * xCrit N σ k ≠ 0 := by
    intro i h0
    rcases (hσ i).eq_or_lt with h0' | hpos
    · rw [← h0'] at h0; norm_num at h0
    · have := hpb i
      rw [h0, abs_zero] at this
      linarith [mul_pos hpos h.pos]
  have hxf : xCrit N σ k ≠ 0 ∧ fR1 N σ (xCrit N σ k) = 0 := by
    by_cases hkp : k = 2 * numBands N σ
    · have hy0 : yEdge N σ ≠ 0 := fun h0 => hfin ⟨hkp, h0⟩
      obtain ⟨hyC, hyF⟩ := yEdge_spec N σ hσ hN hS
      have hx : xCrit N σ k = (yEdge N σ)⁻¹ := by unfold xCrit; simp only [hkp, ↓reduceIte]
      rw [hx]
      exact ⟨inv_ne_zero hy0, by rw [et_fR1_inv N σ hσ hy0 hyC, hyF, mul_zero]⟩
    · obtain ⟨hmem, -⟩ := et_xCrit_spec N σ hσ hN hS hk1 (lt_of_le_of_ne hk2 hkp)
      obtain ⟨hin, -, hf⟩ := et_mem_innerCrit N σ hσ hN hmem
      exact ⟨hin.1.ne, hf⟩
  exact ⟨hfin, hxf.1, hpb, hnp, hxf.2, edgeVal_eq_fR N σ hσ hN hS hk1 hk2 hfin⟩

/-- Lemma A.3, (f_der_est): `|x| ≥ c_x` at every nonzero critical point `x`. -/
private lemma et_cx_le {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) {x : ℝ}
    (hx : x ≠ 0) (h1 : fR1 N σ x = 0) : edgecx τ ≤ |x| := by
  have hτ := h.pos
  have hs := Real.sqrt_pos.2 hτ
  have hss : √τ ^ 2 = τ := Real.sq_sqrt hτ.le
  by_cases hxt : τ ≤ |x|
  · exact (et_consts hτ).2.2.1.trans hxt
  rw [not_le] at hxt
  have hax := abs_pos.2 hx
  have hd : 0 < τ - |x| := by linarith
  have hterm : ∀ i, σ i ^ 2 / (N * (1 + σ i * x) ^ 2) ≤ ((τ - |x|) ^ 2)⁻¹ / N := by
    intro i
    have h0 := h.nonneg i
    have hστ : σ i * τ ≤ 1 := by
      have := mul_le_mul_of_nonneg_right (h.bound_Sigma i) hτ.le
      rwa [inv_mul_cancel₀ hτ.ne'] at this
    have hxl : -|x| ≤ x := neg_abs_le x
    have hq : σ i * (τ - |x|) ≤ 1 + σ i * x := by nlinarith [mul_le_mul_of_nonneg_left hxl h0]
    have hqpos : 0 < 1 + σ i * x := by
      have : 0 < τ * (1 + σ i * x) := by
        nlinarith [mul_le_mul_of_nonneg_left hxl h0, mul_nonneg (sub_nonneg.2 hστ) (abs_nonneg x)]
      exact pos_of_mul_pos_right this hτ.le
    have e : σ i ^ 2 / (N * (1 + σ i * x) ^ 2) = (σ i / (1 + σ i * x)) ^ 2 / N := by
      rw [div_pow, div_div, mul_comm ((1 + σ i * x) ^ 2)]
    rw [e]
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg N)
    have hle : σ i / (1 + σ i * x) ≤ (τ - |x|)⁻¹ := by
      rw [div_le_iff₀ hqpos]
      calc σ i = (τ - |x|)⁻¹ * (σ i * (τ - |x|)) := by field_simp
        _ ≤ (τ - |x|)⁻¹ * (1 + σ i * x) := by gcongr
    rw [← inv_pow]
    exact pow_le_pow_left₀ (div_nonneg h0 hqpos.le) hle 2
  have hsum := et_sum_le h (by positivity) _ hterm
  have h1' : (x ^ 2)⁻¹ = ∑ i, σ i ^ 2 / (N * (1 + σ i * x) ^ 2) := by
    unfold fR1 at h1; linarith
  rw [← h1', ← mul_inv] at hsum
  have h2 : τ * (τ - |x|) ^ 2 ≤ x ^ 2 := by
    rw [← inv_le_inv₀ (by positivity) (by positivity)]
    exact hsum
  have h3 : √τ * (τ - |x|) ≤ |x| := by
    rw [← pow_le_pow_iff_left₀ (by positivity) (abs_nonneg x) two_ne_zero, mul_pow, hss, sq_abs]
    exact h2
  unfold edgecx
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- Lemma A.3, (f_der_est): `|x_k| ≤ C_x` at a regular edge. -/
private lemma et_abs_le_Cx {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ}
    (h : DensityAssumptions τ N σ) (hk : RegularEdge τ N σ k) : |xCrit N σ k| ≤ edgeCx τ := by
  obtain ⟨hN, hS⟩ := et_facts h
  have hσ := h.nonneg
  have hτ := h.pos
  obtain ⟨hfin, -⟩ := et_reg h hk
  have hm := mExt_edgeVal N σ hσ hN hS hk.1 hk.2.1 hfin
  have ha : τ ≤ edgeVal N σ k := hk.2.2.1
  set a := edgeVal N σ k with ha_def
  have ha0 : 0 < a := hτ.trans_le ha
  have ht := tendsto_mFun_of_ne_zero N σ hσ ha0.ne'
  rw [hm] at ht
  set z : ℕ → ℂ := fun n => (a : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I with hz
  have hzim : ∀ n, 0 < (z n).im := fun n => by
    simp only [hz, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
    positivity
  have hzre : ∀ n, a ≤ ‖z n‖ := fun n => by
    have := Complex.abs_re_le_norm (z n)
    have hre : (z n).re = a := by simp [hz]
    rw [hre, abs_of_pos ha0] at this
    exact this
  have hseq : Tendsto z atTop (𝓝[upperHalf] (a : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hzim⟩
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 := ((Complex.continuous_ofReal.tendsto 0).comp h0).mul_const Complex.I
    have h2 := h1.const_add (a : ℂ)
    simpa [hz] using h2
  have hlim := (ht.comp hseq).norm
  have hb : ∀ n, ‖mFun N σ (z n)‖ ≤ (1 + √(massRatio N σ)) / a := fun n =>
    (norm_mFun_le N σ hσ (hzim n)).trans
      (div_le_div_of_nonneg_left (by positivity) ha0 (hzre n))
  have hle := le_of_tendsto' hlim hb
  rw [Complex.norm_real, Real.norm_eq_abs] at hle
  refine hle.trans ?_
  unfold edgeCx
  have hR : massRatio N σ ≤ τ⁻¹ := (massRatio_le_phiRatio N σ).trans h.phi_upper
  have hsR : √(massRatio N σ) ≤ (√τ)⁻¹ := by
    rw [← Real.sqrt_inv]; exact Real.sqrt_le_sqrt hR
  exact div_le_div₀ (by positivity) (by linarith) hτ ha

/-! ## (f''_expr) and the bounds on `x_k` and `f''(x_k)` -/

/-- (f''_expr): at a critical point, `f''(x) = -(2/x) Σ_i σ_i² / (N (1 + σ_i x)³)`. -/
theorem fR2_eq_of_fR1_eq_zero (N : ℕ) (σ : Fin M → ℝ) {x : ℝ} (hx : x ≠ 0)
    (hx' : ∀ i, 1 + σ i * x ≠ 0) (h1 : fR1 N σ x = 0) :
    fR2 N σ x = -(2 / x) * ∑ i, σ i ^ 2 / (N * (1 + σ i * x) ^ 3) := by
  have h1' : (x ^ 2)⁻¹ = ∑ i, σ i ^ 2 / (N * (1 + σ i * x) ^ 2) := by
    unfold fR1 at h1; linarith
  have e : -2 * (x ^ 3)⁻¹ = -(2 / x) * (x ^ 2)⁻¹ := by field_simp
  unfold fR2
  rw [e, h1', Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  · have := hx' i
    have hNr : (N : ℝ) ≠ 0 := by positivity
    field_simp
    ring

/-- Lemma A.3, (f_der_est): `|x_k| ≍ 1`. -/
theorem xCrit_bounds {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ} (h : DensityAssumptions τ N σ)
    (hk : RegularEdge τ N σ k) :
    edgecx τ ≤ |xCrit N σ k| ∧ |xCrit N σ k| ≤ edgeCx τ ∧
      ∀ i, 1 + σ i * xCrit N σ k ≠ 0 := by
  obtain ⟨-, hx0, -, hnp, hf1, -⟩ := et_reg h hk
  exact ⟨et_cx_le h hx0 hf1, et_abs_le_Cx h hk, hnp⟩

/-- Lemma A.3, (f_der_est): `|f''(x_k)| ≤ C₂`. -/
theorem abs_fR2_xCrit_le {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ}
    (h : DensityAssumptions τ N σ) (hk : RegularEdge τ N σ k) :
    |fR2 N σ (xCrit N σ k)| ≤ edgeC2 τ := by
  obtain ⟨-, hx0, hpb, hnp, hf1, -⟩ := et_reg h hk
  have hτ := h.pos
  obtain ⟨hcx, hCx, -⟩ := et_consts hτ
  have hlo := et_cx_le h hx0 hf1
  have hhi := et_abs_le_Cx h hk
  rw [fR2_eq_of_fR1_eq_zero N σ hx0 hnp hf1]
  set x := xCrit N σ k
  have hax : 0 < |x| := abs_pos.2 hx0
  have hterm : ∀ i, |σ i ^ 2 / (N * (1 + σ i * x) ^ 3)| ≤
      (τ⁻¹ ^ 2 + edgeCx τ * τ⁻¹ ^ 3) / N := by
    intro i
    have h0 := h.nonneg i
    rcases h0.eq_or_lt with h0' | hpos
    · rw [← h0']; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        zero_div, abs_zero]; positivity
    set q := |1 + σ i * x| with hq
    have hqpos : 0 < q := lt_of_lt_of_le (mul_pos hpos hτ) (hpb i)
    have hr : σ i / q ≤ τ⁻¹ := by
      rw [div_le_iff₀ hqpos]
      calc σ i = τ⁻¹ * (σ i * τ) := by field_simp
        _ ≤ τ⁻¹ * q := by gcongr; exact hpb i
    have h1q : 1 ≤ q + σ i * |x| := by
      nlinarith [le_abs_self (1 + σ i * x), mul_le_mul_of_nonneg_left (neg_le_abs x) h0]
    have key : σ i ^ 2 / q ^ 3 ≤ τ⁻¹ ^ 2 + edgeCx τ * τ⁻¹ ^ 3 := by
      have e : σ i ^ 2 / q ^ 3 = (σ i / q) ^ 2 * (1 / q) := by field_simp
      have h1 : 1 / q ≤ 1 + σ i / q * |x| := by
        rw [div_le_iff₀ hqpos]
        have : (1 + σ i / q * |x|) * q = q + σ i * |x| := by field_simp
        linarith
      rw [e]
      calc (σ i / q) ^ 2 * (1 / q) ≤ (σ i / q) ^ 2 * (1 + σ i / q * |x|) := by gcongr
        _ = (σ i / q) ^ 2 + (σ i / q) ^ 3 * |x| := by ring
        _ ≤ τ⁻¹ ^ 2 + τ⁻¹ ^ 3 * edgeCx τ := by gcongr
        _ = τ⁻¹ ^ 2 + edgeCx τ * τ⁻¹ ^ 3 := by ring
    have habs : |σ i ^ 2 / (N * (1 + σ i * x) ^ 3)| = σ i ^ 2 / q ^ 3 / N := by
      rw [abs_div, abs_mul, abs_pow, abs_pow, Nat.abs_cast, abs_of_nonneg h0, div_div,
        mul_comm (q ^ 3)]
    rw [habs]
    exact div_le_div_of_nonneg_right key (Nat.cast_nonneg N)
  have hS : |∑ i, σ i ^ 2 / (N * (1 + σ i * x) ^ 3)| ≤
      τ⁻¹ * (τ⁻¹ ^ 2 + edgeCx τ * τ⁻¹ ^ 3) :=
    (Finset.abs_sum_le_sum_abs _ _).trans (et_sum_le h (by positivity) _ hterm)
  rw [abs_mul, abs_neg, abs_div, abs_two]
  unfold edgeC2
  calc 2 / |x| * |∑ i, σ i ^ 2 / (N * (1 + σ i * x) ^ 3)|
      ≤ 2 / edgecx τ * (τ⁻¹ * (τ⁻¹ ^ 2 + edgeCx τ * τ⁻¹ ^ 3)) := by gcongr
    _ = 2 / edgecx τ * τ⁻¹ * (τ⁻¹ ^ 2 + edgeCx τ * τ⁻¹ ^ 3) := by ring

/-! ## The lower bound on `(-1)^{k+1} f''(x_k)` -/

/-- If `x < 0` is a critical point with `0 < 1 + σ_i x` for all `i`, then `f''(x) ≥ 2/|x|³`. -/
private lemma et_fR2_first (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {x : ℝ} (hx : x < 0)
    (hpos : ∀ i, 0 < 1 + σ i * x) (h1 : fR1 N σ x = 0) : 2 / |x| ^ 3 ≤ fR2 N σ x := by
  rw [fR2_eq_of_fR1_eq_zero N σ hx.ne (fun i => (hpos i).ne') h1]
  have h1' : (x ^ 2)⁻¹ = ∑ i, σ i ^ 2 / (N * (1 + σ i * x) ^ 2) := by
    unfold fR1 at h1; linarith
  have hle : (x ^ 2)⁻¹ ≤ ∑ i, σ i ^ 2 / (N * (1 + σ i * x) ^ 3) := by
    rw [h1']
    refine Finset.sum_le_sum fun i _ => ?_
    have hq := hpos i
    have hq1 : 1 + σ i * x ≤ 1 := by nlinarith [hσ i]
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp
    refine div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) ?_
    have : (1 + σ i * x) ^ 3 ≤ (1 + σ i * x) ^ 2 := by
      rw [pow_succ]; nlinarith [pow_pos hq 2]
    exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg N)
  have hax : |x| = -x := abs_of_neg hx
  have hx2 : 0 < -x := by linarith
  calc 2 / |x| ^ 3 = 2 / |x| * (x ^ 2)⁻¹ := by
        rw [hax]; field_simp
    _ ≤ 2 / |x| * ∑ i, σ i ^ 2 / (N * (1 + σ i * x) ^ 3) := by
        gcongr
    _ = -(2 / x) * ∑ i, σ i ^ 2 / (N * (1 + σ i * x) ^ 3) := by
        rw [hax, div_neg]

/-- If `x` is a critical point with `|x| ≤ C_x` and `x (1 + σ_i x) > 0` whenever `σ_i > 0`, then
`-f''(x) ≥ 2τ/((C_x + τ)|x|³)`. -/
private lemma et_fR2_last {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ)
    {x : ℝ} (hx : x ≠ 0) (hnp : ∀ i, 1 + σ i * x ≠ 0)
    (hsg : ∀ i, 0 < σ i → 0 < x * (1 + σ i * x)) (h1 : fR1 N σ x = 0)
    (hX : |x| ≤ edgeCx τ) : 2 * τ / ((edgeCx τ + τ) * |x| ^ 3) ≤ -fR2 N σ x := by
  obtain ⟨hN, -⟩ := et_facts h
  have hτ := h.pos
  have hCx := (et_consts hτ).2.1
  rw [fR2_eq_of_fR1_eq_zero N σ hx hnp h1, neg_mul, neg_neg]
  have h1' : (x ^ 2)⁻¹ = ∑ i, σ i ^ 2 / (N * (1 + σ i * x) ^ 2) := by
    unfold fR1 at h1; linarith
  have hax := abs_pos.2 hx
  have hNr : (N : ℝ) ≠ 0 := by positivity
  set K := τ / ((edgeCx τ + τ) * |x|) with hK
  have hterm : ∀ i, σ i ^ 2 / (N * (1 + σ i * x) ^ 2) * K ≤
      1 / x * (σ i ^ 2 / (N * (1 + σ i * x) ^ 3)) := by
    intro i
    rcases (h.nonneg i).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    have hxq := hsg i hpos
    have hq := hnp i
    have e : 1 / x * (σ i ^ 2 / (N * (1 + σ i * x) ^ 3)) =
        σ i ^ 2 / (N * (1 + σ i * x) ^ 2) * (x * (1 + σ i * x))⁻¹ := by
      field_simp
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [hK, ← one_div, div_le_div_iff₀ (by positivity) hxq, one_mul]
    have hστ : σ i * τ ≤ 1 := by
      have := mul_le_mul_of_nonneg_right (h.bound_Sigma i) hτ.le
      rwa [inv_mul_cancel₀ hτ.ne'] at this
    have hxx : x * (1 + σ i * x) ≤ |x| * (1 + σ i * |x|) := by
      have : x * (1 + σ i * x) = x + σ i * x ^ 2 := by ring
      rw [this, ← sq_abs x]
      nlinarith [le_abs_self x]
    calc τ * (x * (1 + σ i * x)) ≤ τ * (|x| * (1 + σ i * |x|)) := by gcongr
      _ = |x| * (τ + (σ i * τ) * |x|) := by ring
      _ ≤ |x| * (τ + 1 * edgeCx τ) := by gcongr
      _ = (edgeCx τ + τ) * |x| := by ring
  have hsum : (x ^ 2)⁻¹ * K ≤ 1 / x * ∑ i, σ i ^ 2 / (N * (1 + σ i * x) ^ 3) := by
    rw [h1', Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hterm i
  calc 2 * τ / ((edgeCx τ + τ) * |x| ^ 3) = 2 * ((x ^ 2)⁻¹ * K) := by
        rw [hK, ← sq_abs x]; field_simp
    _ ≤ 2 * (1 / x * ∑ i, σ i ^ 2 / (N * (1 + σ i * x) ^ 3)) := by gcongr
    _ = 2 / x * ∑ i, σ i ^ 2 / (N * (1 + σ i * x) ^ 3) := by ring

/-- A function with nonpositive derivative on `[a, b]` satisfies `g b ≤ g a`. -/
private lemma et_antitone {g g' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hd : ∀ y ∈ Set.Icc a b, HasDerivAt g (g' y) y) (hneg : ∀ y ∈ Set.Icc a b, g' y ≤ 0) :
    g b ≤ g a := by
  have hcont : ContinuousOn g (Set.Icc a b) := fun y hy =>
    (hd y hy).continuousAt.continuousWithinAt
  exact antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) hcont
    (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt)
    (fun y hy => hneg y (interior_subset hy)) ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

/-- `y ↦ y³ f''(y) = -2 + 2 N⁻¹ Σ_i (σ_i y / (1 + σ_i y))³` is nondecreasing between two poles. -/
private lemma et_h_mono (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {y₁ y₂ : ℝ}
    (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0) (h12 : y₁ ≤ y₂)
    (hs : ∀ i, 0 < (1 + σ i * y₁) * (1 + σ i * y₂)) :
    y₁ ^ 3 * fR2 N σ y₁ ≤ y₂ ^ 3 * fR2 N σ y₂ := by
  have e : ∀ y : ℝ, y ≠ 0 → y ^ 3 * fR2 N σ y =
      -2 + 2 * ∑ i, (σ i * y / (1 + σ i * y)) ^ 3 / N := by
    intro y hy
    unfold fR2
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · field_simp
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [div_eq_mul_inv, mul_inv, mul_pow, inv_pow]
      ring
  rw [e y₁ hy₁, e y₂ hy₂]
  have hle : ∀ i, (σ i * y₁ / (1 + σ i * y₁)) ^ 3 / N ≤ (σ i * y₂ / (1 + σ i * y₂)) ^ 3 / N := by
    intro i
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg N)
    refine (Odd.strictMono_pow (by decide : Odd 3)).monotone ?_
    have hp := hs i
    have h1 : 1 + σ i * y₁ ≠ 0 := left_ne_zero_of_mul hp.ne'
    have h2 : 1 + σ i * y₂ ≠ 0 := right_ne_zero_of_mul hp.ne'
    have e2 : σ i * y₂ / (1 + σ i * y₂) - σ i * y₁ / (1 + σ i * y₁) =
        σ i * (y₂ - y₁) / ((1 + σ i * y₁) * (1 + σ i * y₂)) := by
      field_simp
      ring
    have : 0 ≤ σ i * (y₂ - y₁) / ((1 + σ i * y₁) * (1 + σ i * y₂)) :=
      div_nonneg (mul_nonneg (hσ i) (by linarith)) hp.le
    linarith
  have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hle i
  linarith

/-- Points of `[c, d]`, `d < 0`, when `1 + σ_i c` and `1 + σ_i d` have the same sign. -/
private lemma et_mid {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) {c d : ℝ} (hd0 : d < 0)
    (hs : ∀ i, 0 < (1 + σ i * c) * (1 + σ i * d)) {y : ℝ} (hy : y ∈ Set.Icc c d) :
    y ≠ 0 ∧ (∀ i, 1 + σ i * y ≠ 0) ∧
      ∀ i, 0 < (1 + σ i * c) * (1 + σ i * y) ∧ 0 < (1 + σ i * y) * (1 + σ i * d) := by
  have key : ∀ i, 0 < (1 + σ i * c) * (1 + σ i * y) ∧ 0 < (1 + σ i * y) * (1 + σ i * d) := by
    intro i
    have h1 : σ i * c ≤ σ i * y := mul_le_mul_of_nonneg_left hy.1 (hσ i)
    have h2 : σ i * y ≤ σ i * d := mul_le_mul_of_nonneg_left hy.2 (hσ i)
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos (hs i) with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have : 0 < 1 + σ i * y := by linarith
      exact ⟨mul_pos ha this, mul_pos this hb⟩
    · have : 1 + σ i * y < 0 := by linarith
      exact ⟨mul_pos_of_neg_of_neg ha this, mul_pos_of_neg_of_neg this hb⟩
  exact ⟨(hy.2.trans_lt hd0).ne, fun i => right_ne_zero_of_mul (key i).1.ne', key⟩

private lemma et_deriv_pair (N : ℕ) (σ : Fin M → ℝ) {y : ℝ} (hy0 : y ≠ 0)
    (hnp : ∀ i, 1 + σ i * y ≠ 0) :
    HasDerivAt (fR N σ) (fR1 N σ y) y ∧ HasDerivAt (fR1 N σ) (fR2 N σ y) y :=
  ⟨hasDerivAt_fR N σ hy0 hnp, hasDerivAt_fR1 N σ hy0 hnp⟩

private lemma et_hasDerivAt_sq (B c y : ℝ) :
    HasDerivAt (fun t : ℝ => B * (t - c) ^ 2 / 2) (B * (y - c)) y := by
  have := ((((hasDerivAt_id' y).sub_const c).mul ((hasDerivAt_id' y).sub_const c)).const_mul
    B).div_const 2
  convert this using 1
  · funext t; simp only [Pi.mul_apply]; ring
  · ring

/-- Interior odd edge: `x_{2j+1} = c ≤ d = x_{2j} < 0` between the same poles, `f'(c) = 0` and
`f(d) - f(c) ≥ τ` give `f''(c) > 0` and `τ ≤ (c/d)³ f''(c) (d - c)² / 2`. -/
private lemma et_odd (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {c d τ : ℝ} (hτ : 0 < τ)
    (hcd : c ≤ d) (hd0 : d < 0) (hs : ∀ i, 0 < (1 + σ i * c) * (1 + σ i * d))
    (hc1 : fR1 N σ c = 0) (hgap : τ ≤ fR N σ d - fR N σ c) :
    0 < fR2 N σ c ∧ τ ≤ (c / d) ^ 3 * fR2 N σ c * (d - c) ^ 2 / 2 := by
  set A := fR2 N σ c with hA
  set B := (c / d) ^ 3 * max A 0 with hB
  have hc0 : c < 0 := hcd.trans_lt hd0
  have hcd3 : 0 < (c / d) ^ 3 := pow_pos (div_pos_of_neg_of_neg hc0 hd0) 3
  have hderiv : ∀ y ∈ Set.Icc c d,
      HasDerivAt (fR N σ) (fR1 N σ y) y ∧ HasDerivAt (fR1 N σ) (fR2 N σ y) y := fun y hy =>
    et_deriv_pair N σ (et_mid hσ hd0 hs hy).1 (et_mid hσ hd0 hs hy).2.1
  have hf2 : ∀ y ∈ Set.Icc c d, fR2 N σ y ≤ B := by
    intro y hy
    obtain ⟨hy0, -, hp⟩ := et_mid hσ hd0 hs hy
    have hyneg : y < 0 := hy.2.trans_lt hd0
    have hm := et_h_mono N σ hσ hc0.ne hy0 hy.1 (fun i => (hp i).1)
    have hy3 : y ^ 3 < 0 := Odd.pow_neg (by decide) hyneg
    have e1 : fR2 N σ y ≤ (c / y) ^ 3 * A := by
      rw [div_pow, div_mul_eq_mul_div, le_div_iff_of_neg hy3]
      linarith
    have hcy0 : 0 < c / y := div_pos_of_neg_of_neg hc0 hyneg
    have hcyd : c / y ≤ c / d := by
      rw [← neg_div_neg_eq c y, ← neg_div_neg_eq c d]
      exact div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith [hy.2])
    calc fR2 N σ y ≤ (c / y) ^ 3 * A := e1
      _ ≤ (c / y) ^ 3 * max A 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
      _ ≤ (c / d) ^ 3 * max A 0 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hcy0.le hcyd 3) (le_max_right _ _)
  have hf1 : ∀ y ∈ Set.Icc c d, fR1 N σ y ≤ B * (y - c) := by
    intro y hy
    have := et_antitone (g := fun t => fR1 N σ t - B * t) (g' := fun t => fR2 N σ t - B) hy.1
      (fun t ht => by
        have h1 := (hderiv t ⟨ht.1, ht.2.trans hy.2⟩).2.sub ((hasDerivAt_id' t).const_mul B)
        convert h1 using 1; ring)
      (fun t ht => by linarith [hf2 t ⟨ht.1, ht.2.trans hy.2⟩])
    simp only [hc1] at this
    linarith
  have hfd : fR N σ d - fR N σ c ≤ B * (d - c) ^ 2 / 2 := by
    have := et_antitone (g := fun t => fR N σ t - B * (t - c) ^ 2 / 2)
      (g' := fun t => fR1 N σ t - B * (t - c)) hcd
      (fun t ht => (hderiv t ht).1.sub (et_hasDerivAt_sq B c t))
      (fun t ht => by linarith [hf1 t ht])
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      zero_div, sub_zero] at this
    linarith
  have hBpos : 0 < B := by
    by_contra hB0
    rw [not_lt] at hB0
    have : B * (d - c) ^ 2 / 2 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hB0 (sq_nonneg _))
        (by norm_num)
    linarith
  have hApos : 0 < A := by
    by_contra hA0
    rw [not_lt] at hA0
    rw [hB, max_eq_right hA0, mul_zero] at hBpos
    exact lt_irrefl _ hBpos
  refine ⟨hApos, ?_⟩
  rw [hB, max_eq_left hApos.le] at hfd
  linarith

/-- Interior even edge: `c = x_{2j+1} ≤ d = x_{2j} < 0` between the same poles, `f'(d) = 0` and
`f(d) - f(c) ≥ τ` give `-f''(d) ≥ τ³/4`. -/
private lemma et_even (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {c d τ : ℝ} (hτ : 0 < τ)
    (hcd : c ≤ d) (hd0 : d < 0) (hs : ∀ i, 0 < (1 + σ i * c) * (1 + σ i * d))
    (hd1 : fR1 N σ d = 0) (hgap : τ ≤ fR N σ d - fR N σ c) : τ ^ 3 / 4 ≤ -fR2 N σ d := by
  set A := fR2 N σ d with hA
  set B := max (-A) 0 with hB
  have hB0 : 0 ≤ B := le_max_right _ _
  have hc0 : c < 0 := hcd.trans_lt hd0
  have hderiv : ∀ y ∈ Set.Icc c d,
      HasDerivAt (fR N σ) (fR1 N σ y) y ∧ HasDerivAt (fR1 N σ) (fR2 N σ y) y := fun y hy =>
    et_deriv_pair N σ (et_mid hσ hd0 hs hy).1 (et_mid hσ hd0 hs hy).2.1
  have hf2 : ∀ y ∈ Set.Icc c d, -B ≤ fR2 N σ y := by
    intro y hy
    obtain ⟨hy0, -, hp⟩ := et_mid hσ hd0 hs hy
    have hyneg : y < 0 := hy.2.trans_lt hd0
    have hm := et_h_mono N σ hσ hy0 hd0.ne hy.2 (fun i => (hp i).2)
    have hy3 : y ^ 3 < 0 := Odd.pow_neg (by decide) hyneg
    have e1 : (d / y) ^ 3 * A ≤ fR2 N σ y := by
      rw [div_pow, div_mul_eq_mul_div, div_le_iff_of_neg hy3]
      linarith
    have hdy0 : 0 < d / y := div_pos_of_neg_of_neg hd0 hyneg
    have hdy1 : d / y ≤ 1 := by
      rw [div_le_one_of_neg hyneg]; exact hy.2
    have hdy3 : (d / y) ^ 3 ≤ 1 := pow_le_one₀ hdy0.le hdy1
    have hAB : -B ≤ A := by rw [hB]; linarith [le_max_left (-A) 0]
    calc -B ≤ (d / y) ^ 3 * (-B) := by nlinarith [pow_pos hdy0 3]
      _ ≤ (d / y) ^ 3 * A := mul_le_mul_of_nonneg_left hAB (pow_pos hdy0 3).le
      _ ≤ fR2 N σ y := e1
  have hf1 : ∀ y ∈ Set.Icc c d, fR1 N σ y ≤ B * (d - y) := by
    intro y hy
    have := et_antitone (g := fun t => -(fR1 N σ t + B * t)) (g' := fun t => -(fR2 N σ t + B))
      hy.2 (fun t ht => by
        have h1 := ((hderiv t ⟨hy.1.trans ht.1, ht.2⟩).2.add ((hasDerivAt_id' t).const_mul B)).neg
        convert h1 using 1; ring)
      (fun t ht => by linarith [hf2 t ⟨hy.1.trans ht.1, ht.2⟩])
    simp only [hd1] at this
    linarith
  have hf1' : ∀ y ∈ Set.Icc c d, fR1 N σ y ≤ (y ^ 2)⁻¹ := by
    intro y _
    unfold fR1
    refine sub_le_self _ (Finset.sum_nonneg fun i _ => ?_)
    exact div_nonneg (sq_nonneg _) (mul_nonneg (Nat.cast_nonneg N) (sq_nonneg _))
  set hh := 2 / τ with hhh
  have hhpos : 0 < hh := by positivity
  -- the part `[y₀, d]`, `y₀ = max c (d - h)`
  have hright : ∀ y₀ ∈ Set.Icc c d, d - hh ≤ y₀ → fR N σ d - fR N σ y₀ ≤ B * hh ^ 2 / 2 := by
    intro y₀ hy₀ hy₀h
    have := et_antitone (g := fun t => fR N σ t + B * (d - t) ^ 2 / 2)
      (g' := fun t => fR1 N σ t - B * (d - t)) hy₀.2
      (fun t ht => by
        have h1 := (hderiv t ⟨hy₀.1.trans ht.1, ht.2⟩).1.add (et_hasDerivAt_sq B d t)
        convert h1 using 1
        · funext s; simp only [Pi.add_apply]; ring
        · ring)
      (fun t ht => by linarith [hf1 t ⟨hy₀.1.trans ht.1, ht.2⟩])
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      zero_div, add_zero] at this
    have hsq : (d - y₀) ^ 2 ≤ hh ^ 2 := pow_le_pow_left₀ (by linarith [hy₀.2]) (by linarith) 2
    nlinarith
  have hmain : τ ≤ B * hh ^ 2 / 2 + 1 / hh := by
    by_cases hch : d - hh ≤ c
    · have := hright c ⟨le_rfl, hcd⟩ hch
      have : 0 < 1 / hh := by positivity
      linarith
    · rw [not_le] at hch
      have hy₀ : d - hh ∈ Set.Icc c d := ⟨hch.le, by linarith⟩
      have h1 := hright (d - hh) hy₀ le_rfl
      have hneg0 : d - hh < 0 := by linarith
      have h2 := et_antitone (g := fun t => fR N σ t + t⁻¹)
        (g' := fun t => fR1 N σ t - (t ^ 2)⁻¹) hch.le
        (fun t ht => by
          have ht' : t ∈ Set.Icc c d := ⟨ht.1, ht.2.trans hy₀.2⟩
          have h1 := (hderiv t ht').1.add (hasDerivAt_inv (et_mid hσ hd0 hs ht').1)
          exact h1.congr_deriv (by ring))
        (fun t ht => by linarith [hf1' t ⟨ht.1, ht.2.trans hy₀.2⟩])
      have hc' : c⁻¹ < 0 := inv_lt_zero.2 hc0
      have hinv : -(d - hh)⁻¹ ≤ 1 / hh := by
        rw [← inv_neg, neg_sub, one_div]
        exact inv_anti₀ hhpos (by linarith)
      linarith
  have hval : B * hh ^ 2 / 2 + 1 / hh = 2 * B / τ ^ 2 + τ / 2 := by
    rw [hhh]; field_simp
  rw [hval] at hmain
  have hBge : τ ^ 3 / 4 ≤ B := by
    have h3 : τ / 2 ≤ 2 * B / τ ^ 2 := by linarith
    rw [le_div_iff₀ (by positivity)] at h3
    nlinarith
  have hBpos : 0 < B := lt_of_lt_of_le (by positivity) hBge
  have hBA : B = -A := by
    rw [hB] at hBpos ⊢
    rcases le_total (-A) 0 with h0 | h0
    · rw [max_eq_right h0] at hBpos; exact absurd hBpos (lt_irrefl _)
    · exact max_eq_left h0
  rw [← hBA]
  exact hBge

/-- Lemma A.3, (f_der_est): `|f''(x_k)| ≥ c₂`, with the sign `(-1)^{k+1}`. -/
theorem edgec2_le_fR2_xCrit {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ}
    (h : DensityAssumptions τ N σ) (hk : RegularEdge τ N σ k) :
    edgec2 τ ≤ (-1 : ℝ) ^ (k + 1) * fR2 N σ (xCrit N σ k) := by
  obtain ⟨hN, hS⟩ := et_facts h
  have hσ := h.nonneg
  have hτ := h.pos
  obtain ⟨hcx, hCx, -, -, -⟩ := et_consts hτ
  obtain ⟨hfin, hx0, -, hnp, hf1, -⟩ := et_reg h hk
  have hX := et_abs_le_Cx h hk
  have hp := (card_innerCrit N σ hσ hN hS).2
  obtain ⟨hk1, hk2, -, hgapk, -⟩ := hk
  have hc2_ext : edgec2 τ ≤ 2 * τ / ((edgeCx τ + τ) * edgeCx τ ^ 3) := min_le_left _ _
  have hc2_odd : edgec2 τ ≤ τ * edgecx τ ^ 3 / (2 * edgeCx τ ^ 5) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hc2_even : edgec2 τ ≤ τ ^ 3 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hax : 0 < |xCrit N σ k| := abs_pos.2 hx0
  -- `2τ/((C_x + τ) C_x³) ≤ 2τ/((C_x + τ)|x_k|³)`
  have hext : 2 * τ / ((edgeCx τ + τ) * edgeCx τ ^ 3) ≤
      2 * τ / ((edgeCx τ + τ) * |xCrit N σ k| ^ 3) := by
    gcongr
  by_cases hk1' : k = 1
  · subst hk1'
    obtain ⟨hxneg, hpos⟩ := et_first N σ hσ hN hS
    have h2 := et_fR2_first N σ hσ hxneg hpos hf1
    rw [show (1 : ℕ) + 1 = 2 from rfl, neg_one_sq, one_mul]
    refine hc2_ext.trans (hext.trans (le_trans ?_ h2))
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 < |xCrit N σ 1| ^ 3 := by positivity
    nlinarith
  by_cases hkp : k = 2 * numBands N σ
  · have hy0 : yEdge N σ ≠ 0 := fun h0 => hfin ⟨hkp, h0⟩
    obtain ⟨hyC, -⟩ := yEdge_spec N σ hσ hN hS
    have hx : xCrit N σ k = (yEdge N σ)⁻¹ := by unfold xCrit; simp only [hkp, ↓reduceIte]
    have hsg : ∀ i, 0 < σ i → 0 < xCrit N σ k * (1 + σ i * xCrit N σ k) := by
      intro i hpos
      have hu : σ i ∈ posVals σ := by simp [posVals, hpos]
      have hys := hyC (σ i) hu
      have e : xCrit N σ k * (1 + σ i * xCrit N σ k) = (yEdge N σ + σ i) / yEdge N σ ^ 2 := by
        rw [hx]; field_simp
      rw [e]
      exact div_pos hys (by positivity)
    have h2 := et_fR2_last h hx0 hnp hsg hf1 hX
    have hodd : Odd (k + 1) := ⟨numBands N σ, by omega⟩
    rw [hodd.neg_one_pow, neg_one_mul]
    exact hc2_ext.trans (hext.trans h2)
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · -- even interior `k = 2j`
    have hk' : k = 2 * j := by omega
    subst hk'
    have hj1 : 1 ≤ j := by omega
    have hj' : 2 * j + 1 < 2 * numBands N σ := by omega
    obtain ⟨hcd, hs⟩ := et_pair N σ hσ hN hS hj1 hj'
    obtain ⟨hmem, -⟩ := et_xCrit_spec N σ hσ hN hS (k := 2 * j) (by omega) (by omega)
    have hd0 := (et_mem_innerCrit N σ hσ hN hmem).1.1
    have hle := edgeVal_succ_le N σ hσ hN hS (k := 2 * j) (by omega) (by omega)
    have hg := hgapk (2 * j + 1) (by omega) (by omega) (by omega)
    have hgap : τ ≤ fR N σ (xCrit N σ (2 * j)) - fR N σ (xCrit N σ (2 * j + 1)) := by
      have e1 : edgeVal N σ (2 * j) = fR N σ (xCrit N σ (2 * j)) := by
        unfold edgeVal; exact ite_eq_right (by omega)
      have e2 : edgeVal N σ (2 * j + 1) = fR N σ (xCrit N σ (2 * j + 1)) := by
        unfold edgeVal; exact ite_eq_right (by omega)
      rw [abs_of_nonneg (by linarith)] at hg
      rw [← e1, ← e2]
      exact hg
    have h2 := et_even N σ hσ hτ hcd hd0 hs hf1 hgap
    have hodd : Odd (2 * j + 1) := ⟨j, rfl⟩
    rw [hodd.neg_one_pow, neg_one_mul]
    exact hc2_even.trans h2
  · -- odd interior `k = 2j + 1`
    subst hj
    have hj1 : 1 ≤ j := by omega
    have hj' : 2 * j + 1 < 2 * numBands N σ := by omega
    obtain ⟨hcd, hs⟩ := et_pair N σ hσ hN hS hj1 hj'
    obtain ⟨hmem, -⟩ := et_xCrit_spec N σ hσ hN hS (k := 2 * j) (by omega) (by omega)
    obtain ⟨hdin, -, hd1⟩ := et_mem_innerCrit N σ hσ hN hmem
    have hd0 := hdin.1
    have hle := edgeVal_succ_le N σ hσ hN hS (k := 2 * j) (by omega) (by omega)
    have hg := hgapk (2 * j) (by omega) (by omega) (by omega)
    have hgap : τ ≤ fR N σ (xCrit N σ (2 * j)) - fR N σ (xCrit N σ (2 * j + 1)) := by
      have e1 : edgeVal N σ (2 * j) = fR N σ (xCrit N σ (2 * j)) := by
        unfold edgeVal; exact ite_eq_right (by omega)
      have e2 : edgeVal N σ (2 * j + 1) = fR N σ (xCrit N σ (2 * j + 1)) := by
        unfold edgeVal; exact ite_eq_right (by omega)
      rw [abs_of_nonpos (by linarith)] at hg
      rw [← e1, ← e2]
      linarith
    obtain ⟨hA, hτA⟩ := et_odd N σ hσ hτ hcd hd0 hs hf1 hgap
    have heven : Even (2 * j + 1 + 1) := ⟨j + 1, by omega⟩
    rw [heven.neg_one_pow, one_mul]
    refine hc2_odd.trans ?_
    set c := xCrit N σ (2 * j + 1)
    set d := xCrit N σ (2 * j)
    set A := fR2 N σ c
    have hc0 : c < 0 := hcd.trans_lt hd0
    have hdlo : edgecx τ ≤ |d| := et_cx_le h hd0.ne hd1
    have hc_abs : |c| = -c := abs_of_neg hc0
    have hd_abs : |d| = -d := abs_of_neg hd0
    have hP : (c / d) ^ 3 ≤ (edgeCx τ / edgecx τ) ^ 3 := by
      have e : c / d = |c| / |d| := by rw [hc_abs, hd_abs, neg_div_neg_eq]
      rw [e]
      exact pow_le_pow_left₀ (by positivity) (div_le_div₀ hCx.le hX hcx hdlo) 3
    have hQ : (d - c) ^ 2 ≤ edgeCx τ ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hτ' : τ ≤ (edgeCx τ / edgecx τ) ^ 3 * A * edgeCx τ ^ 2 / 2 := by
      have h1 : (c / d) ^ 3 * A * (d - c) ^ 2 ≤ (edgeCx τ / edgecx τ) ^ 3 * A * edgeCx τ ^ 2 := by
        have hP0 : 0 ≤ (c / d) ^ 3 := (pow_pos (div_pos_of_neg_of_neg hc0 hd0) 3).le
        calc (c / d) ^ 3 * A * (d - c) ^ 2 ≤ (edgeCx τ / edgecx τ) ^ 3 * A * (d - c) ^ 2 := by
              gcongr
          _ ≤ (edgeCx τ / edgecx τ) ^ 3 * A * edgeCx τ ^ 2 := by gcongr
      linarith
    have e : (edgeCx τ / edgecx τ) ^ 3 * A * edgeCx τ ^ 2 / 2 =
        A * edgeCx τ ^ 5 / (2 * edgecx τ ^ 3) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)] at hτ'
    rw [div_le_iff₀ (by positivity)]
    nlinarith [pow_pos hCx 5]

/-! ## The disk around `x_k` -/

/-- Lemma A.3, (f_der_est): `|f'''| ≤ C₃` on the disk of radius `ρ₀` around `x_k`. -/
theorem norm_fCDeriv3_le {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ}
    (h : DensityAssumptions τ N σ) (hk : RegularEdge τ N σ k) {ζ : ℂ}
    (hζ : ‖ζ - xCrit N σ k‖ ≤ edgeRho0 τ) :
    ζ ≠ 0 ∧ (∀ i, 1 + (σ i : ℂ) * ζ ≠ 0) ∧ ‖fCDeriv3 N σ ζ‖ ≤ edgeC3 τ := by
  have hσ := h.nonneg
  have hτ := h.pos
  obtain ⟨hcx, -, -, -, -, -, -⟩ := et_consts hτ
  obtain ⟨-, hx0, hpb, -, hf1, -⟩ := et_reg h hk
  have hlo := et_cx_le h hx0 hf1
  set x := xCrit N σ k
  have hρc : edgeRho0 τ ≤ edgecx τ / 2 := by
    unfold edgeRho0; linarith [min_le_left (edgecx τ) τ]
  have hρτ : edgeRho0 τ ≤ τ / 2 := by
    unfold edgeRho0; linarith [min_le_right (edgecx τ) τ]
  have hζ0 : edgecx τ / 2 ≤ ‖ζ‖ := by
    have h1 := norm_sub_norm_le (x : ℂ) ζ
    rw [Complex.norm_real, Real.norm_eq_abs, norm_sub_rev] at h1
    linarith
  have hζpos : 0 < ‖ζ‖ := lt_of_lt_of_le (by positivity) hζ0
  have hq : ∀ i, σ i * (τ / 2) ≤ ‖1 + (σ i : ℂ) * ζ‖ := by
    intro i
    have e : ((1 + σ i * x : ℝ) : ℂ) - -((σ i : ℂ) * (ζ - x)) = 1 + (σ i : ℂ) * ζ := by
      push_cast; ring
    have h1 := norm_sub_norm_le (((1 + σ i * x : ℝ) : ℂ)) (-((σ i : ℂ) * (ζ - x)))
    rw [e, norm_neg, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (hσ i)] at h1
    have h2 := hpb i
    have h3 : σ i * ‖ζ - x‖ ≤ σ i * (τ / 2) := mul_le_mul_of_nonneg_left (hζ.trans hρτ) (hσ i)
    linarith
  have hqpos : ∀ i, 0 < ‖1 + (σ i : ℂ) * ζ‖ := by
    intro i
    rcases (hσ i).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · exact lt_of_lt_of_le (by positivity) (hq i)
  refine ⟨norm_pos_iff.1 hζpos, fun i => norm_pos_iff.1 (hqpos i), ?_⟩
  have hterm : ∀ i, ‖(σ i : ℂ) ^ 4 / (N * (1 + σ i * ζ) ^ 4)‖ ≤ (2 / τ) ^ 4 / N := by
    intro i
    rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_natCast, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (hσ i)]
    have e : σ i ^ 4 / (N * ‖1 + (σ i : ℂ) * ζ‖ ^ 4) = (σ i / ‖1 + (σ i : ℂ) * ζ‖) ^ 4 / N := by
      rw [div_pow, div_div, mul_comm (‖1 + (σ i : ℂ) * ζ‖ ^ 4)]
    rw [e]
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg N)
    have hle : σ i / ‖1 + (σ i : ℂ) * ζ‖ ≤ 2 / τ := by
      rw [div_le_div_iff₀ (hqpos i) hτ]
      linarith [hq i]
    exact pow_le_pow_left₀ (div_nonneg (hσ i) (hqpos i).le) hle 4
  have hsum : ‖∑ i, (σ i : ℂ) ^ 4 / (N * (1 + σ i * ζ) ^ 4)‖ ≤ τ⁻¹ * (2 / τ) ^ 4 :=
    (norm_sum_le _ _).trans (et_sum_le h (by positivity) _ hterm)
  have hinv : ‖(ζ ^ 4)⁻¹‖ ≤ (2 / edgecx τ) ^ 4 := by
    rw [norm_inv, norm_pow, ← inv_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ 4
    rw [inv_le_comm₀ hζpos (by positivity), inv_div]
    exact hζ0
  unfold fCDeriv3 edgeC3
  calc ‖6 * (ζ ^ 4)⁻¹ - 6 * ∑ i, (σ i : ℂ) ^ 4 / (N * (1 + σ i * ζ) ^ 4)‖
      ≤ ‖6 * (ζ ^ 4)⁻¹‖ + ‖6 * ∑ i, (σ i : ℂ) ^ 4 / (N * (1 + σ i * ζ) ^ 4)‖ := norm_sub_le _ _
    _ = 6 * ‖(ζ ^ 4)⁻¹‖ + 6 * ‖∑ i, (σ i : ℂ) ^ 4 / (N * (1 + σ i * ζ) ^ 4)‖ := by
        rw [norm_mul, norm_mul]; norm_num
    _ ≤ 6 * (2 / edgecx τ) ^ 4 + 6 * (τ⁻¹ * (2 / τ) ^ 4) := by gcongr
    _ = 6 * (2 / edgecx τ) ^ 4 + 6 * τ⁻¹ * (2 / τ) ^ 4 := by ring

/-- The mean value inequality on the closed disk of radius `‖ζ - x‖` around `x`. -/
private lemma et_mvt {f f' : ℂ → ℂ} {x ζ : ℂ} {C : ℝ}
    (hd : ∀ v ∈ Metric.closedBall x ‖ζ - x‖, HasDerivAt f (f' v) v)
    (hb : ∀ v ∈ Metric.closedBall x ‖ζ - x‖, ‖f' v‖ ≤ C) : ‖f ζ - f x‖ ≤ C * ‖ζ - x‖ :=
  (convex_closedBall x ‖ζ - x‖).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun v hv => (hd v hv).hasDerivWithinAt) hb (Metric.mem_closedBall_self (norm_nonneg _))
    (by rw [Metric.mem_closedBall, dist_eq_norm])

/-- Taylor expansion of `f''`, `f'`, `f` at `x_k` on the disk of radius `ρ₀`. -/
theorem edge_taylor {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ} (h : DensityAssumptions τ N σ)
    (hk : RegularEdge τ N σ k) {ζ : ℂ} (hζ : ‖ζ - xCrit N σ k‖ ≤ edgeRho0 τ) :
    ‖fCDeriv2 N σ ζ - fR2 N σ (xCrit N σ k)‖ ≤ edgeC3 τ * ‖ζ - xCrit N σ k‖ ∧
    ‖fCDeriv N σ ζ - fR2 N σ (xCrit N σ k) * (ζ - xCrit N σ k)‖ ≤
      edgeC3 τ * ‖ζ - xCrit N σ k‖ ^ 2 ∧
    ‖fC N σ ζ - edgeVal N σ k - fR2 N σ (xCrit N σ k) / 2 * (ζ - xCrit N σ k) ^ 2‖ ≤
      edgeC3 τ * ‖ζ - xCrit N σ k‖ ^ 3 := by
  have hτ := h.pos
  obtain ⟨-, -, -, -, hC3, -, -⟩ := et_consts hτ
  obtain ⟨-, -, -, -, hf1, ha⟩ := et_reg h hk
  have hgood : ∀ w : ℂ, ‖w - xCrit N σ k‖ ≤ edgeRho0 τ →
      w ≠ 0 ∧ (∀ i, 1 + (σ i : ℂ) * w ≠ 0) ∧ ‖fCDeriv3 N σ w‖ ≤ edgeC3 τ :=
    fun w hw => norm_fCDeriv3_le h hk hw
  set x := xCrit N σ k
  set F := fR2 N σ x
  have hball : ∀ w : ℂ, ‖w - x‖ ≤ edgeRho0 τ → ∀ v ∈ Metric.closedBall (x : ℂ) ‖w - x‖,
      ‖v - x‖ ≤ ‖w - x‖ ∧ ‖v - x‖ ≤ edgeRho0 τ := by
    intro w hw v hv
    rw [Metric.mem_closedBall, dist_eq_norm] at hv
    exact ⟨hv, hv.trans hw⟩
  have hx2 : fCDeriv2 N σ (x : ℂ) = (F : ℂ) := fCDeriv2_ofReal N σ x
  have hx1 : fCDeriv N σ (x : ℂ) = 0 := by rw [fCDeriv_ofReal, hf1]; simp
  have hx0 : fC N σ (x : ℂ) = (edgeVal N σ k : ℂ) := by rw [fC_ofReal, ha]
  have s1 : ∀ w : ℂ, ‖w - x‖ ≤ edgeRho0 τ → ‖fCDeriv2 N σ w - F‖ ≤ edgeC3 τ * ‖w - x‖ := by
    intro w hw
    rw [← hx2]
    exact et_mvt (fun v hv => by
        obtain ⟨h0, hp, -⟩ := hgood v (hball w hw v hv).2
        exact hasDerivAt_fCDeriv2 N σ h0 hp)
      (fun v hv => (hgood v (hball w hw v hv).2).2.2)
  have s2 : ∀ w : ℂ, ‖w - x‖ ≤ edgeRho0 τ →
      ‖fCDeriv N σ w - F * (w - x)‖ ≤ edgeC3 τ * ‖w - x‖ ^ 2 := by
    intro w hw
    have := et_mvt (f := fun v => fCDeriv N σ v - F * (v - x))
      (f' := fun v => fCDeriv2 N σ v - F) (C := edgeC3 τ * ‖w - x‖) (x := x) (ζ := w)
      (fun v hv => by
        obtain ⟨h0, hp, -⟩ := hgood v (hball w hw v hv).2
        have h1 := (hasDerivAt_fCDeriv N σ h0 hp).sub
          (((hasDerivAt_id' v).sub_const (x : ℂ)).const_mul (F : ℂ))
        convert h1 using 1; ring)
      (fun v hv => (s1 v (hball w hw v hv).2).trans
        (mul_le_mul_of_nonneg_left (hball w hw v hv).1 hC3.le))
    simp only [sub_self, mul_zero, hx1, sub_zero] at this
    calc _ ≤ edgeC3 τ * ‖w - x‖ * ‖w - x‖ := this
      _ = _ := by ring
  refine ⟨s1 ζ hζ, s2 ζ hζ, ?_⟩
  have := et_mvt (f := fun v => fC N σ v - edgeVal N σ k - F / 2 * (v - x) ^ 2)
    (f' := fun v => fCDeriv N σ v - F * (v - x)) (C := edgeC3 τ * ‖ζ - x‖ ^ 2) (x := x) (ζ := ζ)
    (fun v hv => by
      obtain ⟨h0, hp, -⟩ := hgood v (hball ζ hζ v hv).2
      have h1 := ((hasDerivAt_fC N σ h0 hp).sub_const (edgeVal N σ k : ℂ)).sub
        ((((hasDerivAt_id' v).sub_const (x : ℂ)).mul
          ((hasDerivAt_id' v).sub_const (x : ℂ))).const_mul ((F : ℂ) / 2))
      convert h1 using 1
      · funext u; simp only [Pi.sub_apply, Pi.mul_apply]; ring
      · ring)
    (fun v hv => (s2 v (hball ζ hζ v hv).2).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hball ζ hζ v hv).1 2)
        hC3.le))
  simp only [sub_self, hx0, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    sub_zero] at this
  calc _ ≤ edgeC3 τ * ‖ζ - x‖ ^ 2 * ‖ζ - x‖ := this
    _ = _ := by ring

/-- Consequences on the disk of radius `ρ₁`: `|f(ζ) - a_k| ≥ (c₂/4) |ζ - x_k|²` and
`|f'(ζ)| ≥ (3c₂/4) |ζ - x_k|`. -/
theorem edge_disk_lower {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ} (h : DensityAssumptions τ N σ)
    (hk : RegularEdge τ N σ k) {ζ : ℂ} (hζ : ‖ζ - xCrit N σ k‖ ≤ edgeRho1 τ) :
    edgec2 τ / 4 * ‖ζ - xCrit N σ k‖ ^ 2 ≤ ‖fC N σ ζ - edgeVal N σ k‖ ∧
    ‖fC N σ ζ - edgeVal N σ k‖ ≤ edgeC2 τ * ‖ζ - xCrit N σ k‖ ^ 2 ∧
    3 * edgec2 τ / 4 * ‖ζ - xCrit N σ k‖ ≤ ‖fCDeriv N σ ζ‖ := by
  have hτ := h.pos
  obtain ⟨-, -, -, hc2, hC3, -, -⟩ := et_consts hτ
  have hρ10 : edgeRho1 τ ≤ edgeRho0 τ := min_le_left _ _
  have hρ1c : edgeC3 τ * edgeRho1 τ ≤ edgec2 τ / 4 := by
    have := min_le_right (edgeRho0 τ) (edgec2 τ / (4 * edgeC3 τ))
    calc edgeC3 τ * edgeRho1 τ ≤ edgeC3 τ * (edgec2 τ / (4 * edgeC3 τ)) :=
          mul_le_mul_of_nonneg_left this hC3.le
      _ = edgec2 τ / 4 := by field_simp
  obtain ⟨-, t2, t3⟩ := edge_taylor h hk (hζ.trans hρ10)
  have hlow := edgec2_le_fR2_xCrit h hk
  have hup := abs_fR2_xCrit_le h hk
  set r := ‖ζ - xCrit N σ k‖ with hr
  set F := fR2 N σ (xCrit N σ k)
  have hF : edgec2 τ ≤ |F| := by
    refine hlow.trans ?_
    calc (-1 : ℝ) ^ (k + 1) * F ≤ |(-1 : ℝ) ^ (k + 1) * F| := le_abs_self _
      _ = |F| := by rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hr0 : 0 ≤ r := norm_nonneg _
  have hC3r : edgeC3 τ * r ≤ edgec2 τ / 4 :=
    (mul_le_mul_of_nonneg_left hζ hC3.le).trans hρ1c
  have hE3 : edgeC3 τ * r ^ 3 ≤ edgec2 τ / 4 * r ^ 2 := by
    have : edgeC3 τ * r ^ 3 = (edgeC3 τ * r) * r ^ 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hC3r (sq_nonneg r)
  have hE2 : edgeC3 τ * r ^ 2 ≤ edgec2 τ / 4 * r := by
    have : edgeC3 τ * r ^ 2 = (edgeC3 τ * r) * r := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hC3r hr0
  have nq : ‖(F : ℂ) / 2 * (ζ - xCrit N σ k) ^ 2‖ = |F| / 2 * r ^ 2 := by
    rw [norm_mul, norm_div, Complex.norm_real, norm_pow, Real.norm_eq_abs, ← hr]
    norm_num
  have nl : ‖(F : ℂ) * (ζ - xCrit N σ k)‖ = |F| * r := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, ← hr]
  have a1 : |F| / 2 * r ^ 2 - ‖fC N σ ζ - edgeVal N σ k‖ ≤
      ‖fC N σ ζ - edgeVal N σ k - (F : ℂ) / 2 * (ζ - xCrit N σ k) ^ 2‖ := by
    have := norm_sub_norm_le ((F : ℂ) / 2 * (ζ - xCrit N σ k) ^ 2) (fC N σ ζ - edgeVal N σ k)
    rwa [norm_sub_rev ((F : ℂ) / 2 * (ζ - xCrit N σ k) ^ 2), nq] at this
  have a2 : ‖fC N σ ζ - edgeVal N σ k‖ - |F| / 2 * r ^ 2 ≤
      ‖fC N σ ζ - edgeVal N σ k - (F : ℂ) / 2 * (ζ - xCrit N σ k) ^ 2‖ := by
    have := norm_sub_norm_le (fC N σ ζ - edgeVal N σ k) ((F : ℂ) / 2 * (ζ - xCrit N σ k) ^ 2)
    rwa [nq] at this
  have a3 : |F| * r - ‖fCDeriv N σ ζ‖ ≤ ‖fCDeriv N σ ζ - (F : ℂ) * (ζ - xCrit N σ k)‖ := by
    have := norm_sub_norm_le ((F : ℂ) * (ζ - xCrit N σ k)) (fCDeriv N σ ζ)
    rwa [norm_sub_rev ((F : ℂ) * (ζ - xCrit N σ k)), nl] at this
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [sq_nonneg r]
  · have : |F| / 2 * r ^ 2 + edgec2 τ / 4 * r ^ 2 ≤ edgeC2 τ * r ^ 2 := by
      nlinarith [sq_nonneg r]
    linarith
  · nlinarith

/-! ## Instances

Marchenko–Pastur: `M = 1`, `N = 2`, `σ = 1`, `τ = 1/20` (`φ = 1/2`, `p = 1`, `x_1 = √2 - 2`,
`a_1 = 3/2 + √2`, `a_2 = 3/2 - √2`), at the edge `k = 1`, and the point
`ζ = x_1 + i ρ₁` of the Taylor disk. -/

local notation "σMP" => (fun _ : Fin 1 => (1 : ℝ))
local notation "xMP" => xCrit 2 σMP 1
local notation "ζMP" => ((xMP : ℝ) : ℂ) + ((edgeRho1 (1 / 20) : ℝ) : ℂ) * Complex.I

/-- MP (`σ = 1`, `φ = 1/2`): `f''(x_1) = 2 (1 + √φ)⁴ / √φ` at `x_1 = -1/(1 + √φ)`. -/
example : fR2 2 (fun _ : Fin 1 => (1 : ℝ)) (-1 / (1 + √(1 / 2))) =
    2 * (1 + √(1 / 2)) ^ 4 / √(1 / 2) := by
  have hc : √(1 / 2 : ℝ) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have hc0 : 0 < √(1 / 2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  simp only [fR2, Finset.univ_unique, Finset.sum_singleton]
  have h1 : (1 : ℝ) + 1 * (-1 / (1 + √(1 / 2))) = √(1 / 2) / (1 + √(1 / 2)) := by
    field_simp; ring
  rw [h1]
  field_simp
  push_cast
  nlinarith [hc, hc0]

/-- The constants are positive at `τ = 1/20` (the window `τ'` is nondegenerate). -/
example : 0 < edgeTau' (1 / 20) ∧ 0 < edgec2 (1 / 20) := by
  have hx : 0 < edgecx (1 / 20) := by unfold edgecx; positivity
  have hX : 0 < edgeCx (1 / 20) := by unfold edgeCx; positivity
  have h2 : 0 < edgec2 (1 / 20) := by unfold edgec2; positivity
  have h3 : 0 < edgeC3 (1 / 20) := by unfold edgeC3; positivity
  have h0 : 0 < edgeRho0 (1 / 20) := by unfold edgeRho0; positivity
  have h1 : 0 < edgeRho1 (1 / 20) := by unfold edgeRho1; positivity
  exact ⟨by unfold edgeTau' edgeTau0; positivity, h2⟩

end Anisotropic
